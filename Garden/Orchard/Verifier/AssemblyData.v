(** * Commitment allocation and evaluation data for Post-NU6.3 assembly

    This lightweight layer assigns the ghost allocation identities that model
    Rust pointer identity and resolves the commitments/evaluation vectors read
    from the proof.  Keeping it separate bounds Rocq serialization while the
    executable definitions remain transparent. *)

From Stdlib Require Import ZArith Lists.List Bool Arith.PeanoNat.
Require Import Garden.Halo2.Verifier.Encoding.Scalar.
Require Import Garden.Halo2.Verifier.Algebra.
Require Import Garden.Halo2.Verifier.Plonk.
Require Import Garden.Halo2.Verifier.Multiopen.
Require Import Garden.Halo2.Verifier.Commitment.
Require Import Garden.Halo2.Verifier.Reference.
Require Import Garden.Orchard.Verifier.PostNu6_3.

Import ListNotations.
Local Open Scope Z_scope.

Definition direct_key (id : nat) : PlonkVerifier.commitment_key :=
  PlonkVerifier.DirectCommitment id.

(** These naturals are verifier-model allocation identities, not translated
    Rust [usize] values and never enter field arithmetic or the wire format.
    Their only observable operation is equality, modelling [std::ptr::eq];
    consequently there is no machine-integer overflow branch to reproduce. *)
Definition instance_base (_actions : nat) : nat := 0.
Definition advice_base (actions : nat) : nat := actions.
Definition lookup_permuted_base (actions : nat) : nat := (11 * actions)%nat.
Definition permutation_product_base (actions : nat) : nat := (17 * actions)%nat.
Definition lookup_product_base (actions : nat) : nat := (20 * actions)%nat.
Definition random_base (actions : nat) : nat := (23 * actions)%nat.
Definition h_base (actions : nat) : nat := (23 * actions + 1)%nat.
Definition fixed_base (actions : nat) : nat := (23 * actions + 9)%nat.
Definition common_permutation_base (actions : nat) : nat :=
  (23 * actions + 38)%nat.
Definition q_prime_id (actions : nat) : nat := (23 * actions + 53)%nat.
Definition h_msm_id : nat := 0.

Definition instance_key (proof : nat) : PlonkVerifier.commitment_key :=
  direct_key proof.
Definition advice_key (actions proof column : nat) :
    PlonkVerifier.commitment_key :=
  direct_key (advice_base actions + proof * 10 + column)%nat.
Definition lookup_permuted_key (actions proof lookup side : nat) :
    PlonkVerifier.commitment_key :=
  direct_key
    (lookup_permuted_base actions + proof * 6 + lookup * 2 + side)%nat.
Definition permutation_product_key (actions proof set : nat) :
    PlonkVerifier.commitment_key :=
  direct_key (permutation_product_base actions + proof * 3 + set)%nat.
Definition lookup_product_key (actions proof lookup : nat) :
    PlonkVerifier.commitment_key :=
  direct_key (lookup_product_base actions + proof * 3 + lookup)%nat.
Definition random_key (actions : nat) : PlonkVerifier.commitment_key :=
  direct_key (random_base actions).
Definition h_key (actions piece : nat) : PlonkVerifier.commitment_key :=
  direct_key (h_base actions + piece)%nat.
Definition fixed_key (actions column : nat) : PlonkVerifier.commitment_key :=
  direct_key (fixed_base actions + column)%nat.
Definition common_permutation_key (actions column : nat) :
    PlonkVerifier.commitment_key :=
  direct_key (common_permutation_base actions + column)%nat.

Definition binding : Type := (nat * CommitmentVerifier.point)%type.

Fixpoint enumerate_points (start : nat)
    (points : list CommitmentVerifier.point) : list binding :=
  match points with
  | [] => []
  | point :: points' => (start, point) :: enumerate_points (S start) points'
  end.

Definition lookup_permuted_points
    (rows : list (list ReferenceVerifier.lookup_permuted)) :
    list CommitmentVerifier.point :=
  flat_map (fun row => flat_map (fun lookup =>
    [lookup.(ReferenceVerifier.lookup_input_commitment);
     lookup.(ReferenceVerifier.lookup_table_commitment)]) row) rows.

Definition direct_bindings (actions : list (list Z))
    (parsed : ReferenceVerifier.plonk_prefix) : list binding :=
  enumerate_points 0 (map OrchardPostNu63.instance_commitment actions) ++
  enumerate_points (advice_base (List.length actions))
    (concat parsed.(ReferenceVerifier.parsed_advice_commitments)) ++
  enumerate_points (lookup_permuted_base (List.length actions))
    (lookup_permuted_points parsed.(ReferenceVerifier.parsed_lookup_permuted)) ++
  enumerate_points (permutation_product_base (List.length actions))
    (concat parsed.(ReferenceVerifier.parsed_permutation_product_commitments)) ++
  enumerate_points (lookup_product_base (List.length actions))
    (concat parsed.(ReferenceVerifier.parsed_lookup_product_commitments)) ++
  enumerate_points (random_base (List.length actions))
    [parsed.(ReferenceVerifier.parsed_random_poly_commitment)] ++
  enumerate_points (h_base (List.length actions))
    parsed.(ReferenceVerifier.parsed_h_commitments) ++
  enumerate_points (fixed_base (List.length actions))
    OrchardPostNu63.fixed_commitments ++
  enumerate_points (common_permutation_base (List.length actions))
    OrchardPostNu63.permutation_commitments.

Fixpoint find_binding (id : nat) (bindings : list binding) :
    option CommitmentVerifier.point :=
  match bindings with
  | [] => None
  | (candidate, point) :: bindings' =>
      if Nat.eqb id candidate then Some point else find_binding id bindings'
  end.

Fixpoint h_horner (xn : VerifierField.t)
    (points : list CommitmentVerifier.point) (state : CommitmentVerifier.msm) :
    option CommitmentVerifier.msm :=
  match points with
  | [] => Some state
  | point :: points' =>
      match CommitmentVerifier.append_term VerifierField.one point
          (CommitmentVerifier.scale xn state) with
      | CommitmentVerifier.MsmPanicked _ => None
      | CommitmentVerifier.MsmOk state' => h_horner xn points' state'
      end
  end.

Definition h_msm (xn : VerifierField.t)
    (parsed : ReferenceVerifier.plonk_prefix) : option CommitmentVerifier.msm :=
  h_horner xn (rev parsed.(ReferenceVerifier.parsed_h_commitments))
    (CommitmentVerifier.empty OrchardPostNu63.domain_n).

Definition resolver_from (bindings : list binding)
    (h : CommitmentVerifier.msm)
    (key : PlonkVerifier.commitment_key) :
    option ReferenceVerifier.resolved_commitment :=
  match key with
  | PlonkVerifier.DirectCommitment id =>
      option_map ReferenceVerifier.ResolvedPoint
        (find_binding id bindings)
  | PlonkVerifier.MsmCommitment id =>
      if Nat.eqb id h_msm_id then Some (ReferenceVerifier.ResolvedMsm h)
      else None
  end.

(** Rust constructs the commitment map once and then performs all opening-
    claim lookups against that allocation map.  Keep the unshared spelling as
    the auditable pointwise reference; [Assembly.assemble] binds
    [direct_bindings] once and supplies that list to [resolver_from]. *)
Definition resolver (actions : list (list Z))
    (parsed : ReferenceVerifier.plonk_prefix) (h : CommitmentVerifier.msm)
    (key : PlonkVerifier.commitment_key) :
    option ReferenceVerifier.resolved_commitment :=
  resolver_from (direct_bindings actions parsed) h key.

Lemma resolver_from_direct_bindings (actions : list (list Z))
    (parsed : ReferenceVerifier.plonk_prefix) (h : CommitmentVerifier.msm)
    (key : PlonkVerifier.commitment_key) :
  resolver_from (direct_bindings actions parsed) h key =
    resolver actions parsed h key.
Proof. reflexivity. Qed.

(** Pointwise-equal commitment resolvers drive the same Rust-shaped MSM
    update sequence.  This lets the cached implementation be refined without
    appealing to functional extensionality. *)
Lemma resolve_terms_ext
    (left right : PlonkVerifier.commitment_key ->
      option ReferenceVerifier.resolved_commitment)
    (Hresolve : forall key, left key = right key)
    (terms : MultiopenVerifier.symbolic_msm)
    (state : CommitmentVerifier.msm) :
  ReferenceVerifier.resolve_terms left terms state =
    ReferenceVerifier.resolve_terms right terms state.
Proof.
  revert state.
  induction terms as [|term terms IH]; intros state;
    [reflexivity |].
  destruct term as [scalar key].
  cbn [ReferenceVerifier.resolve_terms].
  rewrite (Hresolve key).
  destruct (right key) as [resolved |] eqn:Hkey.
  2: reflexivity.
  1: destruct resolved as [point | value].
  1: destruct (CommitmentVerifier.append_term scalar point state)
       as [state' | failure] eqn:Happend; [apply IH | reflexivity].
  1: destruct (CommitmentVerifier.add_msm
       (CommitmentVerifier.scale scalar value) state)
       as [state' | failure] eqn:Hadd; [apply IH | reflexivity].
Qed.

Lemma resolve_terms_from_direct_bindings (actions : list (list Z))
    (parsed : ReferenceVerifier.plonk_prefix) (h : CommitmentVerifier.msm)
    (terms : MultiopenVerifier.symbolic_msm)
    (state : CommitmentVerifier.msm) :
  ReferenceVerifier.resolve_terms
      (resolver_from (direct_bindings actions parsed) h) terms state =
    ReferenceVerifier.resolve_terms (resolver actions parsed h) terms state.
Proof.
  apply resolve_terms_ext.
  apply resolver_from_direct_bindings.
Qed.

Definition scalar_values (values : list Scalar.t) : list VerifierField.t :=
  map ReferenceVerifier.scalar_Z values.

Definition evaluations_for (parsed : ReferenceVerifier.plonk_prefix)
    (proof : nat) : PlonkVerifier.evaluations := {|
  PlonkVerifier.advice_values := scalar_values
    (nth proof parsed.(ReferenceVerifier.parsed_advice_evals) []);
  PlonkVerifier.fixed_values := scalar_values
    parsed.(ReferenceVerifier.parsed_fixed_evals);
  PlonkVerifier.instance_values := scalar_values
    (nth proof parsed.(ReferenceVerifier.parsed_instance_evals) [])
|}.
