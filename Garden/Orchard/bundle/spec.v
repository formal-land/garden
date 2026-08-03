(** * Orchard bundle vocabulary for the §4.14 balance layer

    Shared definitions for the transaction-level value-balance statement
    over Orchard bundles, against §4.14 'Balance and Binding Signature
    (Orchard)' of the Zcash protocol specification:

    - [t] — the bundle: a list of per-action satisfying assignments and the
      bundle's declared [value_balance] (the [v^balanceOrchard] field);
    - the per-action projections [action_net_value] / [action_rcv] /
      [action_cv_net], read from an assignment through the whole-action
      readers of [Orchard/circuit_proof/inputs.v];
    - the bundle sums [sum_net_values] / [sum_rcv] / [cv_net_sum] and the
      binding-validation key [bundle_bvk] (§4.14:
      [bvk = (⊞ cv_net_i) ⊟ ValueCommit_0(v^balance)]), kept on the
      [Pallas.point] side of the [PallasModel.repr] bridge;
    - [dlog_relation] — the explicit discrete-log conclusion of the
      Pedersen-binding reduction between the two §5.4.8.3 value-commitment
      bases; the group is cyclic of prime order, so such a [k] exists and
      only its computability from a balance violation carries content;
    - [SignatureKnowledge] — the knowledge content of a valid Orchard
      binding signature (§4.14, §5.4.7.2): possession of [bsk] with
      [bvk = [bsk] ℛ^Orchard], i.e. the [(0, bsk)] opening of [bvk];
    - [action_ok] — the per-action hypothesis package of
      [CvNetValue.cv_net_commits_net_value_Z]
      ([Orchard/circuit_proof/cv_net_value.v]);
    - [side_conditions] — the bundle-level consensus ranges: the action
      count fits the transaction encoding bound and [value_balance] is a
      signed 64-bit integer (§4.14 notes).

    This file holds definitions only; the balance theorems over this
    vocabulary live in the sibling files of [Garden/Orchard/bundle/]. *)

Require Import Garden.Halo2.main.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.lemmas.
Require Import Garden.Halo2.PallasModel.
Require Import Garden.EllipticCurve.Weierstrass.
Require Import Garden.EllipticCurve.Pallas.
Require Import Garden.Orchard.Pallas.Generators.
Require Import Garden.Orchard.columns.
Require Garden.Orchard.circuit.
Require Import Garden.Orchard.protocol_spec.
Require Import Garden.Orchard.circuit_proof.inputs.
Require Import Garden.Orchard.circuit_proof.merkle.
Require Import Garden.Orchard.circuit_proof.note_commit.cmx.
Require Import Garden.Orchard.circuit_proof.note_commit.words.
Require Import Garden.Orchard.circuit_proof.old_note.words.
Require Import Garden.Field.Field.
Require Import Garden.Plonky3.M.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Lists.List.

#[local] Existing Instance Primes.PallasPIsPrime.

Global Open Scope Z_scope.

Module OrchardBundleSpec.
  Import OrchardActionInputs.

  (** ** The bundle

      An Orchard bundle for one transaction: the per-action satisfying
      assignments (each an [Assignment.t] over the action circuit's
      columns and regions) together with the transaction's declared net
      value balance [v^balanceOrchard] (§4.14). *)
  Record t : Set := {
    actions : list (Assignment.t columns RegionId.t);
    value_balance : Z;
  }.

  (** ** Per-action projections

      Read from an action's assignment through the whole-action readers
      ([read_action_inputs] / [read_action_outputs]). *)

  (** The action's net value [v_old - v_new], over ℤ (the [v^old - v^new]
      argument of §4.14's balance sum). *)
  Definition action_net_value (Γ : Assignment.t columns RegionId.t) : Z :=
    OrchardSpec.in_v_old (read_action_inputs Γ) -
    OrchardSpec.in_v_new (read_action_inputs Γ).

  (** The action's value-commitment randomness [rcv] (§5.4.8.3), as the
      full-width windowed scalar the circuit reads it as. *)
  Definition action_rcv (Γ : Assignment.t columns RegionId.t) : Z :=
    OrchardSpec.in_rcv (read_action_inputs Γ).

  (** The action's public value commitment [cv_net], carried back across
      the coordinate-record bridge onto the Weierstrass group
      ([PallasModel.unrepr] reads the [(0, 0)] sentinel as the identity). *)
  Definition action_cv_net (Γ : Assignment.t columns RegionId.t)
      : Pallas.point :=
    PallasModel.unrepr (OrchardSpec.out_cv_net (read_action_outputs Γ)).

  (** ** Bundle sums

      List folds over an action list, and their instances at a bundle's
      [actions]. Scalar sums stay in ℤ (no reduction modulo the group
      order). *)

  Definition net_value_sum
      (acts : list (Assignment.t columns RegionId.t)) : Z :=
    fold_right (fun Γ s => action_net_value Γ + s) 0 acts.

  Definition rcv_sum
      (acts : list (Assignment.t columns RegionId.t)) : Z :=
    fold_right (fun Γ s => action_rcv Γ + s) 0 acts.

  (** The §4.14 sum [⊞ cv_net_i], folded with the Pallas group law from
      the identity. *)
  Definition cv_net_sum
      (acts : list (Assignment.t columns RegionId.t)) : Pallas.point :=
    fold_right (fun Γ P => Pallas.add (action_cv_net Γ) P)
      Pallas.identity acts.

  Definition sum_net_values (b : t) : Z := net_value_sum (actions b).

  Definition sum_rcv (b : t) : Z := rcv_sum (actions b).

  (** The number of actions in the bundle. *)
  Definition n_actions (b : t) : Z := Z.of_nat (length (actions b)).

  (** ** The binding-validation key [bvk] (§4.14)

      [ValueCommit_0(v)] in point form: [[v] 𝒱^Orchard + [0] ℛ^Orchard]
      (§5.4.8.3), the randomness term being the group identity. *)
  Definition value_commit_0 (v : Z) : Pallas.point :=
    Pallas.mul v PallasGenerators.value_commit_v_G.

  (** §4.14: [bvk = (⊞ cv_net_i) ⊟ ValueCommit_0(v^balanceOrchard)] — the
      homomorphic sum of the actions' value commitments minus the
      commitment (with zero randomness) to the declared balance. *)
  Definition bundle_bvk (b : t) : Pallas.point :=
    Pallas.add (cv_net_sum (actions b))
      (Pallas.neg (value_commit_0 (value_balance b))).

  (** ** The Pedersen-binding reduction target

      An explicit discrete logarithm of [ℛ^Orchard] in base [𝒱^Orchard]
      (the two §5.4.8.3 value-commitment generators). The Pallas group is
      cyclic of prime order, so some such [k] always exists; the balance
      theorems conclude this relation with a [k] computed from the two
      openings of a colliding commitment, so that discarding the disjunct
      is exactly the discrete-log hardness assumption on the generator
      pair — no independence axiom enters the development. *)
  Definition dlog_relation (k : Z) : Prop :=
    PallasGenerators.value_commit_r_G =
      Pallas.mul k PallasGenerators.value_commit_v_G.

  (** ** Binding-signature knowledge (§4.14, §5.4.7.2)

      The semantic content of a valid binding signature over the bundle:
      the signer knows [bsk] with [bvk = [bsk] ℛ^Orchard] — the [(0, bsk)]
      opening of [bvk]. The step from
      [RedPallas.Validate_bvk(bindingSigOrchard) = 1] to this predicate is
      the SUF-CMA / knowledge-of-secret-key property of RedPallas
      (§5.4.7.2) and stays a hypothesis at this layer. *)
  Definition SignatureKnowledge (b : t) (bsk : Z) : Prop :=
    bundle_bvk b = Pallas.mul bsk PallasGenerators.value_commit_r_G.

  (** ** Per-action hypothesis package

      Exactly the hypothesis set of
      [CvNetValue.cv_net_commits_net_value_Z]: the assignment satisfies the
      circuit, and the two short-lookup range families of the relational
      selector model hold — the residue that feeds the 64-bit ranges of
      [v_old]/[v_new].  Neither is an assumption about the witness: the
      deployed circuit enforces both through its range-check lookup
      argument, and they are discharged from acceptance of the pinned
      circuit ([circuit_proof/lookup_closure.v],
      [circuit_proof/lookup_closure_old_note.v]).

      The [CV_NET] row is ⊥-free (complete addition and total group
      multiples only), so the package carries no Merkle package and no
      Sinsemilla nondegeneracy: those belong to the anchor and [CMX] rows,
      which the balance argument never reads. *)
  Definition action_ok (Γ : Assignment.t columns RegionId.t) : Prop :=
    circuit_holds Γ
      Garden.Orchard.circuit.synthesize
      (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty) /\
    NoteCommitNewWords.note_commit_new_short_lookup_ok Γ /\
    OldNoteWords.old_note_short_lookup_ok Γ.

  (** All actions of the bundle satisfy the per-action package. *)
  Definition actions_ok (b : t) : Prop :=
    Forall action_ok (actions b).

  (** ** Bundle-level consensus side conditions

      The action count fits the transaction encoding bound, and the
      declared balance is a signed 64-bit integer (§4.14 notes) — the two
      ranges the integer lift of the balance theorem consumes. *)
  Record side_conditions (b : t) : Prop := {
    n_actions_max : n_actions b <= 2 ^ 16 - 1;
    value_balance_range : - 2 ^ 63 <= value_balance b < 2 ^ 63;
  }.
End OrchardBundleSpec.
