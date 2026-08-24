(** * Fixed Post-NU6.3 PLONK assembly backend

    This file turns the values read by [Reference.read_plonk_prefix] into the
    exact query stream consumed by Halo2 multiopen.  Every commitment object is
    assigned a fresh natural allocation identity; identities never derive from
    point equality.  Gate, permutation, lookup, and vanishing expressions are
    evaluated in Rust order. *)

From Stdlib Require Import ZArith Lists.List Bool Arith.PeanoNat.
Require Import Garden.Halo2.plonkish.main.
Require Import Garden.Halo2.plonkish.poly_domain.
Require Import Garden.Halo2.serialize.
Require Import Garden.Halo2.Verifier.Encoding.Scalar.
Require Import Garden.Halo2.Verifier.Encoding.Point.
Require Import Garden.Halo2.Verifier.Types.
Require Import Garden.Halo2.Verifier.Algebra.
Require Import Garden.Halo2.Verifier.Plonk.
Require Import Garden.Halo2.Verifier.Permutation.
Require Import Garden.Halo2.Verifier.Lookup.
Require Import Garden.Halo2.Verifier.Vanishing.
Require Import Garden.Halo2.Verifier.Commitment.
Require Import Garden.Halo2.Verifier.Reference.
Require Import Garden.Orchard.compiled.algebraic.
Require Import Garden.Orchard.compiled.configuration.
Require Import Garden.Orchard.compiled.pinned.
Require Import Garden.Orchard.Verifier.PostNu6_3.
Require Import Garden.Orchard.Verifier.AssemblyData.
Require Import Garden.Orchard.Verifier.AssemblyPermutation.
Require Import Garden.Orchard.Verifier.AssemblyLookup.
Require Import Garden.Orchard.Verifier.AssemblyProof.
Require Import Garden.Orchard.Verifier.AssemblyProofExpressions.
Require Import Garden.Orchard.Verifier.AssemblyExpressions.

Import ListNotations.
Import Plonkish.
Local Open Scope Z_scope.



Fixpoint query_specs (omega x : VerifierField.t) (specs : list PlonkVerifier.query_spec)
    (keys : list PlonkVerifier.commitment_key) (evals : list VerifierField.t) (index : nat) :
    option (list PlonkVerifier.verifier_query) :=
  match specs with
  | [] => Some []
  | spec :: specs' =>
      match nth_error keys spec.(PlonkVerifier.query_column).(PlonkVerifier.column_index),
            nth_error evals index,
            PlonkVerifier.rotate_omega omega x spec.(PlonkVerifier.query_rotation),
            query_specs omega x specs' keys evals (S index) with
      | Some key, Some eval, Some point, Some tail => Some ({|
          PlonkVerifier.query_commitment := key; PlonkVerifier.query_point := point; PlonkVerifier.query_eval := eval
        |} :: tail)
      | _, _, _, _ => None
      end
  end.

Definition keys_from (f : nat -> PlonkVerifier.commitment_key) (count : nat) :
    list PlonkVerifier.commitment_key := map f (seq 0 count).

Definition permutation_argument (actions proof : nat) (parsed : ReferenceVerifier.plonk_prefix) :
    PermutationVerifier.evaluated := {|
  PermutationVerifier.sets := permutation_sets_from actions proof 0
    (nth proof parsed.(ReferenceVerifier.parsed_permutation_evals) [])
|}.

Fixpoint lookup_queries_from (actions proof index : nat) (omega x : VerifierField.t)
    (parsed : ReferenceVerifier.plonk_prefix) (values : list ReferenceVerifier.lookup_evals) :
    option (list PlonkVerifier.verifier_query) :=
  match values with
  | [] => Some []
  | value :: values' =>
      match LookupVerifier.queries omega x (lookup_proof actions proof index parsed value),
            lookup_queries_from actions proof (S index) omega x parsed values' with
      | Some queries, Some tail => Some (queries ++ tail)
      | _, _ => None
      end
  end.

Definition proof_queries (actions proof : nat) (parsed : ReferenceVerifier.plonk_prefix) :
    option (list PlonkVerifier.verifier_query) :=
  let x := ReferenceVerifier.scalar_Z parsed.(ReferenceVerifier.challenge_x) in
  match query_specs PolyDomain.omega x
          OrchardPostNu63.instance_query_specs
          [instance_key proof]
          (scalar_values (nth proof parsed.(ReferenceVerifier.parsed_instance_evals) [])) 0,
        query_specs PolyDomain.omega x
          OrchardPostNu63.advice_query_specs
          (keys_from (advice_key actions proof) 10)
          (scalar_values (nth proof parsed.(ReferenceVerifier.parsed_advice_evals) [])) 0,
        PermutationVerifier.queries PolyDomain.omega x
          OrchardPostNu63.blinding_factors
          (permutation_argument actions proof parsed),
        lookup_queries_from actions proof 0 PolyDomain.omega x parsed
          (nth proof parsed.(ReferenceVerifier.parsed_lookup_evals) []) with
  | Some instance, Some advice, Some permutation, Some lookups =>
      Some (instance ++ advice ++ permutation ++ lookups)
  | _, _, _, _ => None
  end.

Fixpoint all_proof_queries (actions proof_count proof : nat)
    (parsed : ReferenceVerifier.plonk_prefix) : option (list PlonkVerifier.verifier_query) :=
  match proof_count with
  | O => Some []
  | S proof_count' =>
      match proof_queries actions proof parsed,
            all_proof_queries actions proof_count' (S proof) parsed with
      | Some queries, Some tail => Some (queries ++ tail)
      | _, _ => None
      end
  end.

Definition global_queries (actions : nat) (parsed : ReferenceVerifier.plonk_prefix)
    (vanishing : VanishingVerifier.evaluated) : option (list PlonkVerifier.verifier_query) :=
  let x := ReferenceVerifier.scalar_Z parsed.(ReferenceVerifier.challenge_x) in
  match query_specs PolyDomain.omega x
          OrchardPostNu63.fixed_query_specs
          (keys_from (fixed_key actions) 29)
          (scalar_values parsed.(ReferenceVerifier.parsed_fixed_evals)) 0 with
  | None => None
  | Some fixed =>
      Some (fixed ++
        PermutationVerifier.common_queries (keys_from (common_permutation_key actions) 15) x
          {| PermutationVerifier.permutation_evals :=
               scalar_values parsed.(ReferenceVerifier.parsed_common_permutation_evals) |} ++
        VanishingVerifier.queries x vanishing)
  end.

Definition assemble (actions : list (list Z)) (parsed : ReferenceVerifier.plonk_prefix) :
    ReferenceVerifier.assembly_result :=
  let action_count := List.length actions in
  (** Materialize Rust's commitment allocation map once.  In particular, the
      instance commitments at its head must not be recomputed for every key
      resolved later by [ReferenceVerifier.resolve_terms]. *)
  let bindings := direct_bindings actions parsed in
  let x := ReferenceVerifier.scalar_Z parsed.(ReferenceVerifier.challenge_x) in
  let y := ReferenceVerifier.scalar_Z parsed.(ReferenceVerifier.challenge_y) in
  let xn := VerifierField.pow_nat x OrchardPostNu63.domain_n in
  let '(l_0, l_last, l_blind) := l_values x xn in
  match all_proof_expressions_from OrchardPostNu63.lookup_descriptions
          action_count action_count 0 parsed
          l_0 l_last l_blind x,
        h_msm xn parsed with
  | Some expressions, Some h =>
      let partial := {|
        VanishingVerifier.partial_h_commitments := keys_from (h_key action_count) 8;
        VanishingVerifier.partial_random_poly_commitment := random_key action_count;
        VanishingVerifier.random_eval := ReferenceVerifier.scalar_Z parsed.(ReferenceVerifier.parsed_random_eval)
      |} in
      match VanishingVerifier.verify h_msm_id expressions y xn partial with
      | VanishingVerifier.VanishingPanickedAtQuotientInverse =>
          ReferenceVerifier.AssemblyPanicked Panic.DivisionByZero
      | VanishingVerifier.VanishingEvaluated vanishing =>
          match all_proof_queries action_count action_count 0 parsed,
                global_queries action_count parsed vanishing with
          | Some proofs, Some globals => ReferenceVerifier.AssemblyReady {|
              ReferenceVerifier.assembly_queries := proofs ++ globals;
              ReferenceVerifier.assembly_initial_terms := [];
              ReferenceVerifier.assembly_q_prime_key := direct_key (q_prime_id action_count);
              ReferenceVerifier.assembly_resolve := resolver_from bindings h
            |}
          | _, _ => ReferenceVerifier.AssemblyPanicked Panic.InternalInvariant
          end
      end
  | _, _ => ReferenceVerifier.AssemblyPanicked Panic.InternalInvariant
  end.

Definition backend (actions : list (list Z)) : ReferenceVerifier.backend := {|
  ReferenceVerifier.assemble_plonk := assemble actions
|}.
