(** * Focused executable tests for verifier control-flow invariants *)

From Stdlib Require Import ZArith Lists.List Bool.
Require Import Garden.Field.Field.
Require Import Garden.Halo2.Verifier.Types.
Require Import Garden.Halo2.Verifier.Encoding.Scalar.
Require Import Garden.Halo2.Verifier.Encoding.Point.
Require Import Garden.Halo2.Verifier.Transcript.
Require Import Garden.Halo2.Verifier.Algebra.
Require Import Garden.Halo2.Verifier.Plonk.
Require Import Garden.Halo2.Verifier.Permutation.
Require Import Garden.Halo2.Verifier.Multiopen.
Require Import Garden.Halo2.Verifier.Commitment.
Require Import Garden.Halo2.Verifier.Reference.

Import ListNotations.
Local Open Scope Z_scope.

Module VerifierCoreTests.
  Module F := VerifierField.
  Module P := PlonkVerifier.
  Module PV := PermutationVerifier.
  Module M := MultiopenVerifier.
  Module C := CommitmentVerifier.
  Module R := ReferenceVerifier.

  Definition permutation_set (id : nat) (last : option F.t) :
      PV.evaluated_set := {|
    PV.product_commitment := P.DirectCommitment id;
    PV.product_eval := Z.of_nat id;
    PV.product_next_eval := Z.of_nat (S id);
    PV.product_last_eval := last
  |}.

  (** [sets.iter().rev().skip(1)] opens set 1 before set 0. *)
  Example permutation_last_query_order :
    PV.last_queries 99
      [permutation_set 10 (Some 110);
       permutation_set 11 (Some 111);
       permutation_set 12 None] =
    Some [
      {| P.query_commitment := P.DirectCommitment 11;
         P.query_point := 99; P.query_eval := 111 |};
      {| P.query_commitment := P.DirectCommitment 10;
         P.query_point := 99; P.query_eval := 110 |}
    ].
  Proof. reflexivity. Qed.

  (** Rust's [sets.iter().skip(1).zip(sets.iter())] emits one linkage
      constraint for every adjacent pair.  With three permutation sets there
      must therefore be two constraints; this guards the recursive tail from
      skipping the middle set. *)
  Definition permutation_linkage_count : nat :=
    match PV.linkage_expressions 7
      [permutation_set 1 (Some 2);
       permutation_set 2 (Some 3);
       permutation_set 3 None] with
    | PV.PermutationExpressions values => List.length values
    | PV.PermutationPanicked _ => 0
    end.

  Example permutation_has_every_adjacent_link :
    permutation_linkage_count = 2%nat.
  Proof. vm_compute. reflexivity. Qed.

  Example permutation_checks_every_previous_last_eval :
    PV.linkage_expressions 7
      [permutation_set 1 (Some 2);
       permutation_set 2 None;
       permutation_set 3 None] =
    PV.PermutationPanicked PV.MissingPreviousLastEvaluation.
  Proof. vm_compute. reflexivity. Qed.

  Definition query (id : nat) (point eval : F.t) : P.verifier_query := {|
    P.query_commitment := P.DirectCommitment id;
    P.query_point := point;
    P.query_eval := eval
  |}.

  Example duplicate_commitment_point_is_rejected :
    M.construct_intermediate_sets [query 4 7 1; query 4 7 2] =
      M.DuplicateCommitmentPointQuery.
  Proof. vm_compute. reflexivity. Qed.

  Definition opposite_y_merge_scalars : list F.t :=
    match C.append_term 3 (Point.affine 1 2) (C.empty 4) with
    | C.MsmPanicked _ => []
    | C.MsmOk first =>
        match C.append_term 5
          (Point.affine 1 (Primes.pallas_q - 2)) first with
        | C.MsmPanicked _ => []
        | C.MsmOk final => map C.term_scalar final.(C.other)
        end
    end.

  Example same_x_opposite_y_subtracts :
    opposite_y_merge_scalars = [F.sub 3 5].
  Proof. vm_compute. reflexivity. Qed.

  Definition duplicate_assembly : R.assembly := {|
    R.assembly_queries := [query 0 1 2; query 0 1 3];
    R.assembly_initial_terms := [];
    R.assembly_q_prime_key := P.DirectCommitment 1;
    R.assembly_resolve := fun _ => None
  |}.

  Definition small_shape : P.verifying_key_shape := {|
    P.vk_k := 1;
    P.vk_n := 2;
    P.vk_cs_degree := 3;
    P.vk_num_instance_columns := 0;
    P.vk_num_advice_columns := 0;
    P.vk_instance_queries := [];
    P.vk_advice_queries := [];
    P.vk_fixed_queries := [];
    P.vk_gate_polynomials := [];
    P.vk_permutation_columns := [];
    P.vk_lookup_count := 0;
    P.vk_blinding_factors := 0;
    P.vk_quotient_poly_degree := 1
  |}.

  Definition finish_rejection_trace_length : nat :=
    match R.finish small_shape duplicate_assembly (Transcript.init []) with
    | Result.Rejected failure => List.length failure.(Reject.trace)
    | Result.Ok _ | Result.Panicked _ => 0
    end.

  (** x1 and x2 are squeezed before the duplicate-query grouping fails. *)
  Example multiopen_grouping_follows_two_squeezes :
    finish_rejection_trace_length = 2%nat.
  Proof. vm_compute. reflexivity. Qed.

  Definition collision_intermediate : M.intermediate_sets := {|
    M.is_commitments := [];
    M.is_point_sets := [[7]]
  |}.

  Definition collision_compressed : list M.compressed_set := [{|
    M.cs_terms := [];
    M.cs_evals := [5];
    M.cs_next_power := 1
  |}].

  (** [Reference.finish] matches this result and panics before the following
      [squeeze_challenge] that samples x4.  The executable collision witness
      avoids hashing a synthetic transcript in this focused branch test. *)
  Example x3_collision_precedes_x4_squeeze :
    M.expected_msm_eval 3 7 collision_intermediate collision_compressed [9] =
      M.X3CollidesWithOpeningPoint.
  Proof. vm_compute. reflexivity. Qed.
End VerifierCoreTests.
