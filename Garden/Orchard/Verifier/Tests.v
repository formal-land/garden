(** * Focused tests for the fixed Post-NU6.3 assembly *)

From Stdlib Require Import ZArith Lists.List Bool.
Require Import Garden.Field.Field.
Require Import Garden.Halo2.Verifier.Plonk.
Require Import Garden.Orchard.Verifier.PostNu6_3.
Require Import Garden.Orchard.Verifier.AssemblyData.
Require Import Garden.Orchard.Verifier.AssemblyExpressions.
Require Import Garden.Orchard.Verifier.Assembly.

Import ListNotations.
Local Open Scope Z_scope.

Module OrchardVerifierTests.
  Module P := PlonkVerifier.
  Module O := OrchardPostNu63.
  Module A := Garden.Orchard.Verifier.AssemblyData.
  Module E := Garden.Orchard.Verifier.AssemblyExpressions.

  (** Expression leaves use registration positions, not physical columns. *)
  Example advice_rotation_query_index :
    O.query_index_from (9, 1) O.advice_query_pairs 0 = Some 10%nat.
  Proof. reflexivity. Qed.

  Example fixed_table_query_index :
    O.query_index_from (0, 0) O.fixed_query_pairs 0 = Some 1%nat.
  Proof. reflexivity. Qed.

  Example concrete_query_table_sizes :
    List.length O.shape.(P.vk_instance_queries) = 1%nat /\
    List.length O.shape.(P.vk_advice_queries) = 25%nat /\
    List.length O.shape.(P.vk_fixed_queries) = 29%nat /\
    List.length O.shape.(P.vk_permutation_columns) = 15%nat.
  Proof. vm_compute. repeat split; reflexivity. Qed.

  (** For three actions, each allocation range starts immediately after the
      preceding Rust-owned commitment vector. *)
  Example allocation_ranges_are_disjoint_and_contiguous :
    A.advice_base 3 = 3%nat /\
    A.lookup_permuted_base 3 = 33%nat /\
    A.permutation_product_base 3 = 51%nat /\
    A.lookup_product_base 3 = 60%nat /\
    A.random_base 3 = 69%nat /\
    A.q_prime_id 3 = 122%nat.
  Proof. vm_compute. repeat split; reflexivity. Qed.

  (** Batch inversion in [l_i_range] leaves the zero denominator at zero. *)
  Example lagrange_zero_denominator_is_zero :
    E.lagrange_eval 1 1 0 = 0.
  Proof. vm_compute. reflexivity. Qed.

  Example non_boolean_public_flag_is_rejected :
    O.validate_actions_from 0 [[0; 0; 0; 0; 0; 0; 0; 1; 2; 0]] =
      Some (O.NonBooleanActionFlag 0 8 2).
  Proof. vm_compute. reflexivity. Qed.

  Example invalid_action_width_is_rejected :
    O.validate_actions_from 0 [[0; 0; 0; 0; 0; 0; 0; 0; 0]] =
      Some (O.InvalidActionWidth 0 10 9).
  Proof. vm_compute. reflexivity. Qed.

  Example noncanonical_action_scalar_is_rejected :
    O.validate_actions_from 0
      [[Primes.pallas_p; 0; 0; 0; 0; 0; 0; 1; 1; 0]] =
      Some (O.NonCanonicalActionScalar 0 0 Primes.pallas_p).
  Proof. vm_compute. reflexivity. Qed.

  Example invalid_proof_byte_is_rejected :
    O.first_invalid_byte 0 [0; 255; 256; 1] =
      Some (O.InvalidProofByte 2 256).
  Proof. vm_compute. reflexivity. Qed.
End OrchardVerifierTests.
