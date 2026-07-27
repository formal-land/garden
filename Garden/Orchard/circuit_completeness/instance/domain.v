(** * Domain certificates of the concrete completeness instance

    The [vm_compute] certificates placing [test_input] in the completeness
    domain: the §4.18.4 typing/ownership envelope ([test_input_valid]) and
    the exceptional-case exclusions — the Merkle chain, the three Sinsemilla
    hash messages and the variable-base ladder, each one linear accumulator
    pass.  [instance/cert.v] assembles [test_input_nondegenerate] from the
    five nondegeneracy certificates. *)

Require Import Garden.Orchard.protocol_spec.
Require Import Garden.Orchard.circuit_proof.internal_spec.
Require Import Garden.Orchard.circuit_proof.inputs.
Require Import Garden.Orchard.circuit_completeness.generator.witness_input.
Require Import Garden.Orchard.circuit_completeness.instance.defs.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Bool.Bool.

Global Open Scope Z_scope.

Module OrchardCompletenessInstanceDomain.
  Import OrchardActionInputs.
  Import OrchardWitnessInput.
  Import OrchardCompletenessInstanceDefs.

  Lemma test_input_valid_b : valid_b test_input = true.
  Proof. vm_cast_no_check (@eq_refl bool true). Qed.

  Lemma test_input_valid : valid test_input.
  Proof. exact (valid_b_sound test_input test_input_valid_b). Qed.

  Lemma merkle_nondeg_cert : merkle_nondeg_b test_input = true.
  Proof. vm_cast_no_check (@eq_refl bool true). Qed.

  Lemma nc_old_nondeg_cert :
    sins_nondeg_go
      (OrchardSpec.note_commit_q orchard_circuit_params)
      (note_commit_old_words test_input) = true.
  Proof. vm_cast_no_check (@eq_refl bool true). Qed.

  Lemma nc_new_nondeg_cert :
    sins_nondeg_go
      (OrchardSpec.note_commit_q orchard_circuit_params)
      (note_commit_new_words test_input) = true.
  Proof. vm_cast_no_check (@eq_refl bool true). Qed.

  Lemma civk_nondeg_cert :
    sins_nondeg_go
      (OrchardSpec.commit_ivk_q orchard_circuit_params)
      (commit_ivk_words test_input) = true.
  Proof. vm_cast_no_check (@eq_refl bool true). Qed.

  (** The variable-base clause: one pass down the 251 incomplete bit
      indices, two group additions and one incomplete addition per step. *)
  Lemma mul_chain_cert : mul_chain_b test_input = true.
  Proof. vm_cast_no_check (@eq_refl bool true). Qed.

End OrchardCompletenessInstanceDomain.
