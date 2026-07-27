(** * Read-back certificate of the concrete completeness instance

    The free-witness readers reproduce the input record on the generated
    assignment: [read_action_inputs Γtest = inputs_of test_input].  One
    [vm_compute] conversion; leaf file so the run (dominated by the hoisted
    table construction and the specification-side [inputs_of] values) is
    never re-paid while the definition files are edited. *)

Require Import Garden.Orchard.protocol_spec.
Require Import Garden.Orchard.circuit_proof.internal_spec.
Require Import Garden.Orchard.circuit_proof.inputs.
Require Import Garden.Orchard.circuit_completeness.generator.witness_input.
Require Import Garden.Orchard.circuit_completeness.instance.defs.
Require Import Stdlib.ZArith.ZArith.

Global Open Scope Z_scope.

Module OrchardCompletenessInstanceRead.
  Import OrchardActionInputs.
  Import OrchardWitnessInput.
  Import OrchardCompletenessInstanceDefs.

  Lemma read_action_inputs_ok :
    read_action_inputs Γtest = inputs_of test_input.
  Proof.
    vm_cast_no_check
      (@eq_refl OrchardSpec.ActionInputs (inputs_of test_input)).
  Qed.

End OrchardCompletenessInstanceRead.
