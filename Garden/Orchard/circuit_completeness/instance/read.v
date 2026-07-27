(** * Specification side of the read-back certificate

    The specification-side values of the concrete instance reduce to the
    pinned [test_action_inputs]: the companion of
    [OrchardCompletenessInstanceReadCells.read_action_inputs_lit], which
    reduces the reader side to the same literal.  [instance/cert.v] composes
    the two into [read_action_inputs Γtest = inputs_of test_input].

    This side mentions neither [Γtest] nor the hoisted table record, so it
    shares no computation with the certificates of [instance/certs.v] and
    stands in its own file to compile in parallel with them.  Its cost is
    the specification's own arithmetic: the 32-layer Merkle fold of
    [anchor_of_leaf] over the note commitment, plus the commitments
    themselves. *)

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

  Lemma inputs_of_lit :
    inputs_of test_input = test_action_inputs.
  Proof.
    vm_cast_no_check
      (@eq_refl OrchardSpec.ActionInputs test_action_inputs).
  Qed.

End OrchardCompletenessInstanceRead.
