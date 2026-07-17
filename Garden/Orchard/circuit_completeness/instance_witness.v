(** * Witness-fact certificate of the concrete completeness instance

    The synthesis program's witness facts ([CellsEqual] / [InstanceIs] /
    [CellIsConstant]) hold on the generated assignment — the copy/constant
    obligations of [Complete.circuit_holds_intro], one [vm_compute] over
    all 2 964 facts. *)

Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.complete.
Require Import Garden.Orchard.columns.
Require Import Garden.Orchard.circuit_completeness.instance_defs.
Require Import Stdlib.Bool.Bool.

Global Open Scope Z_scope.

Module OrchardCompletenessInstanceWitness.
  Import OrchardCompletenessInstanceDefs.

  Lemma witness_facts_ok :
    Complete.check_witness_facts Γtest (Complete.witness_facts facts) = true.
  Proof. vm_cast_no_check (@eq_refl bool true). Qed.

End OrchardCompletenessInstanceWitness.
