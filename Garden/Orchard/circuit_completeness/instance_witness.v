(** * Witness-fact certificate of the concrete completeness instance

    The synthesis program's witness facts ([CellsEqual] / [InstanceIs] /
    [CellIsConstant]) hold on the generated assignment — the copy/constant
    obligations of [Complete.circuit_holds_intro].

    Admitted: 84 of the 2 964 facts read cells of the incomplete advice
    sub-generators and compute [false] — the copies between the stubbed
    [NoteCommit]/[Commit^ivk] decomposition and canonicity subregions and
    their (generated) sources, the variable-base ladder's base-point copies
    at the interior rows, and the [NoteCommit] range regions'
    [CellIsConstant] bitshift constants.  They are exactly the witness-fact
    face of the generator gaps behind the Admitted shard certificates of
    [instance_shards_blocked.v]; the sub-generator completion (the C2
    assembly step) discharges both. *)

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
  Admitted.

End OrchardCompletenessInstanceWitness.
