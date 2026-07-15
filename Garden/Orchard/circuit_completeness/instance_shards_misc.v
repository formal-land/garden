(** * Witness-input / Poseidon / fixed-base shard certificates

    Every enabled selector point of the witness-input, Poseidon, gadget-local
    and Orchard-checks families ([misc_shards_ok]) and of the value-commitment,
    nullifier and spend-authority families ([fixed_shards_ok]) passes
    [check_point] on the generated assignment.  Two [vm_compute] runs; leaf
    file per the certificate cost discipline. *)

Require Import Garden.Orchard.circuit_completeness.instance_defs.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Lists.List.

Import ListNotations.
Global Open Scope Z_scope.

Module OrchardCompletenessInstanceShardsMisc.
  Import OrchardCompletenessInstanceDefs.

  (** Families 0 ([WitnessInput]), 33 ([Poseidon]), 41 ([GadgetLocal],
      empty) and 42 (the [QOrchard] checks row and the new-note witness
      rows). *)
  Lemma misc_shards_ok :
    List.forallb check_point (shard_in [0; 33; 41; 42]) = true.
  Proof. vm_cast_no_check (@eq_refl bool true). Qed.

  (** Families 34 ([ValueCommitment]), 35 ([Nullifier]) and 36
      ([SpendAuthority]): the fixed-base legs, their range checks, the
      canonicity probes and the complete additions. *)
  Lemma fixed_shards_ok :
    List.forallb check_point (shard_in [34; 35; 36]) = true.
  Proof. vm_cast_no_check (@eq_refl bool true). Qed.

End OrchardCompletenessInstanceShardsMisc.
