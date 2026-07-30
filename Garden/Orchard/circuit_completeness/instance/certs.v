(** * The [vm_compute] certificates over the generated assignment

    Every certificate of the concrete completeness instance whose subject is
    [Γtest]: the enabled selector points of all region families, the
    copy/constant witness facts, and the reader side of the read-back
    equation.

    They share one file because they share one computation.  [Γtest] is a
    global constant, so the virtual machine evaluates it — and with it the
    hoisted table record [tables_of test_input] — once per compilation unit
    and reuses the result across every later [vm_compute] in the same file;
    the second and third certificates below cost no measurable time at all.
    Split across separate leaf files, each would rebuild the record from
    scratch, which is the single most expensive computation in the
    completeness instance.  Certificates whose subject is [test_input]
    rather than [Γtest] share nothing with these and belong in
    [instance/domain.v]; the specification side of the read-back equation
    likewise stands alone in [instance/read.v], so that it compiles in
    parallel with this file. *)

Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.complete.
Require Import Garden.Orchard.columns.
Require Import Garden.Orchard.protocol_spec.
Require Import Garden.Orchard.circuit_proof.internal_spec.
Require Import Garden.Orchard.circuit_proof.inputs.
Require Import Garden.Orchard.circuit_completeness.generator.witness_input.
Require Import Garden.Orchard.circuit_completeness.instance.defs.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Lists.List.

Import ListNotations.
Global Open Scope Z_scope.

(** ** Merkle-family shards

    Every enabled selector point of the 32 Merkle layer families passes
    [check_point]: the ≈ 2 000 points read the hoisted record by lookups. *)
Module OrchardCompletenessInstanceShardsMerkle.
  Import OrchardCompletenessInstanceDefs.

  Lemma merkle_shards_ok :
    List.forallb check_point
      (shard_in
        [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16;
         17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31; 32])
      = true.
  Proof. vm_cast_no_check (@eq_refl bool true). Qed.

End OrchardCompletenessInstanceShardsMerkle.

(** ** Witness-input / Poseidon / fixed-base shards *)
Module OrchardCompletenessInstanceShardsMisc.
  Import OrchardCompletenessInstanceDefs.

  (** Families 0 ([WitnessInput]), 33 ([Poseidon]), 41 ([GadgetLocal],
      empty) and 42 (the [QOrchard] checks row, the four post-NU6.3
      cross-address rows, and the new-note witness rows). *)
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

(** ** Ladder / decomposition / canonicity shards

    The four region families whose advice cells come from the dedicated
    table layers:

    - family 37 ([AddressIntegrity]): the 137-row variable-base
      double-and-add ladder and its three overflow-check regions, read off
      the hoisted ladder record ([tables_vb.v]);
    - family 38 ([Commit^ivk]): the message-piece, range-check,
      canonicity-lookup and canonicity-gate subregions, read off the
      bit-slice cell layer ([tables_nc.v]) over the packed message
      [ak_x + nk·2^255];
    - families 39/40 (old/new [NoteCommit]): the hash, blinding-leg,
      message-piece, input-decomposition, y-canonicity, range-check and
      canonicity-lookup subregions, read off the same bit-slice layer over
      the packed §5.4.8.4 note message. *)
Module OrchardCompletenessInstanceShardsBlocked.
  Import OrchardCompletenessInstanceDefs.

  (** [AddressIntegrity]: the variable-base ladder and overflow block. *)
  Lemma shard_37_ok :
    List.forallb check_point (shard_in [37]) = true.
  Proof. vm_cast_no_check (@eq_refl bool true). Qed.

  (** [Commit^ivk]: the decomposition and canonicity subregions. *)
  Lemma shard_38_ok :
    List.forallb check_point (shard_in [38]) = true.
  Proof. vm_cast_no_check (@eq_refl bool true). Qed.

  (** Old [NoteCommit]: the hash, decomposition and canonicity subregions. *)
  Lemma shard_39_ok :
    List.forallb check_point (shard_in [39]) = true.
  Proof. vm_cast_no_check (@eq_refl bool true). Qed.

  (** New [NoteCommit]: the hash, decomposition and canonicity subregions. *)
  Lemma shard_40_ok :
    List.forallb check_point (shard_in [40]) = true.
  Proof. vm_cast_no_check (@eq_refl bool true). Qed.

End OrchardCompletenessInstanceShardsBlocked.

(** ** Witness facts

    The synthesis program's witness facts ([CellsEqual] / [InstanceIs] /
    [CellIsConstant]) hold on the generated assignment — the copy/constant
    obligations of [Complete.circuit_holds_intro], over all 3 004 facts. *)
Module OrchardCompletenessInstanceWitness.
  Import OrchardCompletenessInstanceDefs.

  Lemma witness_facts_ok :
    Complete.check_witness_facts Γtest (Complete.witness_facts facts) = true.
  Proof. vm_cast_no_check (@eq_refl bool true). Qed.

End OrchardCompletenessInstanceWitness.

(** ** The reader side of the read-back equation

    The free-witness readers on the generated assignment reduce to the
    pinned [test_action_inputs].  Certifying against that literal rather
    than against [inputs_of test_input] keeps the specification side out of
    this conversion entirely: comparing the two computed sides directly
    evaluates [inputs_of test_input] a second time, since it stands on both
    sides of the checked cast. *)
Module OrchardCompletenessInstanceReadCells.
  Import OrchardActionInputs.
  Import OrchardWitnessInput.
  Import OrchardCompletenessInstanceDefs.

  Lemma read_action_inputs_lit :
    read_action_inputs Γtest = test_action_inputs.
  Proof.
    vm_cast_no_check
      (@eq_refl OrchardSpec.ActionInputs test_action_inputs).
  Qed.

End OrchardCompletenessInstanceReadCells.
