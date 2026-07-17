(** * Ladder / decomposition / canonicity shard certificates of the
    completeness instance

    The four region families whose advice cells come from the dedicated
    table layers — one [vm_compute] certificate per family:

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

Require Import Garden.Orchard.circuit_completeness.instance_defs.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Lists.List.

Import ListNotations.
Global Open Scope Z_scope.

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
