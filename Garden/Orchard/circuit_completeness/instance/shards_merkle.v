(** * Merkle-family shard certificates of the completeness instance

    Every enabled selector point of the 32 Merkle layer families passes
    [check_point] on the generated assignment.  One [vm_compute] run: the
    hoisted table record is forced once, and the ≈ 2 000 points read it by
    lookups.  Leaf file per the certificate cost discipline. *)

Require Import Garden.Orchard.circuit_completeness.instance.defs.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Lists.List.

Import ListNotations.
Global Open Scope Z_scope.

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
