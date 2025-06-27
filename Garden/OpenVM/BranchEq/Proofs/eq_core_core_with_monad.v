Require Import ZArith.
Require Import List.
Import ListNotations.

(* TODO: design examples to prove initially they are identical:
  1. let* _ := pure tt in pure tt
  2. let* _ := assert_zero 0 in pure tt
  3. let* _ := assert_bool 1 in pure tt
*)
Module MBuilder_test.
  Require Import Garden.OpenVM.BranchEq.M.MBuilder.
  Locate M.

  Definition test1 := let* _ := M.Pure tt in M.Pure tt.
  Definition test2 := let* _ := assert_zero 0%Z in M.Pure tt.
  Definition teste := let* _ := assert_bool 1%Z in M.Pure tt.
End MBuilder_test.

Module MLessEffects_test.
  Require Import Garden.Plonky3.MLessEffects.
  Definition M := MLessEffects.M.t.

  Definition test1 := let* _ := M.Pure tt in M.Pure tt.
  Definition test2 := let* _ := assert_zero 0%Z in M.Pure tt.
  (* TODO: fix this *)
  Definition test3 := let* _ := assert_bool 0%Z in M.Pure tt.
End MLessEffects_test.