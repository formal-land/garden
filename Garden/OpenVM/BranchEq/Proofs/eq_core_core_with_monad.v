Require Import ZArith.
Require Import List.
Import ListNotations.

Require Garden.OpenVM.BranchEq.M.MBuilder.
Require Garden.Plonky3.MLessEffects.

(* TODO: design examples to prove initially they are identical:
  1. let* _ := pure tt in pure tt
  2. let* _ := assert_zero 0 in pure tt
  3. let* _ := assert_bool 1 in pure tt
*)
Module MBuilder_test.
  Import Garden.OpenVM.BranchEq.M.MBuilder.

  Definition test1 := let*B _ := [[ tt ]]* in [[ tt ]]*.
  Theorem eq_builder_test1 : forall (output : unit) (b1 b2 : Builder.t),
    {{ [[ test1 ]]* | b1 🔽 output | b2 }}* ->
    b1 = b2. Admitted.
  Definition test2 (x : Z) := let*B _ := assert_zero x in M.Pure tt.
  Definition test3 (x : Z) := let*B _ := assert_bool x in M.Pure tt.
  Definition test4 := 
    let f := fun (x : Z) => (x + x) in
    [[ f 4 ]]*.
End MBuilder_test.

Module MLessEffects_test.
  Import Garden.Plonky3.MLessEffects.

  Definition test1 := let* _ := M.Pure tt in M.Pure tt.
  Definition test2 (x : Z) := let* _ := assert_zero x in M.Pure tt.
  Definition test3 {p} `{Prime p} (x : Z) := let* _ := assert_bool x in M.Pure tt.
  Definition test4 := 
    let f := fun (x : Z) => (x + x) in
    [[ f 4 ]].
End MLessEffects_test.

Module Equality.
  Import Garden.OpenVM.BranchEq.M.MBuilder.
  Import Garden.Plonky3.MLessEffects. 
  
  Theorem eq_builder_test1 : forall (output : unit) (b1 b2 : Builder.t),
    {{ [[ MBuilder_test.test1 ]]* | b1 🔽 output | b2 }}* ->
    b1 = b2. Admitted.
  Definition test1_notation := forall (o1 o2 : unit) (b1 b2 : Builder.t),
  {{ [[ MBuilder_test.test1 ]]* | b1 🔽 o1 | b2 }}*.

  (* Required for dependent destruction *)
  Require Import Coq.Program.Equality.

  Theorem eq_output_test1 : forall (o1 o2 : unit) (b1 b2 : Builder.t),
    {{ [[ MBuilder_test.test1 ]]* | b1 🔽 o1 | b2 }}* ->
    {{ [[ MLessEffects_test.test1 ]] 🔽 o2, True }} ->
    o1 = o2.
  Admitted.

  (* 
  Theorem eq_output_test2 : forall (x1 x2 : Z) (o1 o2 : unit),
    x1 = x2 ->
    {{ MBuilder_test.test2 x1 | b 🔽 o1 | b }} ->
    {{ MLessEffects_test.test2 x2 🔽 o2 , True }} ->
    o1 = o2.
  *)

  Theorem eq_test4 : forall (o1 o2 : Z) (b1 b2 : Builder.t),
  {{ [[ MBuilder_test.test4 ]]* | b1 🔽 o1 | b2 }}* ->
  {{ [[ MLessEffects_test.test4 ]] 🔽 o2, True }} ->
  o1 = o2.
  Proof.
    intros o1 o2 b1 b2 runB4 runLE4.
    cbv in runB4, runLE4.
    (* Prove o1 = 8 *)
    inversion runB4.
    dependent destruction H1.
    dependent destruction H2.
    (* TODO: Prove o2 = 8 *)
    inversion runLE4.
    dependent destruction H1.
    dependent destruction H3.
    (* Stuck *)
    injection x.
    Abort.

    (* apply (MBuilder.Run.Pure b1 8) in runB4. *)
  (* Admitted. *)

End Equality.