Require Import Garden.Plonky3.M.
Require Import Garden.Brevis.compiler.word.
Require Import Garden.Brevis.machine.builder.range_check.

Module AddGadget.
  Record t : Set := {
    value : Word.t;
    carry : Array.t Z 3;
  }.

  Global Instance IsMapMod {p} `{Prime p} : MapMod t := {
    map_mod x := {|
      value := M.map_mod x.(value);
      carry := M.map_mod x.(carry);
    |};
  }.

  Global Instance IsGenerate : MGenerate.C t := {
    generate :=
      [[
        {|
          value := MGenerate.generate (||);
          carry := MGenerate.generate (||);
        |}
      ]];
  }.

  Definition eval {p} `{Prime p}
      (a b : Word.t)
      (cols : t)
      (is_real : Z) :
      M.t unit :=
    let one := 1 in
    let base := 256 in

    let* _ := M.when is_real (
      let overflow_0 := a.[0] +F b.[0] -F cols.(value).[0] in
      let overflow_1 := a.[1] +F b.[1] -F cols.(value).[1] +F cols.(carry).[0] in
      let overflow_2 := a.[2] +F b.[2] -F cols.(value).[2] +F cols.(carry).[1] in
      let overflow_3 := a.[3] +F b.[3] -F cols.(value).[3] +F cols.(carry).[2] in

      let* _ := M.assert_either_zero overflow_0 (overflow_0 -F base) in
      let* _ := M.assert_either_zero overflow_1 (overflow_1 -F base) in
      let* _ := M.assert_either_zero overflow_2 (overflow_2 -F base) in
      let* _ := M.assert_either_zero overflow_3 (overflow_3 -F base) in

      (* let* _ := M.assert_either_zero cols.(carry).[0] (overflow_0 -F base) in
      let* _ := M.assert_either_zero cols.(carry).[1] (overflow_1 -F base) in
      let* _ := M.assert_either_zero cols.(carry).[2] (overflow_2 -F base) in *)

      (* let* _ := M.assert_either_zero (cols.(carry).[0] -F one) overflow_0 in
      let* _ := M.assert_either_zero (cols.(carry).[1] -F one) overflow_1 in
      let* _ := M.assert_either_zero (cols.(carry).[2] -F one) overflow_2 in

      let* _ := M.assert_bool cols.(carry).[0] in
      let* _ := M.assert_bool cols.(carry).[1] in
      let* _ := M.assert_bool cols.(carry).[2] in
      let* _ := M.assert_bool is_real in *)

      M.Pure tt
    ) in
    (* let* _ :=
      let* _ := slice_range_check_u8 a is_real in
      let* _ := slice_range_check_u8 b is_real in
      let* _ := slice_range_check_u8 cols.(value) is_real in
      M.pure tt in *)
    M.Pure tt.

  Module ForEachN.
    Fixpoint t_nat (N : nat) (P : Z -> Prop) : Prop :=
      match N with
      | O => True
      | S N => P (Z.of_nat N) /\ t_nat N P
      end.

    Definition t (N : Z) (P : Z -> Prop) : Prop :=
      t_nat (Z.to_nat N) P.

    Lemma implies_forall_nat (N : nat) (P : Z -> Prop)
        (H_P : t_nat N P) :
      forall i, 0 <= i < Z.of_nat N ->
      P i.
    Proof.
      induction N; cbn in *; intros.
      { lia. }
      { assert (0 <= i < Z.of_nat N \/ i = Z.of_nat N) as [] by lia.
        all: best.
      }
    Qed.

    Lemma implies_forall (N : Z) (P : Z -> Prop)
      (H_P : ForEachN.t N P) :
      forall i, 0 <= i < N ->
      P i.
    Proof.
      assert (N < 0 \/ N = Z.of_nat (Z.to_nat N)) as [? | H_N] by lia.
      { lia. }
      { rewrite H_N.
        now apply implies_forall_nat.
      }
    Qed.
  End ForEachN.

  Lemma eval_correct {p} `{Prime p} (H_p : 2 ^ 9 < p)
      (a' b' : Z)
      (cols' : t)
      (* (is_real : bool) *)
      (H_a : 0 <= a' < 2 ^ 32)
      (H_b : 0 <= b' < 2 ^ 32) :
    let a := Word.of_Z a' in
    let b := Word.of_Z b' in
    let cols := M.map_mod cols' in
    let is_real := Z.b2z true in
    {{ eval a b cols is_real 🔽
      tt,
      cols.(value) =F Word.of_Z (a' + b')
    }}.
  Proof.
    unfold eval.
    eapply Run.Implies. {
      Run.run.
    }
    intros H_post.
    destruct H_post as [H_post _].
    epose proof (H_post ltac:(cbn; lia)) as H_post'; clear H_post.
    cbn in *; unfold Pos.to_nat in *; cbn in *.
    set (col0 := UnOp.from cols'.(value) .[ 0]) in *.
    set (col1 := UnOp.from cols'.(value) .[ 1]) in *.
    set (col2 := UnOp.from cols'.(value) .[ 2]) in *.
    set (col3 := UnOp.from cols'.(value) .[ 3]) in *.
    set (carry0 := cols'.(carry).[0]) in *.
    set (carry1 := cols'.(carry).[1]) in *.
    set (carry2 := cols'.(carry).[2]) in *.
    assert (0 <= col0 < 2 ^ 8) by admit.
    assert (0 <= col1 < 2 ^ 8) by admit.
    assert (0 <= col2 < 2 ^ 8) by admit.
    assert (0 <= col3 < 2 ^ 8) by admit.
    (* assert (0 <= carry0 < 2) by admit.
    assert (0 <= carry1 < 2) by admit.
    assert (0 <= carry2 < 2) by admit. *)
    apply ForEachN.implies_forall.
    repeat constructor.
    all: cbn; unfold Pos.to_nat; cbn.
    all: fold col0 col1 col2 col3.
    all: unfold BinOp.add, BinOp.sub in *.
    all: assert (H_foo : forall z, z mod p = z) by admit.
    all: repeat rewrite H_foo in * |-; clear H_foo.
    Time 4: lia.
    Time 3: lia.
    4: {
      repeat destruct H_post' as [? H_post'].
      replace carry0 with 0 in * by admit.
      replace carry1 with 0 in * by admit.
      replace carry2 with 0 in * by admit.
      Time lia.
      repeat match goal with
      | H : _ |- _ => clear H
      end.
      lia.
      destruct H_post' as [? _].
      lia.
    }
    Time 4: lia.
    all: lia.

    Search List.seq.
    intros i. 
    rewrite <- List.in_seq.
    clearbody col0 col1 col2 col3 carry0 carry1 carry2.
    repeat rewrite M.mul_zero_implies_zero in *.
    autorewrite with field_rewrite in *.
    unfold UnOp.from in *.
    rewrite (M.from_small carry0) in * by (clear H_post'; lia).
    rewrite (M.from_small carry1) in * by (clear H_post'; lia).
    rewrite (M.from_small carry2) in * by (clear H_post'; lia).
    unfold BinOp.add, BinOp.sub in *.
    assert (H_foo : forall z, z mod p = z) by admit.
    repeat rewrite H_foo in * |-.
    clear H_foo.
    intros.
    replace i with 3 by admit.
    replace (cols'.(value) .[ 3] mod p) with col3 by admit.
    cbn; unfold Pos.to_nat; cbn.
    Time lia.
    replace i with 0 by admit.
    replace (cols'.(value) .[ 0] mod p) with col0 by admit.
    cbn; unfold Pos.to_nat; cbn.
    Time lia.
    replace i with 1 by admit.
    replace (cols'.(value) .[ 1] mod p) with col1 by admit.
    cbn; unfold Pos.to_nat; cbn.
    Time lia.
    replace i with 2 by admit.
    replace (cols'.(value) .[ 2] mod p) with col2 by admit.
    cbn; unfold Pos.to_nat; cbn.
    Time lia.
    repeat (match goal with | H : _ /\ _ |- _ => destruct H end).
    rewrite M.mul_zero_implies_zero in *.
    autorewrite with field_rewrite in *.
    rewrite M.sub_zero_equiv in *.
    destruct H2 as [H2|H2].
    {
      assert (0 <= UnOp.from cols'.(value) .[ 0] < 2 ^ 8) by admit.
    assert (UnOp.from cols'.(value) .[ 0] <)
    intros.
    replace i with 0 by admit.
    cbn.
    repeat (match goal with | H : _ /\ _ |- _ => destruct H end).
    rewrite M.mul_zero_implies_zero in *.
    autorewrite with field_rewrite in *.
    rewrite M.sub_zero_equiv in *.
    destruct H2 as [H2|H2].
    {
      assert (0 <= UnOp.from cols'.(value) .[ 0] < 2 ^ 8) by admit.
      rewrite <- H2 in *.
      autorewrite with field_rewrite in *.
      unfold "+F" in *.
      revert H_p H21; clear; intros.
      rewrite Z.mod_small in * by lia.
      lia.
    }
    {
      assert (0 <= UnOp.from cols'.(value) .[ 0] < 2 ^ 8) by admit.
      assert (a' mod 256 +F b' mod 256 -F 256 mod p = cols'.(value) .[ 0]) by admit.
      rewrite <- H22 in *.
      revert H_p H21; clear; intros.
      autorewrite with field_rewrite in *.
      unfold "+F", BinOp.sub in *.
      repeat rewrite M.from_small in * by lia.
      rewrite (M.from_small 256) in * by lia.
      lia.
    }
    {

    }
    intuition.
  Qed.
End AddGadget.
