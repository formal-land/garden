Require Import Garden.Plonky3.M.
Require Import Garden.Plonky3.MExpr.
Require Import Garden.OpenVM.BranchEq.core.

Lemma sum_for_in_zero_to_n_starting_from_always_zero_eq {p} `{Prime p}
    (N : Z) (f : Z -> Z) (start : Z)
    (H_N : 0 <= N)
    (H_f : forall i, 0 <= i < N -> f i = 0) :
  sum_for_in_zero_to_n_starting_from N f (UnOp.from start) =
  UnOp.from start.
Proof.
  unfold sum_for_in_zero_to_n_starting_from.
  replace N with (Z.of_nat (Z.to_nat N)) in H_f by lia.
  set (n := Z.to_nat N) in *; clearbody n.
  set (n' := n) in H_f. assert (H_n' : (n <= n')%nat) by lia; clearbody n'.
  induction n; cbn; intros; autorewrite with field_rewrite; trivial.
  rewrite IHn, H_f by lia.
  now autorewrite with field_rewrite.
Qed.

Definition goldilocks_prime : Z :=
  2^64 - 2^32 + 1.

Definition get_local_with_opcode {NUM_LIMBS : Z}
    (branch_equal_opcode : BranchEqualOpcode.t)
    (local : BranchEqualCoreCols.t NUM_LIMBS Z) :
    BranchEqualCoreCols.t NUM_LIMBS Z :=
  local
    <|
      BranchEqualCoreCols.opcode_beq_flag :=
        match branch_equal_opcode with
        | BranchEqualOpcode.BEQ => 1
        | BranchEqualOpcode.BNE => 0
      end
    |>
    <| BranchEqualCoreCols.opcode_bne_flag :=
      match branch_equal_opcode with
      | BranchEqualOpcode.BEQ => 0
      | BranchEqualOpcode.BNE => 1
      end
    |>.

Definition get_expected_cmp_result {NUM_LIMBS : Z}
    (branch_equal_opcode : BranchEqualOpcode.t)
    (a b : Array.t Z NUM_LIMBS) :
    bool :=
  match branch_equal_opcode with
  | BranchEqualOpcode.BEQ =>
    if Array.Eq.dec a b then
      true
    else
      false
  | BranchEqualOpcode.BNE =>
    if Array.Eq.dec a b then
      false
    else
      true
  end.

Definition get_expected_result {p} `{Prime p} {NUM_LIMBS : Z}
    (self : BranchEqualCoreAir.t NUM_LIMBS)
    (local : BranchEqualCoreCols.t NUM_LIMBS Z)
    (from_pc : Z)
    (expected_cmp_result : bool) :
    AdapterAirContext.t NUM_LIMBS Z :=
  {|
    AdapterAirContext.to_pc :=
      Some (BinOp.add from_pc (
        if expected_cmp_result then
          local.(BranchEqualCoreCols.imm)
        else
          self.(BranchEqualCoreAir.pc_step)
      ));
    AdapterAirContext.reads := [local.(BranchEqualCoreCols.a); local.(BranchEqualCoreCols.b)];
    AdapterAirContext.writes := [];
    AdapterAirContext.instruction := {|
      ImmInstruction.is_valid := 1;
      ImmInstruction.opcode :=
        BinOp.add local.(BranchEqualCoreCols.opcode_bne_flag) self.(BranchEqualCoreAir.offset);
      ImmInstruction.immediate := local.(BranchEqualCoreCols.imm)
    |};
  |}.

(** Determinism *)
Lemma eval_implies `{Prime goldilocks_prime} {NUM_LIMBS : Z}
    (self : BranchEqualCoreAir.t NUM_LIMBS)
    (local' : BranchEqualCoreCols.t NUM_LIMBS Z)
    (from_pc' : Z)
    (branch_equal_opcode : BranchEqualOpcode.t)
    (H_N : 0 <= NUM_LIMBS) :
  let local := get_local_with_opcode branch_equal_opcode (M.map_mod local') in
  let from_pc := M.map_mod from_pc' in
  let expected_cmp_result :=
    get_expected_cmp_result
      branch_equal_opcode
      local.(BranchEqualCoreCols.a)
      local.(BranchEqualCoreCols.b) in
  {{ eval self local from_pc 🔽
    get_expected_result self local from_pc expected_cmp_result,
    local.(BranchEqualCoreCols.cmp_result) = Z.b2z expected_cmp_result
  }}.
Proof.
  intros.
  unfold eval, get_expected_result.
  eapply Run.LetAccumulate with (value := 1) (P1 := True). {
    destruct branch_equal_opcode; cbn;
      eapply Run.Implies; repeat econstructor.
  }
  intros _.
  eapply Run.LetAccumulate. {
    constructor.
  }
  intros _.
  eapply Run.LetAccumulate with (P1 := IsBool.t local.(BranchEqualCoreCols.cmp_result)). {
    apply Run.AssertBool.
  }
  intros H_cmp_result.
  set (cmp_eq :=
    match branch_equal_opcode with
    | BranchEqualOpcode.BEQ => Z.odd local.(BranchEqualCoreCols.cmp_result)
    | BranchEqualOpcode.BNE => negb (Z.odd local.(BranchEqualCoreCols.cmp_result))
    end
  ).
  eapply Run.LetAccumulate with (value := Z.b2z cmp_eq) (P1 := True). {
    rewrite H_cmp_result.
    destruct
      (Z.odd local.(BranchEqualCoreCols.cmp_result)),
      branch_equal_opcode;
      apply Run.Pure.
  }
  intros _.
  eapply Run.LetAccumulate with (P1 :=
    if cmp_eq then
      Equal.t local.(BranchEqualCoreCols.a) local.(BranchEqualCoreCols.b)
    else
      True
  ). {
    eapply Run.Implies. {
      Run.run.
    }
    intros H_for; cbn.
    destruct cmp_eq; cbn; [|trivial].
    intros i H_i.
    pose proof (H_for i H_i) as H_for_i.
    rewrite <- M.sub_zero_equiv.
    autorewrite with field_rewrite in H_for_i.
    rewrite <- H_for_i.
    cbn; unfold UnOp.from; show_equality_modulo.
  }
  intros H_a_b_eq.
  eapply Run.LetAccumulate with (P1 :=
    if cmp_eq then
      True
    else
      ~ (Equal.t local.(BranchEqualCoreCols.a) local.(BranchEqualCoreCols.b))
  ). {
    eapply Run.Implies. {
      repeat constructor.
    }
    intros H_sum; cbn.
    destruct cmp_eq; cbn; [trivial|].
    intro.
    replace (Z.b2z false) with (UnOp.from 0) in H_sum by reflexivity.
    rewrite sum_for_in_zero_to_n_starting_from_always_zero_eq in H_sum;
      try assumption;
      cbn in H_sum;
      [lia|].
    intros.
    replace (BinOp.sub _ _) with 0. 2: {
      symmetry.
      rewrite M.sub_zero_equiv.
      cbn; autorewrite with field_rewrite.
      hauto l: on.
    }
    reflexivity.
  }
  intros H_a_b_neq.
  cbn - [local from_pc].
  autorewrite with field_rewrite.
  assert (local.(BranchEqualCoreCols.cmp_result) = Z.b2z expected_cmp_result) as H_cmp_result_eq. {
    rewrite H_cmp_result; f_equal.
    unfold get_expected_cmp_result, cmp_eq in *.
    destruct branch_equal_opcode, Array.Eq.dec, (Z.odd local.(BranchEqualCoreCols.cmp_result));
      unfold negb in *;
      tauto.
  }
  eapply Run.Implies. {
    eapply Run.Replace. {
      apply Run.Pure.
    }
    f_equal.
    rewrite H_cmp_result_eq.
    now destruct expected_cmp_result; autorewrite with field_rewrite.
  }
  tauto.
Qed.

(** Completeness *)
Lemma eval_complete `{Prime goldilocks_prime} {NUM_LIMBS : Z}
    (self : BranchEqualCoreAir.t NUM_LIMBS)
    (a' : Array.t Z NUM_LIMBS)
    (b' : Array.t Z NUM_LIMBS)
    (imm' : Z)
    (diff_inv_marker' : Array.t Z NUM_LIMBS)
    (from_pc' : Z)
    (branch_equal_opcode : BranchEqualOpcode.t)
    (H_NUM_LIMBS : 0 <= NUM_LIMBS) :
  let a := M.map_mod a' in
  let b := M.map_mod b' in
  let imm := M.map_mod imm' in
  let diff_inv_marker := M.map_mod diff_inv_marker' in
  let from_pc := M.map_mod from_pc' in
  let expected_cmp_result := get_expected_cmp_result branch_equal_opcode a b in
  let local :=
    {|
      BranchEqualCoreCols.a := a;
      BranchEqualCoreCols.b := b;
      BranchEqualCoreCols.cmp_result := Z.b2z expected_cmp_result;
      BranchEqualCoreCols.imm := imm;
      BranchEqualCoreCols.opcode_beq_flag :=
        match branch_equal_opcode with
        | BranchEqualOpcode.BEQ => 1
        | BranchEqualOpcode.BNE => 0
        end;
      BranchEqualCoreCols.opcode_bne_flag :=
        match branch_equal_opcode with
        | BranchEqualOpcode.BEQ => 0
        | BranchEqualOpcode.BNE => 1
        end;
      BranchEqualCoreCols.diff_inv_marker := diff_inv_marker;
    |} in
  forall
    (* We assume a [diff_inv_marker] oracle with the following property *)
    (H_diff_inv_marker :
      if Array.Eq.dec a b then
        (* It can be anything in case of equality *)
        True
      else
        (* Otherwise it is the inverse of the difference in exactly one case, zero elsewhere *)
        exists k, 0 <= k < NUM_LIMBS /\
        forall i, 0 <= i < NUM_LIMBS ->
        if i =? k then
          BinOp.mul (BinOp.sub (a.[i]) (b.[i])) diff_inv_marker.[i] = 1
        else
          diff_inv_marker.[i] = 0
    ),
  {{ eval self local from_pc ✅
    get_expected_result self local from_pc expected_cmp_result
  }}.
Proof.
  intros.
  unfold eval, get_expected_result.
  eapply Complete.Let with (value := 1). {
    cbn.
    destruct branch_equal_opcode; cbn;
      repeat (
        apply Complete.Pure ||
        (apply Complete.AssertZero; reflexivity) ||
        eapply Complete.Let
      ).
  }
  eapply Complete.Let with (value := tt). {
    repeat econstructor.
  }
  eapply Complete.Let with (value := tt). {
    repeat econstructor.
    unfold local; destruct expected_cmp_result; reflexivity.
  }
  set (cmp_eq :=
    match branch_equal_opcode with
    | BranchEqualOpcode.BEQ => expected_cmp_result
    | BranchEqualOpcode.BNE => negb expected_cmp_result
    end
  ).
  eapply Complete.Let with (value := Z.b2z cmp_eq). {
    destruct expected_cmp_result, branch_equal_opcode; cbn;
      apply Complete.Pure.
  }
  eapply Complete.Let with (value := tt). {
    apply Complete.ForInZeroToN.
    intros.
    unfold get_expected_cmp_result in *.
    destruct branch_equal_opcode, Array.Eq.dec as [H_a_b_eq|]; cbn; 
      autorewrite with field_rewrite;
      apply Complete.AssertZero;
      try reflexivity.
    all:
      rewrite M.sub_zero_equiv;
      now apply H_a_b_eq.
  }
  eapply Complete.Let with (value := tt). {
    apply Complete.When.
    intros _.
    apply Complete.AssertZero.
    unfold get_expected_cmp_result in *.
    destruct Array.Eq.dec as [H_a_b_eq | H_a_b_neq]; cbn.
    {
      replace (Z.b2z cmp_eq) with (UnOp.from 1) by now destruct branch_equal_opcode.
      cbn in H_a_b_eq.
      rewrite sum_for_in_zero_to_n_starting_from_always_zero_eq; try reflexivity; try lia; intros.
      set (diff := BinOp.sub _ _).
      replace diff with 0; try reflexivity.
      unfold diff; symmetry.
      rewrite M.sub_zero_equiv.
      hauto lq: on rew: off.
    }
    {
      replace (Z.b2z cmp_eq) with 0 by now destruct branch_equal_opcode.
      set (sum := sum_for_in_zero_to_n_starting_from _ _ _).
      assert (sum = 1). {
        generalize H_NUM_LIMBS, H_diff_inv_marker; clear; intros.
        unfold sum, sum_for_in_zero_to_n_starting_from.
        destruct H_diff_inv_marker as [k [H_k H_diff_inv_marker] ].
        set (f := fun (i : Z) => _).
        assert (H_f :
          forall i, 0 <= i < NUM_LIMBS ->
          f i = if i =? k then 1 else 0
        ). {
          intros i H_i.
          pose proof (H_diff_inv_marker i H_i) as H_diff_inv_marker_i.
          unfold f; destruct (i =? k) eqn:H_i_k; try assumption.
          cbn in H_diff_inv_marker_i.
          rewrite H_diff_inv_marker_i.
          now autorewrite with field_rewrite.
        }
        replace NUM_LIMBS with (Z.of_nat (Z.to_nat NUM_LIMBS)) in H_diff_inv_marker by lia.
        set (N := Z.to_nat NUM_LIMBS).
        replace 1 with (
          if (Z.to_nat k <? N)%nat then
            1
          else
            0
        ) by sauto.
        assert (H_N : (N <= Z.to_nat NUM_LIMBS)%nat) by lia.
        induction N; cbn; [reflexivity|].
        rewrite IHN; [|lia].
        rewrite H_f by lia.
        destruct
          (Z.to_nat k <? N)%nat eqn:?,
          (Z.to_nat k <=? N)%nat eqn:?,
          (Z.of_nat N =? k) eqn:?;
          autorewrite with field_rewrite;
          try reflexivity;
          hauto lb: on.
      }
      hauto q: on.
    }
  }
  cbn.
  autorewrite with field_rewrite.
  destruct expected_cmp_result; autorewrite with field_rewrite; apply Complete.Pure.
Qed.
