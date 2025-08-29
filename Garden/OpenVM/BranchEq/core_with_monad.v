Require Import Garden.Plonky3.M.
Require Import Garden.Plonky3.MExpr.

(*
pub struct ImmInstruction<T> {
    pub is_valid: T,
    pub opcode: T,
    pub immediate: T,
}
*)
Module ImmInstruction.
  Record t {T : Set} : Set := {
    is_valid : T;
    opcode : T;
    immediate : T;
  }.
  Arguments t : clear implicits.

  Definition map {T1 T2 : Set} (f : T1 -> T2) (self : t T1) : t T2 := {|
    ImmInstruction.is_valid := f self.(ImmInstruction.is_valid);
    ImmInstruction.opcode := f self.(ImmInstruction.opcode);
    ImmInstruction.immediate := f self.(ImmInstruction.immediate);
  |}.
End ImmInstruction.

(*
pub struct AdapterAirContext<T, I: VmAdapterInterface<T>> {
  pub to_pc: Option<T>,
  pub reads: I::Reads,
  pub writes: I::Writes,
  pub instruction: I::ProcessedInstruction,
}
*)
(* TODO: move it to another file, as this is actually related to `integration_api.rs` *)
Module AdapterAirContext.
  Record t {NUM_LIMBS : Z} {T : Set} : Set := {
    to_pc : option T;
    (* I::Reads: From<[[AB::Expr; NUM_LIMBS]; 2]>, *)
    reads : list (Array.t T NUM_LIMBS);
    (* I::Writes: Default, *)
    writes : list (Array.t T NUM_LIMBS);
    (* I::ProcessedInstruction: From<ImmInstruction<AB::Expr>>, *)
    instruction : ImmInstruction.t T;
  }.
  Arguments t : clear implicits.

  Definition map {NUM_LIMBS : Z} {T1 T2 : Set} (f : T1 -> T2) (self : t NUM_LIMBS T1) :
      t NUM_LIMBS T2 :=
  {|
    AdapterAirContext.to_pc := option_map f self.(AdapterAirContext.to_pc);
    AdapterAirContext.reads := List.map (Array.map f) self.(AdapterAirContext.reads);
    AdapterAirContext.writes := List.map (Array.map f) self.(AdapterAirContext.writes);
    AdapterAirContext.instruction := ImmInstruction.map f self.(AdapterAirContext.instruction);
  |}.

  Global Instance AdapterAirContextIsEval {NUM_LIMBS : Z} {T : Set} `{Eval.C T Z} :
      Eval.C (t NUM_LIMBS T) (t NUM_LIMBS Z) := {
    eval p _ env self := map (Eval.eval env) self;
  }.
End AdapterAirContext.

(* TODO: from `instructions.rs`, move there *)
(*
pub enum BranchEqualOpcode {
    BEQ,
    BNE,
}
*)
Module BranchEqualOpcode.
  Inductive t : Set :=
    | BEQ
    | BNE.
End BranchEqualOpcode.

(*
pub struct BranchEqualCoreCols<T, const NUM_LIMBS: usize> {
  pub a: [T; NUM_LIMBS],
  pub b: [T; NUM_LIMBS],

  pub cmp_result: T,
  pub imm: T,

  pub opcode_beq_flag: T,
  pub opcode_bne_flag: T,

  pub diff_inv_marker: [T; NUM_LIMBS],
}
*)
Module BranchEqualCoreCols.
  Record t {NUM_LIMBS : Z} {T : Set} : Set := {
    a : Array.t T NUM_LIMBS;
    b : Array.t T NUM_LIMBS;
    cmp_result : T;
    imm : T;
    opcode_beq_flag : T;
    opcode_bne_flag : T;
    diff_inv_marker : Array.t T NUM_LIMBS;
  }.
  Arguments t : clear implicits.

  Definition map {NUM_LIMBS : Z} {T1 T2 : Set} (f : T1 -> T2) (self : t NUM_LIMBS T1) :
      t NUM_LIMBS T2 :=
  {|
    BranchEqualCoreCols.a := Array.map f self.(BranchEqualCoreCols.a);
    BranchEqualCoreCols.b := Array.map f self.(BranchEqualCoreCols.b);
    BranchEqualCoreCols.cmp_result := f self.(BranchEqualCoreCols.cmp_result);
    BranchEqualCoreCols.imm := f self.(BranchEqualCoreCols.imm);
    BranchEqualCoreCols.opcode_beq_flag := f self.(BranchEqualCoreCols.opcode_beq_flag);
    BranchEqualCoreCols.opcode_bne_flag := f self.(BranchEqualCoreCols.opcode_bne_flag);
    BranchEqualCoreCols.diff_inv_marker := Array.map f self.(BranchEqualCoreCols.diff_inv_marker);
  |}.

  Global Instance map_mod {p} `{Prime p} {NUM_LIMBS : Z} : MapMod (t NUM_LIMBS Z) := {
    map_mod := BranchEqualCoreCols.map map_mod;
  }.
End BranchEqualCoreCols.

(*
pub struct BranchEqualCoreAir<const NUM_LIMBS: usize> {
  offset: usize,
  pc_step: u32,
}
*)
Module BranchEqualCoreAir.
  Record t {NUM_LIMBS : Z} : Set := {
    offset : Z;
    pc_step : Z;
  }.
  Arguments t : clear implicits.
End BranchEqualCoreAir.

Fixpoint sum_for_in_zero_to_n_starting_from_aux {p} `{Prime p} (n : nat) (f : Z -> Z) (start : Z) :
    Z :=
  match n with
  | O => start
  | S n => BinOp.add (sum_for_in_zero_to_n_starting_from_aux n f start) (f (Z.of_nat n))
  end.

Definition sum_for_in_zero_to_n_starting_from {p} `{Prime p} (n : Z) (f : Z -> Z) (start : Z) : Z :=
  sum_for_in_zero_to_n_starting_from_aux (Z.to_nat n) f start.

Definition eval {p} `{Prime p} {NUM_LIMBS : Z}
    (self : BranchEqualCoreAir.t NUM_LIMBS)
    (local : BranchEqualCoreCols.t NUM_LIMBS Z)
    (from_pc : Z) :
    M.t (AdapterAirContext.t NUM_LIMBS Z) :=
  let flags : list Z := [
    local.(BranchEqualCoreCols.opcode_beq_flag);
    local.(BranchEqualCoreCols.opcode_bne_flag)
  ] in

  let* is_valid : Z :=
    M.List.fold_left
      (fun acc flag =>
        let* _ := M.assert_bool flag in
        M.pure (BinOp.add acc flag)
      )
      Z.zero
      flags in
  let* _ := M.assert_bool is_valid in
  let* _ := M.assert_bool local.(BranchEqualCoreCols.cmp_result) in

  let a : Array.t Z NUM_LIMBS := local.(BranchEqualCoreCols.a) in
  let b : Array.t Z NUM_LIMBS := local.(BranchEqualCoreCols.b) in
  let inv_marker : Array.t Z NUM_LIMBS := local.(BranchEqualCoreCols.diff_inv_marker) in

  let* cmp_eq : Z :=
    M.pure (
      BinOp.add
        (BinOp.mul local.(BranchEqualCoreCols.cmp_result) local.(BranchEqualCoreCols.opcode_beq_flag))
        (BinOp.mul (M.not local.(BranchEqualCoreCols.cmp_result)) local.(BranchEqualCoreCols.opcode_bne_flag))
    ) in

  let* _ := M.for_in_zero_to_n NUM_LIMBS (fun i =>
    M.assert_zero (BinOp.mul cmp_eq (BinOp.sub (Array.get a i) (Array.get b i)))
  ) in
  let sum : Z := sum_for_in_zero_to_n_starting_from NUM_LIMBS (fun i =>
    BinOp.mul (BinOp.sub (Array.get a i) (Array.get b i)) (Array.get inv_marker i)
  ) cmp_eq in
  let* _ := M.when is_valid (M.assert_one sum) in

  let flags_with_opcode_integer : list (Z * Z) :=
    [
      (local.(BranchEqualCoreCols.opcode_beq_flag), 0);
      (local.(BranchEqualCoreCols.opcode_bne_flag), 1)
    ] in
  let expected_opcode : Z :=
    Lists.List.fold_left
      (fun acc '(flag, opcode) =>
        BinOp.add acc (BinOp.mul flag opcode)
      )
      flags_with_opcode_integer
      0 in
  let expected_opcode : Z :=
    BinOp.add expected_opcode self.(BranchEqualCoreAir.offset) in

  let to_pc : Z :=
    BinOp.add
      (BinOp.add
        from_pc
        (BinOp.mul local.(BranchEqualCoreCols.cmp_result) local.(BranchEqualCoreCols.imm))
      )
      (BinOp.mul (M.not local.(BranchEqualCoreCols.cmp_result)) self.(BranchEqualCoreAir.pc_step))
    in

  M.pure {|
    AdapterAirContext.to_pc := Some to_pc;
    AdapterAirContext.reads := [a; b];
    AdapterAirContext.writes := [];
    AdapterAirContext.instruction := {|
      ImmInstruction.is_valid := is_valid;
      ImmInstruction.opcode := expected_opcode;
      ImmInstruction.immediate := local.(BranchEqualCoreCols.imm);
    |};
  |}.

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
    |},
    local.(BranchEqualCoreCols.cmp_result) = Z.b2z expected_cmp_result
  }}.
Proof.
  intros.
  unfold eval.
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
      Array.Eq.t local.(BranchEqualCoreCols.a) local.(BranchEqualCoreCols.b)
    else
      True
  ). {
    eapply Run.Implies. {
      Run.run.
    }
    intros H_for.
    unfold Array.Eq.t.
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
      ~ (Array.Eq.t local.(BranchEqualCoreCols.a) local.(BranchEqualCoreCols.b))
  ). {
    eapply Run.Implies. {
      repeat constructor.
    }
    intros H_sum.
    unfold Array.Eq.t.
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
    |}
  }}.
Proof.
  intros.
  unfold eval.
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
    destruct branch_equal_opcode, Array.Eq.dec as [H_a_b_eq|]; unfold Array.Eq.t in *; cbn; 
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
      unfold Array.Eq.t in H_a_b_eq.
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
