Require Import Garden.Plonky3.M.

(*
pub struct ImmInstruction<T> {
    pub is_valid: T,
    pub opcode: T,
    pub immediate: T,
}
*)
Module ImmInstruction.
  Record t : Set := {
    is_valid : Z;
    opcode : Z;
    immediate : Z;
  }.
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
  Record t {NUM_LIMBS : Z}: Set := {
    to_pc : option Z;
    (* I::Reads: From<[[AB::Expr; NUM_LIMBS]; 2]>, *)
    reads : Array.t Z NUM_LIMBS * Array.t Z NUM_LIMBS;
    (* I::Writes: Default, *)
    writes : unit;
    (* I::ProcessedInstruction: From<ImmInstruction<AB::Expr>>, *)
    instruction : ImmInstruction.t;
  }.
  Arguments t : clear implicits.
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
  Record t {NUM_LIMBS : Z} : Set := {
    a : Array.t Z NUM_LIMBS;
    b : Array.t Z NUM_LIMBS;
    cmp_result : Z;
    imm : Z;
    opcode_beq_flag : Z;
    opcode_bne_flag : Z;
    diff_inv_marker : Array.t Z NUM_LIMBS;
  }.
  Arguments t : clear implicits.

  Global Instance map_mod {p} `{Prime p} {NUM_LIMBS : Z} : MapMod (t NUM_LIMBS) := {
    map_mod := fun x => {|
      BranchEqualCoreCols.a := M.map_mod x.(BranchEqualCoreCols.a);
      BranchEqualCoreCols.b := M.map_mod x.(BranchEqualCoreCols.b);
      BranchEqualCoreCols.cmp_result := M.map_mod x.(BranchEqualCoreCols.cmp_result);
      BranchEqualCoreCols.imm := M.map_mod x.(BranchEqualCoreCols.imm);
      BranchEqualCoreCols.opcode_beq_flag := M.map_mod x.(BranchEqualCoreCols.opcode_beq_flag);
      BranchEqualCoreCols.opcode_bne_flag := M.map_mod x.(BranchEqualCoreCols.opcode_bne_flag);
      BranchEqualCoreCols.diff_inv_marker := M.map_mod x.(BranchEqualCoreCols.diff_inv_marker);
    |};
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

Definition eval {p} `{Prime p} {NUM_LIMBS : Z}
    (self : BranchEqualCoreAir.t NUM_LIMBS)
    (local : BranchEqualCoreCols.t NUM_LIMBS)
    (from_pc : Z) :
    M.t (AdapterAirContext.t NUM_LIMBS) :=
  let flags : list Z := [
    local.(BranchEqualCoreCols.opcode_beq_flag);
    local.(BranchEqualCoreCols.opcode_bne_flag)
  ] in

  let* is_valid : Z :=
    List.fold_left
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
  let sum : Z := M.sum_for_in_zero_to_n NUM_LIMBS (fun i =>
    BinOp.mul (Array.get inv_marker i) (BinOp.sub (Array.get a i) (Array.get b i))
  ) in
  let sum := BinOp.add sum cmp_eq in
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
    AdapterAirContext.reads := (a, b);
    AdapterAirContext.writes := tt;
    AdapterAirContext.instruction := {|
      ImmInstruction.is_valid := is_valid;
      ImmInstruction.opcode := expected_opcode;
      ImmInstruction.immediate := local.(BranchEqualCoreCols.imm);
    |};
  |}.

Definition goldilocks_prime : Z :=
  2^64 - 2^32 + 1.

Lemma eval_implies `{Prime goldilocks_prime} {NUM_LIMBS : Z}
    (self : BranchEqualCoreAir.t NUM_LIMBS)
    (local' : BranchEqualCoreCols.t NUM_LIMBS)
    (from_pc' : Z)
    (branch_equal_opcode : BranchEqualOpcode.t) :
  let local :=
    M.map_mod local'
      <| BranchEqualCoreCols.opcode_beq_flag :=
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
      |> in
  let from_pc := M.map_mod from_pc' in
  let expected_cmp_result : bool :=
    match branch_equal_opcode with
    | BranchEqualOpcode.BEQ =>
      if Array.Eq.dec local.(BranchEqualCoreCols.a) local.(BranchEqualCoreCols.b) then
        true
      else
        false
    | BranchEqualOpcode.BNE =>
      if Array.Eq.dec local.(BranchEqualCoreCols.a) local.(BranchEqualCoreCols.b) then
        false
      else
        true
    end in
  {{ eval self local from_pc 🔽
    {|
      AdapterAirContext.to_pc :=
        Some (BinOp.add from_pc (
          if expected_cmp_result then
            local.(BranchEqualCoreCols.imm)
          else
            self.(BranchEqualCoreAir.pc_step)
        ));
      AdapterAirContext.reads := (local.(BranchEqualCoreCols.a), local.(BranchEqualCoreCols.b));
      AdapterAirContext.writes := tt;
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
      repeat constructor.
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
    set (sum_for := M.sum_for_in_zero_to_n _ _) in H_sum.
    replace sum_for with 0 in H_sum. 2: {
      symmetry.
      apply M.sum_for_in_zero_to_n_zeros_eq.
      intros.
      replace (BinOp.sub _ _) with 0. 2: {
        symmetry.
        rewrite M.sub_zero_equiv.
        sauto lq: on rew: off.
      }
      now autorewrite with field_rewrite.
    }
    easy.
  }
  intros H_a_b_neq.
  cbn - [local from_pc].
  autorewrite with field_rewrite.
  assert (local.(BranchEqualCoreCols.cmp_result) = Z.b2z expected_cmp_result) as H_cmp_result_eq. {
    rewrite H_cmp_result; f_equal.
    unfold expected_cmp_result, cmp_eq in *.
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
