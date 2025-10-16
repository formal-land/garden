Require Import Garden.Plonky3.M.
Require Import Garden.Plonky3.MExpr.
Require Import Garden.OpenVM.BranchEq.core.

Global Instance ImmInstructionIsToRocq : PrettyPrint.C (ImmInstruction.t Expr.t) := {
  to_string self indent :=
    PrettyPrint.cats [PrettyPrint.indent indent; "ImmInstruction:"; PrettyPrint.endl;
      PrettyPrint.indent (indent + 2); "is_valid:"; PrettyPrint.endl;
      PrettyPrint.to_string self.(ImmInstruction.is_valid) (indent + 4); PrettyPrint.endl;
      PrettyPrint.indent (indent + 2); "opcode:"; PrettyPrint.endl;
      PrettyPrint.to_string self.(ImmInstruction.opcode) (indent + 4); PrettyPrint.endl;
      PrettyPrint.indent (indent + 2); "immediate:"; PrettyPrint.endl;
      PrettyPrint.to_string self.(ImmInstruction.immediate) (indent + 4)
    ];
}.

Global Instance AdapterAirContextIsToRocq {NUM_LIMBS : Z} :
    PrettyPrint.C (AdapterAirContext.t NUM_LIMBS Expr.t) := {
  to_string self indent :=
    PrettyPrint.cats [PrettyPrint.indent indent; "AdapterAirContext:"; PrettyPrint.endl;
      PrettyPrint.cats [PrettyPrint.indent (indent + 2); "to_pc:"; PrettyPrint.endl;
        PrettyPrint.to_string self.(AdapterAirContext.to_pc) (indent + 4)
      ];
      PrettyPrint.endl;
      PrettyPrint.cats [PrettyPrint.indent (indent + 2); "reads:"; PrettyPrint.endl;
        PrettyPrint.to_string self.(AdapterAirContext.reads) (indent + 4)
      ];
      PrettyPrint.endl;
      PrettyPrint.cats [PrettyPrint.indent (indent + 2); "writes:"; PrettyPrint.endl;
        PrettyPrint.to_string self.(AdapterAirContext.writes) (indent + 4)
      ];
      PrettyPrint.endl;
      PrettyPrint.cats [PrettyPrint.indent (indent + 2); "instruction:"; PrettyPrint.endl;
        PrettyPrint.to_string self.(AdapterAirContext.instruction) (indent + 4)
      ]
    ];
}.

Fixpoint sum_for_in_zero_to_n_starting_from_aux
    (n : nat)
    (f : Z -> Expr.t)
    (start : Expr.t) :
    Expr.t :=
  match n with
  | O => start
  | S n => Expr.Add (sum_for_in_zero_to_n_starting_from_aux n f start) (f (Z.of_nat n))
  end.

Definition sum_for_in_zero_to_n_starting_from
    (N : Z)
    (f : Z -> Expr.t)
    (start : Expr.t) :
    Expr.t :=
  sum_for_in_zero_to_n_starting_from_aux (Z.to_nat N) f start.

Lemma sum_for_in_zero_to_n_starting_from_eq {p} `{Prime p}
    (env : Env.t)
    (N : Z)
    (f : Z -> Expr.t) (f' : Z -> Z)
    (start : Expr.t) (start' : Z)
    (H_f : forall (i : Z),
      Eval.eval env (f i) = f' i
    )
    (H_start : Eval.eval env start = start') :
  Eval.eval env (sum_for_in_zero_to_n_starting_from N f start) =
  core.sum_for_in_zero_to_n_starting_from N f' start'.
Proof.
  unfold sum_for_in_zero_to_n_starting_from, core.sum_for_in_zero_to_n_starting_from.
  set (n := Z.to_nat N); clearbody n.
  induction n; cbn; intros; scongruence.
Qed.

Definition eval {NUM_LIMBS : Z}
    (self : BranchEqualCoreAir.t NUM_LIMBS)
    (local : BranchEqualCoreCols.t NUM_LIMBS Var.t)
    (from_pc : Var.t) :
    MExpr.t (AdapterAirContext.t NUM_LIMBS Expr.t) :=
  let flags : list Var.t := [
    local.(BranchEqualCoreCols.opcode_beq_flag);
    local.(BranchEqualCoreCols.opcode_bne_flag)
  ] in

  let! is_valid :=
    MExpr.List.fold_left
      (fun acc flag =>
        let! _ := MExpr.assert_bool (Expr.Var flag) in
        MExpr.pure (Expr.Add acc (Expr.Var flag))
      )
      Expr.ZERO
      flags in
  let! _ := MExpr.assert_bool is_valid in
  let! _ := MExpr.assert_bool (Expr.Var local.(BranchEqualCoreCols.cmp_result)) in

  let a : Array.t Var.t NUM_LIMBS := local.(BranchEqualCoreCols.a) in
  let b : Array.t Var.t NUM_LIMBS := local.(BranchEqualCoreCols.b) in
  let inv_marker : Array.t Var.t NUM_LIMBS := local.(BranchEqualCoreCols.diff_inv_marker) in

  let! cmp_eq : Expr.t :=
    MExpr.pure (
      Expr.Add
        (Expr.Mul
          (Expr.Var local.(BranchEqualCoreCols.cmp_result))
          (Expr.Var local.(BranchEqualCoreCols.opcode_beq_flag)))
        (Expr.Mul
          (Expr.not (Expr.Var local.(BranchEqualCoreCols.cmp_result)))
          (Expr.Var local.(BranchEqualCoreCols.opcode_bne_flag)))
    ) in

  let! _ :=
    MExpr.for_in_zero_to_n NUM_LIMBS (fun i =>
      MExpr.assert_zero (
        Expr.Mul cmp_eq (Expr.Sub (Expr.Var (Array.get a i)) (Expr.Var (Array.get b i)))
      )
    ) in
  let sum : Expr.t :=
    sum_for_in_zero_to_n_starting_from NUM_LIMBS (fun i =>
      Expr.Mul
        (Expr.Sub (Expr.Var (Array.get a i)) (Expr.Var (Array.get b i)))
        (Expr.Var (Array.get inv_marker i))
    ) cmp_eq in
  let! _ := MExpr.when is_valid (MExpr.assert_one sum) in

  let flags_with_opcode_integer : list (Var.t * Z) :=
    [
      (local.(BranchEqualCoreCols.opcode_beq_flag), 0);
      (local.(BranchEqualCoreCols.opcode_bne_flag), 1)
    ] in
  let expected_opcode : Expr.t :=
    Lists.List.fold_left
      (fun acc '(flag, opcode) =>
        Expr.Add acc (Expr.Mul (Expr.Var flag) (Expr.constant opcode))
      )
      flags_with_opcode_integer
      Expr.ZERO in
  let expected_opcode : Expr.t :=
    Expr.Add expected_opcode (Expr.constant self.(BranchEqualCoreAir.offset)) in

  let to_pc : Expr.t :=
    Expr.Add
      (Expr.Add
        (Expr.Var from_pc)
        (Expr.Mul
          (Expr.Var local.(BranchEqualCoreCols.cmp_result))
          (Expr.Var local.(BranchEqualCoreCols.imm))))
      (Expr.Mul
        (Expr.not (Expr.Var local.(BranchEqualCoreCols.cmp_result)))
        (Expr.constant self.(BranchEqualCoreAir.pc_step)))
    in

  MExpr.pure {|
    AdapterAirContext.to_pc := Some to_pc;
    AdapterAirContext.reads := [Array.map Expr.Var a; Array.map Expr.Var b];
    AdapterAirContext.writes := [];
    AdapterAirContext.instruction := {|
      ImmInstruction.is_valid := is_valid;
      ImmInstruction.opcode := expected_opcode;
      ImmInstruction.immediate := Expr.Var local.(BranchEqualCoreCols.imm);
    |};
  |}.

(** We prove the equality of the [eval] definition above with the [eval] definition directly using
    field elements. *)
Lemma eval_eq {p} `{Prime p} {NUM_LIMBS : Z}
    (env : Env.t)
    (self : BranchEqualCoreAir.t NUM_LIMBS)
    (local : BranchEqualCoreCols.t NUM_LIMBS Var.t)
    (from_pc : Var.t) :
  MExpr.Eq.t env
    (eval self local from_pc)
    (core.eval
      self
      (BranchEqualCoreCols.map (Var.eval env.(Env.var)) local)
      (Var.eval env.(Env.var) from_pc)
    ).
Proof.
  unfold eval, core.eval.
  econstructor. {
    apply List.Eq.fold_left_eq; try reflexivity.
    econstructor. {
      repeat constructor.
      cbn; now autorewrite with field_rewrite.
    }
    intros.
    repeat constructor.
  }
  intros.
  econstructor. {
    constructor; cbn; now autorewrite with field_rewrite.
  }
  intros.
  econstructor. {
    constructor; cbn; now autorewrite with field_rewrite.
  }
  intros.
  econstructor. {
    apply MExpr.Eq.Pure.
    unfold M.not.
    now cbn; FieldRewrite.run.
  }
  intros.
  econstructor. {
    apply for_in_zero_to_n_eq.
    intros.
    now constructor.
  }
  intros.
  econstructor. {
    econstructor; try reflexivity.
    constructor; try reflexivity.
    cbn; autorewrite with field_rewrite.
    f_equal.
    now apply sum_for_in_zero_to_n_starting_from_eq.
  }
  intros.
  constructor.
  cbn; unfold AdapterAirContext.map; cbn.
  f_equal.
  { unfold M.not.
    now cbn; FieldRewrite.run.
  }
  { unfold ImmInstruction.map; cbn; f_equal.
    now cbn; FieldRewrite.run.
  }
Qed.
