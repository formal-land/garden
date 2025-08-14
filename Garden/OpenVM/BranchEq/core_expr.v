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
    reads : Array.t T NUM_LIMBS * Array.t T NUM_LIMBS;
    (* I::Writes: Default, *)
    writes : unit;
    (* I::ProcessedInstruction: From<ImmInstruction<AB::Expr>>, *)
    instruction : ImmInstruction.t T;
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

Definition eval {NUM_LIMBS : Z}
    (self : BranchEqualCoreAir.t NUM_LIMBS)
    (builder : Builder.t)
    (local : BranchEqualCoreCols.t NUM_LIMBS Var.t)
    (from_pc : Var.t) :
    AdapterAirContext.t NUM_LIMBS Expr.t * Builder.t :=
  let flags : list Var.t := [
    local.(BranchEqualCoreCols.opcode_beq_flag);
    local.(BranchEqualCoreCols.opcode_bne_flag)
  ] in

  let '(is_valid, builder) :=
    Lists.List.fold_left
      (fun '(acc, builder) flag =>
        let builder := Builder.assert_bool builder (Expr.Var flag) in
        (Expr.Add acc (Expr.Var flag), builder)
      )
      flags
      (Expr.ZERO, builder) in
  let builder := Builder.assert_bool builder is_valid in
  let builder := Builder.assert_bool builder (Expr.Var local.(BranchEqualCoreCols.cmp_result)) in

  let a : Array.t Var.t NUM_LIMBS := local.(BranchEqualCoreCols.a) in
  let b : Array.t Var.t NUM_LIMBS := local.(BranchEqualCoreCols.b) in
  let inv_marker : Array.t Var.t NUM_LIMBS := local.(BranchEqualCoreCols.diff_inv_marker) in

  let cmp_eq : Expr.t :=
    Expr.Add
      (Expr.Mul
        (Expr.Var local.(BranchEqualCoreCols.cmp_result))
        (Expr.Var local.(BranchEqualCoreCols.opcode_beq_flag)))
      (Expr.Mul
        (Expr.not (Expr.Var local.(BranchEqualCoreCols.cmp_result)))
        (Expr.Var local.(BranchEqualCoreCols.opcode_bne_flag))) in

  let builder :=
    Lists.List.fold_left
      (fun builder (i : nat) =>
        let i := Z.of_nat i in
        Builder.assert_zero builder
          (Expr.Mul cmp_eq (Expr.Sub (Expr.Var (Array.get a i)) (Expr.Var (Array.get b i))))
      )
      (Lists.List.seq 0 (Z.to_nat NUM_LIMBS))
      builder in
  let sum : Expr.t :=
    Lists.List.fold_left
      (fun sum (i : nat) =>
        let i := Z.of_nat i in
        Expr.Add sum
          (Expr.Mul
            (Expr.Var (Array.get inv_marker i))
            (Expr.Sub (Expr.Var (Array.get a i)) (Expr.Var (Array.get b i))))
      )
      (Lists.List.seq 0 (Z.to_nat NUM_LIMBS))
      Expr.ZERO in
  let sum : Expr.t := Expr.Add sum cmp_eq in
  let builder := Builder.assert_zero builder (Expr.Mul is_valid (Expr.assert_one sum)) in

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

  (
    {|
      AdapterAirContext.to_pc := Some to_pc;
      AdapterAirContext.reads := (Array.map a Expr.Var, Array.map b Expr.Var);
      AdapterAirContext.writes := tt;
      AdapterAirContext.instruction := {|
        ImmInstruction.is_valid := is_valid;
        ImmInstruction.opcode := expected_opcode;
        ImmInstruction.immediate := Expr.Var local.(BranchEqualCoreCols.imm);
      |};
    |},
    builder
  ).
