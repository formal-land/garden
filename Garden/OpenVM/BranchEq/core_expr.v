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

Global Instance ImmInstructionIsToRocq : ToRocq.C (ImmInstruction.t Expr.t) := {
  to_rocq self indent :=
    ToRocq.cats [ToRocq.indent indent; "ImmInstruction:"; ToRocq.endl;
      ToRocq.to_rocq self.(ImmInstruction.is_valid) (indent + 2);
      ToRocq.to_rocq self.(ImmInstruction.opcode) (indent + 2);
      ToRocq.to_rocq self.(ImmInstruction.immediate) (indent + 2)
    ];
}.

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
End AdapterAirContext.

Global Instance AdapterAirContextIsToRocq {NUM_LIMBS : Z} :
    ToRocq.C (AdapterAirContext.t NUM_LIMBS Expr.t) := {
  to_rocq self indent :=
    ToRocq.cats [ToRocq.indent indent; "AdapterAirContext:"; ToRocq.endl;
      ToRocq.cats [ToRocq.indent (indent + 2); "to_pc:"; ToRocq.endl;
        ToRocq.to_rocq self.(AdapterAirContext.to_pc) (indent + 4)
      ];
      ToRocq.cats [ToRocq.indent (indent + 2); "reads:"; ToRocq.endl;
        ToRocq.to_rocq self.(AdapterAirContext.reads) (indent + 4)
      ];
      ToRocq.cats [ToRocq.indent (indent + 2); "writes:"; ToRocq.endl;
        ToRocq.to_rocq self.(AdapterAirContext.writes) (indent + 4)
      ];
      ToRocq.cats [ToRocq.indent (indent + 2); "instruction:"; ToRocq.endl;
        ToRocq.to_rocq self.(AdapterAirContext.instruction) (indent + 4)
      ]
    ];
}.

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
            (Expr.Sub (Expr.Var (Array.get a i)) (Expr.Var (Array.get b i)))
            (Expr.Var (Array.get inv_marker i)))
      )
      (Lists.List.seq 0 (Z.to_nat NUM_LIMBS))
      cmp_eq in
  let builder := Builder.when builder is_valid (fun builder => Builder.assert_one builder sum) in

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
      AdapterAirContext.reads := [Array.map a Expr.Var; Array.map b Expr.Var];
      AdapterAirContext.writes := [];
      AdapterAirContext.instruction := {|
        ImmInstruction.is_valid := is_valid;
        ImmInstruction.opcode := expected_opcode;
        ImmInstruction.immediate := Expr.Var local.(BranchEqualCoreCols.imm);
      |};
    |},
    builder
  ).

Definition print_branch_eq {NUM_LIMBS : Z} :
    string :=
  let air := {|
    BranchEqualCoreAir.offset := 12;
    BranchEqualCoreAir.pc_step := 23;
  |} in
  let builder := Builder.new in
  let local : BranchEqualCoreCols.t NUM_LIMBS Var.t := {|
    BranchEqualCoreCols.a := {| Array.get := fun i => Var.make (i + 0) |};
    BranchEqualCoreCols.b := {| Array.get := fun i => Var.make (i + NUM_LIMBS) |};
    BranchEqualCoreCols.cmp_result := Var.make (2 * NUM_LIMBS);
    BranchEqualCoreCols.imm := Var.make (2 * NUM_LIMBS + 1);
    BranchEqualCoreCols.opcode_beq_flag := Var.make (2 * NUM_LIMBS + 2);
    BranchEqualCoreCols.opcode_bne_flag := Var.make (2 * NUM_LIMBS + 3);
    BranchEqualCoreCols.diff_inv_marker := {| Array.get := fun i => Var.make (i + 2 * NUM_LIMBS + 4) |};
  |} in
  let from_pc : Var.t := Var.make (3 * NUM_LIMBS + 4) in
  let '(result, builder) := eval air builder local from_pc in
  ToRocq.cats [
    ToRocq.endl;
    ToRocq.to_rocq builder 0;
    ToRocq.to_rocq result 0
  ].

Compute print_branch_eq (NUM_LIMBS := 4).
