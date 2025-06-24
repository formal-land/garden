Require Import Garden.Plonky3.MLessEffects.

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
  Record t : Set := {
    to_pc : option Z;
    (* reads : I::Reads;
    writes : I::Writes;
    instruction : I::ProcessedInstruction; *)
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
    M.t AdapterAirContext.t :=
  let flags : list Z := [
    local.(BranchEqualCoreCols.opcode_beq_flag);
    local.(BranchEqualCoreCols.opcode_bne_flag)
  ] in

  let* is_valid : Z :=
    List.fold_left
      (fun acc flag =>
        let* _ := assert_bool flag in
        M.pure (BinOp.add acc flag)
      )
      Z.zero
      flags in
  let* _ := assert_bool is_valid in
  let* _ := assert_bool local.(BranchEqualCoreCols.cmp_result) in

  let a : Array.t Z NUM_LIMBS := local.(BranchEqualCoreCols.a) in
  let b : Array.t Z NUM_LIMBS := local.(BranchEqualCoreCols.b) in
  let inv_marker : Array.t Z NUM_LIMBS := local.(BranchEqualCoreCols.diff_inv_marker) in

  let cmp_eq : Z :=
    BinOp.add
      (BinOp.mul local.(BranchEqualCoreCols.cmp_result) local.(BranchEqualCoreCols.opcode_beq_flag))
      (BinOp.mul (MLessEffects.not local.(BranchEqualCoreCols.cmp_result)) local.(BranchEqualCoreCols.opcode_bne_flag))
    in

  let* sum : Z :=
    List.fold_left
      (fun acc i =>
        let i := Z.of_nat i in
        let* _ := assert_zero (BinOp.mul cmp_eq (BinOp.sub (Array.get a i) (Array.get b i))) in
        M.pure (BinOp.add acc (BinOp.mul (Array.get inv_marker i) (BinOp.sub (Array.get a i) (Array.get b i))))
      )
      Z.zero (List.seq 0 (Z.to_nat NUM_LIMBS)) in
  let* _ := when is_valid (assert_one sum) in

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
      (BinOp.mul (MLessEffects.not local.(BranchEqualCoreCols.cmp_result)) self.(BranchEqualCoreAir.pc_step))
    in

  M.pure {|
    AdapterAirContext.to_pc := Some to_pc;
  |}.
