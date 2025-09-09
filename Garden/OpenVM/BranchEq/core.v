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
