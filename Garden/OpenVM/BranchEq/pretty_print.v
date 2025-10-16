Require Import Garden.Plonky3.M.
Require Import Garden.Plonky3.MExpr.
Require Import Garden.OpenVM.BranchEq.core.
Require Import Garden.OpenVM.BranchEq.core_expr.

Definition print_branch_eq {NUM_LIMBS : Z} : string :=
  let air := {|
    BranchEqualCoreAir.offset := 12;
    BranchEqualCoreAir.pc_step := 23;
  |} in
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
  PrettyPrint.cats [
    PrettyPrint.endl;
    PrettyPrint.to_string (eval air local from_pc) 0;
    PrettyPrint.endl
  ].

Compute print_branch_eq (NUM_LIMBS := 4).
