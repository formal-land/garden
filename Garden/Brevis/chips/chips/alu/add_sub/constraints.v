Require Import Garden.Plonky3.M.
Require Import Garden.Brevis.chips.chips.alu.add_sub.columns.
Require Import Garden.Brevis.chips.gadgets.add.
Require Import Garden.Brevis.compiler.riscv.opcode.
Require Import Garden.Brevis.machine.builder.lookup.

Definition eval {p} `{Prime p} (local : AddSubCols.t) : M.t unit :=
  M.for_each local.(AddSubCols.values) (fun value =>
    let '{|
      AddSubValueCols.add_operation := add_operation;
      AddSubValueCols.operand_1 := operand_1;
      AddSubValueCols.operand_2 := operand_2;
      AddSubValueCols.is_add := is_add;
      AddSubValueCols.is_sub := is_sub;
    |} := value in
    let* _ := AddGadget.eval operand_1 operand_2 add_operation (is_add +F is_sub) in

    let opcode := is_add *F Opcode.to_Z Opcode.ADD
        +F is_sub *F Opcode.to_Z Opcode.SUB in

    let* _ :=
      looked_alu
        opcode
        add_operation.(AddGadget.value)
        operand_1
        operand_2
        is_add in

    let* _ := looked_alu opcode operand_1 add_operation.(AddGadget.value) operand_2 is_sub in

    let is_real := is_add +F is_sub in
    let* _ := M.assert_bool is_add in
    let* _ := M.assert_bool is_sub in
    let* _ := M.assert_bool is_real in
    M.pure tt
  ).
