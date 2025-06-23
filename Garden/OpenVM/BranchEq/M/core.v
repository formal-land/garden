Require Import ZArith.
Require Import List.
Import ListNotations.
Require Import Garden.OpenVM.BranchEq.M.MBuilder.

(* TODO: 
- copy MLessEffects to make a completely separate monad 
*)

Module ImmInstruction.
  Record t : Set := {
    is_valid : Z;
    op_code : Z;
    immediate : Z;
  }.
End ImmInstruction.

Module AdapterAirContext.
  Record t (Instruction : Set) : Set := {
    to_pc : option Z;
    reads : list Z;
    writes : list Z;
    instruction : Instruction;
  }.
End AdapterAirContext.

Module BranchEqualOpcode.
  Definition opcode_offset : Z := 0x220.

  Inductive t :=
  | BEQ
  | BNE
  .

  Definition as_usize (x : t) : Z :=
    match x with
    | BEQ => Z.add 0 opcode_offset
    | BNE => Z.add 1 opcode_offset
    end.

  Definition iter : list t := [BEQ; BNE].
End BranchEqualOpcode.

Module BranchEqualCoreCols.
  Record t (NUM_LIMBS : Z) : Set := {
    a : list Z;
    b : list Z;
    cmp_result : Z;
    imm : Z;
    opcode_beq_flag : Z;
    opcode_bne_flag : Z;
    diff_inv_marker : list Z;
  }.
End BranchEqualCoreCols.


Module Impl_Borrow_BranchEqualCoreCols_for_T.
  Fixpoint next_helper {T : Set} (n : nat) (src : list T) (store : list T) : list T * list T :=
    match n with
    | O => (src, store)
    | S n' => match src with
      | x :: xs => next_helper n' xs (store ++ [x])
      | [] => (src, store)
      end
    end.

  (* slice the first n elements of a list, return it with the remaining part of the list *)
  Definition next {T : Set} (n : nat) (src : list T) : list T * list T :=
    next_helper n src [].

  Definition borrow_helper (cols : list Z) (NUM_LIMBS : Z) (default_T : Z)
    : BranchEqualCoreCols.t NUM_LIMBS :=
    let NUM_LIMBS' := Z.to_nat NUM_LIMBS in
    let (cols, a) := next NUM_LIMBS' cols in
    let (cols, b) := next NUM_LIMBS' cols in
    let (cols, cmp_result) := next 1 cols in
    let cmp_result := match (head cmp_result) with | Some x => x | None => default_T end in
    let (cols, imm) := next 1 cols in
    let imm := match (head imm) with | Some x => x | None => default_T end in
    let (cols, opcode_beq_flag) := next 1 cols in
    let opcode_beq_flag := match (head opcode_beq_flag) with | Some x => x | None => default_T end in
    let (cols, opcode_bne_flag) := next 1 cols in
    let opcode_bne_flag := match (head opcode_bne_flag) with | Some x => x | None => default_T end in
    let (cols, diff_inv_marker) := next NUM_LIMBS' cols in
    let diff_inv_marker := diff_inv_marker in
    BranchEqualCoreCols.Build_t NUM_LIMBS
      a b cmp_result imm opcode_beq_flag opcode_bne_flag diff_inv_marker.

  Definition borrow (cols : list Z) (NUM_LIMBS : Z) : BranchEqualCoreCols.t NUM_LIMBS 
    := borrow_helper cols NUM_LIMBS 999. (* After we can make sure the translation works well we should
    switch the number to 0 *)
End Impl_Borrow_BranchEqualCoreCols_for_T.

Module BranchEqualCoreAir.
  Record t (NUM_LIMBS : Z) : Set := {
    offset : Z;
    pc_step : Z;
  }.
End BranchEqualCoreAir.

Module Impl_VmCoreAir_for_BranchEqualCoreAir.
  Definition Self (NUM_LIMBS : Z) := BranchEqualCoreAir.t NUM_LIMBS.

  Definition eval (NUM_LIMBS : Z) (self : (Self NUM_LIMBS)) (local : list Z) (from_pc : Z) : 
    (* M.t (AdapterAirContext.t ImmInstruction.t) := *)
    M.t unit :=
    let* _ := M.pure tt in
    (* let* _ := when is_first_row (
      M.zeros (Array.slice_from local.(KeccakCols.step_flags) 1)
    ) in
    let* _ := when is_transition (
      M.zeros (N := NUM_ROUNDS) {|
        Array.get i :=
          BinOp.sub (local.(KeccakCols.step_flags).(Array.get) i)
          (next.(KeccakCols.step_flags).(Array.get) ((i + 1) mod NUM_ROUNDS))
      |}
    ) in *)
    M.pure tt.
End Impl_VmCoreAir_for_BranchEqualCoreAir.