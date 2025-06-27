Require Import ZArith.
Require Import List.
Import ListNotations.
Require Import Garden.OpenVM.BranchEq.M.MBuilder.

(* TODO: 
- Implement eval using MBuilder
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
  Import BranchEqualCoreCols.
  Definition Self (NUM_LIMBS : Z) := BranchEqualCoreAir.t NUM_LIMBS.

  Definition default_Z : Z := 0.

  Definition eval (NUM_LIMBS : Z) (self : (Self NUM_LIMBS)) (local : list Z) (from_pc : Z) : 
    (* M.t (AdapterAirContext.t ImmInstruction.t) := *)
    M.t (AdapterAirContext.t ImmInstruction.t) :=
    (* 
    let cols: &BranchEqualCoreCols<_, NUM_LIMBS> = local.borrow();
    let flags = [cols.opcode_beq_flag, cols.opcode_bne_flag];
    *)
    let cols := @Impl_Borrow_BranchEqualCoreCols_for_T.borrow
      local NUM_LIMBS in
    let f1 := cols.(opcode_beq_flag NUM_LIMBS) in
    let f2 := cols.(opcode_bne_flag NUM_LIMBS) in
    (* 
    let is_valid = flags.iter().fold(AB::Expr::ZERO, |acc, &flag| {
              builder.assert_bool(flag);
              acc + flag.into()
          });
    *)
    let* _ := assert_bool f1 in
    let* _ := assert_bool f2 in
    let is_valid := Z.add f1 f2 in
    (* 
    builder.assert_bool(is_valid.clone());
    builder.assert_bool(cols.cmp_result);
    *)
    let* _ := assert_bool is_valid in
    let cmp_result := cols.(cmp_result NUM_LIMBS) in
    let* _ := assert_bool cmp_result in
    (* 
    let a = &cols.a;
    let b = &cols.b;
    let inv_marker = &cols.diff_inv_marker;
    *)
    let a := cols.(a NUM_LIMBS) in
    let b := cols.(b NUM_LIMBS) in
    let inv_maker := cols.(diff_inv_marker NUM_LIMBS) in
    (* 
    // 1 if cmp_result indicates a and b are equal, 0 otherwise
    let cmp_eq =
        cols.cmp_result * cols.opcode_beq_flag + not(cols.cmp_result) * cols.opcode_bne_flag;
    let mut sum = cmp_eq.clone();
    *)
    let opcode_beq_flag := cols.(opcode_beq_flag NUM_LIMBS) in
    let opcode_bne_flag := cols.(opcode_bne_flag NUM_LIMBS) in
    let cmp_eq := Z.add (Z.mul cmp_result opcode_beq_flag)
      (Z.mul (Z.sub 1 cmp_result) opcode_bne_flag) in
    let sum := cmp_eq in
        (* 
    // For BEQ, inv_marker is used to check equality of a and b:
    // - If a == b, all inv_marker values must be 0 (sum = 0)
    // - If a != b, inv_marker contains 0s for all positions except ONE position i where a[i] !=
    //   b[i]
    // - At this position, inv_marker[i] contains the multiplicative inverse of (a[i] - b[i])
    // - This ensures inv_marker[i] * (a[i] - b[i]) = 1, making the sum = 1
    // Note: There might be multiple valid inv_marker if a != b.
    // But as long as the trace can provide at least one, that’s sufficient to prove a != b.
    //
    // Note:
    // - If cmp_eq == 0, then it is impossible to have sum != 0 if a == b.
    // - If cmp_eq == 1, then it is impossible for a[i] - b[i] == 0 to pass for all i if a != b.
    for i in 0..NUM_LIMBS {
        sum += (a[i] - b[i]) * inv_marker[i];
        builder.assert_zero(cmp_eq.clone() * (a[i] - b[i]));
    }
    builder.when(is_valid.clone()).assert_one(sum); 
    *)
    let fix loop (n : nat) (sum : Z) {struct n} := 
    match n with 
    | O => M.pure sum
    | S n' =>
      (* 0 <= x < NUM_LIMBS *)
      let x := minus (minus (Z.to_nat NUM_LIMBS) 1) n' in
      let a_i := nth x a default_Z in
      let b_i := nth x b default_Z in
      let inv_maker_i := nth x inv_maker default_Z in
      let sum := Z.add sum (Z.mul (Z.sub a_i b_i) inv_maker_i) in
      let* _ := assert_zero (Z.mul cmp_eq (Z.sub a_i b_i)) in
      loop n' sum
    end in
    let* sum := loop (Z.to_nat NUM_LIMBS) sum in
    let* _ := @M.When unit is_valid in
    let* _ := assert_one sum in
    let* _ := M.EndWhen in
    (* 
    let expected_opcode = flags
        .iter()
        .zip(BranchEqualOpcode::iter())
        .fold(AB::Expr::ZERO, |acc, (flag, opcode)| {
            acc + ( \*flag).into() * AB::Expr::from_canonical_u8(opcode as u8)
        })
        + AB::Expr::from_canonical_usize(self.offset);
    *)
    let opcodes := map BranchEqualOpcode.as_usize BranchEqualOpcode.iter in
    let o1 := nth 0 opcodes BranchEqualOpcode.opcode_offset in
    let o2 := nth 1 opcodes BranchEqualOpcode.opcode_offset in
    let expected_opcode := Z.add 
      (Z.mul f1 o1) (Z.mul f2 o2) in
    (* 
    let to_pc = from_pc
              + cols.cmp_result * cols.imm
              + not(cols.cmp_result) * AB::Expr::from_canonical_u32(self.pc_step);
    *)
    let imm := (cols.(imm NUM_LIMBS)) in
    let to_pc := Z.add from_pc (Z.mul cmp_result imm) in
    let pc_step := self.(BranchEqualCoreAir.pc_step NUM_LIMBS) in
    let to_pc := Z.add to_pc (Z.mul (Z.sub 1 cmp_result) pc_step) in
    (* 
    AdapterAirContext {
        to_pc: Some(to_pc),
        reads: [cols.a.map(Into::into), cols.b.map(Into::into)].into(),
        writes: Default::default(),
        instruction: ImmInstruction {
            is_valid,
            opcode: expected_opcode,
            immediate: cols.imm.into(),
        }
        .into(),
    }
    *)
    let reads := a ++ b in
    let context := (AdapterAirContext.Build_t 
      ImmInstruction.t (Some to_pc) reads []
      (ImmInstruction.Build_t is_valid expected_opcode imm)
    ) in
    M.pure context.
End Impl_VmCoreAir_for_BranchEqualCoreAir.