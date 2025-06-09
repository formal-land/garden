Require Import ZArith.
Require Import List.
Import ListNotations.

(* 
TODO:
- Implement enough functionality to make the following code works:
  let cols: &BranchEqualCoreCols<_, NUM_LIMBS> = local.borrow();
  let flags = [cols.opcode_beq_flag, cols.opcode_bne_flag];
- Investigate `AB::Var`
*)

(* 
use std::{
    array,
    borrow::{Borrow, BorrowMut},
};

use openvm_circuit::arch::{
    AdapterAirContext, AdapterRuntimeContext, ImmInstruction, Result, VmAdapterInterface,
    VmCoreAir, VmCoreChip,
};
use openvm_circuit_primitives::utils::not;
use openvm_circuit_primitives_derive::AlignedBorrow;
use openvm_instructions::{instruction::Instruction, LocalOpcode};
use openvm_rv32im_transpiler::BranchEqualOpcode;
use openvm_stark_backend::{
    interaction::InteractionBuilder,
    p3_air::{AirBuilder, BaseAir},
    p3_field::{Field, FieldAlgebra, PrimeField32},
    rap::BaseAirWithPublicValues,
};
use serde::{Deserialize, Serialize};
use serde_big_array::BigArray;
use strum::IntoEnumIterator;
*)

Module Dependency.
  Inductive Expr : Set := | Make_Expr .
  Inductive BusIndex : Set := | Make_BusIndex .

  (* 
  pub struct Interaction<Expr> {
      pub message: Vec<Expr>,
      pub count: Expr,
      /// The bus index specifying the bus to send the message over. All valid instantiations of
      /// `BusIndex` are safe.
      pub bus_index: BusIndex,
      /// Determines the contribution of each interaction message to a linear constraint on the trace
      /// heights in the verifier.
      ///
      /// For each bus index and trace, `count_weight` values are summed per interaction on that
      /// bus index and multiplied by the trace height. The total sum over all traces is constrained
      /// by the verifier to not overflow the field characteristic \( p \).
      ///
      /// This is used to impose sufficient conditions for bus constraint soundness and setting a
      /// proper value depends on the bus and the constraint it imposes.
      pub count_weight: u32,
  }
  *)
  (* TODO: examine this type in the future *)
  Record Interaction (e : Expr) : Set := {
    message : list Expr;
    count : Expr;
    bus_index : BusIndex;
    count_weight : Z;
  }.
End Dependency.

Module VmAdapterInterface.
  (* 
  /// The interface between primitive AIR and machine adapter AIR.
  pub trait VmAdapterInterface<T> {
      /// The memory read data that should be exposed for downstream use
      type Reads;
      /// The memory write data that are expected to be provided by the integrator
      type Writes;
      /// The parts of the instruction that should be exposed to the integrator.
      /// This will typically include `is_valid`, which indicates whether the trace row
      /// is being used and `opcode` to indicate which opcode is being executed if the
      /// VmChip supports multiple opcodes.
      type ProcessedInstruction;
  }
  *)
  Class t (T : Set) : Type := {
    Reads : Set;
    Writes : Set;
    ProcessedInstruction : Set;
  }.
End VmAdapterInterface.

(* 
pub trait InteractionBuilder: AirBuilder {
    /// Stores a new interaction in the builder.
    ///
    /// See [Interaction] for more details on `count_weight`.
    fn push_interaction<E: Into<Self::Expr>>(
        &mut self,
        bus_index: BusIndex,
        fields: impl IntoIterator<Item = E>,
        count: impl Into<Self::Expr>,
        count_weight: u32,
    );

    /// Returns the current number of interactions.
    fn num_interactions(&self) -> usize;

    /// Returns all interactions stored.
    fn all_interactions(&self) -> &[Interaction<Self::Expr>];
}
*)
Module InteractionBuilder.
  Class t : Type := {
    (* Types from AirBuilder
    type F: Field;
    type Expr: Algebra<Self::F> + Algebra<Self::Var>;
    type Var: Into<Self::Expr>
    type M: Matrix<Self::Var>;
    *)
    F : Set;
    Expr : Set;
    Var : Set;
    M : Set;
  }.
End InteractionBuilder.

(*
#[repr(C)]
#[derive(AlignedBorrow)]
pub struct BranchEqualCoreCols<T, const NUM_LIMBS: usize> {
    pub a: [T; NUM_LIMBS],
    pub b: [T; NUM_LIMBS],

    // Boolean result of a op b. Should branch if and only if cmp_result = 1.
    pub cmp_result: T,
    pub imm: T,

    pub opcode_beq_flag: T,
    pub opcode_bne_flag: T,

    pub diff_inv_marker: [T; NUM_LIMBS],
}
*)
Record BranchEqualCoreCols (T : Set) (NUM_LIMBS : Z) : Set := {
  a : list T;
  b : list T;
  cmp_result : T;
  imm : T;
  opcode_beq_flag : T;
  opcode_bne_flag : T;
  diff_inv_marker : list T;
}.

(* 
#[derive(Copy, Clone, Debug)]
pub struct BranchEqualCoreAir<const NUM_LIMBS: usize> {
    offset: usize,
    pc_step: u32,
}
*)
Record BranchEqualCoreAir (NUM_LIMBS : Z) : Set := {
  offset : Z;
  pc_step : Z;
}.

(* ************* *)
(* ****FOCUS**** *)
(* ************* *)
(* 
impl<F: Field, const NUM_LIMBS: usize> BaseAir<F> for BranchEqualCoreAir<NUM_LIMBS> {
    fn width(&self) -> usize {
        BranchEqualCoreCols::<F, NUM_LIMBS>::width()
    }
}
*)
Module Impl_BaseAir_for_BranchEqualCoreAir.
(* TODO: investigate the macro to get the exact meaning *)
(* 
  pub const fn width() -> usize {
      std::mem::size_of::<#name<u8 #(, #non_first_generics)*>>()
  }
*)
End Impl_BaseAir_for_BranchEqualCoreAir.

(* 
impl<F: Field, const NUM_LIMBS: usize> BaseAirWithPublicValues<F>
    for BranchEqualCoreAir<NUM_LIMBS>
{
}
*)
Module Impl_BaseAirWithPublicValues_for_BranchEqualCoreAir.
  (* NOTE: BaseAirWithPublicValues should be able to use all functions from
   BranchEqualCoreAir *)
End Impl_BaseAirWithPublicValues_for_BranchEqualCoreAir.

(* 
impl<AB, I, const NUM_LIMBS: usize> VmCoreAir<AB, I> for BranchEqualCoreAir<NUM_LIMBS>
where
    AB: InteractionBuilder,
    I: VmAdapterInterface<AB::Expr>,
    I::Reads: From<[[AB::Expr; NUM_LIMBS]; 2]>,
    I::Writes: Default,
    I::ProcessedInstruction: From<ImmInstruction<AB::Expr>>,
{
*)
Section Impl_VmCoreAir_for_BranchEqualCoreAir.
  Import InteractionBuilder.

  (* TODO: fill correctly into the function below *)
  Definition test (T : Set) (NUM_LIMBS : Z) (local : BranchEqualCoreCols T NUM_LIMBS): unit :=
    let cols := local in 
    let f1 := cols.(opcode_beq_flag T NUM_LIMBS) in
    let f2 := cols.(opcode_bne_flag T NUM_LIMBS) in
    let flags := [f1; f2] in
    tt.

  (* ********Types******** *)
  (* TODO:
  - Define custom type for I
  - Investigate VmCoreAir, understand its role
  - Implement type conversion for BranchEqualCoreCols
  *)
  Context `{AB : InteractionBuilder.t}.
  (* TODO: specify constraints for I's fields *)
  Context `{I : VmAdapterInterface.t}.
  Variable NUM_LIMBS : Z.

  (* TODO: maybe refine this code in the future *)
  Definition VmCoreAir_Self : Set. Admitted.

  (* 
  fn eval(
          &self,
          builder: &mut AB,
          local: &[AB::Var],
          from_pc: AB::Var,
      ) -> AdapterAirContext<AB::Expr, I> {
  *)
  Definition eval 
  (T : Set) (NUM_LIMBS : Z) (* TODO: parameters for InteractionBuilder. To be eliminated *)
  (self : Set) (local : list (AB.(Var))) (from_pc : AB.(Var)) : 
  unit :=
  (* AdapterAirContext Expr I := *)
    (* 
    let cols: &BranchEqualCoreCols<_, NUM_LIMBS> = local.borrow();
    let flags = [cols.opcode_beq_flag, cols.opcode_bne_flag];
    *)
    let cols := head local in (* TODO: examine this line of code *)
    match cols with
    | Some cols =>
      let f1 := cols.(opcode_beq_flag T NUM_LIMBS) in
      let f2 := cols.(opcode_bne_flag T NUM_LIMBS) in
      let flags := [f1; f2] in
      tt
    | None => tt
    end
    .

    (* 
    let is_valid = flags.iter().fold(AB::Expr::ZERO, |acc, &flag| {
              builder.assert_bool(flag);
              acc + flag.into()
          });
    *)
    let is_valid := _ in
    tt.

    (* 
    builder.assert_bool(is_valid.clone());
    builder.assert_bool(cols.cmp_result);
    *)
    let assert_result := if _ then true else false in
    let assert_result := if _ then assert_result else false in
    (* TODO: completely ignore all the followings if assertion is false *)

    (* 
    let a = &cols.a;
    let b = &cols.b;
    let inv_marker = &cols.diff_inv_marker;
    *)
    let a := cols.(a) in
    let b := cols.(b) in
    let inv_maker := cols.(diff_inv_marker) in

    (* 
    // 1 if cmp_result indicates a and b are equal, 0 otherwise
    let cmp_eq =
        cols.cmp_result * cols.opcode_beq_flag + not(cols.cmp_result) * cols.opcode_bne_flag;
    let mut sum = cmp_eq.clone();
    *)
    let cmp_eq := cols.cmp_result * cols.opcode_beq_flag 
      + not(cols.cmp_result) * cols.opcode_bne_flag in
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

          let expected_opcode = flags
              .iter()
              .zip(BranchEqualOpcode::iter())
              .fold(AB::Expr::ZERO, |acc, (flag, opcode)| {
                  acc + ( \*flag).into() * AB::Expr::from_canonical_u8(opcode as u8)
              })
              + AB::Expr::from_canonical_usize(self.offset);

          let to_pc = from_pc
              + cols.cmp_result * cols.imm
              + not(cols.cmp_result) * AB::Expr::from_canonical_u32(self.pc_step);

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
      }
  *)

End Impl_VmCoreAir_for_BranchEqualCoreAir.

(*
    fn start_offset(&self) -> usize {
        self.offset
    }
}

#[repr(C)]
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct BranchEqualCoreRecord<T, const NUM_LIMBS: usize> {
    #[serde(with = "BigArray")]
    pub a: [T; NUM_LIMBS],
    #[serde(with = "BigArray")]
    pub b: [T; NUM_LIMBS],
    pub cmp_result: T,
    pub imm: T,
    pub diff_inv_val: T,
    pub diff_idx: usize,
    pub opcode: BranchEqualOpcode,
}

#[derive(Debug)]
pub struct BranchEqualCoreChip<const NUM_LIMBS: usize> {
    pub air: BranchEqualCoreAir<NUM_LIMBS>,
}

impl<const NUM_LIMBS: usize> BranchEqualCoreChip<NUM_LIMBS> {
    pub fn new(offset: usize, pc_step: u32) -> Self {
        Self {
            air: BranchEqualCoreAir { offset, pc_step },
        }
    }
}

impl<F: PrimeField32, I: VmAdapterInterface<F>, const NUM_LIMBS: usize> VmCoreChip<F, I>
    for BranchEqualCoreChip<NUM_LIMBS>
where
    I::Reads: Into<[[F; NUM_LIMBS]; 2]>,
    I::Writes: Default,
{
    type Record = BranchEqualCoreRecord<F, NUM_LIMBS>;
    type Air = BranchEqualCoreAir<NUM_LIMBS>;

    #[allow(clippy::type_complexity)]
    fn execute_instruction(
        &self,
        instruction: &Instruction<F>,
        from_pc: u32,
        reads: I::Reads,
    ) -> Result<(AdapterRuntimeContext<F, I>, Self::Record)> {
        let Instruction { opcode, c: imm, .. } = *instruction;
        let branch_eq_opcode =
            BranchEqualOpcode::from_usize(opcode.local_opcode_idx(self.air.offset));

        let data: [[F; NUM_LIMBS]; 2] = reads.into();
        let x = data[0].map(|x| x.as_canonical_u32());
        let y = data[1].map(|y| y.as_canonical_u32());
        let (cmp_result, diff_idx, diff_inv_val) = run_eq::<F, NUM_LIMBS>(branch_eq_opcode, &x, &y);

        let output = AdapterRuntimeContext {
            to_pc: cmp_result.then_some((F::from_canonical_u32(from_pc) + imm).as_canonical_u32()),
            writes: Default::default(),
        };
        let record = BranchEqualCoreRecord {
            opcode: branch_eq_opcode,
            a: data[0],
            b: data[1],
            cmp_result: F::from_bool(cmp_result),
            imm,
            diff_idx,
            diff_inv_val,
        };

        Ok((output, record))
    }

    fn get_opcode_name(&self, opcode: usize) -> String {
        format!(
            "{:?}",
            BranchEqualOpcode::from_usize(opcode - self.air.offset)
        )
    }

    fn generate_trace_row(&self, row_slice: &mut [F], record: Self::Record) {
        let row_slice: &mut BranchEqualCoreCols<_, NUM_LIMBS> = row_slice.borrow_mut();
        row_slice.a = record.a;
        row_slice.b = record.b;
        row_slice.cmp_result = record.cmp_result;
        row_slice.imm = record.imm;
        row_slice.opcode_beq_flag = F::from_bool(record.opcode == BranchEqualOpcode::BEQ);
        row_slice.opcode_bne_flag = F::from_bool(record.opcode == BranchEqualOpcode::BNE);
        row_slice.diff_inv_marker = array::from_fn(|i| {
            if i == record.diff_idx {
                record.diff_inv_val
            } else {
                F::ZERO
            }
        });
    }

    fn air(&self) -> &Self::Air {
        &self.air
    }
}

// Returns (cmp_result, diff_idx, x[diff_idx] - y[diff_idx])
pub(super) fn run_eq<F: PrimeField32, const NUM_LIMBS: usize>(
    local_opcode: BranchEqualOpcode,
    x: &[u32; NUM_LIMBS],
    y: &[u32; NUM_LIMBS],
) -> (bool, usize, F) {
    for i in 0..NUM_LIMBS {
        if x[i] != y[i] {
            return (
                local_opcode == BranchEqualOpcode::BNE,
                i,
                (F::from_canonical_u32(x[i]) - F::from_canonical_u32(y[i])).inverse(),
            );
        }
    }
    (local_opcode == BranchEqualOpcode::BEQ, 0, F::ZERO)
}
*)