Require Import ZArith.
Require Import List.
Import ListNotations.

(* 
TODO(PROGRESS):
- (Future)Write a convertion function to transform between `Number T` and its `T`, especially 
  in the context of list. Alternatively can we just delete the `Number` class safely?
- (Future)Investigate how `builder` uses `assert` and see if its necessary to use builder to invoke them
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

(* ****TOOLS**** *)
(* Just a modified product type to conviniently record the constraints.
Writer monad is definitely better but I feel it too heavy to implement for now
*)
Definition RecordRun {A B : Set} : Type := A * (list B).

(* Datatype to present all asserted constraints *)
Module Assert.
  Inductive t (A : Set) : Set :=
    | Mul : t A -> t A -> t A
    | _Add : t A -> t A -> t A
    | Neg : t A -> t A
    | Eq : t A -> t A -> t A
    | Var : A -> t A
    | One : t A
    | Zero : t A
    .
  Arguments Mul {_} _ _.
  Arguments _Add {_} _ _.
  Arguments Neg {_} _.
  Arguments Eq {_} _ _.
  Arguments Var {_} _.
  Arguments One {_}.
  Arguments Zero {_}.
End Assert.

Definition assert_zero {A : Set} (c : A) : Assert.t A :=
  Assert.Eq Assert.Zero (Assert.Var c).

Definition assert_zero_A {A : Set} (a : Assert.t A) : Assert.t A :=
  Assert.Eq Assert.Zero a.

Definition assert_one {A : Set} (c : A) : Assert.t A :=
  Assert.Eq Assert.One (Assert.Var c).

Definition assert_one_A {A : Set} (a : Assert.t A) : Assert.t A :=
  Assert.Eq Assert.One a.

Definition assert_bool {A : Set} (c : A) : Assert.t A :=
  Assert._Add (assert_zero c) (assert_one c).

Definition assert_bool_A {A : Set} (a : Assert.t A) : Assert.t A :=
  Assert._Add (assert_zero_A a) (assert_one_A a).

(* A helper function just to make the assert operations standing out *)
Definition assert {A : Set} (l : list (Assert.t A)) (a : Assert.t A) :=
  a :: l.

(* In principle, these types are supposed to be able to do math. So for InteractionBuilder
 we try to use Z to model them similar to what we do to all the Uints *)
Class Number (N : Set) : Type := {
  get_number : Z;
}.

(* ****DEPENDENCIES**** *)
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
Module Interaction.
  Record t (e : Expr) : Set := {
    message : list Expr;
    count : Expr;
    bus_index : BusIndex;
    count_weight : Z;
  }.
End Interaction.

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
  (* NOTE: maybe we should require all types to be `Number T`
  on the instance side *)
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

(* NOTE: for reference
#[proc_macro_derive(AlignedBorrow)]
pub fn aligned_borrow_derive(input: TokenStream) -> TokenStream {
    let ast = parse_macro_input!(input as DeriveInput);
    let name = &ast.ident;

    // Get first generic which must be type (ex. `T`) for input <T, N: NumLimbs, const M: usize>
    let type_generic = ast
        .generics
        .params
        .iter()
        .map(|param| match param {
            GenericParam::Type(type_param) => &type_param.ident,
            _ => panic!("Expected first generic to be a type"),
        })
        .next()
        .expect("Expected at least one generic");

    // Get generics after the first (ex. `N: NumLimbs, const M: usize`)
    // We need this because when we assert the size, we want to substitute u8 for T.
    let non_first_generics = ast
        .generics
        .params
        .iter()
        .skip(1)
        .filter_map(|param| match param {
            GenericParam::Type(type_param) => Some(&type_param.ident),
            GenericParam::Const(const_param) => Some(&const_param.ident),
            _ => None,
        })
        .collect::<Vec<_>>();

    // Get impl generics (`<T, N: NumLimbs, const M: usize>`), type generics (`<T, N>`), where
    // clause (`where T: Clone`)
    let (impl_generics, type_generics, where_clause) = ast.generics.split_for_impl();

    impl #impl_generics core::borrow::Borrow<#name #type_generics> for [#type_generic] #where_clause {
        fn borrow(&self) -> &#name #type_generics {
            debug_assert_eq!(self.len(), #name::#type_generics::width());
            let (prefix, shorts, _suffix) = unsafe { self.align_to::<#name #type_generics>() };
            debug_assert!(prefix.is_empty(), "Alignment should match");
            debug_assert_eq!(shorts.len(), 1);
            &shorts[0]
        }
    }


    let methods = quote! {
        impl #impl_generics core::borrow::Borrow<#name #type_generics> for [#type_generic] #where_clause {
            fn borrow(&self) -> &#name #type_generics {
                debug_assert_eq!(self.len(), #name::#type_generics::width());
                let (prefix, shorts, _suffix) = unsafe { self.align_to::<#name #type_generics>() };
                debug_assert!(prefix.is_empty(), "Alignment should match");
                debug_assert_eq!(shorts.len(), 1);
                &shorts[0]
            }
        }

        impl #impl_generics core::borrow::BorrowMut<#name #type_generics> for [#type_generic] #where_clause {
            fn borrow_mut(&mut self) -> &mut #name #type_generics {
                debug_assert_eq!(self.len(), #name::#type_generics::width());
                let (prefix, shorts, _suffix) = unsafe { self.align_to_mut::<#name #type_generics>() };
                debug_assert!(prefix.is_empty(), "Alignment should match");
                debug_assert_eq!(shorts.len(), 1);
                &mut shorts[0]
            }
        }

        impl #impl_generics #name #type_generics {
            pub const fn width() -> usize {
                std::mem::size_of::<#name<u8 #(, #non_first_generics)*>>()
            }
        }
    };

    TokenStream::from(methods)
}
*)

(* *************************** *)
(* ****END OF DEPENDENCIES**** *)
(* *************************** *)

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
Record BranchEqualCoreCols (T : Set) `{Number T} (NUM_LIMBS : Z) : Set := {
  a : list (Number T);
  b : list (Number T);
  cmp_result : (Number T);
  imm : (Number T);
  opcode_beq_flag : (Number T);
  opcode_bne_flag : (Number T);
  diff_inv_marker : list (Number T);
}.

(* From #[derive(AlignedBorrow)]
impl <T NUM_LIMBS> core::borrow::Borrow<BranchEqualCoreCols T NUM_LIMBS> for [T] {
    fn borrow(&self) -> &BranchEqualCoreCols T NUM_LIMBS {
        debug_assert_eq!(self.len(), BranchEqualCoreCols::<T NUM_LIMBS>::width());
        let (prefix, shorts, _suffix) = unsafe { self.align_to::<BranchEqualCoreCols T NUM_LIMBS>() };
        debug_assert!(prefix.is_empty(), "Alignment should match");
        debug_assert_eq!(shorts.len(), 1);
        &shorts[0]
    }
}
*)
Module Impl_Borrow_BranchEqualCoreCols_for_T.
  Fixpoint next_helper {T : Set} (n : nat) (src : list T) (store : list T) : list T * list T :=
    match n with
    | O => (src, [])
    | S n' => match src with
      | x :: xs => next_helper n' xs (store ++ [x])
      | [] => (src, store)
      end
    end.

  Definition next {T : Set} (n : nat) (src : list T) : list T * list T :=
    next_helper n src [].

  Definition borrow {T : Set} (cols : list (Number T)) (NUM_LIMBS : Z) (default_T : Number T)
    : BranchEqualCoreCols T NUM_LIMBS :=
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
    Build_BranchEqualCoreCols T _ NUM_LIMBS
      a b cmp_result imm opcode_beq_flag opcode_bne_flag diff_inv_marker.
End Impl_Borrow_BranchEqualCoreCols_for_T.

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
  Import Number.

  (* ********TYPES******** *)
  (* TODO:
  - Investigate VmCoreAir, understand its role
  *)
  Context `{AB : InteractionBuilder.t}.
  Context `{I : VmAdapterInterface.t}.
  (* NOTE: demo to require subfield of I to be instance
    Context `{From I.Reads}. *)
  Variable NUM_LIMBS : Z.

  Parameter default_AB_Var : Number AB.(Var).

  (* Definition Self := VmCoreAir AB I. *)
  Definition Self : Set. Admitted. (* NOTE: stub *)

  (* ********FUNCTIIONS******** *)
  (* 
  fn eval(
          &self,
          builder: &mut AB,
          local: &[AB::Var],
          from_pc: AB::Var,
      ) -> AdapterAirContext<AB::Expr, I> {
  *)
  Definition eval 
    (self : Self) (local : list (Number AB.(Var))) (from_pc : AB.(Var)) : 
      (@RecordRun unit (Assert.t Z)) :=
      (* AdapterAirContext Expr I := *)
    let record : list (Assert.t Z) := [] in
    (* 
    let cols: &BranchEqualCoreCols<_, NUM_LIMBS> = local.borrow();
    let flags = [cols.opcode_beq_flag, cols.opcode_bne_flag];
    *)
    let cols := @Impl_Borrow_BranchEqualCoreCols_for_T.borrow AB.(Var)
      local NUM_LIMBS default_AB_Var in
    let f1 := cols.(opcode_beq_flag AB.(Var) NUM_LIMBS).(get_number) in
    let f2 := cols.(opcode_bne_flag AB.(Var) NUM_LIMBS).(get_number) in
    (* 
    let is_valid = flags.iter().fold(AB::Expr::ZERO, |acc, &flag| {
              builder.assert_bool(flag);
              acc + flag.into()
          });
    *)
    let record := assert record (assert_bool f1) in
    let record := assert record (assert_bool f2) in
    let is_valid := Assert._Add (Assert.Var f1) (Assert.Var f2) in
    (* 
    builder.assert_bool(is_valid.clone());
    builder.assert_bool(cols.cmp_result);
    *)
    let record := assert record (assert_bool_A is_valid) in
    let cmp_result := cols.(cmp_result AB.(Var) NUM_LIMBS).(get_number) in
    let record := assert record (assert_bool cmp_result) in
    (* 
    let a = &cols.a;
    let b = &cols.b;
    let inv_marker = &cols.diff_inv_marker;
    *)
    let a := cols.(a AB.(Var) NUM_LIMBS) in
    let b := cols.(b AB.(Var) NUM_LIMBS) in
    let inv_maker := cols.(diff_inv_marker AB.(Var) NUM_LIMBS) in
    (* 
    // 1 if cmp_result indicates a and b are equal, 0 otherwise
    let cmp_eq =
        cols.cmp_result * cols.opcode_beq_flag + not(cols.cmp_result) * cols.opcode_bne_flag;
    let mut sum = cmp_eq.clone();
    *)
    let opcode_beq_flag := cols.(opcode_beq_flag AB.(Var) NUM_LIMBS).(get_number) in
    let opcode_bne_flag := cols.(opcode_bne_flag AB.(Var) NUM_LIMBS).(get_number) in
    let cmp_eq := Assert._Add 
      (Assert.Mul (Assert.Var cmp_result) (Assert.Var opcode_beq_flag))
      (Assert.Mul (Assert.Neg (Assert.Var cmp_result)) (Assert.Var opcode_bne_flag)) in
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
    (* NOTE: A sole line `when(a).b` works as just a * b. If a sub builder 
      is built with `when`, every constraints for the sub builder are prefixed with `a *`.
    *)
    let fix loop (n : nat) (sum : Assert.t Z) (record : list (Assert.t Z)) {struct n} := 
      match n with 
      | O => (sum, record)
      | S n' =>
        let x := minus (minus (Z.to_nat NUM_LIMBS) 1) n' in
        let a_i := (nth n a default_AB_Var).(get_number) in
        let b_i := (nth n b default_AB_Var).(get_number) in
        let inv_maker_i := (nth n inv_maker default_AB_Var).(get_number) in
        (* I feel minus doesnt need to be put into the contraint and can be computed immediately *)
        let sum := Assert._Add sum (Assert.Mul (Assert.Var (Zminus a_i b_i)) (Assert.Var inv_maker_i)) in
        let record := assert record (assert_zero_A (Assert.Mul cmp_eq (Assert.Var (Zminus a_i b_i)))) in
        loop n' sum record
      end
    in
    let (sum, record) := loop (Z.to_nat NUM_LIMBS) sum record in

    (* ************* *)
    (* ****FOCUS**** *)
    (* ************* *)
    (* 
    let expected_opcode = flags
        .iter()
        .zip(BranchEqualOpcode::iter())
        .fold(AB::Expr::ZERO, |acc, (flag, opcode)| {
            acc + ( \*flag).into() * AB::Expr::from_canonical_u8(opcode as u8)
        })
        + AB::Expr::from_canonical_usize(self.offset);
    *)
    (* 
    let to_pc = from_pc
              + cols.cmp_result * cols.imm
              + not(cols.cmp_result) * AB::Expr::from_canonical_u32(self.pc_step);
    *)
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
    
    (tt, record)
    .

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