Require Import ZArith.
Require Import List.
Import ListNotations.

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
Definition RecordRun {A B : Set} : Type := A * B.

(* ****DEPENDENCIES**** *)
(* 
#[repr(C)]
#[derive(AlignedBorrow)]
pub struct ImmInstruction<T> {
    pub is_valid: T,
    /// Absolute opcode number
    pub opcode: T,
    pub immediate: T,
}
*)
Module ImmInstruction.
  Record t : Set := {
    is_valid : Z;
    op_code : Z;
    immediate : Z;
  }.
End ImmInstruction.

(* Inductive Expr : Set := | Make_Expr . *)
(* Inductive BusIndex : Set := | Make_BusIndex . *)

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

(* Module Interaction.
  Record t (e : Expr) : Set := {
    message : list Expr;
    count : Expr;
    bus_index : BusIndex;
    count_weight : Z;
  }.
End Interaction. *)

(* NOTE: UNUSED *)
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
pub struct AdapterAirContext<T, I: VmAdapterInterface<T>> {
    /// Leave as `None` to allow the adapter to decide the `to_pc` automatically.
    pub to_pc: Option<T>,
    pub reads: I::Reads,
    pub writes: I::Writes,
    pub instruction: I::ProcessedInstruction,
}
*)
Module AdapterAirContext.
  Record t (instruction_type : Set) : Set := {
    to_pc : option Z;
    (* NOTE: for now we only design them as simple as they can be. We will
    see how to extend them in the future *)
    reads : list Z;
    writes : list Z;
    instruction : instruction_type;
  }.
End AdapterAirContext.

(* 
#[opcode_offset = 0x220]
#[repr(usize)]
#[allow(non_camel_case_types)]
pub enum BranchEqualOpcode {
    BEQ,
    BNE,
}
*)
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
  (* Datatype to present all asserted constraints from `assert_zero`, always and only *)
  Module Assert.
    Inductive t (A : Set) : Set :=
      | Var : A -> t A
      .
    Arguments Var {_} _.
  End Assert.

  (* NOTE: for future reference
  Class F {T : Type} : Type := {
    get_num : Z;
  }.
  *)
  Inductive F := 
  | num_f : Z -> F.

  Inductive Var := 
  | num_var : F -> Var.

  Inductive Expr :=
  | num_expr : Var -> Expr.

  Definition M := list (list Var).

  (* TODO: Extend to any types beyond Z in the future. The dependencies between 
    the types seem to be a little bit hard to express. We might find some external way
    to express this *)
  Record Builder : Type := {
    (* Types from AirBuilder
    type F: Field;
    type Expr: Algebra<Self::F> + Algebra<Self::Var>;
    type Var: Into<Self::Expr>
    type M: Matrix<Self::Var>;
    *)
    _F := F; 
    _Expr := Expr;
    _Var := Var;
    _M := M;

    (* Stores the context generated from `when` *)
    constraints : list (Assert.t Expr);
    (* Stores the result `assert_zero` makes *)
    assertions : list (Assert.t Expr);
  }.

  Definition z_to_var (z : Z) : Var :=
    num_var (num_f z).

  Definition z_to_expr (z : Z) : Expr :=
    num_expr (z_to_var z).

  Definition f_to_z (f : F) : Z := let '(num_f n) := f in n.

  Definition var_to_z (v : Var) : Z := let '(num_var f) := v in f_to_z f.

  Definition expr_to_z (e : Expr) : Z := let '(num_expr v) := e in var_to_z v.

  Definition assert_expr_to_z (a : Assert.t Expr) : Z :=
    let '(Assert.Var x) := a in expr_to_z x.

  (* NOTE: to be optimized *)
  Fixpoint aggregate_constraints (l : list (Assert.t Expr)) : option (Assert.t Expr) :=
    match l with
    | x :: [] => Some x
    | x :: xs => match (aggregate_constraints xs) with
      | Some x' => 
        let x := assert_expr_to_z x in
        let x' := assert_expr_to_z x' in
        Some (Assert.Var (z_to_expr (Z.mul x x')))
      | None => None
      end
    | [] => None
    end.

  Definition when (builder : Builder) (c : Assert.t builder.(_Expr)) : Builder :=
    let c' := builder.(constraints) in
    let a' := builder.(assertions) in
    Build_Builder (c :: c') a'.
  
  (* Pop a constraint off to simulate one constraint being removed. When it comes to 
  monad, a structure similar tos a stack would be helpful *)
  Definition end_when (builder : Builder) : Builder :=
    let c' := builder.(constraints) in
    let c := match c' with
    | [] => c'
    | _ :: c => c
    end in
    let a' := builder.(assertions) in
    Build_Builder c a'.
  
  (* NOTE: every other primitives are built on this primitive *)
  Definition assert_zero (builder : Builder) 
    (e : builder.(_Expr)) : Builder :=
    let c' := builder.(constraints) in
    let a := aggregate_constraints (c' ++ [Assert.Var e]) in
    (* desugar the option *)
    let a := match a with
    | Some a' => a'
    | None => Assert.Var e
    end in
    let '(Assert.Var a) := a in
    let a := if Z.eqb 0 (expr_to_z a) then 1%Z else 0%Z in
    Build_Builder c' (builder.(assertions) ++ [Assert.Var (z_to_expr a)]).

  Definition assert_one (builder : Builder) (e : builder.(_Expr)) : Builder :=
    let z := expr_to_z e in
    assert_zero builder (z_to_expr (Z.sub 1 z)).

  Definition assert_bool (builder : Builder) (e : builder.(_Expr)) : Builder :=
    let z := expr_to_z e in
    let bool_check := Z.mul z (Z.sub 1%Z z) in
    assert_zero builder (z_to_expr bool_check).
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
(* For similar reason to above, here we put in a concrete type and later we will
see how to extend the type *)
(* NOTE that we didnt use the T here... *)
Record BranchEqualCoreCols (NUM_LIMBS : Z) : Set := {
  a : list InteractionBuilder.Expr;
  b : list InteractionBuilder.Expr;
  cmp_result : InteractionBuilder.Expr;
  imm : InteractionBuilder.Expr;
  opcode_beq_flag : InteractionBuilder.Expr;
  opcode_bne_flag : InteractionBuilder.Expr;
  diff_inv_marker : list InteractionBuilder.Expr;
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
    | O => (src, store)
    | S n' => match src with
      | x :: xs => next_helper n' xs (store ++ [x])
      | [] => (src, store)
      end
    end.

  (* slice the first n elements of a list, return it with the remaining part of the list *)
  Definition next {T : Set} (n : nat) (src : list T) : list T * list T :=
    next_helper n src [].

  (* NOTE: for now, InteractionBuilder only *)
  Definition borrow (cols : list InteractionBuilder.Var) (NUM_LIMBS : Z) (default_T : InteractionBuilder.Var)
    : BranchEqualCoreCols NUM_LIMBS :=
    let NUM_LIMBS' := Z.to_nat NUM_LIMBS in
    let (cols, a) := next NUM_LIMBS' cols in
    let a := map InteractionBuilder.num_expr a in
    let (cols, b) := next NUM_LIMBS' cols in
    let b := map InteractionBuilder.num_expr b in
    let (cols, cmp_result) := next 1 cols in
    let cmp_result := InteractionBuilder.num_expr (match (head cmp_result) with | Some x => x | None => default_T end) in
    let (cols, imm) := next 1 cols in
    let imm := InteractionBuilder.num_expr (match (head imm) with | Some x => x | None => default_T end) in
    let (cols, opcode_beq_flag) := next 1 cols in
    let opcode_beq_flag := InteractionBuilder.num_expr (match (head opcode_beq_flag) with | Some x => x | None => default_T end) in
    let (cols, opcode_bne_flag) := next 1 cols in
    let opcode_bne_flag := InteractionBuilder.num_expr (match (head opcode_bne_flag) with | Some x => x | None => default_T end) in
    let (cols, diff_inv_marker) := next NUM_LIMBS' cols in
    let diff_inv_marker := map InteractionBuilder.num_expr diff_inv_marker in
    Build_BranchEqualCoreCols NUM_LIMBS
      a b cmp_result imm opcode_beq_flag opcode_bne_flag diff_inv_marker.
End Impl_Borrow_BranchEqualCoreCols_for_T.

(* 
#[derive(Copy, Clone, Debug)]
pub struct BranchEqualCoreAir<const NUM_LIMBS: usize> {
    offset: usize,
    pc_step: u32,
}
*)
Module BranchEqualCoreAir.
  Record t (NUM_LIMBS : Z) : Set := {
    offset : Z;
    pc_step : Z;
  }.
End BranchEqualCoreAir.

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
Module Impl_VmCoreAir_for_BranchEqualCoreAir.
  Section Impl.
  Import InteractionBuilder.
  Import Number.

  Context (builder : InteractionBuilder.Builder). (* We ignore the AB for now *)
  (* Context `{I : VmAdapterInterface.t}. *)
  (* NOTE: I stands for a `AdapterInterface` type being used in other places
  Demo to require subfield of I to be instance:
  Context `{From I.Reads}. *)
  Variable NUM_LIMBS : Z.

  Definition Self := BranchEqualCoreAir.t NUM_LIMBS.

  Parameter default_AB_Var : builder.(_Var).
  Parameter default_AB_Expr : builder.(_Expr).

  (* ********FUNCTIIONS******** *)
  (* 
  fn eval(
          &self,
          builder: &mut AB,
          local: &[AB::Var],
          from_pc: AB::Var,
      ) -> AdapterAirContext<AB::Expr, I> {
  *)
  (* NOTE: In this function:
  - `record` collects all constraints, which is the primary goal for current implementation
  *)
  Definition eval 
    (self : Self) 
    (local : list builder.(_Var)) (from_pc : builder.(_Var)) : 
      (@RecordRun (AdapterAirContext.t ImmInstruction.t) Builder) :=
    (* 
    let cols: &BranchEqualCoreCols<_, NUM_LIMBS> = local.borrow();
    let flags = [cols.opcode_beq_flag, cols.opcode_bne_flag];
    *)
    let cols := @Impl_Borrow_BranchEqualCoreCols_for_T.borrow
      local NUM_LIMBS default_AB_Var in
    let f1 := cols.(opcode_beq_flag NUM_LIMBS) in
    let f2 := cols.(opcode_bne_flag NUM_LIMBS) in
    (* 
    let is_valid = flags.iter().fold(AB::Expr::ZERO, |acc, &flag| {
              builder.assert_bool(flag);
              acc + flag.into()
          });
    *)
    let builder := assert_bool builder f1 in
    let builder := assert_bool builder f2 in
    let is_valid := Z.add (InteractionBuilder.expr_to_z f1) (InteractionBuilder.expr_to_z f2) in
    let is_valid_expr := InteractionBuilder.z_to_expr is_valid in
    (* 
    builder.assert_bool(is_valid.clone());
    builder.assert_bool(cols.cmp_result);
    *)
    let builder := assert_bool builder is_valid_expr in
    let cmp_result_expr := cols.(cmp_result NUM_LIMBS) in
    let cmp_result := InteractionBuilder.expr_to_z cmp_result_expr in
    let builder := assert_bool builder cmp_result_expr in
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
    let opcode_beq_flag_expr := cols.(opcode_beq_flag NUM_LIMBS) in
    let opcode_beq_flag := InteractionBuilder.expr_to_z opcode_beq_flag_expr in
    let opcode_bne_flag_expr := cols.(opcode_bne_flag NUM_LIMBS) in
    let opcode_bne_flag := InteractionBuilder.expr_to_z opcode_bne_flag_expr in
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
    (* NOTE: A sole line `when(a).b` works as just a * b. If a sub builder 
      is built with `when`, every constraints for the sub builder are prefixed with `a *`.
    *)
    let fix loop (n : nat) (sum : Z) 
      (builder : Builder) {struct n} := 
      match n with 
      | O => (sum, builder)
      | S n' =>
        (* 0 <= x < NUM_LIMBS *)
        let x := minus (minus (Z.to_nat NUM_LIMBS) 1) n' in
        let a_i := InteractionBuilder.expr_to_z (nth x a default_AB_Expr) in
        let b_i := InteractionBuilder.expr_to_z (nth x b default_AB_Expr) in
        let inv_maker_i := InteractionBuilder.expr_to_z 
          (nth x inv_maker default_AB_Expr) in
        let sum := Z.add sum (Z.mul (Z.sub a_i b_i) inv_maker_i) in
        let builder := assert_zero builder 
          (InteractionBuilder.z_to_expr (Z.mul cmp_eq (Z.sub a_i b_i))) in
        loop n' sum builder
      end
    in
    let (sum, builder) := loop (Z.to_nat NUM_LIMBS) sum builder in
    let builder := when builder (Assert.Var is_valid_expr) in
    let builder := assert_one builder (InteractionBuilder.z_to_expr sum) in 
    let builder := end_when builder in
    (* 
    let expected_opcode = flags
        .iter()
        .zip(BranchEqualOpcode::iter())
        .fold(AB::Expr::ZERO, |acc, (flag, opcode)| {
            acc + ( \*flag).into() * AB::Expr::from_canonical_u8(opcode as u8)
        })
        + AB::Expr::from_canonical_usize(self.offset);
    *)
    (* NOTE: WARNING: 
    - We dont't check the boundary for u8
    - The computation here is being completed immediately. Maybe we should also do it 
      for other computations. Same for the code blocks followed 
    *)
    let opcodes := map BranchEqualOpcode.as_usize BranchEqualOpcode.iter in
    let o1 := nth 0 opcodes BranchEqualOpcode.opcode_offset in
    let o2 := nth 1 opcodes BranchEqualOpcode.opcode_offset in
    let expected_opcode := Z.add 
      (Z.mul (InteractionBuilder.expr_to_z f1) o1) (Z.mul (InteractionBuilder.expr_to_z f2) o2) in
    (* 
    let to_pc = from_pc
              + cols.cmp_result * cols.imm
              + not(cols.cmp_result) * AB::Expr::from_canonical_u32(self.pc_step);
    *)
    let to_pc := InteractionBuilder.var_to_z from_pc in
    let imm := InteractionBuilder.expr_to_z (cols.(imm NUM_LIMBS)) in
    let to_pc := Z.add to_pc (Z.mul cmp_result imm) in
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
    let a := map InteractionBuilder.expr_to_z a in
    let b := map InteractionBuilder.expr_to_z b in
    let reads := a ++ b in
    let context := (AdapterAirContext.Build_t ImmInstruction.t
      (Some to_pc) reads []
      (ImmInstruction.Build_t is_valid expected_opcode imm)
    ) in
    (context, builder).
  End Impl.
End Impl_VmCoreAir_for_BranchEqualCoreAir.

Module _Test.
Definition builder : InteractionBuilder.Builder := InteractionBuilder.Build_Builder [] [].

Definition NUM_LIMBS : Z := 8.

Definition a := map Z.of_nat [0; 0; 0; 0; 0; 0; 0; 0].
Definition b := map Z.of_nat [0; 0; 0; 0; 0; 0; 0; 0].

Definition cmp_result := 1%Z.
Definition imm := 1%Z.
Definition opcode_beq_flag := 1%Z.
Definition opcode_bne_flag := 1%Z.
Definition diff_inv_marker := map Z.of_nat [0; 0; 0; 0; 0; 0; 0; 0].

Definition local : list InteractionBuilder.Var :=
  let stream := a ++ b ++ [cmp_result; imm; opcode_beq_flag; opcode_bne_flag ] ++ diff_inv_marker in
  map InteractionBuilder.z_to_var stream.

Definition from_pc : InteractionBuilder.Var := InteractionBuilder.z_to_var 0%Z.

Definition self : BranchEqualCoreAir.t NUM_LIMBS := BranchEqualCoreAir.Build_t NUM_LIMBS 0%Z 4%Z.

Definition result := Impl_VmCoreAir_for_BranchEqualCoreAir.eval builder NUM_LIMBS self local from_pc.

Definition result_builder := let '(_, b) := result in b.

Definition builder_assertions := result_builder.(InteractionBuilder.assertions).

End _Test.


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