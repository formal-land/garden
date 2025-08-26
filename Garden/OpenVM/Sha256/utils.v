Require Import Garden.Plonky3.M.
Require Import Garden.Plonky3.MExpr.
Require Import OpenVM.primitives.utils.

(* pub const SHA256_ROW_VAR_CNT: usize = 5; *)
Definition SHA256_ROW_VAR_CNT : Z := 5.

(* pub const SHA256_ROUNDS_PER_ROW: usize = 4; *)
Definition SHA256_ROUNDS_PER_ROW : Z := 4.

(* pub const SHA256_WORD_BITS: usize = 32; *)
Definition SHA256_WORD_BITS : Z := 32.

(* pub const SHA256_WORD_U16S: usize = SHA256_WORD_BITS / 16; *)
Definition SHA256_WORD_U16S : Z := SHA256_WORD_BITS / 16.

(* pub const SHA256_WORD_U8S: usize = SHA256_WORD_BITS / 8; *)
Definition SHA256_WORD_U8S : Z := SHA256_WORD_BITS / 8.

(* pub const SHA256_HASH_WORDS: usize = 8; *)
Definition SHA256_HASH_WORDS : Z := 8.

(*
pub(crate) fn xor_bit<F: FieldAlgebra + Clone>(
    x: impl Into<F>,
    y: impl Into<F>,
    z: impl Into<F>,
) -> F {
    let (x, y, z) = (x.into(), y.into(), z.into());
    (x.clone() * y.clone() * z.clone())
        + (x.clone() * not::<F>(y.clone()) * not::<F>(z.clone()))
        + (not::<F>(x.clone()) * y.clone() * not::<F>(z.clone()))
        + (not::<F>(x) * not::<F>(y) * z)
}
*)
Definition xor_bit (x y z : Expr.t) : Expr.t :=
  (x *E y *E z) +E
  (x *E Expr.not y *E Expr.not z) +E
  (Expr.not x *E y *E Expr.not z) +E
  (Expr.not x *E Expr.not y *E z).

(*
pub(crate) fn xor<F: FieldAlgebra + Clone>(
    x: &[impl Into<F> + Clone; SHA256_WORD_BITS],
    y: &[impl Into<F> + Clone; SHA256_WORD_BITS],
    z: &[impl Into<F> + Clone; SHA256_WORD_BITS],
) -> [F; SHA256_WORD_BITS] {
    array::from_fn(|i| xor_bit(x[i].clone(), y[i].clone(), z[i].clone()))
}
*)
Definition xor (x y z : Array.t Expr.t SHA256_WORD_BITS) : Array.t Expr.t SHA256_WORD_BITS :=
  {|
    Array.get (i : Z) := xor_bit x.[i] y.[i] z.[i];
  |}.

(*
pub(crate) fn rotr<F: FieldAlgebra + Clone>(
    bits: &[impl Into<F> + Clone; SHA256_WORD_BITS],
    n: usize,
) -> [F; SHA256_WORD_BITS] {
    array::from_fn(|i| bits[(i + n) % SHA256_WORD_BITS].clone().into())
}
*)
Definition rotr (bits : Array.t Expr.t SHA256_WORD_BITS) (n : Z) :
    Array.t Expr.t SHA256_WORD_BITS :=
  {|
    Array.get (i : Z) := bits.[(i + n) mod SHA256_WORD_BITS];
  |}.

(*
pub(crate) fn shr<F: FieldAlgebra + Clone>(
    bits: &[impl Into<F> + Clone; SHA256_WORD_BITS],
    n: usize,
) -> [F; SHA256_WORD_BITS] {
    array::from_fn(|i| {
        if i + n < SHA256_WORD_BITS {
            bits[i + n].clone().into()
        } else {
            F::ZERO
        }
    })
}
*)
Definition shr (bits : Array.t Expr.t SHA256_WORD_BITS) (n : Z) : Array.t Expr.t SHA256_WORD_BITS :=
  {|
    Array.get (i : Z) :=
      if i + n <? SHA256_WORD_BITS then
        bits.[i + n]
      else
        Expr.ZERO;
  |}.

(*
pub(crate) fn small_sig0_field<F: FieldAlgebra + Clone>(
    x: &[impl Into<F> + Clone; SHA256_WORD_BITS],
) -> [F; SHA256_WORD_BITS] {
    xor(&rotr::<F>(x, 7), &rotr::<F>(x, 18), &shr::<F>(x, 3))
}
*)
Definition small_sig0_field (x : Array.t Expr.t SHA256_WORD_BITS) :
    Array.t Expr.t SHA256_WORD_BITS :=
  xor (rotr x 7) (rotr x 18) (shr x 3).

(*
pub(crate) fn small_sig1_field<F: FieldAlgebra + Clone>(
    x: &[impl Into<F> + Clone; SHA256_WORD_BITS],
) -> [F; SHA256_WORD_BITS] {
    xor(&rotr::<F>(x, 17), &rotr::<F>(x, 19), &shr::<F>(x, 10))
}
*)
Definition small_sig1_field (x : Array.t Expr.t SHA256_WORD_BITS) :
    Array.t Expr.t SHA256_WORD_BITS :=
  xor (rotr x 17) (rotr x 19) (shr x 10).

(*
pub fn constraint_word_addition<AB: AirBuilder>(
    builder: &mut AB,
    terms_bits: &[&[impl Into<AB::Expr> + Clone; SHA256_WORD_BITS]],
    terms_limb: &[&[impl Into<AB::Expr> + Clone; SHA256_WORD_U16S]],
    expected_sum: &[impl Into<AB::Expr> + Clone; SHA256_WORD_BITS],
    carries: &[impl Into<AB::Expr> + Clone; SHA256_WORD_U16S],
) {
    for i in 0..SHA256_WORD_U16S {
        let mut limb_sum = if i == 0 {
            AB::Expr::ZERO
        } else {
            carries[i - 1].clone().into()
        };
        for term in terms_bits {
            limb_sum += compose::<AB::Expr>(&term[i * 16..(i + 1) * 16], 1);
        }
        for term in terms_limb {
            limb_sum += term[i].clone().into();
        }
        let expected_sum_limb = compose::<AB::Expr>(&expected_sum[i * 16..(i + 1) * 16], 1)
            + carries[i].clone().into() * AB::Expr::from_canonical_u32(1 << 16);
        builder.assert_eq(limb_sum, expected_sum_limb);
    }
}
*)
Definition constrain_word_addition
    (terms_bits : list (Array.t Expr.t SHA256_WORD_BITS))
    (terms_limb : list (Array.t Expr.t SHA256_WORD_U16S))
    (expected_sum : Array.t Expr.t SHA256_WORD_BITS)
    (carries : Array.t Expr.t SHA256_WORD_U16S) :
    MExpr.t unit :=
  MExpr.for_in_zero_to_n SHA256_WORD_U16S (fun i =>
    let limb_sum : Expr.t :=
      if i =? 0 then
        Expr.ZERO
      else
        carries.[i - 1] in
    let limb_sum : Expr.t :=
      Lists.List.fold_left (fun limb_sum term =>
        limb_sum +E utils.compose (Array.slice_range term (i * 16) ((i + 1) * 16)) 1
      )
      terms_bits
      limb_sum in
    let limb_sum : Expr.t :=
      Lists.List.fold_left (fun limb_sum term =>
        limb_sum +E term.[i]
      )
      terms_limb
      limb_sum in
    let expected_sum_limb : Expr.t :=
      compose (Array.slice_range expected_sum (i * 16) ((i + 1) * 16)) 1 +E
      carries.[i] *E Expr.from_canonical_u32 (2 ^ 16) in
    MExpr.assert_eq limb_sum expected_sum_limb
  ).
