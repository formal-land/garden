Require Import Garden.Plonky3.M.
Require Import Garden.Plonky3.MExpr.

(*
pub struct Encoder {
    var_cnt: usize,
    flag_cnt: usize,
    max_flag_degree: u32,
    pts: Vec<Vec<u32>>,
    reserve_invalid: bool,
}
*)
Module Encoder.
  Record t : Set := {
    var_cnt : Z;
    flag_cnt : Z;
    max_flag_degree : Z;
    pts : list (list Z);
    reserve_invalid : bool;
  }.
End Encoder.

(*
fn expression_for_point<AB: InteractionBuilder>(
    &self,
    pt: &[u32],
    vars: &[AB::Var],
) -> AB::Expr {
    assert_eq!(self.var_cnt, pt.len(), "wrong point dimension");
    assert_eq!(self.var_cnt, vars.len(), "wrong number of variables");
    let mut expr = AB::Expr::ONE;
    let mut denom = AB::F::ONE;

    // First part: product for each coordinate
    for (i, &coord) in pt.iter().enumerate() {
        for j in 0..coord {
            expr *= vars[i] - AB::Expr::from_canonical_u32(j);
            denom *= AB::F::from_canonical_u32(coord - j);
        }
    }

    // Second part: ensure the sum doesn't exceed max_degree
    {
        let sum: u32 = pt.iter().sum();
        let var_sum = vars.iter().fold(AB::Expr::ZERO, |acc, &v| acc + v);
        for j in 0..(self.max_flag_degree - sum) {
            expr *= AB::Expr::from_canonical_u32(self.max_flag_degree - j) - var_sum.clone();
            denom *= AB::F::from_canonical_u32(j + 1);
        }
    }
    expr * denom.inverse()
}
*)
Definition expression_for_point
    (self : Encoder.t)
    (pt : Array.t Z self.(Encoder.var_cnt))
    (vars : Array.t Var.t self.(Encoder.var_cnt)) :
    Expr.t.
Admitted.

(*
pub fn sum_of_unused<AB: InteractionBuilder>(&self, vars: &[AB::Var]) -> AB::Expr {
    let mut expr = AB::Expr::ZERO;
    for i in (self.flag_cnt + self.reserve_invalid as usize)..self.pts.len() {
        expr += self.expression_for_point::<AB>(&self.pts[i], vars);
    }
    expr
}
*)
Definition sum_of_unused (self : Encoder.t) (vars : Array.t Var.t self.(Encoder.var_cnt)) : Expr.t.
Admitted.
  (* let expr : Expr.t := Expr.ZERO in
  let start_index : Z :=
    self.(Encoder.flag_cnt) + Z.b2z self.(Encoder.reserve_invalid) in
  Lists.List.fold_left
    (fun expr i =>
      let i := Z.of_nat i in
      expr +E expression_for_point self.(Encoder.pts).[i] vars
    )
    (List.seq (Z.to_nat start_index) (List.length self.(Encoder.pts) - Z.to_nat start_index))
    Expr.ZERO. *)

(*
fn eval<'a>(&'a self, builder: &'a mut AB, local: &'a [AB::Var])
where
    AB: 'a,
    AB::Expr: 'a,
{
    assert_eq!(local.len(), self.var_cnt, "wrong number of variables");

    // Helper function to create the product (x-0)(x-1)...(x-max_degree)
    let falling_factorial = |lin: AB::Expr| {
        let mut res = AB::Expr::ONE;
        for i in 0..=self.max_flag_degree {
            res *= lin.clone() - AB::Expr::from_canonical_u32(i);
        }
        res
    };
    // All x_i are from 0 to max_degree
    for &var in local.iter() {
        builder.assert_zero(falling_factorial(var.into()))
    }
    // Sum of all x_i is from 0 to max_degree
    builder.assert_zero(falling_factorial(
        local.iter().fold(AB::Expr::ZERO, |acc, &x| acc + x),
    ));
    // This constraint guarantees that the encoded point either:
    // 1. Is the zero point (0,...,0) if reserved for invalid/dummy rows, or
    // 2. Represents one of our defined selectors (flag_idx from 0 to flag_cnt-1)
    // It works by requiring the sum of Lagrange polynomials for all unused points to be zero,
    // which forces the current point to be one of our explicitly defined selector patterns
    builder.assert_zero(self.sum_of_unused::<AB>(local));
}
*)
Definition eval (self : Encoder.t) (local : Array.t Var.t self.(Encoder.var_cnt)) : MExpr.t unit :=
  let falling_factorial (lin : Expr.t) : Expr.t :=
    let res : Expr.t := Expr.ONE in
    Lists.List.fold_left
      (fun res i =>
        let i := Z.of_nat i in
        res *E (lin -E Expr.from_canonical_u32 i)
      )
      (List.seq 0 (Z.to_nat (self.(Encoder.max_flag_degree) + 1)))
      res in
  let! _ :=
    MExpr.for_in_zero_to_n self.(Encoder.var_cnt) (fun i =>
      MExpr.assert_zero (falling_factorial local.[i])
    ) in
  let! _ := MExpr.assert_zero (falling_factorial (
    Lists.List.fold_left (fun acc x => acc +E Expr.Var x) (Array.to_list local) Expr.ZERO
  )) in
  let! _ := MExpr.assert_zero (sum_of_unused self local) in
  MExpr.pure tt.
