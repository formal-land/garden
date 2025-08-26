Require Import Garden.Plonky3.M.
Require Import Garden.Plonky3.MExpr.

(*
pub fn compose<F: FieldAlgebra>(a: &[impl Into<F> + Clone], limb_size: usize) -> F {
    a.iter().enumerate().fold(F::ZERO, |acc, (i, x)| {
        acc + x.clone().into() * F::from_canonical_usize(1 << (i * limb_size))
    })
}
*)
Definition compose {N : Z} (x : Array.t Expr.t N) (limb_size : Z) : Expr.t :=
  Lists.List.fold_left (fun acc (i : nat) =>
    let i : Z := Z.of_nat i in
    acc +E x.[i] *E Expr.from_canonical_usize (2 ^ (i * limb_size))
  )
  (Lists.List.seq 0 (Z.to_nat N))
  Expr.ZERO.
