(** * Arithmetic helpers used by the Halo 2 verifier over Vesta

    Transcription of the verifier-facing pieces of
    [halo2_proofs/src/arithmetic.rs]: Horner [eval_polynomial], a
    [lagrange_interpolate] that returns the same coefficient list as the
    Rust routine, and [best_multiexp] as a left fold of Vesta scalar
    multiplication. *)

Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Lists.List.
Require Import Garden.Rust.primitives.
Require Import Garden.Halo2.halo2_proofs.pasta.

Import List.ListNotations.
Global Open Scope Z_scope.

Module Arithmetic.

  Definition eval_polynomial (poly : list Z) (point : Z) : Z :=
    List.fold_left
      (fun acc coeff => acc *s point +s coeff)
      (List.rev poly)
      0.

  (** Product of [(X - x_k)] for [k <> j], scaled by [eval_j / denom_j],
      as a low-degree-first coefficient list of length [n]. *)
  Definition mul_linear (poly : list Z) (c0 c1 : Z) : list Z :=
    (* (c0 + c1 X) * poly *)
    let shifted := 0 :: poly in
    let scaled0 := List.map (fun a => a *s c0) poly ++ [0] in
    let scaled1 := List.map (fun a => a *s c1) shifted in
    List.map (fun '(a, b) => a +s b) (List.combine scaled0 scaled1).

  Fixpoint basis_poly (j : nat) (k : nat) (points : list Z) (inv_denom : Z) : list Z :=
    match points with
    | [] => [inv_denom]
    | xk :: rest =>
      if Nat.eqb j k then basis_poly j (S k) rest inv_denom
      else
        let tail := basis_poly j (S k) rest inv_denom in
        mul_linear tail (Fp.opp xk) 1
    end.

  Definition denom_j (j : nat) (points : list Z) : Z :=
    let xj := List.nth j points 0 in
    fst (List.fold_left
      (fun '(acc, k) xk =>
        if Nat.eqb j k then (acc, S k)
        else ((acc *s (xj -s xk)), S k))
      points (Fp.from 1, 0%nat)).

  Definition lagrange_interpolate (points evals : list Z) : list Z :=
    let n := List.length points in
    match n with
    | O => []
    | 1%nat => evals
    | _ =>
      List.fold_left
        (fun acc j =>
          let invd :=
            match Fp.invert (denom_j j points) with
            | Some i => i
            | None => 0
            end in
          let basis := basis_poly j 0%nat points invd in
          let ej := List.nth j evals 0 in
          List.map (fun '(a, b) => a +s (b *s ej)) (List.combine acc basis))
        (List.seq 0 n)
        (List.repeat 0 n)
    end.

  Definition best_multiexp (scalars : list Z) (bases : list VestaCurve.point) : VestaCurve.point :=
    List.fold_left
      (fun acc '(s, P) => VestaCurve.add acc (VestaCurve.mul s P))
      (List.combine scalars bases)
      VestaCurve.identity.

  Definition is_identity_point (P : VestaCurve.point) : bool :=
    VestaEncoding.is_identity P.
End Arithmetic.
