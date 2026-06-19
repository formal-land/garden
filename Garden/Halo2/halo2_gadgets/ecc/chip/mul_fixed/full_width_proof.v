Require Import Garden.Halo2.main.
Require Import Garden.Halo2.proof.
Require Garden.Halo2.halo2_gadgets.ecc.chip.mul_fixed.full_width.
Require Import Garden.Field.Field.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.mul_fixed_proof.
Require Import Garden.Halo2.halo2_gadgets.utilities_proof.
Require Import Garden.Orchard.columns.
Require Import Garden.Plonky3.M.

#[local] Existing Instance Primes.PallasPIsPrime.

Global Open Scope Z_scope.

Module FullWidthFixedBaseScalarMul.
  Definition output {p : Z} `{Prime p}
      (c0 c1 c2 c3 c4 c5 c6 c7 window u fixed_z : Z)
      : Garden.Halo2.halo2_gadgets.utilities_proof.Point.t :=
    CoordsCheck.output c0 c1 c2 c3 c4 c5 c6 c7 window u fixed_z.

  (* The full-width fixed-base point [(x_p, y_p)] on A0/A1 is uniquely determined
     by the Lagrange-interpolation fixed coefficients, the window on A4, the
     witness [u] on A5, and the fixed [z], via [full_width_fixed_base_scalar_mul_gate]. *)
  Theorem deterministic
      (Γ : Assignment.t columns) (row : Z)
      (Hselector : Γ ⊢ ⟦ Selector.QMulFixedFull ⟧ row <> 0)
      (Hgate :
        Γ ⊢ ⟦ Garden.Halo2.halo2_gadgets.ecc.chip.mul_fixed.full_width
            .full_width_fixed_base_scalar_mul_gate ⟧ row) :
      {|
        Garden.Halo2.halo2_gadgets.utilities_proof.Point.x :=
          Γ ⊢ ⟦ Expression.Advice Advice.A0 Rotation.cur ⟧ row;
        Garden.Halo2.halo2_gadgets.utilities_proof.Point.y :=
          Γ ⊢ ⟦ Expression.Advice Advice.A1 Rotation.cur ⟧ row;
      |} =
        output
          (Γ ⊢ ⟦ Expression.Fixed Fixed.LagrangeCoeffs0 Rotation.cur ⟧ row)
          (Γ ⊢ ⟦ Expression.Fixed Fixed.LagrangeCoeffs1 Rotation.cur ⟧ row)
          (Γ ⊢ ⟦ Expression.Fixed Fixed.LagrangeCoeffs2 Rotation.cur ⟧ row)
          (Γ ⊢ ⟦ Expression.Fixed Fixed.LagrangeCoeffs3 Rotation.cur ⟧ row)
          (Γ ⊢ ⟦ Expression.Fixed Fixed.LagrangeCoeffs4 Rotation.cur ⟧ row)
          (Γ ⊢ ⟦ Expression.Fixed Fixed.LagrangeCoeffs5 Rotation.cur ⟧ row)
          (Γ ⊢ ⟦ Expression.Fixed Fixed.LagrangeCoeffs6 Rotation.cur ⟧ row)
          (Γ ⊢ ⟦ Expression.Fixed Fixed.LagrangeCoeffs7 Rotation.cur ⟧ row)
          (Γ ⊢ ⟦ Expression.Advice Advice.A4 Rotation.cur ⟧ row)
          (Γ ⊢ ⟦ Expression.Advice Advice.A5 Rotation.cur ⟧ row)
          (Γ ⊢ ⟦ Expression.Fixed Fixed.FixedZ Rotation.cur ⟧ row).
  Proof.
    unfold output, FullWidthFixedBaseScalarMul.output, CoordsCheck.output,
      interpolated_x, square, pow_nat.
    with_strategy opaque [BinOp.add BinOp.mul BinOp.sub UnOp.from] cbn in *.
    destruct Hgate as (hx & hy & _ & _).
    specialize (hx Hselector).
    specialize (hy Hselector).
    f_equal.
    - (* [x_p] is the Lagrange interpolation of the fixed coefficients. *)
      FieldRewrite.run. symmetry. exact hx.
    - (* [y_p] is recovered from the [check y] constraint [u^2 - y_p = z]. *)
      clear hx. field_solve.
  Qed.
End FullWidthFixedBaseScalarMul.
