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
      (ρ : Evaluation.t columns)
      (Hselector : ⟦ Selector.QMulFixedFull ⟧ ρ <> 0)
      (Hgate :
        ⟦ Garden.Halo2.halo2_gadgets.ecc.chip.mul_fixed.full_width
            .full_width_fixed_base_scalar_mul_gate ⟧ ρ) :
      {|
        Garden.Halo2.halo2_gadgets.utilities_proof.Point.x :=
          ⟦ Expression.Advice Advice.A0 Rotation.cur ⟧ ρ;
        Garden.Halo2.halo2_gadgets.utilities_proof.Point.y :=
          ⟦ Expression.Advice Advice.A1 Rotation.cur ⟧ ρ;
      |} =
        output
          (⟦ Expression.Fixed Fixed.LagrangeCoeffs0 Rotation.cur ⟧ ρ)
          (⟦ Expression.Fixed Fixed.LagrangeCoeffs1 Rotation.cur ⟧ ρ)
          (⟦ Expression.Fixed Fixed.LagrangeCoeffs2 Rotation.cur ⟧ ρ)
          (⟦ Expression.Fixed Fixed.LagrangeCoeffs3 Rotation.cur ⟧ ρ)
          (⟦ Expression.Fixed Fixed.LagrangeCoeffs4 Rotation.cur ⟧ ρ)
          (⟦ Expression.Fixed Fixed.LagrangeCoeffs5 Rotation.cur ⟧ ρ)
          (⟦ Expression.Fixed Fixed.LagrangeCoeffs6 Rotation.cur ⟧ ρ)
          (⟦ Expression.Fixed Fixed.LagrangeCoeffs7 Rotation.cur ⟧ ρ)
          (⟦ Expression.Advice Advice.A4 Rotation.cur ⟧ ρ)
          (⟦ Expression.Advice Advice.A5 Rotation.cur ⟧ ρ)
          (⟦ Expression.Fixed Fixed.FixedZ Rotation.cur ⟧ ρ).
  Proof.
  Admitted.
End FullWidthFixedBaseScalarMul.
