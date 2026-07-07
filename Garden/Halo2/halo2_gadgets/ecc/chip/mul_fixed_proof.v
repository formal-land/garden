Require Import Garden.Halo2.main.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.lemmas.
Require Import Garden.Halo2.halo2_gadgets.utilities_proof.
Require Import Garden.Field.Field.
Require Garden.Halo2.halo2_gadgets.ecc.chip.mul_fixed.
Require Garden.Halo2.halo2_gadgets.ecc.chip.constants.
Require Import Garden.Orchard.columns.
Require Import Garden.Plonky3.M.

#[local] Existing Instance Primes.PallasPIsPrime.

Global Open Scope Z_scope.

Definition interpolated_x {p : Z} `{Prime p}
    (c0 c1 c2 c3 c4 c5 c6 c7 window : Z)
    : Z :=
  UnOp.from c0 +F
  Garden.Halo2.halo2_gadgets.utilities_proof.pow_nat window 1 *F UnOp.from c1 +F
  Garden.Halo2.halo2_gadgets.utilities_proof.pow_nat window 2 *F UnOp.from c2 +F
  Garden.Halo2.halo2_gadgets.utilities_proof.pow_nat window 3 *F UnOp.from c3 +F
  Garden.Halo2.halo2_gadgets.utilities_proof.pow_nat window 4 *F UnOp.from c4 +F
  Garden.Halo2.halo2_gadgets.utilities_proof.pow_nat window 5 *F UnOp.from c5 +F
  Garden.Halo2.halo2_gadgets.utilities_proof.pow_nat window 6 *F UnOp.from c6 +F
  Garden.Halo2.halo2_gadgets.utilities_proof.pow_nat window 7 *F UnOp.from c7.

Module CoordsCheck.
  Definition output {p : Z} `{Prime p}
      (c0 c1 c2 c3 c4 c5 c6 c7 window u fixed_z : Z)
      : Garden.Halo2.lemmas.Point.t := {|
    Garden.Halo2.lemmas.Point.x :=
      interpolated_x c0 c1 c2 c3 c4 c5 c6 c7 window;
    Garden.Halo2.lemmas.Point.y :=
      Garden.Halo2.halo2_gadgets.utilities_proof.square u -F fixed_z;
  |}.
End CoordsCheck.

Module RunningSumCoordinatesCheck.
  Definition output {p : Z} `{Prime p}
      (c0 c1 c2 c3 c4 c5 c6 c7 z_cur z_next u fixed_z : Z)
      : Garden.Halo2.lemmas.Point.t :=
    let window :=
      z_cur -F
        z_next *F
          UnOp.from Garden.Halo2.halo2_gadgets.ecc.chip.constants.h in
    CoordsCheck.output c0 c1 c2 c3 c4 c5 c6 c7 window u fixed_z.

  (* The fixed-base coordinates [(x_p, y_p)] on advice columns A0/A1 are
     uniquely determined by the row's Lagrange-interpolation fixed coefficients,
     the running-sum cells [z_cur]/[z_next] on A4, the witness [u] on A5, and the
     fixed [z] coefficient, as constrained by [running_sum_coordinates_check_gate]. *)
  Theorem deterministic
      {RegionId : Set} (Γ : Assignment.t columns RegionId) (region : RegionId) (row : Z)
      (Hselector : Γ ⊢ ⟦ Selector.QMulFixedRunningSum ⟧ (region, row) <> 0)
      (Hgate :
        Γ ⊢ ⟦ Garden.Halo2.halo2_gadgets.ecc.chip.mul_fixed
            .running_sum_coordinates_check_gate ⟧ (region, row)) :
      {|
        Garden.Halo2.lemmas.Point.x :=
          Γ ⊢ ⟦ Expression.Advice Advice.A0 Rotation.cur ⟧ (region, row);
        Garden.Halo2.lemmas.Point.y :=
          Γ ⊢ ⟦ Expression.Advice Advice.A1 Rotation.cur ⟧ (region, row);
      |} =
        output
          (Γ ⊢ ⟦ Expression.Fixed Fixed.LagrangeCoeffs0 Rotation.cur ⟧ (region, row))
          (Γ ⊢ ⟦ Expression.Fixed Fixed.LagrangeCoeffs1 Rotation.cur ⟧ (region, row))
          (Γ ⊢ ⟦ Expression.Fixed Fixed.LagrangeCoeffs2 Rotation.cur ⟧ (region, row))
          (Γ ⊢ ⟦ Expression.Fixed Fixed.LagrangeCoeffs3 Rotation.cur ⟧ (region, row))
          (Γ ⊢ ⟦ Expression.Fixed Fixed.LagrangeCoeffs4 Rotation.cur ⟧ (region, row))
          (Γ ⊢ ⟦ Expression.Fixed Fixed.LagrangeCoeffs5 Rotation.cur ⟧ (region, row))
          (Γ ⊢ ⟦ Expression.Fixed Fixed.LagrangeCoeffs6 Rotation.cur ⟧ (region, row))
          (Γ ⊢ ⟦ Expression.Fixed Fixed.LagrangeCoeffs7 Rotation.cur ⟧ (region, row))
          (Γ ⊢ ⟦ Expression.Advice Advice.A4 Rotation.cur ⟧ (region, row))
          (Γ ⊢ ⟦ Expression.Advice Advice.A4 Rotation.next ⟧ (region, row))
          (Γ ⊢ ⟦ Expression.Advice Advice.A5 Rotation.cur ⟧ (region, row))
          (Γ ⊢ ⟦ Expression.Fixed Fixed.FixedZ Rotation.cur ⟧ (region, row)).
  Proof.
    unfold output, RunningSumCoordinatesCheck.output, CoordsCheck.output,
      interpolated_x, square, pow_nat.
    with_strategy opaque [BinOp.add BinOp.mul BinOp.sub UnOp.from] cbn in *.
    destruct Hgate as (hx & hy & _).
    specialize (hx Hselector).
    specialize (hy Hselector).
    f_equal.
    - (* [x_p] is the Lagrange interpolation of the fixed coefficients: the
         configured fold and the proof-level [interpolated_x] coincide after
         normalising the field operations. *)
      FieldRewrite.run. symmetry. exact hx.
    - (* [y_p] is recovered from the [check y] constraint [u^2 - y_p = z]. *)
      clear hx. field_solve.
  Qed.

  (* Chip-level determinism: [mul_fixed.synthesize] enables
     [QMulFixedRunningSum] at offset 0 of region [EccMulFixed], so
     [circuit_holds] discharges the [Hselector]/[Hgate] of [deterministic].
     See [CompleteAddition.synthesize_correct] (add_proof.v) for the
     template. *)
  Theorem synthesize_correct
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit :
        circuit_holds Γ
          Garden.Halo2.halo2_gadgets.ecc.chip.mul_fixed.synthesize
          (𝓒.run_unit Garden.Halo2.halo2_gadgets.ecc.chip.mul_fixed.configure
            ConstraintSystem.empty)) :
      {|
        Garden.Halo2.lemmas.Point.x :=
          Γ ⊢ ⟦ Expression.Advice Advice.A0 Rotation.cur ⟧
            (RegionId.GadgetLocal RegionId.GadgetLocal.EccMulFixed, 0);
        Garden.Halo2.lemmas.Point.y :=
          Γ ⊢ ⟦ Expression.Advice Advice.A1 Rotation.cur ⟧
            (RegionId.GadgetLocal RegionId.GadgetLocal.EccMulFixed, 0);
      |} =
        output
          (Γ ⊢ ⟦ Expression.Fixed Fixed.LagrangeCoeffs0 Rotation.cur ⟧
            (RegionId.GadgetLocal RegionId.GadgetLocal.EccMulFixed, 0))
          (Γ ⊢ ⟦ Expression.Fixed Fixed.LagrangeCoeffs1 Rotation.cur ⟧
            (RegionId.GadgetLocal RegionId.GadgetLocal.EccMulFixed, 0))
          (Γ ⊢ ⟦ Expression.Fixed Fixed.LagrangeCoeffs2 Rotation.cur ⟧
            (RegionId.GadgetLocal RegionId.GadgetLocal.EccMulFixed, 0))
          (Γ ⊢ ⟦ Expression.Fixed Fixed.LagrangeCoeffs3 Rotation.cur ⟧
            (RegionId.GadgetLocal RegionId.GadgetLocal.EccMulFixed, 0))
          (Γ ⊢ ⟦ Expression.Fixed Fixed.LagrangeCoeffs4 Rotation.cur ⟧
            (RegionId.GadgetLocal RegionId.GadgetLocal.EccMulFixed, 0))
          (Γ ⊢ ⟦ Expression.Fixed Fixed.LagrangeCoeffs5 Rotation.cur ⟧
            (RegionId.GadgetLocal RegionId.GadgetLocal.EccMulFixed, 0))
          (Γ ⊢ ⟦ Expression.Fixed Fixed.LagrangeCoeffs6 Rotation.cur ⟧
            (RegionId.GadgetLocal RegionId.GadgetLocal.EccMulFixed, 0))
          (Γ ⊢ ⟦ Expression.Fixed Fixed.LagrangeCoeffs7 Rotation.cur ⟧
            (RegionId.GadgetLocal RegionId.GadgetLocal.EccMulFixed, 0))
          (Γ ⊢ ⟦ Expression.Advice Advice.A4 Rotation.cur ⟧
            (RegionId.GadgetLocal RegionId.GadgetLocal.EccMulFixed, 0))
          (Γ ⊢ ⟦ Expression.Advice Advice.A4 Rotation.next ⟧
            (RegionId.GadgetLocal RegionId.GadgetLocal.EccMulFixed, 0))
          (Γ ⊢ ⟦ Expression.Advice Advice.A5 Rotation.cur ⟧
            (RegionId.GadgetLocal RegionId.GadgetLocal.EccMulFixed, 0))
          (Γ ⊢ ⟦ Expression.Fixed Fixed.FixedZ Rotation.cur ⟧
            (RegionId.GadgetLocal RegionId.GadgetLocal.EccMulFixed, 0)).
  Proof.
    destruct Hcircuit as [Hfacts HSatisfies].
    destruct HSatisfies as [Hgates Hlookups].
    apply deterministic.
    - (* Selector enabled by [synthesize] ([decompose_running_sum.synthesize]
         contributes no facts). *)
      cbn in Hfacts.
      destruct Hfacts as [Hselector Htrivial].
      exact (enabled_nonzero Γ Selector.QMulFixedRunningSum
        (RegionId.GadgetLocal RegionId.GadgetLocal.EccMulFixed) 0 Hselector).
    - (* The running-sum coordinates-check gate is one of the configured gates
         (alongside [decompose_running_sum]'s range-check gate). *)
      apply (satisfies_gates_at Γ
        (𝓒.run_unit Garden.Halo2.halo2_gadgets.ecc.chip.mul_fixed.configure
          ConstraintSystem.empty)
        Garden.Halo2.halo2_gadgets.ecc.chip.mul_fixed.running_sum_coordinates_check_gate
        (RegionId.GadgetLocal RegionId.GadgetLocal.EccMulFixed) 0); [| exact Hgates].
      cbn. tauto.
  Qed.
End RunningSumCoordinatesCheck.
