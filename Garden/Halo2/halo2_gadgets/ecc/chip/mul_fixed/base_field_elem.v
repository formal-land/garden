Require Import Garden.Halo2.main.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.common.
Require Garden.Halo2.halo2_gadgets.utilities.
Require Garden.Halo2.halo2_gadgets.ecc.chip.constants.

Import ListNotations.
Global Open Scope pstring_scope.
Global Open Scope Z_scope.

Definition canonicity_checks_gate : Gate.t columns := {|
  Gate.name := "Canonicity checks";
  Gate.constraints :=
    let alpha := Expression.Advice Advice.A6 Rotation.prev in
    let z_84_alpha := Expression.Advice Advice.A8 Rotation.prev in
    let alpha_0 := alpha ➖ (z_84_alpha ● (2 ^ 252)) in
    let alpha_1 := Expression.Advice Advice.A7 Rotation.cur in
    let alpha_2 := Expression.Advice Advice.A8 Rotation.cur in
    let alpha_0_prime := Expression.Advice Advice.A6 Rotation.cur in
    let z_13_alpha_0_prime :=
      Expression.Advice Advice.A6 Rotation.next in
    let z_44_alpha := Expression.Advice Advice.A7 Rotation.next in
    let z_43_alpha := Expression.Advice Advice.A8 Rotation.next in
    let z_84_alpha_check :=
      z_84_alpha ➖ (alpha_1 ➕ (alpha_2 ● (2 ^ 2))) in
    let alpha_0_prime_check :=
      alpha_0_prime
        ➖ (alpha_0
          ➕ Expression.Constant (2 ^ 130)
          ➖ Expression.Constant Garden.Halo2.halo2_gadgets.ecc.chip.constants.t_p) in
    let alpha_0_hi_120 :=
      z_44_alpha ➖ (z_84_alpha ✖️ Expression.Constant (2 ^ 120)) in
    let a_43 :=
      z_43_alpha
        ➖ (z_44_alpha ● Garden.Halo2.halo2_gadgets.ecc.chip.constants.h) in
    Constraints.with_selector
      Selector.QMulFixedBaseField
      [
        (Some "MSB = 1 => alpha_1 = 0",
          Constraint.Either
            (Constraint.EqualZeroToPrecise alpha_2)
            (Constraint.EqualZeroToPrecise alpha_1));
        (Some "MSB = 1 => alpha_0_hi_120 = 0",
          Constraint.Either
            (Constraint.EqualZeroToPrecise alpha_2)
            (Constraint.EqualZeroToPrecise alpha_0_hi_120));
        (Some "MSB = 1 => a_43 = 0 or 1",
          Constraint.Either
            (Constraint.EqualZeroToPrecise alpha_2)
            (Constraint.Boolean a_43));
        (Some "MSB = 1 => z_13_alpha_0_prime = 0",
          Constraint.Either
            (Constraint.EqualZeroToPrecise alpha_2)
            (Constraint.EqualZeroToPrecise z_13_alpha_0_prime));
        (Some "alpha_1_range_check",
          Constraint.Range alpha_1 4);
        (Some "alpha_2_range_check",
          Constraint.Boolean alpha_2);
        (Some "z_84_alpha_check",
          Constraint.Equal z_84_alpha (alpha_1 ➕ (alpha_2 ● (2 ^ 2))));
        (Some "alpha_0_prime check",
          Constraint.Equal
            alpha_0_prime
            (alpha_0
              ➕ Expression.Constant (2 ^ 130)
              ➖ Expression.Constant Garden.Halo2.halo2_gadgets.ecc.chip.constants.t_p))
      ];
|}.

Definition configure : 𝓒 columns unit :=
  do🞵 𝓒.CreateGate canonicity_checks_gate in
  return🞵 tt.

Definition synthesize
    : 𝓛 columns RegionId.t unit :=
  𝓛.AddRegion
    (RegionId.GadgetLocal RegionId.GadgetLocal.EccMulFixedBaseField)
    "Canonicity checks" (fun _ =>
    𝓡.EnableSelector Selector.QMulFixedBaseField 0 "").
