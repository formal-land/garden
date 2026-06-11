Require Import Garden.Halo2.main.
Require Import Garden.Halo2.Gadgets.Ecc.chip.common.
Require Garden.Halo2.Gadgets.Utilities.
Require Garden.Halo2.Gadgets.Ecc.chip.constants.

Import ListNotations.
Global Open Scope pstring_scope.
Global Open Scope Z_scope.

Definition configure
    (meta : ConstraintSystem.t columns)
    : ConstraintSystem.t columns :=
  let meta := ConstraintSystem.create_gate meta {|
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
      let alpha_1_range_check :=
        Garden.Halo2.Gadgets.Utilities.range_check alpha_1 4 in
      let alpha_2_range_check :=
        Garden.Halo2.Gadgets.Utilities.bool_check alpha_2 in
      let z_84_alpha_check :=
        z_84_alpha ➖ (alpha_1 ➕ (alpha_2 ● (2 ^ 2))) in
      let alpha_0_prime_check :=
        alpha_0_prime
          ➖ (alpha_0
            ➕ Expression.Constant (2 ^ 130)
            ➖ Expression.Constant Garden.Halo2.Gadgets.Ecc.chip.constants.t_p) in
      let alpha_0_hi_120 :=
        z_44_alpha ➖ (z_84_alpha ✖️ Expression.Constant (2 ^ 120)) in
      let a_43 :=
        z_43_alpha
          ➖ (z_44_alpha ● Garden.Halo2.Gadgets.Ecc.chip.constants.h) in
      Constraints.with_selector
        Selector.QMulFixedBaseField
        [
          (Some "MSB = 1 => alpha_1 = 0",
            Constraint.EqualZeroToPrecise (alpha_2 ✖️ alpha_1));
          (Some "MSB = 1 => alpha_0_hi_120 = 0",
            Constraint.EqualZeroToPrecise (alpha_2 ✖️ alpha_0_hi_120));
          (Some "MSB = 1 => a_43 = 0 or 1",
            Constraint.EqualZeroToPrecise
              (alpha_2 ✖️ Garden.Halo2.Gadgets.Utilities.bool_check a_43));
          (Some "MSB = 1 => z_13_alpha_0_prime = 0",
            Constraint.EqualZeroToPrecise (alpha_2 ✖️ z_13_alpha_0_prime));
          (Some "alpha_1_range_check",
            Constraint.EqualZeroToPrecise alpha_1_range_check);
          (Some "alpha_2_range_check",
            Constraint.EqualZeroToPrecise alpha_2_range_check);
          (Some "z_84_alpha_check",
            Constraint.EqualZeroToPrecise z_84_alpha_check);
          (Some "alpha_0_prime check",
            Constraint.EqualZeroToPrecise alpha_0_prime_check)
        ];
  |} in
  meta.

Definition synthesize
    : 𝓛 columns RegionId.t unit :=
  ℒ.AddRegion
    (RegionId.GadgetLocal RegionId.GadgetLocal.EccMulFixedBaseField)
    "Canonicity checks" (fun _ =>
    ℛ.EnableSelector Selector.QMulFixedBaseField 0 "").
