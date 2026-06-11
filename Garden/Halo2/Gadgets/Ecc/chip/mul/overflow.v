Require Import Garden.Halo2.main.
Require Import Garden.Halo2.Gadgets.Ecc.chip.common.
Require Garden.Halo2.Gadgets.Ecc.chip.constants.

Import ListNotations.
Global Open Scope pstring_scope.
Global Open Scope Z_scope.

Definition configure
    (meta : ConstraintSystem.t columns)
    : ConstraintSystem.t columns :=
  let meta := ConstraintSystem.create_gate meta {|
    Gate.name := "overflow checks";
    Gate.constraints :=
      let one := Expression.Constant 1 in
      let two_pow_124 := Expression.Constant (2 ^ 124) in
      let two_pow_130 := two_pow_124 ✖️ Expression.Constant (2 ^ 6) in
      let z_0 := Expression.Advice Advice.A6 Rotation.prev in
      let z_130 := Expression.Advice Advice.A6 Rotation.cur in
      let eta := Expression.Advice Advice.A6 Rotation.next in
      let k_254 := Expression.Advice Advice.A7 Rotation.prev in
      let alpha := Expression.Advice Advice.A7 Rotation.cur in
      let s_minus_lo_130 := Expression.Advice Advice.A7 Rotation.next in
      let s := Expression.Advice Advice.A8 Rotation.cur in
      let s_check := s ➖ (alpha ➕ (k_254 ✖️ two_pow_130)) in
      let t_q :=
        Expression.Constant Garden.Halo2.Gadgets.Ecc.chip.constants.t_q in
      let recovery := z_0 ➖ alpha ➖ t_q in
      let lo_zero := k_254 ✖️ (z_130 ➖ two_pow_124) in
      let s_minus_lo_130_check := k_254 ✖️ s_minus_lo_130 in
      let canonicity :=
        (one ➖ k_254) ✖️ (one ➖ (z_130 ✖️ eta)) ✖️ s_minus_lo_130 in
      Constraints.with_selector Selector.QMulOverflow [
        (Some "s_check", Constraint.EqualZeroToPrecise s_check);
        (Some "recovery", Constraint.EqualZeroToPrecise recovery);
        (Some "lo_zero", Constraint.EqualZeroToPrecise lo_zero);
        (Some "s_minus_lo_130_check",
          Constraint.EqualZeroToPrecise s_minus_lo_130_check);
        (Some "canonicity", Constraint.EqualZeroToPrecise canonicity)
      ];
  |} in
  meta.

Definition synthesize
    : 𝓛 columns RegionId.t unit :=
  ℒ.AddRegion
    (RegionId.GadgetLocal RegionId.GadgetLocal.EccMulOverflowCheck)
    "overflow checks" (fun _ =>
    ℛ.EnableSelector Selector.QMulOverflow 0 "").
