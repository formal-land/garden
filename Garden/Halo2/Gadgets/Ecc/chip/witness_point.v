Require Import Garden.Halo2.main.
Require Import Garden.Halo2.Gadgets.Ecc.chip.common.
Require Garden.Halo2.Gadgets.Utilities.
Require Garden.Halo2.Gadgets.Ecc.chip.constants.

Import ListNotations.
Global Open Scope pstring_scope.
Global Open Scope Z_scope.

Definition curve_eqn
    (x y : Advice.t)
    : Expression.t columns :=
  let x := Expression.Advice x Rotation.cur in
  let y := Expression.Advice y Rotation.cur in
  Garden.Halo2.Gadgets.Utilities.square y
    ➖ (Garden.Halo2.Gadgets.Utilities.square x ✖️ x)
    ➖ Expression.Constant Garden.Halo2.Gadgets.Ecc.chip.constants.pallas_b.

Definition configure
    (meta : ConstraintSystem.t columns)
    : ConstraintSystem.t columns :=
  let meta := ConstraintSystem.create_gate meta {|
    Gate.name := "witness point";
    Gate.constraints :=
      let q_point := Expression.Selector Selector.QWitnessPoint in
      let x_cur := Expression.Advice Advice.A0 Rotation.cur in
      let y_cur := Expression.Advice Advice.A1 Rotation.cur in
      [
        (Some "x == 0 v on_curve",
          Constraint.EqualZeroToPrecise
            ((q_point ✖️ x_cur) ✖️ curve_eqn Advice.A0 Advice.A1));
        (Some "y == 0 v on_curve",
          Constraint.EqualZeroToPrecise
            ((q_point ✖️ y_cur) ✖️ curve_eqn Advice.A0 Advice.A1))
      ];
  |} in
  let meta := ConstraintSystem.create_gate meta {|
    Gate.name := "witness non-identity point";
    Gate.constraints :=
      Constraints.with_selector Selector.QWitnessPointNonId [
        (Some "on_curve",
          Constraint.EqualZeroToPrecise (curve_eqn Advice.A0 Advice.A1))
      ];
  |} in
  meta.

Definition synthesize
    : 𝓛 columns RegionId.t unit :=
  let🞵 _ :=
    ℒ.AddRegion (RegionId.of_index 0) "witness point" (
      ℛ.EnableSelector Selector.QWitnessPoint 0 "") in
  ℒ.AddRegion (RegionId.of_index 0) "witness non-identity point" (
    ℛ.EnableSelector Selector.QWitnessPointNonId 0 "").
