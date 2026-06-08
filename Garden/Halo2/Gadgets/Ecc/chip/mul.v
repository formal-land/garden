Require Import Garden.Halo2.main.
Require Import Garden.Halo2.Gadgets.Ecc.chip.common.
Require Garden.Halo2.Gadgets.Utilities.
Require Garden.Halo2.Gadgets.Ecc.chip.mul.incomplete.
Require Garden.Halo2.Gadgets.Ecc.chip.mul.complete.
Require Garden.Halo2.Gadgets.Ecc.chip.mul.overflow.

Import ListNotations.
Global Open Scope pstring_scope.
Global Open Scope Z_scope.

Definition configure
    (meta : ConstraintSystem.t columns)
    : ConstraintSystem.t columns :=
  let meta :=
    Garden.Halo2.Gadgets.Ecc.chip.mul.incomplete.configure
      meta
      Selector.QMulIncompleteHi1
      Selector.QMulIncompleteHi2
      Selector.QMulIncompleteHi3
      Advice.A9
      Advice.A3
      Advice.A0
      Advice.A1
      Advice.A4
      Advice.A5 in
  let meta :=
    Garden.Halo2.Gadgets.Ecc.chip.mul.incomplete.configure
      meta
      Selector.QMulIncompleteLo1
      Selector.QMulIncompleteLo2
      Selector.QMulIncompleteLo3
      Advice.A6
      Advice.A7
      Advice.A0
      Advice.A1
      Advice.A8
      Advice.A2 in
  let meta :=
    Garden.Halo2.Gadgets.Ecc.chip.mul.complete.configure
      meta in
  let meta :=
    Garden.Halo2.Gadgets.Ecc.chip.mul.overflow.configure
      meta in
  let meta := ConstraintSystem.create_gate meta {|
    Gate.name := "LSB check";
    Gate.constraints :=
      let z_1 := Expression.Advice Advice.A9 Rotation.cur in
      let z_0 := Expression.Advice Advice.A9 Rotation.next in
      let x_p := Expression.Advice Advice.A0 Rotation.cur in
      let y_p := Expression.Advice Advice.A1 Rotation.cur in
      let base_x := Expression.Advice Advice.A0 Rotation.next in
      let base_y := Expression.Advice Advice.A1 Rotation.next in
      let lsb := z_0 ➖ (z_1 ● 2) in
      let bool_check := Garden.Halo2.Gadgets.Utilities.bool_check lsb in
      let lsb_x :=
        Garden.Halo2.Gadgets.Utilities.ternary
          lsb
          x_p
          (x_p ➖ base_x) in
      let lsb_y :=
        Garden.Halo2.Gadgets.Utilities.ternary
          lsb
          y_p
          (y_p ➕ base_y) in
      Constraints.with_selector
        Selector.QMulLsb
        [
          (Some "bool_check", Constraint.EqualZeroToPrecise bool_check);
          (Some "lsb_x", Constraint.EqualZeroToPrecise lsb_x);
          (Some "lsb_y", Constraint.EqualZeroToPrecise lsb_y)
        ];
  |} in
  meta.

Definition synthesize
    : Layouter.t columns unit :=
  let_ℒ _ :=
    Garden.Halo2.Gadgets.Ecc.chip.mul.incomplete.synthesize
      Selector.QMulIncompleteHi1
      Selector.QMulIncompleteHi2
      Selector.QMulIncompleteHi3 in
  let_ℒ _ :=
    Garden.Halo2.Gadgets.Ecc.chip.mul.incomplete.synthesize
      Selector.QMulIncompleteLo1
      Selector.QMulIncompleteLo2
      Selector.QMulIncompleteLo3 in
  let_ℒ _ := Garden.Halo2.Gadgets.Ecc.chip.mul.complete.synthesize in
  let_ℒ _ := Garden.Halo2.Gadgets.Ecc.chip.mul.overflow.synthesize in
  Layouter.assign_region "LSB check" (
    Region.enable_selector Selector.QMulLsb 0 "").
