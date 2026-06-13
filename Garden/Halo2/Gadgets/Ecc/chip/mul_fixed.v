Require Import Garden.Halo2.main.
Require Import Garden.Halo2.Gadgets.Ecc.chip.common.
Require Garden.Halo2.Gadgets.Utilities.
Require Garden.Halo2.Gadgets.Utilities.DecomposeRunningSum.
Require Garden.Halo2.Gadgets.Ecc.chip.constants.

Import ListNotations.
Global Open Scope pstring_scope.
Global Open Scope Z_scope.

Definition lagrange_coeffs : list Fixed.t :=
  [
    Fixed.LagrangeCoeffs0;
    Fixed.LagrangeCoeffs1;
    Fixed.LagrangeCoeffs2;
    Fixed.LagrangeCoeffs3;
    Fixed.LagrangeCoeffs4;
    Fixed.LagrangeCoeffs5;
    Fixed.LagrangeCoeffs6;
    Fixed.LagrangeCoeffs7
  ].

Definition interpolated_x
    (window : Expression.t columns)
    : Expression.t columns :=
  List.fold_left
    (fun acc '(power, coeff) =>
      acc ➕
        (Garden.Halo2.Gadgets.Utilities.pow_expr window power
          ✖️ Expression.Fixed coeff Rotation.cur))
    (List.combine
      (List.seq 0 Garden.Halo2.Gadgets.Ecc.chip.constants.h_nat)
      lagrange_coeffs)
    (Expression.Constant 0).

Definition coords_check
    (window : Expression.t columns)
    : Constraints.t columns :=
  let y_p := Expression.Advice Advice.A1 Rotation.cur in
  let x_p := Expression.Advice Advice.A0 Rotation.cur in
  let z := Expression.Fixed Fixed.FixedZ Rotation.cur in
  let u := Expression.Advice Advice.A5 Rotation.cur in
  let x_check := interpolated_x window ➖ x_p in
  let y_check :=
    Garden.Halo2.Gadgets.Utilities.square u ➖ y_p ➖ z in
  let on_curve :=
    Garden.Halo2.Gadgets.Utilities.square y_p
      ➖ Garden.Halo2.Gadgets.Utilities.square x_p ✖️ x_p
      ➖ Expression.Constant Garden.Halo2.Gadgets.Ecc.chip.constants.pallas_b in
  [
    (Some "check x", Constraint.Equal (interpolated_x window) x_p);
    (Some "check y",
      Constraint.Equal
        (Garden.Halo2.Gadgets.Utilities.square u ➖ y_p)
        z);
    (Some "on-curve", Constraint.EqualZeroToPrecise on_curve)
  ].

Definition running_sum_coordinates_check_gate : Gate.t columns := {|
  Gate.name := "Running sum coordinates check";
  Gate.constraints :=
    let z_cur := Expression.Advice Advice.A4 Rotation.cur in
    let z_next := Expression.Advice Advice.A4 Rotation.next in
    let word :=
      z_cur ➖
        (z_next ● Garden.Halo2.Gadgets.Ecc.chip.constants.h) in
    Constraints.with_selector
      Selector.QMulFixedRunningSum
      (coords_check word);
|}.

Definition configure : 𝓒 columns unit :=
  do🞵
    Garden.Halo2.Gadgets.Utilities.DecomposeRunningSum.configure
      Garden.Halo2.Gadgets.Ecc.chip.constants.fixed_base_window_size
      Selector.QMulFixedRunningSum
      Advice.A4 in
  do🞵 𝓒.CreateGate running_sum_coordinates_check_gate in
  return🞵 tt.

Definition synthesize
    : 𝓛 columns RegionId.t unit :=
  do🞵 Garden.Halo2.Gadgets.Utilities.DecomposeRunningSum.synthesize in
  𝓛.AddRegion
    (RegionId.GadgetLocal RegionId.GadgetLocal.EccMulFixed)
    "Running sum coordinates check" (fun _ =>
    𝓡.EnableSelector Selector.QMulFixedRunningSum 0 "").
