Require Import Garden.Halo2.main.
Require Import Garden.Halo2.Gadgets.Ecc.chip.common.
Require Garden.Halo2.Gadgets.Utilities.

Import ListNotations.
Global Open Scope pstring_scope.
Global Open Scope Z_scope.

Definition short_fixed_base_mul_gate : Gate.t columns := {|
  Gate.name := "Short fixed-base mul gate";
  Gate.constraints :=
    let y_p := Expression.Advice Advice.A1 Rotation.cur in
    let y_a := Expression.Advice Advice.A3 Rotation.cur in
    let last_window := Expression.Advice Advice.A5 Rotation.cur in
    let sign := Expression.Advice Advice.A4 Rotation.cur in
    let one := Expression.Constant 1 in
    Constraints.with_selector
      Selector.QMulFixedShort
      [
        (Some "last_window_check",
          Constraint.Boolean last_window);
        (Some "sign_check",
          Constraint.Equal
            (Garden.Halo2.Gadgets.Utilities.square sign)
            one);
        (Some "y_check",
          Constraint.Either
            (Constraint.Equal y_p y_a)
            (Constraint.EqualZeroToPrecise (y_p ➕ y_a)));
        (Some "negation_check",
          Constraint.Equal (sign ✖️ y_p) y_a)
      ];
|}.

Definition configure_program : 𝓒 columns unit :=
  do🞵 𝓒.CreateGate short_fixed_base_mul_gate in
  return🞵 tt.

Definition configure
    (meta : ConstraintSystem.t columns)
    : ConstraintSystem.t columns :=
  𝓒.run_unit configure_program meta.

Definition synthesize
    : 𝓛 columns RegionId.t unit :=
  𝓛.AddRegion
    (RegionId.GadgetLocal RegionId.GadgetLocal.EccMulFixedShort)
    "Short fixed-base mul gate" (fun _ =>
    𝓡.EnableSelector Selector.QMulFixedShort 0 "").
