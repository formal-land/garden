Require Import Garden.Halo2.main.
Require Import Garden.Halo2.Gadgets.Ecc.chip.common.
Require Garden.Halo2.Gadgets.Utilities.

Import ListNotations.
Global Open Scope pstring_scope.
Global Open Scope Z_scope.

Definition configure
    (meta : ConstraintSystem.t columns)
    : ConstraintSystem.t columns :=
  let meta := ConstraintSystem.create_gate meta {|
    Gate.name := "Short fixed-base mul gate";
    Gate.constraints :=
      let y_p := Expression.Advice Advice.A1 Rotation.cur in
      let y_a := Expression.Advice Advice.A3 Rotation.cur in
      let last_window := Expression.Advice Advice.A5 Rotation.cur in
      let sign := Expression.Advice Advice.A4 Rotation.cur in
      let one := Expression.Constant 1 in
      let last_window_check :=
        Garden.Halo2.Gadgets.Utilities.bool_check last_window in
      let sign_check :=
        Garden.Halo2.Gadgets.Utilities.square sign -E one in
      let y_check := (y_p -E y_a) *E (y_p +E y_a) in
      let negation_check := sign *E y_p -E y_a in
      Constraints.with_selector
        Selector.QMulFixedShort
        [
          (Some "last_window_check", last_window_check);
          (Some "sign_check", sign_check);
          (Some "y_check", y_check);
          (Some "negation_check", negation_check)
        ];
  |} in
  meta.
