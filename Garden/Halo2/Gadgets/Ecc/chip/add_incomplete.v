Require Import Garden.Halo2.main.
Require Import Garden.Halo2.Gadgets.Ecc.chip.common.
Require Garden.Halo2.Gadgets.Utilities.

Import ListNotations.
Global Open Scope pstring_scope.

Definition configure
    (meta : ConstraintSystem.t columns)
    : ConstraintSystem.t columns :=
  let meta := ConstraintSystem.create_gate meta {|
    Gate.name := "incomplete addition";
    Gate.constraints :=
      let x_p := Expression.Advice Advice.A0 Rotation.cur in
      let y_p := Expression.Advice Advice.A1 Rotation.cur in
      let x_q := Expression.Advice Advice.A2 Rotation.cur in
      let y_q := Expression.Advice Advice.A3 Rotation.cur in
      let x_r := Expression.Advice Advice.A2 Rotation.next in
      let y_r := Expression.Advice Advice.A3 Rotation.next in
      let poly1 :=
        (x_r +E x_q +E x_p)
          *E (x_p -E x_q)
          *E (x_p -E x_q)
          -E Garden.Halo2.Gadgets.Utilities.square (y_p -E y_q) in
      let poly2 :=
        (y_r +E y_q) *E (x_p -E x_q)
          -E (y_p -E y_q) *E (x_q -E x_r) in
      Constraints.with_selector Selector.QAddIncomplete [
        (Some "x_r", poly1);
        (Some "y_r", poly2)
      ];
  |} in
  meta.
