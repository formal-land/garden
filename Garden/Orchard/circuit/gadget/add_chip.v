Require Import Garden.Halo2.main.
Require Import Garden.Orchard.columns.

Import ListNotations.
Global Open Scope pstring_scope.

Definition configure
    (meta : ConstraintSystem.t columns)
    : ConstraintSystem.t columns :=
  let meta := ConstraintSystem.create_gate meta {|
    Gate.name := "Field element addition: c = a + b";
    Gate.constraints :=
      let a := Expression.Advice Advice.A7 Rotation.cur in
      let b := Expression.Advice Advice.A8 Rotation.cur in
      let c := Expression.Advice Advice.A6 Rotation.cur in
      Constraints.with_selector Selector.QAdd [
        (None, Constraint.EqualZeroToPrecise (a ➕ b ➖ c))
      ];
  |} in
  meta.
