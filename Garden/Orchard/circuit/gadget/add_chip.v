Require Import Garden.Halo2.main.
Require Import Garden.Halo2.Synthesis.
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

Definition synthesize
    (a b c : Value.t)
    : Layouter.t columns (Cell.t columns * Cell.t columns * Cell.t columns) :=
  Layouter.assign_region "add" (
    let_ℛ _ := Region.enable_selector Selector.QAdd 0 "" in
    let_ℛ a_cell := Region.assign_advice "a" Advice.A7 0 a in
    let_ℛ b_cell := Region.assign_advice "b" Advice.A8 0 b in
    let_ℛ c_cell := Region.assign_advice "c" Advice.A6 0 c in
    return_ℛ (a_cell, b_cell, c_cell)).
