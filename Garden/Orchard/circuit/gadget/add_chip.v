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
    (a b c : Z)
    : 𝓛 columns RegionId.t (Cell.t columns RegionId.t * Cell.t columns RegionId.t * Cell.t columns RegionId.t) :=
  ℒ.AddRegion (RegionId.GadgetLocal RegionId.GadgetLocal.AddChip) "add" (fun region =>
    do🞵 ℛ.EnableSelector Selector.QAdd 0 "" in
    let a_cell := Cell.advice region Advice.A7 0 in
    let b_cell := Cell.advice region Advice.A8 0 in
    let c_cell := Cell.advice region Advice.A6 0 in
    return🞵 (a_cell, b_cell, c_cell)).
