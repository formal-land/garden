Require Import Garden.Halo2.main.
Require Import Garden.Halo2.Synthesis.
Require Import Garden.Orchard.columns.

Import ListNotations.
Global Open Scope pstring_scope.

Definition addition_gate : Gate.t columns := {|
  Gate.name := "Field element addition: c = a + b";
  Gate.constraints :=
    let a := Expression.Advice Advice.A7 Rotation.cur in
    let b := Expression.Advice Advice.A8 Rotation.cur in
    let c := Expression.Advice Advice.A6 Rotation.cur in
    Constraints.with_selector Selector.QAdd [
      (None, Constraint.Equal (a ➕ b) c)
    ];
|}.

Definition configure : 𝓒 columns unit :=
  do🞵 𝓒.CreateGate addition_gate in
  return🞵 tt.

Definition synthesize
    (a b c : Z)
    : 𝓛 columns RegionId.t (Cell.t columns RegionId.t * Cell.t columns RegionId.t * Cell.t columns RegionId.t) :=
  𝓛.AddRegion (RegionId.GadgetLocal RegionId.GadgetLocal.AddChip) "add" (fun region =>
    do🞵 𝓡.EnableSelector Selector.QAdd 0 "" in
    let a_cell := Cell.advice region Advice.A7 0 in
    let b_cell := Cell.advice region Advice.A8 0 in
    let c_cell := Cell.advice region Advice.A6 0 in
    return🞵 (a_cell, b_cell, c_cell)).
