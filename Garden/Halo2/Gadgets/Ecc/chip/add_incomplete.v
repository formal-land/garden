Require Import Garden.Halo2.main.
Require Import Garden.Halo2.Gadgets.Ecc.chip.common.
Require Garden.Halo2.Gadgets.Utilities.

Import ListNotations.
Global Open Scope pstring_scope.

Definition incomplete_addition_gate : Gate.t columns := {|
  Gate.name := "incomplete addition";
  Gate.constraints :=
    let x_p := Expression.Advice Advice.A0 Rotation.cur in
    let y_p := Expression.Advice Advice.A1 Rotation.cur in
    let x_q := Expression.Advice Advice.A2 Rotation.cur in
    let y_q := Expression.Advice Advice.A3 Rotation.cur in
    let x_r := Expression.Advice Advice.A2 Rotation.next in
    let y_r := Expression.Advice Advice.A3 Rotation.next in
    let poly1 :=
      (x_r ➕ x_q ➕ x_p)
        ✖️ (x_p ➖ x_q)
        ✖️ (x_p ➖ x_q)
        ➖ Garden.Halo2.Gadgets.Utilities.square (y_p ➖ y_q) in
    let poly2 :=
      (y_r ➕ y_q) ✖️ (x_p ➖ x_q)
        ➖ (y_p ➖ y_q) ✖️ (x_q ➖ x_r) in
    Constraints.with_selector Selector.QAddIncomplete [
      (Some "x_r", Constraint.EqualZeroToPrecise poly1);
      (Some "y_r", Constraint.EqualZeroToPrecise poly2)
    ];
|}.

Definition configure : 𝓒 columns unit :=
  do🞵 𝓒.CreateGate incomplete_addition_gate in
  return🞵 tt.

Definition synthesize
    : 𝓛 columns RegionId.t unit :=
  𝓛.AddRegion
    (RegionId.GadgetLocal RegionId.GadgetLocal.EccAddIncomplete)
    "incomplete addition" (fun _ =>
    𝓡.EnableSelector Selector.QAddIncomplete 0 "").
