Require Import Garden.Halo2.main.
Require Import Garden.Halo2.Gadgets.Ecc.chip.common.
Require Garden.Halo2.Gadgets.Utilities.

Import ListNotations.
Global Open Scope pstring_scope.
Global Open Scope Z_scope.

Definition decompose_scalar_complete_gate : Gate.t columns := {|
  Gate.name := "Decompose scalar for complete bits of variable-base mul";
  Gate.constraints :=
    let z_prev := Expression.Advice Advice.A9 Rotation.prev in
    let z_next := Expression.Advice Advice.A9 Rotation.next in
    let k := z_next ➖ (Expression.Constant 2 ✖️ z_prev) in
    let base_y := Expression.Advice Advice.A9 Rotation.cur in
    let y_p := Expression.Advice Advice.A1 Rotation.prev in
    let y_switch :=
      Garden.Halo2.Gadgets.Utilities.ternary
        k
        (base_y ➖ y_p)
        (base_y ➕ y_p) in
    Constraints.with_selector Selector.QMulDecomposeVar [
      (Some "bool_check", Constraint.Boolean k);
      (Some "y_switch", Constraint.EqualZeroToPrecise y_switch)
    ];
|}.

Definition configure : 𝓒 columns unit :=
  do🞵 𝓒.CreateGate decompose_scalar_complete_gate in
  return🞵 tt.

Definition synthesize
    : 𝓛 columns RegionId.t unit :=
  𝓛.AddRegion
    (RegionId.GadgetLocal RegionId.GadgetLocal.EccMulComplete)
    "Decompose scalar for complete bits of variable-base mul" (fun _ =>
    𝓡.EnableSelector Selector.QMulDecomposeVar 0 "").
