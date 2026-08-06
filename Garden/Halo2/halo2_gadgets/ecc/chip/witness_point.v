Require Import Garden.Halo2.main.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.common.
Require Garden.Halo2.halo2_gadgets.utilities.
Require Garden.Halo2.halo2_gadgets.ecc.chip.constants.

Import ListNotations.
Global Open Scope pstring_scope.
Global Open Scope Z_scope.

Definition curve_eqn
    (x y : Advice.t)
    : Expression.t columns :=
  let x := Expression.Advice x Rotation.cur in
  let y := Expression.Advice y Rotation.cur in
  Garden.Halo2.halo2_gadgets.utilities.square y
    ➖ (Garden.Halo2.halo2_gadgets.utilities.square x ✖️ x)
    ➖ Expression.Constant Garden.Halo2.halo2_gadgets.ecc.chip.constants.pallas_b.

Definition witness_point_gate : Gate.t columns := {|
  Gate.name := "witness point";
  Gate.constraints :=
    let x_cur := Expression.Advice Advice.A0 Rotation.cur in
    let y_cur := Expression.Advice Advice.A1 Rotation.cur in
    let on_curve := curve_eqn Advice.A0 Advice.A1 in
    Constraints.with_selector Selector.QWitnessPoint [
      (Some "x == 0 v on_curve",
        Constraint.EitherZeroToPrecise x_cur on_curve);
      (Some "y == 0 v on_curve",
        Constraint.EitherZeroToPrecise y_cur on_curve)
    ];
|}.

Definition witness_non_identity_point_gate : Gate.t columns := {|
  Gate.name := "witness non-identity point";
  Gate.constraints :=
    Constraints.with_selector Selector.QWitnessPointNonId [
      (Some "on_curve",
        Constraint.EqualZeroToPrecise (curve_eqn Advice.A0 Advice.A1))
    ];
|}.

Definition configure : 𝓒 columns unit :=
  do🞵 𝓒.CreateGate witness_point_gate in
  do🞵 𝓒.CreateGate witness_non_identity_point_gate in
  return🞵 tt.

Definition synthesize
    : 𝓛 columns RegionId.t unit :=
  do🞵
    𝓛.AddRegion
      (RegionId.GadgetLocal RegionId.GadgetLocal.EccWitnessPoint)
      "witness point" (fun _ =>
      𝓡.EnableSelector Selector.QWitnessPoint 0 "") in
  𝓛.AddRegion
    (RegionId.GadgetLocal RegionId.GadgetLocal.EccWitnessNonIdentityPoint)
    "witness non-identity point" (fun _ =>
    𝓡.EnableSelector Selector.QWitnessPointNonId 0 "").
