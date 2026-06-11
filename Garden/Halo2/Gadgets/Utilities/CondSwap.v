Require Import Garden.Halo2.main.
Require Import Garden.Halo2.Synthesis.
Require Import Garden.Orchard.columns.
Require Garden.Halo2.Gadgets.Utilities.

Import ListNotations.
Global Open Scope pstring_scope.

Definition configure_instance
    (meta : ConstraintSystem.t columns)
    (q_swap : Selector.t)
    (a b a_swapped b_swapped swap : Advice.t)
    : ConstraintSystem.t columns :=
  let meta := ConstraintSystem.create_gate meta {|
    Gate.name := "a' = b ⋅ swap + a ⋅ (1-swap)";
    Gate.constraints :=
      let a := Expression.Advice a Rotation.cur in
      let b := Expression.Advice b Rotation.cur in
      let a_swapped := Expression.Advice a_swapped Rotation.cur in
      let b_swapped := Expression.Advice b_swapped Rotation.cur in
      let swap := Expression.Advice swap Rotation.cur in
      let a_check :=
        a_swapped ➖
          Garden.Halo2.Gadgets.Utilities.ternary swap b a in
      let b_check :=
        b_swapped ➖
          Garden.Halo2.Gadgets.Utilities.ternary swap a b in
      let bool_check := Garden.Halo2.Gadgets.Utilities.bool_check swap in
      Constraints.with_selector q_swap [
        (Some "a check", Constraint.EqualZeroToPrecise a_check);
        (Some "b check", Constraint.EqualZeroToPrecise b_check);
        (Some "swap is bool", Constraint.EqualZeroToPrecise bool_check)
      ];
  |} in
  meta.

Definition configure_1
    (meta : ConstraintSystem.t columns)
    : ConstraintSystem.t columns :=
  configure_instance
    meta
    Selector.QCondSwap1
    Advice.A0
    Advice.A1
    Advice.A2
    Advice.A3
    Advice.A4.

Definition configure_2
    (meta : ConstraintSystem.t columns)
    : ConstraintSystem.t columns :=
  configure_instance
    meta
    Selector.QCondSwap2
    Advice.A5
    Advice.A6
    Advice.A7
    Advice.A8
    Advice.A9.

Definition synthesize_instance
    (q_swap : Selector.t)
    : 𝓛 columns RegionId.t unit :=
  ℒ.AddRegion
    (RegionId.GadgetLocal RegionId.GadgetLocal.CondSwap)
    "conditional swap" (fun _ =>
    ℛ.EnableSelector q_swap 0 "").

Definition synthesize_1
    : 𝓛 columns RegionId.t unit :=
  synthesize_instance Selector.QCondSwap1.

Definition synthesize_2
    : 𝓛 columns RegionId.t unit :=
  synthesize_instance Selector.QCondSwap2.
