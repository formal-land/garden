Require Import Garden.Halo2.main.
Require Import Garden.Halo2.Synthesis.
Require Import Garden.Orchard.columns.
Require Garden.Halo2.halo2_gadgets.utilities.

Import ListNotations.
Global Open Scope pstring_scope.

Definition cond_swap_gate
    (q_swap : Selector.t)
    (a b a_swapped b_swapped swap : Advice.t)
    : Gate.t columns := {|
  Gate.name := "a' = b ⋅ swap + a ⋅ (1-swap)";
  Gate.constraints :=
    let a := Expression.Advice a Rotation.cur in
    let b := Expression.Advice b Rotation.cur in
    let a_swapped := Expression.Advice a_swapped Rotation.cur in
    let b_swapped := Expression.Advice b_swapped Rotation.cur in
    let swap := Expression.Advice swap Rotation.cur in
    Constraints.with_selector q_swap [
      (Some "a check",
        Constraint.Equal
          a_swapped
          (Garden.Halo2.halo2_gadgets.utilities.ternary swap b a));
      (Some "b check",
        Constraint.Equal
          b_swapped
          (Garden.Halo2.halo2_gadgets.utilities.ternary swap a b));
      (Some "swap is bool", Constraint.Boolean swap)
    ];
|}.

Definition configure_instance
    (q_swap : Selector.t)
    (a b a_swapped b_swapped swap : Advice.t)
    : 𝓒 columns unit :=
  do🞵 𝓒.CreateGate (cond_swap_gate q_swap a b a_swapped b_swapped swap) in
  return🞵 tt.

Definition configure_1 : 𝓒 columns unit :=
  configure_instance
    Selector.QCondSwap1
    Advice.A0
    Advice.A1
    Advice.A2
    Advice.A3
    Advice.A4.

Definition configure_2 : 𝓒 columns unit :=
  configure_instance
    Selector.QCondSwap2
    Advice.A5
    Advice.A6
    Advice.A7
    Advice.A8
    Advice.A9.

Definition synthesize_instance
    (q_swap : Selector.t)
    : 𝓛 columns RegionId.t unit :=
  𝓛.AddRegion
    (RegionId.GadgetLocal RegionId.GadgetLocal.CondSwap)
    "conditional swap" (fun _ =>
    𝓡.EnableSelector q_swap 0 "").

Definition synthesize_1
    : 𝓛 columns RegionId.t unit :=
  synthesize_instance Selector.QCondSwap1.

Definition synthesize_2
    : 𝓛 columns RegionId.t unit :=
  synthesize_instance Selector.QCondSwap2.
