Require Import Garden.Halo2.main.
Require Import Garden.Halo2.Synthesis.
Require Import Garden.Orchard.columns.
Require Garden.Halo2.Gadgets.Utilities.CondSwap.

Import ListNotations.
Global Open Scope pstring_scope.
Global Open Scope Z_scope.

Definition decomposition_check_gate
    (q_decompose : Selector.t)
    (a_col b_col c_col left_col right_col : Advice.t)
    : Gate.t columns := {|
  Gate.name := "Decomposition check";
  Gate.constraints :=
    let l_whole := Expression.Advice right_col Rotation.next in
    let a_whole := Expression.Advice a_col Rotation.cur in
    let b_whole := Expression.Advice b_col Rotation.cur in
    let c_whole := Expression.Advice c_col Rotation.cur in
    let left_node := Expression.Advice left_col Rotation.cur in
    let right_node := Expression.Advice right_col Rotation.cur in
    let z1_a := Expression.Advice a_col Rotation.next in
    let a_1 := z1_a in
    let a_0 := a_whole ➖ (a_1 ● (2 ^ 10)) in
    let z1_b := Expression.Advice b_col Rotation.next in
    let b_1 := Expression.Advice c_col Rotation.next in
    let b_2 := Expression.Advice left_col Rotation.next in
    let b1_b2_check := z1_b ➖ (b_1 ➕ (b_2 ● (2 ^ 5))) in
    let b_0 := b_whole ➖ (z1_b ● (2 ^ 10)) in
    let left_check :=
      let reconstructed :=
        a_1 ➕ ((b_0 ➕ (b_1 ● (2 ^ 10))) ● (2 ^ 240)) in
      reconstructed ➖ left_node in
    let right_check := b_2 ➕ (c_whole ● (2 ^ 5)) ➖ right_node in
    Constraints.with_selector q_decompose [
      (Some "l_check", Constraint.Equal a_0 l_whole);
      (Some "left_check", Constraint.EqualZeroToPrecise left_check);
      (Some "right_check",
        Constraint.Equal (b_2 ➕ (c_whole ● (2 ^ 5))) right_node);
      (Some "b1_b2_check",
        Constraint.Equal z1_b (b_1 ➕ (b_2 ● (2 ^ 5))))
    ];
|}.

Definition configure_instance_program
    (q_decompose : Selector.t)
    (configure_cond_swap : 𝓒 columns unit)
    (a_col b_col c_col left_col right_col : Advice.t)
    : 𝓒 columns unit :=
  do🞵 configure_cond_swap in
  do🞵
    𝓒.CreateGate
      (decomposition_check_gate q_decompose a_col b_col c_col left_col right_col) in
  return🞵 tt.

Definition configure_instance
    (meta : ConstraintSystem.t columns)
    (q_decompose : Selector.t)
    (configure_cond_swap : 𝓒 columns unit)
    (a_col b_col c_col left_col right_col : Advice.t)
    : ConstraintSystem.t columns :=
  𝓒.run_unit
    (configure_instance_program
      q_decompose
      configure_cond_swap
      a_col
      b_col
      c_col
      left_col
      right_col)
    meta.

Definition configure_1_program : 𝓒 columns unit :=
  configure_instance_program
    Selector.QMerkleDecompose1
    Garden.Halo2.Gadgets.Utilities.CondSwap.configure_1_program
    Advice.A0
    Advice.A1
    Advice.A2
    Advice.A3
    Advice.A4.

Definition configure_1
    (meta : ConstraintSystem.t columns)
    : ConstraintSystem.t columns :=
  𝓒.run_unit configure_1_program meta.

Definition configure_2_program : 𝓒 columns unit :=
  configure_instance_program
    Selector.QMerkleDecompose2
    Garden.Halo2.Gadgets.Utilities.CondSwap.configure_2_program
    Advice.A5
    Advice.A6
    Advice.A7
    Advice.A8
    Advice.A9.

Definition configure_2
    (meta : ConstraintSystem.t columns)
    : ConstraintSystem.t columns :=
  𝓒.run_unit configure_2_program meta.

Definition synthesize_instance
    (q_decompose : Selector.t)
    (synthesize_cond_swap : 𝓛 columns RegionId.t unit)
    : 𝓛 columns RegionId.t unit :=
  do🞵 synthesize_cond_swap in
  𝓛.AddRegion
    (RegionId.GadgetLocal RegionId.GadgetLocal.SinsemillaMerkleDecomposition)
    "Decomposition check" (fun _ =>
    𝓡.EnableSelector q_decompose 0 "").

Definition synthesize_1
    : 𝓛 columns RegionId.t unit :=
  synthesize_instance
    Selector.QMerkleDecompose1
    Garden.Halo2.Gadgets.Utilities.CondSwap.synthesize_1.

Definition synthesize_2
    : 𝓛 columns RegionId.t unit :=
  synthesize_instance
    Selector.QMerkleDecompose2
    Garden.Halo2.Gadgets.Utilities.CondSwap.synthesize_2.
