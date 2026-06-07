Require Import Garden.Halo2.main.
Require Import Garden.Orchard.columns.
Require Garden.Halo2.Gadgets.Utilities.CondSwap.

Import ListNotations.
Global Open Scope pstring_scope.
Global Open Scope Z_scope.

Definition configure_instance
    (meta : ConstraintSystem.t columns)
    (q_decompose : Selector.t)
    (configure_cond_swap : ConstraintSystem.t columns -> ConstraintSystem.t columns)
    (a_col b_col c_col left_col right_col : Advice.t)
    : ConstraintSystem.t columns :=
  let meta := configure_cond_swap meta in
  let meta := ConstraintSystem.create_gate meta {|
    Gate.name := "Decomposition check";
    Gate.constraints :=
      let l_whole := Expression.Advice right_col Rotation.next in
      let two_pow_5 := Expression.Constant (2 ^ 5) in
      let two_pow_10 := Expression.Constant (2 ^ 10) in
      let a_whole := Expression.Advice a_col Rotation.cur in
      let b_whole := Expression.Advice b_col Rotation.cur in
      let c_whole := Expression.Advice c_col Rotation.cur in
      let left_node := Expression.Advice left_col Rotation.cur in
      let right_node := Expression.Advice right_col Rotation.cur in
      let z1_a := Expression.Advice a_col Rotation.next in
      let a_1 := z1_a in
      let a_0 := a_whole -E (a_1 *E two_pow_10) in
      let z1_b := Expression.Advice b_col Rotation.next in
      let b_1 := Expression.Advice c_col Rotation.next in
      let b_2 := Expression.Advice left_col Rotation.next in
      let b1_b2_check := z1_b -E (b_1 +E b_2 *E two_pow_5) in
      let b_0 := b_whole -E (z1_b *E two_pow_10) in
      let left_check :=
        let two_pow_240 := Expression.Constant (2 ^ 240) in
        let reconstructed := a_1 +E ((b_0 +E b_1 *E two_pow_10) *E two_pow_240) in
        reconstructed -E left_node in
      let right_check := b_2 +E c_whole *E two_pow_5 -E right_node in
      Constraints.with_selector q_decompose [
        (Some "l_check", a_0 -E l_whole);
        (Some "left_check", left_check);
        (Some "right_check", right_check);
        (Some "b1_b2_check", b1_b2_check)
      ];
  |} in
  meta.

Definition configure_1
    (meta : ConstraintSystem.t columns)
    : ConstraintSystem.t columns :=
  configure_instance
    meta
    Selector.QMerkleDecompose1
    Garden.Halo2.Gadgets.Utilities.CondSwap.configure_1
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
    Selector.QMerkleDecompose2
    Garden.Halo2.Gadgets.Utilities.CondSwap.configure_2
    Advice.A5
    Advice.A6
    Advice.A7
    Advice.A8
    Advice.A9.
