Require Import Garden.Halo2.main.
Require Import Garden.Orchard.columns.
Require Garden.Halo2.Gadgets.Poseidon.P128Pow5T3.
Require Garden.Halo2.Gadgets.Utilities.

Import ListNotations.
Global Open Scope pstring_scope.
Global Open Scope Z_scope.

Definition pow_5
    (value : Expression.t columns)
    : Expression.t columns :=
  let value_2 := Garden.Halo2.Gadgets.Utilities.square value in
  let value_4 := Garden.Halo2.Gadgets.Utilities.square value_2 in
  value_4 *E value.

Definition full_round_sum
    (row : nat)
    : Expression.t columns :=
  let state_0 := Expression.Advice Advice.A6 Rotation.cur in
  let state_1 := Expression.Advice Advice.A7 Rotation.cur in
  let state_2 := Expression.Advice Advice.A8 Rotation.cur in
  let rc_a_0 := Expression.Fixed Fixed.LagrangeCoeffs2 Rotation.cur in
  let rc_a_1 := Expression.Fixed Fixed.LagrangeCoeffs3 Rotation.cur in
  let rc_a_2 := Expression.Fixed Fixed.LagrangeCoeffs4 Rotation.cur in
  let state_0_sbox := pow_5 (state_0 +E rc_a_0) in
  let state_1_sbox := pow_5 (state_1 +E rc_a_1) in
  let state_2_sbox := pow_5 (state_2 +E rc_a_2) in
  (state_0_sbox *Z (P128Pow5T3.mds_coeff row 0))
    +E (state_1_sbox *Z (P128Pow5T3.mds_coeff row 1))
    +E (state_2_sbox *Z (P128Pow5T3.mds_coeff row 2)).

Definition mid
    (row : nat)
    : Expression.t columns :=
  let mid_0 := Expression.Advice Advice.A5 Rotation.cur in
  let state_1 := Expression.Advice Advice.A7 Rotation.cur in
  let state_2 := Expression.Advice Advice.A8 Rotation.cur in
  let rc_a_1 := Expression.Fixed Fixed.LagrangeCoeffs3 Rotation.cur in
  let rc_a_2 := Expression.Fixed Fixed.LagrangeCoeffs4 Rotation.cur in
  (mid_0 *Z (P128Pow5T3.mds_coeff row 0))
    +E ((state_1 +E rc_a_1) *Z (P128Pow5T3.mds_coeff row 1))
    +E ((state_2 +E rc_a_2) *Z (P128Pow5T3.mds_coeff row 2)).

Definition next
    (row : nat)
    : Expression.t columns :=
  let state_0 := Expression.Advice Advice.A6 Rotation.next in
  let state_1 := Expression.Advice Advice.A7 Rotation.next in
  let state_2 := Expression.Advice Advice.A8 Rotation.next in
  (state_0 *Z (P128Pow5T3.mds_inv_coeff row 0))
    +E (state_1 *Z (P128Pow5T3.mds_inv_coeff row 1))
    +E (state_2 *Z (P128Pow5T3.mds_inv_coeff row 2)).

Definition configure
    (meta : ConstraintSystem.t columns)
    : ConstraintSystem.t columns :=
  let meta := ConstraintSystem.create_gate meta {|
    Gate.name := "full round";
    Gate.constraints :=
      let state_0_next := Expression.Advice Advice.A6 Rotation.next in
      let state_1_next := Expression.Advice Advice.A7 Rotation.next in
      let state_2_next := Expression.Advice Advice.A8 Rotation.next in
      Constraints.with_selector Selector.QPoseidonFull [
        (None, full_round_sum 0 -E state_0_next);
        (None, full_round_sum 1 -E state_1_next);
        (None, full_round_sum 2 -E state_2_next)
      ];
  |} in
  let meta := ConstraintSystem.create_gate meta {|
    Gate.name := "partial rounds";
    Gate.constraints :=
      let cur_0 := Expression.Advice Advice.A6 Rotation.cur in
      let mid_0 := Expression.Advice Advice.A5 Rotation.cur in
      let rc_a_0 := Expression.Fixed Fixed.LagrangeCoeffs2 Rotation.cur in
      let rc_b_0 := Expression.Fixed Fixed.LagrangeCoeffs5 Rotation.cur in
      let rc_b_1 := Expression.Fixed Fixed.LagrangeCoeffs6 Rotation.cur in
      let rc_b_2 := Expression.Fixed Fixed.LagrangeCoeffs7 Rotation.cur in
      Constraints.with_selector Selector.QPoseidonPartial [
        (None, pow_5 (cur_0 +E rc_a_0) -E mid_0);
        (None, pow_5 (mid 0 +E rc_b_0) -E next 0);
        (None, mid 1 +E rc_b_1 -E next 1);
        (None, mid 2 +E rc_b_2 -E next 2)
      ];
  |} in
  let meta := ConstraintSystem.create_gate meta {|
    Gate.name := "pad-and-add";
    Gate.constraints :=
      let state_0_prev := Expression.Advice Advice.A6 Rotation.prev in
      let state_1_prev := Expression.Advice Advice.A7 Rotation.prev in
      let state_2_prev := Expression.Advice Advice.A8 Rotation.prev in
      let state_0_cur := Expression.Advice Advice.A6 Rotation.cur in
      let state_1_cur := Expression.Advice Advice.A7 Rotation.cur in
      let state_0_next := Expression.Advice Advice.A6 Rotation.next in
      let state_1_next := Expression.Advice Advice.A7 Rotation.next in
      let state_2_next := Expression.Advice Advice.A8 Rotation.next in
      Constraints.with_selector Selector.QPoseidonPadAndAdd [
        (None, state_0_prev +E state_0_cur -E state_0_next);
        (None, state_1_prev +E state_1_cur -E state_1_next);
        (None, state_2_prev -E state_2_next)
      ];
  |} in
  meta.
