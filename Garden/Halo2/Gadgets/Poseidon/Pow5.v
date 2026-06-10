Require Import Garden.Halo2.main.
Require Import Garden.Halo2.Synthesis.
Require Import Garden.Orchard.columns.
Require Garden.Halo2.Gadgets.Poseidon.P128Pow5T3.
Require Garden.Halo2.Gadgets.Poseidon.P128Pow5T3Synthesis.
Require Garden.Halo2.Gadgets.Utilities.

Import ListNotations.
Global Open Scope pstring_scope.
Global Open Scope Z_scope.

Module State.
  Record t : Set := {
    state_0 : Cell.t columns RegionId.t;
    state_1 : Cell.t columns RegionId.t;
    state_2 : Cell.t columns RegionId.t;
  }.
End State.

Definition pow_5
    (value : Expression.t columns)
    : Expression.t columns :=
  let value_2 := Garden.Halo2.Gadgets.Utilities.square value in
  let value_4 := Garden.Halo2.Gadgets.Utilities.square value_2 in
  value_4 ✖️ value.

Definition full_round_sum
    (row : nat)
    : Expression.t columns :=
  let state_0 := Expression.Advice Advice.A6 Rotation.cur in
  let state_1 := Expression.Advice Advice.A7 Rotation.cur in
  let state_2 := Expression.Advice Advice.A8 Rotation.cur in
  let rc_a_0 := Expression.Fixed Fixed.LagrangeCoeffs2 Rotation.cur in
  let rc_a_1 := Expression.Fixed Fixed.LagrangeCoeffs3 Rotation.cur in
  let rc_a_2 := Expression.Fixed Fixed.LagrangeCoeffs4 Rotation.cur in
  let state_0_sbox := pow_5 (state_0 ➕ rc_a_0) in
  let state_1_sbox := pow_5 (state_1 ➕ rc_a_1) in
  let state_2_sbox := pow_5 (state_2 ➕ rc_a_2) in
  (state_0_sbox ● (P128Pow5T3.mds_coeff row 0))
    ➕ (state_1_sbox ● (P128Pow5T3.mds_coeff row 1))
    ➕ (state_2_sbox ● (P128Pow5T3.mds_coeff row 2)).

Definition mid
    (row : nat)
    : Expression.t columns :=
  let mid_0 := Expression.Advice Advice.A5 Rotation.cur in
  let state_1 := Expression.Advice Advice.A7 Rotation.cur in
  let state_2 := Expression.Advice Advice.A8 Rotation.cur in
  let rc_a_1 := Expression.Fixed Fixed.LagrangeCoeffs3 Rotation.cur in
  let rc_a_2 := Expression.Fixed Fixed.LagrangeCoeffs4 Rotation.cur in
  (mid_0 ● (P128Pow5T3.mds_coeff row 0))
    ➕ ((state_1 ➕ rc_a_1) ● (P128Pow5T3.mds_coeff row 1))
    ➕ ((state_2 ➕ rc_a_2) ● (P128Pow5T3.mds_coeff row 2)).

Definition next
    (row : nat)
    : Expression.t columns :=
  let state_0 := Expression.Advice Advice.A6 Rotation.next in
  let state_1 := Expression.Advice Advice.A7 Rotation.next in
  let state_2 := Expression.Advice Advice.A8 Rotation.next in
  (state_0 ● (P128Pow5T3.mds_inv_coeff row 0))
    ➕ (state_1 ● (P128Pow5T3.mds_inv_coeff row 1))
    ➕ (state_2 ● (P128Pow5T3.mds_inv_coeff row 2)).

Definition full_round_gate : Gate.t columns := {|
    Gate.name := "full round";
    Gate.constraints :=
      let state_0_next := Expression.Advice Advice.A6 Rotation.next in
      let state_1_next := Expression.Advice Advice.A7 Rotation.next in
      let state_2_next := Expression.Advice Advice.A8 Rotation.next in
      Constraints.with_selector Selector.QPoseidonFull [
        (None, Constraint.Equal (full_round_sum 0) state_0_next);
        (None, Constraint.Equal (full_round_sum 1) state_1_next);
        (None, Constraint.Equal (full_round_sum 2) state_2_next)
      ];
  |}.

Definition partial_rounds_gate : Gate.t columns := {|
    Gate.name := "partial rounds";
    Gate.constraints :=
      let cur_0 := Expression.Advice Advice.A6 Rotation.cur in
      let mid_0 := Expression.Advice Advice.A5 Rotation.cur in
      let rc_a_0 := Expression.Fixed Fixed.LagrangeCoeffs2 Rotation.cur in
      let rc_b_0 := Expression.Fixed Fixed.LagrangeCoeffs5 Rotation.cur in
      let rc_b_1 := Expression.Fixed Fixed.LagrangeCoeffs6 Rotation.cur in
      let rc_b_2 := Expression.Fixed Fixed.LagrangeCoeffs7 Rotation.cur in
      Constraints.with_selector Selector.QPoseidonPartial [
        (None, Constraint.Equal (pow_5 (cur_0 ➕ rc_a_0)) mid_0);
        (None, Constraint.Equal (pow_5 (mid 0 ➕ rc_b_0)) (next 0));
        (None, Constraint.Equal (mid 1 ➕ rc_b_1) (next 1));
        (None, Constraint.Equal (mid 2 ➕ rc_b_2) (next 2))
      ];
  |}.

Definition pad_and_add_gate : Gate.t columns := {|
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
        (None, Constraint.Equal (state_0_prev ➕ state_0_cur) state_0_next);
        (None, Constraint.Equal (state_1_prev ➕ state_1_cur) state_1_next);
        (None, Constraint.Equal state_2_prev state_2_next)
      ];
  |}.

Definition configure
    (meta : ConstraintSystem.t columns)
    : ConstraintSystem.t columns :=
  let meta := ConstraintSystem.create_gate meta full_round_gate in
  let meta := ConstraintSystem.create_gate meta partial_rounds_gate in
  let meta := ConstraintSystem.create_gate meta pad_and_add_gate in
  meta.

Definition assign_state
    (offset : Z)
    : 𝓡 columns RegionId.t State.t :=
  let🞵 state_0 :=
    ℛ.AssignAdvice "state_0" Advice.A6 offset 0 in
  let🞵 state_1 :=
    ℛ.AssignAdvice "state_1" Advice.A7 offset 0 in
  let🞵 state_2 :=
    ℛ.AssignAdvice "state_2" Advice.A8 offset 0 in
  return🞵 {|
    State.state_0 := state_0;
    State.state_1 := state_1;
    State.state_2 := state_2;
  |}.

Definition copy_state
    (offset : Z)
    (state : State.t)
    : 𝓡 columns RegionId.t State.t :=
  let🞵 state_0 :=
    copy_advice
      "state_0" state.(State.state_0) Advice.A6 offset 0 in
  let🞵 state_1 :=
    copy_advice
      "state_1" state.(State.state_1) Advice.A7 offset 0 in
  let🞵 state_2 :=
    copy_advice
      "state_2" state.(State.state_2) Advice.A8 offset 0 in
  return🞵 {|
    State.state_0 := state_0;
    State.state_1 := state_1;
    State.state_2 := state_2;
  |}.

Definition synthesize_initial_state
    : 𝓛 columns RegionId.t State.t :=
  ℒ.InNamespace "Poseidon init" (
    ℒ.AddRegion (RegionId.of_index 271) "initial state for domain ConstantLength<2>"
      (assign_state 0)).

Fixpoint assign_round_constant_entries
    (offset : Z)
    (entries :
      list
        Garden.Halo2.Gadgets.Poseidon.P128Pow5T3Synthesis
          .round_constant_entry)
    : 𝓡 columns RegionId.t unit :=
  match entries with
  | [] => return🞵 tt
  | (column, annotation, value) :: entries =>
      let🞵 _ :=
        ℛ.AssignFixed annotation column offset value in
      assign_round_constant_entries offset entries
  end.

Definition assign_round_constant_row
    (offset : Z)
    (row :
      Garden.Halo2.Gadgets.Poseidon.P128Pow5T3Synthesis
        .round_constant_row)
    : 𝓡 columns RegionId.t unit :=
  let '(selector, entries) := row in
  let🞵 _ := ℛ.EnableSelector selector offset "" in
  assign_round_constant_entries offset entries.

Fixpoint assign_permutation_rows
    (offset : Z)
    (rows :
      list
        Garden.Halo2.Gadgets.Poseidon.P128Pow5T3Synthesis
          .round_constant_row)
    : 𝓡 columns RegionId.t State.t :=
  match rows with
  | [] => assign_state offset
  | row :: rows =>
      let🞵 _ := assign_round_constant_row offset row in
      let🞵 _ := assign_state (offset + 1) in
      assign_permutation_rows (offset + 1) rows
  end.

Definition synthesize_add_input_region
    (state : State.t)
    (input_0 input_1 : Cell.t columns RegionId.t)
    : 𝓛 columns RegionId.t State.t :=
  ℒ.AddRegion (RegionId.of_index 272) "add input for domain ConstantLength<2>" (
    let🞵 _ := ℛ.EnableSelector Selector.QPoseidonPadAndAdd 1 "" in
    let🞵 _ := copy_state 0 state in
    let🞵 state_0 :=
      ℛ.AssignAdvice "state_0" Advice.A6 1 0 in
    let🞵 state_1 :=
      ℛ.AssignAdvice "state_1" Advice.A7 1 0 in
    let🞵 state_2 :=
      ℛ.AssignAdvice "state_2" Advice.A8 1 0 in
    let🞵 _ := ℛ.Copy input_0 state_0 in
    let🞵 _ := ℛ.Copy input_1 state_1 in
    let🞵 state_0 :=
      ℛ.AssignAdvice "state_0" Advice.A6 2 0 in
    let🞵 state_1 :=
      ℛ.AssignAdvice "state_1" Advice.A7 2 0 in
    let🞵 state_2 :=
      ℛ.AssignAdvice "state_2" Advice.A8 2 0 in
    return🞵 {|
      State.state_0 := state_0;
      State.state_1 := state_1;
      State.state_2 := state_2;
    |}).

Definition synthesize_permute_state
    (state : State.t)
    : 𝓛 columns RegionId.t State.t :=
  ℒ.AddRegion (RegionId.of_index 273) "permute state" (
    let🞵 _ := copy_state 0 state in
    assign_permutation_rows
      0
      Garden.Halo2.Gadgets.Poseidon.P128Pow5T3Synthesis
        .permutation_rows).

Definition synthesize_sponge
    (state : State.t)
    (input_0 input_1 : Cell.t columns RegionId.t)
    : 𝓛 columns RegionId.t State.t :=
  ℒ.InNamespace "PoseidonSponge" (
    let🞵 state := synthesize_add_input_region state input_0 input_1 in
    synthesize_permute_state state).

Definition synthesize_hash
    (input_0 input_1 : Cell.t columns RegionId.t)
    : 𝓛 columns RegionId.t (Cell.t columns RegionId.t) :=
  let🞵 state := synthesize_initial_state in
  ℒ.InNamespace "Poseidon hash (nk, rho)" (
    let🞵 _ := ℒ.InNamespace "absorb_0" (return🞵 tt) in
    let🞵 _ := ℒ.InNamespace "absorb_1" (return🞵 tt) in
    let🞵 state :=
      ℒ.InNamespace "finish absorbing" (
        synthesize_sponge state input_0 input_1) in
    let🞵 _ := ℒ.InNamespace "squeeze" (return🞵 tt) in
    return🞵 state.(State.state_0)).

Definition synthesize_full_round
    : 𝓛 columns RegionId.t unit :=
  ℒ.AddRegion (RegionId.of_index 0) "full round" (
    ℛ.EnableSelector Selector.QPoseidonFull 0 "").

Definition synthesize_partial_rounds
    : 𝓛 columns RegionId.t unit :=
  ℒ.AddRegion (RegionId.of_index 0) "partial rounds" (
    ℛ.EnableSelector Selector.QPoseidonPartial 0 "").

Definition synthesize_pad_and_add
    : 𝓛 columns RegionId.t unit :=
  ℒ.AddRegion (RegionId.of_index 0) "pad-and-add" (
    ℛ.EnableSelector Selector.QPoseidonPadAndAdd 0 "").

Definition synthesize
    : 𝓛 columns RegionId.t unit :=
  let🞵 _ := synthesize_full_round in
  let🞵 _ := synthesize_partial_rounds in
  synthesize_pad_and_add.
