Require Import Garden.Plonky3.M.
Require Import Garden.Plonky3.keccak.columns.
Require Import Garden.Plonky3.keccak.constants.

(*
pub(crate) fn eval_round_flags<AB: AirBuilder>(builder: &mut AB) {
    let main = builder.main();
    let (local, next) = (
        main.row_slice(0).expect("The matrix is empty?"),
        main.row_slice(1).expect("The matrix only has 1 row?"),
    );
    let local: &KeccakCols<AB::Var> = ( *local).borrow();
    let next: &KeccakCols<AB::Var> = ( *next).borrow();

    // Initially, the first step flag should be 1 while the others should be 0.
    builder.when_first_row().assert_one(local.step_flags[0]);
    builder
        .when_first_row()
        .assert_zeros::<NUM_ROUNDS_MIN_1, _>(local.step_flags[1..].try_into().unwrap());

    builder
        .when_transition()
        .assert_zeros::<NUM_ROUNDS, _>(array::from_fn(|i| {
            local.step_flags[i] - next.step_flags[(i + 1) % NUM_ROUNDS]
        }));
}
*)
Definition eval_round_flags {p} `{Prime p}
    (local next : KeccakCols.t)
    (is_first_row is_transition : Z) :
    M.t unit :=
  let* _ := M.when is_first_row (
    M.assert_one (local.(KeccakCols.step_flags).(Array.get) 0)
  ) in
  let* _ := M.when is_first_row (
    M.assert_zeros (Array.slice_from local.(KeccakCols.step_flags) 1)
  ) in
  let* _ := M.when is_transition (
    M.assert_zeros (N := NUM_ROUNDS) {|
      Array.get i :=
        local.(KeccakCols.step_flags).(Array.get) i -F
        next.(KeccakCols.step_flags).(Array.get) ((i + 1) mod NUM_ROUNDS)
    |}
  ) in
  M.pure tt.

Definition array_of_round (round : Z) : Array.t Z NUM_ROUNDS :=
  {|
    Array.get i :=
      if i =? round then 1 else 0
  |}.

(** This is a rather brute-force approach but it simplifies the proof after. *)
Lemma i_in_bounds (P : Z -> Prop) :
  (
    P 0 /\ P 1 /\ P 2 /\ P 3 /\ P 4 /\ P 5 /\ P 6 /\ P 7 /\ P 8 /\ P 9 /\
    P 10 /\ P 11 /\ P 12 /\ P 13 /\ P 14 /\ P 15 /\ P 16 /\ P 17 /\ P 18 /\ P 19 /\
    P 20 /\ P 21 /\ P 22 /\ P 23
  ) ->
  forall i, 0 <= i < NUM_ROUNDS ->
  P i.
Proof.
  unfold NUM_ROUNDS; intuition.
  assert (i = 0 \/ 1 <= i < 24) as [] by lia; [congruence|].
  assert (i = 1 \/ 2 <= i < 24) as [] by lia; [congruence|].
  assert (i = 2 \/ 3 <= i < 24) as [] by lia; [congruence|].
  assert (i = 3 \/ 4 <= i < 24) as [] by lia; [congruence|].
  assert (i = 4 \/ 5 <= i < 24) as [] by lia; [congruence|].
  assert (i = 5 \/ 6 <= i < 24) as [] by lia; [congruence|].
  assert (i = 6 \/ 7 <= i < 24) as [] by lia; [congruence|].
  assert (i = 7 \/ 8 <= i < 24) as [] by lia; [congruence|].
  assert (i = 8 \/ 9 <= i < 24) as [] by lia; [congruence|].
  assert (i = 9 \/ 10 <= i < 24) as [] by lia; [congruence|].
  assert (i = 10 \/ 11 <= i < 24) as [] by lia; [congruence|].
  assert (i = 11 \/ 12 <= i < 24) as [] by lia; [congruence|].
  assert (i = 12 \/ 13 <= i < 24) as [] by lia; [congruence|].
  assert (i = 13 \/ 14 <= i < 24) as [] by lia; [congruence|].
  assert (i = 14 \/ 15 <= i < 24) as [] by lia; [congruence|].
  assert (i = 15 \/ 16 <= i < 24) as [] by lia; [congruence|].
  assert (i = 16 \/ 17 <= i < 24) as [] by lia; [congruence|].
  assert (i = 17 \/ 18 <= i < 24) as [] by lia; [congruence|].
  assert (i = 18 \/ 19 <= i < 24) as [] by lia; [congruence|].
  assert (i = 19 \/ 20 <= i < 24) as [] by lia; [congruence|].
  assert (i = 20 \/ 21 <= i < 24) as [] by lia; [congruence|].
  assert (i = 21 \/ 22 <= i < 24) as [] by lia; [congruence|].
  assert (i = 22 \/ 23 <= i < 24) as [] by lia; [congruence|].
  assert (i = 23) by lia; congruence.
Qed.

Module step_flags.
  Module Valid.
    Definition t (local : KeccakCols.t) (round : Z) : Prop :=
      local.(KeccakCols.step_flags) =F array_of_round round.
  End Valid.
End step_flags.

Module Spec.
  Record t (local next : KeccakCols.t) (is_first_row is_transition : bool) : Prop := {
    first :
      if is_first_row then
        step_flags.Valid.t local 0
      else
        True;
    transition :
      if is_transition then
        forall round, 0 <= round < NUM_ROUNDS ->
        step_flags.Valid.t local round ->
        step_flags.Valid.t next ((round + 1) mod NUM_ROUNDS)
      else
        True;
  }.
End Spec.

Lemma implies {p} `{Prime p}
    (local' next' : KeccakCols.t)
    (is_first_row is_transition : bool) :
  let local := M.map_mod local' in
  let next := M.map_mod next' in
  {{ eval_round_flags local next (Z.b2z is_first_row) (Z.b2z is_transition) 🔽
    tt,
    Spec.t local next is_first_row is_transition
  }}.
Proof.
  eapply Run.Implies. {
    Run.run.
  }
  constructor;
    with_strategy opaque [Z.add] cbn in *;
    unfold Z.b2z in *;
    FieldRewrite.run.
  { destruct is_first_row; trivial.
    intros.
    destruct (i =? 0) eqn:H_eq; try lia.
    { replace i with 0 by lia.
      replace 1 with (UnOp.from 1) by now autorewrite with field_rewrite.
      apply sub_zero_equiv.
      hauto l: on.
    }
    { set (i' := i - 1).
      replace i with (1 + i') by lia.
      assert (0 <= i' < NUM_ROUNDS - 1) by lia.
      hauto lq: on rew: off.
    }
  }
  { destruct is_transition; trivial.
    intros round H_round H_local i H_i.
    set (i' := (i - 1) mod NUM_ROUNDS).
    replace i with ((i' + 1) mod NUM_ROUNDS) at 1. 2: {
      unfold i'; clear i'.
      generalize i H_i.
      apply i_in_bounds; trivial.
      now cbn.
    }
    assert (0 <= i' < NUM_ROUNDS) by lia.
    replace
      (UnOp.from next'.(KeccakCols.step_flags).[(i' + 1) mod NUM_ROUNDS]) with
      (UnOp.from local'.(KeccakCols.step_flags).[i'])
      by hauto lq: on rew: off.
    rewrite H_local by trivial.
    unfold i'; generalize i H_i.
    apply i_in_bounds.
    generalize round H_round; apply i_in_bounds; cbv; repeat constructor.
  }
Qed.

Module OlderSpec.
  Lemma spec_first_row {p} `{Prime p}
      (local' next' : KeccakCols.t) :
    let local := M.map_mod local' in
    let next := M.map_mod next' in
    {{ eval_round_flags local next 1 0 🔽
      tt,
      forall i, 0 <= i < NUM_ROUNDS ->
      local.(KeccakCols.step_flags).(Array.get) i =
      if i =? 0 then 1 else 0
    }}.
  Proof.
    eapply Run.Implies. {
      Run.run.
    }
    with_strategy opaque [Z.add] cbn.
    intros.
    destruct (i =? 0) eqn:H_eq; try lia.
    {
      replace i with 0 by lia.
      replace 1 with (UnOp.from 1) by now autorewrite with field_rewrite.
      apply sub_zero_equiv.
      autorewrite with field_rewrite in *.
      hauto l: on.
    }
    { set (i' := i - 1).
      replace i with (1 + i') by lia.
      assert (0 <= i' < NUM_ROUNDS - 1) by lia.
      hauto lq: on rew: off.
    }
  Qed.

  Lemma spec_transition {p} `{Prime p}
      (local' next' : KeccakCols.t) :
    let local := M.map_mod local' in
    let next := M.map_mod next' in
    {{ eval_round_flags local next 0 1 🔽
      tt,
      forall i, 0 <= i < NUM_ROUNDS ->
      local.(KeccakCols.step_flags).(Array.get) i =
      next.(KeccakCols.step_flags).(Array.get) ((i + 1) mod NUM_ROUNDS)
    }}.
  Proof.
    eapply Run.Implies. {
      Run.run.
    }
    cbn.
    FieldRewrite.run.
    hauto lq: on rew: off.
  Qed.
End OlderSpec.
