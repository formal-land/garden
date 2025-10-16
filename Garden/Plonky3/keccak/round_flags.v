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
  let* _ := when is_first_row (
    M.assert_one (local.(KeccakCols.step_flags).(Array.get) 0)
  ) in
  let* _ := when is_first_row (
    M.assert_zeros (Array.slice_from local.(KeccakCols.step_flags) 1)
  ) in
  let* _ := when is_transition (
    M.assert_zeros (N := NUM_ROUNDS) {|
      Array.get i :=
        BinOp.sub (local.(KeccakCols.step_flags).(Array.get) i)
        (next.(KeccakCols.step_flags).(Array.get) ((i + 1) mod NUM_ROUNDS))
    |}
  ) in
  M.pure tt.

Module Spec.
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
End Spec.
