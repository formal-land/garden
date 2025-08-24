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
    (is_first_row is_transition : bool)
    (local next : KeccakCols.t) :
    M.t unit :=
  let* _ := when_bool is_first_row (
    M.assert_one (local.(KeccakCols.step_flags).(Array.get) 0)
  ) in
  let* _ := when_bool is_first_row (
    M.assert_zeros (Array.slice_from local.(KeccakCols.step_flags) 1)
  ) in
  let* _ := when_bool is_transition (
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
    {{ eval_round_flags true false local next 🔽
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
      now autorewrite with field_rewrite in *.
    }
    { assert (1 <= i < NUM_ROUNDS) by lia.
      intuition.
      match goal with
      | [ H : _ |- _ ] =>
        rewrite <- (H (i - 1)) by lia
      end.
      now replace (1 + (i - 1)) with i by lia.
    }
  Qed.

  Lemma spec_transition {p} `{Prime p}
      (local' next' : KeccakCols.t) :
    let local := M.map_mod local' in
    let next := M.map_mod next' in
    {{ eval_round_flags false true local next 🔽
      tt,
      forall i, 0 <= i < NUM_ROUNDS ->
      local.(KeccakCols.step_flags).(Array.get) i =
      next.(KeccakCols.step_flags).(Array.get) ((i + 1) mod NUM_ROUNDS)
    }}.
  Proof.
    eapply Run.Implies. {
      Run.run.
    }
    hauto q: on db: field_rewrite.
  Qed.
End Spec.
