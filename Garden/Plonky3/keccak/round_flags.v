Require Import Garden.Plonky3.MLessEffects.
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
    M.equal (local.(KeccakCols.step_flags).(Array.get) 0) 1
  ) in
  let* _ := when_bool is_first_row (
    M.zeros (Array.slice_from local.(KeccakCols.step_flags) 1)
  ) in
  let* _ := when_bool is_transition (
    M.zeros (N := NUM_ROUNDS) {|
      Array.get i :=
        BinOp.sub (local.(KeccakCols.step_flags).(Array.get) i)
        (next.(KeccakCols.step_flags).(Array.get) ((i + 1) mod NUM_ROUNDS))
    |}
  ) in
  M.pure tt.

Definition round_indicator (round : Z) : Array.t Z NUM_ROUNDS :=
  {|
    Array.get i := Z.b2z (i =? round);
  |}.

Definition eval_round_flags_transition_as_spec {p} `{Prime p}
    (round : Z) (H_round : 0 <= round < NUM_ROUNDS)
    (local next : KeccakCols.t)
    (H_local : local.(KeccakCols.step_flags) = round_indicator round) :
    M.t unit :=
  let* _ := M.explicit tt True in
  let* _ := M.explicit tt True in
  let* _ := M.explicit tt (
    next.(KeccakCols.step_flags) = round_indicator ((round + 1) mod NUM_ROUNDS)
  ) in
  M.pure tt.

Module Spec.
  Inductive t (A : Set) : Set :=
  | Pure (value : A) : t A
  | Let {B E : Set} (P : E -> Prop) (k : B -> E -> t A) : t A.
  Arguments Pure {_}.
  Arguments Let {_ _ _}.
End Spec.

Module AsSpec.
  Inductive t {A : Set} : forall (source spec : M.t A), Prop :=
  | Pure (value : A) :
    t (M.Pure value) (M.Pure value)
  | Explicit (e : M.t A) (value : A) (post : Prop) :
    {{ e 🔽 value, post }} ->
    t e (M.Explicit value post)
  | Let {B : Set} (e_source e_spec : M.t B) (k_source k_spec : B -> M.t A) :
    t e_source e_spec ->
    (forall value, t (k_source value) (k_spec value)) ->
    t (M.Let e_source k_source) (M.Let e_spec k_spec).
End AsSpec.

Lemma eval_round_flags_transition_as_spec_correct {p} `{Prime p}
    (round : Z) (H_round : 0 <= round < NUM_ROUNDS)
    (is_first_row : bool)
    (local next : KeccakCols.t)
    (H_local : local.(KeccakCols.step_flags) = round_indicator round) :
  AsSpec.t
    (eval_round_flags is_first_row true local next)
    (eval_round_flags_transition_as_spec round H_round local next H_local).
Proof.
  apply AsSpec.Let. {
    apply AsSpec.Explicit. {
      destruct is_first_row; cbn;
      eapply Run.Implies.
      all: try apply Run.Pure.
      all: try apply Run.Equal.
      all: trivial.
    }
  }
  intros [].
  apply AsSpec.Let. {
    apply AsSpec.Explicit. {
      destruct is_first_row; cbn;
      eapply Run.Implies.
      all: try apply Run.Pure.
      all: try apply Run.Zeros.
      all: trivial.
    }
  }
  intros [].
  apply AsSpec.Let. {
    apply AsSpec.Explicit. {
      cbn.
      eapply Run.Implies. {
        apply Run.AssertZerosFromFnSub.
      }
      intros H_for.
      apply Array.eq.
      intros.
      cbn in H_for.
      replace i with (((i - 1) mod NUM_ROUNDS + 1) mod NUM_ROUNDS) at 1. 2: {
        admit.
      }
      rewrite <- H_for by lia.
      rewrite H_local.
      unfold round_indicator; cbn.
      f_equal.
      admit.
    }
  }
  intros [].
  apply AsSpec.Pure.
Admitted.

(* Module Spec.
  Lemma spec_first_row {p} `{Prime p}
      (is_transition : bool)
      (local next : KeccakCols.t) :
    {{ eval_round_flags true is_transition local next 🔽
      tt,
      forall i, 0 <= i < NUM_ROUNDS ->
      local.(KeccakCols.step_flags).(Array.get) i =
      if i =? 0 then 1 else 0
    }}.
  Proof.
    eapply Run.Implies. {
      destruct is_transition;
      progress repeat (
        apply Run.Pure ||
        (eapply Run.Let; [|intro]) ||
        apply Run.Equal ||
        apply Run.Zeros ||
        cbn
      ).
      apply Run.Pure.
    }
    with_strategy opaque [Z.add] cbn.
    intros.
    destruct (i =? 0) eqn:H_eq; try lia.
    {
      assert (i = 0) by lia.
      sfirstorder.
    }
    { assert (1 <= i < NUM_ROUNDS) by lia.
      intuition.
      match goal with
      | [ H : _ |- _ ] =>
        rewrite <- (H (i - 1)) by lia
      end.
      f_equal; lia.
    }
  Qed.

  Lemma spec_transition {p} `{Prime p}
      (local next : KeccakCols.t) :
    {{ eval_round_flags false true local next 🔽
      tt,
      forall i, 0 <= i < NUM_ROUNDS ->
      local.(KeccakCols.step_flags).(Array.get) i =
      next.(KeccakCols.step_flags).(Array.get) ((i + 1) mod NUM_ROUNDS)
    }}.
  Proof.
    eapply Run.Implies. {
      progress repeat (
        apply Run.Pure ||
        (eapply Run.Let; [|intro]) ||
        apply Run.Equal ||
        apply Run.AssertZerosFromFnSub ||
        cbn
      ).
    }
    easy.
  Qed.
End Spec. *)
