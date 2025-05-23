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
Definition eval_round_flags (is_first_row is_transition : bool) (local next : KeccakCols.t) :
    M.t unit :=
  let* _ := when is_first_row [[
    assert_one (| Array.get (| local.(KeccakCols.step_flags), 0 |) |)
  ]] in
  let* _ := when is_first_row [[
    assert_zeros (| Array.slice_from local.(KeccakCols.step_flags) 1 |)
  ]] in
  let* _ := when is_transition [[
    assert_zeros (N := NUM_ROUNDS) (| Array.from_fn (| fun i => [[
      M.sub (|
        Array.get (| local.(KeccakCols.step_flags), i |),
        Array.get (| next.(KeccakCols.step_flags), (i + 1) mod NUM_ROUNDS |)
      |)
    ]] |) |)
  ]] in
  M.Pure tt.

Definition eval_round_flags_step_flags
    (is_first_row is_transition : bool)
    (local next : Array.t Z NUM_ROUNDS) :
    M.t unit :=
  let* _ := when is_first_row [[
    assert_one (| Array.get (| local, 0 |) |)
  ]] in
  let* _ := when is_first_row [[
    assert_zeros (| Array.slice_from local 1 |)
  ]] in
  let* _ := when is_transition [[
    assert_zeros (N := NUM_ROUNDS) (| Array.from_fn (| fun i => [[
      M.sub (|
        Array.get (| local, i |),
        Array.get (| next, (i + 1) mod NUM_ROUNDS |)
      |)
    ]] |) |)
  ]] in
  M.Pure tt.

(* Definition eval_round_flags_explicit
    (is_first_row is_transition : bool)
    (local next : KeccakColsExplicit.t) :
    M.t unit :=
  let* _ := when is_first_row [[
    assert_one (| ExplicitArray.get local.(KeccakColsExplicit.step_flags) 0 |)
  ]] in
  let* _ := when is_first_row [[
    assert_zeros (| ExplicitArray.slice_from local.(KeccakColsExplicit.step_flags) 1 |)
  ]] in
  (* let* _ := when is_transition [[
    assert_zeros (N := NUM_ROUNDS) (| ExplicitArray.from_fn (| fun i => [[
      M.sub (|
        ExplicitArray.get local.(KeccakColsExplicit.step_flags) i,
        ExplicitArray.get next.(KeccakColsExplicit.step_flags) ((i + 1) mod NUM_ROUNDS)
      |)
    ]] |) |)
  ]] in *)
  M.Pure tt. *)

Module Spec.
  Lemma spec_first_row (p : Z)
      (local next : StepFlagsInput.t)
      (H_p : IsPrime p) :
    {{ M.eval p (eval_round_flags_step_flags true false
        (StepFlagsInput.to_value local) (StepFlagsInput.to_value next)) 🔽
      tt,
      StepFlagsInput.to_value local = StepFlagsOutput.to_value 0
    }}.
  Proof.
    destruct local.
    cbn; unfold Pos.to_nat; cbn.
    eapply Run.Equiv. {
      progress repeat (
        apply Run.Pure ||
        eapply Run.Let ||
        apply Run.Equal
      ).
    }
    unfold StepFlagsInput.to_value, StepFlagsOutput.to_value, Array.from_fn_pure; cbn.
    unfold Pos.to_nat; cbn.
    split; sauto lq: on rew: off.
  Qed.

  Lemma spec_transition (p : Z)
      (local : StepFlagsOutput.t)
      (next : StepFlagsInput.t)
      (H_p : IsPrime p) :
    {{ M.eval p (eval_round_flags_step_flags false true
        (StepFlagsOutput.to_value local) (StepFlagsInput.to_value next)) 🔽
      tt,
      StepFlagsInput.to_value next = StepFlagsOutput.to_value (local + 1)
    }}.
  Proof.
    (* destruct next. *)
    (* unfold StepFlagsOutput.to_value, Array.from_fn_pure; cbn.
    unfold Pos.to_nat, Array.get; cbn. *)
    eapply Run.Equiv; cbn. {
      progress repeat (
        apply Run.Pure ||
        eapply Run.Let ||
        apply Run.Equal
      ).
    }
    replace local with 15 by admit.
    cbn.
    withcbn.
    split; sauto lq: on rew: off.

  Definition initial_step_flags : Array.t Z NUM_ROUNDS :=
    Array.from_fn_pure (fun i =>
      if i =? 0 then 1 else 0
    ).

  Definition initial_step_flags_explicit : ExplicitArray.t Z NUM_ROUNDS :=
    ExplicitArray.from_fn (length := NUM_ROUNDS) (fun i =>
      if i =? 0 then 1 else 0
    ).

  Definition shift (local_step_flags next_step_flags : Array.t Z NUM_ROUNDS) : Prop :=
    forall i,
      Array.get local_step_flags i =
      Array.get next_step_flags ((i + 1) mod NUM_ROUNDS).

  Definition spec (is_first_row is_transition : bool) (local next : KeccakCols.t) : Prop :=
    if is_first_row then
      local.(KeccakCols.step_flags) = initial_step_flags
    else if is_transition then
      shift local.(KeccakCols.step_flags) next.(KeccakCols.step_flags)
    else
      True.

  Definition spec_step_flags (is_first_row is_transition : bool) (local next : Array.t Z NUM_ROUNDS) : Prop :=
    if is_first_row then
      local = initial_step_flags
    else if is_transition then
      shift local next
    else
      True.

  Definition spec_step_flags_explicit (is_first_row is_transition : bool) (local next : ExplicitArray.t Z NUM_ROUNDS) : Prop :=
    if is_first_row then
      local = initial_step_flags_explicit
    else if is_transition then
      shift (ExplicitArray.to_array local) (ExplicitArray.to_array next)
    else
      True.

  (* Notation "array [< >]" := (array.(Pair.x)) (at level 100).
  Notation "array [< .. >]" := (array.(Pair.xs)) (at level 100). *)

  Lemma spec_correct_step_flags (p : Z)
    (local next : ExplicitArray.t Z NUM_ROUNDS)
    (H_p : IsPrime p) :
    let local_array := ExplicitArray.to_array local in
    let next_array := ExplicitArray.to_array next in
    {{ M.eval p (eval_round_flags_step_flags true false local_array next_array) 🔽
      tt, spec_step_flags_explicit true false local next
    }}.
  Proof.
    do 24 destruct local as [? local].
    cbn; unfold Pos.to_nat; cbn.
    eapply Run.Equiv. {
      progress repeat (
        apply Run.Pure ||
        eapply Run.Let ||
        apply Run.Equal
      ).
    }
    split; sauto lq: on rew: off.
  Qed.

  Lemma spec_correct (p : Z) (is_first_row is_transition : bool) (local next : KeccakCols.t)
    (H_p : IsPrime p)
    (H_local : KeccakCols.Valid.t local)
    (H_next : KeccakCols.Valid.t next) :
    {{ M.eval p (eval_round_flags is_first_row is_transition local next) 🔽
      tt, spec is_first_row is_transition local next
    }}.
  Proof.
    destruct H_local, H_next.
    (* Print Array.Valid.t.
    destruct is_first_row, is_transition; cbn.
    { eapply Run.Equiv. {
        destruct local.(KeccakCols.step_flags).(Array.value).
      }

    } *)
