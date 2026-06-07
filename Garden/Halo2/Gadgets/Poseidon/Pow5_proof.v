Require Import Garden.Halo2.main.
Require Import Garden.Halo2.proof.
Require Garden.Halo2.Gadgets.Poseidon.Pow5.
Require Import Garden.Halo2.Gadgets.Poseidon.P128Pow5T3.
Require Import Garden.Orchard.columns.
Require Import Garden.Plonky3.M.

#[local] Existing Instance Primes.PallasPIsPrime.

Global Open Scope Z_scope.

Module State.
  Record t : Set := {
    x0 : Z;
    x1 : Z;
    x2 : Z;
  }.

  Definition get (state : t) (column : nat) : Z :=
    match column with
    | O => state.(x0)
    | S O => state.(x1)
    | S (S O) => state.(x2)
    | _ => 0
    end.

  Global Instance IsMapMod : MapMod t := {
    map_mod state := {|
      x0 := UnOp.from state.(x0);
      x1 := UnOp.from state.(x1);
      x2 := UnOp.from state.(x2);
    |};
  }.
End State.

Definition coeff
    (rows : list (list Z))
    (row column : nat)
    : Z :=
  P128Pow5T3.get rows row column.

Definition lin
    (rows : list (list Z))
    (row : nat)
    (state : State.t)
    : Z :=
  coeff rows row 0 *F state.(State.x0) +F
  coeff rows row 1 *F state.(State.x1) +F
  coeff rows row 2 *F state.(State.x2).

Definition matrix_mul
    (rows : list (list Z))
    (state : State.t)
    : State.t := {|
  State.x0 := lin rows 0 state;
  State.x1 := lin rows 1 state;
  State.x2 := lin rows 2 state;
|}.

Definition mds_mul : State.t -> State.t :=
  matrix_mul P128Pow5T3.mds.

Definition mds_inv_mul : State.t -> State.t :=
  matrix_mul P128Pow5T3.mds_inv.

Lemma mds_mul_mds_inv_identity (state : State.t) :
    mds_mul (mds_inv_mul (M.map_mod state)) =
      M.map_mod state.
Admitted.

Lemma mds_inv_mul_mds_identity (state : State.t) :
    mds_inv_mul (mds_mul (M.map_mod state)) =
      M.map_mod state.
Admitted.

Lemma mds_inv_mul_injective (left right : State.t) :
    mds_inv_mul (M.map_mod left) = mds_inv_mul (M.map_mod right) ->
    M.map_mod left = M.map_mod right.
Proof.
  intros H.
  rewrite <- (mds_mul_mds_inv_identity left).
  rewrite <- (mds_mul_mds_inv_identity right).
  now rewrite H.
Qed.

Definition pow5 (value : Z) : Z :=
  (((value *F value) *F value) *F value) *F value.

Module FullRound.
  Theorem deterministic_from_evaluation
      (assignment : Assignment.t columns)
      (row nb_rows : Z) :
      eval_selector assignment row Selector.QPoseidonFull <> 0 ->
      eval_gate assignment row nb_rows Pow5.full_round_gate ->
      eval_expression
        assignment
        row
        nb_rows
        (Expression.Advice Advice.A6 Rotation.next) =
        eval_expression assignment row nb_rows (Pow5.full_round_sum 0) /\
      eval_expression
        assignment
        row
        nb_rows
        (Expression.Advice Advice.A7 Rotation.next) =
        eval_expression assignment row nb_rows (Pow5.full_round_sum 1) /\
      eval_expression
        assignment
        row
        nb_rows
        (Expression.Advice Advice.A8 Rotation.next) =
        eval_expression assignment row nb_rows (Pow5.full_round_sum 2).
  Admitted.

  Definition sbox_state
      (state round_constants : State.t)
      : State.t := {|
    State.x0 :=
      pow5
        (state.(State.x0) +F round_constants.(State.x0));
    State.x1 :=
      pow5
        (state.(State.x1) +F round_constants.(State.x1));
    State.x2 :=
      pow5
        (state.(State.x2) +F round_constants.(State.x2));
  |}.

  Definition output
      (state round_constants : State.t)
      : State.t :=
    mds_mul (sbox_state state round_constants).

  Definition constraints
      (state round_constants next_state : State.t)
      : Prop :=
    next_state = output state round_constants.

  Theorem deterministic (state round_constants left right : State.t) :
      constraints state round_constants left ->
      constraints state round_constants right ->
      left = right.
  Proof.
    intros Hleft Hright.
    transitivity (output state round_constants).
    { exact Hleft. }
    now symmetry.
  Qed.
End FullRound.

Module PartialRound.
  Definition first_sbox_value
      (state rc_a : State.t)
      : Z :=
    pow5 (state.(State.x0) +F rc_a.(State.x0)).

  Definition pre_mix
      (state rc_a : State.t)
      (mid_0 : Z)
      : State.t := {|
    State.x0 := UnOp.from mid_0;
    State.x1 := state.(State.x1) +F rc_a.(State.x1);
    State.x2 := state.(State.x2) +F rc_a.(State.x2);
  |}.

  Definition mid
      (state rc_a : State.t)
      (mid_0 : Z)
      : State.t :=
    mds_mul (pre_mix state rc_a mid_0).

  Definition target_after_inverse
      (state rc_a rc_b : State.t)
      (mid_0 : Z)
      : State.t :=
    let mixed := mid state rc_a mid_0 in {|
      State.x0 :=
        pow5
          (mixed.(State.x0) +F rc_b.(State.x0));
      State.x1 := mixed.(State.x1) +F rc_b.(State.x1);
      State.x2 := mixed.(State.x2) +F rc_b.(State.x2);
    |}.

  Definition output
      (state rc_a rc_b : State.t)
      : State.t :=
    mds_mul
      (target_after_inverse
        state
        rc_a
        rc_b
        (first_sbox_value state rc_a)).

  Definition constraints
      (state rc_a rc_b : State.t)
      (mid_0 : Z)
      (next_state : State.t)
      : Prop :=
    mid_0 = first_sbox_value state rc_a /\
    mds_inv_mul next_state =
      target_after_inverse state rc_a rc_b mid_0.

  Lemma constraints_imply_output
      (state rc_a rc_b : State.t)
      (mid_0 : Z)
      (next_state : State.t) :
      constraints state rc_a rc_b mid_0 next_state ->
      M.map_mod next_state = M.map_mod (output state rc_a rc_b).
  Admitted.

  Theorem deterministic
      (state rc_a rc_b : State.t)
      (left_mid_0 right_mid_0 : Z)
      (left_next right_next : State.t) :
      constraints state rc_a rc_b left_mid_0 left_next ->
      constraints state rc_a rc_b right_mid_0 right_next ->
      left_mid_0 = right_mid_0 /\
      M.map_mod left_next = M.map_mod right_next.
  Proof.
    intros Hleft Hright.
    destruct Hleft as [Hleft_mid Hleft_next].
    destruct Hright as [Hright_mid Hright_next].
    split.
    {
      now rewrite Hleft_mid, Hright_mid.
    }
    transitivity
      (M.map_mod (output state rc_a rc_b)).
    {
      apply (constraints_imply_output state rc_a rc_b left_mid_0 left_next).
      split; assumption.
    }
    symmetry.
    apply (constraints_imply_output state rc_a rc_b right_mid_0 right_next).
    split; assumption.
  Qed.
End PartialRound.

Module PadAndAdd.
  Definition output
      (previous input : State.t)
      : State.t := {|
    State.x0 :=
      previous.(State.x0) +F input.(State.x0);
    State.x1 :=
      previous.(State.x1) +F input.(State.x1);
    State.x2 := UnOp.from previous.(State.x2);
  |}.

  Definition constraints
      (previous input next_state : State.t)
      : Prop :=
    next_state = output previous input.

  Theorem deterministic (previous input left right : State.t) :
      constraints previous input left ->
      constraints previous input right ->
      left = right.
  Proof.
    intros Hleft Hright.
    transitivity (output previous input).
    { exact Hleft. }
    now symmetry.
  Qed.
End PadAndAdd.
