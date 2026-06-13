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

Lemma mds_inv_mul_injective
    (left right : State.t)
    (H : mds_inv_mul (M.map_mod left) = mds_inv_mul (M.map_mod right)) :
    M.map_mod left = M.map_mod right.
Proof.
  rewrite <- (mds_mul_mds_inv_identity left).
  rewrite <- (mds_mul_mds_inv_identity right).
  now rewrite H.
Qed.

Definition pow5 (value : Z) : Z :=
  let value_2 := value *F value in
  let value_4 := value_2 *F value_2 in
  value_4 *F value.

Module FullRound.
  Definition output_coordinate
      (row : nat)
      (state_0 state_1 state_2 : Z)
      (round_constant_0 round_constant_1 round_constant_2 : Z)
      : Z :=
    let state_0_sbox := pow5 (state_0 +F round_constant_0) in
    let state_1_sbox := pow5 (state_1 +F round_constant_1) in
    let state_2_sbox := pow5 (state_2 +F round_constant_2) in
    state_0_sbox *F UnOp.from (P128Pow5T3.mds_coeff row 0) +F
    state_1_sbox *F UnOp.from (P128Pow5T3.mds_coeff row 1) +F
    state_2_sbox *F UnOp.from (P128Pow5T3.mds_coeff row 2).

  Definition output
      (state_0 state_1 state_2 : Z)
      (round_constant_0 round_constant_1 round_constant_2 : Z)
      : State.t := {|
    State.x0 :=
      output_coordinate
        0
        state_0
        state_1
        state_2
        round_constant_0
        round_constant_1
        round_constant_2;
    State.x1 :=
      output_coordinate
        1
        state_0
        state_1
        state_2
        round_constant_0
        round_constant_1
        round_constant_2;
    State.x2 :=
      output_coordinate
        2
        state_0
        state_1
        state_2
        round_constant_0
        round_constant_1
        round_constant_2;
  |}.

  Theorem deterministic
      (ρ : Evaluation.t columns)
      (Hselector : ⟦ Selector.QPoseidonFull ⟧ ρ <> 0)
      (Hgate : ⟦ Pow5.full_round_gate ⟧ ρ) :
      {|
        State.x0 := ⟦ Expression.Advice Advice.A6 Rotation.next ⟧ ρ;
        State.x1 := ⟦ Expression.Advice Advice.A7 Rotation.next ⟧ ρ;
        State.x2 := ⟦ Expression.Advice Advice.A8 Rotation.next ⟧ ρ;
      |} =
        output
          (⟦ Expression.Advice Advice.A6 Rotation.cur ⟧ ρ)
          (⟦ Expression.Advice Advice.A7 Rotation.cur ⟧ ρ)
          (⟦ Expression.Advice Advice.A8 Rotation.cur ⟧ ρ)
          (⟦ Expression.Fixed Fixed.LagrangeCoeffs2 Rotation.cur ⟧ ρ)
          (⟦ Expression.Fixed Fixed.LagrangeCoeffs3 Rotation.cur ⟧ ρ)
          (⟦ Expression.Fixed Fixed.LagrangeCoeffs4 Rotation.cur ⟧ ρ).
  Proof.
    unfold output, output_coordinate, pow5.
    with_strategy opaque [BinOp.add BinOp.mul BinOp.sub UnOp.from]
      cbn in *.
    hauto lq: on.
  Qed.
End FullRound.

Module PartialRound.
  Definition output
      (state_0 state_1 state_2 : Z)
      (round_constant_a_0 round_constant_a_1 round_constant_a_2 : Z)
      (round_constant_b_0 round_constant_b_1 round_constant_b_2 : Z)
      : State.t.
  Admitted.

  Theorem deterministic
      (ρ : Evaluation.t columns)
      (Hselector : ⟦ Selector.QPoseidonPartial ⟧ ρ <> 0)
      (Hgate : ⟦ Pow5.partial_rounds_gate ⟧ ρ) :
      {|
        State.x0 := ⟦ Expression.Advice Advice.A6 Rotation.next ⟧ ρ;
        State.x1 := ⟦ Expression.Advice Advice.A7 Rotation.next ⟧ ρ;
        State.x2 := ⟦ Expression.Advice Advice.A8 Rotation.next ⟧ ρ;
      |} =
        output
          (⟦ Expression.Advice Advice.A6 Rotation.cur ⟧ ρ)
          (⟦ Expression.Advice Advice.A7 Rotation.cur ⟧ ρ)
          (⟦ Expression.Advice Advice.A8 Rotation.cur ⟧ ρ)
          (⟦ Expression.Fixed Fixed.LagrangeCoeffs2 Rotation.cur ⟧ ρ)
          (⟦ Expression.Fixed Fixed.LagrangeCoeffs3 Rotation.cur ⟧ ρ)
          (⟦ Expression.Fixed Fixed.LagrangeCoeffs4 Rotation.cur ⟧ ρ)
          (⟦ Expression.Fixed Fixed.LagrangeCoeffs5 Rotation.cur ⟧ ρ)
          (⟦ Expression.Fixed Fixed.LagrangeCoeffs6 Rotation.cur ⟧ ρ)
          (⟦ Expression.Fixed Fixed.LagrangeCoeffs7 Rotation.cur ⟧ ρ).
  Admitted.
End PartialRound.

Module PadAndAdd.
  Definition output
      (previous_state_0 previous_state_1 previous_state_2 : Z)
      (current_state_0 current_state_1 : Z)
      : State.t := {|
    State.x0 := previous_state_0 +F current_state_0;
    State.x1 := previous_state_1 +F current_state_1;
    State.x2 := previous_state_2;
  |}.

  Theorem deterministic
      (ρ : Evaluation.t columns)
      (Hselector : ⟦ Selector.QPoseidonPadAndAdd ⟧ ρ <> 0)
      (Hgate : ⟦ Pow5.pad_and_add_gate ⟧ ρ) :
      {|
        State.x0 := ⟦ Expression.Advice Advice.A6 Rotation.next ⟧ ρ;
        State.x1 := ⟦ Expression.Advice Advice.A7 Rotation.next ⟧ ρ;
        State.x2 := ⟦ Expression.Advice Advice.A8 Rotation.next ⟧ ρ;
      |} =
        output
          (⟦ Expression.Advice Advice.A6 Rotation.prev ⟧ ρ)
          (⟦ Expression.Advice Advice.A7 Rotation.prev ⟧ ρ)
          (⟦ Expression.Advice Advice.A8 Rotation.prev ⟧ ρ)
          (⟦ Expression.Advice Advice.A6 Rotation.cur ⟧ ρ)
          (⟦ Expression.Advice Advice.A7 Rotation.cur ⟧ ρ).
  Proof.
    unfold output.
    with_strategy opaque [BinOp.add BinOp.mul BinOp.sub UnOp.from]
      cbn in *.
    hauto lq: on.
  Qed.
End PadAndAdd.
