(** * Poseidon correspondence for the standalone Garden-shaped Action

    Kept separate from [action_garden_bridge.v] so the large fixed schedule can
    be checked independently of the representation and Sinsemilla lemmas. *)

Require Import
  Garden.Orchard.IronwoodGardenActionBridge.action_garden_bridge.
Require Import
  Garden.Orchard.IronwoodGardenActionBridge.action_garden_generated.
Require Import Garden.Halo2.halo2_gadgets.poseidon.spec.
Require Import Garden.Halo2.halo2_gadgets.poseidon.pow5_proof.
Require Import Garden.Field.Field.
Require Import Garden.Field.Lemmas.
Require Import Garden.Plonky3.M.

Open Scope Z_scope.

#[local] Existing Instance Primes.PallasPIsPrime.

Module ActionGardenPoseidonBridge.
  Module Bridge := ActionGardenBridge.
  Module GardenState :=
    Garden.Halo2.halo2_gadgets.poseidon.pow5_proof.State.
  Module GardenFullRound :=
    Garden.Halo2.halo2_gadgets.poseidon.pow5_proof.FullRound.
  Module GardenPartialRound :=
    Garden.Halo2.halo2_gadgets.poseidon.pow5_proof.PartialRound.

  Lemma mds_coeff_get (row column : nat) :
    p128pow5t3.mds_coeff row column =
      p128pow5t3.get p128pow5t3.mds row column.
  Proof. reflexivity. Qed.

  Strategy opaque
    [p128pow5t3.round_constant p128pow5t3.mds_coeff].

  Lemma field_mul_right_reduce (value coefficient : Z) :
    value *F coefficient = value *F UnOp.from coefficient.
  Proof.
    transitivity (coefficient *F value).
    - apply field_mul_comm.
    - rewrite mul_left_reduce.
      apply field_mul_comm.
  Qed.

  Definition from_garden_state (state : GardenState.t) : ActionGardenZ_State3 := {|
    ActionGardenZ_x0 := state.(GardenState.x0);
    ActionGardenZ_x1 := state.(GardenState.x1);
    ActionGardenZ_x2 := state.(GardenState.x2)
  |}.

  Definition to_garden_state (state : ActionGardenZ_State3) : GardenState.t := {|
    GardenState.x0 := state.(ActionGardenZ_x0);
    GardenState.x1 := state.(ActionGardenZ_x1);
    GardenState.x2 := state.(ActionGardenZ_x2)
  |}.

  (** One partial round, factored out of the generated two-round operation.
      This definition is deliberately written with the same record fields and
      primitive calls as [ActionGardenZ_poseidonPartialPair]. *)
  Definition z_partial_round
      (round : Z) (state : ActionGardenZ_State3) : ActionGardenZ_State3 :=
    let constants := Bridge.z_poseidon_parameters.(ActionGardenZ_roundConstant) round in
    ActionGardenZ_matrixApply Bridge.z_poseidon_parameters.(ActionGardenZ_mds) {|
      ActionGardenZ_x0 :=
        ActionGardenZ_basePow5
          (ActionGardenZ_baseAdd state.(ActionGardenZ_x0) constants.(ActionGardenZ_x0));
      ActionGardenZ_x1 :=
        ActionGardenZ_baseAdd state.(ActionGardenZ_x1) constants.(ActionGardenZ_x1);
      ActionGardenZ_x2 :=
        ActionGardenZ_baseAdd state.(ActionGardenZ_x2) constants.(ActionGardenZ_x2)
    |}.

  (** The corresponding one-round operation in Garden's native field model. *)
  Definition garden_partial_round
      (round : nat) (state : GardenState.t) : GardenState.t :=
    Garden.Halo2.halo2_gadgets.poseidon.pow5_proof.mds_mul
      (GardenPartialRound.sbox_partial {|
        GardenState.x0 :=
          state.(GardenState.x0) +F p128pow5t3.round_constant round 0;
        GardenState.x1 :=
          state.(GardenState.x1) +F p128pow5t3.round_constant round 1;
        GardenState.x2 :=
          state.(GardenState.x2) +F p128pow5t3.round_constant round 2
      |}).

  Lemma poseidon_full_round_eq
      (round : nat) (state : ActionGardenZ_State3) :
    to_garden_state
      (ActionGardenZ_poseidonFullRound Bridge.z_poseidon_parameters
        (Z.of_nat round) state) =
      Poseidon.apply_full round (to_garden_state state).
  Proof.
    destruct state as [state0 state1 state2].
    unfold to_garden_state,
      ActionGardenZ_poseidonFullRound, Bridge.z_poseidon_parameters,
      Poseidon.apply_full, Poseidon.rc, GardenFullRound.output,
      GardenFullRound.output_coordinate, ActionGardenZ_matrixApply,
      ActionGardenZ_basePow5,
      Garden.Halo2.halo2_gadgets.poseidon.pow5_proof.pow5.
    cbn [ActionGardenZ_roundConstant ActionGardenZ_mds ActionGardenZ_x0 ActionGardenZ_x1
      ActionGardenZ_x2 GardenState.x0 GardenState.x1 GardenState.x2].
    rewrite Nat2Z.id.
    repeat match goal with
    | |- context [ActionGardenZ_baseAdd ?left ?right] =>
        rewrite (Bridge.base_add_eq left right)
    | |- context [ActionGardenZ_baseMul ?left ?right] =>
        rewrite (Bridge.base_mul_eq left right)
    end.
    repeat match goal with
    | |- context [
        ?value *F p128pow5t3.mds_coeff ?row ?column] =>
        rewrite
          (field_mul_right_reduce value
            (p128pow5t3.mds_coeff row column))
    end.
    reflexivity.
  Qed.

  Lemma poseidon_partial_round_eq
      (round : nat) (state : ActionGardenZ_State3) :
    to_garden_state (z_partial_round (Z.of_nat round) state) =
      garden_partial_round round (to_garden_state state).
  Proof.
    destruct state as [state0 state1 state2].
    unfold to_garden_state, z_partial_round, garden_partial_round,
      Bridge.z_poseidon_parameters, ActionGardenZ_matrixApply, ActionGardenZ_basePow5,
      GardenPartialRound.sbox_partial,
      Garden.Halo2.halo2_gadgets.poseidon.pow5_proof.mds_mul,
      Garden.Halo2.halo2_gadgets.poseidon.pow5_proof.matrix_mul,
      Garden.Halo2.halo2_gadgets.poseidon.pow5_proof.lin,
      Garden.Halo2.halo2_gadgets.poseidon.pow5_proof.coeff,
      Garden.Halo2.halo2_gadgets.poseidon.pow5_proof.pow5.
    cbn [ActionGardenZ_roundConstant ActionGardenZ_mds ActionGardenZ_x0 ActionGardenZ_x1
      ActionGardenZ_x2 GardenState.x0 GardenState.x1 GardenState.x2].
    rewrite Nat2Z.id.
    repeat match goal with
    | |- context [ActionGardenZ_baseAdd ?left ?right] =>
        rewrite (Bridge.base_add_eq left right)
    | |- context [ActionGardenZ_baseMul ?left ?right] =>
        rewrite (Bridge.base_mul_eq left right)
    end.
    cbn [ActionGardenZ_m00 ActionGardenZ_m01 ActionGardenZ_m02 ActionGardenZ_m10 ActionGardenZ_m11
      ActionGardenZ_m12 ActionGardenZ_m20 ActionGardenZ_m21 ActionGardenZ_m22].
    repeat match goal with
    | |- context [
        ?value *F p128pow5t3.mds_coeff ?row ?column] =>
        rewrite
          (field_mul_comm value
            (p128pow5t3.mds_coeff row column))
    end.
    repeat rewrite mds_coeff_get.
    reflexivity.
  Qed.

  Lemma poseidon_partial_pair_eq
      (round : nat) (state : ActionGardenZ_State3) :
    to_garden_state
      (ActionGardenZ_poseidonPartialPair Bridge.z_poseidon_parameters
        (Z.of_nat round) state) =
      Poseidon.apply_partial round (S round) (to_garden_state state).
  Proof.
    unfold ActionGardenZ_poseidonPartialPair.
    change (
      to_garden_state
        (z_partial_round
          (ActionGardenZ_zAdd (Z.of_nat round) ActionGardenZ_zOne)
          (z_partial_round (Z.of_nat round) state)) =
      Poseidon.apply_partial round (S round) (to_garden_state state)).
    replace (ActionGardenZ_zAdd (Z.of_nat round) ActionGardenZ_zOne)
      with (Z.of_nat (S round)).
    2: unfold ActionGardenZ_zAdd, ActionGardenZ_zOne; lia.
    rewrite poseidon_partial_round_eq.
    rewrite poseidon_partial_round_eq.
    unfold Poseidon.apply_partial, GardenPartialRound.output,
      garden_partial_round, Poseidon.rc.
    reflexivity.
  Qed.

  Strategy opaque
    [Poseidon.apply_full Poseidon.apply_partial
      ActionGardenZ_poseidonFullRound ActionGardenZ_poseidonPartialPair].

  (** A generic commuting-map lemma keeps the induction proof independent of
      the (large) concrete Poseidon round bodies. *)
  Lemma iterate_indexed_from_map
      {A B : Type}
      (convert : A -> B)
      (left_step : nat -> A -> A)
      (right_step : nat -> B -> B)
      (step_eq :
        forall (index : nat) (state : A),
          convert (left_step index state) =
            right_step index (convert state))
      (count index : nat) (state : A) :
    convert
      (ActionGardenZ_iterateIndexedFrom count index left_step state) =
      ActionGardenZ_iterateIndexedFrom count index right_step (convert state).
  Proof.
    revert index state.
    induction count as [| count IH]; intros index state.
    - reflexivity.
    - cbn [ActionGardenZ_iterateIndexedFrom].
      rewrite IH.
      rewrite step_eq.
      reflexivity.
  Qed.

  (** Mapping a state conversion across the generated iterator avoids
      normalizing all 64 rounds into one enormous term. *)
  Lemma iterate_full_rounds_eq
      (round_at : nat -> nat) (count index : nat)
      (state : ActionGardenZ_State3) :
    to_garden_state
      (ActionGardenZ_iterateIndexedFrom count index
        (fun current current_state =>
          ActionGardenZ_poseidonFullRound Bridge.z_poseidon_parameters
            (Z.of_nat (round_at current)) current_state)
        state) =
      ActionGardenZ_iterateIndexedFrom count index
        (fun current current_state =>
          Poseidon.apply_full (round_at current) current_state)
        (to_garden_state state).
  Proof.
    apply iterate_indexed_from_map.
    intros current current_state.
    apply poseidon_full_round_eq.
  Qed.

  Lemma iterate_partial_pairs_eq
      (round_at : nat -> nat) (count index : nat)
      (state : ActionGardenZ_State3) :
    to_garden_state
      (ActionGardenZ_iterateIndexedFrom count index
        (fun current current_state =>
          ActionGardenZ_poseidonPartialPair Bridge.z_poseidon_parameters
            (Z.of_nat (round_at current)) current_state)
        state) =
      ActionGardenZ_iterateIndexedFrom count index
        (fun current current_state =>
          Poseidon.apply_partial
            (round_at current) (S (round_at current)) current_state)
        (to_garden_state state).
  Proof.
    apply iterate_indexed_from_map.
    intros current current_state.
    apply poseidon_partial_pair_eq.
  Qed.

  (** The fixed 64-round schedule is the same on both sides. *)
  Lemma poseidon_permute_eq (state : ActionGardenZ_State3) :
    to_garden_state
      (ActionGardenZ_poseidonPermute Bridge.z_poseidon_parameters state) =
      Poseidon.permute (to_garden_state state).
  Proof.
    unfold ActionGardenZ_poseidonPermute, ActionGardenZ_iterateIndexed.
    rewrite iterate_full_rounds_eq.
    rewrite iterate_partial_pairs_eq.
    rewrite iterate_full_rounds_eq.
    unfold Poseidon.permute.
    cbn [ActionGardenZ_iterateIndexedFrom Nat.add Nat.mul].
    reflexivity.
  Qed.

  Lemma base_add_zero_left_canonical
      (value : Z) (Hcanonical : ActionGardenZ_baseCanonical value) :
    ActionGardenZ_baseAdd ActionGardenZ_zZero value = value.
  Proof.
    rewrite Bridge.base_add_eq.
    unfold ActionGardenZ_zZero, BinOp.add.
    cbn.
    unfold ActionGardenZ_baseCanonical in Hcanonical.
    rewrite Bridge.base_normalize_eq in Hcanonical.
    exact Hcanonical.
  Qed.

  Lemma poseidon_capacity_eq :
    ActionGardenZ_baseNormalize
      (ActionGardenZ_zMul (Z.of_nat 2)
        (ActionGardenZ_zPowNat (Z.of_nat 2) 64%nat)) =
      Poseidon.domain_iv_constant_length_2.
  Proof.
    rewrite Bridge.base_normalize_eq.
    unfold ActionGardenZ_zMul, ActionGardenZ_zPowNat,
      Poseidon.domain_iv_constant_length_2, UnOp.from.
    vm_compute.
    reflexivity.
  Qed.

  (** The generated fixed-length hash agrees with Garden as a total [Z]
      function.  Both definitions enter the permutation with the two message
      words directly in the state, so no input-canonicality premise is
      required here. *)
  Lemma poseidon_hash2_eq (left right : Z) :
    ActionGardenZ_poseidonHash2 Bridge.z_poseidon_parameters left right =
      Poseidon.poseidon_hash2 left right.
  Proof.
    unfold ActionGardenZ_poseidonHash2.
    pose proof
      (poseidon_permute_eq {|
        ActionGardenZ_x0 := left;
        ActionGardenZ_x1 := right;
        ActionGardenZ_x2 :=
          ActionGardenZ_baseNormalize
            (ActionGardenZ_zMul (Z.of_nat 2)
              (ActionGardenZ_zPowNat (Z.of_nat 2) 64%nat))
      |}) as Hpermute.
    apply (f_equal (fun state => state.(GardenState.x0))) in Hpermute.
    cbn [to_garden_state GardenState.x0 ActionGardenZ_x0] in Hpermute.
    rewrite poseidon_capacity_eq in Hpermute.
    unfold Poseidon.poseidon_hash2.
    cbn [ActionGardenZ_x0 ActionGardenZ_x1 ActionGardenZ_x2].
    rewrite poseidon_capacity_eq.
    exact Hpermute.
  Qed.

End ActionGardenPoseidonBridge.
