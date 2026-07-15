Require Import Garden.Halo2.main.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.lemmas.
Require Import Garden.Halo2.PallasModel.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.spec.
Require Import Garden.Halo2.halo2_gadgets.poseidon.pow5_proof.
Require Import Garden.Halo2.halo2_gadgets.poseidon.spec.
Require Garden.Halo2.halo2_poseidon.p128pow5t3.
Require Import Garden.EllipticCurve.Weierstrass.
Require Import Garden.EllipticCurve.Pallas.
Require Import Garden.Orchard.regions.
Require Import Garden.Orchard.columns.
Require Import Garden.Orchard.protocol_spec.
Require Import Garden.Orchard.circuit_proof.internal_spec.
Require Import Garden.Orchard.circuit_proof.inputs.
Require Import Garden.Orchard.circuit_completeness.witness_input.
Require Import Garden.Field.Field.
Require Import Garden.Plonky3.M.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Lists.List.
Require Import Stdlib.micromega.Lia.

Import ListNotations.

#[local] Existing Instance Primes.PallasPIsPrime.

Global Open Scope Z_scope.

(** * Advice sub-generator: the Poseidon regions and the nullifier chain

    The forward image, on the [RegionId.Poseidon] and [RegionId.Nullifier]
    sub-trees, of the readers and region synthesis programs the soundness
    bridges pin.  For each advice cell some gate/copy/lookup reads, the
    generator places the honest prover's value, computed from the spec-layer
    derived values of [witness_input.v]; every other cell defaults to [0].

    Layout sources (soundness bridges the generator is the forward image of):

    - Poseidon: [circuit_proof/poseidon.v] and [poseidon/pow5.v].  The three
      populated regions of [synthesize_hash] are [InitialState] (the
      [ConstantLength<2>] seed [{0, 0, 2^65}] on [A6]/[A7]/[A8] row 0),
      [AddInput] (seed copy at row 0, the two inputs [nk]/[rho_old] at row 1,
      the pad-and-add output at row 2), and [PermuteState] (the absorbed
      state at row 0, then the 36-row round chain — state lanes on
      [A6]/[A7]/[A8], the partial-round S-box intermediate [mid_0] on [A5]).
      [FullRound]/[PartialRounds]/[PadAndAdd] are the enable-only
      configuration regions of [pow5.synthesize]; they carry no advice.

    - Nullifier: [circuit.synthesize_nullifier] and the base-field bridges
      ([circuit_proof/fixed_base/base_field.v],
      [circuit_proof/base_field_canonicity.v]).  [ScalarAdd] holds
      [poseidon_hash2 + psi] on [A6]/[A7]/[A8]; [BaseFieldIncomplete] is the
      85-window [NullifierK] fixed-base ladder (window points [A0]/[A1],
      incomplete-addition accumulator [A2]/[A3], base-8 running sum [A4],
      square-root witnesses [A5]); [BaseFieldComplete] folds the top window
      into the accumulator; [AlphaLookup] is the 13-word ten-bit lookup of
      [alpha_0']; [CanonicityChecks] gathers the canonicity-gate probes;
      [CompletePointAdd] adds the old-note commitment to the [NullifierK]
      multiple. *)

Module OrchardAdvicePoseidonNullifier.
  Import OrchardActionInputs.
  Import OrchardWitnessInput.

  (** ** The [NullifierK] fixed-base ladder values

      The base-field multiplication's scalar is the nullifier PRF word
      [poseidon_hash2 nk rho_old + psi_old] ([nullifier_scalar]); its
      per-window square-root witnesses are [us_nullifier]. *)
  Definition nk_table : EccSpec.fixed_table :=
    OrchardCircuitSpec.nullifier_k orchard_internal_params.

  Definition default_window : EccSpec.fixed_window :=
    {| EccSpec.fw_coeffs := []; EccSpec.fw_z := 0 |}.

  (** The window-[i] fixed-base multiple point: [fixed_window_point] at the
      scalar's base-8 digit [i] and the [i]-th square-root witness — exactly
      the point the [RunningSumCoordinatesCheck] gate pins to [A0]/[A1] of
      row [i] ([fixed_base/main.v full_width_incomplete_window_correct]). *)
  Definition nk_window_point (w : HonestInput) (i : nat) : Point.t :=
    EccSpec.fixed_window_point
      (List.nth i nk_table default_window)
      (EccSpec.window_digit (nullifier_scalar w) i)
      (List.nth i (us_nullifier w) 0).

  (** The incomplete-addition accumulator after folding windows [0..k]: the
      value carried by [A2]/[A3] at row [k + 1] of the incomplete region
      ([base_field.v incomplete_additions_output]). *)
  Fixpoint nk_acc (w : HonestInput) (k : nat) : Point.t :=
    match k with
    | O => nk_window_point w 0
    | S k' =>
        EccSpec.point_add_incomplete (nk_window_point w (S k')) (nk_acc w k')
    end.

  (** The [BaseFieldComplete] region's product: the complete addition of the
      top window (84) into the incomplete fold of windows [0..83] — the
      whole [NullifierK] multiple ([base_field.v
      base_field_nullifier_k_correct]). *)
  Definition nk_product (w : HonestInput) : Point.t :=
    EccSpec.point_add (nk_window_point w 84%nat) (nk_acc w 83%nat).

  (** The nullifier point [cm_old + [scalar] NullifierK]; its [x] is the
      public [NF_OLD]. *)
  Definition nf_point (w : HonestInput) : Point.t :=
    EccSpec.point_add (cm_old w) (nk_product w).

  (** ** The base-field scalar's canonicity probes

      The canonicity gate ([mul_fixed/base_field_elem.v]) reads the
      running-sum entry [z_84], its low-two-bit / MSB split
      [alpha_1]/[alpha_2], and the ten-bit lookup decomposition of
      [alpha_0' = alpha_0 + 2^130 - t_p] with [alpha_0 = alpha - z_84·2^252]
      ([base_field_canonicity.v]). *)
  Definition z84 (w : HonestInput) : Z :=
    running_sum_at (nullifier_scalar w) 84%nat.

  Definition alpha1 (w : HonestInput) : Z := z84 w mod 4.
  Definition alpha2 (w : HonestInput) : Z := z84 w / 4.

  Definition alpha_0 (w : HonestInput) : Z :=
    nullifier_scalar w - z84 w * 2 ^ 252.

  Definition alpha_0_prime (w : HonestInput) : Z :=
    (alpha_0 w + 2 ^ 130 - Primes.t_p) mod Primes.pallas_p.

  (** The [i]-th ten-bit running sum of [alpha_0'] laid on [A9] of the
      [AlphaLookup] region ([z_i = alpha_0' / 2^{10 i}]). *)
  Definition alpha_run (w : HonestInput) (i : nat) : Z :=
    alpha_0_prime w / 2 ^ (10 * Z.of_nat i).

  (** ** Poseidon state and partial-round intermediate

      [poseidon_round_state w n] ([witness_input.v]) is the state read on
      [A6]/[A7]/[A8] of [PermuteState] row [n].  A partial-round row also
      carries the S-box intermediate [mid_0 = (state_0 + rc)^5] on [A5]
      ([pow5.v partial_rounds_gate]). *)
  Definition pow5_field (x : Z) : Z :=
    let x2 := x *F x in (x2 *F x2) *F x.

  Definition poseidon_mid (w : HonestInput) (row : nat) : Z :=
    pow5_field
      (State.x0 (poseidon_round_state w row)
        +F Garden.Halo2.halo2_poseidon.p128pow5t3.round_constant
             (2 * row - 4)%nat 0%nat).

  (** ** The Poseidon advice plane *)
  Definition advice_poseidon
      (w : HonestInput) (col : Advice.t) (region : RegionId.Poseidon.t)
      (off : Z) : Z :=
    match region with
    | RegionId.Poseidon.InitialState =>
        if off =? 0 then
          match col with
          | Advice.A6 => 0
          | Advice.A7 => 0
          | Advice.A8 => 2 ^ 65
          | _ => 0
          end
        else 0
    | RegionId.Poseidon.AddInput =>
        if off =? 0 then
          match col with
          | Advice.A6 => 0
          | Advice.A7 => 0
          | Advice.A8 => 2 ^ 65
          | _ => 0
          end
        else if off =? 1 then
          match col with
          | Advice.A6 => hi_nk w
          | Advice.A7 => hi_rho_old w
          | _ => 0
          end
        else if off =? 2 then
          match col with
          | Advice.A6 => hi_nk w
          | Advice.A7 => hi_rho_old w
          | Advice.A8 => 2 ^ 65
          | _ => 0
          end
        else 0
    | RegionId.Poseidon.PermuteState =>
        if (0 <=? off) && (off <=? 36) then
          let n := Z.to_nat off in
          match col with
          | Advice.A6 => State.x0 (poseidon_round_state w n)
          | Advice.A7 => State.x1 (poseidon_round_state w n)
          | Advice.A8 => State.x2 (poseidon_round_state w n)
          | Advice.A5 =>
              if (4 <=? off) && (off <=? 31) then poseidon_mid w n else 0
          | _ => 0
          end
        else 0
    | _ => 0
    end.

  (** ** The nullifier-chain advice plane *)
  Definition advice_nullifier
      (w : HonestInput) (col : Advice.t) (region : RegionId.Nullifier.t)
      (off : Z) : Z :=
    match region with
    | RegionId.Nullifier.ScalarAdd =>
        if off =? 0 then
          match col with
          | Advice.A6 => nullifier_scalar w
          | Advice.A7 => Poseidon.poseidon_hash2 (hi_nk w) (hi_rho_old w)
          | Advice.A8 => hi_psi_old w
          | _ => 0
          end
        else 0
    | RegionId.Nullifier.BaseFieldIncomplete =>
        match col with
        | Advice.A0 =>
            if (0 <=? off) && (off <=? 84)
            then Point.x (nk_window_point w (Z.to_nat off)) else 0
        | Advice.A1 =>
            if (0 <=? off) && (off <=? 84)
            then Point.y (nk_window_point w (Z.to_nat off)) else 0
        | Advice.A2 =>
            if (1 <=? off) && (off <=? 84)
            then Point.x (nk_acc w (Z.to_nat off - 1)) else 0
        | Advice.A3 =>
            if (1 <=? off) && (off <=? 84)
            then Point.y (nk_acc w (Z.to_nat off - 1)) else 0
        | Advice.A4 =>
            if (0 <=? off) && (off <=? 85)
            then running_sum_at (nullifier_scalar w) (Z.to_nat off) else 0
        | Advice.A5 =>
            if (0 <=? off) && (off <=? 84)
            then List.nth (Z.to_nat off) (us_nullifier w) 0 else 0
        | _ => 0
        end
    | RegionId.Nullifier.BaseFieldComplete =>
        if off =? 0 then
          match col with
          | Advice.A0 => Point.x (nk_window_point w 84%nat)
          | Advice.A1 => Point.y (nk_window_point w 84%nat)
          | Advice.A2 => Point.x (nk_acc w 83%nat)
          | Advice.A3 => Point.y (nk_acc w 83%nat)
          | _ => 0
          end
        else if off =? 1 then
          match col with
          | Advice.A2 => Point.x (nk_product w)
          | Advice.A3 => Point.y (nk_product w)
          | _ => 0
          end
        else 0
    | RegionId.Nullifier.AlphaLookup =>
        match col with
        | Advice.A9 =>
            if (0 <=? off) && (off <=? 13)
            then alpha_run w (Z.to_nat off) else 0
        | _ => 0
        end
    | RegionId.Nullifier.CanonicityChecks =>
        match col with
        | Advice.A6 =>
            if off =? 0 then nullifier_scalar w
            else if off =? 1 then alpha_0_prime w
            else if off =? 2 then alpha_run w 13%nat
            else 0
        | Advice.A7 =>
            if off =? 1 then alpha1 w
            else if off =? 2 then running_sum_at (nullifier_scalar w) 44%nat
            else 0
        | Advice.A8 =>
            if off =? 0 then z84 w
            else if off =? 1 then alpha2 w
            else if off =? 2 then running_sum_at (nullifier_scalar w) 43%nat
            else 0
        | _ => 0
        end
    | RegionId.Nullifier.CompletePointAdd =>
        if off =? 0 then
          match col with
          | Advice.A0 => Point.x (cm_old w)
          | Advice.A1 => Point.y (cm_old w)
          | Advice.A2 => Point.x (nk_product w)
          | Advice.A3 => Point.y (nk_product w)
          | _ => 0
          end
        else if off =? 1 then
          match col with
          | Advice.A2 => Point.x (nf_point w)
          | Advice.A3 => Point.y (nf_point w)
          | _ => 0
          end
        else 0
    end.

  (** ** The dispatcher on the sub-tree

      Total on all of [RegionId.t]: the Poseidon and Nullifier constructors
      route to the two planes above; every other region (owned by sibling
      sub-generators) reads as [0]. *)
  Definition advice_poseidon_nullifier
      (w : HonestInput) (col : Advice.t) (region : RegionId.t) (off : Z) : Z :=
    match region with
    | RegionId.Poseidon sub => advice_poseidon w col sub off
    | RegionId.Nullifier sub => advice_nullifier w col sub off
    | _ => 0
    end.

  (** ** Agreement lemmas on the generator's own definitions *)

  (** The base-8 running sum telescopes one window at a time: the value on
      [A4] of row [i] is the row-[(i+1)] value scaled by 8 plus the window
      digit the coordinates-check gate reads. *)
  Lemma advice_A4_running_sum_step (w : HonestInput) (i : nat) :
    running_sum_at (nullifier_scalar w) i =
      EccSpec.window_digit (nullifier_scalar w) i
        + 8 * running_sum_at (nullifier_scalar w) (S i).
  Proof. apply running_sum_step. Qed.

  (** The canonicity split [z_84 = alpha_1 + 4·alpha_2] the [z_84_alpha_check]
      constraint pins. *)
  Lemma z84_split (w : HonestInput) :
    z84 w = alpha1 w + 4 * alpha2 w.
  Proof.
    unfold alpha1, alpha2.
    pose proof (Z.div_mod (z84 w) 4 ltac:(lia)) as Hdm.
    lia.
  Qed.

  (** The [PermuteState] output cell [A6] at row 36 is the Poseidon hash of
      the two inputs — the value [circuit_proof/poseidon.v] reads as the
      nullifier PRF output. *)
  Lemma advice_permute_output (w : HonestInput) :
    advice_poseidon w Advice.A6 RegionId.Poseidon.PermuteState 36 =
      Poseidon.poseidon_hash2 (hi_nk w) (hi_rho_old w).
  Proof.
    unfold advice_poseidon.
    change ((0 <=? 36) && (36 <=? 36)) with true.
    cbv iota.
    change (Z.to_nat 36) with 36%nat.
    apply poseidon_round_state_hash2.
  Qed.

  (** The absorbed [PermuteState] row-0 lanes are the PRF seed
      [{nk, rho_old, 2^65}]. *)
  Lemma advice_permute_seed (w : HonestInput) :
    advice_poseidon w Advice.A6 RegionId.Poseidon.PermuteState 0 = hi_nk w /\
    advice_poseidon w Advice.A7 RegionId.Poseidon.PermuteState 0 =
      hi_rho_old w /\
    advice_poseidon w Advice.A8 RegionId.Poseidon.PermuteState 0 =
      Poseidon.domain_iv_constant_length_2.
  Proof.
    unfold advice_poseidon.
    change ((0 <=? 0) && (0 <=? 36)) with true.
    cbv iota.
    change (Z.to_nat 0) with 0%nat.
    unfold poseidon_round_state, poseidon_state.
    cbn [List.seq Stdlib.Lists.List.fold_left poseidon_input_state
      State.x0 State.x1 State.x2].
    repeat split.
  Qed.

End OrchardAdvicePoseidonNullifier.
