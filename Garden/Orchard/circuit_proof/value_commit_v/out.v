(** * ValueCommitV K-out: the [Hvalue] hypothesis from [Holds] alone

    Composes the short-structure wrapper
    [ShortFixedBaseStructure.short_scalar_mul_correct]
    ([circuit_proof/fixed_base/short.v]) with:
    - the whole short-mul program facts peeled from [Holds]
      ([value_commit_v_short_mul_facts]);
    - the ladder-distinctness certificate
      [ValueCommitVLadder.value_commit_v_distinct_holds]
      ([circuit_proof/ladder/value_commit_v.v]), lifted
      through [incomplete_complete_precondition_of_distinct] and
      [incomplete_complete_implies_precondition]
      into the incomplete-additions precondition;
    - the circuit precondition
      [value_commit_v_circuit_precondition_of_holds]
      (the counterpart of the spend_auth_g form in
      [circuit_proof/fixed_base/main.v]);
    - the per-window spec-table match
      [OrchardActionFixedBase.value_commit_v_window_correct];
    - the sign-cell resolution [UnOp.from (eval_cell Γ sign) =
      read9 Γ (…SignRangeCheck)] via [assigned_free_advice_value].

    The final lemma [value_commit_v_hvalue] is verbatim the [Hvalue]
    hypothesis of [cv_net_x_correct_of_fixed_base] /
    [cv_net_y_correct_of_fixed_base] ([circuit_proof/bridges.v:510/576]),
    closed from [Holds] alone. *)

Require Import Garden.Halo2.main.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.lemmas.
Require Import Garden.Orchard.columns.
Require Garden.Orchard.circuit.
Require Garden.Orchard.constants.fixed_bases.value_commit_v.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.spec.
Require Import Garden.Orchard.circuit_spec.
Require Import Garden.Orchard.circuit_proof.inputs.
Require Import Garden.Orchard.circuit_proof.facts.
Require Import Garden.Orchard.circuit_proof.fixed_base.main.
Require Import Garden.Orchard.circuit_proof.fixed_base.short.
Require Import Garden.Orchard.circuit_proof.ladder.value_commit_v.
Require Import Garden.Field.Field.
Require Import Garden.Field.Lemmas.
Require Import Garden.Field.Sqrt.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.fixed_window_canonical.
Require Import Garden.Plonky3.M.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Lists.List.
Require Import Stdlib.micromega.Lia.

Import ListNotations.

#[local] Existing Instance Primes.PallasPIsPrime.

Global Open Scope Z_scope.


Module ValueCommitVOut.
  Import OrchardActionFixedBase.

  (* The consumed ladder/cert lemmas carry [is_square]/[field_sqrt]/
     [fixed_window_point_canonical] over the concrete Pallas modulus;
     conversion must compare them by congruence, never unfold ([modpow] at the
     ~2^253 exponent blows the term up). *)
  Strategy opaque
    [is_square modpow modpow_pos field_sqrt fixed_window_point_canonical].

  Local Notation Holds Γ :=
    (circuit_holds Γ
      Garden.Orchard.circuit.synthesize
      (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)).

  (** ** Table split of the 22-window ValueCommitV spec table *)

  Definition value_commit_v_first : EccSpec.fixed_window :=
    List.hd fixed_window_default
      (OrchardSpec.value_commit_v orchard_circuit_params).

  Definition value_commit_v_middle : EccSpec.fixed_table :=
    List.firstn 20
      (List.skipn 1 (OrchardSpec.value_commit_v orchard_circuit_params)).

  Definition value_commit_v_last : EccSpec.fixed_window :=
    List.nth 21 (OrchardSpec.value_commit_v orchard_circuit_params)
      fixed_window_default.

  Lemma value_commit_v_spec_table_split :
    OrchardSpec.value_commit_v orchard_circuit_params =
    value_commit_v_first :: value_commit_v_middle ++ [value_commit_v_last].
  Proof. reflexivity. Qed.

  Lemma value_commit_v_middle_length :
    List.length value_commit_v_middle = 20%nat.
  Proof. reflexivity. Qed.

  (** ** Facts of the whole short-mul program (both regions), from [Holds] *)

  Lemma value_commit_v_short_mul_facts
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    interpret_facts Γ
      (layouter_facts
        (Garden.Orchard.circuit.synthesize_short_fixed_base_mul
          (layouter_value
            (Garden.Orchard.circuit.assign_free_advice
              (Garden.Orchard.circuit.value_commitment_region
                RegionId.ValueCommitment.MagnitudeRangeCheck)
              "v_net magnitude" Advice.A9 0))
          (layouter_value
            (Garden.Orchard.circuit.assign_free_advice
              (Garden.Orchard.circuit.value_commitment_region
                RegionId.ValueCommitment.SignRangeCheck)
              "v_net sign" Advice.A9 0)))).
  Proof.
    pose proof (value_commitment_facts Γ Hcircuit) as Hfacts.
    unfold Garden.Orchard.circuit.synthesize_value_commitment in Hfacts.
    do 4 apply interpret_layouter_facts_bind_right in Hfacts.
    apply interpret_layouter_facts_bind_left in Hfacts.
    unfold Garden.Orchard.circuit.synthesize_value_commit_orchard in Hfacts.
    apply interpret_layouter_facts_in_namespace in Hfacts.
    apply interpret_layouter_facts_bind_left in Hfacts.
    do 2 apply interpret_layouter_facts_in_namespace in Hfacts.
    exact Hfacts.
  Qed.

  (** ** Window x-nonzero for the 22 ValueCommitV windows (from the on-curve
      coordinates check; the short analogue of
      [spend_auth_g_window_x_nonzero]) *)

  Lemma value_commit_v_window_x_nonzero
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (i : nat) (Hi : (i < 22)%nat) :
    UnOp.from
      (Point.x
        (incomplete_additions_window_point Γ
          (RegionId.ValueCommitment
            RegionId.ValueCommitment.ValueCommitVIncomplete)
          (Z.of_nat i))) <> 0.
  Proof.
    pose proof
      (short_incomplete_region_window_on_curve Γ
        (RegionId.ValueCommitment
          RegionId.ValueCommitment.ValueCommitVIncomplete)
        (Garden.Halo2.Synthesis.Cell.advice
          (Garden.Orchard.circuit.value_commitment_region
            RegionId.ValueCommitment.MagnitudeRangeCheck)
          Advice.A9 0)
        i
        (value_commit_v_incomplete_facts Γ Hcircuit)
        (holds_gates Γ Hcircuit)
        Hi) as Honc.
    apply (EccSpec.pallas_curve_x_nonzero
      (Point.x
        (incomplete_additions_window_point Γ
          (RegionId.ValueCommitment
            RegionId.ValueCommitment.ValueCommitVIncomplete)
          (Z.of_nat i)))
      (Point.y
        (incomplete_additions_window_point Γ
          (RegionId.ValueCommitment
            RegionId.ValueCommitment.ValueCommitVIncomplete)
          (Z.of_nat i)))).
    exact Honc.
  Qed.

  (** ** The complete precondition from [Holds]: ladder distinctness +
      on-curve + x-nonzero, through
      [incomplete_complete_precondition_of_distinct] *)

  Lemma value_commit_v_complete_of_holds
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    incomplete_additions_complete_precondition Γ
      (RegionId.ValueCommitment
        RegionId.ValueCommitment.ValueCommitVIncomplete) 1 20
      (incomplete_additions_window_point Γ
        (RegionId.ValueCommitment
          RegionId.ValueCommitment.ValueCommitVIncomplete) 0).
  Proof.
    apply incomplete_complete_precondition_of_distinct.
    - replace 0 with (Z.of_nat 0) by reflexivity.
      apply (short_incomplete_region_window_on_curve Γ
        (RegionId.ValueCommitment
          RegionId.ValueCommitment.ValueCommitVIncomplete)
        (Garden.Halo2.Synthesis.Cell.advice
          (Garden.Orchard.circuit.value_commitment_region
            RegionId.ValueCommitment.MagnitudeRangeCheck)
          Advice.A9 0)
        0%nat
        (value_commit_v_incomplete_facts Γ Hcircuit)
        (holds_gates Γ Hcircuit)).
      lia.
    - replace 0 with (Z.of_nat 0) by reflexivity.
      apply (value_commit_v_window_x_nonzero Γ Hcircuit 0%nat).
      lia.
    - intros i Hi.
      replace (1 + Z.of_nat i) with (Z.of_nat (S i)) by lia.
      apply (short_incomplete_region_window_on_curve Γ
        (RegionId.ValueCommitment
          RegionId.ValueCommitment.ValueCommitVIncomplete)
        (Garden.Halo2.Synthesis.Cell.advice
          (Garden.Orchard.circuit.value_commitment_region
            RegionId.ValueCommitment.MagnitudeRangeCheck)
          Advice.A9 0)
        (S i)
        (value_commit_v_incomplete_facts Γ Hcircuit)
        (holds_gates Γ Hcircuit)).
      lia.
    - intros i Hi.
      replace (1 + Z.of_nat i) with (Z.of_nat (S i)) by lia.
      apply (value_commit_v_window_x_nonzero Γ Hcircuit (S i)).
      lia.
    - exact
        (ValueCommitVLadder.value_commit_v_distinct_holds
          Γ Hcircuit).
  Qed.

  Lemma value_commit_v_incomplete_of_holds
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    incomplete_additions_precondition Γ
      (RegionId.ValueCommitment
        RegionId.ValueCommitment.ValueCommitVIncomplete) 1 20
      (incomplete_additions_window_point Γ
        (RegionId.ValueCommitment
          RegionId.ValueCommitment.ValueCommitVIncomplete) 0).
  Proof.
    apply incomplete_complete_implies_precondition.
    exact (value_commit_v_complete_of_holds Γ Hcircuit).
  Qed.

  (** ** The circuit precondition from [Holds] (the counterpart of
      [spend_auth_g_circuit_of_complete]
      at counts 20/last 21) *)

  Lemma value_commit_v_circuit_precondition_of_holds
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    fixed_scalar_mul_circuit_precondition
      (OrchardSpec.value_commit_v orchard_circuit_params)
      (read9 Γ
        (RegionId.ValueCommitment
          RegionId.ValueCommitment.MagnitudeRangeCheck))
      (read_us Γ
        (RegionId.ValueCommitment
          RegionId.ValueCommitment.ValueCommitVIncomplete) 22).
  Proof.
    pose proof (value_commit_v_window_correct Γ Hcircuit 0%nat
      value_commit_v_first eq_refl) as Hfirst.
    rewrite value_commit_v_spec_table_split.
    cbn [fixed_scalar_mul_circuit_precondition].
    rewrite <- Hfirst.
    eapply circuit_tail_precondition_of_complete
      with (n := 20%nat).
    - rewrite List.length_app, value_commit_v_middle_length. reflexivity.
    - exact (value_commit_v_complete_of_holds Γ Hcircuit).
    - intros j w Hnth.
      replace (1 + Z.of_nat j) with (Z.of_nat (S j)) by lia.
      replace (1 + j)%nat with (S j) by lia.
      apply (value_commit_v_window_correct Γ Hcircuit).
      rewrite value_commit_v_spec_table_split.
      cbn [List.nth_error].
      exact Hnth.
    - apply (short_incomplete_region_window_on_curve Γ
        (RegionId.ValueCommitment
          RegionId.ValueCommitment.ValueCommitVIncomplete)
        (Garden.Halo2.Synthesis.Cell.advice
          (Garden.Orchard.circuit.value_commitment_region
            RegionId.ValueCommitment.MagnitudeRangeCheck)
          Advice.A9 0)
        0%nat
        (value_commit_v_incomplete_facts Γ Hcircuit)
        (holds_gates Γ Hcircuit)).
      lia.
    - exact (proj1 (incomplete_additions_window_point_reduced Γ
        (RegionId.ValueCommitment
          RegionId.ValueCommitment.ValueCommitVIncomplete)
        (Z.of_nat 0))).
    - exact (proj2 (incomplete_additions_window_point_reduced Γ
        (RegionId.ValueCommitment
          RegionId.ValueCommitment.ValueCommitVIncomplete)
        (Z.of_nat 0))).
    - intros j Hj.
      rewrite List.length_app, value_commit_v_middle_length in Hj.
      cbn [List.length] in Hj.
      replace (1 + Z.of_nat j) with (Z.of_nat (S j)) by lia.
      apply (short_incomplete_region_window_on_curve Γ
        (RegionId.ValueCommitment
          RegionId.ValueCommitment.ValueCommitVIncomplete)
        (Garden.Halo2.Synthesis.Cell.advice
          (Garden.Orchard.circuit.value_commitment_region
            RegionId.ValueCommitment.MagnitudeRangeCheck)
          Advice.A9 0)
        (S j)
        (value_commit_v_incomplete_facts Γ Hcircuit)
        (holds_gates Γ Hcircuit)).
      lia.
    - intros j Hj.
      exact (proj1 (incomplete_additions_window_point_reduced Γ
        (RegionId.ValueCommitment
          RegionId.ValueCommitment.ValueCommitVIncomplete)
        (1 + Z.of_nat j))).
    - intros j Hj.
      exact (proj2 (incomplete_additions_window_point_reduced Γ
        (RegionId.ValueCommitment
          RegionId.ValueCommitment.ValueCommitVIncomplete)
        (1 + Z.of_nat j))).
  Qed.

  (** ** The [Hvalue] hypothesis of [cv_net_x_correct_of_fixed_base] /
      [cv_net_y_correct_of_fixed_base] ([circuit_proof/bridges.v:510/576]),
      from [Holds] alone. *)

  Lemma value_commit_v_hvalue
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    let magnitude :=
      layouter_value
        (Garden.Orchard.circuit.assign_free_advice
          (Garden.Orchard.circuit.value_commitment_region
            RegionId.ValueCommitment.MagnitudeRangeCheck)
          "v_net magnitude" Advice.A9 0) in
    let sign :=
      layouter_value
        (Garden.Orchard.circuit.assign_free_advice
          (Garden.Orchard.circuit.value_commitment_region
            RegionId.ValueCommitment.SignRangeCheck)
          "v_net sign" Advice.A9 0) in
    let v_point :=
      EccSpec.fixed_scalar_mul
        (OrchardSpec.value_commit_v orchard_circuit_params)
        (read9 Γ
          (RegionId.ValueCommitment
            RegionId.ValueCommitment.MagnitudeRangeCheck))
        (read_us Γ
          (RegionId.ValueCommitment
            RegionId.ValueCommitment.ValueCommitVIncomplete) 22) in
    Field.map_mod
      (assigned_point_value Γ
        (layouter_value
          (Garden.Orchard.circuit
            .synthesize_short_fixed_base_mul magnitude sign))) =
    {|
      Point.x := Point.x v_point;
      Point.y :=
        read9 Γ
          (RegionId.ValueCommitment
            RegionId.ValueCommitment.SignRangeCheck) *F
        Point.y v_point;
    |}.
  Proof.
    cbv zeta.
    assert (Hwindow :
      forall (j : nat) (w : EccSpec.fixed_window),
        List.nth_error
          (value_commit_v_first :: value_commit_v_middle ++
            [value_commit_v_last]) j = Some w ->
        incomplete_additions_window_point Γ
          (RegionId.ValueCommitment
            RegionId.ValueCommitment.ValueCommitVIncomplete) (Z.of_nat j) =
        EccSpec.fixed_window_point w
          (EccSpec.window_digit
            (read9 Γ
              (RegionId.ValueCommitment
                RegionId.ValueCommitment.MagnitudeRangeCheck))
            j)
          (List.nth j
            (read_us Γ
              (RegionId.ValueCommitment
                RegionId.ValueCommitment.ValueCommitVIncomplete) 22)
            0)).
    { intros j w Hnth.
      apply (value_commit_v_window_correct Γ Hcircuit j w).
      rewrite value_commit_v_spec_table_split.
      exact Hnth. }
    assert (Hcircuit_pre :
      fixed_scalar_mul_circuit_precondition
        (value_commit_v_first :: value_commit_v_middle ++
          [value_commit_v_last])
        (read9 Γ
          (RegionId.ValueCommitment
            RegionId.ValueCommitment.MagnitudeRangeCheck))
        (read_us Γ
          (RegionId.ValueCommitment
            RegionId.ValueCommitment.ValueCommitVIncomplete) 22)).
    { rewrite <- value_commit_v_spec_table_split.
      exact
        (value_commit_v_circuit_precondition_of_holds
          Γ Hcircuit). }
    rewrite
      (ShortFixedBaseStructure.short_scalar_mul_correct
        Γ _ _ value_commit_v_first value_commit_v_last value_commit_v_middle _ _
        (value_commit_v_short_mul_facts Γ Hcircuit)
        (holds_gates Γ Hcircuit)
        (value_commit_v_incomplete_of_holds Γ Hcircuit)
        value_commit_v_middle_length
        Hwindow
        Hcircuit_pre).
    rewrite <- value_commit_v_spec_table_split.
    rewrite (assigned_free_advice_value Γ
      (Garden.Orchard.circuit.value_commitment_region
        RegionId.ValueCommitment.SignRangeCheck)
      "v_net sign" Advice.A9).
    reflexivity.
  Qed.

End ValueCommitVOut.
