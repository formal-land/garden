(* Structure wrapper for the base-field (85-window) fixed-base
   multiplication used by the nullifier [NullifierK] leg: the
   incomplete-addition region (windows 0..84, counts 1/83), the window-84
   [mul_b] read-off, the separate [BaseFieldComplete] region's complete
   addition, and the composed program
   [synth_nullifier_k_mul], down to
   [EccSpec.fixed_scalar_mul].  Table-parameterized: the scalar [k] and the
   per-window hypothesis [Hwindow] are inputs, so the consumer instantiates
   [k] at the circuit-word scalar ([A4[0]] of the incomplete region); the
   digit match and the [poseidon_hash2] identification of that word live in
   the canonicity lane, not here. *)

Require Import Garden.Halo2.main.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.lemmas.
Require Import Garden.Orchard.columns.
Require Garden.Orchard.circuit.
Require Garden.Orchard.constants.fixed_bases.nullifier_k.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.spec.
Require Import Garden.Orchard.circuit_spec.
Require Import Garden.Orchard.circuit_proof.inputs.
Require Import Garden.Orchard.circuit_proof.facts.
Require Import Garden.Orchard.circuit_proof.fixed_base.main.
Require Import Garden.Field.Field.
Require Import Garden.Field.Lemmas.
Require Import Garden.Plonky3.M.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Lists.List.
Require Import Stdlib.micromega.Lia.

Import ListNotations.

#[local] Existing Instance Primes.PallasPIsPrime.

Global Open Scope Z_scope.


Module BaseFieldFixedBaseStructure.
  Import OrchardActionFixedBase.

  (** Accumulator of the base-field incomplete-addition region: the fold of
      the 83 incomplete additions (rows 1..83) over the window-0 point. *)
  Lemma base_field_incomplete_region_acc_correct
      (Γ : Assignment.t columns RegionId.t)
      (region : RegionId.t)
      (scalar : Garden.Halo2.Synthesis.Cell.t columns RegionId.t)
      (Hfacts :
        interpret_facts Γ
          (layouter_facts
            (Garden.Orchard.circuit
              .synth_base_field_mul_incomplete
              region scalar)))
      (Hgates :
        satisfies_gates Γ
          (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty))
      (Hpre :
        incomplete_additions_precondition Γ region 1 83
          (incomplete_additions_window_point Γ region 0)) :
    Field.map_mod
      (assigned_point_value Γ
        (layouter_value
          (Garden.Orchard.circuit
            .synth_base_field_mul_incomplete
            region scalar)).(Garden.Orchard.circuit.BaseFieldFixedResult.acc)) =
      incomplete_additions_output Γ region 1 83
        (incomplete_additions_window_point Γ region 0).
  Proof.
    pose proof Hfacts as Hacc_facts.
    unfold Garden.Orchard.circuit
      .synth_base_field_mul_incomplete in Hacc_facts.
    apply interpret_layouter_facts_add_region in Hacc_facts.
    do 5 apply interpret_region_facts_bind_right in Hacc_facts.
    apply interpret_region_facts_bind_left in Hacc_facts.
    unfold Garden.Orchard.circuit
      .synth_base_field_mul_incomplete.
    cbn [layouter_value region_value Monad.bind
      Garden.Halo2.Synthesis.RegionIsMonad
      Garden.Orchard.circuit.BaseFieldFixedResult.acc].
    change (Field.map_mod
      (assigned_point_value Γ
        (region_value
          (Garden.Orchard.circuit.assign_incomplete_additions region 1 83
            (region_value
              (Garden.Orchard.circuit.assign_mul_fixed_window region 0))))) =
      incomplete_additions_output Γ region 1 83
        (incomplete_additions_window_point Γ region 0)).
    rewrite (assign_incomplete_additions_correct Γ region 1 83
      (region_value
        (Garden.Orchard.circuit.assign_mul_fixed_window region 0))).
    - rewrite assign_mul_fixed_window_correct. reflexivity.
    - exact Hacc_facts.
    - exact Hgates.
    - rewrite assign_mul_fixed_window_correct. exact Hpre.
  Qed.

  (** The [mul_b] output of the base-field incomplete-addition region is the
      window-84 point (the most significant window, folded separately by a
      complete addition in the [BaseFieldComplete] region). *)
  Lemma base_field_incomplete_region_mul_b_correct
      (Γ : Assignment.t columns RegionId.t)
      (region : RegionId.t)
      (scalar : Garden.Halo2.Synthesis.Cell.t columns RegionId.t) :
    Field.map_mod
      (assigned_point_value Γ
        (layouter_value
          (Garden.Orchard.circuit
            .synth_base_field_mul_incomplete
            region scalar))
          .(Garden.Orchard.circuit.BaseFieldFixedResult.mul_b)) =
      incomplete_additions_window_point Γ region 84.
  Proof.
    unfold Garden.Orchard.circuit
      .synth_base_field_mul_incomplete.
    cbn [layouter_value region_value Monad.bind
      Garden.Halo2.Synthesis.RegionIsMonad
      Garden.Orchard.circuit.BaseFieldFixedResult.mul_b].
    change (Field.map_mod
      (assigned_point_value Γ
        (region_value
          (Garden.Orchard.circuit.assign_mul_fixed_window region 84))) =
      incomplete_additions_window_point Γ region 84).
    rewrite assign_mul_fixed_window_correct.
    reflexivity.
  Qed.

  (** The [BaseFieldComplete] region: a single complete addition of [mul_b]
      (window 84) into the incomplete-addition accumulator. *)
  Lemma base_field_complete_region_correct
      (Γ : Assignment.t columns RegionId.t)
      (region : RegionId.t)
      (result : Garden.Orchard.circuit.BaseFieldFixedResult.t)
      (Hfacts :
        interpret_facts Γ
          (layouter_facts
            (Garden.Orchard.circuit
              .synth_base_field_mul_complete
              region result)))
      (Hgates :
        satisfies_gates Γ
          (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)) :
    Field.map_mod
      (assigned_point_value Γ
        (layouter_value
          (Garden.Orchard.circuit
            .synth_base_field_mul_complete
            region result))) =
      EccSpec.point_add
        (Field.map_mod
          (assigned_point_value Γ
            result.(Garden.Orchard.circuit.BaseFieldFixedResult.mul_b)))
        (Field.map_mod
          (assigned_point_value Γ
            result.(Garden.Orchard.circuit.BaseFieldFixedResult.acc))).
  Proof.
    unfold Garden.Orchard.circuit
      .synth_base_field_mul_complete in Hfacts.
    apply interpret_layouter_facts_add_region in Hfacts.
    apply (complete_point_add_correct Γ region ""
      result.(Garden.Orchard.circuit.BaseFieldFixedResult.mul_b)
      result.(Garden.Orchard.circuit.BaseFieldFixedResult.acc)).
    - exact Hfacts.
    - exact Hgates.
  Qed.

  (** Whole-program structure of the base-field fixed-base multiplication of
      NullifierK: the complete addition of window 84 into the fold of windows
      0..83.  The [AlphaLookup] and [CanonicityChecks] legs are
      value-transparent (the program returns the complete-region product). *)
  Lemma base_field_nullifier_k_correct
      (Γ : Assignment.t columns RegionId.t)
      (scalar : Garden.Halo2.Synthesis.Cell.t columns RegionId.t)
      (Hfacts :
        interpret_facts Γ
          (layouter_facts
            (Garden.Orchard.circuit
              .synth_nullifier_k_mul scalar)))
      (Hgates :
        satisfies_gates Γ
          (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty))
      (Hpre :
        incomplete_additions_precondition Γ
          (RegionId.Nullifier RegionId.Nullifier.BaseFieldIncomplete) 1 83
          (incomplete_additions_window_point Γ
            (RegionId.Nullifier RegionId.Nullifier.BaseFieldIncomplete) 0)) :
    Field.map_mod
      (assigned_point_value Γ
        (layouter_value
          (Garden.Orchard.circuit
            .synth_nullifier_k_mul scalar))) =
      EccSpec.point_add
        (incomplete_additions_window_point Γ
          (RegionId.Nullifier RegionId.Nullifier.BaseFieldIncomplete) 84)
        (incomplete_additions_output Γ
          (RegionId.Nullifier RegionId.Nullifier.BaseFieldIncomplete) 1 83
          (incomplete_additions_window_point Γ
            (RegionId.Nullifier RegionId.Nullifier.BaseFieldIncomplete) 0)).
  Proof.
    unfold Garden.Orchard.circuit
      .synth_nullifier_k_mul in Hfacts.
    apply interpret_layouter_facts_in_namespace in Hfacts.
    pose (incomplete :=
      Garden.Orchard.circuit
        .synth_base_field_mul_incomplete
        (Garden.Orchard.circuit.nullifier_region
          RegionId.Nullifier.BaseFieldIncomplete)
        scalar).
    assert (Hincomplete_facts : interpret_facts Γ (layouter_facts incomplete)).
    { subst incomplete.
      apply interpret_layouter_facts_bind_left in Hfacts.
      exact Hfacts. }
    assert (Hcomplete_facts :
        interpret_facts Γ
          (layouter_facts
            (Garden.Orchard.circuit
              .synth_base_field_mul_complete
              (Garden.Orchard.circuit.nullifier_region
                RegionId.Nullifier.BaseFieldComplete)
              (layouter_value incomplete)))).
    { subst incomplete.
      apply interpret_layouter_facts_bind_right in Hfacts.
      apply interpret_layouter_facts_bind_left in Hfacts.
      exact Hfacts. }
    change (Field.map_mod
      (assigned_point_value Γ
        (layouter_value
          (Garden.Orchard.circuit
            .synth_base_field_mul_complete
            (Garden.Orchard.circuit.nullifier_region
              RegionId.Nullifier.BaseFieldComplete)
            (layouter_value incomplete)))) =
      EccSpec.point_add
        (incomplete_additions_window_point Γ
          (RegionId.Nullifier RegionId.Nullifier.BaseFieldIncomplete) 84)
        (incomplete_additions_output Γ
          (RegionId.Nullifier RegionId.Nullifier.BaseFieldIncomplete) 1 83
          (incomplete_additions_window_point Γ
            (RegionId.Nullifier RegionId.Nullifier.BaseFieldIncomplete) 0))).
    rewrite (base_field_complete_region_correct Γ
      (Garden.Orchard.circuit.nullifier_region
        RegionId.Nullifier.BaseFieldComplete)
      (layouter_value incomplete) Hcomplete_facts Hgates).
    subst incomplete.
    rewrite (base_field_incomplete_region_mul_b_correct
      Γ
      (Garden.Orchard.circuit.nullifier_region
        RegionId.Nullifier.BaseFieldIncomplete)
      scalar).
    rewrite (base_field_incomplete_region_acc_correct
      Γ
      (Garden.Orchard.circuit.nullifier_region
        RegionId.Nullifier.BaseFieldIncomplete)
      scalar Hincomplete_facts Hgates Hpre).
    reflexivity.
  Qed.

  (** Final base-field wrapper: with a window-correctness hypothesis over the
      85-entry table split [first :: middle ++ [last]] and the circuit
      precondition, the program output is the specification's
      [fixed_scalar_mul].  [k] is a parameter: the consumer instantiates it
      at the circuit-word scalar ([A4[0]] of the incomplete region), and
      [Hwindow] is then the digit-match obligation of the canonicity lane. *)
  Lemma base_field_nullifier_k_scalar_mul_correct
      (Γ : Assignment.t columns RegionId.t)
      (scalar : Garden.Halo2.Synthesis.Cell.t columns RegionId.t)
      (first last : EccSpec.fixed_window) (middle : EccSpec.fixed_table)
      (k : Z) (us : list Z)
      (Hfacts :
        interpret_facts Γ
          (layouter_facts
            (Garden.Orchard.circuit
              .synth_nullifier_k_mul scalar)))
      (Hgates :
        satisfies_gates Γ
          (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty))
      (Hpre :
        incomplete_additions_precondition Γ
          (RegionId.Nullifier RegionId.Nullifier.BaseFieldIncomplete) 1 83
          (incomplete_additions_window_point Γ
            (RegionId.Nullifier RegionId.Nullifier.BaseFieldIncomplete) 0))
      (Hmiddle_len : List.length middle = 83%nat)
      (Hwindow :
        forall (j : nat) (w : EccSpec.fixed_window),
          List.nth_error (first :: middle ++ [last]) j = Some w ->
          incomplete_additions_window_point Γ
            (RegionId.Nullifier RegionId.Nullifier.BaseFieldIncomplete)
            (Z.of_nat j) =
          EccSpec.fixed_window_point w
            (EccSpec.window_digit k j)
            (List.nth j us 0))
      (Hcircuit_pre :
        fixed_scalar_mul_circuit_precondition (first :: middle ++ [last]) k us) :
    Field.map_mod
      (assigned_point_value Γ
        (layouter_value
          (Garden.Orchard.circuit
            .synth_nullifier_k_mul scalar))) =
      EccSpec.fixed_scalar_mul (first :: middle ++ [last]) k us.
  Proof.
    rewrite (base_field_nullifier_k_correct Γ scalar
      Hfacts Hgates Hpre).
    assert (Hfirst :
        incomplete_additions_window_point Γ
          (RegionId.Nullifier RegionId.Nullifier.BaseFieldIncomplete) 0 =
        EccSpec.fixed_window_point first
          (EccSpec.window_digit k 0%nat)
          (List.nth 0%nat us 0)).
    { exact (Hwindow 0%nat first eq_refl). }
    assert (Hlast :
        incomplete_additions_window_point Γ
          (RegionId.Nullifier RegionId.Nullifier.BaseFieldIncomplete) 84 =
        EccSpec.fixed_window_point last
          (EccSpec.window_digit k 84%nat)
          (List.nth 84%nat us 0)).
    { replace 84 with (Z.of_nat (S (List.length middle))) by
        (rewrite Hmiddle_len; reflexivity).
      replace 84%nat with (S (List.length middle)) by
        (rewrite Hmiddle_len; reflexivity).
      apply Hwindow.
      cbn [List.nth_error].
      rewrite nth_error_app2 by lia.
      rewrite Nat.sub_diag.
      reflexivity. }
    rewrite Hlast.
    rewrite <- Hmiddle_len.
    rewrite (incomplete_output_scalar_mul_incomplete_tail Γ
      (RegionId.Nullifier RegionId.Nullifier.BaseFieldIncomplete) 1 middle k us
      1%nat
      (incomplete_additions_window_point Γ
        (RegionId.Nullifier RegionId.Nullifier.BaseFieldIncomplete) 0)).
    - rewrite Hfirst.
      (* [rewrite <- Hmiddle_len] also rewrites inside the unary numeral
         [84 = S 83], so the most significant index now reads
         [S (List.length middle)]. *)
      replace (S (List.length middle)) with (1 + List.length middle)%nat
        by lia.
      rewrite <- (fixed_scalar_mul_circuit_tail_app_last middle last k us 1%nat
        (EccSpec.fixed_window_point first
          (EccSpec.window_digit k 0%nat)
          (List.nth 0%nat us 0))).
      change (fixed_scalar_mul_circuit (first :: middle ++ [last]) k us =
        EccSpec.fixed_scalar_mul (first :: middle ++ [last]) k us).
      apply fixed_scalar_mul_circuit_eq_fixed_scalar_mul.
      exact Hcircuit_pre.
    - intros j w Hnth.
      replace (1 + Z.of_nat j) with (Z.of_nat (S j)) by lia.
      replace (1 + j)%nat with (S j) by lia.
      apply Hwindow.
      cbn [List.nth_error].
      rewrite nth_error_app1.
      + exact Hnth.
      + apply nth_error_Some.
        rewrite Hnth.
        discriminate.
  Qed.

End BaseFieldFixedBaseStructure.
