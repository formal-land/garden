(* Structure wrapper for the short (signed, 22-window) fixed-base
   multiplication used by the value commitment [ValueCommitV] leg: the
   incomplete-addition region (windows 0..20, counts 1/20), the window-21
   [mul_b] read-off, the MSB region's complete addition, the sign row
   ([QMulFixedShort] gate), and the composed program
   [synthesize_short_fixed_base_mul], down to
   [EccSpec.fixed_scalar_mul] with the sign applied to the ordinate. *)

Require Import Garden.Halo2.main.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.lemmas.
Require Import Garden.Orchard.columns.
Require Garden.Orchard.circuit.
Require Garden.Orchard.constants.fixed_bases.value_commit_v.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.spec.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.mul_fixed.short_proof.
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


Module ShortFixedBaseStructure.
  Import OrchardActionFixedBase.

  (** Accumulator of the short incomplete-addition region: the fold of the 20
      incomplete additions (rows 1..20) over the window-0 point. *)
  Lemma short_incomplete_region_acc_correct
      (Γ : Assignment.t columns RegionId.t)
      (region : RegionId.t)
      (magnitude : Garden.Halo2.Synthesis.Cell.t columns RegionId.t)
      (Hfacts :
        interpret_facts Γ
          (layouter_facts
            (Garden.Orchard.circuit
              .synth_short_mul_incomplete
              region magnitude)))
      (Hgates :
        satisfies_gates Γ
          (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty))
      (Hpre :
        incomplete_additions_precondition Γ region 1 20
          (incomplete_additions_window_point Γ region 0)) :
    Field.map_mod
      (assigned_point_value Γ
        (layouter_value
          (Garden.Orchard.circuit
            .synth_short_mul_incomplete
            region magnitude)).(Garden.Orchard.circuit.ShortFixedResult.acc)) =
      incomplete_additions_output Γ region 1 20
        (incomplete_additions_window_point Γ region 0).
  Proof.
    pose proof Hfacts as Hacc_facts.
    unfold Garden.Orchard.circuit
      .synth_short_mul_incomplete in Hacc_facts.
    apply interpret_layouter_facts_add_region in Hacc_facts.
    do 5 apply interpret_region_facts_bind_right in Hacc_facts.
    apply interpret_region_facts_bind_left in Hacc_facts.
    unfold Garden.Orchard.circuit
      .synth_short_mul_incomplete.
    cbn [layouter_value region_value Monad.bind
      Garden.Halo2.Synthesis.RegionIsMonad
      Garden.Orchard.circuit.ShortFixedResult.acc].
    change (Field.map_mod
      (assigned_point_value Γ
        (region_value
          (Garden.Orchard.circuit.assign_incomplete_additions region 1 20
            (region_value
              (Garden.Orchard.circuit.assign_mul_fixed_window region 0))))) =
      incomplete_additions_output Γ region 1 20
        (incomplete_additions_window_point Γ region 0)).
    rewrite (assign_incomplete_additions_correct Γ region 1 20
      (region_value
        (Garden.Orchard.circuit.assign_mul_fixed_window region 0))).
    - rewrite assign_mul_fixed_window_correct. reflexivity.
    - exact Hacc_facts.
    - exact Hgates.
    - rewrite assign_mul_fixed_window_correct. exact Hpre.
  Qed.

  (** The [mul_b] output of the short incomplete-addition region is the
      window-21 point (the most significant window, folded separately by a
      complete addition in the MSB region). *)
  Lemma short_incomplete_region_mul_b_correct
      (Γ : Assignment.t columns RegionId.t)
      (region : RegionId.t)
      (magnitude : Garden.Halo2.Synthesis.Cell.t columns RegionId.t) :
    Field.map_mod
      (assigned_point_value Γ
        (layouter_value
          (Garden.Orchard.circuit
            .synth_short_mul_incomplete
            region magnitude)).(Garden.Orchard.circuit.ShortFixedResult.mul_b)) =
      incomplete_additions_window_point Γ region 21.
  Proof.
    unfold Garden.Orchard.circuit
      .synth_short_mul_incomplete.
    cbn [layouter_value region_value Monad.bind
      Garden.Halo2.Synthesis.RegionIsMonad
      Garden.Orchard.circuit.ShortFixedResult.mul_b].
    change (Field.map_mod
      (assigned_point_value Γ
        (region_value
          (Garden.Orchard.circuit.assign_mul_fixed_window region 21))) =
      incomplete_additions_window_point Γ region 21).
    rewrite assign_mul_fixed_window_correct.
    reflexivity.
  Qed.

  (** The complete addition inside the MSB region adds [mul_b] (window 21)
      into the incomplete-addition accumulator. *)
  Lemma short_msb_region_add_correct
      (Γ : Assignment.t columns RegionId.t)
      (region : RegionId.t)
      (sign last_window : Garden.Halo2.Synthesis.Cell.t columns RegionId.t)
      (acc mul_b : Garden.Orchard.circuit.AssignedPoint.t)
      (Hfacts :
        interpret_facts Γ
          (layouter_facts
            (Garden.Orchard.circuit.synthesize_short_fixed_base_mul_msb_region
              region sign last_window acc mul_b)))
      (Hgates :
        satisfies_gates Γ
          (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)) :
    Field.map_mod
      (assigned_point_value Γ
        (region_value
          (Garden.Orchard.circuit.assign_complete_add region mul_b acc))) =
      EccSpec.point_add
        (Field.map_mod (assigned_point_value Γ mul_b))
        (Field.map_mod (assigned_point_value Γ acc)).
  Proof.
    unfold Garden.Orchard.circuit
      .synthesize_short_fixed_base_mul_msb_region in Hfacts.
    apply interpret_layouter_facts_add_region in Hfacts.
    apply interpret_region_facts_bind_left in Hfacts.
    exact (complete_point_add_correct Γ region "" mul_b acc Hfacts Hgates).
  Qed.

  (** The "sign_check" constraint of [short_fixed_base_mul_gate]: the
      witnessed sign on A4 squares to one. *)
  Lemma short_fixed_base_mul_sign_square
      (Γ : Assignment.t columns RegionId.t)
      (region : RegionId.t) (row : Z)
      (Hselector : Γ ⊢ ⟦ Selector.QMulFixedShort ⟧ (region, row) <> 0)
      (Hgate :
        Γ ⊢ ⟦ Garden.Halo2.halo2_gadgets.ecc.chip.mul_fixed.short
            .short_fixed_base_mul_gate ⟧ (region, row)) :
    (Γ ⊢ ⟦ Expression.Advice Advice.A4 Rotation.cur ⟧ (region, row)) *F
      (Γ ⊢ ⟦ Expression.Advice Advice.A4 Rotation.cur ⟧ (region, row)) = 1.
  Proof.
    with_strategy opaque [BinOp.add BinOp.mul BinOp.sub UnOp.from] cbn in *.
    destruct Hgate as (_ & h2 & _ & _).
    specialize (h2 Hselector).
    rewrite h2.
    apply from_one.
  Qed.

  (** Output of the MSB region: the x-coordinate of the complete addition,
      and its y-coordinate multiplied by the copied sign. *)
  Lemma short_msb_region_output_correct
      (Γ : Assignment.t columns RegionId.t)
      (region : RegionId.t)
      (sign last_window : Garden.Halo2.Synthesis.Cell.t columns RegionId.t)
      (acc mul_b : Garden.Orchard.circuit.AssignedPoint.t)
      (Hfacts :
        interpret_facts Γ
          (layouter_facts
            (Garden.Orchard.circuit.synthesize_short_fixed_base_mul_msb_region
              region sign last_window acc mul_b)))
      (Hgates :
        satisfies_gates Γ
          (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)) :
    Field.map_mod
      (assigned_point_value Γ
        (layouter_value
          (Garden.Orchard.circuit.synthesize_short_fixed_base_mul_msb_region
            region sign last_window acc mul_b))) =
      {|
        Point.x :=
          Point.x
            (EccSpec.point_add
              (Field.map_mod (assigned_point_value Γ mul_b))
              (Field.map_mod (assigned_point_value Γ acc)));
        Point.y :=
          UnOp.from (eval_cell Γ sign) *F
          Point.y
            (EccSpec.point_add
              (Field.map_mod (assigned_point_value Γ mul_b))
              (Field.map_mod (assigned_point_value Γ acc)));
      |}.
  Proof.
    pose proof (short_msb_region_add_correct Γ region
      sign last_window acc mul_b Hfacts Hgates) as Hadd.
    (* The sign copy: A4 at row 1 holds the sign cell's value. *)
    pose proof Hfacts as Hcopy_sign.
    unfold Garden.Orchard.circuit
      .synthesize_short_fixed_base_mul_msb_region in Hcopy_sign.
    apply interpret_layouter_facts_add_region in Hcopy_sign.
    apply interpret_region_facts_bind_right in Hcopy_sign.
    apply interpret_region_facts_bind_left in Hcopy_sign.
    cbn [region_facts interpret_facts interpret_fact] in Hcopy_sign.
    destruct Hcopy_sign as [Hcopy_sign _].
    (* The [QMulFixedShort] selector is enabled at row 1. *)
    pose proof Hfacts as Hsel.
    unfold Garden.Orchard.circuit
      .synthesize_short_fixed_base_mul_msb_region in Hsel.
    apply interpret_layouter_facts_add_region in Hsel.
    do 3 apply interpret_region_facts_bind_right in Hsel.
    apply interpret_region_facts_bind_left in Hsel.
    cbn [region_facts interpret_facts interpret_fact] in Hsel.
    destruct Hsel as [Hsel _].
    pose proof (enabled_nonzero Γ Selector.QMulFixedShort region 1 Hsel)
      as Hsel'.
    pose proof (satisfies_gates_at Γ
      (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)
      Garden.Halo2.halo2_gadgets.ecc.chip.mul_fixed.short
        .short_fixed_base_mul_gate
      region 1 ltac:(cbn; repeat (first [left; reflexivity | right]))
      Hgates) as Hgate.
    pose proof (ShortFixedBaseMul.deterministic Γ region 1 Hsel' Hgate)
      as Hdet.
    pose proof (f_equal ShortFixedBaseMul.y_a Hdet) as HA3.
    unfold ShortFixedBaseMul.output in HA3.
    cbn [ShortFixedBaseMul.y_a] in HA3.
    pose proof (short_fixed_base_mul_sign_square Γ region 1 Hsel' Hgate)
      as Hsq.
    (* Component equalities. *)
    assert (Hx :
        UnOp.from
          (eval_cell Γ (Garden.Halo2.Synthesis.Cell.advice region Advice.A2 1)) =
        Point.x
          (EccSpec.point_add
            (Field.map_mod (assigned_point_value Γ mul_b))
            (Field.map_mod (assigned_point_value Γ acc)))).
    { exact (f_equal Point.x Hadd). }
    assert (Hy_add :
        UnOp.from
          (eval_cell Γ (Garden.Halo2.Synthesis.Cell.advice region Advice.A3 1)) =
        Point.y
          (EccSpec.point_add
            (Field.map_mod (assigned_point_value Γ mul_b))
            (Field.map_mod (assigned_point_value Γ acc)))).
    { exact (f_equal Point.y Hadd). }
    assert (Hy :
        UnOp.from
          (eval_cell Γ (Garden.Halo2.Synthesis.Cell.advice region Advice.A1 1)) =
        UnOp.from (eval_cell Γ sign) *F
        Point.y
          (EccSpec.point_add
            (Field.map_mod (assigned_point_value Γ mul_b))
            (Field.map_mod (assigned_point_value Γ acc)))).
    { rewrite <- Hcopy_sign.
      rewrite <- (eval_advice_cur_cell Γ region Advice.A4 1).
      rewrite <- Hy_add.
      rewrite <- (eval_advice_cur_cell Γ region Advice.A3 1).
      rewrite HA3.
      rewrite <- field_mul_assoc.
      rewrite Hsq.
      rewrite FieldRewrite.mul_one_left.
      rewrite (eval_advice_cur_cell Γ region Advice.A1 1).
      rewrite from_idem.
      reflexivity. }
    unfold Garden.Orchard.circuit.synthesize_short_fixed_base_mul_msb_region.
    cbn [layouter_value region_value Monad.bind Monad.ret
      Garden.Halo2.Synthesis.RegionIsMonad
      Garden.Orchard.circuit.assign_complete_add
      assigned_point_value
      Garden.Orchard.circuit.AssignedPoint.x
      Garden.Orchard.circuit.AssignedPoint.y
      Field.map_mod Point.IsMapMod Point.x Point.y].
    rewrite Hx, Hy.
    reflexivity.
  Qed.

  (** Whole-program structure of the short fixed-base multiplication: the
      complete addition of window 21 into the fold of windows 0..20, with the
      sign applied to the ordinate. *)
  Lemma synthesize_short_fixed_base_mul_correct
      (Γ : Assignment.t columns RegionId.t)
      (magnitude sign : Garden.Halo2.Synthesis.Cell.t columns RegionId.t)
      (Hfacts :
        interpret_facts Γ
          (layouter_facts
            (Garden.Orchard.circuit.synthesize_short_fixed_base_mul
              magnitude sign)))
      (Hgates :
        satisfies_gates Γ
          (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty))
      (Hpre :
        incomplete_additions_precondition Γ
          (RegionId.ValueCommitment
            RegionId.ValueCommitment.ValueCommitVIncomplete) 1 20
          (incomplete_additions_window_point Γ
            (RegionId.ValueCommitment
              RegionId.ValueCommitment.ValueCommitVIncomplete) 0)) :
    Field.map_mod
      (assigned_point_value Γ
        (layouter_value
          (Garden.Orchard.circuit.synthesize_short_fixed_base_mul
            magnitude sign))) =
      {|
        Point.x :=
          Point.x
            (EccSpec.point_add
              (incomplete_additions_window_point Γ
                (RegionId.ValueCommitment
                  RegionId.ValueCommitment.ValueCommitVIncomplete) 21)
              (incomplete_additions_output Γ
                (RegionId.ValueCommitment
                  RegionId.ValueCommitment.ValueCommitVIncomplete) 1 20
                (incomplete_additions_window_point Γ
                  (RegionId.ValueCommitment
                    RegionId.ValueCommitment.ValueCommitVIncomplete) 0)));
        Point.y :=
          UnOp.from (eval_cell Γ sign) *F
          Point.y
            (EccSpec.point_add
              (incomplete_additions_window_point Γ
                (RegionId.ValueCommitment
                  RegionId.ValueCommitment.ValueCommitVIncomplete) 21)
              (incomplete_additions_output Γ
                (RegionId.ValueCommitment
                  RegionId.ValueCommitment.ValueCommitVIncomplete) 1 20
                (incomplete_additions_window_point Γ
                  (RegionId.ValueCommitment
                    RegionId.ValueCommitment.ValueCommitVIncomplete) 0)));
      |}.
  Proof.
    unfold Garden.Orchard.circuit.synthesize_short_fixed_base_mul in Hfacts.
    pose (incomplete :=
      Garden.Orchard.circuit.synth_short_mul_incomplete
        (Garden.Orchard.circuit.value_commitment_region
          RegionId.ValueCommitment.ValueCommitVIncomplete)
        magnitude).
    pose (program :=
      let🞵 result := incomplete in
      Garden.Orchard.circuit.synthesize_short_fixed_base_mul_msb_region
        (Garden.Orchard.circuit.value_commitment_region
          RegionId.ValueCommitment.ValueCommitVMsb)
        sign
        result.(Garden.Orchard.circuit.ShortFixedResult.last_window)
        result.(Garden.Orchard.circuit.ShortFixedResult.acc)
        result.(Garden.Orchard.circuit.ShortFixedResult.mul_b)).
    assert (Hincomplete_facts : interpret_facts Γ (layouter_facts incomplete)).
    { subst program incomplete.
      apply interpret_layouter_facts_bind_left in Hfacts.
      exact Hfacts. }
    assert (Hmsb_facts :
        interpret_facts Γ
          (layouter_facts
            (Garden.Orchard.circuit.synthesize_short_fixed_base_mul_msb_region
              (Garden.Orchard.circuit.value_commitment_region
                RegionId.ValueCommitment.ValueCommitVMsb)
              sign
              (layouter_value incomplete)
                .(Garden.Orchard.circuit.ShortFixedResult.last_window)
              (layouter_value incomplete)
                .(Garden.Orchard.circuit.ShortFixedResult.acc)
              (layouter_value incomplete)
                .(Garden.Orchard.circuit.ShortFixedResult.mul_b)))).
    { subst program.
      apply interpret_layouter_facts_bind_right in Hfacts.
      exact Hfacts. }
    change (Field.map_mod
      (assigned_point_value Γ (layouter_value program)) =
      {|
        Point.x :=
          Point.x
            (EccSpec.point_add
              (incomplete_additions_window_point Γ
                (RegionId.ValueCommitment
                  RegionId.ValueCommitment.ValueCommitVIncomplete) 21)
              (incomplete_additions_output Γ
                (RegionId.ValueCommitment
                  RegionId.ValueCommitment.ValueCommitVIncomplete) 1 20
                (incomplete_additions_window_point Γ
                  (RegionId.ValueCommitment
                    RegionId.ValueCommitment.ValueCommitVIncomplete) 0)));
        Point.y :=
          UnOp.from (eval_cell Γ sign) *F
          Point.y
            (EccSpec.point_add
              (incomplete_additions_window_point Γ
                (RegionId.ValueCommitment
                  RegionId.ValueCommitment.ValueCommitVIncomplete) 21)
              (incomplete_additions_output Γ
                (RegionId.ValueCommitment
                  RegionId.ValueCommitment.ValueCommitVIncomplete) 1 20
                (incomplete_additions_window_point Γ
                  (RegionId.ValueCommitment
                    RegionId.ValueCommitment.ValueCommitVIncomplete) 0)));
      |}).
    subst program.
    cbn [layouter_value Monad.bind Garden.Halo2.Synthesis.LayouterIsMonad].
    rewrite (short_msb_region_output_correct Γ
      (Garden.Orchard.circuit.value_commitment_region
        RegionId.ValueCommitment.ValueCommitVMsb)
      sign
      (layouter_value incomplete)
        .(Garden.Orchard.circuit.ShortFixedResult.last_window)
      (layouter_value incomplete)
        .(Garden.Orchard.circuit.ShortFixedResult.acc)
      (layouter_value incomplete)
        .(Garden.Orchard.circuit.ShortFixedResult.mul_b)
      Hmsb_facts Hgates).
    subst incomplete.
    rewrite (short_incomplete_region_mul_b_correct Γ
      (Garden.Orchard.circuit.value_commitment_region
        RegionId.ValueCommitment.ValueCommitVIncomplete)
      magnitude).
    rewrite (short_incomplete_region_acc_correct Γ
      (Garden.Orchard.circuit.value_commitment_region
        RegionId.ValueCommitment.ValueCommitVIncomplete)
      magnitude Hincomplete_facts Hgates Hpre).
    reflexivity.
  Qed.

  (** Final short wrapper: with a window-correctness hypothesis over the
      22-entry table split [first :: middle ++ [last]] and the circuit
      precondition, the program output is the specification's
      [fixed_scalar_mul], with the sign applied to the ordinate. *)
  Lemma short_scalar_mul_correct
      (Γ : Assignment.t columns RegionId.t)
      (magnitude sign : Garden.Halo2.Synthesis.Cell.t columns RegionId.t)
      (first last : EccSpec.fixed_window) (middle : EccSpec.fixed_table)
      (k : Z) (us : list Z)
      (Hfacts :
        interpret_facts Γ
          (layouter_facts
            (Garden.Orchard.circuit.synthesize_short_fixed_base_mul
              magnitude sign)))
      (Hgates :
        satisfies_gates Γ
          (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty))
      (Hpre :
        incomplete_additions_precondition Γ
          (RegionId.ValueCommitment
            RegionId.ValueCommitment.ValueCommitVIncomplete) 1 20
          (incomplete_additions_window_point Γ
            (RegionId.ValueCommitment
              RegionId.ValueCommitment.ValueCommitVIncomplete) 0))
      (Hmiddle_len : List.length middle = 20%nat)
      (Hwindow :
        forall (j : nat) (w : EccSpec.fixed_window),
          List.nth_error (first :: middle ++ [last]) j = Some w ->
          incomplete_additions_window_point Γ
            (RegionId.ValueCommitment
              RegionId.ValueCommitment.ValueCommitVIncomplete) (Z.of_nat j) =
          EccSpec.fixed_window_point w
            (EccSpec.window_digit k j)
            (List.nth j us 0))
      (Hcircuit_pre :
        fixed_scalar_mul_circuit_precondition (first :: middle ++ [last]) k us) :
    Field.map_mod
      (assigned_point_value Γ
        (layouter_value
          (Garden.Orchard.circuit.synthesize_short_fixed_base_mul
            magnitude sign))) =
      {|
        Point.x :=
          Point.x (EccSpec.fixed_scalar_mul (first :: middle ++ [last]) k us);
        Point.y :=
          UnOp.from (eval_cell Γ sign) *F
          Point.y (EccSpec.fixed_scalar_mul (first :: middle ++ [last]) k us);
      |}.
  Proof.
    rewrite (synthesize_short_fixed_base_mul_correct Γ magnitude sign
      Hfacts Hgates Hpre).
    assert (HT :
      EccSpec.point_add
        (incomplete_additions_window_point Γ
          (RegionId.ValueCommitment
            RegionId.ValueCommitment.ValueCommitVIncomplete) 21)
        (incomplete_additions_output Γ
          (RegionId.ValueCommitment
            RegionId.ValueCommitment.ValueCommitVIncomplete) 1 20
          (incomplete_additions_window_point Γ
            (RegionId.ValueCommitment
              RegionId.ValueCommitment.ValueCommitVIncomplete) 0)) =
      EccSpec.fixed_scalar_mul (first :: middle ++ [last]) k us).
    { assert (Hfirst :
          incomplete_additions_window_point Γ
            (RegionId.ValueCommitment
              RegionId.ValueCommitment.ValueCommitVIncomplete) 0 =
          EccSpec.fixed_window_point first
            (EccSpec.window_digit k 0%nat)
            (List.nth 0%nat us 0)).
      { exact (Hwindow 0%nat first eq_refl). }
      assert (Hlast :
          incomplete_additions_window_point Γ
            (RegionId.ValueCommitment
              RegionId.ValueCommitment.ValueCommitVIncomplete) 21 =
          EccSpec.fixed_window_point last
            (EccSpec.window_digit k 21%nat)
            (List.nth 21%nat us 0)).
      { replace 21 with (Z.of_nat (S (List.length middle))) by
          (rewrite Hmiddle_len; reflexivity).
        replace 21%nat with (S (List.length middle)) by
          (rewrite Hmiddle_len; reflexivity).
        apply Hwindow.
        cbn [List.nth_error].
        rewrite nth_error_app2 by lia.
        rewrite Nat.sub_diag.
        reflexivity. }
      rewrite Hlast.
      rewrite <- Hmiddle_len.
      rewrite (incomplete_output_scalar_mul_incomplete_tail Γ
        (RegionId.ValueCommitment
          RegionId.ValueCommitment.ValueCommitVIncomplete) 1 middle k us 1%nat
        (incomplete_additions_window_point Γ
          (RegionId.ValueCommitment
            RegionId.ValueCommitment.ValueCommitVIncomplete) 0)).
      - rewrite Hfirst.
        (* [rewrite <- Hmiddle_len] also rewrites inside the unary numeral
           [21 = S 20], so the most significant index now reads
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
          discriminate. }
    rewrite HT.
    reflexivity.
  Qed.

End ShortFixedBaseStructure.
