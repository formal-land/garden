(** * Typed input: the value_commit_v magnitude is a 64-bit value, from
      [Holds] alone

    The sharpened magnitude bound: [in_magnitude] — [read9] of the
    [MagnitudeRangeCheck] free-witness cell — lies in [0, 2^64), refining the
    [0, 8^22) bound of [circuit_proof/typed_inputs/magnitude.v].

    Route.  The Orchard circuit pinned by the synthesis snapshot does not
    range-check the magnitude through the 10-bit lookup table: the "v_net"
    namespace synthesizes no regions (its [ScalarFixedShort] wraps the
    (magnitude, sign) pair without a lookup), so the snapshot has no
    range-check region between the "load private" rows and the short
    fixed-base mul.  The 64-bit bound is instead enforced by the short
    fixed-base multiplication itself:

    - the strict 22-window running sum of [ValueCommitVIncomplete] pins
      [A4[0]] to the magnitude cell ([value_commit_v_initial_z]), bounds each
      word [z_i - 8·z_{i+1}] in [0, 8)
      ([short_incomplete_region_word_range]), and pins the tail [A4[22]] to
      zero ([value_commit_v_z_boundary_of_holds]);
    - the MSB region copies the last running-sum entry [z_21 = A4[21]] onto
      [A5] of the [QMulFixedShort] row, where the gate's "last_window_check"
      constrains it Boolean ([last_window_boolean] below) — mirroring
      [mul_fixed/short.rs], where this constraint is exactly what tightens
      the strict 66-bit decomposition to 64 bits.

    The integer reconstruction ([running_sum_boolean_top_head_bound] below)
    telescopes the 21 low windows under the Boolean top entry:
    [magnitude = Σ_{i<21} w_i·8^i + 8^21·z_21 ≤ (8^21 - 1) + 8^21 < 2^64].

    Every ingredient is derived from [Holds]; no model-gap hypothesis is
    involved.  In particular the short-lookup selector-plane gap (the
    [q_running = 0] rows behind the named honesty hypotheses of the
    note-commit word decompositions) is not touched: the magnitude bound
    never consumes a lookup argument. *)

Require Import Garden.Halo2.main.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.lemmas.
Require Import Garden.Orchard.columns.
Require Garden.Orchard.circuit.
Require Garden.Halo2.halo2_gadgets.ecc.chip.mul_fixed.short.
Require Import Garden.Orchard.protocol_spec.
Require Import Garden.Orchard.circuit_proof.inputs.
Require Import Garden.Orchard.circuit_proof.facts.
Require Import Garden.Orchard.circuit_proof.fixed_base.main.
Require Import Garden.Orchard.circuit_proof.value_commit_v.out.
Require Import Garden.Field.Field.
Require Import Garden.Field.Sqrt.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.fixed_window_canonical.
Require Import Garden.Plonky3.M.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Lists.List.
Require Import Stdlib.micromega.Lia.

Import ListNotations.

#[local] Existing Instance Primes.PallasPIsPrime.

Global Open Scope Z_scope.


Module TypedInputsMagnitude64.
  Import OrchardActionFixedBase.

  (* The consumed short-mul facts sit in files whose types mention
     [is_square]/[field_sqrt]/[fixed_window_point_canonical]; keep the chain
     opaque to the conversion oracle ([docs/compile-performance.md]). *)
  Strategy opaque
    [is_square modpow modpow_pos field_sqrt fixed_window_point_canonical].

  Local Notation Holds Γ :=
    (circuit_holds Γ
      Garden.Orchard.circuit.synthesize
      (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)).

  (** The "last_window_check" constraint of [short_fixed_base_mul_gate],
      landed on the last running-sum entry: the MSB region of the short
      fixed-base multiplication copies [A4[21]] of [ValueCommitVIncomplete]
      onto [A5] of the [QMulFixedShort] row, where the gate constrains it to
      be Boolean. *)
  Lemma last_window_boolean
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    Γ ⊢ ⟦ Expression.Advice Advice.A4 Rotation.cur ⟧
      (RegionId.ValueCommitment
        RegionId.ValueCommitment.ValueCommitVIncomplete, 21) = 0 \/
    Γ ⊢ ⟦ Expression.Advice Advice.A4 Rotation.cur ⟧
      (RegionId.ValueCommitment
        RegionId.ValueCommitment.ValueCommitVIncomplete, 21) = 1.
  Proof.
    pose proof
      (ValueCommitVOut.value_commit_v_short_mul_facts Γ Hcircuit) as Hfacts.
    unfold Garden.Orchard.circuit.synthesize_short_fixed_base_mul in Hfacts.
    apply interpret_layouter_facts_bind_right in Hfacts.
    unfold Garden.Orchard.circuit
      .synthesize_short_fixed_base_mul_msb_region in Hfacts.
    apply interpret_layouter_facts_add_region in Hfacts.
    (* The last-window copy: A5 at row 1 of the MSB region holds the value of
       A4[21] of the incomplete region. *)
    pose proof Hfacts as Hcopy_lw.
    do 2 apply interpret_region_facts_bind_right in Hcopy_lw.
    apply interpret_region_facts_bind_left in Hcopy_lw.
    cbn [region_facts interpret_facts interpret_fact] in Hcopy_lw.
    destruct Hcopy_lw as [Hcopy_lw _].
    replace
        ((layouter_value
           (Garden.Orchard.circuit.synth_short_mul_incomplete
              (Garden.Orchard.circuit.value_commitment_region
                 RegionId.ValueCommitment.ValueCommitVIncomplete)
              (layouter_value
                 (Garden.Orchard.circuit.assign_free_advice
                    (Garden.Orchard.circuit.value_commitment_region
                       RegionId.ValueCommitment.MagnitudeRangeCheck)
                    "v_net magnitude" Advice.A9 0))))
          .(Garden.Orchard.circuit.ShortFixedResult.last_window))
      with
        (Garden.Halo2.Synthesis.Cell.advice
          (Garden.Orchard.circuit.value_commitment_region
            RegionId.ValueCommitment.ValueCommitVIncomplete)
          Advice.A4 21)
      in Hcopy_lw by (vm_compute; reflexivity).
    (* The [QMulFixedShort] selector is enabled at row 1. *)
    pose proof Hfacts as Hsel.
    do 3 apply interpret_region_facts_bind_right in Hsel.
    apply interpret_region_facts_bind_left in Hsel.
    cbn [region_facts interpret_facts interpret_fact] in Hsel.
    destruct Hsel as [Hsel _].
    pose proof (enabled_nonzero Γ Selector.QMulFixedShort
      (Garden.Orchard.circuit.value_commitment_region
        RegionId.ValueCommitment.ValueCommitVMsb) 1 Hsel) as Hselector.
    pose proof (satisfies_gates_at Γ
      (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)
      Garden.Halo2.halo2_gadgets.ecc.chip.mul_fixed.short
        .short_fixed_base_mul_gate
      (Garden.Orchard.circuit.value_commitment_region
        RegionId.ValueCommitment.ValueCommitVMsb) 1
      ltac:(cbn; repeat (first [left; reflexivity | right]))
      (holds_gates Γ Hcircuit)) as Hgate.
    with_strategy opaque [BinOp.add BinOp.mul BinOp.sub UnOp.from] cbn
      in Hgate.
    destruct Hgate as (h1 & _).
    specialize (h1 Hselector).
    cbn in Hcopy_lw.
    rewrite eval_advice_cur_cell.
    cbn [eval_cell Garden.Halo2.Synthesis.Cell.advice
      Garden.Halo2.Synthesis.Cell.column Garden.Halo2.Synthesis.Cell.region
      Garden.Halo2.Synthesis.Cell.row_offset].
    unfold Garden.Orchard.circuit.value_commitment_region in Hcopy_lw, h1.
    rewrite <- Hcopy_lw.
    (* [h1] is the reduced-form Boolean fact [x = Z.b2z (Z.odd x)]; the
       conversion-level application keeps the primitive-projection
       representations aligned. *)
    assert (Hcase : forall x : Z, x = Z.b2z (Z.odd x) -> x = 0 \/ x = 1).
    { intros x Hx. rewrite Hx. destruct (Z.odd x); [right | left];
        reflexivity. }
    exact (Hcase _ h1).
  Qed.

  (** Integer head bound of a running-sum chain with a Boolean top entry:
      reduced entries [zs] whose 21 low words lie in [0, 8) satisfy
      [zs 0 < 8^21·(zs 21 + 1)] over the integers — with [zs 21 ≤ 1] this is
      the 64-bit bound [zs 0 < 2·8^21 = 2^64]. *)
  Lemma running_sum_boolean_top_head_bound
      (zs : nat -> Z)
      (Hreduced :
        forall i : nat, (i <= 21)%nat -> 0 <= zs i < Primes.pallas_p)
      (Hwords :
        forall i : nat,
          (i < 21)%nat ->
          0 <=
            zs i -F
              zs (S i) *F
              UnOp.from Garden.Halo2.halo2_gadgets.ecc.chip.constants.h <
            8)
      (Htop : 0 <= zs 21%nat <= 1) :
    forall r j : nat,
      (j + r)%nat = 21%nat ->
      0 <= zs j < 8 ^ Z.of_nat r * (zs 21%nat + 1).
  Proof.
    induction r as [| r IH]; intros j Hj.
    - assert (Hj21 : j = 21%nat) by lia.
      subst j.
      cbn.
      clear -Htop.
      replace (match zs 21%nat + 1 with
               | 0 => 0
               | Z.pos y' => Z.pos y'
               | Z.neg y' => Z.neg y'
               end) with (zs 21%nat + 1)
        by (destruct (zs 21%nat + 1); reflexivity).
      lia.
    - (* [Primes.pallas_p] stays folded throughout: the [-F]/[*F] atoms carry
         it as an implicit argument, and unfolding it in place would split
         those atoms apart for [lia]. *)
      assert (HP : Primes.pallas_p =
          28948022309329048855892746252171976963363056481941560715954676764349967630337)
        by (vm_compute; reflexivity).
      assert (HSj : (S j + r)%nat = 21%nat) by lia.
      destruct (IH (S j) HSj) as [IH0 IH1].
      pose proof (Hwords j ltac:(lia)) as Hw.
      rewrite from_h_eq_8 in Hw.
      assert (Hpow_nonneg : 0 <= 8 ^ Z.of_nat r)
        by (apply Z.pow_nonneg; lia).
      assert (Hpow20 : 8 ^ Z.of_nat r <= 8 ^ 20).
      { apply Z.pow_le_mono_r; lia. }
      assert (H820 : 8 ^ 20 = 1152921504606846976) by reflexivity.
      assert (Hb2 : zs (S j) < 2 * 8 ^ Z.of_nat r).
      { apply Z.lt_le_trans with (8 ^ Z.of_nat r * (zs 21%nat + 1));
          [exact IH1 |].
        replace (2 * 8 ^ Z.of_nat r) with (8 ^ Z.of_nat r * 2) by ring.
        apply Z.mul_le_mono_nonneg_l;
          [exact Hpow_nonneg | clear -Htop; lia]. }
      assert (Hstep : zs j = (zs j -F zs (S j) *F 8) + 8 * zs (S j)).
      { apply (running_sum_word_step Primes.pallas_p).
        - clear -HP; lia.
        - unfold BinOp.sub, BinOp.mul; reflexivity.
        - apply Hreduced; lia.
        - exact IH0.
        - clear -HP Hw Hb2 Hpow20 H820 IH0.
          lia. }
      assert (Hpow_succ : 8 ^ Z.of_nat (S r) = 8 * 8 ^ Z.of_nat r).
      { rewrite Nat2Z.inj_succ, Z.pow_succ_r; lia. }
      rewrite Hpow_succ.
      set (E := 8 ^ Z.of_nat r) in *.
      set (Q := E * (zs 21%nat + 1)) in *.
      replace (8 * E * (zs 21%nat + 1)) with (8 * Q) by (subst Q; ring).
      rewrite Hstep.
      clear -Hw IH0 IH1.
      lia.
  Qed.

  (** The magnitude cell — [read9] of [MagnitudeRangeCheck], the source of
      [in_magnitude] — lies in [0, 2^64). *)
  Lemma magnitude_range_check_range_64
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    0 <=
      read9 Γ
        (RegionId.ValueCommitment
          RegionId.ValueCommitment.MagnitudeRangeCheck) <
      2 ^ 64.
  Proof.
    rewrite <- (value_commit_v_initial_z Γ Hcircuit).
    pose proof (value_commit_v_incomplete_facts Γ Hcircuit) as Hfacts.
    pose proof (holds_gates Γ Hcircuit) as Hgates.
    set (zs := fun n : nat =>
      Γ ⊢ ⟦ Expression.Advice Advice.A4 Rotation.cur ⟧
        (RegionId.ValueCommitment
          RegionId.ValueCommitment.ValueCommitVIncomplete,
          Z.of_nat n)).
    assert (Hreduced :
      forall i : nat, (i <= 21)%nat -> 0 <= zs i < Primes.pallas_p).
    { intros i _. apply eval_advice_cur_bounds. }
    assert (Hwords :
      forall i : nat,
        (i < 21)%nat ->
        0 <=
          zs i -F
            zs (S i) *F
            UnOp.from Garden.Halo2.halo2_gadgets.ecc.chip.constants.h <
          8).
    { intros i Hi.
      pose proof
        (short_incomplete_region_word_range Γ
          (RegionId.ValueCommitment
            RegionId.ValueCommitment.ValueCommitVIncomplete)
          (Garden.Halo2.Synthesis.Cell.advice
            (Garden.Orchard.circuit.value_commitment_region
              RegionId.ValueCommitment.MagnitudeRangeCheck)
            Advice.A9 0)
          i Hfacts Hgates ltac:(lia)) as Hword.
      rewrite (eval_advice_next_succ Γ Advice.A4
        (RegionId.ValueCommitment
          RegionId.ValueCommitment.ValueCommitVIncomplete) i) in Hword.
      exact Hword. }
    assert (Htop : 0 <= zs 21%nat <= 1).
    { destruct (last_window_boolean Γ Hcircuit) as [H0 | H1].
      - change (zs 21%nat) with
          (Γ ⊢ ⟦ Expression.Advice Advice.A4 Rotation.cur ⟧
            (RegionId.ValueCommitment
              RegionId.ValueCommitment.ValueCommitVIncomplete, Z.of_nat 21)).
        replace (Z.of_nat 21) with 21 by reflexivity.
        lia.
      - change (zs 21%nat) with
          (Γ ⊢ ⟦ Expression.Advice Advice.A4 Rotation.cur ⟧
            (RegionId.ValueCommitment
              RegionId.ValueCommitment.ValueCommitVIncomplete, Z.of_nat 21)).
        replace (Z.of_nat 21) with 21 by reflexivity.
        lia. }
    destruct
      (running_sum_boolean_top_head_bound zs Hreduced Hwords Htop
        21%nat 0%nat eq_refl) as [Hlo Hhi].
    split.
    - exact Hlo.
    - apply Z.lt_le_trans with (8 ^ Z.of_nat 21 * (zs 21%nat + 1));
        [exact Hhi |].
      assert (H821 : 8 ^ Z.of_nat 21 = 9223372036854775808) by reflexivity.
      assert (H264 : 2 ^ 64 = 18446744073709551616) by reflexivity.
      clear -Htop H821 H264.
      nia.
  Qed.

  (** The 64-bit magnitude bound at the [read_action_inputs] spelling
      consumed by the theorem surface ([circuit_proof/main.v]). *)
  Lemma in_magnitude_range_64
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    0 <=
      OrchardSpec.in_magnitude (OrchardActionInputs.read_action_inputs Γ) <
      2 ^ 64.
  Proof.
    exact (magnitude_range_check_range_64 Γ Hcircuit).
  Qed.

End TypedInputsMagnitude64.
