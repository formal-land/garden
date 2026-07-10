(** * Variable-base scalar multiplication: circuit side of the overflow argument

    Proof of the [VarBaseMul.overflow_scalar_exact] statement against the
    shared surface of [circuit_proof/ownership/var_base_defs.v]: from
    [Holds Γ] and the LSB-phase outputs, the recovered 255-bit running sum
    equals [α + t_q] over the integers.

    Structure:
    - facts extractors for the three overflow regions of the
      address-integrity mul block ([Mul.OverflowS] / [OverflowLookup] /
      [OverflowCheck]) — the copies pinning the [overflow_checks_gate] cells
      to the running-sum probes [z_136]/[z_126]/[z_2], the scalar cell [α],
      the lookup tail [z_13] and the [s] witness;
    - the ten-bit range of each [OverflowLookup] running-sum word, through
      the shared [TableIdx] range-check lookup argument
      ([RangeTable.word_sound], [utilities/lookup_range_check_proof.v]) at
      the generator-table load ([GeneratorTable.loaded] — the index column
      of [load_generator_table] is the range table);
    - the pure reconstruction [running_sum_zero_bound]: a running sum of
      ten-bit words whose tail is zero reconstructs over the integers, so
      the [s] head cell is bounded by [2^130];
    - the assembly [overflow_scalar_exact]: [OverflowChecks.deterministic]
      (the [s_check]/[recovery] constraints) plus the three raw [Either]
      constraints ([lo_zero], [s_minus_lo_130_check], [canonicity])
      discharge the hypotheses of the pure core
      [VarBaseDefs.overflow_no_wrap]. *)

Require Import Garden.Orchard.circuit_proof.ownership.var_base_defs.
Require Garden.Halo2.halo2_gadgets.ecc.chip.mul.
Require Garden.Halo2.halo2_gadgets.ecc.chip.mul.overflow.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.mul.overflow_proof.
Require Import Garden.Halo2.halo2_gadgets.utilities.lookup_range_check_proof.
Require Garden.Halo2.halo2_gadgets.sinsemilla.chip_proof.
Require Garden.Orchard.circuit_proof.merkle.

#[local] Existing Instance Primes.PallasPIsPrime.

Global Open Scope Z_scope.

Module VarBaseOverflow.
  Import OrchardActionFacts.

  Local Notation Holds Γ :=
    (circuit_holds Γ
      Garden.Orchard.circuit.synthesize
      (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)).

  Notation mul_region := VarBaseDefs.mul_region.
  Notation overflow_s_region := VarBaseDefs.overflow_s_region.
  Notation overflow_lookup_region := VarBaseDefs.overflow_lookup_region.
  Notation overflow_check_region := VarBaseDefs.overflow_check_region.
  Notation ivk_add_region := VarBaseDefs.ivk_add_region.
  Notation alpha_cell := VarBaseDefs.alpha_cell.
  Notation av := VarBaseDefs.av.
  Notation alpha_value := VarBaseDefs.alpha_value.
  Notation lsb_bit := VarBaseDefs.lsb_bit.
  Notation recovered_scalar := VarBaseDefs.recovered_scalar.
  Notation overflow_no_wrap := VarBaseDefs.overflow_no_wrap.

  (** ** Facts extractors: the overflow block of the address-integrity mul

      [synthesize_overflow_check] is the second bind of [mul.synthesize]
      ([ecc/chip/mul.v]); its source cells are the ones the variable-base
      region program returns ([MulResult.overflow_sources]). *)
  Lemma overflow_block_facts
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    interpret_facts Γ
      (layouter_facts
        (Garden.Halo2.halo2_gadgets.ecc.chip.mul.synthesize_overflow_check
          overflow_s_region overflow_lookup_region overflow_check_region
          {|
            Garden.Halo2.halo2_gadgets.ecc.chip.mul.OverflowSources.alpha :=
              alpha_cell;
            Garden.Halo2.halo2_gadgets.ecc.chip.mul.OverflowSources.z_2 :=
              Cell.advice mul_region Advice.A9 2;
            Garden.Halo2.halo2_gadgets.ecc.chip.mul.OverflowSources.z_126 :=
              Cell.advice mul_region Advice.A9 126;
            Garden.Halo2.halo2_gadgets.ecc.chip.mul.OverflowSources.z_136 :=
              Cell.advice mul_region Advice.A9 136;
          |})).
  Proof.
    pose proof (holds_facts Γ Hcircuit) as Hfacts.
    unfold Garden.Orchard.circuit.synthesize in Hfacts.
    do 7 apply interpret_layouter_facts_bind_right in Hfacts.
    apply interpret_layouter_facts_bind_left in Hfacts.
    unfold Garden.Orchard.circuit.synthesize_address_integrity in Hfacts.
    do 3 apply interpret_layouter_facts_bind_right in Hfacts.
    apply interpret_layouter_facts_bind_left in Hfacts.
    apply interpret_layouter_facts_in_namespace in Hfacts.
    unfold Garden.Halo2.halo2_gadgets.ecc.chip.mul.synthesize in Hfacts.
    apply interpret_layouter_facts_in_namespace in Hfacts.
    apply interpret_layouter_facts_bind_right in Hfacts.
    apply interpret_layouter_facts_bind_left in Hfacts.
    exact Hfacts.
  Qed.

  (** The [OverflowCheck] region: the [QMulOverflow] selector at offset 1 and
      the six copies feeding the gate cells. *)
  Lemma overflow_check_region_facts
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    Γ.(Assignment.selector) Selector.QMulOverflow overflow_check_region 1 =
      1 /\
    eval_cell Γ (Cell.advice overflow_check_region Advice.A6 0) =
      eval_cell Γ (Cell.advice mul_region Advice.A9 136) /\
    eval_cell Γ (Cell.advice overflow_check_region Advice.A6 1) =
      eval_cell Γ (Cell.advice mul_region Advice.A9 126) /\
    eval_cell Γ (Cell.advice overflow_check_region Advice.A7 0) =
      eval_cell Γ (Cell.advice mul_region Advice.A9 2) /\
    eval_cell Γ (Cell.advice overflow_check_region Advice.A7 1) =
      eval_cell Γ alpha_cell /\
    eval_cell Γ (Cell.advice overflow_check_region Advice.A7 2) =
      eval_cell Γ (Cell.advice overflow_lookup_region Advice.A9 13) /\
    eval_cell Γ (Cell.advice overflow_check_region Advice.A8 1) =
      eval_cell Γ (Cell.advice overflow_s_region Advice.A6 0).
  Proof.
    pose proof (overflow_block_facts Γ Hcircuit) as Hfacts.
    unfold Garden.Halo2.halo2_gadgets.ecc.chip.mul.synthesize_overflow_check
      in Hfacts.
    apply interpret_layouter_facts_in_namespace in Hfacts.
    do 2 apply interpret_layouter_facts_bind_right in Hfacts.
    apply interpret_layouter_facts_add_region in Hfacts.
    cbn [Monad.bind Garden.Halo2.Synthesis.RegionIsMonad
      Garden.Halo2.Synthesis.LayouterIsMonad
      Garden.Halo2.halo2_gadgets.ecc.chip.mul
        .synthesize_running_sum_decomposition
      Garden.Halo2.halo2_gadgets.ecc.chip.mul.OverflowSources.alpha
      Garden.Halo2.halo2_gadgets.ecc.chip.mul.OverflowSources.z_2
      Garden.Halo2.halo2_gadgets.ecc.chip.mul.OverflowSources.z_126
      Garden.Halo2.halo2_gadgets.ecc.chip.mul.OverflowSources.z_136
      region_facts region_value layouter_value
      List.app interpret_facts interpret_fact] in Hfacts.
    tauto.
  Qed.

  (** The [OverflowLookup] region: the [s] head copy and the 13 lookup rows'
      selector facts. *)
  Lemma overflow_lookup_region_facts
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    eval_cell Γ (Cell.advice overflow_lookup_region Advice.A9 0) =
      eval_cell Γ (Cell.advice overflow_s_region Advice.A6 0) /\
    interpret_facts Γ
      (region_facts overflow_lookup_region
        (Garden.Halo2.halo2_gadgets.ecc.chip.mul.enable_lookup_running_rows
          0 13)).
  Proof.
    pose proof (overflow_block_facts Γ Hcircuit) as Hfacts.
    unfold Garden.Halo2.halo2_gadgets.ecc.chip.mul.synthesize_overflow_check
      in Hfacts.
    apply interpret_layouter_facts_in_namespace in Hfacts.
    apply interpret_layouter_facts_bind_right in Hfacts.
    apply interpret_layouter_facts_bind_left in Hfacts.
    unfold Garden.Halo2.halo2_gadgets.ecc.chip.mul
      .synthesize_running_sum_decomposition in Hfacts.
    do 2 apply interpret_layouter_facts_in_namespace in Hfacts.
    apply interpret_layouter_facts_add_region in Hfacts.
    split.
    - apply interpret_region_facts_bind_left in Hfacts.
      cbn [region_facts region_value layouter_value
        interpret_facts interpret_fact] in Hfacts.
      tauto.
    - apply interpret_region_facts_bind_right in Hfacts.
      apply interpret_region_facts_bind_left in Hfacts.
      exact Hfacts.
  Qed.

  (** Both range-check selectors are enabled at rows [offset .. offset+count)
      by the chip's [enable_lookup_running_rows] ([ecc/chip/mul.v]). *)
  Lemma enable_lookup_running_rows_selector_fact
      (region : RegionId.t) (offset : Z) (count i : nat) :
    (i < count)%nat ->
    List.In
      (Fact.SelectorOn Selector.QLookup region (offset + Z.of_nat i))
      (region_facts region
        (Garden.Halo2.halo2_gadgets.ecc.chip.mul.enable_lookup_running_rows
          offset count)) /\
    List.In
      (Fact.SelectorOn Selector.QRunning region (offset + Z.of_nat i))
      (region_facts region
        (Garden.Halo2.halo2_gadgets.ecc.chip.mul.enable_lookup_running_rows
          offset count)).
  Proof.
    revert offset i.
    induction count as [| count IH]; intros offset i Hi.
    - lia.
    - destruct i as [| i].
      + cbn [Garden.Halo2.halo2_gadgets.ecc.chip.mul.enable_lookup_running_rows
          region_facts List.app].
        split.
        * left. f_equal. lia.
        * right. left. f_equal. lia.
      + cbn [Garden.Halo2.halo2_gadgets.ecc.chip.mul.enable_lookup_running_rows
          region_facts List.app].
        destruct (IH (offset + 1) i ltac:(lia)) as [H1 H2].
        replace (offset + Z.of_nat (S i)) with (offset + 1 + Z.of_nat i)
          by lia.
        split; right; right; assumption.
  Qed.

  Lemma overflow_lookup_selectors_on
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (j : nat) (Hj : (j < 13)%nat) :
    Γ.(Assignment.selector) Selector.QLookup
      overflow_lookup_region (Z.of_nat j) = 1 /\
    Γ.(Assignment.selector) Selector.QRunning
      overflow_lookup_region (Z.of_nat j) = 1.
  Proof.
    destruct (overflow_lookup_region_facts Γ Hcircuit) as [_ Hfacts].
    destruct
      (enable_lookup_running_rows_selector_fact
        overflow_lookup_region 0 13 j Hj)
      as [Hin_lookup Hin_running].
    rewrite Z.add_0_l in Hin_lookup, Hin_running.
    split.
    - exact (interpret_facts_In Γ _ _ Hfacts Hin_lookup).
    - exact (interpret_facts_In Γ _ _ Hfacts Hin_running).
  Qed.

  (** ** The ten-bit lookup bound on the [OverflowLookup] running-sum words

      The range-check lookup argument (configured by
      [lookup_range_check.configure 10 QLookup QRunning QBitshift A9 TableIdx]
      at [circuit.configure]) holds at every [(region, row)], at the
      generator-table row bound — the shared [TableIdx] column is the ten-bit
      table.  Mirrors [BaseFieldCanonicity.range_check_lookup_holds]. *)
  Lemma range_check_lookup_holds
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (region : RegionId.t) (row : Z) :
    eval_lookup_argument Γ (region, row)
      Garden.Halo2.halo2_gadgets.sinsemilla.chip_proof.GeneratorTable
        .table_rows
      (RangeTable.argument 10 Selector.QLookup Selector.QRunning
        Advice.A9 Lookup.TableIdx).
  Proof.
    rewrite <- Garden.Orchard.circuit_proof.merkle.OrchardActionMerkle
      .orchard_table_rows_eq.
    apply (Garden.Orchard.circuit_proof.merkle.OrchardActionMerkle
        .satisfies_lookups_at Γ
      (layouter_table_rows Garden.Orchard.circuit.synthesize)
      orchard_constraint_system
      (RangeTable.argument 10 Selector.QLookup Selector.QRunning
        Advice.A9 Lookup.TableIdx)
      region row).
    - unfold orchard_constraint_system.
      cbn.
      repeat (first [left; reflexivity | right]).
    - exact (holds_lookups Γ Hcircuit).
  Qed.

  (** Per-row ten-bit word range over the [OverflowLookup] region, through
      [RangeTable.word_sound] with the loaded index table
      ([GeneratorTable.loaded] at [Lookup.TableIdx]). *)
  Lemma overflow_lookup_word_range
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (j : nat) (Hj : (j < 13)%nat) :
    0 <=
      (Γ ⊢ ⟦ Expression.Advice Advice.A9 Rotation.cur ⟧
        (overflow_lookup_region, Z.of_nat j)) -F
        (Γ ⊢ ⟦ Expression.Advice Advice.A9 Rotation.next ⟧
          (overflow_lookup_region, Z.of_nat j)) *F
        UnOp.from (2 ^ 10) <
      2 ^ 10.
  Proof.
    destruct (overflow_lookup_selectors_on Γ Hcircuit j Hj)
      as [Hsel_lookup Hsel_running].
    pose proof
      (range_check_lookup_holds Γ Hcircuit
        overflow_lookup_region (Z.of_nat j)) as Hlookup.
    rewrite Garden.Halo2.halo2_gadgets.sinsemilla.chip_proof.GeneratorTable
      .table_rows_eq in Hlookup.
    change (2 ^ Garden.Halo2.halo2_gadgets.sinsemilla.chip.sinsemilla_k)
      with (2 ^ 10) in Hlookup.
    apply (RangeTable.word_sound Γ 10 Selector.QLookup Selector.QRunning
      Advice.A9 Lookup.TableIdx (2 ^ 10)
      overflow_lookup_region (Z.of_nat j)).
    - intros i Hi.
      pose proof
        (Garden.Halo2.halo2_gadgets.sinsemilla.chip_proof.GeneratorTable
          .loaded Γ
          (Garden.Orchard.circuit_proof.merkle.OrchardActionMerkle
            .generator_table_facts Γ Hcircuit)
          Lookup.TableIdx i Hi) as Hload.
      exact Hload.
    - exact Hsel_lookup.
    - exact Hsel_running.
    - exact Hlookup.
  Qed.

  (** ** Pure core of the [s]-decomposition

      A running sum of [n] ten-bit words whose final entry is zero
      reconstructs over the integers: every entry is a reduced field cell and
      every partial sum stays below [2^(10 n) < p], so each mod-[p] step
      collapses, bounding the head by [2^(10 n)]. *)
  Lemma running_sum_zero_bound
      (z : nat -> Z) (n : nat)
      (Hred : forall j : nat, 0 <= z j < Primes.pallas_p)
      (Hword : forall j : nat, (j < n)%nat ->
        0 <= (z j - z (S j) * 2 ^ 10) mod Primes.pallas_p < 2 ^ 10)
      (Hcap : 2 ^ (10 * Z.of_nat n) < Primes.pallas_p)
      (Hlast : z n = 0) :
    0 <= z 0%nat < 2 ^ (10 * Z.of_nat n).
  Proof.
    assert (Hgen : forall (k j : nat), (j + k = n)%nat ->
      0 <= z j < 2 ^ (10 * Z.of_nat k)).
    { induction k as [| k IH]; intros j Hjk.
      - replace j with n by lia.
        rewrite Hlast.
        cbn.
        lia.
      - assert (Hnext : 0 <= z (S j) < 2 ^ (10 * Z.of_nat k))
          by (apply IH; lia).
        pose proof (Hword j ltac:(lia)) as Hw.
        set (w := (z j - z (S j) * 2 ^ 10) mod Primes.pallas_p) in *.
        assert (Hpow :
            2 ^ (10 * Z.of_nat (S k)) = 2 ^ 10 * 2 ^ (10 * Z.of_nat k)).
        { rewrite <- Z.pow_add_r by lia.
          f_equal.
          lia. }
        assert (Hmono : 2 ^ (10 * Z.of_nat (S k)) <= 2 ^ (10 * Z.of_nat n)).
        { apply Z.pow_le_mono_r; lia. }
        assert (Hupper :
            z (S j) * 2 ^ 10 <= (2 ^ (10 * Z.of_nat k) - 1) * 2 ^ 10).
        { apply Z.mul_le_mono_nonneg_r; lia. }
        assert (Hzj : z j = w + z (S j) * 2 ^ 10).
        { assert (Heq : (w + z (S j) * 2 ^ 10) mod Primes.pallas_p =
            z j mod Primes.pallas_p).
          { unfold w.
            rewrite Zplus_mod_idemp_l.
            f_equal.
            ring. }
          rewrite (Z.mod_small (z j)) in Heq by (apply Hred).
          rewrite (Z.mod_small (w + z (S j) * 2 ^ 10)) in Heq.
          - lia.
          - clear -Hw Hnext Hupper Hpow Hmono Hcap.
            lia. }
        rewrite Hzj.
        clear -Hw Hnext Hupper Hpow.
        lia. }
    apply (Hgen n 0%nat).
    lia.
  Qed.

  (** ** The assembly

      Statement identical to [VarBaseMul.overflow_scalar_exact]
      ([circuit_proof/ownership/var_base_mul.v]); see there for the phase
      documentation.  The proof discharges the hypotheses of
      [VarBaseDefs.overflow_no_wrap] at [z0 := recovered_scalar Γ],
      [alpha := alpha_value Γ] and [s] the (reduced) [OverflowS] witness
      cell: [OverflowChecks.deterministic] supplies the [s_check] and
      [recovery] congruences at the copied cells, the raw [lo_zero] /
      [s_minus_lo_130_check] / [canonicity] constraints supply the case
      analysis, and the 13-word lookup decomposition of [s] supplies the
      [s < 2^130] bound. *)
  Lemma overflow_scalar_exact
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (Hz_1 : 0 <= av Γ Advice.A9 135 < 2 ^ 254)
      (Hbit : lsb_bit Γ = 0 \/ lsb_bit Γ = 1)
      (Hcell : av Γ Advice.A9 136 = recovered_scalar Γ mod Primes.pallas_p)
      (Hz130 : recovered_scalar Γ / 2 ^ 130 = av Γ Advice.A9 126)
      (Hk254 : recovered_scalar Γ / 2 ^ 254 = av Γ Advice.A9 2) :
    recovered_scalar Γ = alpha_value Γ + Primes.t_q.
  Proof.
    pose proof (overflow_check_region_facts Γ Hcircuit)
      as (Hsel & Hc_z136 & Hc_z126 & Hc_z2 & Hc_alpha & Hc_z13 & Hc_s).
    pose proof
      (satisfies_gates_at Γ
        (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)
        Garden.Halo2.halo2_gadgets.ecc.chip.mul.overflow.overflow_checks_gate
        overflow_check_region 1
        ltac:(cbn; repeat (first [left; reflexivity | right]))
        (holds_gates Γ Hcircuit)) as Hgate.
    pose proof
      (enabled_nonzero Γ Selector.QMulOverflow
        overflow_check_region 1 Hsel) as Hselnz.
    pose proof
      (OverflowChecks.deterministic Γ overflow_check_region 1
        Hselnz Hgate) as Hdet.
    (* The [s_check]/[recovery] constraints, as the two record projections. *)
    pose proof (f_equal OverflowChecks.s Hdet) as Hdet_s.
    pose proof (f_equal OverflowChecks.z_0 Hdet) as Hdet_z0.
    cbn [OverflowChecks.s OverflowChecks.z_0 OverflowChecks.output]
      in Hdet_s, Hdet_z0.
    clear Hdet.
    (* The three raw [Either] constraints of the gate. *)
    with_strategy opaque [BinOp.add BinOp.mul BinOp.sub UnOp.from]
      cbn in Hgate.
    destruct Hgate as (_ & _ & Hlo_zero & Hsml & Hcanon).
    specialize (Hlo_zero Hselnz).
    specialize (Hsml Hselnz).
    specialize (Hcanon Hselnz).
    (* Align every gate cell with its copy source. *)
    cbn [Evaluation.eval ExpressionIsEvaluable eval_expression]
      in Hdet_s, Hdet_z0.
    change (rotated_row 1 Rotation.cur) with 1 in Hdet_s, Hdet_z0.
    change (rotated_row 1 Rotation.prev) with 0 in Hdet_s, Hdet_z0.
    cbn in Hc_z136, Hc_z126, Hc_z2, Hc_alpha, Hc_z13, Hc_s.
    rewrite Hc_z136 in Hdet_z0.
    rewrite Hc_alpha in Hdet_s, Hdet_z0.
    rewrite Hc_z2 in Hdet_s, Hlo_zero, Hsml, Hcanon.
    rewrite Hc_z126 in Hlo_zero, Hcanon.
    rewrite Hc_z13 in Hsml, Hcanon.
    rewrite Hc_s in Hdet_s.
    (* The readers, at the source cells. *)
    assert (Hp_lit : Primes.pallas_p =
      28948022309329048855892746252171976963363056481941560715954676764349967630337)
      by reflexivity.
    assert (Hfrom_bound : forall w : Z, 0 <= UnOp.from w < Primes.pallas_p).
    { intro w.
      unfold UnOp.from.
      apply Z.mod_pos_bound.
      rewrite Hp_lit.
      lia. }
    assert (Halpha_eq : alpha_value Γ =
      UnOp.from (Γ.(Assignment.advice) Advice.A2 ivk_add_region 1))
      by reflexivity.
    assert (Hav136_eq : av Γ Advice.A9 136 =
      UnOp.from (Γ.(Assignment.advice) Advice.A9 mul_region 136))
      by reflexivity.
    assert (Hav126_eq : av Γ Advice.A9 126 =
      UnOp.from (Γ.(Assignment.advice) Advice.A9 mul_region 126))
      by reflexivity.
    assert (Hav2_eq : av Γ Advice.A9 2 =
      UnOp.from (Γ.(Assignment.advice) Advice.A9 mul_region 2))
      by reflexivity.
    rewrite Hav136_eq in Hcell.
    rewrite Hav126_eq in Hz130.
    rewrite Hav2_eq in Hk254.
    (* The hypotheses of [overflow_no_wrap]. *)
    assert (Halpha : 0 <= alpha_value Γ < Primes.pallas_p)
      by (rewrite Halpha_eq; apply Hfrom_bound).
    assert (Hz0 : 0 <= recovered_scalar Γ < 2 ^ 255).
    { assert (H255 : 2 ^ 255 = 2 * 2 ^ 254) by (rewrite <- Z.pow_succ_r; lia).
      unfold VarBaseDefs.recovered_scalar.
      clear -Hz_1 Hbit H255.
      lia. }
    assert (Hs_bound : 0 <=
      UnOp.from (Γ.(Assignment.advice) Advice.A6 overflow_s_region 0) <
      Primes.pallas_p)
      by apply Hfrom_bound.
    assert (Hrecovery : recovered_scalar Γ mod Primes.pallas_p =
      (alpha_value Γ + Primes.t_q) mod Primes.pallas_p).
    { rewrite <- Hcell.
      rewrite Hdet_z0.
      rewrite Halpha_eq.
      unfold BinOp.add, UnOp.from.
      change Garden.Halo2.halo2_gadgets.ecc.chip.constants.t_q
        with Primes.t_q.
      now rewrite Zplus_mod_idemp_r. }
    assert (Hs_check :
      UnOp.from (Γ.(Assignment.advice) Advice.A6 overflow_s_region 0)
        mod Primes.pallas_p =
      (alpha_value Γ + recovered_scalar Γ / 2 ^ 254 * 2 ^ 130)
        mod Primes.pallas_p).
    { rewrite Hk254, Halpha_eq.
      rewrite Hdet_s.
      unfold BinOp.add, BinOp.mul, UnOp.from.
      rewrite Z.mod_mod by (rewrite Hp_lit; lia).
      change (2 ^ 130 mod Primes.pallas_p) with (2 ^ 130).
      now rewrite Zplus_mod_idemp_r. }
    assert (Hfrom1 : (UnOp.from 1 : Z) = 1)
      by (unfold UnOp.from; apply Z.mod_small; rewrite Hp_lit; lia).
    assert (Hhigh : recovered_scalar Γ / 2 ^ 254 = 1 ->
      recovered_scalar Γ / 2 ^ 130 = 2 ^ 124).
    { intros Hk1.
      rewrite Hk254 in Hk1.
      destruct Hlo_zero as [Hk0 | H126].
      - congruence.
      - rewrite Hz130.
        refine (eq_trans H126 _).
        vm_compute.
        reflexivity. }
    assert (Hs_low : recovered_scalar Γ / 2 ^ 254 = 1 \/
      recovered_scalar Γ / 2 ^ 130 = 0 ->
      UnOp.from (Γ.(Assignment.advice) Advice.A6 overflow_s_region 0) <
      2 ^ 130).
    { intros Hcase.
      (* Every case of the [s]-decomposition constraints forces [z_13 = 0]. *)
      assert (Hz13 : UnOp.from
        (Γ.(Assignment.advice) Advice.A9 overflow_lookup_region 13) = 0).
      { destruct Hcase as [Hk1 | Hlow].
        - rewrite Hk254 in Hk1.
          destruct Hsml as [Hk0 | Hz13]; [| exact Hz13].
          exfalso.
          assert (Habs : (1:Z) = 0) by exact (eq_trans (eq_sym Hk1) Hk0).
          lia.
        - assert (Hz126_0 : UnOp.from
            (Γ.(Assignment.advice) Advice.A9 mul_region 126) = 0)
            by (rewrite <- Hz130; exact Hlow).
          assert (H130pos : (0:Z) < 2 ^ 130)
            by (apply Z.pow_pos_nonneg; lia).
          assert (Hz0small : recovered_scalar Γ < 2 ^ 130).
          { destruct (Z.lt_ge_cases (recovered_scalar Γ) (2 ^ 130))
              as [Hlt | Hge]; [exact Hlt | exfalso].
            pose proof (Z.div_le_lower_bound
              (recovered_scalar Γ) (2 ^ 130) 1
              H130pos ltac:(lia)) as Hd.
            rewrite Hlow in Hd.
            lia. }
          assert (Hk254_0 : UnOp.from
            (Γ.(Assignment.advice) Advice.A9 mul_region 2) = 0).
          { rewrite <- Hk254.
            apply Z.div_small.
            assert (H130le : (2:Z) ^ 130 <= 2 ^ 254)
              by (apply Z.pow_le_mono_r; lia).
            clear -Hz0 Hz0small H130le.
            lia. }
          destruct Hcanon as [[H1k | H1ze] | Hz13]; [| | exact Hz13].
          + exfalso.
            assert (Habs : (1:Z) = 0)
              by exact (eq_trans (eq_sym Hfrom1) (eq_trans H1k Hk254_0)).
            lia.
          + exfalso.
            assert (Hmul0 : UnOp.from
                (Γ.(Assignment.advice) Advice.A9 mul_region 126) *F
              UnOp.from
                (Γ.(Assignment.advice) Advice.A6
                  overflow_check_region 2) = 0).
            { rewrite Hz126_0.
              unfold BinOp.mul.
              rewrite Z.mul_0_l.
              apply Zmod_0_l. }
            assert (Habs : (1:Z) = 0)
              by exact (eq_trans (eq_sym Hfrom1) (eq_trans H1ze Hmul0)).
            lia. }
      (* The 13-word running sum reconstructs [s] below [2^130]. *)
      destruct (overflow_lookup_region_facts Γ Hcircuit) as [Hl_copy _].
      cbn in Hl_copy.
      set (zf := fun j : nat => UnOp.from
        (Γ.(Assignment.advice) Advice.A9 overflow_lookup_region
          (Z.of_nat j))).
      assert (Hzf_red : forall j : nat, 0 <= zf j < Primes.pallas_p)
        by (intro j; apply Hfrom_bound).
      assert (Hzf_last : zf 13%nat = 0) by exact Hz13.
      assert (Hzf_word : forall j : nat, (j < 13)%nat ->
        0 <= (zf j - zf (S j) * 2 ^ 10) mod Primes.pallas_p < 2 ^ 10).
      { intros j Hj.
        pose proof (overflow_lookup_word_range Γ Hcircuit j Hj) as Hw.
        cbn [Evaluation.eval ExpressionIsEvaluable eval_expression]
          in Hw.
        replace (rotated_row (Z.of_nat j) Rotation.cur) with (Z.of_nat j)
          in Hw by (unfold rotated_row; cbn; lia).
        replace (rotated_row (Z.of_nat j) Rotation.next)
          with (Z.of_nat (S j)) in Hw by (unfold rotated_row; cbn; lia).
        unfold zf, BinOp.sub, BinOp.mul, UnOp.from in Hw |- *.
        change (2 ^ 10 mod Primes.pallas_p) with (2 ^ 10) in Hw.
        rewrite Zminus_mod_idemp_r in Hw.
        exact Hw. }
      assert (Hcap : 2 ^ (10 * Z.of_nat 13) < Primes.pallas_p).
      { change (10 * Z.of_nat 13) with 130.
        rewrite Hp_lit.
        assert (H130 : (2:Z) ^ 130 = 1361129467683753853853498429727072845824)
          by reflexivity.
        lia. }
      pose proof (running_sum_zero_bound zf 13 Hzf_red Hzf_word Hcap Hzf_last)
        as Hbound.
      change (10 * Z.of_nat 13) with 130 in Hbound.
      unfold zf in Hbound.
      change (Z.of_nat 0) with 0 in Hbound.
      rewrite Hl_copy in Hbound.
      lia. }
    exact (overflow_no_wrap
      (alpha_value Γ)
      (recovered_scalar Γ)
      (UnOp.from (Γ.(Assignment.advice) Advice.A6 overflow_s_region 0))
      Halpha Hz0 Hs_bound Hrecovery Hs_check Hhigh Hs_low).
  Qed.
End VarBaseOverflow.
