(** * Circuit-facing base-field scalar canonicity for the nullifier leg.

    The base-field ([NullifierK]) fixed-base multiplication decomposes its
    scalar into 85 base-8 windows on [A4] of the [BaseFieldIncomplete] region.
    Since [8^85 > pallas_p], the mod-p running-sum telescoping alone does not
    pin the windows to the scalar's digits: one field element admits two valid
    255-bit digit strings.  The circuit excludes the non-canonical string with
    the [QMulFixedBaseField] canonicity gate over the [CanonicityChecks]
    region plus the 13-word ten-bit lookup decomposition of
    [alpha_0' = alpha_0 + 2^130 - t_p] in the [AlphaLookup] region.

    This file extracts, from [Holds Γ]:
    - the per-window word ranges of the base-field running sum (the
      [QMulFixedRunningSum] range-check gate, rows 0..84);
    - the canonicity-gate facts at [(CanonicityChecks, 1)] together with the
      six region copies tying the gate cells to the running-sum probes
      [z_0]/[z_43]/[z_44]/[z_84] and the lookup cells [alpha_0']/[z_13];
    - the ten-bit lookup range facts of the [AlphaLookup] running sum (the
      shared [TableIdx] range-check lookup argument);
    and discharges the canonicity bound [wsum 0 85 < pallas_p]
    ([nullifier_k_wsum_canonical]).  Feeding the bound to the circuit-free
    core [Field/BaseEightReconstruct.v] ([reconstruct_of_canon]) yields the
    85-window digit match [nullifier_k_window_digit] — the base-field
    analogue of [short_incomplete_region_window_digit].

    The scalar-value identification ([A4[0] = poseidon_hash2 nk rho + psi])
    is deliberately not part of this file: it composes the Poseidon lane with
    the [QAdd]/[Copy] chain.  Here the scalar is identified only up to its
    cell ([nullifier_k_initial_z]: [A4[0]] is a copy of the [ScalarAdd]
    region's output cell [A6[0]]). *)

Require Import Garden.Halo2.main.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.lemmas.
Require Import Garden.Orchard.columns.
Require Garden.Orchard.circuit.
Require Garden.Halo2.halo2_gadgets.ecc.chip.constants.
Require Garden.Halo2.halo2_gadgets.ecc.chip.mul_fixed.base_field_elem.
Require Garden.Halo2.halo2_gadgets.sinsemilla.chip.
Require Garden.Halo2.halo2_gadgets.sinsemilla.chip_proof.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.spec.
Require Import Garden.Orchard.circuit_spec.
Require Import Garden.Orchard.circuit_proof.inputs.
Require Import Garden.Orchard.circuit_proof.facts.
Require Import Garden.Orchard.circuit_proof.fixed_base.main.
Require Import Garden.Orchard.circuit_proof.merkle.
Require Import Garden.Field.Field.
Require Import Garden.Field.BaseEightReconstruct.
Require Import Garden.Plonky3.M.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Lists.List.
Require Import Stdlib.micromega.Lia.

Import ListNotations.

#[local] Existing Instance Primes.PallasPIsPrime.

Global Open Scope Z_scope.


Module BaseFieldCanonicity.
  Import OrchardActionFixedBase.

  Local Notation Holds Γ :=
    (circuit_holds Γ
      Garden.Orchard.circuit.synthesize
      (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)).

  Local Notation bf_region :=
    (RegionId.Nullifier RegionId.Nullifier.BaseFieldIncomplete).
  Local Notation canon_region :=
    (RegionId.Nullifier RegionId.Nullifier.CanonicityChecks).
  Local Notation alpha_region :=
    (RegionId.Nullifier RegionId.Nullifier.AlphaLookup).
  Local Notation scalar_add_region :=
    (RegionId.Nullifier RegionId.Nullifier.ScalarAdd).

  (* ---------------------------------------------------------------------- *)
  (* Pure helpers on the base-8 word sums of [BaseEightReconstruct].         *)
  (* ---------------------------------------------------------------------- *)

  Lemma is_bool_01 (x : Z) (Hx : IsBool.t x) : x = 0 \/ x = 1.
  Proof.
    unfold IsBool.t, IsBool.ZIsBool in Hx.
    destruct (Z.odd x); cbn in Hx; [right | left]; exact Hx.
  Qed.

  Lemma wsum_one (P : Z) (zs : nat -> Z) (j : nat) :
    BaseEightReconstruct.wsum P zs j 1 = BaseEightReconstruct.word P zs j.
  Proof.
    cbn [BaseEightReconstruct.wsum].
    lia.
  Qed.

  (* Weighted-sum splitting: the first [r1] words plus the shifted tail. *)
  Lemma wsum_split (P : Z) (zs : nat -> Z) :
    forall r1 r2 j : nat,
      BaseEightReconstruct.wsum P zs j (r1 + r2) =
        BaseEightReconstruct.wsum P zs j r1 +
          8 ^ Z.of_nat r1 * BaseEightReconstruct.wsum P zs (j + r1)%nat r2.
  Proof.
    induction r1 as [| r1 IH]; intros r2 j.
    - cbn [Nat.add BaseEightReconstruct.wsum].
      rewrite Nat.add_0_r.
      cbn [Z.of_nat].
      lia.
    - cbn [Nat.add BaseEightReconstruct.wsum].
      rewrite IH.
      rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
      replace (j + S r1)%nat with (S j + r1)%nat by lia.
      ring.
  Qed.

  (* Ranged word-sum bound: only the words actually covered by the sum need
     to be in [0, 8) (the global-quantifier [wsum_bound] of the core is not
     usable circuit-side, where rows past the region are unconstrained). *)
  Lemma wsum_bound_ranged (P : Z) (zs : nat -> Z) :
    forall r j : nat,
      (forall i : nat, (j <= i < j + r)%nat ->
        0 <= BaseEightReconstruct.word P zs i < 8) ->
      0 <= BaseEightReconstruct.wsum P zs j r < 8 ^ Z.of_nat r.
  Proof.
    induction r as [| r IH]; intros j Hwords.
    - cbn [BaseEightReconstruct.wsum Z.of_nat]. lia.
    - cbn [BaseEightReconstruct.wsum].
      pose proof (IH (S j) ltac:(intros i Hi; apply Hwords; lia)) as Htail.
      pose proof (Hwords j ltac:(lia)) as Hhead.
      rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
      lia.
  Qed.

  (* The word sum is the [scalar_from_windows] of the word list — the bridge
     to the window-digit read-off of [circuit_proof/inputs.v]. *)
  Lemma wsum_eq_scalar_from_windows (P : Z) (zs : nat -> Z) :
    forall r j : nat,
      BaseEightReconstruct.wsum P zs j r =
        scalar_from_windows
          (List.map (fun m : nat => BaseEightReconstruct.word P zs m)
            (List.seq j r)).
  Proof.
    induction r as [| r IH]; intros j.
    - reflexivity.
    - cbn [BaseEightReconstruct.wsum List.seq List.map].
      rewrite scalar_from_windows_cons.
      rewrite (IH (S j)).
      reflexivity.
  Qed.

  (* Generic-base running-sum head bound: a zero-tailed chain of reduced
     entries with [count] words in [0, B) reconstructs below [B^count]
     (used at base [2^10] for the [alpha_0'] lookup decomposition). *)
  Lemma chain_head_bound
      (P B : Z) (zl : nat -> Z) (count : nat)
      (HP : 0 < P) (HB : 1 < B)
      (Hfit : B ^ Z.of_nat count < P)
      (Hred : forall n : nat, (n <= count)%nat -> 0 <= zl n < P)
      (Hwords : forall j : nat, (j < count)%nat ->
        0 <= (zl j - B * zl (S j)) mod P < B)
      (Hzero : zl count = 0) :
    0 <= zl 0%nat < B ^ Z.of_nat count.
  Proof.
    assert (Hgen : forall r j : nat, (j + r = count)%nat ->
        0 <= zl j < B ^ Z.of_nat r).
    { induction r as [| r IH]; intros j Hj.
      - assert (j = count) by lia. subst j.
        rewrite Hzero. cbn [Z.of_nat]. lia.
      - pose proof (IH (S j) ltac:(lia)) as Htail.
        pose proof (Hwords j ltac:(lia)) as Hword.
        assert (Hpow_succ : B ^ Z.of_nat (S r) = B * B ^ Z.of_nat r).
        { rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. reflexivity. }
        assert (Hpow_le : B ^ Z.of_nat (S r) <= B ^ Z.of_nat count).
        { apply Z.pow_le_mono_r; lia. }
        set (w := (zl j - B * zl (S j)) mod P) in *.
        assert (Hmul_le : B * zl (S j) <= B * (B ^ Z.of_nat r - 1)).
        { apply Z.mul_le_mono_nonneg_l; lia. }
        assert (Hsum : 0 <= w + B * zl (S j) < B ^ Z.of_nat (S r)).
        { rewrite Hpow_succ. lia. }
        assert (Hstep : zl j = w + B * zl (S j)).
        { assert (Hcong : (w + B * zl (S j)) mod P = zl j mod P).
          { subst w.
            rewrite Zplus_mod_idemp_l.
            f_equal. ring. }
          rewrite (Z.mod_small (w + B * zl (S j)) P) in Hcong by lia.
          rewrite (Z.mod_small (zl j) P) in Hcong by (apply Hred; lia).
          lia. }
        lia. }
    exact (Hgen count 0%nat ltac:(lia)).
  Qed.

  (* Field word to integer word: for a reduced scale [B], the running-sum
     word [a -F b *F B] is [(a - B·b) mod p]. *)
  Lemma field_scaled_word_val (B a b : Z)
      (HB : 0 <= B < Primes.pallas_p) :
    a -F b *F UnOp.from B = (a - B * b) mod Primes.pallas_p.
  Proof.
    unfold BinOp.sub, BinOp.mul, UnOp.from.
    rewrite (Z.mod_small B Primes.pallas_p HB).
    rewrite Zminus_mod_idemp_r.
    f_equal. ring.
  Qed.

  (* The base-8 instance, in the [UnOp.from h] shape the running-sum gates
     produce. *)
  Lemma field_word_h (a b : Z) :
    a -F b *F UnOp.from Garden.Halo2.halo2_gadgets.ecc.chip.constants.h =
      (a - 8 * b) mod Primes.pallas_p.
  Proof.
    rewrite (field_scaled_word_val
      Garden.Halo2.halo2_gadgets.ecc.chip.constants.h a b)
      by (unfold Garden.Halo2.halo2_gadgets.ecc.chip.constants.h,
        Garden.Halo2.halo2_gadgets.ecc.chip.constants.fixed_base_window_size,
        Primes.pallas_p, Primes.t_p; lia).
    reflexivity.
  Qed.

  Lemma pallas_p_eq :
    Primes.pallas_p = 2 ^ 254 + Primes.t_p.
  Proof. reflexivity. Qed.

  Lemma t_p_bounds : 0 < Primes.t_p < 2 ^ 130.
  Proof. unfold Primes.t_p. lia. Qed.

  Lemma pallas_p_gt_8 : 8 < Primes.pallas_p.
  Proof. unfold Primes.pallas_p, Primes.t_p. lia. Qed.

  (* ---------------------------------------------------------------------- *)
  (* Fact extraction: the base-field mul program of the nullifier leg.       *)
  (* ---------------------------------------------------------------------- *)

  (* The whole [synth_nullifier_k_mul] program at
     its concrete scalar cell (the [ScalarAdd] region's output [A6[0]]). *)
  Lemma nullifier_k_mul_facts
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    interpret_facts Γ
      (layouter_facts
        (Garden.Orchard.circuit.synth_nullifier_k_mul
          (Garden.Halo2.Synthesis.Cell.advice scalar_add_region Advice.A6 0))).
  Proof.
    pose proof (nullifier_facts Γ Hcircuit) as Hfacts.
    destruct (layouter_value Garden.Orchard.circuit.synthesize_witness_inputs)
      as [ [ [ [ [ [ [psi_old rho_old] cm_old] g_d_old] ak_P] nk] v_old]
        v_new].
    unfold Garden.Orchard.circuit.synthesize_nullifier in Hfacts.
    apply interpret_layouter_facts_bind_left in Hfacts.
    apply interpret_layouter_facts_in_namespace in Hfacts.
    do 2 apply interpret_layouter_facts_bind_right in Hfacts.
    apply interpret_layouter_facts_bind_left in Hfacts.
    apply interpret_layouter_facts_in_namespace in Hfacts.
    exact Hfacts.
  Qed.

  (* The incomplete-addition region's synthesis facts. *)
  Lemma nullifier_k_incomplete_facts
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    interpret_facts Γ
      (layouter_facts
        (Garden.Orchard.circuit
          .synth_base_field_mul_incomplete
          bf_region
          (Garden.Halo2.Synthesis.Cell.advice scalar_add_region Advice.A6 0))).
  Proof.
    pose proof (nullifier_k_mul_facts Γ Hcircuit) as Hfacts.
    unfold Garden.Orchard.circuit
      .synth_nullifier_k_mul in Hfacts.
    apply interpret_layouter_facts_in_namespace in Hfacts.
    apply interpret_layouter_facts_bind_left in Hfacts.
    exact Hfacts.
  Qed.

  (* [QMulFixedRunningSum] is enabled at every window row of the base-field
     incomplete region (85 rows; the base-field sibling of
     [short_incomplete_selector_fact]). *)
  Lemma base_field_incomplete_selector_fact
      (region : RegionId.t)
      (scalar : Garden.Halo2.Synthesis.Cell.t columns RegionId.t)
      (i : nat) :
    (i < 85)%nat ->
    List.In
      (Fact.SelectorOn Selector.QMulFixedRunningSum region (Z.of_nat i))
      (layouter_facts
        (Garden.Orchard.circuit
          .synth_base_field_mul_incomplete
          region scalar)).
  Proof.
    intros Hi.
    unfold Garden.Orchard.circuit
      .synth_base_field_mul_incomplete.
    cbn [layouter_facts region_facts].
    apply List.in_or_app.
    right.
    apply List.in_or_app.
    right.
    apply List.in_or_app.
    left.
    replace (Z.of_nat i) with (0 + Z.of_nat i) by lia.
    apply running_sum_rows_selector_fact.
    exact Hi.
  Qed.

  (* Per-row word range over the base-field region: each of the 85
     running-sum words lies in [0, 8). *)
  Lemma nullifier_k_word_range
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (i : nat) (Hi : (i < 85)%nat) :
    0 <=
      (Γ ⊢ ⟦ Expression.Advice Advice.A4 Rotation.cur ⟧
        (bf_region, Z.of_nat i)) -F
        (Γ ⊢ ⟦ Expression.Advice Advice.A4 Rotation.next ⟧
          (bf_region, Z.of_nat i)) *F
        UnOp.from Garden.Halo2.halo2_gadgets.ecc.chip.constants.h <
      8.
  Proof.
    apply (running_sum_word_range_of_facts Γ
      (layouter_facts
        (Garden.Orchard.circuit
          .synth_base_field_mul_incomplete
          bf_region
          (Garden.Halo2.Synthesis.Cell.advice scalar_add_region Advice.A6 0)))
      bf_region (Z.of_nat i)
      (nullifier_k_incomplete_facts Γ Hcircuit)).
    - apply base_field_incomplete_selector_fact.
      exact Hi.
    - exact (holds_gates Γ Hcircuit).
  Qed.

  (* The initial running-sum entry [A4[0]] is a copy of the scalar cell
     ([A6[0]] of the [ScalarAdd] region). *)
  Lemma nullifier_k_initial_z
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    read_advice Γ Advice.A4 bf_region 0 =
      UnOp.from
        (eval_cell Γ
          (Garden.Halo2.Synthesis.Cell.advice scalar_add_region Advice.A6 0)).
  Proof.
    pose proof (nullifier_k_incomplete_facts Γ Hcircuit) as Hfacts.
    unfold Garden.Orchard.circuit
      .synth_base_field_mul_incomplete in Hfacts.
    apply interpret_layouter_facts_add_region in Hfacts.
    apply interpret_region_facts_bind_left in Hfacts.
    cbn [region_facts interpret_facts interpret_fact] in Hfacts.
    destruct Hfacts as [Hcopy _].
    unfold read_advice.
    rewrite eval_advice_cur_cell.
    rewrite Hcopy.
    reflexivity.
  Qed.

  (* ---------------------------------------------------------------------- *)
  (* Fact extraction: the ten-bit lookup decomposition of [alpha_0'].        *)
  (* ---------------------------------------------------------------------- *)

  (* Both range-check selectors are enabled at rows 0..12 of the
     [AlphaLookup] region. *)
  Lemma enable_lookup_running_rows_selector_fact
      (region : RegionId.t) (offset : Z) (count i : nat) :
    (i < count)%nat ->
    List.In
      (Fact.SelectorOn Selector.QLookup region (offset + Z.of_nat i))
      (region_facts region
        (Garden.Orchard.circuit.enable_lookup_running_rows offset count)) /\
    List.In
      (Fact.SelectorOn Selector.QRunning region (offset + Z.of_nat i))
      (region_facts region
        (Garden.Orchard.circuit.enable_lookup_running_rows offset count)).
  Proof.
    revert offset i.
    induction count as [| count IH]; intros offset i Hi.
    - lia.
    - destruct i as [| i].
      + cbn [Garden.Orchard.circuit.enable_lookup_running_rows region_facts
          List.app].
        split.
        * left. f_equal. lia.
        * right. left. f_equal. lia.
      + cbn [Garden.Orchard.circuit.enable_lookup_running_rows region_facts
          List.app].
        destruct (IH (offset + 1) i ltac:(lia)) as [H1 H2].
        replace (offset + Z.of_nat (S i)) with (offset + 1 + Z.of_nat i)
          by lia.
        split; right; right; assumption.
  Qed.

  Lemma nullifier_k_alpha_lookup_facts
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    interpret_facts Γ
      (region_facts alpha_region
        (Garden.Orchard.circuit.enable_lookup_running_rows 0 13)).
  Proof.
    pose proof (nullifier_k_mul_facts Γ Hcircuit) as Hfacts.
    unfold Garden.Orchard.circuit
      .synth_nullifier_k_mul in Hfacts.
    apply interpret_layouter_facts_in_namespace in Hfacts.
    do 2 apply interpret_layouter_facts_bind_right in Hfacts.
    apply interpret_layouter_facts_bind_left in Hfacts.
    unfold Garden.Orchard.circuit.synthesize_alpha_lookup in Hfacts.
    apply interpret_layouter_facts_in_namespace in Hfacts.
    apply interpret_layouter_facts_add_region in Hfacts.
    apply interpret_region_facts_bind_left in Hfacts.
    exact Hfacts.
  Qed.

  Lemma nullifier_k_alpha_lookup_selectors_on
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (j : nat) (Hj : (j < 13)%nat) :
    Γ.(Assignment.selector) Selector.QLookup alpha_region (Z.of_nat j) = 1 /\
    Γ.(Assignment.selector) Selector.QRunning alpha_region (Z.of_nat j) = 1.
  Proof.
    pose proof (nullifier_k_alpha_lookup_facts Γ Hcircuit) as Hfacts.
    destruct (enable_lookup_running_rows_selector_fact alpha_region 0 13 j Hj)
      as [Hin_lookup Hin_running].
    rewrite Z.add_0_l in Hin_lookup, Hin_running.
    split.
    - exact (interpret_facts_In Γ _ _ Hfacts Hin_lookup).
    - exact (interpret_facts_In Γ _ _ Hfacts Hin_running).
  Qed.

  (* The ten-bit range-check lookup argument configured by
     [lookup_range_check.configure 10 QLookup QRunning QBitshift A9 TableIdx]. *)
  Definition range_check_lookup_argument : LookupArgument.t columns := {|
    LookupArgument.pairs :=
      let q_lookup := Expression.Selector Selector.QLookup in
      let q_running := Expression.Selector Selector.QRunning in
      let z_cur := Expression.Advice Advice.A9 Rotation.cur in
      let one := Expression.Constant 1 in
      let running_sum_lookup :=
        let z_next := Expression.Advice Advice.A9 Rotation.next in
        let running_sum_word := z_cur ➖ (z_next ● (2 ^ 10)) in
        q_running ✖️ running_sum_word in
      let short_lookup :=
        let short_word := z_cur in
        let q_short := one ➖ q_running in
        q_short ✖️ short_word in
      [
        (q_lookup ✖️ (running_sum_lookup ➕ short_lookup), Lookup.TableIdx)
      ];
  |}.

  (* The range-check lookup argument holds at every [(region, row)], at the
     generator-table row bound (the shared [TableIdx] column is the ten-bit
     table).  Mirrors [generator_table_lookup_holds_1]. *)
  Lemma range_check_lookup_holds
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ)
      (region : RegionId.t) (row : Z) :
    eval_lookup_argument Γ (region, row)
      Garden.Halo2.halo2_gadgets.sinsemilla.chip_proof.GeneratorTable.table_rows
      range_check_lookup_argument.
  Proof.
    rewrite <- OrchardActionMerkle.orchard_table_rows_eq.
    apply (OrchardActionMerkle.satisfies_lookups_at Γ
      (layouter_table_rows Garden.Orchard.circuit.synthesize)
      orchard_constraint_system
      range_check_lookup_argument
      region row).
    - unfold orchard_constraint_system, range_check_lookup_argument.
      cbn.
      repeat (first [left; reflexivity | right]).
    - exact (holds_lookups Γ Hcircuit).
  Qed.

  (* Per-row ten-bit word range over the [AlphaLookup] region: each of the 13
     lookup running-sum words lies in [0, 2^10). *)
  Lemma alpha_lookup_word_range
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ)
      (j : nat) (Hj : (j < 13)%nat) :
    0 <=
      (Γ ⊢ ⟦ Expression.Advice Advice.A9 Rotation.cur ⟧
        (alpha_region, Z.of_nat j)) -F
        (Γ ⊢ ⟦ Expression.Advice Advice.A9 Rotation.next ⟧
          (alpha_region, Z.of_nat j)) *F
        UnOp.from (2 ^ 10) <
      2 ^ 10.
  Proof.
    destruct (nullifier_k_alpha_lookup_selectors_on Γ Hcircuit j Hj)
      as [Hsel_lookup Hsel_running].
    pose proof (range_check_lookup_holds Γ Hcircuit alpha_region (Z.of_nat j))
      as Hlookup.
    with_strategy opaque [BinOp.add BinOp.sub BinOp.mul UnOp.from
      Garden.Halo2.halo2_gadgets.sinsemilla.chip_proof.GeneratorTable
        .table_rows]
      cbn in Hlookup.
    destruct Hlookup as (table_row & Hbound & Hpairs).
    rewrite Garden.Halo2.halo2_gadgets.sinsemilla.chip_proof.GeneratorTable
      .table_rows_eq in Hbound.
    unfold range_check_lookup_argument in Hpairs.
    cbn [LookupArgument.pairs] in Hpairs.
    rewrite Forall_cons_iff in Hpairs.
    destruct Hpairs as [Hpair _].
    with_strategy opaque [BinOp.add BinOp.sub BinOp.mul UnOp.from]
      cbn in Hpair.
    rewrite Hsel_lookup, Hsel_running in Hpair.
    rewrite (Garden.Halo2.halo2_gadgets.sinsemilla.chip_proof.GeneratorTable
      .loaded Γ
      (OrchardActionMerkle.generator_table_facts Γ Hcircuit)
      Lookup.TableIdx table_row Hbound) in Hpair.
    cbn [Garden.Halo2.halo2_gadgets.sinsemilla.chip_proof.GeneratorTable.lookup]
      in Hpair.
    assert (Hsub11 : BinOp.sub 1 1 = 0).
    { unfold BinOp.sub. now rewrite Z.sub_diag, Zmod_0_l. }
    rewrite FieldRewrite.from_one in Hpair.
    setoid_rewrite Hsub11 in Hpair.
    setoid_rewrite FieldRewrite.add_zero_right in Hpair.
    repeat setoid_rewrite FieldRewrite.mul_one_left in Hpair.
    repeat setoid_rewrite FieldRewrite.from_from in Hpair.
    repeat setoid_rewrite FieldRewrite.from_sub in Hpair.
    with_strategy opaque [BinOp.add BinOp.sub BinOp.mul UnOp.from] cbn.
    unfold BinOp.sub, BinOp.mul, BinOp.add, UnOp.from in Hpair |- *.
    rewrite Hpair.
    change (2 ^ Garden.Halo2.halo2_gadgets.sinsemilla.chip.sinsemilla_k)
      with 1024 in Hbound.
    exact Hbound.
  Qed.

  (* ---------------------------------------------------------------------- *)
  (* Fact extraction: the [CanonicityChecks] region and its gate.            *)
  (* ---------------------------------------------------------------------- *)

  (* The region facts: [QMulFixedBaseField] enabled at offset 1, and the six
     copies feeding the gate — [alpha]/[z_84]/[z_44]/[z_43] from the
     base-field running sum, [alpha_0']/[z_13] from the lookup region. *)
  Lemma nullifier_k_canonicity_region_facts
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    Γ.(Assignment.selector) Selector.QMulFixedBaseField canon_region 1 = 1 /\
    eval_cell Γ (Garden.Halo2.Synthesis.Cell.advice canon_region Advice.A6 0) =
      eval_cell Γ (Garden.Halo2.Synthesis.Cell.advice bf_region Advice.A4 0) /\
    eval_cell Γ (Garden.Halo2.Synthesis.Cell.advice canon_region Advice.A8 0) =
      eval_cell Γ (Garden.Halo2.Synthesis.Cell.advice bf_region Advice.A4 84) /\
    eval_cell Γ (Garden.Halo2.Synthesis.Cell.advice canon_region Advice.A6 1) =
      eval_cell Γ (Garden.Halo2.Synthesis.Cell.advice alpha_region Advice.A9 0) /\
    eval_cell Γ (Garden.Halo2.Synthesis.Cell.advice canon_region Advice.A6 2) =
      eval_cell Γ
        (Garden.Halo2.Synthesis.Cell.advice alpha_region Advice.A9 13) /\
    eval_cell Γ (Garden.Halo2.Synthesis.Cell.advice canon_region Advice.A7 2) =
      eval_cell Γ (Garden.Halo2.Synthesis.Cell.advice bf_region Advice.A4 44) /\
    eval_cell Γ (Garden.Halo2.Synthesis.Cell.advice canon_region Advice.A8 2) =
      eval_cell Γ (Garden.Halo2.Synthesis.Cell.advice bf_region Advice.A4 43).
  Proof.
    pose proof (nullifier_k_mul_facts Γ Hcircuit) as Hfacts.
    unfold Garden.Orchard.circuit
      .synth_nullifier_k_mul in Hfacts.
    apply interpret_layouter_facts_in_namespace in Hfacts.
    do 3 apply interpret_layouter_facts_bind_right in Hfacts.
    apply interpret_layouter_facts_bind_left in Hfacts.
    unfold Garden.Orchard.circuit.synthesize_canonicity_checks in Hfacts.
    apply interpret_layouter_facts_add_region in Hfacts.
    cbn [region_facts region_value layouter_value Monad.bind
      Garden.Halo2.Synthesis.RegionIsMonad
      Garden.Orchard.circuit.BaseFieldFixedResult.alpha
      Garden.Orchard.circuit.BaseFieldFixedResult.z_43_alpha
      Garden.Orchard.circuit.BaseFieldFixedResult.z_44_alpha
      Garden.Orchard.circuit.BaseFieldFixedResult.z_84_alpha
      Garden.Orchard.circuit.LookupResult.z_0
      Garden.Orchard.circuit.LookupResult.z_13
      List.app interpret_facts interpret_fact] in Hfacts.
    tauto.
  Qed.

  (* All eight conjuncts of the canonicity gate at an enabled row, including
     the four [MSB = 1 => _] conditionals that [CanonicityChecks.sound]
     leaves out. *)
  Lemma canonicity_gate_eval
      (Γ : Assignment.t columns RegionId.t)
      (region : RegionId.t) (row : Z)
      (Hselector :
        Γ ⊢ ⟦ Selector.QMulFixedBaseField ⟧ (region, row) <> 0)
      (Hgates :
        satisfies_gates Γ
          (𝓒.run_unit Garden.Orchard.circuit.configure
            ConstraintSystem.empty)) :
    ((Γ ⊢ ⟦ Expression.Advice Advice.A8 Rotation.cur ⟧ (region, row)) = 0 \/
      (Γ ⊢ ⟦ Expression.Advice Advice.A7 Rotation.cur ⟧ (region, row)) = 0) /\
    ((Γ ⊢ ⟦ Expression.Advice Advice.A8 Rotation.cur ⟧ (region, row)) = 0 \/
      (Γ ⊢ ⟦ Expression.Advice Advice.A7 Rotation.next ⟧ (region, row)) -F
        (Γ ⊢ ⟦ Expression.Advice Advice.A8 Rotation.prev ⟧ (region, row)) *F
        UnOp.from (2 ^ 120) = 0) /\
    ((Γ ⊢ ⟦ Expression.Advice Advice.A8 Rotation.cur ⟧ (region, row)) = 0 \/
      IsBool.t
        ((Γ ⊢ ⟦ Expression.Advice Advice.A8 Rotation.next ⟧ (region, row)) -F
          (Γ ⊢ ⟦ Expression.Advice Advice.A7 Rotation.next ⟧ (region, row)) *F
          UnOp.from Garden.Halo2.halo2_gadgets.ecc.chip.constants.h)) /\
    ((Γ ⊢ ⟦ Expression.Advice Advice.A8 Rotation.cur ⟧ (region, row)) = 0 \/
      (Γ ⊢ ⟦ Expression.Advice Advice.A6 Rotation.next ⟧ (region, row)) = 0) /\
    (0 <= Γ ⊢ ⟦ Expression.Advice Advice.A7 Rotation.cur ⟧ (region, row) <
      Z.of_nat 4) /\
    IsBool.t (Γ ⊢ ⟦ Expression.Advice Advice.A8 Rotation.cur ⟧ (region, row)) /\
    (Γ ⊢ ⟦ Expression.Advice Advice.A8 Rotation.prev ⟧ (region, row)) =
      (Γ ⊢ ⟦ Expression.Advice Advice.A7 Rotation.cur ⟧ (region, row)) +F
        (Γ ⊢ ⟦ Expression.Advice Advice.A8 Rotation.cur ⟧ (region, row)) *F
        UnOp.from (2 ^ 2) /\
    (Γ ⊢ ⟦ Expression.Advice Advice.A6 Rotation.cur ⟧ (region, row)) =
      (Γ ⊢ ⟦ Expression.Advice Advice.A6 Rotation.prev ⟧ (region, row)) -F
        (Γ ⊢ ⟦ Expression.Advice Advice.A8 Rotation.prev ⟧ (region, row)) *F
        UnOp.from (2 ^ 252) +F
        UnOp.from (2 ^ 130) -F
        UnOp.from Garden.Halo2.halo2_gadgets.ecc.chip.constants.t_p.
  Proof.
    assert (Hgate :
      Γ ⊢ ⟦ Garden.Halo2.halo2_gadgets.ecc.chip.mul_fixed.base_field_elem
          .canonicity_checks_gate ⟧ (region, row)).
    { apply (satisfies_gates_at Γ
        (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)
        Garden.Halo2.halo2_gadgets.ecc.chip.mul_fixed.base_field_elem
          .canonicity_checks_gate
        region row); [| exact Hgates].
      cbn.
      repeat (first [left; reflexivity | right]). }
    with_strategy opaque [BinOp.add BinOp.mul BinOp.sub UnOp.from IsBool.t]
      cbn in Hgate |- *.
    destruct Hgate as (h1 & h2 & h3 & h4 & h5 & h6 & h7 & h8).
    specialize (h1 Hselector).
    specialize (h2 Hselector).
    specialize (h3 Hselector).
    specialize (h4 Hselector).
    specialize (h5 Hselector).
    specialize (h6 Hselector).
    specialize (h7 Hselector).
    specialize (h8 Hselector).
    exact (conj h1 (conj h2 (conj h3 (conj h4
      (conj h5 (conj h6 (conj h7 h8))))))).
  Qed.

  (* Rotated advice evaluation as a cell read (generic in the rotation; the
     [cur] case is [eval_advice_cur_cell]). *)
  Lemma eval_advice_rot_cell
      (Γ : Assignment.t columns RegionId.t)
      (column : Advice.t) (region : RegionId.t) (row : Z)
      (rotation : Rotation.t) :
    Γ ⊢ ⟦ Expression.Advice column rotation ⟧ (region, row) =
      UnOp.from
        (eval_cell Γ
          (Garden.Halo2.Synthesis.Cell.advice region column
            (row + rotation.(Rotation.offset)))).
  Proof.
    reflexivity.
  Qed.

  (* ---------------------------------------------------------------------- *)
  (* The circuit-free canonicity core.                                       *)
  (* ---------------------------------------------------------------------- *)

  (* From the digested gate/lookup facts, the 85-window word sum of the
     base-field running sum lies below the field modulus.  [zs] are the
     (reduced) running-sum entries, [zl0] the (reduced) [alpha_0'] lookup
     head, [a1]/[a2] the gate's top-window pieces. *)
  Lemma wsum_canonical_core
      (zs : nat -> Z) (zl0 a1 a2 : Z)
      (Hzred : forall n : nat, 0 <= zs n < Primes.pallas_p)
      (Hlred : 0 <= zl0 < Primes.pallas_p)
      (Hwords : forall i : nat, (i < 85)%nat ->
        0 <= BaseEightReconstruct.word Primes.pallas_p zs i < 8)
      (Hz85 : zs 85%nat = 0)
      (Ha1 : 0 <= a1 < 4)
      (Ha2 : a2 = 0 \/ a2 = 1)
      (Hz84 : zs 84%nat = a1 + 4 * a2)
      (Hmsb_a1 : a2 = 1 -> a1 = 0)
      (Hmsb_hi : a2 = 1 ->
        zs 44%nat = (zs 84%nat * 2 ^ 120) mod Primes.pallas_p)
      (Hmsb_43 : a2 = 1 ->
        BaseEightReconstruct.word Primes.pallas_p zs 43 = 0 \/
        BaseEightReconstruct.word Primes.pallas_p zs 43 = 1)
      (Hmsb_l0 : a2 = 1 -> zl0 < 2 ^ 130)
      (Hl0 : zl0 mod Primes.pallas_p =
        (zs 0%nat - zs 84%nat * 2 ^ 252 + 2 ^ 130 - Primes.t_p)
          mod Primes.pallas_p) :
    0 <= BaseEightReconstruct.wsum Primes.pallas_p zs 0 85 <
      Primes.pallas_p.
  Proof.
    pose proof pallas_p_gt_8 as Hp8.
    pose proof pallas_p_eq as Hp.
    pose proof t_p_bounds as Htp.
    (* Top word: [word 84 = zs 84]. *)
    assert (Hw84 : BaseEightReconstruct.word Primes.pallas_p zs 84 =
        zs 84%nat).
    { unfold BaseEightReconstruct.word.
      rewrite Hz85.
      replace (zs 84%nat - 8 * 0) with (zs 84%nat) by ring.
      apply Z.mod_small.
      split; [lia | ].
      pose proof (Hzred 84%nat). lia. }
    (* Split off the top window. *)
    pose proof (wsum_split Primes.pallas_p zs 84 1 0) as Hsplit85.
    replace (84 + 1)%nat with 85%nat in Hsplit85 by reflexivity.
    cbn [Nat.add] in Hsplit85.
    rewrite wsum_one, Hw84 in Hsplit85.
    assert (Hb84 : 0 <= BaseEightReconstruct.wsum Primes.pallas_p zs 0 84 <
        8 ^ Z.of_nat 84).
    { apply wsum_bound_ranged.
      intros i Hi. apply Hwords. lia. }
    assert (Hpow84 : 8 ^ Z.of_nat 84 = 2 ^ 252) by reflexivity.
    destruct Ha2 as [Ha2_0 | Ha2_1].
    - (* MSB clear: the sum is below [2^254]. *)
      rewrite Hsplit85.
      rewrite Hz84, Ha2_0.
      lia.
    - (* MSB set: the canonicity chain bounds the low part below [t_p]. *)
      specialize (Hmsb_a1 Ha2_1).
      specialize (Hmsb_hi Ha2_1).
      specialize (Hmsb_43 Ha2_1).
      specialize (Hmsb_l0 Ha2_1).
      assert (Hz84_4 : zs 84%nat = 4) by lia.
      (* [zs 44 = 2^122]. *)
      assert (Hz44 : zs 44%nat = 2 ^ 122).
      { rewrite Hmsb_hi, Hz84_4.
        apply Z.mod_small. lia. }
      (* Middle windows 44..83 vanish. *)
      pose proof (BaseEightReconstruct.wsum_tail_congruent
        Primes.pallas_p Hp8 zs 85 Hz85 41 44 ltac:(lia)) as Hcong44.
      pose proof (wsum_split Primes.pallas_p zs 40 1 44) as Hsplit44.
      replace (40 + 1)%nat with 41%nat in Hsplit44 by reflexivity.
      replace (44 + 40)%nat with 84%nat in Hsplit44 by reflexivity.
      rewrite wsum_one, Hw84, Hz84_4 in Hsplit44.
      assert (Hb4440 : 0 <=
          BaseEightReconstruct.wsum Primes.pallas_p zs 44 40 < 8 ^ Z.of_nat 40).
      { apply wsum_bound_ranged.
        intros i Hi. apply Hwords. lia. }
      assert (Hpow40 : 8 ^ Z.of_nat 40 = 2 ^ 120) by reflexivity.
      assert (Hmid : BaseEightReconstruct.wsum Primes.pallas_p zs 44 40 = 0).
      { rewrite (Z.mod_small
            (BaseEightReconstruct.wsum Primes.pallas_p zs 44 41)
            Primes.pallas_p) in Hcong44 by lia.
        rewrite (Z.mod_small (zs 44%nat) Primes.pallas_p) in Hcong44
          by (apply Hzred).
        lia. }
      (* The low 84 windows are the low 44 windows. *)
      pose proof (wsum_split Primes.pallas_p zs 44 40 0) as Hsplit84low.
      replace (44 + 40)%nat with 84%nat in Hsplit84low by reflexivity.
      cbn [Nat.add] in Hsplit84low.
      rewrite Hmid in Hsplit84low.
      (* Window 43 is boolean, so the low part is below [2^130]. *)
      pose proof (wsum_split Primes.pallas_p zs 43 1 0) as Hsplit43.
      replace (43 + 1)%nat with 44%nat in Hsplit43 by reflexivity.
      cbn [Nat.add] in Hsplit43.
      rewrite wsum_one in Hsplit43.
      assert (Hb43 : 0 <=
          BaseEightReconstruct.wsum Primes.pallas_p zs 0 43 < 8 ^ Z.of_nat 43).
      { apply wsum_bound_ranged.
        intros i Hi. apply Hwords. lia. }
      assert (Hpow43 : 8 ^ Z.of_nat 43 = 2 ^ 129) by reflexivity.
      assert (Hlow130 : 0 <=
          BaseEightReconstruct.wsum Primes.pallas_p zs 0 44 < 2 ^ 130).
      { rewrite Hsplit43. lia. }
      (* [alpha_0' = wsum 0 44 + 2^130 - t_p] over the integers. *)
      pose proof (BaseEightReconstruct.wsum_tail_congruent
        Primes.pallas_p Hp8 zs 85 Hz85 85 0 ltac:(lia)) as Hcong0.
      rewrite (Z.mod_small (zs 0%nat) Primes.pallas_p) in Hcong0
        by (apply Hzred).
      assert (Hl0v : zl0 =
          BaseEightReconstruct.wsum Primes.pallas_p zs 0 44 + 2 ^ 130 -
            Primes.t_p).
      { assert (Hchain : zl0 mod Primes.pallas_p =
            (BaseEightReconstruct.wsum Primes.pallas_p zs 0 44 + 2 ^ 130 -
              Primes.t_p) mod Primes.pallas_p).
        { rewrite Hl0.
          rewrite <- Hcong0.
          replace (BaseEightReconstruct.wsum Primes.pallas_p zs 0 85
              mod Primes.pallas_p - zs 84%nat * 2 ^ 252 + 2 ^ 130 - Primes.t_p)
            with (BaseEightReconstruct.wsum Primes.pallas_p zs 0 85
              mod Primes.pallas_p +
              (- (zs 84%nat * 2 ^ 252) + 2 ^ 130 - Primes.t_p)) by ring.
          rewrite Zplus_mod_idemp_l.
          f_equal.
          rewrite Hsplit85, Hsplit84low, Hz84_4.
          rewrite Hpow84.
          ring. }
        rewrite (Z.mod_small zl0 Primes.pallas_p Hlred) in Hchain.
        rewrite (Z.mod_small _ Primes.pallas_p) in Hchain by lia.
        exact Hchain. }
      (* The lookup bound turns it into [wsum 0 44 < t_p]. *)
      assert (Hlow_tp : BaseEightReconstruct.wsum Primes.pallas_p zs 0 44 <
          Primes.t_p) by lia.
      rewrite Hsplit85, Hsplit84low, Hz84_4.
      lia.
  Qed.

  (* ---------------------------------------------------------------------- *)
  (* The canonicity bound from [Holds].                                      *)
  (* ---------------------------------------------------------------------- *)

  (* The canonicity bound: the 85-window word sum of the base-field running
     sum, read at the [BaseFieldIncomplete] rows, lies in [0, pallas_p). *)
  Lemma nullifier_k_wsum_canonical
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    0 <=
      BaseEightReconstruct.wsum Primes.pallas_p
        (fun n : nat =>
          Γ ⊢ ⟦ Expression.Advice Advice.A4 Rotation.cur ⟧
            (bf_region, Z.of_nat n))
        0 85 <
      Primes.pallas_p.
  Proof.
    set (zs := fun n : nat =>
      Γ ⊢ ⟦ Expression.Advice Advice.A4 Rotation.cur ⟧
        (bf_region, Z.of_nat n)).
    set (zl := fun n : nat =>
      Γ ⊢ ⟦ Expression.Advice Advice.A9 Rotation.cur ⟧
        (alpha_region, Z.of_nat n)).
    (* Reduced entries. *)
    assert (Hzred : forall n : nat, 0 <= zs n < Primes.pallas_p).
    { intros n. apply eval_advice_cur_bounds. }
    assert (Hlred : forall n : nat, 0 <= zl n < Primes.pallas_p).
    { intros n. apply eval_advice_cur_bounds. }
    (* Words in range. *)
    assert (Hwords : forall i : nat, (i < 85)%nat ->
        0 <= BaseEightReconstruct.word Primes.pallas_p zs i < 8).
    { intros i Hi.
      pose proof (nullifier_k_word_range Γ Hcircuit i Hi) as Hrange.
      rewrite (eval_advice_next_succ Γ Advice.A4 bf_region i) in Hrange.
      rewrite field_word_h in Hrange.
      exact Hrange. }
    (* Boundary. *)
    assert (Hz85 : zs 85%nat = 0).
    { exact (nullifier_k_z_boundary_of_holds Γ Hcircuit). }
    (* Canonicity region: selector and copies. *)
    destruct (nullifier_k_canonicity_region_facts Γ Hcircuit)
      as (Hsel & Hc_alpha & Hc_z84 & Hc_a0p & Hc_z13 & Hc_z44 & Hc_z43).
    pose proof (canonicity_gate_eval Γ canon_region 1
      (enabled_nonzero Γ Selector.QMulFixedBaseField canon_region 1 Hsel)
      (holds_gates Γ Hcircuit))
      as (Hg1 & Hg2 & Hg3 & Hg4 & Hg5 & Hg6 & Hg7 & Hg8).
    (* Gate operands as running-sum / lookup reads. *)
    assert (Ha6prev :
        Γ ⊢ ⟦ Expression.Advice Advice.A6 Rotation.prev ⟧ (canon_region, 1) =
        zs 0%nat).
    { rewrite eval_advice_rot_cell.
      change (1 + (Rotation.prev).(Rotation.offset)) with 0.
      rewrite Hc_alpha.
      rewrite <- eval_advice_cur_cell.
      reflexivity. }
    assert (Ha8prev :
        Γ ⊢ ⟦ Expression.Advice Advice.A8 Rotation.prev ⟧ (canon_region, 1) =
        zs 84%nat).
    { rewrite eval_advice_rot_cell.
      change (1 + (Rotation.prev).(Rotation.offset)) with 0.
      rewrite Hc_z84.
      rewrite <- eval_advice_cur_cell.
      reflexivity. }
    assert (Ha6cur :
        Γ ⊢ ⟦ Expression.Advice Advice.A6 Rotation.cur ⟧ (canon_region, 1) =
        zl 0%nat).
    { rewrite eval_advice_rot_cell.
      change (1 + (Rotation.cur).(Rotation.offset)) with 1.
      rewrite Hc_a0p.
      rewrite <- eval_advice_cur_cell.
      reflexivity. }
    assert (Ha6next :
        Γ ⊢ ⟦ Expression.Advice Advice.A6 Rotation.next ⟧ (canon_region, 1) =
        zl 13%nat).
    { rewrite eval_advice_rot_cell.
      change (1 + (Rotation.next).(Rotation.offset)) with 2.
      rewrite Hc_z13.
      rewrite <- eval_advice_cur_cell.
      reflexivity. }
    assert (Ha7next :
        Γ ⊢ ⟦ Expression.Advice Advice.A7 Rotation.next ⟧ (canon_region, 1) =
        zs 44%nat).
    { rewrite eval_advice_rot_cell.
      change (1 + (Rotation.next).(Rotation.offset)) with 2.
      rewrite Hc_z44.
      rewrite <- eval_advice_cur_cell.
      reflexivity. }
    assert (Ha8next :
        Γ ⊢ ⟦ Expression.Advice Advice.A8 Rotation.next ⟧ (canon_region, 1) =
        zs 43%nat).
    { rewrite eval_advice_rot_cell.
      change (1 + (Rotation.next).(Rotation.offset)) with 2.
      rewrite Hc_z43.
      rewrite <- eval_advice_cur_cell.
      reflexivity. }
    set (a1 := Γ ⊢ ⟦ Expression.Advice Advice.A7 Rotation.cur ⟧
      (canon_region, 1)) in *.
    set (a2 := Γ ⊢ ⟦ Expression.Advice Advice.A8 Rotation.cur ⟧
      (canon_region, 1)) in *.
    rewrite Ha7next, Ha8prev in Hg2.
    rewrite Ha8next, Ha7next in Hg3.
    rewrite Ha6next in Hg4.
    rewrite Ha8prev in Hg7.
    rewrite Ha6cur, Ha6prev, Ha8prev in Hg8.
    (* Digest the gate facts. *)
    apply is_bool_01 in Hg6.
    change (Z.of_nat 4) with 4 in Hg5.
    assert (Hz84 : zs 84%nat = a1 + 4 * a2).
    { rewrite Hg7.
      unfold BinOp.add, BinOp.mul, UnOp.from.
      change (2 ^ 2) with 4.
      rewrite (Z.mod_small 4) by (unfold Primes.pallas_p, Primes.t_p; lia).
      rewrite (Z.mod_small (a2 * 4))
        by (unfold Primes.pallas_p, Primes.t_p; lia).
      rewrite Z.mod_small by (unfold Primes.pallas_p, Primes.t_p; lia).
      ring. }
    assert (Hmsb_a1 : a2 = 1 -> a1 = 0).
    { intros Ha2_1. destruct Hg1 as [Ha2_0 | Ha1_0]; [lia | exact Ha1_0]. }
    assert (Hmsb_hi : a2 = 1 ->
        zs 44%nat = (zs 84%nat * 2 ^ 120) mod Primes.pallas_p).
    { intros Ha2_1.
      destruct Hg2 as [Ha2_0 | Hhi]; [lia | ].
      apply sub_zero_equiv in Hhi.
      unfold BinOp.mul, UnOp.from in Hhi.
      rewrite (Z.mod_small (zs 44%nat)) in Hhi by (apply Hzred).
      rewrite Hhi.
      rewrite Zmod_mod.
      rewrite (Z.mod_small (2 ^ 120))
        by (unfold Primes.pallas_p, Primes.t_p; lia).
      reflexivity. }
    assert (Hmsb_43 : a2 = 1 ->
        BaseEightReconstruct.word Primes.pallas_p zs 43 = 0 \/
        BaseEightReconstruct.word Primes.pallas_p zs 43 = 1).
    { intros Ha2_1.
      destruct Hg3 as [Ha2_0 | Hb43]; [lia | ].
      rewrite field_word_h in Hb43.
      apply is_bool_01 in Hb43.
      exact Hb43. }
    (* The lookup chain bounds [alpha_0'] when the MSB is set. *)
    assert (Hlwords : forall j : nat, (j < 13)%nat ->
        0 <= (zl j - 2 ^ 10 * zl (S j)) mod Primes.pallas_p < 2 ^ 10).
    { intros j Hj.
      pose proof (alpha_lookup_word_range Γ Hcircuit j Hj) as Hrange.
      rewrite (eval_advice_next_succ Γ Advice.A9 alpha_region j) in Hrange.
      rewrite (field_scaled_word_val (2 ^ 10)) in Hrange
        by (unfold Primes.pallas_p, Primes.t_p; lia).
      exact Hrange. }
    assert (Hmsb_l0 : a2 = 1 -> zl 0%nat < 2 ^ 130).
    { intros Ha2_1.
      assert (Hz13 : zl 13%nat = 0).
      { destruct Hg4 as [Ha2_0 | Hz13]; [lia | exact Hz13]. }
      pose proof (chain_head_bound Primes.pallas_p (2 ^ 10) zl 13
        ltac:(unfold Primes.pallas_p, Primes.t_p; lia)
        ltac:(lia)
        ltac:(unfold Primes.pallas_p, Primes.t_p; lia)
        ltac:(intros n _; apply Hlred)
        Hlwords
        Hz13) as Hhead.
      change ((2 ^ 10) ^ Z.of_nat 13) with (2 ^ 130) in Hhead.
      lia. }
    (* The [alpha_0'] reconstruction equation, over the integers mod p. *)
    assert (Hl0 : zl 0%nat mod Primes.pallas_p =
        (zs 0%nat - zs 84%nat * 2 ^ 252 + 2 ^ 130 - Primes.t_p)
          mod Primes.pallas_p).
    { rewrite Hg8.
      unfold Garden.Halo2.halo2_gadgets.ecc.chip.constants.t_p.
      unfold BinOp.add, BinOp.sub, BinOp.mul, UnOp.from.
      rewrite Zmod_mod.
      rewrite (Z.mod_small (2 ^ 252))
        by (unfold Primes.pallas_p, Primes.t_p; lia).
      rewrite Zminus_mod_idemp_r.
      rewrite Zplus_mod_idemp_l.
      rewrite (Z.mod_small (2 ^ 130))
        by (unfold Primes.pallas_p, Primes.t_p; lia).
      rewrite Zminus_mod_idemp_l.
      replace (zs 0%nat - (zs 84%nat * 2 ^ 252) mod Primes.pallas_p + 2 ^ 130 -
          Primes.t_p)
        with (zs 0%nat + 2 ^ 130 - Primes.t_p -
          (zs 84%nat * 2 ^ 252) mod Primes.pallas_p) by ring.
      rewrite Zminus_mod_idemp_r.
      f_equal.
      ring. }
    (* Assemble. *)
    exact (wsum_canonical_core zs (zl 0%nat) a1 a2
      Hzred (Hlred 0%nat) Hwords Hz85 Hg5 Hg6 Hz84
      Hmsb_a1 Hmsb_hi Hmsb_43 Hmsb_l0 Hl0).
  Qed.

  (* ---------------------------------------------------------------------- *)
  (* The 85-window digit match.                                              *)
  (* ---------------------------------------------------------------------- *)

  (* Per-window digit match over the base-field region: digit [i] of the
     initial running-sum entry [A4[0]] is the [i]-th circuit word — the
     85-window analogue of [short_incomplete_region_window_digit], with the
     canonicity bound replacing the [8^count < p] fit. *)
  Lemma nullifier_k_window_digit
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (i : nat) (Hi : (i < 85)%nat) :
    EccSpec.window_digit (read_advice Γ Advice.A4 bf_region 0) i =
      (Γ ⊢ ⟦ Expression.Advice Advice.A4 Rotation.cur ⟧
        (bf_region, Z.of_nat i)) -F
        (Γ ⊢ ⟦ Expression.Advice Advice.A4 Rotation.next ⟧
          (bf_region, Z.of_nat i)) *F
        UnOp.from Garden.Halo2.halo2_gadgets.ecc.chip.constants.h.
  Proof.
    pose proof pallas_p_gt_8 as Hp8.
    set (zs := fun n : nat =>
      Γ ⊢ ⟦ Expression.Advice Advice.A4 Rotation.cur ⟧
        (bf_region, Z.of_nat n)).
    assert (Hwords : forall m : nat, (m < 85)%nat ->
        0 <= BaseEightReconstruct.word Primes.pallas_p zs m < 8).
    { intros m Hm.
      pose proof (nullifier_k_word_range Γ Hcircuit m Hm) as Hrange.
      rewrite (eval_advice_next_succ Γ Advice.A4 bf_region m) in Hrange.
      rewrite field_word_h in Hrange.
      exact Hrange. }
    assert (Hz85 : zs 85%nat = 0).
    { exact (nullifier_k_z_boundary_of_holds Γ Hcircuit). }
    (* The reconstruction over the integers, from the canonicity bound. *)
    assert (Hrec : zs 0%nat =
        BaseEightReconstruct.wsum Primes.pallas_p zs 0 85).
    { apply (BaseEightReconstruct.reconstruct_of_canon
        Primes.pallas_p Hp8 zs 85 Hz85).
      - apply eval_advice_cur_bounds.
      - exact (nullifier_k_wsum_canonical Γ Hcircuit). }
    (* Read the digit off the reconstructed word list. *)
    rewrite (eval_advice_next_succ Γ Advice.A4 bf_region i).
    rewrite field_word_h.
    change ((Γ ⊢ ⟦ Expression.Advice Advice.A4 Rotation.cur ⟧
        (bf_region, Z.of_nat i) -
        8 * Γ ⊢ ⟦ Expression.Advice Advice.A4 Rotation.cur ⟧
          (bf_region, Z.of_nat (S i))) mod Primes.pallas_p)
      with (BaseEightReconstruct.word Primes.pallas_p zs i).
    change (read_advice Γ Advice.A4 bf_region 0) with (zs 0%nat).
    rewrite Hrec.
    rewrite (wsum_eq_scalar_from_windows Primes.pallas_p zs 85 0%nat).
    rewrite (window_digit_scalar_from_windows_nth
      (List.map (fun m : nat => BaseEightReconstruct.word Primes.pallas_p zs m)
        (List.seq 0 85))
      i).
    - apply (nth_map_seq
        (fun m : nat => BaseEightReconstruct.word Primes.pallas_p zs m)
        85 i 0).
      exact Hi.
    - apply List.Forall_forall.
      intros w Hin.
      apply List.in_map_iff in Hin.
      destruct Hin as [m Hin].
      destruct Hin as [Hw Hin].
      apply List.in_seq in Hin.
      subst w.
      apply Hwords.
      lia.
    - rewrite List.length_map, List.length_seq.
      exact Hi.
  Qed.

  (* The same digit match, with the scalar named through its cell: [A4[0]]
     is the copy of the [ScalarAdd] output cell, so the digits are those of
     the (reduced) scalar cell value.  The scalar-value identification
     ([A6[0]] of [ScalarAdd] equals [poseidon_hash2 nk rho + psi]) is a
     separate obligation, discharged by the Poseidon composition in
     [circuit_proof/us_free/nullifier_k.v]. *)
  Lemma nullifier_k_window_digit_scalar_cell
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (i : nat) (Hi : (i < 85)%nat) :
    EccSpec.window_digit
      (UnOp.from
        (eval_cell Γ
          (Garden.Halo2.Synthesis.Cell.advice scalar_add_region Advice.A6 0)))
      i =
      (Γ ⊢ ⟦ Expression.Advice Advice.A4 Rotation.cur ⟧
        (bf_region, Z.of_nat i)) -F
        (Γ ⊢ ⟦ Expression.Advice Advice.A4 Rotation.next ⟧
          (bf_region, Z.of_nat i)) *F
        UnOp.from Garden.Halo2.halo2_gadgets.ecc.chip.constants.h.
  Proof.
    rewrite <- (nullifier_k_initial_z Γ Hcircuit).
    apply (nullifier_k_window_digit Γ Hcircuit i Hi).
  Qed.

End BaseFieldCanonicity.
