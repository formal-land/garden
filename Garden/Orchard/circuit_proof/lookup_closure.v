(** * Deriving the short-lookup range facts from operational acceptance

    The relational model leaves the [QRunning] selector free at the rows
    where a short range check fires, so the ten-bit lookup bound on the
    checked cell is not derivable from [Holds] alone: a dishonest
    assignment can set [QRunning] nonzero there and route the lookup
    through the running-sum branch (see the header of
    [circuit_proof/note_commit/words.v]).  Operational acceptance closes
    that gap.  The realized assignment reads its selector plane from the
    replayed grid at absolute rows, and the pinned Orchard event stream
    enables [QRunning] at none of the short-range rows, so the selector is
    the initial grid's zero there.

    The file provides:

    - [replay_selector_unset]: a selector index/row that no event enables
      keeps the initial grid's value along any successful replay;
    - [ten_bit_bound_at]: the short branch of the shared range-check
      lookup argument ([RangeTable.short_word_sound]) at a row where
      [QLookup] is on and [QRunning] is off;
    - [bitshift_gate_at]: the companion [Short lookup bitshift] gate;
    - [short_range_bound]: the width-tightening extraction lemma — one
      lemma parameterized on the region, the bit width and the pinned
      inverse constant, covering every short-range site of the circuit;
    - the row-inventory certificates over the pinned event stream and the
      reified synthesis facts, factored through one generic per-site
      lemma;
    - [note_commit_new_short_lookup_ok_operational]: the whole eleven-cell
      new-note family, from replay success and ideal operational
      acceptance of the serialized Orchard circuit. *)

Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Lists.List.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.ZArith.ZArith.
Require Import Garden.Halo2.main.
Require Import Garden.Halo2.Synthesis.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.lemmas.
Require Import Garden.Halo2.serialize.
Require Import Garden.Halo2.realize.main.
Require Import Garden.Halo2.realize.sound.
Require Garden.Halo2.halo2_gadgets.utilities.lookup_range_check.
Require Import Garden.Halo2.halo2_gadgets.utilities.lookup_range_check_proof.
Require Garden.Halo2.halo2_gadgets.ecc.chip.constants.
Require Import Garden.Halo2.halo2_gadgets.sinsemilla.chip_proof.
Require Import Garden.Orchard.columns.
Require Import Garden.Orchard.decidable_eq.
Require Import Garden.Orchard.circuit_synthesis_layout.
Require Garden.Orchard.circuit.
Require Import Garden.Orchard.circuit_proof.facts.
Require Import Garden.Orchard.circuit_proof.merkle.
Require Import Garden.Orchard.circuit_proof.note_commit.words.
Require Import Garden.Orchard.circuit_operational.
Require Import Garden.Field.Field.
Require Import Garden.Plonky3.M.

Import ListNotations.

#[local] Existing Instance Primes.PallasPIsPrime.

Global Open Scope Z_scope.

Module OrchardShortLookupClosure.
  Import OrchardDecidableEq.
  Import OrchardActionMerkle.

  Local Notation Holds Γ :=
    (circuit_holds Γ
      Garden.Orchard.circuit.synthesize
      (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)).

  (** ** A selector no event enables keeps the initial grid's value

      The positive direction ([Halo2/realize/facts.v]
      [replay_selector_pinned]) reads an enabled point out of the replay
      log.  This is the negative direction: [apply_event] touches
      [RawGrid.sel] only in the [EnableSelector] branch, and
      [RawGrid.set_selector] changes the plane only at the written point,
      so a point that no event writes is untouched by the whole replay. *)

  Definition selector_enabled_at (column row : Z) (event : Raw.Event.t)
      : bool :=
    match event with
    | Raw.Event.EnableSelector c r _ => andb (c =? column) (r =? row)
    | _ => false
    end.

  Lemma apply_events_log_selector_unset
      (events : list Raw.Event.t) (column row : Z)
      (Hnone :
        List.forallb (fun e => negb (selector_enabled_at column row e))
          events = true)
      (state state' : ReplayState.t)
      (Happly : apply_events_log events state = Some state') :
    state'.(ReplayState.grid).(RawGrid.sel) column row =
      state.(ReplayState.grid).(RawGrid.sel) column row.
  Proof.
    revert state Happly.
    induction events as [| event events IH];
      cbn in Hnone |- *; intros state Happly.
    - injection Happly as <-.
      reflexivity.
    - apply andb_true_iff in Hnone.
      destruct Hnone as [Hhead Htail].
      destruct (apply_event state event) as [state1 |] eqn:Hevent;
        [| discriminate Happly].
      rewrite (IH Htail state1 Happly).
      revert Hevent.
      destruct event as
        [name | name | name | name | c r annotation
        | c r annotation value | left_cell right_cell
        | c from_row to_row value];
        cbn;
        try (intros Hevent; injection Hevent as <-; reflexivity).
      + destruct (List.existsb (write_conflicts_write c r 1)
            state.(ReplayState.log).(Log.selectors));
          intros Hevent; [discriminate Hevent |].
        injection Hevent as <-.
        cbn.
        cbn [selector_enabled_at] in Hhead.
        apply negb_true_iff in Hhead.
        destruct (andb (column =? c) (row =? r)) eqn:Hpoint; [| reflexivity].
        apply andb_true_iff in Hpoint.
        destruct Hpoint as [Hc Hr].
        apply Z.eqb_eq in Hc, Hr.
        subst.
        rewrite !Z.eqb_refl in Hhead.
        discriminate Hhead.
      + destruct (orb
            (List.existsb (write_conflicts_write c r value)
              state.(ReplayState.log).(Log.fixeds))
            (List.existsb (write_conflicts_fill c r value)
              state.(ReplayState.log).(Log.fills)));
          intros Hevent; [discriminate Hevent |].
        injection Hevent as <-.
        reflexivity.
      + destruct (orb
            (List.existsb (fill_conflicts_write c from_row to_row value)
              state.(ReplayState.log).(Log.fixeds))
            (List.existsb (fill_conflicts_fill c from_row to_row value)
              state.(ReplayState.log).(Log.fills)));
          intros Hevent; [discriminate Hevent |].
        injection Hevent as <-.
        reflexivity.
  Qed.

  Lemma replay_selector_unset
      (events : list Raw.Event.t) (initial final : RawGrid.t)
      (column row : Z)
      (Hreplay : apply_events events initial = Some final)
      (Hnone :
        List.forallb (fun e => negb (selector_enabled_at column row e))
          events = true) :
    final.(RawGrid.sel) column row = initial.(RawGrid.sel) column row.
  Proof.
    unfold apply_events in Hreplay.
    destruct (apply_events_log events (ReplayState.init initial))
      as [state |] eqn:Hlog; [| discriminate Hreplay].
    injection Hreplay as <-.
    exact (apply_events_log_selector_unset events column row Hnone
      (ReplayState.init initial) state Hlog).
  Qed.

  (** The witness supplies no selector plane, so the initial grid holds
      [0] at every selector point. *)
  Lemma realized_selector_unset
      (events : list Raw.Event.t) (advice instance_ : Z -> Z -> Z)
      (grid : RawGrid.t) (column row : Z)
      (Hreplay :
        apply_events events (initial_grid advice instance_) = Some grid)
      (Hnone :
        List.forallb (fun e => negb (selector_enabled_at column row e))
          events = true) :
    grid.(RawGrid.sel) column row = 0.
  Proof.
    exact (replay_selector_unset events (initial_grid advice instance_) grid
      column row Hreplay Hnone).
  Qed.

  (** ** Reflection from a membership checker to [List.In]

      Only the two fact shapes this file reads are compared; every other
      pair is rejected, which keeps [fact_beq_eq] a three-case proof. *)

  Definition fact_beq (f g : Fact.t columns RegionId.t) : bool :=
    match f, g with
    | Fact.SelectorOn s r o, Fact.SelectorOn s' r' o' =>
        andb (andb (selector_eqb s s') (region_id_eqb r r')) (o =? o')
    | Fact.CellIsConstant c v, Fact.CellIsConstant c' v' =>
        andb (cell_eqb c c') (v =? v')
    | _, _ => false
    end.

  Lemma fact_beq_eq (f g : Fact.t columns RegionId.t) :
    fact_beq f g = true -> f = g.
  Proof.
    destruct f, g; cbn [fact_beq]; intros Hb; try discriminate Hb.
    - apply andb_true_iff in Hb; destruct Hb as [Hb Ho].
      apply andb_true_iff in Hb; destruct Hb as [Hs Hr].
      apply selector_eqb_eq in Hs.
      apply region_id_eqb_eq in Hr.
      apply Z.eqb_eq in Ho.
      subst.
      reflexivity.
    - apply andb_true_iff in Hb; destruct Hb as [Hc Hv].
      apply cell_eqb_eq in Hc.
      apply Z.eqb_eq in Hv.
      subst.
      reflexivity.
  Qed.

  Lemma fact_In_of_beq (f : Fact.t columns RegionId.t)
      (l : list (Fact.t columns RegionId.t)) :
    List.existsb (fact_beq f) l = true -> List.In f l.
  Proof.
    intros Hex.
    apply List.existsb_exists in Hex.
    destruct Hex as [g Hg].
    destruct Hg as [Hin Hb].
    rewrite (fact_beq_eq _ _ Hb).
    exact Hin.
  Qed.

  (** ** The shared range-check lookup argument

      The circuit configures exactly one range check
      ([lookup_range_check.configure 10 QLookup QRunning QBitshift A9
      TableIdx] at [circuit.configure]); every short-range site of every
      family uses it.  Its [TableIdx] column is the ten-bit index column
      of the shared generator-table load. *)

  Definition range_check_argument : LookupArgument.t columns :=
    RangeTable.argument 10 Selector.QLookup Selector.QRunning
      Advice.A9 Lookup.TableIdx.

  Lemma range_check_lookup_holds
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ)
      (region : RegionId.t) (row : Z) :
    eval_lookup_argument Γ (region, row)
      Garden.Halo2.halo2_gadgets.sinsemilla.chip_proof.GeneratorTable
        .table_rows
      range_check_argument.
  Proof.
    rewrite <- OrchardActionMerkle.orchard_table_rows_eq.
    apply (OrchardActionMerkle.satisfies_lookups_at Γ
      (layouter_table_rows Garden.Orchard.circuit.synthesize)
      orchard_constraint_system
      range_check_argument
      region row).
    - unfold orchard_constraint_system, range_check_argument.
      cbn.
      repeat (first [left; reflexivity | right]).
    - exact (holds_lookups Γ Hcircuit).
  Qed.

  (** The short branch: at a row where [QLookup] is on and [QRunning] is
      off, the lookup input collapses to the [A9] cell itself, so table
      membership is the ten-bit bound. *)
  Lemma ten_bit_bound_at
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ)
      (region : RegionId.t) (row : Z)
      (Hlk : Γ.(Assignment.selector) Selector.QLookup region row = 1)
      (Hrun : Γ.(Assignment.selector) Selector.QRunning region row = 0) :
    0 <=
      UnOp.from
        (eval_cell Γ
          (Garden.Halo2.Synthesis.Cell.advice region Advice.A9 row)) <
      2 ^ 10.
  Proof.
    rewrite <- (eval_advice_cur_cell Γ region Advice.A9 row).
    pose proof (range_check_lookup_holds Γ Hcircuit region row) as Hlookup.
    rewrite Garden.Halo2.halo2_gadgets.sinsemilla.chip_proof.GeneratorTable
      .table_rows_eq in Hlookup.
    change (2 ^ Garden.Halo2.halo2_gadgets.sinsemilla.chip.sinsemilla_k)
      with (2 ^ 10) in Hlookup.
    apply (RangeTable.short_word_sound Γ 10 Selector.QLookup Selector.QRunning
      Advice.A9 Lookup.TableIdx (2 ^ 10) region row).
    - intros i Hi.
      exact (Garden.Halo2.halo2_gadgets.sinsemilla.chip_proof.GeneratorTable
        .loaded Γ (OrchardActionMerkle.generator_table_facts Γ Hcircuit)
        Lookup.TableIdx i Hi).
    - exact Hlk.
    - exact Hrun.
    - exact Hlookup.
  Qed.

  (** ** The companion bitshift gate *)

  Lemma bitshift_gate_In :
    List.In
      (Garden.Halo2.halo2_gadgets.utilities.lookup_range_check
        .short_lookup_bitshift_gate (columns := columns)
        10 Selector.QBitshift Advice.A9)
      (𝓒.run_unit Garden.Orchard.circuit.configure
        ConstraintSystem.empty).(ConstraintSystem.gates).
  Proof.
    cbn.
    repeat (first [left; reflexivity | right]).
  Qed.

  Lemma bitshift_gate_at
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ)
      (region : RegionId.t)
      (Hbs : Γ.(Assignment.selector) Selector.QBitshift region 1 = 1) :
    BinOp.mul
      (BinOp.mul
        (UnOp.from (Γ.(Assignment.advice) Advice.A9 region 0))
        (UnOp.from (2 ^ 10)))
      (UnOp.from (Γ.(Assignment.advice) Advice.A9 region 2)) =
    UnOp.from (Γ.(Assignment.advice) Advice.A9 region 1).
  Proof.
    pose proof (satisfies_gates_at Γ
      (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)
      (Garden.Halo2.halo2_gadgets.utilities.lookup_range_check
        .short_lookup_bitshift_gate (columns := columns)
        10 Selector.QBitshift Advice.A9)
      region 1 bitshift_gate_In (holds_gates Γ Hcircuit)) as Hgate.
    with_strategy opaque [BinOp.add BinOp.sub BinOp.mul UnOp.from]
      cbn in Hgate.
    rewrite Hbs in Hgate.
    change (2 ^ 10) with 1024.
    apply Hgate.
    rewrite FieldRewrite.from_one.
    clear.
    unfold Primes.pallas_p.
    lia.
  Qed.

  (** ** The width-tightening arithmetic

      With the pinned inverse [inv] satisfying [2^10 * inv = 2^(10 - bits)]
      in the field, the bitshift row reads, over the integers,
      [z_1 = z_0 * 2^(10 - bits)]: the product is below [2^20 < p], so the
      reduction is the identity and the ten-bit bound on [z_1] tightens the
      ten-bit bound on [z_0] to [bits] bits. *)

  Lemma pallas_p_big : 2 ^ 20 < Primes.pallas_p.
  Proof.
    apply Z.ltb_lt.
    vm_cast_no_check (@eq_refl bool true).
  Qed.

  Lemma short_word_tighten (p a b inv bits : Z)
      (Hp : 2 ^ 20 < p)
      (Hbits : 0 <= bits <= 10)
      (Ha : 0 <= a < 2 ^ 10)
      (Hb : 0 <= b < 2 ^ 10)
      (Hinv : (2 ^ 10 * inv) mod p = 2 ^ (10 - bits))
      (Hgate : (a * (2 ^ 10 mod p) mod p * (inv mod p)) mod p = b) :
    a < 2 ^ bits.
  Proof.
    assert (Hpow_lo : 0 < 2 ^ (10 - bits))
      by (apply Z.pow_pos_nonneg; clear -Hbits; lia).
    assert (Hpow_hi : 2 ^ (10 - bits) <= 2 ^ 10)
      by (apply Z.pow_le_mono_r; clear -Hbits; lia).
    assert (Hsplit : 2 ^ bits * 2 ^ (10 - bits) = 2 ^ 10).
    { rewrite <- Z.pow_add_r by (clear -Hbits; lia).
      f_equal.
      clear -Hbits; lia. }
    assert (Hbound : 0 <= a * 2 ^ (10 - bits) < p).
    { assert (Hnn : 0 <= a * 2 ^ (10 - bits))
        by (apply Z.mul_nonneg_nonneg; clear -Ha Hpow_lo; lia).
      assert (Hle : a * 2 ^ (10 - bits) <= (2 ^ 10 - 1) * 2 ^ 10).
      { apply Z.mul_le_mono_nonneg;
          clear -Ha Hpow_lo Hpow_hi; lia. }
      change ((2 ^ 10 - 1) * 2 ^ 10) with 1047552 in Hle.
      change (2 ^ 20) with 1048576 in Hp.
      clear -Hnn Hle Hp; lia. }
    rewrite Zmult_mod_idemp_r in Hgate.
    rewrite Zmult_mod_idemp_l in Hgate.
    replace (a * (2 ^ 10 mod p) * inv) with (a * inv * (2 ^ 10 mod p))
      in Hgate by ring.
    rewrite Zmult_mod_idemp_r in Hgate.
    replace (a * inv * 2 ^ 10) with (a * (2 ^ 10 * inv)) in Hgate by ring.
    assert (Hstep :
        (a * (2 ^ 10 * inv)) mod p = (a * ((2 ^ 10 * inv) mod p)) mod p)
      by (rewrite Zmult_mod_idemp_r; reflexivity).
    rewrite Hstep, Hinv, (Z.mod_small _ _ Hbound) in Hgate.
    rewrite <- Hgate in Hb.
    rewrite <- Hsplit in Hb.
    apply (proj2 (Z.mul_lt_mono_pos_r (2 ^ (10 - bits)) a (2 ^ bits) Hpow_lo)).
    clear -Hb; lia.
  Qed.

  (** ** The generic extraction lemma

      One lemma for every short-range site of the circuit, parameterized on
      the region, the bit width and the pinned inverse constant.  All the
      premises except the two [QRunning] readings are consequences of
      [Holds Γ] for an arbitrary [Γ]; those two are where operational
      acceptance enters. *)

  Lemma advice_cell_read
      (Γ : Assignment.t columns RegionId.t)
      (region : RegionId.t) (column : Advice.t) (row : Z) :
    eval_cell Γ (Garden.Halo2.Synthesis.Cell.advice region column row) =
      Γ.(Assignment.advice) column region row.
  Proof.
    reflexivity.
  Qed.

  Lemma short_range_bound
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ)
      (region : RegionId.t) (bits inv : Z)
      (Hbits : 0 <= bits <= 10)
      (Hinv : UnOp.from (2 ^ 10 * inv) = 2 ^ (10 - bits))
      (Hconst :
        List.In
          (Fact.CellIsConstant
            (Garden.Halo2.Synthesis.Cell.advice region Advice.A9 2) inv)
          (layouter_facts Garden.Orchard.circuit.synthesize))
      (Hlk0 :
        List.In (Fact.SelectorOn Selector.QLookup region 0)
          (layouter_facts Garden.Orchard.circuit.synthesize))
      (Hlk1 :
        List.In (Fact.SelectorOn Selector.QLookup region 1)
          (layouter_facts Garden.Orchard.circuit.synthesize))
      (Hbs1 :
        List.In (Fact.SelectorOn Selector.QBitshift region 1)
          (layouter_facts Garden.Orchard.circuit.synthesize))
      (Hrun0 : Γ.(Assignment.selector) Selector.QRunning region 0 = 0)
      (Hrun1 : Γ.(Assignment.selector) Selector.QRunning region 1 = 0) :
    0 <=
      UnOp.from
        (eval_cell Γ
          (Garden.Halo2.Synthesis.Cell.advice region Advice.A9 0)) <
      2 ^ bits.
  Proof.
    pose proof (holds_facts Γ Hcircuit) as Hfacts.
    pose proof (interpret_facts_In Γ _ _ Hfacts Hlk0) as Hlk0'.
    pose proof (interpret_facts_In Γ _ _ Hfacts Hlk1) as Hlk1'.
    pose proof (interpret_facts_In Γ _ _ Hfacts Hbs1) as Hbs1'.
    pose proof (interpret_facts_In Γ _ _ Hfacts Hconst) as Hconst'.
    cbn [interpret_fact] in Hlk0', Hlk1', Hbs1', Hconst'.
    rewrite advice_cell_read in Hconst'.
    pose proof (ten_bit_bound_at Γ Hcircuit region 0 Hlk0' Hrun0) as Ha.
    pose proof (ten_bit_bound_at Γ Hcircuit region 1 Hlk1' Hrun1) as Hb.
    pose proof (bitshift_gate_at Γ Hcircuit region Hbs1') as Hgate.
    rewrite advice_cell_read in Ha, Hb.
    rewrite Hconst' in Hgate.
    split; [apply Z.mod_pos_bound, Primes.pallas_p_pos |].
    unfold BinOp.mul, UnOp.from in Hgate, Hinv.
    apply (short_word_tighten Primes.pallas_p
      (UnOp.from (Γ.(Assignment.advice) Advice.A9 region 0))
      (UnOp.from (Γ.(Assignment.advice) Advice.A9 region 1))
      inv bits pallas_p_big Hbits Ha Hb Hinv Hgate).
  Qed.

  (** ** The row inventory

      Each short-range site is a three-row region emitting [QLookup] at
      offsets [0] and [1], [QBitshift] at offset [1], and a
      [ConstrainConstant] of the [A9] cell at offset [2] to the inverse of
      [2^bits].  [QRunning] is enabled nowhere inside it.  The record
      pins, per site, the region, the width, the inverse constant and the
      absolute placement row; the certificates below check the four facts,
      the placement, the inverse identity and the [QRunning] absence
      against the pinned data. *)

  Record ShortSite : Set := {
    ss_region : RegionId.t;
    ss_bits : Z;
    ss_inv : Z;
    ss_start : Z;
  }.

  (** The reified synthesis facts and the serialized event stream, bound
      as globals so each certificate's [vm_compute] forces them once per
      compilation unit. *)
  Definition orchard_facts : list (Fact.t columns RegionId.t) :=
    layouter_facts Garden.Orchard.circuit.synthesize.

  (** The [QRunning] selector's column index in the serialized grid. *)
  Definition qrunning_index : Z := 3.

  Lemma qrunning_index_eq :
    Index.indices.(Indices.selector) Selector.QRunning = qrunning_index.
  Proof.
    vm_cast_no_check (@eq_refl Z qrunning_index).
  Qed.

  Definition site_facts_ok (site : ShortSite) : bool :=
    andb
      (andb
        (List.existsb
          (fact_beq (Fact.SelectorOn Selector.QLookup site.(ss_region) 0))
          orchard_facts)
        (List.existsb
          (fact_beq (Fact.SelectorOn Selector.QLookup site.(ss_region) 1))
          orchard_facts))
      (andb
        (List.existsb
          (fact_beq (Fact.SelectorOn Selector.QBitshift site.(ss_region) 1))
          orchard_facts)
        (List.existsb
          (fact_beq
            (Fact.CellIsConstant
              (Garden.Halo2.Synthesis.Cell.advice site.(ss_region) Advice.A9 2)
              site.(ss_inv)))
          orchard_facts)).

  Definition site_start_ok (site : ShortSite) : bool :=
    region_start_of site.(ss_region) =? site.(ss_start).

  Definition site_inv_ok (site : ShortSite) : bool :=
    andb
      (andb (0 <=? site.(ss_bits)) (site.(ss_bits) <=? 10))
      ((2 ^ 10 * site.(ss_inv)) mod Primes.pallas_p =?
        2 ^ (10 - site.(ss_bits))).

  Definition site_qrunning_ok (site : ShortSite) : bool :=
    andb
      (List.forallb
        (fun e =>
          negb (selector_enabled_at qrunning_index site.(ss_start) e))
        orchard_events)
      (List.forallb
        (fun e =>
          negb (selector_enabled_at qrunning_index (site.(ss_start) + 1) e))
        orchard_events).

  (** ** The new-note family sites *)

  Definition site_nc_new_b0 : ShortSite := {|
    ss_region := NoteCommitNewWords.ncr RegionId.NoteCommit.RangeB0;
    ss_bits := 4;
    ss_inv := Garden.Halo2.halo2_gadgets.ecc.chip.constants.inv_two_pow_4;
    ss_start := 676;
  |}.

  Definition site_nc_new_b3 : ShortSite := {|
    ss_region := NoteCommitNewWords.ncr RegionId.NoteCommit.RangeB3;
    ss_bits := 4;
    ss_inv := Garden.Halo2.halo2_gadgets.ecc.chip.constants.inv_two_pow_4;
    ss_start := 679;
  |}.

  Definition site_nc_new_d2 : ShortSite := {|
    ss_region := NoteCommitNewWords.ncr RegionId.NoteCommit.RangeD2;
    ss_bits := 8;
    ss_inv := Garden.Halo2.halo2_gadgets.ecc.chip.constants.inv_two_pow_8;
    ss_start := 703;
  |}.

  Definition site_nc_new_e0 : ShortSite := {|
    ss_region := NoteCommitNewWords.ncr RegionId.NoteCommit.RangeE0;
    ss_bits := 6;
    ss_inv := Garden.Halo2.halo2_gadgets.ecc.chip.constants.inv_two_pow_6;
    ss_start := 709;
  |}.

  Definition site_nc_new_e1 : ShortSite := {|
    ss_region := NoteCommitNewWords.ncr RegionId.NoteCommit.RangeE1;
    ss_bits := 4;
    ss_inv := Garden.Halo2.halo2_gadgets.ecc.chip.constants.inv_two_pow_4;
    ss_start := 724;
  |}.

  Definition site_nc_new_g1 : ShortSite := {|
    ss_region := NoteCommitNewWords.ncr RegionId.NoteCommit.RangeG1;
    ss_bits := 9;
    ss_inv := Garden.Halo2.halo2_gadgets.ecc.chip.constants.inv_two_pow_9;
    ss_start := 727;
  |}.

  Definition site_nc_new_h0 : ShortSite := {|
    ss_region := NoteCommitNewWords.ncr RegionId.NoteCommit.RangeH0;
    ss_bits := 5;
    ss_inv := Garden.Halo2.halo2_gadgets.ecc.chip.constants.inv_two_pow_5;
    ss_start := 748;
  |}.

  Definition site_nc_new_gd_k0 : ShortSite := {|
    ss_region :=
      NoteCommitNewWords.nyr RegionId.NoteCommit.YSubject.GD
        RegionId.NoteCommit.YCanonicity.RangeK0;
    ss_bits := 9;
    ss_inv := Garden.Halo2.halo2_gadgets.ecc.chip.constants.inv_two_pow_9;
    ss_start := 754;
  |}.

  Definition site_nc_new_gd_k2 : ShortSite := {|
    ss_region :=
      NoteCommitNewWords.nyr RegionId.NoteCommit.YSubject.GD
        RegionId.NoteCommit.YCanonicity.RangeK2;
    ss_bits := 4;
    ss_inv := Garden.Halo2.halo2_gadgets.ecc.chip.constants.inv_two_pow_4;
    ss_start := 1621;
  |}.

  Definition site_nc_new_pkd_k0 : ShortSite := {|
    ss_region :=
      NoteCommitNewWords.nyr RegionId.NoteCommit.YSubject.PkD
        RegionId.NoteCommit.YCanonicity.RangeK0;
    ss_bits := 9;
    ss_inv := Garden.Halo2.halo2_gadgets.ecc.chip.constants.inv_two_pow_9;
    ss_start := 1624;
  |}.

  Definition site_nc_new_pkd_k2 : ShortSite := {|
    ss_region :=
      NoteCommitNewWords.nyr RegionId.NoteCommit.YSubject.PkD
        RegionId.NoteCommit.YCanonicity.RangeK2;
    ss_bits := 4;
    ss_inv := Garden.Halo2.halo2_gadgets.ecc.chip.constants.inv_two_pow_4;
    ss_start := 1630;
  |}.

  Definition nc_new_sites : list ShortSite := [
    site_nc_new_b0;
    site_nc_new_b3;
    site_nc_new_d2;
    site_nc_new_e0;
    site_nc_new_e1;
    site_nc_new_g1;
    site_nc_new_h0;
    site_nc_new_gd_k0;
    site_nc_new_gd_k2;
    site_nc_new_pkd_k0;
    site_nc_new_pkd_k2
  ].

  (** ** The certificates *)

  Lemma nc_new_facts_cert :
    List.forallb site_facts_ok nc_new_sites = true.
  Proof.
    vm_cast_no_check (@eq_refl bool true).
  Qed.

  Lemma nc_new_start_cert :
    List.forallb site_start_ok nc_new_sites = true.
  Proof.
    vm_cast_no_check (@eq_refl bool true).
  Qed.

  Lemma nc_new_inv_cert :
    List.forallb site_inv_ok nc_new_sites = true.
  Proof.
    vm_cast_no_check (@eq_refl bool true).
  Qed.

  Lemma nc_new_qrunning_cert :
    List.forallb site_qrunning_ok nc_new_sites = true.
  Proof.
    vm_cast_no_check (@eq_refl bool true).
  Qed.

  (** ** The generic per-site derivation

      Every premise of [short_range_bound] is read off the certificates at
      a site of the pinned list; the two [QRunning] readings go through
      [realized_selector_unset] at the site's absolute rows. *)

  Lemma site_short_bound
      (advice instance_ : Z -> Z -> Z) (grid : RawGrid.t)
      (Hreplay :
        apply_events orchard_events (initial_grid advice instance_) =
          Some grid)
      (Hcircuit :
        Holds (realize Index.indices region_start_of grid))
      (sites : list ShortSite)
      (Hfacts_cert : List.forallb site_facts_ok sites = true)
      (Hstart_cert : List.forallb site_start_ok sites = true)
      (Hinv_cert : List.forallb site_inv_ok sites = true)
      (Hrun_cert : List.forallb site_qrunning_ok sites = true)
      (site : ShortSite) (Hin : List.In site sites) :
    0 <=
      UnOp.from
        (eval_cell (realize Index.indices region_start_of grid)
          (Garden.Halo2.Synthesis.Cell.advice site.(ss_region) Advice.A9 0)) <
      2 ^ site.(ss_bits).
  Proof.
    pose proof
      (proj1 (List.forallb_forall site_facts_ok sites) Hfacts_cert site Hin)
      as Hfacts.
    pose proof
      (proj1 (List.forallb_forall site_start_ok sites) Hstart_cert site Hin)
      as Hstart.
    pose proof
      (proj1 (List.forallb_forall site_inv_ok sites) Hinv_cert site Hin)
      as Hinv.
    pose proof
      (proj1 (List.forallb_forall site_qrunning_ok sites) Hrun_cert site Hin)
      as Hrun.
    unfold site_facts_ok in Hfacts.
    apply andb_true_iff in Hfacts.
    destruct Hfacts as [Hfacts_lk Hfacts_bs].
    apply andb_true_iff in Hfacts_lk.
    destruct Hfacts_lk as [Hlk0 Hlk1].
    apply andb_true_iff in Hfacts_bs.
    destruct Hfacts_bs as [Hbs1 Hconst].
    unfold site_start_ok in Hstart.
    apply Z.eqb_eq in Hstart.
    unfold site_inv_ok in Hinv.
    apply andb_true_iff in Hinv.
    destruct Hinv as [Hbits Hinv_eq].
    apply andb_true_iff in Hbits.
    destruct Hbits as [Hbits_lo Hbits_hi].
    apply Z.leb_le in Hbits_lo, Hbits_hi.
    apply Z.eqb_eq in Hinv_eq.
    unfold site_qrunning_ok in Hrun.
    apply andb_true_iff in Hrun.
    destruct Hrun as [Hrun0 Hrun1].
    apply (short_range_bound
      (realize Index.indices region_start_of grid) Hcircuit
      site.(ss_region) site.(ss_bits) site.(ss_inv)
      (conj Hbits_lo Hbits_hi) Hinv_eq
      (fact_In_of_beq _ _ Hconst)
      (fact_In_of_beq _ _ Hlk0)
      (fact_In_of_beq _ _ Hlk1)
      (fact_In_of_beq _ _ Hbs1)).
    - cbn [realize Assignment.selector].
      rewrite qrunning_index_eq, Hstart, Z.add_0_r.
      exact (realized_selector_unset orchard_events advice instance_ grid
        qrunning_index site.(ss_start) Hreplay Hrun0).
    - cbn [realize Assignment.selector].
      rewrite qrunning_index_eq, Hstart.
      exact (realized_selector_unset orchard_events advice instance_ grid
        qrunning_index (site.(ss_start) + 1) Hreplay Hrun1).
  Qed.

  (** ** The new-note family, from operational acceptance

      [orchard_operational_sound] carries replay success and ideal
      acceptance to the relational [Holds] of the realized assignment; the
      site derivations supply the eleven bounds the relational model
      leaves free. *)

  Lemma nc_new_site_bound
      (advice instance_ : Z -> Z -> Z) (grid : RawGrid.t)
      (Hreplay :
        apply_events orchard_events (initial_grid advice instance_) =
          Some grid)
      (Hmock :
        mock_prover_accepts orchard_indexed_system orchard_events grid
          orchard_table_rows)
      (site : ShortSite) (Hin : List.In site nc_new_sites) :
    0 <=
      UnOp.from
        (eval_cell (realize Index.indices region_start_of grid)
          (Garden.Halo2.Synthesis.Cell.advice site.(ss_region) Advice.A9 0)) <
      2 ^ site.(ss_bits).
  Proof.
    exact (site_short_bound advice instance_ grid Hreplay
      (orchard_operational_sound advice instance_ grid Hreplay Hmock)
      nc_new_sites nc_new_facts_cert nc_new_start_cert nc_new_inv_cert
      nc_new_qrunning_cert site Hin).
  Qed.

  Theorem note_commit_new_short_lookup_ok_operational
      (advice instance_ : Z -> Z -> Z) (grid : RawGrid.t)
      (Hreplay :
        apply_events orchard_events (initial_grid advice instance_) =
          Some grid)
      (Hmock :
        mock_prover_accepts orchard_indexed_system orchard_events grid
          orchard_table_rows) :
    NoteCommitNewWords.note_commit_new_short_lookup_ok
      (realize Index.indices region_start_of grid).
  Proof.
    unfold NoteCommitNewWords.note_commit_new_short_lookup_ok,
      NoteCommitNewWords.short_ok, NoteCommitNewWords.val,
      NoteCommitNewWords.adv.
    split;
      [exact (nc_new_site_bound advice instance_ grid Hreplay Hmock
        site_nc_new_b0
        ltac:(unfold nc_new_sites; repeat (first [left; reflexivity | right]))) |].
    split;
      [exact (nc_new_site_bound advice instance_ grid Hreplay Hmock
        site_nc_new_b3
        ltac:(unfold nc_new_sites; repeat (first [left; reflexivity | right]))) |].
    split;
      [exact (nc_new_site_bound advice instance_ grid Hreplay Hmock
        site_nc_new_d2
        ltac:(unfold nc_new_sites; repeat (first [left; reflexivity | right]))) |].
    split;
      [exact (nc_new_site_bound advice instance_ grid Hreplay Hmock
        site_nc_new_e0
        ltac:(unfold nc_new_sites; repeat (first [left; reflexivity | right]))) |].
    split;
      [exact (nc_new_site_bound advice instance_ grid Hreplay Hmock
        site_nc_new_e1
        ltac:(unfold nc_new_sites; repeat (first [left; reflexivity | right]))) |].
    split;
      [exact (nc_new_site_bound advice instance_ grid Hreplay Hmock
        site_nc_new_g1
        ltac:(unfold nc_new_sites; repeat (first [left; reflexivity | right]))) |].
    split;
      [exact (nc_new_site_bound advice instance_ grid Hreplay Hmock
        site_nc_new_h0
        ltac:(unfold nc_new_sites; repeat (first [left; reflexivity | right]))) |].
    split;
      [exact (nc_new_site_bound advice instance_ grid Hreplay Hmock
        site_nc_new_gd_k0
        ltac:(unfold nc_new_sites; repeat (first [left; reflexivity | right]))) |].
    split;
      [exact (nc_new_site_bound advice instance_ grid Hreplay Hmock
        site_nc_new_gd_k2
        ltac:(unfold nc_new_sites; repeat (first [left; reflexivity | right]))) |].
    split;
      [exact (nc_new_site_bound advice instance_ grid Hreplay Hmock
        site_nc_new_pkd_k0
        ltac:(unfold nc_new_sites; repeat (first [left; reflexivity | right]))) |].
    exact (nc_new_site_bound advice instance_ grid Hreplay Hmock
      site_nc_new_pkd_k2
      ltac:(unfold nc_new_sites; repeat (first [left; reflexivity | right]))).
  Qed.
End OrchardShortLookupClosure.
