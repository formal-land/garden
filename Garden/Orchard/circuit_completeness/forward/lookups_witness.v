(** * Forward lemmas: the lookup obligations and the witness facts

    The [family_lookups_ok] and [witness_facts_forward_ok] obligations of the
    forward statement API ([forward/api.v]), proved symbolically over every
    valid, nondegenerate honest input.

    Lookup arguments of the configured system (pasted literals, pinned by
    [lookups_eq]):

    - [range_check_arg] — the 10-bit range check ([lookup_range_check.v]):
      one pair on [Lookup.TableIdx], gated by [QLookup] with the
      [QRunning]-selected running-sum word [z_cur − 2^10·z_next] or the short
      word [z_cur];
    - [sins1_arg] / [sins2_arg] — the two Sinsemilla generator-table
      arguments ([sinsemilla/chip.v]): the [(word, x_p, y_p)] triple against
      [(TableIdx, TableX, TableY)], gated by [QSinsemilla1_1] /
      [QSinsemilla1_2].

    Structure:

    - the table plane ([lookup_plane_idx]): the honest lookup plane holds the
      loaded generator table, and the index column is the identity on rows
      [0..1023];
    - two generic site lemmas ([running_site_lemma], [short_site_lemma])
      reduce every range-check site to (a) the generator's advice shape at
      the site, (b) a range bound on the decomposed value, and (c) a
      [vm_compute] certificate for the selector plane at the site's rows;
    - the per-site instances cover every enabled range-check row: the
      nullifier and variable-base overflow lookups, the [Commit^ivk] and
      [NoteCommit] canonicity lookups and short range checks, the
      y-canonicity blocks, and the Merkle [b_1]/[b_2] short checks;
    - the Sinsemilla generator-table sites (the hash-region rounds) are the
      five [sins_site_sound] leaves, proved in the nested module
      [SinsemillaSites] from one generic site lemma: the loaded table's
      index/abscissa/ordinate columns read back as the identity and the two
      [sinsemilla_s] coordinates, the [bits]-column telescoping supplies the
      round word against the [q_sinsemilla2] piece schedule, and the [y_p]
      reconstruction runs on the round algebra of [forward/sinsemilla.v]
      under the non-vertical chords of [nondegenerate w];
    - the witness facts split by the Boolean [fact_trivial]: the
      self-copy facts (identical source and target cell) hold by
      reflexivity for any assignment, and the non-self-copy facts are
      pinned as the literal [nt_closed ++ nt_open], covered by one
      input-independent [vm_compute] scan ([nt_cover]).  [nt_closed] is
      proved by group: the copies whose two cell addresses the advice
      dispatch sends to one reader expression, the blinding-leg
      boundaries, and the Merkle running-node chain.  [nt_open] — the
      facts whose two sides are different derivations of one value — is
      the [Admitted] leaf [open_witness_facts].

    Exports: [lookups_forward_ok : family_lookups_ok all_families] (the
    [Hlookups] side of [completeness_statement_of_families]) and
    [witness_facts_ok : witness_facts_forward_ok] (complete modulo
    [open_witness_facts]).

    Every [vm_compute] certificate here is input-independent (facts, enabled
    points and selector membership only — never a [Γ] advice evaluation), so
    this file stays off the heavy-certificate cost map. *)

Require Import Garden.Halo2.main.
Require Import Garden.Halo2.lemmas.
Require Import Garden.Halo2.Synthesis.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.complete.
Require Import Garden.Field.Field.
Require Import Garden.Plonky3.M.
Require Import Garden.EllipticCurve.Weierstrass.
Require Import Garden.EllipticCurve.Pallas.
Require Import Garden.Halo2.PallasModel.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.spec.
Require Import Garden.Halo2.halo2_gadgets.sinsemilla.spec.
Require Garden.Halo2.halo2_gadgets.sinsemilla.chip.
Require Import Garden.Orchard.columns.
Require Import Garden.Orchard.regions.
Require Import Garden.Orchard.decidable_eq.
Require Import Garden.Field.Pow2.
Require Import Garden.Orchard.circuit_proof.inputs.
Require Import Garden.Orchard.circuit_completeness.generator.witness_input.
Require Import Garden.Orchard.circuit_completeness.generator.certificates.
Require Import Garden.Orchard.circuit_completeness.generator.advice_merkle_sinsemilla.
Require Import Garden.Orchard.circuit_completeness.generator.advice_ecc_muls.
Require Import Garden.Orchard.circuit_completeness.generator.tables_vb.
Require Import Garden.Orchard.circuit_completeness.generator.tables_nc.
Require Import Garden.Orchard.circuit_completeness.generator.tables.
Require Import Garden.Orchard.circuit_completeness.generator.honest_assignment.
Require Import Garden.Orchard.circuit_completeness.instance.defs.
Require Import Garden.Orchard.circuit_completeness.forward.api.
Require Import Garden.Orchard.circuit_completeness.forward.sinsemilla.
Require Import Garden.Orchard.circuit_completeness.forward.witness.bits_column.
Require Import Garden.Orchard.circuit_completeness.forward.witness.chain_outputs.
Require Import Garden.Orchard.circuit_completeness.forward.witness.slice_bounds.
Require Import Garden.Orchard.circuit_completeness.forward.witness.fixed_legs.
Require Import Garden.Orchard.circuit_completeness.forward.witness.var_base.
Require Import Garden.Field.Div.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.add_proof.
Require Import Garden.Halo2.halo2_gadgets.sinsemilla.hash_to_point_proof.
Require Garden.Orchard.circuit.
Require Garden.Orchard.protocol_spec.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Lists.List.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.Setoids.Setoid.
Require Import Stdlib.Classes.Morphisms.

Import ListNotations.
Global Open Scope Z_scope.

#[local] Existing Instance Primes.PallasPIsPrime.

Module OrchardForwardLookupsWitness.
  Import OrchardWitnessInput.
  Import OrchardCompletenessInstanceDefs.
  Import OrchardCompletenessForward.

  (** ** Shared abbreviations *)

  Notation Γw w := (OrchardHonestAssignment.honest_assignment w).

  (** The enabled-point membership of the honest selector plane. *)
  Definition memb (sel : Selector.t) (region : RegionId.t) (row : Z) : bool :=
    Complete.enabled_memb OrchardHonestAssignment.selector_eqb
      OrchardHonestAssignment.region_eqb OrchardHonestAssignment.facts
      sel region row.

  (** The three planes of the generated assignment, read off by
      definitional equality. *)
  Lemma selector_plane (w : HonestInput) (sel : Selector.t)
      (region : RegionId.t) (row : Z) :
    (Γw w).(Assignment.selector) sel region row =
    if memb sel region row then 1 else 0.
  Proof. reflexivity. Qed.

  Lemma advice_plane (w : HonestInput) (col : Advice.t)
      (region : RegionId.t) (row : Z) :
    (Γw w).(Assignment.advice) col region row =
    OrchardCompletenessTables.advice_t w
      (OrchardCompletenessTables.tables_of w) col region row.
  Proof. reflexivity. Qed.

  Lemma lookup_plane (w : HonestInput) (col : Lookup.t) (row : Z) :
    (Γw w).(Assignment.lookup) col row =
    Complete.table_value OrchardHonestAssignment.lookup_eqb
      OrchardHonestAssignment.facts col row.
  Proof. reflexivity. Qed.

  (** ** The configured lookup arguments (pasted literals) *)

  Definition range_check_arg : LookupArgument.t columns := {|
    LookupArgument.pairs :=
      [(Expression.Selector Selector.QLookup
        ✖️ (Expression.Selector Selector.QRunning
            ✖️ (Expression.Advice Advice.A9 {| Rotation.offset := 0 |}
                ➖ Expression.Advice Advice.A9
                    {| Rotation.offset := 1 |}
                  ● 1024)
            ➕ (Expression.Constant 1
               ➖ Expression.Selector Selector.QRunning)
              ✖️ Expression.Advice Advice.A9 {| Rotation.offset := 0 |}),
        Lookup.TableIdx)];
  |}.

  Definition sins1_arg : LookupArgument.t columns := {|
    LookupArgument.pairs :=
      [(Expression.Selector Selector.QSinsemilla1_1
        ✖️ (Expression.Advice Advice.A2 {| Rotation.offset := 0 |}
            ➖ (Expression.Fixed Fixed.QSinsemilla2_1
                 {| Rotation.offset := 0 |}
               ➖ Expression.Fixed Fixed.QSinsemilla2_1
                   {| Rotation.offset := 0 |}
                 ✖️ (Expression.Fixed Fixed.QSinsemilla2_1
                       {| Rotation.offset := 0 |}
                     ➖ Expression.Constant 1))
              ✖️ Expression.Advice Advice.A2 {| Rotation.offset := 1 |}
              ● 1024),
        Lookup.TableIdx);
       (Expression.Selector Selector.QSinsemilla1_1
        ✖️ Expression.Advice Advice.A1 {| Rotation.offset := 0 |}
        ➕ (Expression.Constant 1
           ➖ Expression.Selector Selector.QSinsemilla1_1)
          ● 6200097879647205583499851243213148560621730003917924543823561700220554504799,
        Lookup.TableX);
       (Expression.Selector Selector.QSinsemilla1_1
        ✖️ ((Expression.Advice Advice.A3 {| Rotation.offset := 0 |}
             ➕ Expression.Advice Advice.A4 {| Rotation.offset := 0 |})
            ✖️ (Expression.Advice Advice.A0 {| Rotation.offset := 0 |}
                ➖ (Expression.Advice Advice.A3
                     {| Rotation.offset := 0 |}
                   ✖️ Expression.Advice Advice.A3
                        {| Rotation.offset := 0 |}
                   ➖ Expression.Advice Advice.A0
                       {| Rotation.offset := 0 |}
                   ➖ Expression.Advice Advice.A1
                       {| Rotation.offset := 0 |}))
            ● 14474011154664524427946373126085988481681528240970780357977338382174983815169
            ➖ Expression.Advice Advice.A3 {| Rotation.offset := 0 |}
              ✖️ (Expression.Advice Advice.A0
                    {| Rotation.offset := 0 |}
                  ➖ Expression.Advice Advice.A1
                      {| Rotation.offset := 0 |}))
        ➕ (Expression.Constant 1
           ➖ Expression.Selector Selector.QSinsemilla1_1)
          ● 21285653556795296467031706491948305595095309413618206259690549906869937136771,
        Lookup.TableY)];
  |}.

  Definition sins2_arg : LookupArgument.t columns := {|
    LookupArgument.pairs :=
      [(Expression.Selector Selector.QSinsemilla1_2
        ✖️ (Expression.Advice Advice.A7 {| Rotation.offset := 0 |}
            ➖ (Expression.Fixed Fixed.QSinsemilla2_2
                 {| Rotation.offset := 0 |}
               ➖ Expression.Fixed Fixed.QSinsemilla2_2
                   {| Rotation.offset := 0 |}
                 ✖️ (Expression.Fixed Fixed.QSinsemilla2_2
                       {| Rotation.offset := 0 |}
                     ➖ Expression.Constant 1))
              ✖️ Expression.Advice Advice.A7 {| Rotation.offset := 1 |}
              ● 1024),
        Lookup.TableIdx);
       (Expression.Selector Selector.QSinsemilla1_2
        ✖️ Expression.Advice Advice.A6 {| Rotation.offset := 0 |}
        ➕ (Expression.Constant 1
           ➖ Expression.Selector Selector.QSinsemilla1_2)
          ● 6200097879647205583499851243213148560621730003917924543823561700220554504799,
        Lookup.TableX);
       (Expression.Selector Selector.QSinsemilla1_2
        ✖️ ((Expression.Advice Advice.A8 {| Rotation.offset := 0 |}
             ➕ Expression.Advice Advice.A9 {| Rotation.offset := 0 |})
            ✖️ (Expression.Advice Advice.A5 {| Rotation.offset := 0 |}
                ➖ (Expression.Advice Advice.A8
                     {| Rotation.offset := 0 |}
                   ✖️ Expression.Advice Advice.A8
                        {| Rotation.offset := 0 |}
                   ➖ Expression.Advice Advice.A5
                       {| Rotation.offset := 0 |}
                   ➖ Expression.Advice Advice.A6
                       {| Rotation.offset := 0 |}))
            ● 14474011154664524427946373126085988481681528240970780357977338382174983815169
            ➖ Expression.Advice Advice.A8 {| Rotation.offset := 0 |}
              ✖️ (Expression.Advice Advice.A5
                    {| Rotation.offset := 0 |}
                  ➖ Expression.Advice Advice.A6
                      {| Rotation.offset := 0 |}))
        ➕ (Expression.Constant 1
           ➖ Expression.Selector Selector.QSinsemilla1_2)
          ● 21285653556795296467031706491948305595095309413618206259690549906869937136771,
        Lookup.TableY)];
  |}.

  Lemma lookups_eq :
    system.(ConstraintSystem.lookups) = [range_check_arg; sins1_arg; sins2_arg].
  Proof.
    vm_cast_no_check
      (@eq_refl (list (LookupArgument.t columns))
        [range_check_arg; sins1_arg; sins2_arg]).
  Qed.

  (** ** The loaded table: the index column is the identity

      The honest lookup plane carries the loaded generator table
      ([load_generator_table]); on rows [0..1023] the [TableIdx] column reads
      back the row number. *)

  Lemma table_idx_entry :
    Complete.table_lookup OrchardHonestAssignment.lookup_eqb
      (Complete.table_entries OrchardHonestAssignment.facts) Lookup.TableIdx =
    Some (Garden.Halo2.halo2_gadgets.sinsemilla.chip.generator_table_indexes, 0).
  Proof.
    vm_cast_no_check
      (@eq_refl (option (list Z * Z))
        (Some
          (Garden.Halo2.halo2_gadgets.sinsemilla.chip.generator_table_indexes,
           0))).
  Qed.

  Lemma lookup_plane_idx (w : HonestInput) (r : Z) :
    0 <= r < 1024 ->
    (Γw w).(Assignment.lookup) Lookup.TableIdx r = r.
  Proof.
    intros Hr.
    rewrite lookup_plane.
    unfold Complete.table_value.
    rewrite table_idx_entry.
    unfold value_at_row,
      Garden.Halo2.halo2_gadgets.sinsemilla.chip.generator_table_indexes.
    change (Z.to_nat (2 ^ Garden.Halo2.halo2_gadgets.sinsemilla.chip.sinsemilla_k))
      with 1024%nat.
    change 0 with (Z.of_nat 0%nat).
    rewrite List.map_nth.
    rewrite List.seq_nth by lia.
    lia.
  Qed.

  (** ** Field-arithmetic cores of the two range-check shapes *)

  Lemma pallas_p_big : 2 ^ 250 < Primes.pallas_p.
  Proof. unfold Primes.pallas_p, Primes.t_p. lia. Qed.

  Lemma pallas_p_1024 : 1024 < Primes.pallas_p.
  Proof. pose proof pallas_p_big. lia. Qed.

  (** The evaluated running-sum pair at an active row: with both selectors
      at [1], the pair expression computes the 10-bit digit
      [z_cur mod 2^10]. *)
  Lemma range_word_arith (x row : Z)
      (Hx : 0 <= x < Primes.pallas_p) (Hrow : 0 <= row) :
    BinOp.mul (UnOp.from 1)
      (BinOp.add
        (BinOp.mul (UnOp.from 1)
          (BinOp.sub (UnOp.from (x / 2 ^ (10 * row)))
            (BinOp.mul (UnOp.from (x / 2 ^ (10 * (row + 1))))
              (UnOp.from 1024))))
        (BinOp.mul (BinOp.sub (UnOp.from 1) (UnOp.from 1))
          (UnOp.from (x / 2 ^ (10 * row)))))
    = (x / 2 ^ (10 * row)) mod 1024.
  Proof.
    pose proof pallas_p_1024 as Hp.
    assert (Hpow : 0 < 2 ^ (10 * row))
      by (apply Z.pow_pos_nonneg; lia).
    set (a := x / 2 ^ (10 * row)).
    set (b := x / 2 ^ (10 * (row + 1))).
    assert (Ha : 0 <= a <= x).
    { subst a. split.
      - apply Z.div_pos; lia.
      - apply Z.div_le_upper_bound; [lia | clear -Hx Hpow; nia]. }
    assert (Hb : b = a / 1024).
    { subst a b.
      replace (10 * (row + 1)) with (10 * row + 10) by lia.
      rewrite Z.pow_add_r by lia.
      rewrite Z.div_div by lia.
      reflexivity. }
    assert (Hbr : 0 <= b <= a).
    { rewrite Hb. split.
      - apply Z.div_pos; lia.
      - apply Z.div_le_upper_bound; [lia | clear -Ha; nia]. }
    assert (Hsplit : a = 1024 * b + a mod 1024).
    { rewrite Hb. apply Z.div_mod. lia. }
    assert (Hm : 0 <= a mod 1024 < 1024)
      by (apply Z.mod_pos_bound; lia).
    unfold BinOp.mul, BinOp.add, BinOp.sub, UnOp.from.
    repeat first
      [ rewrite <- Zmult_mod
      | rewrite Zmult_mod_idemp_l
      | rewrite Zmult_mod_idemp_r
      | rewrite <- Zplus_mod
      | rewrite Zplus_mod_idemp_l
      | rewrite Zplus_mod_idemp_r
      | rewrite <- Zminus_mod
      | rewrite Zminus_mod_idemp_l
      | rewrite Zminus_mod_idemp_r
      | rewrite Zmod_mod ].
    rewrite (Z.mod_small 1) by lia.
    rewrite (Z.mod_small a) by lia.
    rewrite (Z.mod_small (b * 1024)) by lia.
    repeat first
      [ rewrite <- Zmult_mod
      | rewrite Zmult_mod_idemp_l
      | rewrite Zmult_mod_idemp_r
      | rewrite <- Zplus_mod
      | rewrite Zplus_mod_idemp_l
      | rewrite Zplus_mod_idemp_r
      | rewrite <- Zminus_mod
      | rewrite Zminus_mod_idemp_l
      | rewrite Zminus_mod_idemp_r
      | rewrite Zmod_mod ].
    rewrite !Z.mul_1_l.
    rewrite Z.sub_diag, Z.mul_0_l.
    rewrite Zmod_0_l.
    rewrite Z.add_0_r.
    rewrite Zmod_mod.
    replace (a - b * 1024) with (a mod 1024) by lia.
    apply Z.mod_small; lia.
  Qed.

  (** The evaluated short pair at an active row: with [QRunning] off, the
      pair expression computes the checked word itself; the running branch
      is killed by the zero selector whatever its next-row operand [W]. *)
  Lemma short_word_arith (W v : Z) (Hv : 0 <= v < 1024) :
    BinOp.mul (UnOp.from 1)
      (BinOp.add (BinOp.mul (UnOp.from 0) W)
        (BinOp.mul (BinOp.sub (UnOp.from 1) (UnOp.from 0)) (UnOp.from v)))
    = v.
  Proof.
    pose proof pallas_p_1024 as Hp.
    unfold BinOp.mul, BinOp.add, BinOp.sub, UnOp.from.
    repeat first
      [ rewrite <- Zmult_mod
      | rewrite Zmult_mod_idemp_l
      | rewrite Zmult_mod_idemp_r
      | rewrite <- Zplus_mod
      | rewrite Zplus_mod_idemp_l
      | rewrite Zplus_mod_idemp_r
      | rewrite <- Zminus_mod
      | rewrite Zminus_mod_idemp_l
      | rewrite Zminus_mod_idemp_r
      | rewrite Zmod_mod ].
    rewrite (Z.mod_small 0) by lia.
    rewrite (Z.mod_small 1) by lia.
    rewrite Zmod_0_l.
    rewrite Z.sub_0_r.
    rewrite Z.add_0_l.
    rewrite !Z.mul_1_l.
    rewrite Zmod_mod.
    apply Z.mod_small; lia.
  Qed.

  (** ** Site soundness: the per-(region, rows) obligations *)

  (** A running-sum lookup site: rows [0 .. n-1] of [region] satisfy the
      range-check argument. *)
  Definition running_site_sound (region : RegionId.t) (n : Z) : Prop :=
    forall w : HonestInput,
      valid w -> nondegenerate w ->
      forall row : Z,
        0 <= row < n ->
        eval_lookup_argument (Γw w) (region, row) 1024 range_check_arg.

  (** A short range-check site: rows [0] and [1] of [region] satisfy the
      range-check argument. *)
  Definition short_site_sound (region : RegionId.t) : Prop :=
    forall w : HonestInput,
      valid w -> nondegenerate w ->
      forall row : Z,
        row = 0 \/ row = 1 ->
        eval_lookup_argument (Γw w) (region, row) 1024 range_check_arg.

  (** A Sinsemilla hash-region site: rows [0 .. n-1] of [region] satisfy the
      generator-table argument [arg]. *)
  Definition sins_site_sound (arg : LookupArgument.t columns)
      (region : RegionId.t) (n : Z) : Prop :=
    forall w : HonestInput,
      valid w -> nondegenerate w ->
      forall row : Z,
        0 <= row < n ->
        eval_lookup_argument (Γw w) (region, row) 1024 arg.

  (** ** The generic running-site lemma *)

  Lemma running_site_lemma (region : RegionId.t) (n : Z)
      (z0 : HonestInput -> Z)
      (Hadv : forall (w : HonestInput) (row : Z),
        OrchardCompletenessTables.advice_t w
          (OrchardCompletenessTables.tables_of w) Advice.A9 region row =
        OrchardNoteCommitCells.running_lookup_advice (z0 w) n Advice.A9 row)
      (Hz : forall w : HonestInput,
        valid w -> nondegenerate w -> 0 <= z0 w < Primes.pallas_p)
      (Hsel : List.forallb
        (fun j =>
          memb Selector.QLookup region (Z.of_nat j) &&
          memb Selector.QRunning region (Z.of_nat j))
        (List.seq 0 (Z.to_nat n)) = true) :
    running_site_sound region n.
  Proof.
    intros w Hv Hnd row Hrow.
    pose proof
      (forallb_seq_sound _ 0 (Z.to_nat n) Hsel (Z.to_nat row)
        ltac:(lia)) as Hs.
    lazy beta in Hs.
    rewrite Z2Nat.id in Hs by lia.
    apply andb_true_iff in Hs.
    destruct Hs as [Hql Hqr].
    unfold eval_lookup_argument.
    exists ((z0 w / 2 ^ (10 * row)) mod 1024).
    assert (Hwd : 0 <= (z0 w / 2 ^ (10 * row)) mod 1024 < 1024)
      by (apply Z.mod_pos_bound; lia).
    split; [lia |].
    apply List.Forall_cons; [| apply List.Forall_nil].
    rewrite lookup_plane_idx by lia.
    cbn [eval_expression eval_selector].
    unfold rotated_row.
    cbn [Rotation.offset].
    rewrite Z.add_0_r.
    rewrite !selector_plane, !advice_plane.
    rewrite Hql, Hqr.
    rewrite !Hadv.
    unfold OrchardNoteCommitCells.running_lookup_advice.
    assert (Hg1 : (0 <=? row) && (row <=? n) = true)
      by (apply andb_true_iff; split; apply Z.leb_le; lia).
    assert (Hg2 : (0 <=? row + 1) && (row + 1 <=? n) = true)
      by (apply andb_true_iff; split; apply Z.leb_le; lia).
    rewrite Hg1, Hg2.
    change (if true then 1 else 0) with 1.
    exact (range_word_arith (z0 w) row (Hz w Hv Hnd) ltac:(lia)).
  Qed.

  (** ** The generic short-site lemma *)

  Lemma short_site_lemma (region : RegionId.t)
      (v : HonestInput -> Z) (f : Z)
      (Hf : 0 < f)
      (Hadv0 : forall w : HonestInput,
        OrchardCompletenessTables.advice_t w
          (OrchardCompletenessTables.tables_of w) Advice.A9 region 0 = v w)
      (Hadv1 : forall w : HonestInput,
        OrchardCompletenessTables.advice_t w
          (OrchardCompletenessTables.tables_of w) Advice.A9 region 1 =
        v w * f)
      (Hv : forall w : HonestInput,
        valid w -> nondegenerate w -> 0 <= v w /\ v w * f < 1024)
      (Hsel :
        memb Selector.QLookup region 0 && memb Selector.QLookup region 1 &&
        negb (memb Selector.QRunning region 0) &&
        negb (memb Selector.QRunning region 1) = true) :
    short_site_sound region.
  Proof.
    intros w Hv' Hnd row Hrow.
    apply andb_true_iff in Hsel; destruct Hsel as [Hsel Hqr1].
    apply andb_true_iff in Hsel; destruct Hsel as [Hsel Hqr0].
    apply andb_true_iff in Hsel; destruct Hsel as [Hql0 Hql1].
    apply negb_true_iff in Hqr0.
    apply negb_true_iff in Hqr1.
    destruct (Hv w Hv' Hnd) as [Hv0 Hv1].
    assert (Hvf : v w <= v w * f) by (clear -Hf Hv0; nia).
    unfold eval_lookup_argument.
    exists (if row =? 0 then v w else v w * f).
    split.
    { destruct (row =? 0); lia. }
    apply List.Forall_cons; [| apply List.Forall_nil].
    rewrite lookup_plane_idx by (destruct (row =? 0); lia).
    cbn [eval_expression eval_selector].
    unfold rotated_row.
    cbn [Rotation.offset].
    rewrite Z.add_0_r.
    rewrite !selector_plane, !advice_plane.
    destruct Hrow as [-> | ->].
    - rewrite Hql0, Hqr0.
      rewrite Hadv0.
      change (0 =? 0) with true.
      change (if true then 1 else 0) with 1.
      change (if false then 1 else 0) with 0.
      apply short_word_arith; lia.
    - rewrite Hql1, Hqr1.
      rewrite Hadv1.
      change (1 =? 0) with false.
      change (if true then 1 else 0) with 1.
      change (if false then 1 else 0) with 0.
      apply short_word_arith; lia.
  Qed.

  (** ** Range facts for the site values *)

  Lemma div_bound (b d hi : Z) (Hb : 0 <= b < d * hi) (Hd : 0 < d) :
    0 <= b / d < hi.
  Proof.
    split.
    - apply Z.div_pos; lia.
    - apply Z.div_lt_upper_bound; lia.
  Qed.

  (** The overflow-block running-sum head [s] is a reduced field element. *)
  Lemma vb_s_range (alpha : Z) (B : Point.t) :
    0 <=
      OrchardVarBaseTables.vb_s (OrchardVarBaseTables.vb_columns alpha B) <
      Primes.pallas_p.
  Proof.
    unfold OrchardVarBaseTables.vb_columns.
    cbv zeta.
    repeat match goal with
    | |- context [match ?t with pair _ _ => _ end] => destruct t
    end.
    cbn [OrchardVarBaseTables.vb_s].
    apply Z.mod_pos_bound.
    exact Primes.pallas_p_pos.
  Qed.

  (** ** The running-site values

      Each [z0] definition spells the exact head value of the site's
      generator formulas, so the advice-shape premise of
      [running_site_lemma] holds by reflexivity. *)

  (** The nullifier canonicity head [α'_0] ([advice_nullifier_t]). *)
  Definition alpha_z0 (w : HonestInput) : Z :=
    let nscalar :=
      OrchardCompletenessTables.t_nullifier_scalar
        (OrchardCompletenessTables.tables_of w) in
    (nscalar - running_sum_at nscalar 84%nat * 2 ^ 252 + 2 ^ 130 -
     Primes.t_p) mod Primes.pallas_p.

  (** The packed [Commit^ivk] message of the honest input. *)
  Definition civk_pk (w : HonestInput) : Z :=
    OrchardNoteCommitCells.civk_packed
      (EccSpec.extract_x (hi_ak w)) (hi_nk w).

  (** The packed old-note and new-note messages of the honest input
      ([ρ_new] is the hoisted nullifier). *)
  Definition nc_pk_old (w : HonestInput) : Z :=
    OrchardNoteCommitCells.nc_packed
      (hi_g_d_old w) (hi_pk_d_old w) (hi_v_old w) (hi_rho_old w)
      (hi_psi_old w).

  Definition nc_pk_new (w : HonestInput) : Z :=
    OrchardNoteCommitCells.nc_packed
      (hi_g_d_new w) (hi_pk_d_new w) (hi_v_new w)
      (OrchardCompletenessTables.t_nf_spec
        (OrchardCompletenessTables.tables_of w))
      (hi_psi_new w).

  (** The packed note message of either note. *)
  Definition nc_pk_of (which : RegionId.NoteCommit.Which.t)
      (w : HonestInput) : Z :=
    match which with
    | RegionId.NoteCommit.Which.Old => nc_pk_old w
    | RegionId.NoteCommit.Which.New => nc_pk_new w
    end.

  (** The compressed point of a y-canonicity block. *)
  Definition nc_y_of (which : RegionId.NoteCommit.Which.t)
      (subject : RegionId.NoteCommit.YSubject.t) (w : HonestInput) : Z :=
    match which, subject with
    | RegionId.NoteCommit.Which.Old, RegionId.NoteCommit.YSubject.GD =>
        Point.y (hi_g_d_old w)
    | RegionId.NoteCommit.Which.Old, RegionId.NoteCommit.YSubject.PkD =>
        Point.y (hi_pk_d_old w)
    | RegionId.NoteCommit.Which.New, RegionId.NoteCommit.YSubject.GD =>
        Point.y (hi_g_d_new w)
    | RegionId.NoteCommit.Which.New, RegionId.NoteCommit.YSubject.PkD =>
        Point.y (hi_pk_d_new w)
    end.

  (** The [b]-piece word of a Merkle layer, as the hoisted record spells
      it. *)
  Definition merkle_b_word_t (w : HonestInput)
      (layer : RegionId.Merkle.Layer.t) : Z :=
    List.nth 26
      (OrchardCompletenessTables.hd_words
        (OrchardCompletenessTables.lyd_hash
          (List.nth (Z.to_nat (RegionId.Merkle.Layer.to_index layer))
            (OrchardCompletenessTables.t_layers
              (OrchardCompletenessTables.tables_of w))
            OrchardCompletenessTables.layer0))) 0.

  (** The cell-shape discharge: reduce the generator dispatch and the site
      value to one spelling on both sides, then compare syntactically.  A
      bare [reflexivity] diverges here — unification's head-normalization
      forces the hoisted record's Poseidon/hash folds (see
      [docs/compile-performance.md]). *)
  Ltac cell_refl :=
    cbn [OrchardCompletenessTables.advice_t
         OrchardCompletenessTables.advice_nullifier_t
         OrchardCompletenessTables.merkle_advice_t
         OrchardCompletenessTables.advice_ecc_t
         OrchardVarBaseTables.mul_advice_of];
    unfold OrchardVarBaseTables.overflow_lookup_advice_of,
           OrchardNoteCommitCells.civk_advice,
           OrchardNoteCommitCells.nc_advice,
           OrchardNoteCommitCells.ycanon_advice,
           OrchardNoteCommitCells.running_lookup_advice,
           OrchardNoteCommitCells.short_range_advice,
           alpha_z0, civk_pk, nc_pk_old, nc_pk_new, nc_pk_of, nc_y_of,
           merkle_b_word_t;
    reflexivity.

  (** ** The running-site instances *)

  Lemma site_alpha :
    running_site_sound
      (RegionId.Nullifier RegionId.Nullifier.AlphaLookup) 13.
  Proof.
    apply (running_site_lemma _ _ alpha_z0).
    - intros w row. cell_refl.
    - intros w _ _.
      unfold alpha_z0.
      cbv zeta.
      apply Z.mod_pos_bound.
      exact Primes.pallas_p_pos.
    - vm_compute. reflexivity.
  Qed.

  Lemma site_overflow :
    running_site_sound
      (RegionId.AddressIntegrity
        (RegionId.AddressIntegrity.Mul
          RegionId.AddressIntegrity.Mul.OverflowLookup)) 13.
  Proof.
    apply (running_site_lemma _ _
      (fun w =>
        OrchardVarBaseTables.vb_s
          (OrchardCompletenessTables.t_vb
            (OrchardCompletenessTables.tables_of w)))).
    - intros w row. cell_refl.
    - intros w _ _.
      cbn [OrchardCompletenessTables.tables_of OrchardCompletenessTables.t_vb].
      apply vb_s_range.
    - vm_compute. reflexivity.
  Qed.

  Lemma site_civk_ak :
    running_site_sound (RegionId.CommitIvk RegionId.CommitIvk.AkLookup) 13.
  Proof.
    apply (running_site_lemma _ _
      (fun w => OrchardNoteCommitCells.civk_a_prime (civk_pk w))).
    - intros w row. cell_refl.
    - intros w _ _.
      unfold OrchardNoteCommitCells.civk_a_prime, OrchardNoteCommitCells.prime_of.
      apply Z.mod_pos_bound.
      exact Primes.pallas_p_pos.
    - vm_compute. reflexivity.
  Qed.

  Lemma site_civk_nk :
    running_site_sound (RegionId.CommitIvk RegionId.CommitIvk.NkLookup) 14.
  Proof.
    apply (running_site_lemma _ _
      (fun w => OrchardNoteCommitCells.civk_b2_c_prime (civk_pk w))).
    - intros w row. cell_refl.
    - intros w _ _.
      unfold OrchardNoteCommitCells.civk_b2_c_prime,
        OrchardNoteCommitCells.prime_of.
      apply Z.mod_pos_bound.
      exact Primes.pallas_p_pos.
    - vm_compute. reflexivity.
  Qed.

  (** The prime-offset range fact shared by the note-commitment lookup
      heads. *)
  Lemma prime_of_range (low k : Z) :
    0 <= OrchardNoteCommitCells.prime_of low k < Primes.pallas_p.
  Proof.
    unfold OrchardNoteCommitCells.prime_of.
    apply Z.mod_pos_bound.
    exact Primes.pallas_p_pos.
  Qed.

  Lemma ycanon_j_range (y : Z) :
    0 <= OrchardNoteCommitCells.ycanon_j y < Primes.pallas_p.
  Proof.
    unfold OrchardNoteCommitCells.ycanon_j.
    assert (Hpow : 0 < 2 ^ 250) by (apply Z.pow_pos_nonneg; lia).
    pose proof (Z.mod_pos_bound y (2 ^ 250) Hpow).
    pose proof pallas_p_big.
    lia.
  Qed.

  Lemma site_nc_old_xgd :
    running_site_sound
      (RegionId.NoteCommit RegionId.NoteCommit.Which.Old
        RegionId.NoteCommit.XGDLookup) 13.
  Proof.
    apply (running_site_lemma _ _
      (fun w => OrchardNoteCommitCells.nc_a_prime (nc_pk_old w))).
    - intros w row. cell_refl.
    - intros w _ _. apply prime_of_range.
    - vm_compute. reflexivity.
  Qed.

  Lemma site_nc_old_xpkd :
    running_site_sound
      (RegionId.NoteCommit RegionId.NoteCommit.Which.Old
        RegionId.NoteCommit.XPKDLookup) 14.
  Proof.
    apply (running_site_lemma _ _
      (fun w => OrchardNoteCommitCells.nc_b3_c_prime (nc_pk_old w))).
    - intros w row. cell_refl.
    - intros w _ _. apply prime_of_range.
    - vm_compute. reflexivity.
  Qed.

  Lemma site_nc_old_rho :
    running_site_sound
      (RegionId.NoteCommit RegionId.NoteCommit.Which.Old
        RegionId.NoteCommit.RhoLookup) 14.
  Proof.
    apply (running_site_lemma _ _
      (fun w => OrchardNoteCommitCells.nc_e1_f_prime (nc_pk_old w))).
    - intros w row. cell_refl.
    - intros w _ _. apply prime_of_range.
    - vm_compute. reflexivity.
  Qed.

  Lemma site_nc_old_psi :
    running_site_sound
      (RegionId.NoteCommit RegionId.NoteCommit.Which.Old
        RegionId.NoteCommit.PsiLookup) 13.
  Proof.
    apply (running_site_lemma _ _
      (fun w => OrchardNoteCommitCells.nc_g1_g2_prime (nc_pk_old w))).
    - intros w row. cell_refl.
    - intros w _ _. apply prime_of_range.
    - vm_compute. reflexivity.
  Qed.

  Lemma site_nc_new_xgd :
    running_site_sound
      (RegionId.NoteCommit RegionId.NoteCommit.Which.New
        RegionId.NoteCommit.XGDLookup) 13.
  Proof.
    apply (running_site_lemma _ _
      (fun w => OrchardNoteCommitCells.nc_a_prime (nc_pk_new w))).
    - intros w row. cell_refl.
    - intros w _ _. apply prime_of_range.
    - vm_compute. reflexivity.
  Qed.

  Lemma site_nc_new_xpkd :
    running_site_sound
      (RegionId.NoteCommit RegionId.NoteCommit.Which.New
        RegionId.NoteCommit.XPKDLookup) 14.
  Proof.
    apply (running_site_lemma _ _
      (fun w => OrchardNoteCommitCells.nc_b3_c_prime (nc_pk_new w))).
    - intros w row. cell_refl.
    - intros w _ _. apply prime_of_range.
    - vm_compute. reflexivity.
  Qed.

  Lemma site_nc_new_rho :
    running_site_sound
      (RegionId.NoteCommit RegionId.NoteCommit.Which.New
        RegionId.NoteCommit.RhoLookup) 14.
  Proof.
    apply (running_site_lemma _ _
      (fun w => OrchardNoteCommitCells.nc_e1_f_prime (nc_pk_new w))).
    - intros w row. cell_refl.
    - intros w _ _. apply prime_of_range.
    - vm_compute. reflexivity.
  Qed.

  Lemma site_nc_new_psi :
    running_site_sound
      (RegionId.NoteCommit RegionId.NoteCommit.Which.New
        RegionId.NoteCommit.PsiLookup) 13.
  Proof.
    apply (running_site_lemma _ _
      (fun w => OrchardNoteCommitCells.nc_g1_g2_prime (nc_pk_new w))).
    - intros w row. cell_refl.
    - intros w _ _. apply prime_of_range.
    - vm_compute. reflexivity.
  Qed.

  Lemma site_ycan_old_gd_j :
    running_site_sound
      (RegionId.NoteCommit RegionId.NoteCommit.Which.Old
        (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.GD
          RegionId.NoteCommit.YCanonicity.JLookup)) 25.
  Proof.
    apply (running_site_lemma _ _
      (fun w => OrchardNoteCommitCells.ycanon_j (Point.y (hi_g_d_old w)))).
    - intros w row. cell_refl.
    - intros w _ _. apply ycanon_j_range.
    - vm_compute. reflexivity.
  Qed.

  Lemma site_ycan_old_gd_jp :
    running_site_sound
      (RegionId.NoteCommit RegionId.NoteCommit.Which.Old
        (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.GD
          RegionId.NoteCommit.YCanonicity.JPrimeLookup)) 13.
  Proof.
    apply (running_site_lemma _ _
      (fun w =>
        OrchardNoteCommitCells.ycanon_j_prime (Point.y (hi_g_d_old w)))).
    - intros w row. cell_refl.
    - intros w _ _.
      unfold OrchardNoteCommitCells.ycanon_j_prime.
      apply prime_of_range.
    - vm_compute. reflexivity.
  Qed.

  Lemma site_ycan_old_pkd_j :
    running_site_sound
      (RegionId.NoteCommit RegionId.NoteCommit.Which.Old
        (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.PkD
          RegionId.NoteCommit.YCanonicity.JLookup)) 25.
  Proof.
    apply (running_site_lemma _ _
      (fun w => OrchardNoteCommitCells.ycanon_j (Point.y (hi_pk_d_old w)))).
    - intros w row. cell_refl.
    - intros w _ _. apply ycanon_j_range.
    - vm_compute. reflexivity.
  Qed.

  Lemma site_ycan_old_pkd_jp :
    running_site_sound
      (RegionId.NoteCommit RegionId.NoteCommit.Which.Old
        (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.PkD
          RegionId.NoteCommit.YCanonicity.JPrimeLookup)) 13.
  Proof.
    apply (running_site_lemma _ _
      (fun w =>
        OrchardNoteCommitCells.ycanon_j_prime (Point.y (hi_pk_d_old w)))).
    - intros w row. cell_refl.
    - intros w _ _.
      unfold OrchardNoteCommitCells.ycanon_j_prime.
      apply prime_of_range.
    - vm_compute. reflexivity.
  Qed.

  Lemma site_ycan_new_gd_j :
    running_site_sound
      (RegionId.NoteCommit RegionId.NoteCommit.Which.New
        (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.GD
          RegionId.NoteCommit.YCanonicity.JLookup)) 25.
  Proof.
    apply (running_site_lemma _ _
      (fun w => OrchardNoteCommitCells.ycanon_j (Point.y (hi_g_d_new w)))).
    - intros w row. cell_refl.
    - intros w _ _. apply ycanon_j_range.
    - vm_compute. reflexivity.
  Qed.

  Lemma site_ycan_new_gd_jp :
    running_site_sound
      (RegionId.NoteCommit RegionId.NoteCommit.Which.New
        (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.GD
          RegionId.NoteCommit.YCanonicity.JPrimeLookup)) 13.
  Proof.
    apply (running_site_lemma _ _
      (fun w =>
        OrchardNoteCommitCells.ycanon_j_prime (Point.y (hi_g_d_new w)))).
    - intros w row. cell_refl.
    - intros w _ _.
      unfold OrchardNoteCommitCells.ycanon_j_prime.
      apply prime_of_range.
    - vm_compute. reflexivity.
  Qed.

  Lemma site_ycan_new_pkd_j :
    running_site_sound
      (RegionId.NoteCommit RegionId.NoteCommit.Which.New
        (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.PkD
          RegionId.NoteCommit.YCanonicity.JLookup)) 25.
  Proof.
    apply (running_site_lemma _ _
      (fun w => OrchardNoteCommitCells.ycanon_j (Point.y (hi_pk_d_new w)))).
    - intros w row. cell_refl.
    - intros w _ _. apply ycanon_j_range.
    - vm_compute. reflexivity.
  Qed.

  Lemma site_ycan_new_pkd_jp :
    running_site_sound
      (RegionId.NoteCommit RegionId.NoteCommit.Which.New
        (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.PkD
          RegionId.NoteCommit.YCanonicity.JPrimeLookup)) 13.
  Proof.
    apply (running_site_lemma _ _
      (fun w =>
        OrchardNoteCommitCells.ycanon_j_prime (Point.y (hi_pk_d_new w)))).
    - intros w row. cell_refl.
    - intros w _ _.
      unfold OrchardNoteCommitCells.ycanon_j_prime.
      apply prime_of_range.
    - vm_compute. reflexivity.
  Qed.

  (** ** Bounds toolbox for the short-site values *)

  (** A masked value times its shift stays a 10-bit table word. *)
  Lemma short_mod_bound (x m f : Z) (Hm : 0 < m) (Hf : 0 < f)
      (Hmf : m * f <= 1024) :
    0 <= x mod m /\ (x mod m) * f < 1024.
  Proof.
    pose proof (Z.mod_pos_bound x m Hm) as Hx.
    split; [lia |].
    assert (Hle : (x mod m) * f <= (m - 1) * f)
      by (apply Z.mul_le_mono_nonneg_r; lia).
    assert (Heq : (m - 1) * f = m * f - f) by ring.
    lia.
  Qed.

  (** A truncated quotient times its shift stays a 10-bit table word. *)
  Lemma short_div_bound (x d f hi : Z) (Hx : 0 <= x < d * hi)
      (Hd : 0 < d) (Hf : 0 < f) (Hh : 0 < hi) (Hhf : hi * f <= 1024) :
    0 <= x / d /\ (x / d) * f < 1024.
  Proof.
    destruct (div_bound x d hi Hx Hd) as [H1 H2].
    split; [exact H1 |].
    assert (Hle : (x / d) * f <= (hi - 1) * f)
      by (apply Z.mul_le_mono_nonneg_r; lia).
    assert (Heq : (hi - 1) * f = hi * f - f) by ring.
    lia.
  Qed.

  (** Every word of a little-endian decomposition is a 10-bit digit. *)
  Lemma words_le_bound (count : nat) (n : Z) :
    List.Forall (fun wd => 0 <= wd < 1024)
      (SinsemillaSpec.words_le count n).
  Proof.
    revert n; induction count as [| c IH]; intros n;
      cbn [SinsemillaSpec.words_le].
    - constructor.
    - constructor.
      + change (2 ^ SinsemillaSpec.sinsemilla_k) with 1024.
        apply Z.mod_pos_bound; lia.
      + apply IH.
  Qed.

  Lemma nth_bound_1024 (j : nat) (ws : list Z)
      (H : List.Forall (fun wd => 0 <= wd < 1024) ws) :
    0 <= List.nth j ws 0 < 1024.
  Proof.
    destruct (Nat.lt_ge_cases j (List.length ws)) as [Hj | Hj].
    - exact (proj1 (List.Forall_forall _ _) H _ (List.nth_In ws 0 Hj)).
    - rewrite List.nth_overflow by lia. lia.
  Qed.

  Lemma Forall_firstn {A : Type} (P : A -> Prop) (n : nat) (l : list A)
      (H : List.Forall P l) :
    List.Forall P (List.firstn n l).
  Proof.
    revert l H; induction n as [| n IH]; intros l H; cbn [List.firstn].
    - constructor.
    - destruct l as [| x l]; [constructor |].
      inversion H; subst.
      constructor; [assumption | apply IH; assumption].
  Qed.

  Lemma Forall_skipn {A : Type} (P : A -> Prop) (n : nat) (l : list A)
      (H : List.Forall P l) :
    List.Forall P (List.skipn n l).
  Proof.
    revert l H; induction n as [| n IH]; intros l H; cbn [List.skipn].
    - exact H.
    - destruct l as [| x l]; [constructor |].
      inversion H; subst.
      apply IH; assumption.
  Qed.

  (** Splitting a message into pieces and flattening preserves a per-word
      bound. *)
  Lemma forall_concat_split_pieces (P : Z -> Prop) (lens : list nat)
      (l : list Z) (H : List.Forall P l) :
    List.Forall P
      (Stdlib.Lists.List.concat
        (OrchardAdviceMerkleSinsemilla.split_pieces lens l)).
  Proof.
    revert l H; induction lens as [| len lens IH]; intros l H;
      cbn [OrchardAdviceMerkleSinsemilla.split_pieces
           Stdlib.Lists.List.concat].
    - constructor.
    - apply List.Forall_app; split.
      + apply Forall_firstn; exact H.
      + apply IH; apply Forall_skipn; exact H.
  Qed.

  (** The stored word list of a hash-region record is the flattened
      message. *)
  Lemma hd_words_hash_data_of (Q : Point.t) (pieces : list (list Z)) :
    OrchardCompletenessTables.hd_words
      (OrchardCompletenessTables.hash_data_of Q pieces) =
    Stdlib.Lists.List.concat pieces.
  Proof.
    unfold OrchardCompletenessTables.hash_data_of.
    destruct
      (OrchardCompletenessTables.hash_go Q
        (Stdlib.Lists.List.concat pieces)) as [rows out].
    reflexivity.
  Qed.

  (** Every stored Merkle-layer word is a 10-bit digit, whatever node value
      the layer fold threads. *)
  Lemma layers_go_words_bound (w : HonestInput) (count : nat) :
    forall (node : Z) (i : nat),
      List.Forall
        (fun ld =>
          List.Forall (fun wd => 0 <= wd < 1024)
            (OrchardCompletenessTables.hd_words
              (OrchardCompletenessTables.lyd_hash ld)))
        (OrchardCompletenessTables.layers_go w node i count).
  Proof.
    induction count as [| count IH]; intros node i;
      cbn [OrchardCompletenessTables.layers_go].
    - constructor.
    - constructor.
      + cbn [OrchardCompletenessTables.lyd_hash].
        rewrite hd_words_hash_data_of.
        apply forall_concat_split_pieces.
        unfold OrchardCompletenessTables.merkle_words_at.
        destruct (path_bit w i);
          (unfold SinsemillaSpec.merkle_message; apply words_le_bound).
      + apply IH.
  Qed.

  (** The leaf value the hoisted record threads into the Merkle chain: the
      old note commitment's x-coordinate. *)
  Definition t_leaf (w : HonestInput) : Z :=
    Point.x
      (EccSpec.point_add
        (OrchardCompletenessTables.hd_out
          (OrchardCompletenessTables.hash_data_of
            OrchardAdviceMerkleSinsemilla.note_commit_Q
            (OrchardAdviceMerkleSinsemilla.split_pieces
              OrchardAdviceMerkleSinsemilla.note_commit_lens
              (note_commit_old_words w))))
        (Garden.Orchard.protocol_spec.OrchardProtocolSpec.mul_note_commit_r
          (hi_rcm_old w))).

  (** The hoisted layer list is the [layers_of] fold at that leaf. *)
  Lemma t_layers_eq (w : HonestInput) :
    OrchardCompletenessTables.t_layers
      (OrchardCompletenessTables.tables_of w) =
    OrchardCompletenessTables.layers_of w (t_leaf w).
  Proof.
    unfold OrchardCompletenessTables.tables_of, t_leaf.
    reflexivity.
  Qed.

  Lemma merkle_b_word_bound (w : HonestInput)
      (layer : RegionId.Merkle.Layer.t) :
    0 <= merkle_b_word_t w layer < 1024.
  Proof.
    unfold merkle_b_word_t.
    apply nth_bound_1024.
    rewrite t_layers_eq.
    unfold OrchardCompletenessTables.layers_of.
    destruct
      (Nat.lt_ge_cases (Z.to_nat (RegionId.Merkle.Layer.to_index layer))
        (List.length
          (OrchardCompletenessTables.layers_go w (t_leaf w) 0%nat 32%nat)))
      as [Hi | Hi].
    - exact (proj1 (List.Forall_forall _ _)
        (layers_go_words_bound w 32%nat (t_leaf w) 0%nat) _
        (List.nth_In _ OrchardCompletenessTables.layer0 Hi)).
    - rewrite List.nth_overflow by lia.
      cbn. constructor.
  Qed.

  (** ** The short-site instances

      Every 2-row short range check of the circuit, each through
      [short_site_lemma]: the checked value at row 0, its bitshifted word at
      row 1 ([value · 2^(10−s)] for an [s]-bit check). *)

  Lemma site_merkle_b1 (layer : RegionId.Merkle.Layer.t) :
    short_site_sound (RegionId.Merkle layer RegionId.Merkle.Region.RangeB1).
  Proof.
    apply (short_site_lemma _
      (fun w => merkle_b_word_t w layer mod 2 ^ 5) (2 ^ 5)).
    - lia.
    - intros w. cell_refl.
    - intros w. cell_refl.
    - intros w _ _.
      change (2 ^ 5) with 32.
      apply short_mod_bound; lia.
    - destruct layer; vm_compute; reflexivity.
  Qed.

  Lemma site_merkle_b2 (layer : RegionId.Merkle.Layer.t) :
    short_site_sound (RegionId.Merkle layer RegionId.Merkle.Region.RangeB2).
  Proof.
    apply (short_site_lemma _
      (fun w => merkle_b_word_t w layer / 2 ^ 5) (2 ^ 5)).
    - lia.
    - intros w. cell_refl.
    - intros w. cell_refl.
    - intros w _ _.
      change (2 ^ 5) with 32.
      apply (short_div_bound _ 32 32 32); [| lia | lia | lia | lia].
      pose proof (merkle_b_word_bound w layer). lia.
    - destruct layer; vm_compute; reflexivity.
  Qed.

  Lemma site_civk_b0 :
    short_site_sound (RegionId.CommitIvk RegionId.CommitIvk.RangeB0).
  Proof.
    apply (short_site_lemma _
      (fun w => OrchardNoteCommitCells.civk_b0 (civk_pk w)) (2 ^ 6)).
    - lia.
    - intros w. cell_refl.
    - intros w. cell_refl.
    - intros w _ _.
      unfold OrchardNoteCommitCells.civk_b0.
      change (2 ^ 4) with 16; change (2 ^ 6) with 64.
      apply short_mod_bound; lia.
    - vm_compute. reflexivity.
  Qed.

  Lemma site_civk_b2 :
    short_site_sound (RegionId.CommitIvk RegionId.CommitIvk.RangeB2).
  Proof.
    apply (short_site_lemma _
      (fun w => OrchardNoteCommitCells.civk_b2 (civk_pk w)) (2 ^ 5)).
    - lia.
    - intros w. cell_refl.
    - intros w. cell_refl.
    - intros w _ _.
      unfold OrchardNoteCommitCells.civk_b2.
      change (2 ^ 5) with 32.
      apply (short_div_bound _ 32 32 32); [| lia | lia | lia | lia].
      unfold OrchardNoteCommitCells.civk_b.
      change (2 ^ 10) with 1024.
      apply Z.mod_pos_bound; lia.
    - vm_compute. reflexivity.
  Qed.

  Lemma site_civk_d0 :
    short_site_sound (RegionId.CommitIvk RegionId.CommitIvk.RangeD0).
  Proof.
    apply (short_site_lemma _
      (fun w => OrchardNoteCommitCells.civk_d0 (civk_pk w)) 2).
    - lia.
    - intros w. cell_refl.
    - intros w. cell_refl.
    - intros w _ _.
      unfold OrchardNoteCommitCells.civk_d0.
      change (2 ^ 9) with 512.
      apply short_mod_bound; lia.
    - vm_compute. reflexivity.
  Qed.

  Lemma site_nc_b0 (which : RegionId.NoteCommit.Which.t) :
    short_site_sound (RegionId.NoteCommit which RegionId.NoteCommit.RangeB0).
  Proof.
    apply (short_site_lemma _
      (fun w => OrchardNoteCommitCells.nc_b0 (nc_pk_of which w)) (2 ^ 6)).
    - lia.
    - intros w. destruct which; cell_refl.
    - intros w. destruct which; cell_refl.
    - intros w _ _.
      unfold OrchardNoteCommitCells.nc_b0.
      change (2 ^ 4) with 16; change (2 ^ 6) with 64.
      apply short_mod_bound; lia.
    - destruct which; vm_compute; reflexivity.
  Qed.

  Lemma site_nc_b3 (which : RegionId.NoteCommit.Which.t) :
    short_site_sound (RegionId.NoteCommit which RegionId.NoteCommit.RangeB3).
  Proof.
    apply (short_site_lemma _
      (fun w => OrchardNoteCommitCells.nc_b3 (nc_pk_of which w)) (2 ^ 6)).
    - lia.
    - intros w. destruct which; cell_refl.
    - intros w. destruct which; cell_refl.
    - intros w _ _.
      unfold OrchardNoteCommitCells.nc_b3.
      change (2 ^ 6) with 64.
      apply (short_div_bound _ 64 64 16); [| lia | lia | lia | lia].
      unfold OrchardNoteCommitCells.nc_b.
      change (2 ^ 10) with 1024.
      apply Z.mod_pos_bound; lia.
    - destruct which; vm_compute; reflexivity.
  Qed.

  Lemma site_nc_d2 (which : RegionId.NoteCommit.Which.t) :
    short_site_sound (RegionId.NoteCommit which RegionId.NoteCommit.RangeD2).
  Proof.
    apply (short_site_lemma _
      (fun w => OrchardNoteCommitCells.nc_d2 (nc_pk_of which w)) (2 ^ 2)).
    - lia.
    - intros w. destruct which; cell_refl.
    - intros w. destruct which; cell_refl.
    - intros w _ _.
      unfold OrchardNoteCommitCells.nc_d2.
      change (2 ^ 8) with 256; change (2 ^ 2) with 4.
      apply short_mod_bound; lia.
    - destruct which; vm_compute; reflexivity.
  Qed.

  Lemma site_nc_e0 (which : RegionId.NoteCommit.Which.t) :
    short_site_sound (RegionId.NoteCommit which RegionId.NoteCommit.RangeE0).
  Proof.
    apply (short_site_lemma _
      (fun w => OrchardNoteCommitCells.nc_e0 (nc_pk_of which w)) (2 ^ 4)).
    - lia.
    - intros w. destruct which; cell_refl.
    - intros w. destruct which; cell_refl.
    - intros w _ _.
      unfold OrchardNoteCommitCells.nc_e0.
      change (2 ^ 6) with 64; change (2 ^ 4) with 16.
      apply short_mod_bound; lia.
    - destruct which; vm_compute; reflexivity.
  Qed.

  Lemma site_nc_e1 (which : RegionId.NoteCommit.Which.t) :
    short_site_sound (RegionId.NoteCommit which RegionId.NoteCommit.RangeE1).
  Proof.
    apply (short_site_lemma _
      (fun w => OrchardNoteCommitCells.nc_e1 (nc_pk_of which w)) (2 ^ 6)).
    - lia.
    - intros w. destruct which; cell_refl.
    - intros w. destruct which; cell_refl.
    - intros w _ _.
      unfold OrchardNoteCommitCells.nc_e1.
      change (2 ^ 6) with 64.
      apply (short_div_bound _ 64 64 16); [| lia | lia | lia | lia].
      unfold OrchardNoteCommitCells.nc_e.
      change (2 ^ 10) with 1024.
      apply Z.mod_pos_bound; lia.
    - destruct which; vm_compute; reflexivity.
  Qed.

  Lemma site_nc_g1 (which : RegionId.NoteCommit.Which.t) :
    short_site_sound (RegionId.NoteCommit which RegionId.NoteCommit.RangeG1).
  Proof.
    apply (short_site_lemma _
      (fun w => OrchardNoteCommitCells.nc_g1 (nc_pk_of which w)) 2).
    - lia.
    - intros w. destruct which; cell_refl.
    - intros w. destruct which; cell_refl.
    - intros w _ _.
      unfold OrchardNoteCommitCells.nc_g1.
      change (2 ^ 9) with 512.
      apply short_mod_bound; lia.
    - destruct which; vm_compute; reflexivity.
  Qed.

  Lemma site_nc_h0 (which : RegionId.NoteCommit.Which.t) :
    short_site_sound (RegionId.NoteCommit which RegionId.NoteCommit.RangeH0).
  Proof.
    apply (short_site_lemma _
      (fun w => OrchardNoteCommitCells.nc_h0 (nc_pk_of which w)) (2 ^ 5)).
    - lia.
    - intros w. destruct which; cell_refl.
    - intros w. destruct which; cell_refl.
    - intros w _ _.
      unfold OrchardNoteCommitCells.nc_h0.
      change (2 ^ 5) with 32.
      apply short_mod_bound; lia.
    - destruct which; vm_compute; reflexivity.
  Qed.

  Lemma site_ycan_k0 (which : RegionId.NoteCommit.Which.t)
      (subject : RegionId.NoteCommit.YSubject.t) :
    short_site_sound
      (RegionId.NoteCommit which
        (RegionId.NoteCommit.YCanonicity subject
          RegionId.NoteCommit.YCanonicity.RangeK0)).
  Proof.
    apply (short_site_lemma _
      (fun w => OrchardNoteCommitCells.ycanon_k0 (nc_y_of which subject w))
      2).
    - lia.
    - intros w. destruct which, subject; cell_refl.
    - intros w. destruct which, subject; cell_refl.
    - intros w _ _.
      unfold OrchardNoteCommitCells.ycanon_k0.
      change (2 ^ 9) with 512.
      apply short_mod_bound; lia.
    - destruct which, subject; vm_compute; reflexivity.
  Qed.

  Lemma site_ycan_k2 (which : RegionId.NoteCommit.Which.t)
      (subject : RegionId.NoteCommit.YSubject.t) :
    short_site_sound
      (RegionId.NoteCommit which
        (RegionId.NoteCommit.YCanonicity subject
          RegionId.NoteCommit.YCanonicity.RangeK2)).
  Proof.
    apply (short_site_lemma _
      (fun w => OrchardNoteCommitCells.ycanon_k2 (nc_y_of which subject w))
      (2 ^ 6)).
    - lia.
    - intros w. destruct which, subject; cell_refl.
    - intros w. destruct which, subject; cell_refl.
    - intros w _ _.
      unfold OrchardNoteCommitCells.ycanon_k2.
      change (2 ^ 4) with 16; change (2 ^ 6) with 64.
      apply short_mod_bound; lia.
    - destruct which, subject; vm_compute; reflexivity.
  Qed.

  (** ** The site tables

      The complete inventory of the enabled lookup rows, keyed by the gating
      selector — certified against [enabled] by the [lookup_scan]
      [vm_compute] below. *)

  Definition running_sites : list (RegionId.t * Z) := [
    (RegionId.Nullifier RegionId.Nullifier.AlphaLookup, 13);
    (RegionId.AddressIntegrity
      (RegionId.AddressIntegrity.Mul
        RegionId.AddressIntegrity.Mul.OverflowLookup), 13);
    (RegionId.CommitIvk RegionId.CommitIvk.AkLookup, 13);
    (RegionId.CommitIvk RegionId.CommitIvk.NkLookup, 14);
    (RegionId.NoteCommit RegionId.NoteCommit.Which.Old
      RegionId.NoteCommit.XGDLookup, 13);
    (RegionId.NoteCommit RegionId.NoteCommit.Which.Old
      RegionId.NoteCommit.XPKDLookup, 14);
    (RegionId.NoteCommit RegionId.NoteCommit.Which.Old
      RegionId.NoteCommit.RhoLookup, 14);
    (RegionId.NoteCommit RegionId.NoteCommit.Which.Old
      RegionId.NoteCommit.PsiLookup, 13);
    (RegionId.NoteCommit RegionId.NoteCommit.Which.Old
      (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.GD
        RegionId.NoteCommit.YCanonicity.JLookup), 25);
    (RegionId.NoteCommit RegionId.NoteCommit.Which.Old
      (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.GD
        RegionId.NoteCommit.YCanonicity.JPrimeLookup), 13);
    (RegionId.NoteCommit RegionId.NoteCommit.Which.Old
      (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.PkD
        RegionId.NoteCommit.YCanonicity.JLookup), 25);
    (RegionId.NoteCommit RegionId.NoteCommit.Which.Old
      (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.PkD
        RegionId.NoteCommit.YCanonicity.JPrimeLookup), 13);
    (RegionId.NoteCommit RegionId.NoteCommit.Which.New
      RegionId.NoteCommit.XGDLookup, 13);
    (RegionId.NoteCommit RegionId.NoteCommit.Which.New
      RegionId.NoteCommit.XPKDLookup, 14);
    (RegionId.NoteCommit RegionId.NoteCommit.Which.New
      RegionId.NoteCommit.RhoLookup, 14);
    (RegionId.NoteCommit RegionId.NoteCommit.Which.New
      RegionId.NoteCommit.PsiLookup, 13);
    (RegionId.NoteCommit RegionId.NoteCommit.Which.New
      (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.GD
        RegionId.NoteCommit.YCanonicity.JLookup), 25);
    (RegionId.NoteCommit RegionId.NoteCommit.Which.New
      (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.GD
        RegionId.NoteCommit.YCanonicity.JPrimeLookup), 13);
    (RegionId.NoteCommit RegionId.NoteCommit.Which.New
      (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.PkD
        RegionId.NoteCommit.YCanonicity.JLookup), 25);
    (RegionId.NoteCommit RegionId.NoteCommit.Which.New
      (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.PkD
        RegionId.NoteCommit.YCanonicity.JPrimeLookup), 13)
  ].

  Definition all_layers : list RegionId.Merkle.Layer.t := [
    RegionId.Merkle.Layer.L0; RegionId.Merkle.Layer.L1;
    RegionId.Merkle.Layer.L2; RegionId.Merkle.Layer.L3;
    RegionId.Merkle.Layer.L4; RegionId.Merkle.Layer.L5;
    RegionId.Merkle.Layer.L6; RegionId.Merkle.Layer.L7;
    RegionId.Merkle.Layer.L8; RegionId.Merkle.Layer.L9;
    RegionId.Merkle.Layer.L10; RegionId.Merkle.Layer.L11;
    RegionId.Merkle.Layer.L12; RegionId.Merkle.Layer.L13;
    RegionId.Merkle.Layer.L14; RegionId.Merkle.Layer.L15;
    RegionId.Merkle.Layer.L16; RegionId.Merkle.Layer.L17;
    RegionId.Merkle.Layer.L18; RegionId.Merkle.Layer.L19;
    RegionId.Merkle.Layer.L20; RegionId.Merkle.Layer.L21;
    RegionId.Merkle.Layer.L22; RegionId.Merkle.Layer.L23;
    RegionId.Merkle.Layer.L24; RegionId.Merkle.Layer.L25;
    RegionId.Merkle.Layer.L26; RegionId.Merkle.Layer.L27;
    RegionId.Merkle.Layer.L28; RegionId.Merkle.Layer.L29;
    RegionId.Merkle.Layer.L30; RegionId.Merkle.Layer.L31
  ].

  Definition short_sites : list RegionId.t :=
    List.map
      (fun layer => RegionId.Merkle layer RegionId.Merkle.Region.RangeB1)
      all_layers ++
    List.map
      (fun layer => RegionId.Merkle layer RegionId.Merkle.Region.RangeB2)
      all_layers ++
    [RegionId.CommitIvk RegionId.CommitIvk.RangeB0;
     RegionId.CommitIvk RegionId.CommitIvk.RangeB2;
     RegionId.CommitIvk RegionId.CommitIvk.RangeD0;
     RegionId.NoteCommit RegionId.NoteCommit.Which.Old
       RegionId.NoteCommit.RangeB0;
     RegionId.NoteCommit RegionId.NoteCommit.Which.Old
       RegionId.NoteCommit.RangeB3;
     RegionId.NoteCommit RegionId.NoteCommit.Which.Old
       RegionId.NoteCommit.RangeD2;
     RegionId.NoteCommit RegionId.NoteCommit.Which.Old
       RegionId.NoteCommit.RangeE0;
     RegionId.NoteCommit RegionId.NoteCommit.Which.Old
       RegionId.NoteCommit.RangeE1;
     RegionId.NoteCommit RegionId.NoteCommit.Which.Old
       RegionId.NoteCommit.RangeG1;
     RegionId.NoteCommit RegionId.NoteCommit.Which.Old
       RegionId.NoteCommit.RangeH0;
     RegionId.NoteCommit RegionId.NoteCommit.Which.Old
       (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.GD
         RegionId.NoteCommit.YCanonicity.RangeK0);
     RegionId.NoteCommit RegionId.NoteCommit.Which.Old
       (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.GD
         RegionId.NoteCommit.YCanonicity.RangeK2);
     RegionId.NoteCommit RegionId.NoteCommit.Which.Old
       (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.PkD
         RegionId.NoteCommit.YCanonicity.RangeK0);
     RegionId.NoteCommit RegionId.NoteCommit.Which.Old
       (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.PkD
         RegionId.NoteCommit.YCanonicity.RangeK2);
     RegionId.NoteCommit RegionId.NoteCommit.Which.New
       RegionId.NoteCommit.RangeB0;
     RegionId.NoteCommit RegionId.NoteCommit.Which.New
       RegionId.NoteCommit.RangeB3;
     RegionId.NoteCommit RegionId.NoteCommit.Which.New
       RegionId.NoteCommit.RangeD2;
     RegionId.NoteCommit RegionId.NoteCommit.Which.New
       RegionId.NoteCommit.RangeE0;
     RegionId.NoteCommit RegionId.NoteCommit.Which.New
       RegionId.NoteCommit.RangeE1;
     RegionId.NoteCommit RegionId.NoteCommit.Which.New
       RegionId.NoteCommit.RangeG1;
     RegionId.NoteCommit RegionId.NoteCommit.Which.New
       RegionId.NoteCommit.RangeH0;
     RegionId.NoteCommit RegionId.NoteCommit.Which.New
       (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.GD
         RegionId.NoteCommit.YCanonicity.RangeK0);
     RegionId.NoteCommit RegionId.NoteCommit.Which.New
       (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.GD
         RegionId.NoteCommit.YCanonicity.RangeK2);
     RegionId.NoteCommit RegionId.NoteCommit.Which.New
       (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.PkD
         RegionId.NoteCommit.YCanonicity.RangeK0);
     RegionId.NoteCommit RegionId.NoteCommit.Which.New
       (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.PkD
         RegionId.NoteCommit.YCanonicity.RangeK2)
    ].

  (** The two Sinsemilla configurations' hash-region sites. *)
  Definition layers_1 : list RegionId.Merkle.Layer.t :=
    List.firstn 16%nat all_layers.
  Definition layers_2 : list RegionId.Merkle.Layer.t :=
    List.skipn 16%nat all_layers.

  Definition sins1_sites : list (RegionId.t * Z) :=
    List.map
      (fun layer =>
        (RegionId.Merkle layer RegionId.Merkle.Region.HashToPoint, 52))
      layers_1 ++
    [(RegionId.CommitIvk RegionId.CommitIvk.HashToPoint, 51);
     (RegionId.NoteCommit RegionId.NoteCommit.Which.Old
        RegionId.NoteCommit.HashToPoint, 109)].

  Definition sins2_sites : list (RegionId.t * Z) :=
    List.map
      (fun layer =>
        (RegionId.Merkle layer RegionId.Merkle.Region.HashToPoint, 52))
      layers_2 ++
    [(RegionId.NoteCommit RegionId.NoteCommit.Which.New
        RegionId.NoteCommit.HashToPoint, 109)].

  (** ** The Sinsemilla hash-region site leaves

      The generator-table membership of every ladder round tuple
      [(word, x_p, y_p)]: the [bits]-column telescoping gives the word, the
      stored round row gives [x_p], and the [y_p] reconstruction identity
      ((λ₁+λ₂)·(x_a − x_r)·2⁻¹ − λ₁·(x_a − x_p) = y_p, over the non-vertical
      chords that [nondegenerate w] supplies) gives the [TableY] pair.

      The proofs live in the nested module below, whose imports (the hoisted
      cell layer, the Merkle/Sinsemilla generator and the round algebra of
      [forward/sinsemilla.v]) are confined to that scope; the leaves
      themselves are stated and proved after it. *)
  Module SinsemillaSites.
    Module SC := Garden.Halo2.halo2_gadgets.sinsemilla.chip.

    Import OrchardCompletenessTables.
    Import OrchardAdviceMerkleSinsemilla.
    Import OrchardForwardSinsemilla.

    Strategy opaque [BinOp.div mod_inverse CompleteAddition.output].

    (** ** The congruence toolkit

        The [Zdiv.eqm] setoid instances and the [BinOp]-to-[eqm] morphism
        lemmas, in the spelling of [forward/sinsemilla.v] (whose own
        declarations are file-local). *)

    #[local] Instance eqm_equiv (q : Z) : Equivalence (Zdiv.eqm q).
    Proof.
      unfold Zdiv.eqm; split;
        [intro | intros ? ? | intros ? ? ?]; congruence.
    Qed.

    #[local] Instance eqm_iff_proper (q : Z) :
      Proper (Zdiv.eqm q ==> Zdiv.eqm q ==> iff) (Zdiv.eqm q).
    Proof.
      intros a b Hab c d Hcd.
      unfold Zdiv.eqm in *.
      split; congruence.
    Qed.

    #[local] Existing Instances Zdiv.Zplus_eqm Zdiv.Zmult_eqm Zdiv.Zopp_eqm
      Zdiv.Zminus_eqm.

    Lemma unop_from_eqm (x : Z) :
      Zdiv.eqm Primes.pallas_p (UnOp.from x) x.
    Proof. unfold UnOp.from. apply Zdiv.Zmod_eqm. Qed.

    Lemma binop_add_eqm (x y : Z) :
      Zdiv.eqm Primes.pallas_p (BinOp.add x y) (x + y).
    Proof. unfold BinOp.add. apply Zdiv.Zmod_eqm. Qed.

    (** Strip every field operation of its guarding [mod]. *)
    Ltac strip_mods :=
      repeat (setoid_rewrite binop_mul_eqm || setoid_rewrite binop_sub_eqm
              || setoid_rewrite binop_add_eqm || setoid_rewrite unop_from_eqm).

    (** A congruence between reduced values is an equality. *)
    Lemma eqm_reduced (X Y : Z) :
      Zdiv.eqm Primes.pallas_p X Y ->
      X mod Primes.pallas_p = X ->
      0 <= Y < Primes.pallas_p ->
      X = Y.
    Proof.
      unfold Zdiv.eqm.
      intros Heq Hx Hy.
      rewrite <- Hx, Heq.
      apply Z.mod_small. exact Hy.
    Qed.

    Lemma binop_mul_reduced (x y : Z) :
      BinOp.mul x y mod Primes.pallas_p = BinOp.mul x y.
    Proof.
      unfold BinOp.mul. rewrite Zdiv.Zmod_mod. reflexivity.
    Qed.

    Lemma binop_add_reduced (x y : Z) :
      BinOp.add x y mod Primes.pallas_p = BinOp.add x y.
    Proof.
      unfold BinOp.add. rewrite Zdiv.Zmod_mod. reflexivity.
    Qed.

    (** Linear combinations of congruences. *)
    Lemma mod0_mul (c a : Z) :
      a mod Primes.pallas_p = 0 -> (c * a) mod Primes.pallas_p = 0.
    Proof.
      intros Ha.
      rewrite Zdiv.Zmult_mod, Ha, Z.mul_0_r, Zdiv.Zmod_0_l.
      reflexivity.
    Qed.

    Lemma mod0_add (a b : Z) :
      a mod Primes.pallas_p = 0 -> b mod Primes.pallas_p = 0 ->
      (a + b) mod Primes.pallas_p = 0.
    Proof.
      intros Ha Hb.
      rewrite Zdiv.Zplus_mod, Ha, Hb, Z.add_0_r, Zdiv.Zmod_0_l.
      reflexivity.
    Qed.

    Lemma eqm_of_diff (X Y D : Z) :
      D mod Primes.pallas_p = 0 -> X - Y = D -> Zdiv.eqm Primes.pallas_p X Y.
    Proof.
      intros HD Hdiff.
      unfold Zdiv.eqm.
      replace X with (Y + D) by lia.
      rewrite Zdiv.Zplus_mod, HD, Z.add_0_r, Zdiv.Zmod_mod.
      reflexivity.
    Qed.

    (** ** The first chord's exactness *)

    Lemma chord1_mul (A G : Point.t)
        (Hnd : BinOp.sub (Point.x A) (Point.x G) <> 0) :
      Zdiv.eqm Primes.pallas_p
        (rr_l1 A G * (Point.x A - Point.x G))
        (Point.y A - Point.y G).
    Proof.
      assert (Hp2 : 2 < Primes.pallas_p)
        by (unfold Primes.pallas_p, Primes.t_p; lia).
      assert (Hden :
          BinOp.sub (Point.x A) (Point.x G) mod Primes.pallas_p <> 0).
      { unfold BinOp.sub.
        rewrite Zdiv.Zmod_mod.
        exact Hnd. }
      pose proof (div_mul
        (BinOp.sub (Point.y A) (Point.y G))
        (BinOp.sub (Point.x A) (Point.x G))
        Hp2 Hden) as Hmul.
      change (BinOp.div (BinOp.sub (Point.y A) (Point.y G))
          (BinOp.sub (Point.x A) (Point.x G)))
        with (rr_l1 A G) in Hmul.
      unfold Zdiv.eqm.
      unfold BinOp.mul, BinOp.sub in Hmul.
      rewrite Zdiv.Zmult_mod_idemp_r in Hmul.
      rewrite Zdiv.Zmod_mod in Hmul.
      exact Hmul.
    Qed.

    Lemma chord1_nonzero (Q : Point.t) (ws : list Z) (j : nat)
        (HQ : 0 <= Point.x Q < Primes.pallas_p)
        (Hj : (j < List.length ws)%nat)
        (Hg : 0 <= Point.x (SinsemillaSpec.generator (List.nth j ws 0))
                < Primes.pallas_p)
        (Hnd : SinsemillaHash.nondegenerate Q ws) :
      BinOp.sub (Point.x (sinsemilla_acc Q ws j))
        (Point.x (SinsemillaSpec.generator (List.nth j ws 0))) <> 0.
    Proof.
      destruct (Hnd j Hj) as [Hneq _].
      intros Hzero.
      apply sub_zero_equiv in Hzero.
      unfold UnOp.from in Hzero.
      rewrite (Z.mod_small _ _ (acc_x_reduced Q ws j HQ)) in Hzero.
      rewrite (Z.mod_small _ _ Hg) in Hzero.
      exact (Hneq Hzero).
    Qed.

    (** ** bits telescoping *)

    (** The running-sum column telescopes within a piece. *)
    Lemma sds_step (l : list Z) :
      forall i : nat,
        (i < List.length l)%nat ->
        List.nth i (suffix_digit_sums l) 0 =
          List.nth i l 0 + 2 ^ 10 * List.nth (S i) (suffix_digit_sums l) 0.
    Proof.
      induction l as [| x l IH]; intros i Hi; cbn [List.length] in Hi; [lia |].
      destruct i as [| i].
      - cbn [suffix_digit_sums List.nth].
        destruct (suffix_digit_sums l) as [| y r]; reflexivity.
      - cbn [suffix_digit_sums List.nth].
        apply IH. lia.
    Qed.

    (** The last index of a piece, computed from the piece-length layout. *)
    Fixpoint bnd_lens (lens : list nat) (j : nat) : bool :=
      match lens with
      | [] => false
      | a :: lens' =>
          if (S j =? a)%nat then true
          else if (j <? a)%nat then false
          else bnd_lens lens' (j - a)
      end.

    Lemma nth_firstn_lt {A : Type} (d : A) (n : nat) (l : list A) :
      forall i : nat,
        (i < n)%nat -> List.nth i (List.firstn n l) d = List.nth i l d.
    Proof.
      revert l; induction n as [| n IH]; intros l i Hi; [lia |].
      destruct l as [| x l]; cbn [List.firstn].
      - destruct i; reflexivity.
      - destruct i as [| i]; cbn [List.nth]; [reflexivity |].
        apply IH. lia.
    Qed.

    Lemma split_cons (a : nat) (lens : list nat) (l : list Z) :
      split_pieces (a :: lens) l =
        List.firstn a l :: split_pieces lens (List.skipn a l).
    Proof. reflexivity. Qed.

    Lemma bits_cons (p : list Z) (ps : list (list Z)) :
      bits_column (p :: ps) = suffix_digit_sums p ++ bits_column ps.
    Proof. reflexivity. Qed.

    Lemma bits_step (lens : list nat) :
      forall (l : list Z) (j : nat),
        OrchardForwardSinsemilla.lens_sum lens = List.length l ->
        (j < List.length l)%nat ->
        List.nth j (bits_column (split_pieces lens l)) 0 =
          List.nth j l 0 +
          (if bnd_lens lens j
           then 0
           else 2 ^ 10 *
             List.nth (S j) (bits_column (split_pieces lens l)) 0).
    Proof.
      induction lens as [| a lens IH]; intros l j Hlen Hj;
        cbn [OrchardForwardSinsemilla.lens_sum] in Hlen.
      - cbn [List.length] in Hj. lia.
      - rewrite split_cons, bits_cons.
        assert (Ha : (a <= List.length l)%nat) by lia.
        assert (Hp : List.length (suffix_digit_sums (List.firstn a l)) = a).
        { rewrite suffix_digit_sums_length, List.length_firstn. lia. }
        cbn [bnd_lens].
        destruct (Nat.lt_ge_cases j a) as [Hlt | Hge].
        + rewrite List.app_nth1 by lia.
          rewrite sds_step
            by (rewrite List.length_firstn; lia).
          rewrite nth_firstn_lt by lia.
          destruct (Nat.eq_dec (S j) a) as [Heq | Hne].
          * rewrite (proj2 (Nat.eqb_eq (S j) a) Heq).
            assert (Hz : List.nth (S j)
              (suffix_digit_sums (List.firstn a l)) 0 = 0)
              by (apply List.nth_overflow; lia).
            rewrite Hz.
            lazy beta iota.
            lia.
          * rewrite (proj2 (Nat.eqb_neq (S j) a) Hne).
            rewrite (proj2 (Nat.ltb_lt j a) Hlt).
            lazy beta iota.
            rewrite List.app_nth1 by lia.
            reflexivity.
        + rewrite (proj2 (Nat.eqb_neq (S j) a)) by lia.
          rewrite (proj2 (Nat.ltb_ge j a) Hge).
          lazy beta iota.
          rewrite List.app_nth2 by lia.
          rewrite Hp.
          rewrite (IH (List.skipn a l) (j - a)%nat)
            by (rewrite List.length_skipn; lia).
          rewrite List.nth_skipn.
          replace (a + (j - a))%nat with j by lia.
          destruct (bnd_lens lens (j - a)%nat).
          * reflexivity.
          * rewrite List.app_nth2 by lia.
            rewrite Hp.
            replace (S j - a)%nat with (S (j - a))%nat by lia.
            reflexivity.
    Qed.

    (** ** table plane *)

    Lemma table_x_entry :
      Complete.table_lookup OrchardHonestAssignment.lookup_eqb
        (Complete.table_entries OrchardHonestAssignment.facts) Lookup.TableX =
      Some (List.map SC.sinsemilla_s_x SC.generator_table_indexes,
            SC.sinsemilla_s0_x).
    Proof.
      vm_cast_no_check
        (@eq_refl (option (list Z * Z))
          (Some (List.map SC.sinsemilla_s_x SC.generator_table_indexes,
                 SC.sinsemilla_s0_x))).
    Qed.

    Lemma table_y_entry :
      Complete.table_lookup OrchardHonestAssignment.lookup_eqb
        (Complete.table_entries OrchardHonestAssignment.facts) Lookup.TableY =
      Some (List.map SC.sinsemilla_s_y SC.generator_table_indexes,
            SC.sinsemilla_s0_y).
    Proof.
      vm_cast_no_check
        (@eq_refl (option (list Z * Z))
          (Some (List.map SC.sinsemilla_s_y SC.generator_table_indexes,
                 SC.sinsemilla_s0_y))).
    Qed.

    Lemma indexes_nth (r : Z) :
      0 <= r < 1024 ->
      List.nth (Z.to_nat r) SC.generator_table_indexes 0 = r.
    Proof.
      intros Hr.
      unfold SC.generator_table_indexes.
      change (Z.to_nat (2 ^ SC.sinsemilla_k)) with 1024%nat.
      change 0 with (Z.of_nat 0%nat).
      rewrite List.map_nth.
      rewrite List.seq_nth by lia.
      lia.
    Qed.

    Lemma indexes_length :
      List.length SC.generator_table_indexes = 1024%nat.
    Proof.
      unfold SC.generator_table_indexes.
      rewrite List.length_map, List.length_seq.
      reflexivity.
    Qed.

    Lemma lookup_plane_x (w : HonestInput) (r : Z) :
      0 <= r < 1024 ->
      (Γw w).(Assignment.lookup) Lookup.TableX r = SC.sinsemilla_s_x r.
    Proof.
      intros Hr.
      rewrite lookup_plane.
      unfold Complete.table_value.
      rewrite table_x_entry.
      unfold value_at_row.
      assert (Hlen : (Z.to_nat r <
        List.length (List.map SC.sinsemilla_s_x
          SC.generator_table_indexes))%nat).
      { rewrite List.length_map, indexes_length. lia. }
      rewrite (List.nth_indep _ _ (SC.sinsemilla_s_x 0) Hlen).
      rewrite List.map_nth.
      rewrite indexes_nth by lia.
      reflexivity.
    Qed.

    Lemma lookup_plane_y (w : HonestInput) (r : Z) :
      0 <= r < 1024 ->
      (Γw w).(Assignment.lookup) Lookup.TableY r = SC.sinsemilla_s_y r.
    Proof.
      intros Hr.
      rewrite lookup_plane.
      unfold Complete.table_value.
      rewrite table_y_entry.
      unfold value_at_row.
      assert (Hlen : (Z.to_nat r <
        List.length (List.map SC.sinsemilla_s_y
          SC.generator_table_indexes))%nat).
      { rewrite List.length_map, indexes_length. lia. }
      rewrite (List.nth_indep _ _ (SC.sinsemilla_s_y 0) Hlen).
      rewrite List.map_nth.
      rewrite indexes_nth by lia.
      reflexivity.
    Qed.

    (** The generator table's entries are reduced field elements. *)
    Definition s_entry_ok (i : Z) : bool :=
      (0 <=? SC.sinsemilla_s_x i) &&
      (SC.sinsemilla_s_x i <? Primes.pallas_p) &&
      (0 <=? SC.sinsemilla_s_y i) &&
      (SC.sinsemilla_s_y i <? Primes.pallas_p).

    Lemma s_entries_ok :
      List.forallb s_entry_ok SC.generator_table_indexes = true.
    Proof. vm_cast_no_check (@eq_refl bool true). Qed.

    Lemma s_reduced (r : Z) (Hr : 0 <= r < 1024) :
      0 <= SC.sinsemilla_s_x r < Primes.pallas_p /\
      0 <= SC.sinsemilla_s_y r < Primes.pallas_p.
    Proof.
      assert (Hin : List.In r SC.generator_table_indexes).
      { unfold SC.generator_table_indexes.
        change (Z.to_nat (2 ^ SC.sinsemilla_k)) with 1024%nat.
        apply List.in_map_iff.
        exists (Z.to_nat r).
        split; [lia |].
        apply List.in_seq. lia. }
      pose proof (proj1 (List.forallb_forall s_entry_ok
        SC.generator_table_indexes) s_entries_ok _ Hin) as Hb.
      unfold s_entry_ok in Hb.
      repeat (apply andb_true_iff in Hb; destruct Hb as [Hb ?]).
      repeat match goal with
      | H : (_ <=? _) = true |- _ => apply Z.leb_le in H
      | H : (_ <? _) = true |- _ => apply Z.ltb_lt in H
      end.
      lia.
    Qed.

    (** ** The per-row pair obligations *)

    Definition sins_sel (second : bool) : Selector.t :=
      if second then Selector.QSinsemilla1_2 else Selector.QSinsemilla1_1.

    Definition sins_arg (second : bool) : LookupArgument.t columns :=
      if second then sins2_arg else sins1_arg.

    Definition bits_col (second : bool) : Advice.t :=
      if second then Advice.A7 else Advice.A2.

    Definition qfac (q : Z) : Z := q - q * (q - 1).

    Lemma sins_row (second : bool) (w : HonestInput) (region : RegionId.t)
        (row : Z) (A G : Point.t) (zc zn qv wd : Z)
        (Hsel : (Γw w).(Assignment.selector) (sins_sel second) region row = 1)
        (Hxa : (Γw w).(Assignment.advice) (xa_col second) region row = Point.x A)
        (Hxp : (Γw w).(Assignment.advice) (xp_col second) region row = Point.x G)
        (Hl1 : (Γw w).(Assignment.advice) (l1_col second) region row = rr_l1 A G)
        (Hl2 : (Γw w).(Assignment.advice) (l2_col second) region row = rr_l2 A G)
        (Hzc : (Γw w).(Assignment.advice) (bits_col second) region row = zc)
        (Hzn : (Γw w).(Assignment.advice) (bits_col second) region (row + 1) = zn)
        (Hq : (Γw w).(Assignment.fixed) (q2_col second) region row = qv)
        (Hwd : 0 <= wd < 1024)
        (HG : G = SinsemillaSpec.generator wd)
        (Hword : zc = wd + qfac qv * 1024 * zn)
        (Hnd1 : BinOp.sub (Point.x A) (Point.x G) <> 0)
        (Hnd2 : BinOp.sub (Point.x (rr_mid A G)) (Point.x A) <> 0) :
      eval_lookup_argument (Γw w) (region, row) 1024 (sins_arg second).
    Proof.
      assert (Harg : forall s : bool, sins_arg s =
        SC.generator_table_argument (sins_sel s) (q2_col s)
          (xa_col s) (xp_col s) (bits_col s) (l1_col s) (l2_col s))
        by (intro s; destruct s; reflexivity).
      unfold eval_lookup_argument.
      exists wd.
      split; [lia |].
      rewrite Harg.
      unfold SC.generator_table_argument.
      cbn [LookupArgument.pairs].
      repeat apply List.Forall_cons; [ | | | apply List.Forall_nil ].
      all: unfold SC.generator_table_word, SC.generator_table_y_p,
        SC.q_s3, SC.y_a.
      all: cbn [eval_expression eval_selector].
      all: unfold rotated_row.
      all: cbn [Rotation.offset].
      all: rewrite !Z.add_0_r.
      all: rewrite ?Hsel, ?Hxa, ?Hxp, ?Hl1, ?Hl2, ?Hzc, ?Hzn, ?Hq.
      all: unfold SC.x_r.
      all: cbn [eval_expression Rotation.next Rotation.cur Rotation.offset].
      all: unfold rotated_row.
      all: cbn [Rotation.cur Rotation.offset].
      all: rewrite ?Z.add_0_r.
      all: rewrite ?Hsel, ?Hxa, ?Hxp, ?Hl1, ?Hl2, ?Hzc, ?Hzn, ?Hq.
      change (2 ^ SC.sinsemilla_k) with 1024.
      3: unfold Garden.Halo2.halo2_gadgets.utilities.square.
      3: cbn [eval_expression].
      3: unfold rotated_row.
      3: cbn [Rotation.cur Rotation.offset].
      3: rewrite ?Z.add_0_r.
      3: rewrite ?Hl1.
      (* The word pair: the running-sum slice telescopes to the round word. *)
      1: rewrite lookup_plane_idx by lia.
      1: apply eqm_reduced;
         [ | apply binop_mul_reduced | pose proof pallas_p_1024; lia ].
      1: strip_mods.
      1: apply eqm_of_ring.
      1: rewrite Hword; unfold qfac; ring.
      (* The abscissa pair: the stored generator abscissa is the table entry. *)
      1: rewrite lookup_plane_x by lia.
      1: apply eqm_reduced;
         [ | apply binop_add_reduced | exact (proj1 (s_reduced wd ltac:(lia))) ].
      1: strip_mods.
      1: apply eqm_of_ring.
      1: rewrite HG; unfold SC.sinsemilla_s_x, SinsemillaSpec.generator;
         cbn [Point.x]; ring.
      (* The ordinate pair: the [y_p] reconstruction over the two chords. *)
      rewrite lookup_plane_y by lia.
      replace (SC.sinsemilla_s_y wd) with (Point.y G)
        by (rewrite HG; unfold SC.sinsemilla_s_y, SinsemillaSpec.generator;
            cbn [Point.y]; reflexivity).
      apply eqm_reduced;
        [ | apply binop_add_reduced
          | rewrite HG; unfold SinsemillaSpec.generator; cbn [Point.y];
            exact (proj2 (s_reduced wd ltac:(lia))) ].
      pose proof (mid_x_eqm A G) as F1.
      pose proof (mid_y_eqm A G) as F2.
      pose proof (chord2_mul A G Hnd2) as F3.
      pose proof (chord1_mul A G Hnd1) as F4.
      assert (Ht : Zdiv.eqm Primes.pallas_p (2 * constants.two_inv) 1)
        by (vm_cast_no_check (@eq_refl Z 1)).
      clear - F1 F2 F3 F4 Ht.
      revert F1 F2 F3 F4 Ht.
      generalize (Point.y (rr_mid A G)); intro ym.
      generalize (Point.x (rr_mid A G)); intro m.
      generalize (rr_l1 A G); intro l1.
      generalize (rr_l2 A G); intro l2.
      generalize (Point.x A); intro xa.
      generalize (Point.y A); intro ya.
      generalize (Point.x G); intro xp.
      generalize (Point.y G); intro yp.
      generalize constants.two_inv; intro t.
      generalize SC.sinsemilla_s0_y; intro c.
      intros F1 F2 F3 F4 Ht.
      strip_mods.
      apply (eqm_of_diff _ _
        (ya * (2 * t - 1) +
         ((l1 + l2) * t * (m - (l1 * l1 - xa - xp)) +
          ((- t) * (ym - (l1 * (xa - m) - ya)) +
           ((- t) * (l2 * (m - xa) - (ym - ya)) +
            (- (1)) * (l1 * (xa - xp) - (ya - yp))))))).
      - repeat apply mod0_add; apply mod0_mul; apply eqm_diff_zero;
          [ exact Ht | exact F1 | exact F2 | exact F3 | exact F4 ].
      - ring.
    Qed.

    (** ** The [bits] column cell *)

    Lemma hd_bits_of (Q : Point.t) (pieces : list (list Z)) :
      hd_bits (hash_data_of Q pieces) = bits_column pieces.
    Proof.
      unfold hash_data_of.
      destruct (hash_go Q (Stdlib.Lists.List.concat pieces)) as [rows out].
      reflexivity.
    Qed.

    Lemma logical_bits (second : bool) :
      logical_col second (bits_col second) = Some 2%nat.
    Proof. destruct second; reflexivity. Qed.

    Lemma hash_cell_bits (Q : Point.t) (pieces : list (list Z)) (second : bool)
        (j : nat) :
      hash_region_advice_t (hash_data_of Q pieces) second (bits_col second)
        (Z.of_nat j) = List.nth j (bits_column pieces) 0.
    Proof.
      unfold hash_region_advice_t.
      rewrite logical_bits, hd_bits_of.
      rewrite (proj2 (Z.leb_le 0 (Z.of_nat j)) ltac:(lia)).
      rewrite Nat2Z.id.
      reflexivity.
    Qed.

    (** ** The site lemma *)

    Definition row_cert (second : bool) (region : RegionId.t) (lens : list nat)
        (j : nat) : bool :=
      memb (sins_sel second) region (Z.of_nat j) &&
      (qfac (fixed_at (q2_col second) region (Z.of_nat j)) =?
         (if bnd_lens lens j then 0 else 1)).

    Lemma sins_site_generic
        (second : bool) (region : RegionId.t) (Q : Point.t) (lens : list nat)
        (n : nat) (msg : HonestInput -> list Z)
        (Hadv : forall (w : HonestInput) (col : Advice.t) (row : Z),
          (Γw w).(Assignment.advice) col region row =
          hash_region_advice_t (hash_data_of Q (split_pieces lens (msg w)))
            second col row)
        (Hlen : forall w : HonestInput, List.length (msg w) = n)
        (Hlens : lens_sum lens = n)
        (Hbound : forall w : HonestInput,
          List.Forall (fun d => 0 <= d < 1024) (msg w))
        (HQ : 0 <= Point.x Q < Primes.pallas_p)
        (Hnondeg : forall w : HonestInput, valid w -> nondegenerate w ->
          SinsemillaHash.nondegenerate Q (msg w))
        (Hcert : List.forallb (row_cert second region lens)
          (List.seq 0%nat n) = true) :
      sins_site_sound (sins_arg second) region (Z.of_nat n).
    Proof.
      intros w Hv Hnd row Hrow.
      pose proof (Hlen w) as Hlw.
      pose proof (Hnondeg w Hv Hnd) as Hnw.
      pose proof (Hadv w) as Hadvw.
      set (ws := msg w) in *.
      assert (Hcat : Stdlib.Lists.List.concat (split_pieces lens ws) = ws).
      { apply concat_split_pieces. rewrite Hlw. exact Hlens. }
      set (j := Z.to_nat row).
      assert (Hjn : (j < n)%nat) by (unfold j; lia).
      assert (Hrowj : row = Z.of_nat j) by (unfold j; lia).
      pose proof (forallb_seq_sound _ 0%nat n Hcert j ltac:(lia)) as Hc.
      apply andb_true_iff in Hc.
      destruct Hc as [Hmemb Hqf].
      apply Z.eqb_eq in Hqf.
      assert (Hjw : (j < List.length ws)%nat) by lia.
      set (wd := List.nth j ws 0).
      assert (Hwd : 0 <= wd < 1024)
        by (apply nth_bound_1024; apply Hbound).
      apply (sins_row second w region row
        (sinsemilla_acc Q ws j) (SinsemillaSpec.generator wd)
        (List.nth j (bits_column (split_pieces lens ws)) 0)
        (List.nth (S j) (bits_column (split_pieces lens ws)) 0)
        (fixed_at (q2_col second) region (Z.of_nat j))
        wd).
      - rewrite selector_plane, Hrowj, Hmemb. reflexivity.
      - rewrite Hadvw, Hrowj.
        rewrite (hash_cell_xa Q (split_pieces lens ws) second j ltac:(rewrite Hcat; lia)).
        rewrite Hcat. reflexivity.
      - rewrite Hadvw, Hrowj.
        rewrite (hash_cell_xp Q (split_pieces lens ws) second j ltac:(rewrite Hcat; lia)).
        rewrite Hcat. reflexivity.
      - rewrite Hadvw, Hrowj.
        rewrite (hash_cell_l1 Q (split_pieces lens ws) second j ltac:(rewrite Hcat; lia)).
        rewrite Hcat. reflexivity.
      - rewrite Hadvw, Hrowj.
        rewrite (hash_cell_l2 Q (split_pieces lens ws) second j ltac:(rewrite Hcat; lia)).
        rewrite Hcat. reflexivity.
      - rewrite Hadvw, Hrowj.
        apply hash_cell_bits.
      - rewrite Hadvw, Hrowj.
        replace (Z.of_nat j + 1) with (Z.of_nat (S j)) by lia.
        apply hash_cell_bits.
      - rewrite Hrowj. apply fixed_at_read.
      - exact Hwd.
      - reflexivity.
      - rewrite Hqf.
        rewrite (bits_step lens ws j ltac:(rewrite Hlw; exact Hlens) Hjw).
        change (2 ^ 10) with 1024.
        destruct (bnd_lens lens j); lia.
      - apply (chord1_nonzero Q ws j HQ Hjw); [| exact Hnw].
        exact (proj1 (s_reduced wd Hwd)).
      - exact (chord2_nonzero Q ws j HQ Hjw Hnw).
    Qed.

    (** ** Domain-point reducedness *)

    Ltac bool_bounds H :=
      apply andb_true_iff in H; destruct H as [H ?];
      apply andb_true_iff in H; destruct H as [H ?];
      apply andb_true_iff in H; destruct H as [H ?];
      repeat match goal with
      | K : (_ <=? _) = true |- _ => apply Z.leb_le in K
      | K : (_ <? _) = true |- _ => apply Z.ltb_lt in K
      end;
      apply Z.leb_le in H.

    Lemma merkle_Q_x : 0 <= Point.x merkle_Q < Primes.pallas_p.
    Proof. pose proof merkle_Q_reduced as H. bool_bounds H. lia. Qed.

    Lemma nc_Q_x : 0 <= Point.x note_commit_Q < Primes.pallas_p.
    Proof.
      pose proof nc_Q_reduced as H.
      unfold note_commit_Q.
      bool_bounds H. lia.
    Qed.

    Lemma civk_Q_x : 0 <= Point.x commit_ivk_Q < Primes.pallas_p.
    Proof.
      pose proof civk_Q_reduced as H.
      unfold commit_ivk_Q.
      bool_bounds H. lia.
    Qed.

    (** ** The Merkle hash-region sites *)

    Lemma layer_index_lt (layer : RegionId.Merkle.Layer.t) :
      (Z.to_nat (RegionId.Merkle.Layer.to_index layer) < 32)%nat.
    Proof. destruct layer; cbn; lia. Qed.

    Lemma advice_merkle_hash (w : HonestInput)
        (layer : RegionId.Merkle.Layer.t) (col : Advice.t) (row : Z) :
      (Γw w).(Assignment.advice) col (merkle_h2p layer) row =
      hash_region_advice_t
        (hash_data_of merkle_Q
          (split_pieces merkle_lens
            (merkle_layer_words w
              (Z.to_nat (RegionId.Merkle.Layer.to_index layer)))))
        (layer_second layer) col row.
    Proof.
      rewrite advice_merkle_h2p.
      rewrite (t_layers_nth w _ (layer_index_lt layer)).
      reflexivity.
    Qed.

    Lemma merkle_row_certs :
      List.forallb
        (fun layer =>
          List.forallb
            (row_cert (layer_second layer) (merkle_h2p layer) merkle_lens)
            (List.seq 0%nat 52%nat))
        all_layers = true.
    Proof. vm_cast_no_check (@eq_refl bool true). Qed.

    Lemma sins_site_merkle (layer : RegionId.Merkle.Layer.t) :
      sins_site_sound (sins_arg (layer_second layer)) (merkle_h2p layer) 52.
    Proof.
      change 52 with (Z.of_nat 52%nat).
      apply (sins_site_generic (layer_second layer) (merkle_h2p layer) merkle_Q
        merkle_lens 52%nat
        (fun w =>
          merkle_layer_words w
            (Z.to_nat (RegionId.Merkle.Layer.to_index layer)))).
      - intros w col row. apply advice_merkle_hash.
      - intros w. apply merkle_words_length.
      - reflexivity.
      - intros w.
        unfold merkle_layer_words.
        cbv zeta.
        destruct (path_bit w _);
          unfold SinsemillaSpec.merkle_message; apply words_le_bound.
      - exact merkle_Q_x.
      - intros w Hv Hnd.
        exact (proj1 Hnd _ (layer_index_lt layer)).
      - exact (proj1 (List.forallb_forall _ all_layers) merkle_row_certs layer
          (all_layers_complete layer)).
    Qed.

    (** ** The note-commitment and [Commit^ivk] hash-region sites *)

    Lemma civk_row_certs :
      List.forallb (row_cert false civk_h2p commit_ivk_lens)
        (List.seq 0%nat 51%nat) = true.
    Proof. vm_cast_no_check (@eq_refl bool true). Qed.

    Lemma nc_old_row_certs :
      List.forallb
        (row_cert false (nc_h2p RegionId.NoteCommit.Which.Old) note_commit_lens)
        (List.seq 0%nat 109%nat) = true.
    Proof. vm_cast_no_check (@eq_refl bool true). Qed.

    Lemma nc_new_row_certs :
      List.forallb
        (row_cert true (nc_h2p RegionId.NoteCommit.Which.New) note_commit_lens)
        (List.seq 0%nat 109%nat) = true.
    Proof. vm_cast_no_check (@eq_refl bool true). Qed.

    Lemma sins_site_civk_go :
      sins_site_sound (sins_arg false) civk_h2p 51.
    Proof.
      change 51 with (Z.of_nat 51%nat).
      apply (sins_site_generic false civk_h2p commit_ivk_Q commit_ivk_lens
        51%nat commit_ivk_words).
      - intros w col row.
        rewrite advice_civk_h2p, t_civk_hash_of.
        reflexivity.
      - intros w. apply commit_ivk_words_length.
      - reflexivity.
      - intros w. apply words_le_bound.
      - exact civk_Q_x.
      - intros w Hv Hnd.
        exact (proj1 (proj2 (proj2 (proj2 Hnd)))).
      - exact civk_row_certs.
    Qed.

    Lemma sins_site_nc_old_go :
      sins_site_sound (sins_arg false) (nc_h2p RegionId.NoteCommit.Which.Old) 109.
    Proof.
      change 109 with (Z.of_nat 109%nat).
      apply (sins_site_generic false (nc_h2p RegionId.NoteCommit.Which.Old)
        note_commit_Q note_commit_lens 109%nat note_commit_old_words).
      - intros w col row.
        rewrite advice_nc_old_h2p, t_nc_old_hash_of.
        reflexivity.
      - intros w. apply note_commit_message_length.
      - reflexivity.
      - intros w. apply words_le_bound.
      - exact nc_Q_x.
      - intros w Hv Hnd.
        exact (proj1 (proj2 Hnd)).
      - exact nc_old_row_certs.
    Qed.

    Lemma sins_site_nc_new_go :
      sins_site_sound (sins_arg true) (nc_h2p RegionId.NoteCommit.Which.New) 109.
    Proof.
      change 109 with (Z.of_nat 109%nat).
      apply (sins_site_generic true (nc_h2p RegionId.NoteCommit.Which.New)
        note_commit_Q note_commit_lens 109%nat note_commit_new_words).
      - intros w col row.
        rewrite advice_nc_new_h2p, t_nc_new_hash_of.
        reflexivity.
      - intros w. apply note_commit_message_length.
      - reflexivity.
      - intros w. apply words_le_bound.
      - exact nc_Q_x.
      - intros w Hv Hnd.
        exact (proj1 (proj2 (proj2 Hnd))).
      - exact nc_new_row_certs.
    Qed.

    (** ** The variant split of the Merkle layers *)

    Lemma layers_1_second (layer : RegionId.Merkle.Layer.t) :
      List.In layer layers_1 -> layer_second layer = false.
    Proof.
      destruct layer; intros Hlay; try reflexivity;
        exfalso; vm_compute in Hlay; intuition discriminate.
    Qed.

    Lemma layers_2_second (layer : RegionId.Merkle.Layer.t) :
      List.In layer layers_2 -> layer_second layer = true.
    Proof.
      destruct layer; intros Hlay; try reflexivity;
        exfalso; vm_compute in Hlay; intuition discriminate.
    Qed.

    (** ** The five site leaves *)

    Lemma leaf_merkle_1 (layer : RegionId.Merkle.Layer.t)
        (Hlay : List.In layer layers_1) :
      sins_site_sound sins1_arg
        (RegionId.Merkle layer RegionId.Merkle.Region.HashToPoint) 52.
    Proof.
      pose proof (sins_site_merkle layer) as H.
      rewrite (layers_1_second layer Hlay) in H.
      exact H.
    Qed.

    Lemma leaf_merkle_2 (layer : RegionId.Merkle.Layer.t)
        (Hlay : List.In layer layers_2) :
      sins_site_sound sins2_arg
        (RegionId.Merkle layer RegionId.Merkle.Region.HashToPoint) 52.
    Proof.
      pose proof (sins_site_merkle layer) as H.
      rewrite (layers_2_second layer Hlay) in H.
      exact H.
    Qed.

    Lemma leaf_civk :
      sins_site_sound sins1_arg
        (RegionId.CommitIvk RegionId.CommitIvk.HashToPoint) 51.
    Proof. exact sins_site_civk_go. Qed.

    Lemma leaf_nc_old :
      sins_site_sound sins1_arg
        (RegionId.NoteCommit RegionId.NoteCommit.Which.Old
          RegionId.NoteCommit.HashToPoint) 109.
    Proof. exact sins_site_nc_old_go. Qed.

    Lemma leaf_nc_new :
      sins_site_sound sins2_arg
        (RegionId.NoteCommit RegionId.NoteCommit.Which.New
          RegionId.NoteCommit.HashToPoint) 109.
    Proof. exact sins_site_nc_new_go. Qed.

  End SinsemillaSites.

  Lemma sins_site_merkle_1 (layer : RegionId.Merkle.Layer.t)
      (Hlay : List.In layer layers_1) :
    sins_site_sound sins1_arg
      (RegionId.Merkle layer RegionId.Merkle.Region.HashToPoint) 52.
  Proof. exact (SinsemillaSites.leaf_merkle_1 layer Hlay). Qed.

  Lemma sins_site_merkle_2 (layer : RegionId.Merkle.Layer.t)
      (Hlay : List.In layer layers_2) :
    sins_site_sound sins2_arg
      (RegionId.Merkle layer RegionId.Merkle.Region.HashToPoint) 52.
  Proof. exact (SinsemillaSites.leaf_merkle_2 layer Hlay). Qed.

  Lemma sins_site_civk :
    sins_site_sound sins1_arg
      (RegionId.CommitIvk RegionId.CommitIvk.HashToPoint) 51.
  Proof. exact SinsemillaSites.leaf_civk. Qed.

  Lemma sins_site_nc_old :
    sins_site_sound sins1_arg
      (RegionId.NoteCommit RegionId.NoteCommit.Which.Old
        RegionId.NoteCommit.HashToPoint) 109.
  Proof. exact SinsemillaSites.leaf_nc_old. Qed.

  Lemma sins_site_nc_new :
    sins_site_sound sins2_arg
      (RegionId.NoteCommit RegionId.NoteCommit.Which.New
        RegionId.NoteCommit.HashToPoint) 109.
  Proof. exact SinsemillaSites.leaf_nc_new. Qed.

  (** ** Site-table soundness *)

  Lemma running_sites_sound :
    List.Forall (fun '(r, n) => sins_site_sound range_check_arg r n)
      running_sites.
  Proof.
    unfold running_sites.
    constructor; [exact site_alpha |].
    constructor; [exact site_overflow |].
    constructor; [exact site_civk_ak |].
    constructor; [exact site_civk_nk |].
    constructor; [exact site_nc_old_xgd |].
    constructor; [exact site_nc_old_xpkd |].
    constructor; [exact site_nc_old_rho |].
    constructor; [exact site_nc_old_psi |].
    constructor; [exact site_ycan_old_gd_j |].
    constructor; [exact site_ycan_old_gd_jp |].
    constructor; [exact site_ycan_old_pkd_j |].
    constructor; [exact site_ycan_old_pkd_jp |].
    constructor; [exact site_nc_new_xgd |].
    constructor; [exact site_nc_new_xpkd |].
    constructor; [exact site_nc_new_rho |].
    constructor; [exact site_nc_new_psi |].
    constructor; [exact site_ycan_new_gd_j |].
    constructor; [exact site_ycan_new_gd_jp |].
    constructor; [exact site_ycan_new_pkd_j |].
    constructor; [exact site_ycan_new_pkd_jp |].
    constructor.
  Qed.

  Lemma short_sites_sound :
    List.Forall short_site_sound short_sites.
  Proof.
    unfold short_sites.
    apply List.Forall_app; split.
    { apply (proj2 (List.Forall_forall _ _)).
      intros x Hx.
      apply List.in_map_iff in Hx.
      destruct Hx as (layer & <- & _).
      apply site_merkle_b1. }
    apply List.Forall_app; split.
    { apply (proj2 (List.Forall_forall _ _)).
      intros x Hx.
      apply List.in_map_iff in Hx.
      destruct Hx as (layer & <- & _).
      apply site_merkle_b2. }
    constructor; [exact site_civk_b0 |].
    constructor; [exact site_civk_b2 |].
    constructor; [exact site_civk_d0 |].
    constructor; [apply site_nc_b0 |].
    constructor; [apply site_nc_b3 |].
    constructor; [apply site_nc_d2 |].
    constructor; [apply site_nc_e0 |].
    constructor; [apply site_nc_e1 |].
    constructor; [apply site_nc_g1 |].
    constructor; [apply site_nc_h0 |].
    constructor; [apply site_ycan_k0 |].
    constructor; [apply site_ycan_k2 |].
    constructor; [apply site_ycan_k0 |].
    constructor; [apply site_ycan_k2 |].
    constructor; [apply site_nc_b0 |].
    constructor; [apply site_nc_b3 |].
    constructor; [apply site_nc_d2 |].
    constructor; [apply site_nc_e0 |].
    constructor; [apply site_nc_e1 |].
    constructor; [apply site_nc_g1 |].
    constructor; [apply site_nc_h0 |].
    constructor; [apply site_ycan_k0 |].
    constructor; [apply site_ycan_k2 |].
    constructor; [apply site_ycan_k0 |].
    constructor; [apply site_ycan_k2 |].
    constructor.
  Qed.

  Lemma sins1_sites_sound :
    List.Forall (fun '(r, n) => sins_site_sound sins1_arg r n) sins1_sites.
  Proof.
    unfold sins1_sites.
    apply List.Forall_app; split.
    { apply (proj2 (List.Forall_forall _ _)).
      intros x Hx.
      apply List.in_map_iff in Hx.
      destruct Hx as (layer & <- & Hlay).
      exact (sins_site_merkle_1 layer Hlay). }
    constructor; [exact sins_site_civk |].
    constructor; [exact sins_site_nc_old |].
    constructor.
  Qed.

  Lemma sins2_sites_sound :
    List.Forall (fun '(r, n) => sins_site_sound sins2_arg r n) sins2_sites.
  Proof.
    unfold sins2_sites.
    apply List.Forall_app; split.
    { apply (proj2 (List.Forall_forall _ _)).
      intros x Hx.
      apply List.in_map_iff in Hx.
      destruct Hx as (layer & <- & Hlay).
      exact (sins_site_merkle_2 layer Hlay). }
    constructor; [exact sins_site_nc_new |].
    constructor.
  Qed.

  (** ** Membership dispatch *)

  Definition site_range_memb (sites : list (RegionId.t * Z))
      (region : RegionId.t) (row : Z) : bool :=
    List.existsb
      (fun '(r, n) =>
        OrchardDecidableEq.region_id_eqb region r &&
        (0 <=? row) && (row <? n))
      sites.

  Definition short_site_memb (sites : list RegionId.t)
      (region : RegionId.t) (row : Z) : bool :=
    List.existsb
      (fun r =>
        OrchardDecidableEq.region_id_eqb region r &&
        ((row =? 0) || (row =? 1)))
      sites.

  Lemma site_table_sound (arg : LookupArgument.t columns)
      (sites : list (RegionId.t * Z))
      (Hsound : List.Forall (fun '(r, n) => sins_site_sound arg r n) sites)
      (w : HonestInput) (Hv : valid w) (Hnd : nondegenerate w)
      (region : RegionId.t) (row : Z)
      (Hm : site_range_memb sites region row = true) :
    eval_lookup_argument (Γw w) (region, row) 1024 arg.
  Proof.
    apply List.existsb_exists in Hm.
    destruct Hm as ([r n] & Hin & Hb).
    apply andb_true_iff in Hb; destruct Hb as [Hb Hlt].
    apply andb_true_iff in Hb; destruct Hb as [Heq Hge].
    apply OrchardDecidableEq.region_id_eqb_eq in Heq.
    subst r.
    apply Z.leb_le in Hge.
    apply Z.ltb_lt in Hlt.
    exact (proj1 (List.Forall_forall _ _) Hsound _ Hin
      w Hv Hnd row (conj Hge Hlt)).
  Qed.

  Lemma short_table_sound (sites : list RegionId.t)
      (Hsound : List.Forall short_site_sound sites)
      (w : HonestInput) (Hv : valid w) (Hnd : nondegenerate w)
      (region : RegionId.t) (row : Z)
      (Hm : short_site_memb sites region row = true) :
    eval_lookup_argument (Γw w) (region, row) 1024 range_check_arg.
  Proof.
    apply List.existsb_exists in Hm.
    destruct Hm as (r & Hin & Hb).
    apply andb_true_iff in Hb; destruct Hb as [Heq Hrow].
    apply OrchardDecidableEq.region_id_eqb_eq in Heq.
    subst r.
    apply orb_true_iff in Hrow.
    apply (proj1 (List.Forall_forall _ _) Hsound _ Hin w Hv Hnd row).
    destruct Hrow as [Hrow | Hrow]; [left | right];
      apply Z.eqb_eq in Hrow; exact Hrow.
  Qed.

  (** ** The whole-circuit scan certificate

      Every enabled point carrying a lookup-gating selector lies in the site
      tables. *)

  Definition lookup_point_b (pt : Selector.t * RegionId.t * Z) : bool :=
    let '(sel, region, row) := pt in
    match sel with
    | Selector.QLookup | Selector.QRunning =>
        site_range_memb running_sites region row ||
        short_site_memb short_sites region row
    | Selector.QSinsemilla1_1 => site_range_memb sins1_sites region row
    | Selector.QSinsemilla1_2 => site_range_memb sins2_sites region row
    | _ => true
    end.

  Lemma lookup_scan : List.forallb lookup_point_b enabled = true.
  Proof.
    vm_cast_no_check (@eq_refl bool true).
  Qed.

  (** ** Which selectors the arguments mention *)

  Lemma range_mentions_inv (sel : Selector.t) :
    Complete.arg_mentions_selector OrchardDecidableEq.selector_eqb sel
      range_check_arg = true ->
    sel = Selector.QLookup \/ sel = Selector.QRunning.
  Proof.
    destruct sel; intros H; vm_compute in H; try discriminate H;
      [left; reflexivity | right; reflexivity].
  Qed.

  Lemma sins1_mentions_inv (sel : Selector.t) :
    Complete.arg_mentions_selector OrchardDecidableEq.selector_eqb sel
      sins1_arg = true ->
    sel = Selector.QSinsemilla1_1.
  Proof.
    destruct sel; intros H; vm_compute in H; try discriminate H.
    reflexivity.
  Qed.

  Lemma sins2_mentions_inv (sel : Selector.t) :
    Complete.arg_mentions_selector OrchardDecidableEq.selector_eqb sel
      sins2_arg = true ->
    sel = Selector.QSinsemilla1_2.
  Proof.
    destruct sel; intros H; vm_compute in H; try discriminate H.
    reflexivity.
  Qed.

  (** ** The lookup obligation, over the whole family partition *)

  Theorem lookups_forward_ok : family_lookups_ok all_families.
  Proof.
    intros w Hv Hnd sel region row Hin Hfam arg Harg Hment.
    rewrite lookups_eq in Harg.
    destruct Harg as [Heqarg | [Heqarg | [Heqarg | Habs ] ] ];
      [ | | | destruct Habs ]; subst arg.
    - (* The 10-bit range-check argument. *)
      pose proof (proj1 (List.forallb_forall lookup_point_b enabled)
        lookup_scan _ Hin) as Hpt.
      destruct (range_mentions_inv sel Hment) as [-> | ->];
        cbn [lookup_point_b] in Hpt;
        (apply orb_true_iff in Hpt;
         destruct Hpt as [Hm | Hm];
         [ exact (site_table_sound range_check_arg running_sites
             running_sites_sound w Hv Hnd region row Hm)
         | exact (short_table_sound short_sites short_sites_sound
             w Hv Hnd region row Hm) ]).
    - (* The first generator-table argument. *)
      pose proof (sins1_mentions_inv sel Hment) as Heq.
      subst sel.
      pose proof (proj1 (List.forallb_forall lookup_point_b enabled)
        lookup_scan _ Hin) as Hpt.
      cbn [lookup_point_b] in Hpt.
      exact (site_table_sound sins1_arg sins1_sites sins1_sites_sound
        w Hv Hnd region row Hpt).
    - (* The second generator-table argument. *)
      pose proof (sins2_mentions_inv sel Hment) as Heq.
      subst sel.
      pose proof (proj1 (List.forallb_forall lookup_point_b enabled)
        lookup_scan _ Hin) as Hpt.
      cbn [lookup_point_b] in Hpt.
      exact (site_table_sound sins2_arg sins2_sites sins2_sites_sound
        w Hv Hnd region row Hpt).
  Qed.

  (** ** The witness facts

      The copy/constant/instance facts of the synthesis program, split by the
      Boolean [fact_trivial]: a self-copy (identical source and target cell)
      holds of any assignment; the residue — the genuine cross-region copies,
      the pinned constants and the instance rows — is the open leaf
      [nontrivial_witness_facts]. *)

  Definition cell_eqb (c1 c2 : Cell.t columns RegionId.t) : bool :=
    match Cell.column c1, Cell.column c2 with
    | ColumnRef.Advice a1, ColumnRef.Advice a2 =>
        OrchardDecidableEq.advice_eqb a1 a2
    | ColumnRef.Fixed f1, ColumnRef.Fixed f2 =>
        OrchardDecidableEq.fixed_eqb f1 f2
    | ColumnRef.Instance_ i1, ColumnRef.Instance_ i2 =>
        OrchardDecidableEq.instance_eqb i1 i2
    | _, _ => false
    end &&
    OrchardDecidableEq.region_id_eqb (Cell.region c1) (Cell.region c2) &&
    (Cell.row_offset c1 =? Cell.row_offset c2).

  Lemma cell_eqb_eq (c1 c2 : Cell.t columns RegionId.t) :
    cell_eqb c1 c2 = true -> c1 = c2.
  Proof.
    destruct c1 as [col1 r1 o1], c2 as [col2 r2 o2].
    unfold cell_eqb; cbn.
    intros H.
    apply andb_true_iff in H; destruct H as [H Ho].
    apply andb_true_iff in H; destruct H as [Hc Hr].
    apply Z.eqb_eq in Ho.
    apply OrchardDecidableEq.region_id_eqb_eq in Hr.
    subst.
    destruct col1 as [a1 | f1 | i1], col2 as [a2 | f2 | i2];
      try discriminate Hc.
    - apply OrchardDecidableEq.advice_eqb_eq in Hc. subst. reflexivity.
    - apply OrchardDecidableEq.fixed_eqb_eq in Hc. subst. reflexivity.
    - apply OrchardDecidableEq.instance_eqb_eq in Hc. subst. reflexivity.
  Qed.

  Definition fact_trivial (fact : Fact.t columns RegionId.t) : bool :=
    match fact with
    | Fact.CellsEqual c1 c2 => cell_eqb c1 c2
    | _ => false
    end.

  Lemma fact_trivial_sound (Γ : Assignment.t columns RegionId.t)
      (fact : Fact.t columns RegionId.t) :
    fact_trivial fact = true -> interpret_fact Γ fact.
  Proof.
    destruct fact; cbn [fact_trivial]; intros H; try discriminate H.
    apply cell_eqb_eq in H.
    rewrite H.
    cbn [interpret_fact].
    reflexivity.
  Qed.

  (** ** The nontrivial witness facts

      The non-self-copy residue of [witness_facts facts]: the genuine
      cross-region copies, the pinned constants and the instance rows.
      The list is pinned as a literal, and its coverage of the reified
      facts is one input-independent [vm_compute] scan ([nt_cover]).

      [nt_closed] carries the facts proved here, grouped by the shape of
      their proof: the bulk are the copies whose two cell addresses the
      advice dispatch sends to the same reader expression, so the goal is
      a syntactic identity between two stuck projections of the hoisted
      record; the remaining groups are the blinding-leg boundaries and
      the Merkle chain, closed from the projection lemmas below.
      [nt_open] carries the residue, whose two sides are different
      derivations of one value. *)

  (** The hoisted derivation record stays a stuck atom for the rest of
      the module: a reduction that unfolds [tables_of] on symbolic input
      normalizes the Sinsemilla, ladder and Poseidon folds it carries.
      The field inverse, the complete-addition output and the scalar
      multiplications join it, so a cell reduction stops at the reader
      leaves (docs/compile-performance.md). *)
  #[local] Strategy opaque
    [OrchardCompletenessTables.tables_of
     BinOp.div mod_inverse CompleteAddition.output
     Pallas.mul Weierstrass.mul].

  Definition fact_beq (f g : Fact.t columns RegionId.t) : bool :=
    match f, g with
    | Fact.CellsEqual a b, Fact.CellsEqual c d =>
        cell_eqb a c && cell_eqb b d
    | Fact.CellIsConstant a u, Fact.CellIsConstant c v =>
        cell_eqb a c && (u =? v)
    | Fact.InstanceIs a i r, Fact.InstanceIs c j s =>
        cell_eqb a c && OrchardDecidableEq.instance_eqb i j && (r =? s)
    | _, _ => false
    end.

  Lemma fact_beq_eq (f g : Fact.t columns RegionId.t) :
    fact_beq f g = true -> f = g.
  Proof.
    destruct f, g; cbn [fact_beq]; intros Hb; try discriminate Hb.
    - apply andb_true_iff in Hb; destruct Hb as [H1 H2].
      rewrite (cell_eqb_eq _ _ H1), (cell_eqb_eq _ _ H2). reflexivity.
    - apply andb_true_iff in Hb; destruct Hb as [Hb Hr].
      apply andb_true_iff in Hb; destruct Hb as [H1 Hi].
      apply Z.eqb_eq in Hr.
      apply OrchardDecidableEq.instance_eqb_eq in Hi.
      rewrite (cell_eqb_eq _ _ H1). subst. reflexivity.
    - apply andb_true_iff in Hb; destruct Hb as [H1 Hv].
      apply Z.eqb_eq in Hv.
      rewrite (cell_eqb_eq _ _ H1). subst. reflexivity.
  Qed.

  Lemma in_of_beq (f : Fact.t columns RegionId.t)
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

  Definition wf_mnode_0 : list (Fact.t columns RegionId.t) := [
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L0 RegionId.Merkle.Region.NodePosition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.WitnessInput RegionId.WitnessInput.CmOld; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L1 RegionId.Merkle.Region.NodePosition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L0 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 52 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L2 RegionId.Merkle.Region.NodePosition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L1 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 52 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L3 RegionId.Merkle.Region.NodePosition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L2 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 52 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L4 RegionId.Merkle.Region.NodePosition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L3 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 52 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L5 RegionId.Merkle.Region.NodePosition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L4 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 52 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L6 RegionId.Merkle.Region.NodePosition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L5 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 52 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L7 RegionId.Merkle.Region.NodePosition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L6 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 52 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L8 RegionId.Merkle.Region.NodePosition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L7 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 52 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L9 RegionId.Merkle.Region.NodePosition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L8 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 52 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L10 RegionId.Merkle.Region.NodePosition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L9 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 52 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L11 RegionId.Merkle.Region.NodePosition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L10 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 52 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L12 RegionId.Merkle.Region.NodePosition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L11 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 52 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L13 RegionId.Merkle.Region.NodePosition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L12 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 52 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L14 RegionId.Merkle.Region.NodePosition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L13 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 52 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L15 RegionId.Merkle.Region.NodePosition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L14 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 52 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A5; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L16 RegionId.Merkle.Region.NodePosition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L15 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 52 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A5; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L17 RegionId.Merkle.Region.NodePosition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A5; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L16 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 52 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A5; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L18 RegionId.Merkle.Region.NodePosition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A5; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L17 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 52 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A5; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L19 RegionId.Merkle.Region.NodePosition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A5; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L18 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 52 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A5; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L20 RegionId.Merkle.Region.NodePosition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A5; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L19 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 52 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A5; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L21 RegionId.Merkle.Region.NodePosition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A5; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L20 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 52 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A5; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L22 RegionId.Merkle.Region.NodePosition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A5; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L21 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 52 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A5; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L23 RegionId.Merkle.Region.NodePosition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A5; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L22 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 52 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A5; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L24 RegionId.Merkle.Region.NodePosition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A5; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L23 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 52 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A5; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L25 RegionId.Merkle.Region.NodePosition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A5; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L24 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 52 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A5; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L26 RegionId.Merkle.Region.NodePosition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A5; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L25 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 52 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A5; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L27 RegionId.Merkle.Region.NodePosition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A5; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L26 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 52 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A5; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L28 RegionId.Merkle.Region.NodePosition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A5; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L27 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 52 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A5; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L29 RegionId.Merkle.Region.NodePosition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A5; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L28 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 52 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A5; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L30 RegionId.Merkle.Region.NodePosition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A5; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L29 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 52 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A5; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L31 RegionId.Merkle.Region.NodePosition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A5; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L30 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 52 |}].

  Definition wf_mech_0 : list (Fact.t columns RegionId.t) := [
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L0 RegionId.Merkle.Region.RangeB1; Cell.row_offset := 2 |} 28043396612162516079146097931791602683257960966880886943581093115464031141889;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L0 RegionId.Merkle.Region.RangeB2; Cell.row_offset := 2 |} 28043396612162516079146097931791602683257960966880886943581093115464031141889;
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L0 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L0 RegionId.Merkle.Region.WitnessA; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L0 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 25 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L0 RegionId.Merkle.Region.WitnessB; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L0 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 27 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L0 RegionId.Merkle.Region.WitnessC; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L0 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L0 RegionId.Merkle.Region.WitnessA; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A1; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L0 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L0 RegionId.Merkle.Region.WitnessB; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L0 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L0 RegionId.Merkle.Region.WitnessC; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A3; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L0 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L0 RegionId.Merkle.Region.NodePosition; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A4; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L0 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A3; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L0 RegionId.Merkle.Region.NodePosition; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L0 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L0 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 1 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A1; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L0 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L0 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 26 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L0 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L0 RegionId.Merkle.Region.RangeB1; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A3; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L0 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L0 RegionId.Merkle.Region.RangeB2; Cell.row_offset := 0 |};
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A4; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L0 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} 0;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L1 RegionId.Merkle.Region.RangeB1; Cell.row_offset := 2 |} 28043396612162516079146097931791602683257960966880886943581093115464031141889;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L1 RegionId.Merkle.Region.RangeB2; Cell.row_offset := 2 |} 28043396612162516079146097931791602683257960966880886943581093115464031141889;
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L1 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L1 RegionId.Merkle.Region.WitnessA; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L1 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 25 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L1 RegionId.Merkle.Region.WitnessB; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L1 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 27 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L1 RegionId.Merkle.Region.WitnessC; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L1 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L1 RegionId.Merkle.Region.WitnessA; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A1; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L1 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L1 RegionId.Merkle.Region.WitnessB; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L1 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L1 RegionId.Merkle.Region.WitnessC; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A3; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L1 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L1 RegionId.Merkle.Region.NodePosition; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A4; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L1 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A3; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L1 RegionId.Merkle.Region.NodePosition; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L1 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L1 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 1 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A1; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L1 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L1 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 26 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L1 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L1 RegionId.Merkle.Region.RangeB1; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A3; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L1 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L1 RegionId.Merkle.Region.RangeB2; Cell.row_offset := 0 |};
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A4; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L1 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} 1;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L2 RegionId.Merkle.Region.RangeB1; Cell.row_offset := 2 |} 28043396612162516079146097931791602683257960966880886943581093115464031141889;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L2 RegionId.Merkle.Region.RangeB2; Cell.row_offset := 2 |} 28043396612162516079146097931791602683257960966880886943581093115464031141889;
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L2 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L2 RegionId.Merkle.Region.WitnessA; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L2 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 25 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L2 RegionId.Merkle.Region.WitnessB; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L2 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 27 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L2 RegionId.Merkle.Region.WitnessC; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L2 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L2 RegionId.Merkle.Region.WitnessA; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A1; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L2 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L2 RegionId.Merkle.Region.WitnessB; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L2 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L2 RegionId.Merkle.Region.WitnessC; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A3; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L2 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L2 RegionId.Merkle.Region.NodePosition; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A4; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L2 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A3; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L2 RegionId.Merkle.Region.NodePosition; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L2 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L2 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 1 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A1; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L2 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L2 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 26 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L2 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L2 RegionId.Merkle.Region.RangeB1; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A3; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L2 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L2 RegionId.Merkle.Region.RangeB2; Cell.row_offset := 0 |};
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A4; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L2 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} 2;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L3 RegionId.Merkle.Region.RangeB1; Cell.row_offset := 2 |} 28043396612162516079146097931791602683257960966880886943581093115464031141889].

  Definition wf_mech_1 : list (Fact.t columns RegionId.t) := [
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L3 RegionId.Merkle.Region.RangeB2; Cell.row_offset := 2 |} 28043396612162516079146097931791602683257960966880886943581093115464031141889;
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L3 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L3 RegionId.Merkle.Region.WitnessA; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L3 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 25 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L3 RegionId.Merkle.Region.WitnessB; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L3 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 27 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L3 RegionId.Merkle.Region.WitnessC; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L3 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L3 RegionId.Merkle.Region.WitnessA; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A1; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L3 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L3 RegionId.Merkle.Region.WitnessB; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L3 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L3 RegionId.Merkle.Region.WitnessC; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A3; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L3 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L3 RegionId.Merkle.Region.NodePosition; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A4; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L3 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A3; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L3 RegionId.Merkle.Region.NodePosition; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L3 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L3 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 1 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A1; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L3 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L3 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 26 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L3 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L3 RegionId.Merkle.Region.RangeB1; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A3; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L3 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L3 RegionId.Merkle.Region.RangeB2; Cell.row_offset := 0 |};
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A4; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L3 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} 3;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L4 RegionId.Merkle.Region.RangeB1; Cell.row_offset := 2 |} 28043396612162516079146097931791602683257960966880886943581093115464031141889;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L4 RegionId.Merkle.Region.RangeB2; Cell.row_offset := 2 |} 28043396612162516079146097931791602683257960966880886943581093115464031141889;
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L4 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L4 RegionId.Merkle.Region.WitnessA; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L4 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 25 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L4 RegionId.Merkle.Region.WitnessB; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L4 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 27 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L4 RegionId.Merkle.Region.WitnessC; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L4 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L4 RegionId.Merkle.Region.WitnessA; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A1; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L4 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L4 RegionId.Merkle.Region.WitnessB; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L4 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L4 RegionId.Merkle.Region.WitnessC; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A3; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L4 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L4 RegionId.Merkle.Region.NodePosition; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A4; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L4 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A3; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L4 RegionId.Merkle.Region.NodePosition; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L4 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L4 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 1 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A1; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L4 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L4 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 26 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L4 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L4 RegionId.Merkle.Region.RangeB1; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A3; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L4 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L4 RegionId.Merkle.Region.RangeB2; Cell.row_offset := 0 |};
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A4; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L4 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} 4;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L5 RegionId.Merkle.Region.RangeB1; Cell.row_offset := 2 |} 28043396612162516079146097931791602683257960966880886943581093115464031141889;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L5 RegionId.Merkle.Region.RangeB2; Cell.row_offset := 2 |} 28043396612162516079146097931791602683257960966880886943581093115464031141889;
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L5 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L5 RegionId.Merkle.Region.WitnessA; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L5 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 25 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L5 RegionId.Merkle.Region.WitnessB; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L5 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 27 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L5 RegionId.Merkle.Region.WitnessC; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L5 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L5 RegionId.Merkle.Region.WitnessA; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A1; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L5 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L5 RegionId.Merkle.Region.WitnessB; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L5 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L5 RegionId.Merkle.Region.WitnessC; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A3; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L5 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L5 RegionId.Merkle.Region.NodePosition; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A4; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L5 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A3; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L5 RegionId.Merkle.Region.NodePosition; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L5 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L5 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 1 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A1; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L5 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L5 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 26 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L5 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L5 RegionId.Merkle.Region.RangeB1; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A3; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L5 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L5 RegionId.Merkle.Region.RangeB2; Cell.row_offset := 0 |};
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A4; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L5 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} 5;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L6 RegionId.Merkle.Region.RangeB1; Cell.row_offset := 2 |} 28043396612162516079146097931791602683257960966880886943581093115464031141889;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L6 RegionId.Merkle.Region.RangeB2; Cell.row_offset := 2 |} 28043396612162516079146097931791602683257960966880886943581093115464031141889].

  Definition wf_mech_2 : list (Fact.t columns RegionId.t) := [
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L6 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L6 RegionId.Merkle.Region.WitnessA; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L6 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 25 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L6 RegionId.Merkle.Region.WitnessB; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L6 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 27 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L6 RegionId.Merkle.Region.WitnessC; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L6 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L6 RegionId.Merkle.Region.WitnessA; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A1; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L6 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L6 RegionId.Merkle.Region.WitnessB; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L6 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L6 RegionId.Merkle.Region.WitnessC; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A3; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L6 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L6 RegionId.Merkle.Region.NodePosition; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A4; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L6 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A3; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L6 RegionId.Merkle.Region.NodePosition; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L6 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L6 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 1 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A1; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L6 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L6 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 26 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L6 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L6 RegionId.Merkle.Region.RangeB1; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A3; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L6 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L6 RegionId.Merkle.Region.RangeB2; Cell.row_offset := 0 |};
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A4; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L6 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} 6;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L7 RegionId.Merkle.Region.RangeB1; Cell.row_offset := 2 |} 28043396612162516079146097931791602683257960966880886943581093115464031141889;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L7 RegionId.Merkle.Region.RangeB2; Cell.row_offset := 2 |} 28043396612162516079146097931791602683257960966880886943581093115464031141889;
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L7 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L7 RegionId.Merkle.Region.WitnessA; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L7 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 25 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L7 RegionId.Merkle.Region.WitnessB; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L7 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 27 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L7 RegionId.Merkle.Region.WitnessC; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L7 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L7 RegionId.Merkle.Region.WitnessA; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A1; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L7 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L7 RegionId.Merkle.Region.WitnessB; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L7 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L7 RegionId.Merkle.Region.WitnessC; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A3; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L7 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L7 RegionId.Merkle.Region.NodePosition; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A4; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L7 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A3; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L7 RegionId.Merkle.Region.NodePosition; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L7 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L7 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 1 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A1; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L7 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L7 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 26 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L7 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L7 RegionId.Merkle.Region.RangeB1; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A3; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L7 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L7 RegionId.Merkle.Region.RangeB2; Cell.row_offset := 0 |};
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A4; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L7 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} 7;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L8 RegionId.Merkle.Region.RangeB1; Cell.row_offset := 2 |} 28043396612162516079146097931791602683257960966880886943581093115464031141889;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L8 RegionId.Merkle.Region.RangeB2; Cell.row_offset := 2 |} 28043396612162516079146097931791602683257960966880886943581093115464031141889;
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L8 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L8 RegionId.Merkle.Region.WitnessA; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L8 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 25 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L8 RegionId.Merkle.Region.WitnessB; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L8 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 27 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L8 RegionId.Merkle.Region.WitnessC; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L8 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L8 RegionId.Merkle.Region.WitnessA; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A1; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L8 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L8 RegionId.Merkle.Region.WitnessB; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L8 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L8 RegionId.Merkle.Region.WitnessC; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A3; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L8 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L8 RegionId.Merkle.Region.NodePosition; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A4; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L8 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A3; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L8 RegionId.Merkle.Region.NodePosition; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L8 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L8 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 1 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A1; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L8 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L8 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 26 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L8 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L8 RegionId.Merkle.Region.RangeB1; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A3; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L8 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L8 RegionId.Merkle.Region.RangeB2; Cell.row_offset := 0 |};
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A4; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L8 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} 8;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L9 RegionId.Merkle.Region.RangeB1; Cell.row_offset := 2 |} 28043396612162516079146097931791602683257960966880886943581093115464031141889;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L9 RegionId.Merkle.Region.RangeB2; Cell.row_offset := 2 |} 28043396612162516079146097931791602683257960966880886943581093115464031141889;
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L9 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L9 RegionId.Merkle.Region.WitnessA; Cell.row_offset := 0 |}].

  Definition wf_mech_3 : list (Fact.t columns RegionId.t) := [
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L9 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 25 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L9 RegionId.Merkle.Region.WitnessB; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L9 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 27 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L9 RegionId.Merkle.Region.WitnessC; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L9 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L9 RegionId.Merkle.Region.WitnessA; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A1; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L9 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L9 RegionId.Merkle.Region.WitnessB; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L9 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L9 RegionId.Merkle.Region.WitnessC; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A3; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L9 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L9 RegionId.Merkle.Region.NodePosition; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A4; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L9 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A3; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L9 RegionId.Merkle.Region.NodePosition; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L9 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L9 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 1 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A1; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L9 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L9 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 26 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L9 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L9 RegionId.Merkle.Region.RangeB1; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A3; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L9 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L9 RegionId.Merkle.Region.RangeB2; Cell.row_offset := 0 |};
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A4; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L9 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} 9;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L10 RegionId.Merkle.Region.RangeB1; Cell.row_offset := 2 |} 28043396612162516079146097931791602683257960966880886943581093115464031141889;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L10 RegionId.Merkle.Region.RangeB2; Cell.row_offset := 2 |} 28043396612162516079146097931791602683257960966880886943581093115464031141889;
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L10 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L10 RegionId.Merkle.Region.WitnessA; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L10 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 25 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L10 RegionId.Merkle.Region.WitnessB; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L10 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 27 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L10 RegionId.Merkle.Region.WitnessC; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L10 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L10 RegionId.Merkle.Region.WitnessA; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A1; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L10 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L10 RegionId.Merkle.Region.WitnessB; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L10 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L10 RegionId.Merkle.Region.WitnessC; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A3; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L10 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L10 RegionId.Merkle.Region.NodePosition; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A4; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L10 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A3; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L10 RegionId.Merkle.Region.NodePosition; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L10 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L10 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 1 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A1; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L10 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L10 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 26 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L10 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L10 RegionId.Merkle.Region.RangeB1; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A3; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L10 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L10 RegionId.Merkle.Region.RangeB2; Cell.row_offset := 0 |};
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A4; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L10 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} 10;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L11 RegionId.Merkle.Region.RangeB1; Cell.row_offset := 2 |} 28043396612162516079146097931791602683257960966880886943581093115464031141889;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L11 RegionId.Merkle.Region.RangeB2; Cell.row_offset := 2 |} 28043396612162516079146097931791602683257960966880886943581093115464031141889;
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L11 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L11 RegionId.Merkle.Region.WitnessA; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L11 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 25 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L11 RegionId.Merkle.Region.WitnessB; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L11 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 27 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L11 RegionId.Merkle.Region.WitnessC; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L11 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L11 RegionId.Merkle.Region.WitnessA; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A1; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L11 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L11 RegionId.Merkle.Region.WitnessB; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L11 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L11 RegionId.Merkle.Region.WitnessC; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A3; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L11 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L11 RegionId.Merkle.Region.NodePosition; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A4; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L11 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A3; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L11 RegionId.Merkle.Region.NodePosition; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L11 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L11 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 1 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A1; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L11 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L11 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 26 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L11 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L11 RegionId.Merkle.Region.RangeB1; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A3; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L11 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L11 RegionId.Merkle.Region.RangeB2; Cell.row_offset := 0 |};
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A4; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L11 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} 11;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L12 RegionId.Merkle.Region.RangeB1; Cell.row_offset := 2 |} 28043396612162516079146097931791602683257960966880886943581093115464031141889;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L12 RegionId.Merkle.Region.RangeB2; Cell.row_offset := 2 |} 28043396612162516079146097931791602683257960966880886943581093115464031141889;
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L12 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L12 RegionId.Merkle.Region.WitnessA; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L12 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 25 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L12 RegionId.Merkle.Region.WitnessB; Cell.row_offset := 0 |}].

  Definition wf_mech_4 : list (Fact.t columns RegionId.t) := [
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L12 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 27 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L12 RegionId.Merkle.Region.WitnessC; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L12 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L12 RegionId.Merkle.Region.WitnessA; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A1; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L12 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L12 RegionId.Merkle.Region.WitnessB; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L12 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L12 RegionId.Merkle.Region.WitnessC; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A3; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L12 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L12 RegionId.Merkle.Region.NodePosition; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A4; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L12 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A3; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L12 RegionId.Merkle.Region.NodePosition; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L12 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L12 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 1 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A1; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L12 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L12 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 26 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L12 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L12 RegionId.Merkle.Region.RangeB1; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A3; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L12 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L12 RegionId.Merkle.Region.RangeB2; Cell.row_offset := 0 |};
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A4; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L12 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} 12;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L13 RegionId.Merkle.Region.RangeB1; Cell.row_offset := 2 |} 28043396612162516079146097931791602683257960966880886943581093115464031141889;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L13 RegionId.Merkle.Region.RangeB2; Cell.row_offset := 2 |} 28043396612162516079146097931791602683257960966880886943581093115464031141889;
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L13 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L13 RegionId.Merkle.Region.WitnessA; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L13 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 25 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L13 RegionId.Merkle.Region.WitnessB; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L13 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 27 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L13 RegionId.Merkle.Region.WitnessC; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L13 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L13 RegionId.Merkle.Region.WitnessA; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A1; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L13 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L13 RegionId.Merkle.Region.WitnessB; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L13 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L13 RegionId.Merkle.Region.WitnessC; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A3; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L13 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L13 RegionId.Merkle.Region.NodePosition; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A4; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L13 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A3; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L13 RegionId.Merkle.Region.NodePosition; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L13 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L13 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 1 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A1; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L13 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L13 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 26 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L13 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L13 RegionId.Merkle.Region.RangeB1; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A3; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L13 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L13 RegionId.Merkle.Region.RangeB2; Cell.row_offset := 0 |};
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A4; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L13 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} 13;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L14 RegionId.Merkle.Region.RangeB1; Cell.row_offset := 2 |} 28043396612162516079146097931791602683257960966880886943581093115464031141889;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L14 RegionId.Merkle.Region.RangeB2; Cell.row_offset := 2 |} 28043396612162516079146097931791602683257960966880886943581093115464031141889;
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L14 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L14 RegionId.Merkle.Region.WitnessA; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L14 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 25 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L14 RegionId.Merkle.Region.WitnessB; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L14 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 27 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L14 RegionId.Merkle.Region.WitnessC; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L14 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L14 RegionId.Merkle.Region.WitnessA; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A1; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L14 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L14 RegionId.Merkle.Region.WitnessB; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L14 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L14 RegionId.Merkle.Region.WitnessC; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A3; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L14 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L14 RegionId.Merkle.Region.NodePosition; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A4; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L14 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A3; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L14 RegionId.Merkle.Region.NodePosition; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L14 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L14 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 1 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A1; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L14 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L14 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 26 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L14 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L14 RegionId.Merkle.Region.RangeB1; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A3; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L14 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L14 RegionId.Merkle.Region.RangeB2; Cell.row_offset := 0 |};
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A4; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L14 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} 14;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L15 RegionId.Merkle.Region.RangeB1; Cell.row_offset := 2 |} 28043396612162516079146097931791602683257960966880886943581093115464031141889;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L15 RegionId.Merkle.Region.RangeB2; Cell.row_offset := 2 |} 28043396612162516079146097931791602683257960966880886943581093115464031141889;
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L15 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L15 RegionId.Merkle.Region.WitnessA; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L15 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 25 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L15 RegionId.Merkle.Region.WitnessB; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L15 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 27 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L15 RegionId.Merkle.Region.WitnessC; Cell.row_offset := 0 |}].

  Definition wf_mech_5 : list (Fact.t columns RegionId.t) := [
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L15 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L15 RegionId.Merkle.Region.WitnessA; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A1; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L15 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L15 RegionId.Merkle.Region.WitnessB; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L15 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L15 RegionId.Merkle.Region.WitnessC; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A3; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L15 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L15 RegionId.Merkle.Region.NodePosition; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A4; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L15 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A3; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L15 RegionId.Merkle.Region.NodePosition; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L15 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L15 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 1 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A1; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L15 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L15 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 26 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L15 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L15 RegionId.Merkle.Region.RangeB1; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A3; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L15 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L15 RegionId.Merkle.Region.RangeB2; Cell.row_offset := 0 |};
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A4; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L15 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} 15;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L16 RegionId.Merkle.Region.RangeB1; Cell.row_offset := 2 |} 28043396612162516079146097931791602683257960966880886943581093115464031141889;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L16 RegionId.Merkle.Region.RangeB2; Cell.row_offset := 2 |} 28043396612162516079146097931791602683257960966880886943581093115464031141889;
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L16 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L16 RegionId.Merkle.Region.WitnessA; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L16 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 25 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L16 RegionId.Merkle.Region.WitnessB; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L16 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 27 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L16 RegionId.Merkle.Region.WitnessC; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A5; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L16 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L16 RegionId.Merkle.Region.WitnessA; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L16 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L16 RegionId.Merkle.Region.WitnessB; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L16 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L16 RegionId.Merkle.Region.WitnessC; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A8; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L16 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L16 RegionId.Merkle.Region.NodePosition; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L16 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A8; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L16 RegionId.Merkle.Region.NodePosition; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A5; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L16 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L16 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 1 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L16 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L16 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 26 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L16 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L16 RegionId.Merkle.Region.RangeB1; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A8; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L16 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L16 RegionId.Merkle.Region.RangeB2; Cell.row_offset := 0 |};
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L16 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} 16;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L17 RegionId.Merkle.Region.RangeB1; Cell.row_offset := 2 |} 28043396612162516079146097931791602683257960966880886943581093115464031141889;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L17 RegionId.Merkle.Region.RangeB2; Cell.row_offset := 2 |} 28043396612162516079146097931791602683257960966880886943581093115464031141889;
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L17 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L17 RegionId.Merkle.Region.WitnessA; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L17 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 25 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L17 RegionId.Merkle.Region.WitnessB; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L17 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 27 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L17 RegionId.Merkle.Region.WitnessC; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A5; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L17 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L17 RegionId.Merkle.Region.WitnessA; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L17 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L17 RegionId.Merkle.Region.WitnessB; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L17 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L17 RegionId.Merkle.Region.WitnessC; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A8; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L17 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L17 RegionId.Merkle.Region.NodePosition; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L17 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A8; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L17 RegionId.Merkle.Region.NodePosition; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A5; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L17 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L17 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 1 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L17 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L17 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 26 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L17 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L17 RegionId.Merkle.Region.RangeB1; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A8; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L17 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L17 RegionId.Merkle.Region.RangeB2; Cell.row_offset := 0 |};
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L17 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} 17;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L18 RegionId.Merkle.Region.RangeB1; Cell.row_offset := 2 |} 28043396612162516079146097931791602683257960966880886943581093115464031141889;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L18 RegionId.Merkle.Region.RangeB2; Cell.row_offset := 2 |} 28043396612162516079146097931791602683257960966880886943581093115464031141889;
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L18 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L18 RegionId.Merkle.Region.WitnessA; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L18 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 25 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L18 RegionId.Merkle.Region.WitnessB; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L18 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 27 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L18 RegionId.Merkle.Region.WitnessC; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A5; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L18 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L18 RegionId.Merkle.Region.WitnessA; Cell.row_offset := 0 |}].

  Definition wf_mech_6 : list (Fact.t columns RegionId.t) := [
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L18 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L18 RegionId.Merkle.Region.WitnessB; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L18 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L18 RegionId.Merkle.Region.WitnessC; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A8; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L18 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L18 RegionId.Merkle.Region.NodePosition; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L18 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A8; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L18 RegionId.Merkle.Region.NodePosition; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A5; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L18 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L18 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 1 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L18 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L18 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 26 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L18 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L18 RegionId.Merkle.Region.RangeB1; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A8; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L18 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L18 RegionId.Merkle.Region.RangeB2; Cell.row_offset := 0 |};
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L18 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} 18;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L19 RegionId.Merkle.Region.RangeB1; Cell.row_offset := 2 |} 28043396612162516079146097931791602683257960966880886943581093115464031141889;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L19 RegionId.Merkle.Region.RangeB2; Cell.row_offset := 2 |} 28043396612162516079146097931791602683257960966880886943581093115464031141889;
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L19 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L19 RegionId.Merkle.Region.WitnessA; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L19 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 25 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L19 RegionId.Merkle.Region.WitnessB; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L19 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 27 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L19 RegionId.Merkle.Region.WitnessC; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A5; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L19 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L19 RegionId.Merkle.Region.WitnessA; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L19 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L19 RegionId.Merkle.Region.WitnessB; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L19 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L19 RegionId.Merkle.Region.WitnessC; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A8; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L19 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L19 RegionId.Merkle.Region.NodePosition; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L19 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A8; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L19 RegionId.Merkle.Region.NodePosition; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A5; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L19 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L19 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 1 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L19 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L19 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 26 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L19 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L19 RegionId.Merkle.Region.RangeB1; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A8; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L19 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L19 RegionId.Merkle.Region.RangeB2; Cell.row_offset := 0 |};
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L19 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} 19;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L20 RegionId.Merkle.Region.RangeB1; Cell.row_offset := 2 |} 28043396612162516079146097931791602683257960966880886943581093115464031141889;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L20 RegionId.Merkle.Region.RangeB2; Cell.row_offset := 2 |} 28043396612162516079146097931791602683257960966880886943581093115464031141889;
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L20 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L20 RegionId.Merkle.Region.WitnessA; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L20 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 25 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L20 RegionId.Merkle.Region.WitnessB; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L20 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 27 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L20 RegionId.Merkle.Region.WitnessC; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A5; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L20 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L20 RegionId.Merkle.Region.WitnessA; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L20 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L20 RegionId.Merkle.Region.WitnessB; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L20 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L20 RegionId.Merkle.Region.WitnessC; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A8; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L20 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L20 RegionId.Merkle.Region.NodePosition; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L20 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A8; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L20 RegionId.Merkle.Region.NodePosition; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A5; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L20 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L20 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 1 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L20 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L20 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 26 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L20 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L20 RegionId.Merkle.Region.RangeB1; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A8; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L20 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L20 RegionId.Merkle.Region.RangeB2; Cell.row_offset := 0 |};
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L20 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} 20;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L21 RegionId.Merkle.Region.RangeB1; Cell.row_offset := 2 |} 28043396612162516079146097931791602683257960966880886943581093115464031141889;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L21 RegionId.Merkle.Region.RangeB2; Cell.row_offset := 2 |} 28043396612162516079146097931791602683257960966880886943581093115464031141889;
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L21 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L21 RegionId.Merkle.Region.WitnessA; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L21 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 25 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L21 RegionId.Merkle.Region.WitnessB; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L21 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 27 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L21 RegionId.Merkle.Region.WitnessC; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A5; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L21 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L21 RegionId.Merkle.Region.WitnessA; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L21 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L21 RegionId.Merkle.Region.WitnessB; Cell.row_offset := 0 |}].

  Definition wf_mech_7 : list (Fact.t columns RegionId.t) := [
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L21 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L21 RegionId.Merkle.Region.WitnessC; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A8; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L21 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L21 RegionId.Merkle.Region.NodePosition; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L21 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A8; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L21 RegionId.Merkle.Region.NodePosition; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A5; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L21 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L21 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 1 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L21 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L21 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 26 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L21 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L21 RegionId.Merkle.Region.RangeB1; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A8; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L21 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L21 RegionId.Merkle.Region.RangeB2; Cell.row_offset := 0 |};
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L21 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} 21;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L22 RegionId.Merkle.Region.RangeB1; Cell.row_offset := 2 |} 28043396612162516079146097931791602683257960966880886943581093115464031141889;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L22 RegionId.Merkle.Region.RangeB2; Cell.row_offset := 2 |} 28043396612162516079146097931791602683257960966880886943581093115464031141889;
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L22 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L22 RegionId.Merkle.Region.WitnessA; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L22 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 25 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L22 RegionId.Merkle.Region.WitnessB; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L22 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 27 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L22 RegionId.Merkle.Region.WitnessC; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A5; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L22 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L22 RegionId.Merkle.Region.WitnessA; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L22 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L22 RegionId.Merkle.Region.WitnessB; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L22 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L22 RegionId.Merkle.Region.WitnessC; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A8; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L22 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L22 RegionId.Merkle.Region.NodePosition; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L22 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A8; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L22 RegionId.Merkle.Region.NodePosition; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A5; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L22 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L22 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 1 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L22 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L22 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 26 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L22 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L22 RegionId.Merkle.Region.RangeB1; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A8; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L22 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L22 RegionId.Merkle.Region.RangeB2; Cell.row_offset := 0 |};
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L22 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} 22;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L23 RegionId.Merkle.Region.RangeB1; Cell.row_offset := 2 |} 28043396612162516079146097931791602683257960966880886943581093115464031141889;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L23 RegionId.Merkle.Region.RangeB2; Cell.row_offset := 2 |} 28043396612162516079146097931791602683257960966880886943581093115464031141889;
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L23 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L23 RegionId.Merkle.Region.WitnessA; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L23 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 25 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L23 RegionId.Merkle.Region.WitnessB; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L23 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 27 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L23 RegionId.Merkle.Region.WitnessC; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A5; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L23 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L23 RegionId.Merkle.Region.WitnessA; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L23 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L23 RegionId.Merkle.Region.WitnessB; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L23 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L23 RegionId.Merkle.Region.WitnessC; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A8; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L23 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L23 RegionId.Merkle.Region.NodePosition; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L23 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A8; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L23 RegionId.Merkle.Region.NodePosition; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A5; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L23 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L23 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 1 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L23 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L23 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 26 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L23 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L23 RegionId.Merkle.Region.RangeB1; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A8; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L23 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L23 RegionId.Merkle.Region.RangeB2; Cell.row_offset := 0 |};
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L23 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} 23;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L24 RegionId.Merkle.Region.RangeB1; Cell.row_offset := 2 |} 28043396612162516079146097931791602683257960966880886943581093115464031141889;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L24 RegionId.Merkle.Region.RangeB2; Cell.row_offset := 2 |} 28043396612162516079146097931791602683257960966880886943581093115464031141889;
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L24 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L24 RegionId.Merkle.Region.WitnessA; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L24 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 25 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L24 RegionId.Merkle.Region.WitnessB; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L24 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 27 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L24 RegionId.Merkle.Region.WitnessC; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A5; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L24 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L24 RegionId.Merkle.Region.WitnessA; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L24 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L24 RegionId.Merkle.Region.WitnessB; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L24 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L24 RegionId.Merkle.Region.WitnessC; Cell.row_offset := 0 |}].

  Definition wf_mech_8 : list (Fact.t columns RegionId.t) := [
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A8; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L24 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L24 RegionId.Merkle.Region.NodePosition; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L24 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A8; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L24 RegionId.Merkle.Region.NodePosition; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A5; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L24 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L24 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 1 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L24 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L24 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 26 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L24 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L24 RegionId.Merkle.Region.RangeB1; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A8; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L24 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L24 RegionId.Merkle.Region.RangeB2; Cell.row_offset := 0 |};
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L24 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} 24;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L25 RegionId.Merkle.Region.RangeB1; Cell.row_offset := 2 |} 28043396612162516079146097931791602683257960966880886943581093115464031141889;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L25 RegionId.Merkle.Region.RangeB2; Cell.row_offset := 2 |} 28043396612162516079146097931791602683257960966880886943581093115464031141889;
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L25 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L25 RegionId.Merkle.Region.WitnessA; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L25 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 25 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L25 RegionId.Merkle.Region.WitnessB; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L25 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 27 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L25 RegionId.Merkle.Region.WitnessC; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A5; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L25 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L25 RegionId.Merkle.Region.WitnessA; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L25 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L25 RegionId.Merkle.Region.WitnessB; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L25 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L25 RegionId.Merkle.Region.WitnessC; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A8; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L25 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L25 RegionId.Merkle.Region.NodePosition; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L25 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A8; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L25 RegionId.Merkle.Region.NodePosition; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A5; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L25 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L25 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 1 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L25 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L25 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 26 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L25 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L25 RegionId.Merkle.Region.RangeB1; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A8; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L25 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L25 RegionId.Merkle.Region.RangeB2; Cell.row_offset := 0 |};
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L25 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} 25;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L26 RegionId.Merkle.Region.RangeB1; Cell.row_offset := 2 |} 28043396612162516079146097931791602683257960966880886943581093115464031141889;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L26 RegionId.Merkle.Region.RangeB2; Cell.row_offset := 2 |} 28043396612162516079146097931791602683257960966880886943581093115464031141889;
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L26 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L26 RegionId.Merkle.Region.WitnessA; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L26 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 25 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L26 RegionId.Merkle.Region.WitnessB; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L26 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 27 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L26 RegionId.Merkle.Region.WitnessC; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A5; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L26 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L26 RegionId.Merkle.Region.WitnessA; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L26 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L26 RegionId.Merkle.Region.WitnessB; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L26 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L26 RegionId.Merkle.Region.WitnessC; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A8; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L26 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L26 RegionId.Merkle.Region.NodePosition; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L26 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A8; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L26 RegionId.Merkle.Region.NodePosition; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A5; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L26 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L26 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 1 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L26 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L26 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 26 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L26 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L26 RegionId.Merkle.Region.RangeB1; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A8; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L26 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L26 RegionId.Merkle.Region.RangeB2; Cell.row_offset := 0 |};
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L26 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} 26;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L27 RegionId.Merkle.Region.RangeB1; Cell.row_offset := 2 |} 28043396612162516079146097931791602683257960966880886943581093115464031141889;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L27 RegionId.Merkle.Region.RangeB2; Cell.row_offset := 2 |} 28043396612162516079146097931791602683257960966880886943581093115464031141889;
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L27 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L27 RegionId.Merkle.Region.WitnessA; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L27 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 25 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L27 RegionId.Merkle.Region.WitnessB; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L27 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 27 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L27 RegionId.Merkle.Region.WitnessC; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A5; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L27 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L27 RegionId.Merkle.Region.WitnessA; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L27 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L27 RegionId.Merkle.Region.WitnessB; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L27 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L27 RegionId.Merkle.Region.WitnessC; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A8; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L27 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L27 RegionId.Merkle.Region.NodePosition; Cell.row_offset := 0 |}].

  Definition wf_mech_9 : list (Fact.t columns RegionId.t) := [
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L27 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A8; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L27 RegionId.Merkle.Region.NodePosition; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A5; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L27 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L27 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 1 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L27 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L27 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 26 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L27 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L27 RegionId.Merkle.Region.RangeB1; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A8; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L27 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L27 RegionId.Merkle.Region.RangeB2; Cell.row_offset := 0 |};
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L27 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} 27;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L28 RegionId.Merkle.Region.RangeB1; Cell.row_offset := 2 |} 28043396612162516079146097931791602683257960966880886943581093115464031141889;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L28 RegionId.Merkle.Region.RangeB2; Cell.row_offset := 2 |} 28043396612162516079146097931791602683257960966880886943581093115464031141889;
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L28 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L28 RegionId.Merkle.Region.WitnessA; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L28 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 25 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L28 RegionId.Merkle.Region.WitnessB; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L28 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 27 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L28 RegionId.Merkle.Region.WitnessC; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A5; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L28 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L28 RegionId.Merkle.Region.WitnessA; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L28 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L28 RegionId.Merkle.Region.WitnessB; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L28 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L28 RegionId.Merkle.Region.WitnessC; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A8; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L28 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L28 RegionId.Merkle.Region.NodePosition; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L28 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A8; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L28 RegionId.Merkle.Region.NodePosition; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A5; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L28 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L28 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 1 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L28 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L28 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 26 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L28 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L28 RegionId.Merkle.Region.RangeB1; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A8; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L28 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L28 RegionId.Merkle.Region.RangeB2; Cell.row_offset := 0 |};
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L28 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} 28;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L29 RegionId.Merkle.Region.RangeB1; Cell.row_offset := 2 |} 28043396612162516079146097931791602683257960966880886943581093115464031141889;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L29 RegionId.Merkle.Region.RangeB2; Cell.row_offset := 2 |} 28043396612162516079146097931791602683257960966880886943581093115464031141889;
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L29 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L29 RegionId.Merkle.Region.WitnessA; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L29 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 25 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L29 RegionId.Merkle.Region.WitnessB; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L29 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 27 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L29 RegionId.Merkle.Region.WitnessC; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A5; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L29 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L29 RegionId.Merkle.Region.WitnessA; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L29 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L29 RegionId.Merkle.Region.WitnessB; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L29 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L29 RegionId.Merkle.Region.WitnessC; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A8; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L29 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L29 RegionId.Merkle.Region.NodePosition; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L29 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A8; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L29 RegionId.Merkle.Region.NodePosition; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A5; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L29 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L29 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 1 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L29 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L29 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 26 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L29 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L29 RegionId.Merkle.Region.RangeB1; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A8; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L29 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L29 RegionId.Merkle.Region.RangeB2; Cell.row_offset := 0 |};
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L29 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} 29;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L30 RegionId.Merkle.Region.RangeB1; Cell.row_offset := 2 |} 28043396612162516079146097931791602683257960966880886943581093115464031141889;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L30 RegionId.Merkle.Region.RangeB2; Cell.row_offset := 2 |} 28043396612162516079146097931791602683257960966880886943581093115464031141889;
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L30 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L30 RegionId.Merkle.Region.WitnessA; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L30 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 25 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L30 RegionId.Merkle.Region.WitnessB; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L30 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 27 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L30 RegionId.Merkle.Region.WitnessC; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A5; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L30 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L30 RegionId.Merkle.Region.WitnessA; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L30 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L30 RegionId.Merkle.Region.WitnessB; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L30 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L30 RegionId.Merkle.Region.WitnessC; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A8; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L30 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L30 RegionId.Merkle.Region.NodePosition; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L30 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A8; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L30 RegionId.Merkle.Region.NodePosition; Cell.row_offset := 0 |}].

  Definition wf_mech_10 : list (Fact.t columns RegionId.t) := [
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A5; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L30 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L30 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 1 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L30 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L30 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 26 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L30 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L30 RegionId.Merkle.Region.RangeB1; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A8; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L30 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L30 RegionId.Merkle.Region.RangeB2; Cell.row_offset := 0 |};
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L30 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} 30;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L31 RegionId.Merkle.Region.RangeB1; Cell.row_offset := 2 |} 28043396612162516079146097931791602683257960966880886943581093115464031141889;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L31 RegionId.Merkle.Region.RangeB2; Cell.row_offset := 2 |} 28043396612162516079146097931791602683257960966880886943581093115464031141889;
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L31 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L31 RegionId.Merkle.Region.WitnessA; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L31 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 25 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L31 RegionId.Merkle.Region.WitnessB; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L31 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 27 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L31 RegionId.Merkle.Region.WitnessC; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A5; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L31 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L31 RegionId.Merkle.Region.WitnessA; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L31 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L31 RegionId.Merkle.Region.WitnessB; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L31 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L31 RegionId.Merkle.Region.WitnessC; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A8; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L31 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L31 RegionId.Merkle.Region.NodePosition; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L31 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A8; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L31 RegionId.Merkle.Region.NodePosition; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A5; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L31 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L31 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 1 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L31 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L31 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 26 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L31 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L31 RegionId.Merkle.Region.RangeB1; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A8; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L31 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L31 RegionId.Merkle.Region.RangeB2; Cell.row_offset := 0 |};
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L31 RegionId.Merkle.Region.Decomposition; Cell.row_offset := 1 |} 31;
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.ValueCommitment RegionId.ValueCommitment.ValueCommitVIncomplete; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.ValueCommitment RegionId.ValueCommitment.ValueCommitVIncomplete; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A3; Cell.region := RegionId.ValueCommitment RegionId.ValueCommitment.ValueCommitVIncomplete; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A1; Cell.region := RegionId.ValueCommitment RegionId.ValueCommitment.ValueCommitVIncomplete; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.ValueCommitment RegionId.ValueCommitment.ValueCommitVMsb; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.ValueCommitment RegionId.ValueCommitment.ValueCommitVIncomplete; Cell.row_offset := 21 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A1; Cell.region := RegionId.ValueCommitment RegionId.ValueCommitment.ValueCommitVMsb; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A1; Cell.region := RegionId.ValueCommitment RegionId.ValueCommitment.ValueCommitVIncomplete; Cell.row_offset := 21 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.ValueCommitment RegionId.ValueCommitment.ValueCommitVMsb; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.ValueCommitment RegionId.ValueCommitment.ValueCommitVIncomplete; Cell.row_offset := 21 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A3; Cell.region := RegionId.ValueCommitment RegionId.ValueCommitment.ValueCommitVMsb; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A3; Cell.region := RegionId.ValueCommitment RegionId.ValueCommitment.ValueCommitVIncomplete; Cell.row_offset := 21 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A4; Cell.region := RegionId.ValueCommitment RegionId.ValueCommitment.ValueCommitVMsb; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.ValueCommitment RegionId.ValueCommitment.SignRangeCheck; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A5; Cell.region := RegionId.ValueCommitment RegionId.ValueCommitment.ValueCommitVMsb; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A4; Cell.region := RegionId.ValueCommitment RegionId.ValueCommitment.ValueCommitVIncomplete; Cell.row_offset := 21 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.ValueCommitment RegionId.ValueCommitment.ValueCommitRIncomplete; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.ValueCommitment RegionId.ValueCommitment.ValueCommitRIncomplete; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A3; Cell.region := RegionId.ValueCommitment RegionId.ValueCommitment.ValueCommitRIncomplete; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A1; Cell.region := RegionId.ValueCommitment RegionId.ValueCommitment.ValueCommitRIncomplete; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.ValueCommitment RegionId.ValueCommitment.ValueCommitRLast; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.ValueCommitment RegionId.ValueCommitment.ValueCommitRIncomplete; Cell.row_offset := 84 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A1; Cell.region := RegionId.ValueCommitment RegionId.ValueCommitment.ValueCommitRLast; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A1; Cell.region := RegionId.ValueCommitment RegionId.ValueCommitment.ValueCommitRIncomplete; Cell.row_offset := 84 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.ValueCommitment RegionId.ValueCommitment.ValueCommitRLast; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.ValueCommitment RegionId.ValueCommitment.ValueCommitRIncomplete; Cell.row_offset := 84 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A3; Cell.region := RegionId.ValueCommitment RegionId.ValueCommitment.ValueCommitRLast; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A3; Cell.region := RegionId.ValueCommitment RegionId.ValueCommitment.ValueCommitRIncomplete; Cell.row_offset := 84 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.ValueCommitment RegionId.ValueCommitment.CompletePointAdd; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.ValueCommitment RegionId.ValueCommitment.ValueCommitVMsb; Cell.row_offset := 1 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A1; Cell.region := RegionId.ValueCommitment RegionId.ValueCommitment.CompletePointAdd; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A1; Cell.region := RegionId.ValueCommitment RegionId.ValueCommitment.ValueCommitVMsb; Cell.row_offset := 1 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.ValueCommitment RegionId.ValueCommitment.CompletePointAdd; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.ValueCommitment RegionId.ValueCommitment.ValueCommitRLast; Cell.row_offset := 1 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A3; Cell.region := RegionId.ValueCommitment RegionId.ValueCommitment.CompletePointAdd; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A3; Cell.region := RegionId.ValueCommitment RegionId.ValueCommitment.ValueCommitRLast; Cell.row_offset := 1 |};
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Poseidon RegionId.Poseidon.InitialState; Cell.row_offset := 0 |} 0;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Poseidon RegionId.Poseidon.InitialState; Cell.row_offset := 0 |} 0;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A8; Cell.region := RegionId.Poseidon RegionId.Poseidon.InitialState; Cell.row_offset := 0 |} 36893488147419103232;
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Poseidon RegionId.Poseidon.AddInput; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Poseidon RegionId.Poseidon.InitialState; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Poseidon RegionId.Poseidon.AddInput; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Poseidon RegionId.Poseidon.InitialState; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A8; Cell.region := RegionId.Poseidon RegionId.Poseidon.AddInput; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A8; Cell.region := RegionId.Poseidon RegionId.Poseidon.InitialState; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.WitnessInput RegionId.WitnessInput.Nk; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Poseidon RegionId.Poseidon.AddInput; Cell.row_offset := 1 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.WitnessInput RegionId.WitnessInput.RhoOld; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Poseidon RegionId.Poseidon.AddInput; Cell.row_offset := 1 |}].

  Definition wf_mech_11 : list (Fact.t columns RegionId.t) := [
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Poseidon RegionId.Poseidon.PermuteState; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Poseidon RegionId.Poseidon.AddInput; Cell.row_offset := 2 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Poseidon RegionId.Poseidon.PermuteState; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Poseidon RegionId.Poseidon.AddInput; Cell.row_offset := 2 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A8; Cell.region := RegionId.Poseidon RegionId.Poseidon.PermuteState; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A8; Cell.region := RegionId.Poseidon RegionId.Poseidon.AddInput; Cell.row_offset := 2 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A8; Cell.region := RegionId.Nullifier RegionId.Nullifier.ScalarAdd; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.WitnessInput RegionId.WitnessInput.PsiOld; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.Nullifier RegionId.Nullifier.BaseFieldComplete; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.Nullifier RegionId.Nullifier.BaseFieldIncomplete; Cell.row_offset := 84 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A1; Cell.region := RegionId.Nullifier RegionId.Nullifier.BaseFieldComplete; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A1; Cell.region := RegionId.Nullifier RegionId.Nullifier.BaseFieldIncomplete; Cell.row_offset := 84 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Nullifier RegionId.Nullifier.BaseFieldComplete; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Nullifier RegionId.Nullifier.BaseFieldIncomplete; Cell.row_offset := 84 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A3; Cell.region := RegionId.Nullifier RegionId.Nullifier.BaseFieldComplete; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A3; Cell.region := RegionId.Nullifier RegionId.Nullifier.BaseFieldIncomplete; Cell.row_offset := 84 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A8; Cell.region := RegionId.Nullifier RegionId.Nullifier.CanonicityChecks; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A4; Cell.region := RegionId.Nullifier RegionId.Nullifier.BaseFieldIncomplete; Cell.row_offset := 84 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.Nullifier RegionId.Nullifier.CanonicityChecks; Cell.row_offset := 2 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.Nullifier RegionId.Nullifier.AlphaLookup; Cell.row_offset := 13 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.Nullifier RegionId.Nullifier.CanonicityChecks; Cell.row_offset := 2 |} {| Cell.column := ColumnRef.Advice Advice.A4; Cell.region := RegionId.Nullifier RegionId.Nullifier.BaseFieldIncomplete; Cell.row_offset := 44 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A8; Cell.region := RegionId.Nullifier RegionId.Nullifier.CanonicityChecks; Cell.row_offset := 2 |} {| Cell.column := ColumnRef.Advice Advice.A4; Cell.region := RegionId.Nullifier RegionId.Nullifier.BaseFieldIncomplete; Cell.row_offset := 43 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.Nullifier RegionId.Nullifier.CompletePointAdd; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.WitnessInput RegionId.WitnessInput.CmOld; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A1; Cell.region := RegionId.Nullifier RegionId.Nullifier.CompletePointAdd; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A1; Cell.region := RegionId.WitnessInput RegionId.WitnessInput.CmOld; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Nullifier RegionId.Nullifier.CompletePointAdd; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.Nullifier RegionId.Nullifier.BaseFieldComplete; Cell.row_offset := 1 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A3; Cell.region := RegionId.Nullifier RegionId.Nullifier.CompletePointAdd; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A3; Cell.region := RegionId.Nullifier RegionId.Nullifier.BaseFieldComplete; Cell.row_offset := 1 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.SpendAuthority RegionId.SpendAuthority.FullFixedIncomplete; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.SpendAuthority RegionId.SpendAuthority.FullFixedIncomplete; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A3; Cell.region := RegionId.SpendAuthority RegionId.SpendAuthority.FullFixedIncomplete; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A1; Cell.region := RegionId.SpendAuthority RegionId.SpendAuthority.FullFixedIncomplete; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.SpendAuthority RegionId.SpendAuthority.FullFixedLast; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.SpendAuthority RegionId.SpendAuthority.FullFixedIncomplete; Cell.row_offset := 84 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A1; Cell.region := RegionId.SpendAuthority RegionId.SpendAuthority.FullFixedLast; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A1; Cell.region := RegionId.SpendAuthority RegionId.SpendAuthority.FullFixedIncomplete; Cell.row_offset := 84 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.SpendAuthority RegionId.SpendAuthority.FullFixedLast; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.SpendAuthority RegionId.SpendAuthority.FullFixedIncomplete; Cell.row_offset := 84 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A3; Cell.region := RegionId.SpendAuthority RegionId.SpendAuthority.FullFixedLast; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A3; Cell.region := RegionId.SpendAuthority RegionId.SpendAuthority.FullFixedIncomplete; Cell.row_offset := 84 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.SpendAuthority RegionId.SpendAuthority.CompletePointAdd; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.SpendAuthority RegionId.SpendAuthority.FullFixedLast; Cell.row_offset := 1 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A1; Cell.region := RegionId.SpendAuthority RegionId.SpendAuthority.CompletePointAdd; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A3; Cell.region := RegionId.SpendAuthority RegionId.SpendAuthority.FullFixedLast; Cell.row_offset := 1 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.SpendAuthority RegionId.SpendAuthority.CompletePointAdd; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.WitnessInput RegionId.WitnessInput.AkP; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A3; Cell.region := RegionId.SpendAuthority RegionId.SpendAuthority.CompletePointAdd; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A1; Cell.region := RegionId.WitnessInput RegionId.WitnessInput.AkP; Cell.row_offset := 0 |};
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.CommitIvk RegionId.CommitIvk.RangeB0; Cell.row_offset := 2 |} 27138770914995983302399449611411228403152865451820213171207509466578094653441;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.CommitIvk RegionId.CommitIvk.RangeB2; Cell.row_offset := 2 |} 28043396612162516079146097931791602683257960966880886943581093115464031141889;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.CommitIvk RegionId.CommitIvk.RangeD0; Cell.row_offset := 2 |} 28891483203256140557346080732148203570856488012250268605181327786294596599809;
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.CommitIvk RegionId.CommitIvk.FixedBaseIncomplete; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.CommitIvk RegionId.CommitIvk.FixedBaseIncomplete; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A3; Cell.region := RegionId.CommitIvk RegionId.CommitIvk.FixedBaseIncomplete; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A1; Cell.region := RegionId.CommitIvk RegionId.CommitIvk.FixedBaseIncomplete; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.CommitIvk RegionId.CommitIvk.FixedBaseLast; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.CommitIvk RegionId.CommitIvk.FixedBaseIncomplete; Cell.row_offset := 84 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A1; Cell.region := RegionId.CommitIvk RegionId.CommitIvk.FixedBaseLast; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A1; Cell.region := RegionId.CommitIvk RegionId.CommitIvk.FixedBaseIncomplete; Cell.row_offset := 84 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.CommitIvk RegionId.CommitIvk.FixedBaseLast; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.CommitIvk RegionId.CommitIvk.FixedBaseIncomplete; Cell.row_offset := 84 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A3; Cell.region := RegionId.CommitIvk RegionId.CommitIvk.FixedBaseLast; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A3; Cell.region := RegionId.CommitIvk RegionId.CommitIvk.FixedBaseIncomplete; Cell.row_offset := 84 |};
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.CommitIvk RegionId.CommitIvk.HashToPoint; Cell.row_offset := 0 |} 2593820817260930114322133467408868473290945477826616247349533151445648376562;
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.CommitIvk RegionId.CommitIvk.CompletePointAdd; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.CommitIvk RegionId.CommitIvk.FixedBaseLast; Cell.row_offset := 1 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A3; Cell.region := RegionId.CommitIvk RegionId.CommitIvk.CompletePointAdd; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A3; Cell.region := RegionId.CommitIvk RegionId.CommitIvk.FixedBaseLast; Cell.row_offset := 1 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.CommitIvk RegionId.CommitIvk.CanonicityGate; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.WitnessInput RegionId.WitnessInput.AkP; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A1; Cell.region := RegionId.CommitIvk RegionId.CommitIvk.CanonicityGate; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.CommitIvk RegionId.CommitIvk.WitnessA; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.CommitIvk RegionId.CommitIvk.CanonicityGate; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.CommitIvk RegionId.CommitIvk.WitnessB; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A3; Cell.region := RegionId.CommitIvk RegionId.CommitIvk.CanonicityGate; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.CommitIvk RegionId.CommitIvk.RangeB0; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A5; Cell.region := RegionId.CommitIvk RegionId.CommitIvk.CanonicityGate; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.CommitIvk RegionId.CommitIvk.RangeB2; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A8; Cell.region := RegionId.CommitIvk RegionId.CommitIvk.CanonicityGate; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.CommitIvk RegionId.CommitIvk.AkLookup; Cell.row_offset := 13 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.CommitIvk RegionId.CommitIvk.CanonicityGate; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.WitnessInput RegionId.WitnessInput.Nk; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A1; Cell.region := RegionId.CommitIvk RegionId.CommitIvk.CanonicityGate; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.CommitIvk RegionId.CommitIvk.WitnessC; Cell.row_offset := 0 |}].

  Definition wf_mech_12 : list (Fact.t columns RegionId.t) := [
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.CommitIvk RegionId.CommitIvk.CanonicityGate; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.CommitIvk RegionId.CommitIvk.WitnessD; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A3; Cell.region := RegionId.CommitIvk RegionId.CommitIvk.CanonicityGate; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.CommitIvk RegionId.CommitIvk.RangeD0; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A8; Cell.region := RegionId.CommitIvk RegionId.CommitIvk.CanonicityGate; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.CommitIvk RegionId.CommitIvk.NkLookup; Cell.row_offset := 14 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.AddressIntegrity (RegionId.AddressIntegrity.Mul RegionId.AddressIntegrity.Mul.VariableBase); Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.WitnessInput RegionId.WitnessInput.GDOld; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A1; Cell.region := RegionId.AddressIntegrity (RegionId.AddressIntegrity.Mul RegionId.AddressIntegrity.Mul.VariableBase); Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A1; Cell.region := RegionId.WitnessInput RegionId.WitnessInput.GDOld; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.AddressIntegrity (RegionId.AddressIntegrity.Mul RegionId.AddressIntegrity.Mul.VariableBase); Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.WitnessInput RegionId.WitnessInput.GDOld; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A3; Cell.region := RegionId.AddressIntegrity (RegionId.AddressIntegrity.Mul RegionId.AddressIntegrity.Mul.VariableBase); Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A1; Cell.region := RegionId.WitnessInput RegionId.WitnessInput.GDOld; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A3; Cell.region := RegionId.AddressIntegrity (RegionId.AddressIntegrity.Mul RegionId.AddressIntegrity.Mul.VariableBase); Cell.row_offset := 2 |} {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.AddressIntegrity (RegionId.AddressIntegrity.Mul RegionId.AddressIntegrity.Mul.VariableBase); Cell.row_offset := 1 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A4; Cell.region := RegionId.AddressIntegrity (RegionId.AddressIntegrity.Mul RegionId.AddressIntegrity.Mul.VariableBase); Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A3; Cell.region := RegionId.AddressIntegrity (RegionId.AddressIntegrity.Mul RegionId.AddressIntegrity.Mul.VariableBase); Cell.row_offset := 1 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.AddressIntegrity (RegionId.AddressIntegrity.Mul RegionId.AddressIntegrity.Mul.VariableBase); Cell.row_offset := 2 |} {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.WitnessInput RegionId.WitnessInput.GDOld; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A1; Cell.region := RegionId.AddressIntegrity (RegionId.AddressIntegrity.Mul RegionId.AddressIntegrity.Mul.VariableBase); Cell.row_offset := 2 |} {| Cell.column := ColumnRef.Advice Advice.A1; Cell.region := RegionId.WitnessInput RegionId.WitnessInput.GDOld; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.AddressIntegrity (RegionId.AddressIntegrity.Mul RegionId.AddressIntegrity.Mul.VariableBase); Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.AddressIntegrity (RegionId.AddressIntegrity.Mul RegionId.AddressIntegrity.Mul.VariableBase); Cell.row_offset := 126 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A8; Cell.region := RegionId.AddressIntegrity (RegionId.AddressIntegrity.Mul RegionId.AddressIntegrity.Mul.VariableBase); Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A4; Cell.region := RegionId.AddressIntegrity (RegionId.AddressIntegrity.Mul RegionId.AddressIntegrity.Mul.VariableBase); Cell.row_offset := 127 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.AddressIntegrity (RegionId.AddressIntegrity.Mul RegionId.AddressIntegrity.Mul.VariableBase); Cell.row_offset := 2 |} {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.WitnessInput RegionId.WitnessInput.GDOld; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A1; Cell.region := RegionId.AddressIntegrity (RegionId.AddressIntegrity.Mul RegionId.AddressIntegrity.Mul.VariableBase); Cell.row_offset := 2 |} {| Cell.column := ColumnRef.Advice Advice.A1; Cell.region := RegionId.WitnessInput RegionId.WitnessInput.GDOld; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.AddressIntegrity (RegionId.AddressIntegrity.Mul RegionId.AddressIntegrity.Mul.VariableBase); Cell.row_offset := 129 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.AddressIntegrity (RegionId.AddressIntegrity.Mul RegionId.AddressIntegrity.Mul.VariableBase); Cell.row_offset := 127 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.AddressIntegrity (RegionId.AddressIntegrity.Mul RegionId.AddressIntegrity.Mul.VariableBase); Cell.row_offset := 130 |} {| Cell.column := ColumnRef.Advice Advice.A1; Cell.region := RegionId.WitnessInput RegionId.WitnessInput.GDOld; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.AddressIntegrity (RegionId.AddressIntegrity.Mul RegionId.AddressIntegrity.Mul.VariableBase); Cell.row_offset := 129 |} {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.WitnessInput RegionId.WitnessInput.GDOld; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.AddressIntegrity (RegionId.AddressIntegrity.Mul RegionId.AddressIntegrity.Mul.VariableBase); Cell.row_offset := 129 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.AddressIntegrity (RegionId.AddressIntegrity.Mul RegionId.AddressIntegrity.Mul.VariableBase); Cell.row_offset := 128 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A3; Cell.region := RegionId.AddressIntegrity (RegionId.AddressIntegrity.Mul RegionId.AddressIntegrity.Mul.VariableBase); Cell.row_offset := 129 |} {| Cell.column := ColumnRef.Advice Advice.A8; Cell.region := RegionId.AddressIntegrity (RegionId.AddressIntegrity.Mul RegionId.AddressIntegrity.Mul.VariableBase); Cell.row_offset := 128 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.AddressIntegrity (RegionId.AddressIntegrity.Mul RegionId.AddressIntegrity.Mul.VariableBase); Cell.row_offset := 130 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.AddressIntegrity (RegionId.AddressIntegrity.Mul RegionId.AddressIntegrity.Mul.VariableBase); Cell.row_offset := 128 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A1; Cell.region := RegionId.AddressIntegrity (RegionId.AddressIntegrity.Mul RegionId.AddressIntegrity.Mul.VariableBase); Cell.row_offset := 130 |} {| Cell.column := ColumnRef.Advice Advice.A8; Cell.region := RegionId.AddressIntegrity (RegionId.AddressIntegrity.Mul RegionId.AddressIntegrity.Mul.VariableBase); Cell.row_offset := 128 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.AddressIntegrity (RegionId.AddressIntegrity.Mul RegionId.AddressIntegrity.Mul.VariableBase); Cell.row_offset := 132 |} {| Cell.column := ColumnRef.Advice Advice.A1; Cell.region := RegionId.WitnessInput RegionId.WitnessInput.GDOld; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.AddressIntegrity (RegionId.AddressIntegrity.Mul RegionId.AddressIntegrity.Mul.VariableBase); Cell.row_offset := 131 |} {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.WitnessInput RegionId.WitnessInput.GDOld; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.AddressIntegrity (RegionId.AddressIntegrity.Mul RegionId.AddressIntegrity.Mul.VariableBase); Cell.row_offset := 132 |} {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.AddressIntegrity (RegionId.AddressIntegrity.Mul RegionId.AddressIntegrity.Mul.VariableBase); Cell.row_offset := 131 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A1; Cell.region := RegionId.AddressIntegrity (RegionId.AddressIntegrity.Mul RegionId.AddressIntegrity.Mul.VariableBase); Cell.row_offset := 132 |} {| Cell.column := ColumnRef.Advice Advice.A3; Cell.region := RegionId.AddressIntegrity (RegionId.AddressIntegrity.Mul RegionId.AddressIntegrity.Mul.VariableBase); Cell.row_offset := 131 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.AddressIntegrity (RegionId.AddressIntegrity.Mul RegionId.AddressIntegrity.Mul.VariableBase); Cell.row_offset := 134 |} {| Cell.column := ColumnRef.Advice Advice.A1; Cell.region := RegionId.WitnessInput RegionId.WitnessInput.GDOld; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.AddressIntegrity (RegionId.AddressIntegrity.Mul RegionId.AddressIntegrity.Mul.VariableBase); Cell.row_offset := 133 |} {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.WitnessInput RegionId.WitnessInput.GDOld; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.AddressIntegrity (RegionId.AddressIntegrity.Mul RegionId.AddressIntegrity.Mul.VariableBase); Cell.row_offset := 134 |} {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.AddressIntegrity (RegionId.AddressIntegrity.Mul RegionId.AddressIntegrity.Mul.VariableBase); Cell.row_offset := 133 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A1; Cell.region := RegionId.AddressIntegrity (RegionId.AddressIntegrity.Mul RegionId.AddressIntegrity.Mul.VariableBase); Cell.row_offset := 134 |} {| Cell.column := ColumnRef.Advice Advice.A3; Cell.region := RegionId.AddressIntegrity (RegionId.AddressIntegrity.Mul RegionId.AddressIntegrity.Mul.VariableBase); Cell.row_offset := 133 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.AddressIntegrity (RegionId.AddressIntegrity.Mul RegionId.AddressIntegrity.Mul.VariableBase); Cell.row_offset := 136 |} {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.WitnessInput RegionId.WitnessInput.GDOld; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A1; Cell.region := RegionId.AddressIntegrity (RegionId.AddressIntegrity.Mul RegionId.AddressIntegrity.Mul.VariableBase); Cell.row_offset := 136 |} {| Cell.column := ColumnRef.Advice Advice.A1; Cell.region := RegionId.WitnessInput RegionId.WitnessInput.GDOld; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.AddressIntegrity (RegionId.AddressIntegrity.Mul RegionId.AddressIntegrity.Mul.OverflowCheck); Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.AddressIntegrity (RegionId.AddressIntegrity.Mul RegionId.AddressIntegrity.Mul.VariableBase); Cell.row_offset := 136 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.AddressIntegrity (RegionId.AddressIntegrity.Mul RegionId.AddressIntegrity.Mul.OverflowCheck); Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.AddressIntegrity (RegionId.AddressIntegrity.Mul RegionId.AddressIntegrity.Mul.VariableBase); Cell.row_offset := 126 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.AddressIntegrity (RegionId.AddressIntegrity.Mul RegionId.AddressIntegrity.Mul.OverflowCheck); Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.AddressIntegrity (RegionId.AddressIntegrity.Mul RegionId.AddressIntegrity.Mul.VariableBase); Cell.row_offset := 2 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.AddressIntegrity (RegionId.AddressIntegrity.Mul RegionId.AddressIntegrity.Mul.OverflowCheck); Cell.row_offset := 2 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.AddressIntegrity (RegionId.AddressIntegrity.Mul RegionId.AddressIntegrity.Mul.OverflowLookup); Cell.row_offset := 13 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A8; Cell.region := RegionId.AddressIntegrity (RegionId.AddressIntegrity.Mul RegionId.AddressIntegrity.Mul.OverflowCheck); Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.AddressIntegrity (RegionId.AddressIntegrity.Mul RegionId.AddressIntegrity.Mul.OverflowS); Cell.row_offset := 0 |};
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.RangeB0; Cell.row_offset := 2 |} 27138770914995983302399449611411228403152865451820213171207509466578094653441;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.RangeB3; Cell.row_offset := 2 |} 27138770914995983302399449611411228403152865451820213171207509466578094653441;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.RangeD2; Cell.row_offset := 2 |} 28834944097183232258799415212124430178349919542558976494407978808239225569281;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.RangeE0; Cell.row_offset := 2 |} 28495709460745782467519422091981789823310508724411223829767884939906999386113;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.RangeE1; Cell.row_offset := 2 |} 27138770914995983302399449611411228403152865451820213171207509466578094653441;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.RangeG1; Cell.row_offset := 2 |} 28891483203256140557346080732148203570856488012250268605181327786294596599809;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.RangeH0; Cell.row_offset := 2 |} 28043396612162516079146097931791602683257960966880886943581093115464031141889;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.GD RegionId.NoteCommit.YCanonicity.RangeK0); Cell.row_offset := 2 |} 28891483203256140557346080732148203570856488012250268605181327786294596599809;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.GD RegionId.NoteCommit.YCanonicity.RangeK2); Cell.row_offset := 2 |} 27138770914995983302399449611411228403152865451820213171207509466578094653441].

  Definition wf_mech_13 : list (Fact.t columns RegionId.t) := [
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A5; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.GD RegionId.NoteCommit.YCanonicity.Gate); Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A1; Cell.region := RegionId.WitnessInput RegionId.WitnessInput.GDOld; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.GD RegionId.NoteCommit.YCanonicity.Gate); Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.GD RegionId.NoteCommit.YCanonicity.RangeK0); Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A8; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.GD RegionId.NoteCommit.YCanonicity.Gate); Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.GD RegionId.NoteCommit.YCanonicity.RangeK2); Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.GD RegionId.NoteCommit.YCanonicity.Gate); Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.GD RegionId.NoteCommit.YCanonicity.JLookup); Cell.row_offset := 1 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.GD RegionId.NoteCommit.YCanonicity.Gate); Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.GD RegionId.NoteCommit.YCanonicity.JLookup); Cell.row_offset := 13 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.GD RegionId.NoteCommit.YCanonicity.Gate); Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.GD RegionId.NoteCommit.YCanonicity.JPrimeLookup); Cell.row_offset := 13 |};
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.PkD RegionId.NoteCommit.YCanonicity.RangeK0); Cell.row_offset := 2 |} 28891483203256140557346080732148203570856488012250268605181327786294596599809;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.PkD RegionId.NoteCommit.YCanonicity.RangeK2); Cell.row_offset := 2 |} 27138770914995983302399449611411228403152865451820213171207509466578094653441;
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.PkD RegionId.NoteCommit.YCanonicity.Gate); Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.PkD RegionId.NoteCommit.YCanonicity.RangeK0); Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A8; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.PkD RegionId.NoteCommit.YCanonicity.Gate); Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.PkD RegionId.NoteCommit.YCanonicity.RangeK2); Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.PkD RegionId.NoteCommit.YCanonicity.Gate); Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.PkD RegionId.NoteCommit.YCanonicity.JLookup); Cell.row_offset := 1 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.PkD RegionId.NoteCommit.YCanonicity.Gate); Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.PkD RegionId.NoteCommit.YCanonicity.JLookup); Cell.row_offset := 13 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.PkD RegionId.NoteCommit.YCanonicity.Gate); Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.PkD RegionId.NoteCommit.YCanonicity.JPrimeLookup); Cell.row_offset := 13 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.FixedBaseIncomplete; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.FixedBaseIncomplete; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A3; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.FixedBaseIncomplete; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A1; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.FixedBaseIncomplete; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.FixedBaseLast; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.FixedBaseIncomplete; Cell.row_offset := 84 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A1; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.FixedBaseLast; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A1; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.FixedBaseIncomplete; Cell.row_offset := 84 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.FixedBaseLast; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.FixedBaseIncomplete; Cell.row_offset := 84 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A3; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.FixedBaseLast; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A3; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.FixedBaseIncomplete; Cell.row_offset := 84 |};
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.HashToPoint; Cell.row_offset := 0 |} 10629404576683096409262958701336170057000067777256141967953463442979689100381;
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.MessagePieceB; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.WitnessB; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.MessagePieceB; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.RangeB0; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A8; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.MessagePieceB; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.RangeB3; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.MessagePieceD; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.WitnessD; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.MessagePieceD; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.RangeD2; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.MessagePieceE; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.WitnessE; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.MessagePieceE; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.RangeE0; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A8; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.MessagePieceE; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.RangeE1; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.MessagePieceG; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.WitnessG; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.MessagePieceG; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.RangeG1; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.MessagePieceH; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.WitnessH; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.MessagePieceH; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.RangeH0; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.InputGD; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.WitnessInput RegionId.WitnessInput.GDOld; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.InputGD; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.RangeB0; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.InputGD; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A8; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.MessagePieceB; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A8; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.InputGD; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.WitnessA; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.InputGD; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.XGDLookup; Cell.row_offset := 13 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.InputPkD; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.RangeB3; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.InputPkD; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.MessagePieceD; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A8; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.InputPkD; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.WitnessC; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.InputPkD; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.XPKDLookup; Cell.row_offset := 14 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.InputValue; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.WitnessInput RegionId.WitnessInput.VOld; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.InputValue; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.RangeD2; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.InputValue; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.RangeE0; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.InputRho; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.WitnessInput RegionId.WitnessInput.RhoOld; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.InputRho; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.RangeE1; Cell.row_offset := 0 |}].

  Definition wf_mech_14 : list (Fact.t columns RegionId.t) := [
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.InputRho; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.MessagePieceG; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A8; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.InputRho; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.WitnessF; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.InputRho; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.RhoLookup; Cell.row_offset := 14 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.InputPsi; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.WitnessInput RegionId.WitnessInput.PsiOld; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.InputPsi; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.RangeH0; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.InputPsi; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.RangeG1; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.InputPsi; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A8; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.MessagePieceH; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.InputPsi; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.PsiLookup; Cell.row_offset := 13 |};
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.RangeB0; Cell.row_offset := 2 |} 27138770914995983302399449611411228403152865451820213171207509466578094653441;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.RangeB3; Cell.row_offset := 2 |} 27138770914995983302399449611411228403152865451820213171207509466578094653441;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.RangeD2; Cell.row_offset := 2 |} 28834944097183232258799415212124430178349919542558976494407978808239225569281;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.RangeE0; Cell.row_offset := 2 |} 28495709460745782467519422091981789823310508724411223829767884939906999386113;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.RangeE1; Cell.row_offset := 2 |} 27138770914995983302399449611411228403152865451820213171207509466578094653441;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.RangeG1; Cell.row_offset := 2 |} 28891483203256140557346080732148203570856488012250268605181327786294596599809;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.RangeH0; Cell.row_offset := 2 |} 28043396612162516079146097931791602683257960966880886943581093115464031141889;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.GD RegionId.NoteCommit.YCanonicity.RangeK0); Cell.row_offset := 2 |} 28891483203256140557346080732148203570856488012250268605181327786294596599809;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.GD RegionId.NoteCommit.YCanonicity.RangeK2); Cell.row_offset := 2 |} 27138770914995983302399449611411228403152865451820213171207509466578094653441;
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A5; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.GD RegionId.NoteCommit.YCanonicity.Gate); Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A1; Cell.region := RegionId.NoteCommitNewWitnessGD; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.GD RegionId.NoteCommit.YCanonicity.Gate); Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.GD RegionId.NoteCommit.YCanonicity.RangeK0); Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A8; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.GD RegionId.NoteCommit.YCanonicity.Gate); Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.GD RegionId.NoteCommit.YCanonicity.RangeK2); Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.GD RegionId.NoteCommit.YCanonicity.Gate); Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.GD RegionId.NoteCommit.YCanonicity.JLookup); Cell.row_offset := 1 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.GD RegionId.NoteCommit.YCanonicity.Gate); Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.GD RegionId.NoteCommit.YCanonicity.JLookup); Cell.row_offset := 13 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.GD RegionId.NoteCommit.YCanonicity.Gate); Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.GD RegionId.NoteCommit.YCanonicity.JPrimeLookup); Cell.row_offset := 13 |};
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.PkD RegionId.NoteCommit.YCanonicity.RangeK0); Cell.row_offset := 2 |} 28891483203256140557346080732148203570856488012250268605181327786294596599809;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.PkD RegionId.NoteCommit.YCanonicity.RangeK2); Cell.row_offset := 2 |} 27138770914995983302399449611411228403152865451820213171207509466578094653441;
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A5; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.PkD RegionId.NoteCommit.YCanonicity.Gate); Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A1; Cell.region := RegionId.NoteCommitNewWitnessPkD; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.PkD RegionId.NoteCommit.YCanonicity.Gate); Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.PkD RegionId.NoteCommit.YCanonicity.RangeK0); Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A8; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.PkD RegionId.NoteCommit.YCanonicity.Gate); Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.PkD RegionId.NoteCommit.YCanonicity.RangeK2); Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.PkD RegionId.NoteCommit.YCanonicity.Gate); Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.PkD RegionId.NoteCommit.YCanonicity.JLookup); Cell.row_offset := 1 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.PkD RegionId.NoteCommit.YCanonicity.Gate); Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.PkD RegionId.NoteCommit.YCanonicity.JLookup); Cell.row_offset := 13 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.PkD RegionId.NoteCommit.YCanonicity.Gate); Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New (RegionId.NoteCommit.YCanonicity RegionId.NoteCommit.YSubject.PkD RegionId.NoteCommit.YCanonicity.JPrimeLookup); Cell.row_offset := 13 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.FixedBaseIncomplete; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.FixedBaseIncomplete; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A3; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.FixedBaseIncomplete; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A1; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.FixedBaseIncomplete; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.FixedBaseLast; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.FixedBaseIncomplete; Cell.row_offset := 84 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A1; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.FixedBaseLast; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A1; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.FixedBaseIncomplete; Cell.row_offset := 84 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.FixedBaseLast; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.FixedBaseIncomplete; Cell.row_offset := 84 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A3; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.FixedBaseLast; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A3; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.FixedBaseIncomplete; Cell.row_offset := 84 |};
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A5; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.HashToPoint; Cell.row_offset := 0 |} 10629404576683096409262958701336170057000067777256141967953463442979689100381;
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.MessagePieceB; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.WitnessB; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.MessagePieceB; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.RangeB0; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A8; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.MessagePieceB; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.RangeB3; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.MessagePieceD; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.WitnessD; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.MessagePieceD; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.RangeD2; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.MessagePieceE; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.WitnessE; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.MessagePieceE; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.RangeE0; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A8; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.MessagePieceE; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.RangeE1; Cell.row_offset := 0 |}].

  Definition wf_mech_15 : list (Fact.t columns RegionId.t) := [
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.MessagePieceG; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.WitnessG; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.MessagePieceG; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.RangeG1; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.MessagePieceH; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.WitnessH; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.MessagePieceH; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.RangeH0; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.InputGD; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.NoteCommitNewWitnessGD; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.InputGD; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.RangeB0; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.InputGD; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A8; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.MessagePieceB; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A8; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.InputGD; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.WitnessA; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.InputGD; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.XGDLookup; Cell.row_offset := 13 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.InputPkD; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.NoteCommitNewWitnessPkD; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.InputPkD; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.RangeB3; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.InputPkD; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.MessagePieceD; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A8; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.InputPkD; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.WitnessC; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.InputPkD; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.XPKDLookup; Cell.row_offset := 14 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.InputValue; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.WitnessInput RegionId.WitnessInput.VNew; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.InputValue; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.RangeD2; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.InputValue; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.RangeE0; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.InputRho; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.RangeE1; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.InputRho; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.MessagePieceG; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A8; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.InputRho; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.WitnessF; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.InputRho; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.RhoLookup; Cell.row_offset := 14 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.InputPsi; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.NoteCommitNewWitnessPsi; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.InputPsi; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.RangeH0; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.InputPsi; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.RangeG1; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.InputPsi; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A8; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.MessagePieceH; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.InputPsi; Cell.row_offset := 1 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.PsiLookup; Cell.row_offset := 13 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.OrchardCircuitChecks; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.WitnessInput RegionId.WitnessInput.VOld; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A1; Cell.region := RegionId.OrchardCircuitChecks; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.WitnessInput RegionId.WitnessInput.VNew; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.OrchardCircuitChecks; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.ValueCommitment RegionId.ValueCommitment.MagnitudeRangeCheck; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A3; Cell.region := RegionId.OrchardCircuitChecks; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A9; Cell.region := RegionId.ValueCommitment RegionId.ValueCommitment.SignRangeCheck; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A5; Cell.region := RegionId.OrchardCircuitChecks; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Instance_ Instance_.Primary; Cell.region := RegionId.OrchardCircuitChecks; Cell.row_offset := 0 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A6; Cell.region := RegionId.OrchardCircuitChecks; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Instance_ Instance_.Primary; Cell.region := RegionId.OrchardCircuitChecks; Cell.row_offset := 7 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A7; Cell.region := RegionId.OrchardCircuitChecks; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Instance_ Instance_.Primary; Cell.region := RegionId.OrchardCircuitChecks; Cell.row_offset := 8 |}].

  Definition wf_minit_0 : list (Fact.t columns RegionId.t) := [
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L0 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 0 |} 9991206725476878888751475603038274618448000607209514551456795194094072219296;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L1 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 0 |} 9991206725476878888751475603038274618448000607209514551456795194094072219296;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L2 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 0 |} 9991206725476878888751475603038274618448000607209514551456795194094072219296;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L3 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 0 |} 9991206725476878888751475603038274618448000607209514551456795194094072219296;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L4 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 0 |} 9991206725476878888751475603038274618448000607209514551456795194094072219296;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L5 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 0 |} 9991206725476878888751475603038274618448000607209514551456795194094072219296;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L6 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 0 |} 9991206725476878888751475603038274618448000607209514551456795194094072219296;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L7 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 0 |} 9991206725476878888751475603038274618448000607209514551456795194094072219296;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L8 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 0 |} 9991206725476878888751475603038274618448000607209514551456795194094072219296;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L9 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 0 |} 9991206725476878888751475603038274618448000607209514551456795194094072219296;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L10 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 0 |} 9991206725476878888751475603038274618448000607209514551456795194094072219296;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L11 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 0 |} 9991206725476878888751475603038274618448000607209514551456795194094072219296;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L12 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 0 |} 9991206725476878888751475603038274618448000607209514551456795194094072219296;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L13 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 0 |} 9991206725476878888751475603038274618448000607209514551456795194094072219296;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L14 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 0 |} 9991206725476878888751475603038274618448000607209514551456795194094072219296;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A0; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L15 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 0 |} 9991206725476878888751475603038274618448000607209514551456795194094072219296;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A5; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L16 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 0 |} 9991206725476878888751475603038274618448000607209514551456795194094072219296;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A5; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L17 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 0 |} 9991206725476878888751475603038274618448000607209514551456795194094072219296;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A5; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L18 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 0 |} 9991206725476878888751475603038274618448000607209514551456795194094072219296;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A5; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L19 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 0 |} 9991206725476878888751475603038274618448000607209514551456795194094072219296;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A5; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L20 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 0 |} 9991206725476878888751475603038274618448000607209514551456795194094072219296;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A5; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L21 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 0 |} 9991206725476878888751475603038274618448000607209514551456795194094072219296;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A5; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L22 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 0 |} 9991206725476878888751475603038274618448000607209514551456795194094072219296;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A5; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L23 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 0 |} 9991206725476878888751475603038274618448000607209514551456795194094072219296;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A5; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L24 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 0 |} 9991206725476878888751475603038274618448000607209514551456795194094072219296;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A5; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L25 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 0 |} 9991206725476878888751475603038274618448000607209514551456795194094072219296;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A5; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L26 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 0 |} 9991206725476878888751475603038274618448000607209514551456795194094072219296;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A5; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L27 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 0 |} 9991206725476878888751475603038274618448000607209514551456795194094072219296;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A5; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L28 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 0 |} 9991206725476878888751475603038274618448000607209514551456795194094072219296;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A5; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L29 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 0 |} 9991206725476878888751475603038274618448000607209514551456795194094072219296;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A5; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L30 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 0 |} 9991206725476878888751475603038274618448000607209514551456795194094072219296;
    Fact.CellIsConstant {| Cell.column := ColumnRef.Advice Advice.A5; Cell.region := RegionId.Merkle RegionId.Merkle.Layer.L31 RegionId.Merkle.Region.HashToPoint; Cell.row_offset := 0 |} 9991206725476878888751475603038274618448000607209514551456795194094072219296].

  Definition wf_shape_0 : list (Fact.t columns RegionId.t) := [
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.CompletePointAdd; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.FixedBaseLast; Cell.row_offset := 1 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A3; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.CompletePointAdd; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A3; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.Old RegionId.NoteCommit.FixedBaseLast; Cell.row_offset := 1 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.CompletePointAdd; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A2; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.FixedBaseLast; Cell.row_offset := 1 |};
    Fact.CellsEqual {| Cell.column := ColumnRef.Advice Advice.A3; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.CompletePointAdd; Cell.row_offset := 0 |} {| Cell.column := ColumnRef.Advice Advice.A3; Cell.region := RegionId.NoteCommit RegionId.NoteCommit.Which.New RegionId.NoteCommit.FixedBaseLast; Cell.row_offset := 1 |}].

  Definition nt_closed : list (Fact.t columns RegionId.t) :=
    wf_mnode_0 ++
    wf_mech_0 ++
    wf_mech_1 ++
    wf_mech_2 ++
    wf_mech_3 ++
    wf_mech_4 ++
    wf_mech_5 ++
    wf_mech_6 ++
    wf_mech_7 ++
    wf_mech_8 ++
    wf_mech_9 ++
    wf_mech_10 ++
    wf_mech_11 ++
    wf_mech_12 ++
    wf_mech_13 ++
    wf_mech_14 ++
    wf_mech_15 ++
    wf_minit_0 ++
    wf_shape_0.

  (** The residue of the 888 non-self-copy facts: the facts whose two sides
      are distinct derivations of one value.  Each group is pinned and proved
      in its own file under [forward/witness/]; regrouping is sound because
      [nt_cover] is an order-insensitive [existsb] scan over the same
      multiset. *)
  Definition nt_open : list (Fact.t columns RegionId.t) :=
    OrchardWitnessBitsColumn.orchardwitnessbitscolumn_facts ++
    OrchardWitnessChainOutputs.orchardwitnesschainoutputs_facts ++
    OrchardWitnessSliceBounds.orchardwitnessslicebounds_facts ++
    OrchardWitnessFixedLegs.orchardwitnessfixedlegs_facts ++
    OrchardWitnessVarBase.orchardwitnessvarbase_facts.

  (** Coverage: every non-self-copy witness fact of the synthesis program
      is one of the pinned facts. *)
  Lemma nt_cover :
    List.forallb
      (fun f => List.existsb (fact_beq f) (nt_closed ++ nt_open))
      (List.filter (fun f => negb (fact_trivial f))
        (Complete.witness_facts facts)) = true.
  Proof. vm_cast_no_check (@eq_refl bool true). Qed.

  (** *** Cell readings used by the grouped proofs

      Each is a definitional reading of the advice dispatch at one address,
      or a zeta expansion of one field of the hoisted record: the right-hand
      sides are the exact stuck terms the dispatch produces, so no reduction
      engine ever traverses a spec fold. *)
  Module CopySites.
    Import OrchardCompletenessTables.
    Import OrchardAdviceMerkleSinsemilla.
    Import OrchardForwardSinsemilla.

    (** The two note-commitment blinding legs' sums. *)
    Lemma t_nco_pt_shape (w : HonestInput) :
      t_nco_pt (tables_of w) =
      EccSpec.point_add (leg_pt (t_nco_leg (tables_of w)) 84%nat)
        (leg_acc (t_nco_leg (tables_of w)) 83%nat).
    Proof. reflexivity. Qed.

    Lemma t_ncn_pt_shape (w : HonestInput) :
      t_ncn_pt (tables_of w) =
      EccSpec.point_add (leg_pt (t_ncn_leg (tables_of w)) 84%nat)
        (leg_acc (t_ncn_leg (tables_of w)) 83%nat).
    Proof. reflexivity. Qed.

    (** ** The Merkle chain

        The [NodePosition] row of a layer carries the running node, the
        layer's hash region starts at the domain point and ends at the next
        running node, and the chain starts at the old note commitment. *)

    Definition node_col (second : bool) : Advice.t :=
      if second then Advice.A5 else Advice.A0.

    Lemma merkle_node_read (w : HonestInput)
        (layer : RegionId.Merkle.Layer.t) (col : Advice.t)
        (Hcol : col = node_col (layer_second layer)) :
      (Γw w).(Assignment.advice) col
        (RegionId.Merkle layer RegionId.Merkle.Region.NodePosition) 0 =
      merkle_node w (Z.to_nat (RegionId.Merkle.Layer.to_index layer)).
    Proof.
      subst col.
      assert (Hshape :
        (Γw w).(Assignment.advice) (node_col (layer_second layer))
          (RegionId.Merkle layer RegionId.Merkle.Region.NodePosition) 0 =
        lyd_node (List.nth (Z.to_nat (RegionId.Merkle.Layer.to_index layer))
          (t_layers (tables_of w)) layer0))
        by (destruct layer; reflexivity).
      rewrite Hshape.
      rewrite (t_layers_nth w _ (layer_index_lt layer)).
      reflexivity.
    Qed.

    Lemma merkle_h2p_init (w : HonestInput)
        (layer : RegionId.Merkle.Layer.t) (col : Advice.t)
        (Hcol : col = xa_col (layer_second layer)) :
      (Γw w).(Assignment.advice) col
        (RegionId.Merkle layer RegionId.Merkle.Region.HashToPoint) 0 =
      Point.x merkle_Q.
    Proof.
      subst col.
      change (RegionId.Merkle layer RegionId.Merkle.Region.HashToPoint)
        with (merkle_h2p layer).
      rewrite merkle_hash_adv.
      change 0 with (Z.of_nat 0%nat).
      rewrite (hash_cell_xa merkle_Q _ (layer_second layer) 0%nat
        (Nat.le_0_l _)).
      rewrite sinsemilla_acc_zero.
      reflexivity.
    Qed.

    Lemma merkle_h2p_out (w : HonestInput)
        (layer : RegionId.Merkle.Layer.t) (col : Advice.t)
        (Hcol : col = xa_col (layer_second layer)) :
      (Γw w).(Assignment.advice) col
        (RegionId.Merkle layer RegionId.Merkle.Region.HashToPoint) 52 =
      merkle_node w (S (Z.to_nat (RegionId.Merkle.Layer.to_index layer))).
    Proof.
      subst col.
      pose proof (merkle_hash_len w
        (Z.to_nat (RegionId.Merkle.Layer.to_index layer))) as Hlen.
      change (RegionId.Merkle layer RegionId.Merkle.Region.HashToPoint)
        with (merkle_h2p layer).
      rewrite merkle_hash_adv.
      change 52 with (Z.of_nat 52%nat).
      rewrite (hash_cell_xa merkle_Q _ (layer_second layer) 52%nat
        ltac:(rewrite Hlen; lia)).
      rewrite <- Hlen.
      rewrite sinsemilla_acc_full.
      rewrite merkle_words_concat.
      rewrite (merkle_node_succ w _ (layer_index_lt layer)).
      rewrite merkle_layer_words_spec.
      reflexivity.
    Qed.

    Lemma merkle_node_zero (w : HonestInput) :
      merkle_node w 0%nat = Point.x (t_cm_old (tables_of w)).
    Proof. rewrite t_cm_old_of. reflexivity. Qed.

    Lemma cmold_read (w : HonestInput) :
      (Γw w).(Assignment.advice) Advice.A0
        (RegionId.WitnessInput RegionId.WitnessInput.CmOld) 0 =
      Point.x (t_cm_old (tables_of w)).
    Proof. reflexivity. Qed.
  End CopySites.

  Import CopySites.

  (** The head of a witness-fact goal: the two cell addresses, with the
      advice dispatch left folded. *)
  Ltac wf_head :=
    cbn [interpret_fact eval_cell Cell.column Cell.region Cell.row_offset].

  (** The advice dispatch at the two cell addresses, reduced with the
      hoisted record held opaque: both sides become the same stuck
      projection of [tables_of w]. *)
  Ltac wf_fact :=
    wf_head;
    cbn [Assignment.advice Assignment.instance_
         OrchardHonestAssignment.honest_assignment];
    cbn; reflexivity.

  (** The blinding legs' final complete additions: the second summand of the
      commitment region is the leg sum the last window row emits. *)
  Ltac wf_shape :=
    wf_head;
    cbn [Assignment.advice OrchardHonestAssignment.honest_assignment
         OrchardCompletenessTables.advice_t];
    rewrite ?t_nco_pt_shape, ?t_ncn_pt_shape;
    cbn [OrchardAdviceEccMuls.cadd_advice Z.eqb Pos.eqb];
    reflexivity.

  (** The initial accumulator abscissa of a Merkle hash region is the
      domain point's. *)
  Ltac wf_minit :=
    wf_head; rewrite merkle_h2p_init by reflexivity; vm_compute; reflexivity.

  (** The running node of a layer is the previous layer's hash output (and,
      at the first layer, the old note commitment). *)
  Ltac wf_mnode :=
    wf_head;
    rewrite merkle_node_read by reflexivity;
    first
      [ rewrite merkle_h2p_out by reflexivity; reflexivity
      | rewrite merkle_node_zero, cmold_read; reflexivity ].

  Lemma facts_app_intro (Gamma : Assignment.t columns RegionId.t)
      (l1 l2 : list (Fact.t columns RegionId.t)) :
    interpret_facts Gamma l1 -> interpret_facts Gamma l2 ->
    interpret_facts Gamma (l1 ++ l2).
  Proof. intros H1 H2. apply interpret_facts_app. split; assumption. Qed.

  Lemma wf_mnode_0_ok (w : HonestInput) (Hv : valid w)
      (Hnd : nondegenerate w) : interpret_facts (Γw w) wf_mnode_0.
  Proof.
    unfold wf_mnode_0; cbn [interpret_facts]; repeat apply conj;
      first [ exact I | wf_mnode ].
  Qed.

  Lemma wf_mech_0_ok (w : HonestInput) (Hv : valid w)
      (Hnd : nondegenerate w) : interpret_facts (Γw w) wf_mech_0.
  Proof.
    unfold wf_mech_0; cbn [interpret_facts]; repeat apply conj;
      first [ exact I | wf_fact ].
  Qed.

  Lemma wf_mech_1_ok (w : HonestInput) (Hv : valid w)
      (Hnd : nondegenerate w) : interpret_facts (Γw w) wf_mech_1.
  Proof.
    unfold wf_mech_1; cbn [interpret_facts]; repeat apply conj;
      first [ exact I | wf_fact ].
  Qed.

  Lemma wf_mech_2_ok (w : HonestInput) (Hv : valid w)
      (Hnd : nondegenerate w) : interpret_facts (Γw w) wf_mech_2.
  Proof.
    unfold wf_mech_2; cbn [interpret_facts]; repeat apply conj;
      first [ exact I | wf_fact ].
  Qed.

  Lemma wf_mech_3_ok (w : HonestInput) (Hv : valid w)
      (Hnd : nondegenerate w) : interpret_facts (Γw w) wf_mech_3.
  Proof.
    unfold wf_mech_3; cbn [interpret_facts]; repeat apply conj;
      first [ exact I | wf_fact ].
  Qed.

  Lemma wf_mech_4_ok (w : HonestInput) (Hv : valid w)
      (Hnd : nondegenerate w) : interpret_facts (Γw w) wf_mech_4.
  Proof.
    unfold wf_mech_4; cbn [interpret_facts]; repeat apply conj;
      first [ exact I | wf_fact ].
  Qed.

  Lemma wf_mech_5_ok (w : HonestInput) (Hv : valid w)
      (Hnd : nondegenerate w) : interpret_facts (Γw w) wf_mech_5.
  Proof.
    unfold wf_mech_5; cbn [interpret_facts]; repeat apply conj;
      first [ exact I | wf_fact ].
  Qed.

  Lemma wf_mech_6_ok (w : HonestInput) (Hv : valid w)
      (Hnd : nondegenerate w) : interpret_facts (Γw w) wf_mech_6.
  Proof.
    unfold wf_mech_6; cbn [interpret_facts]; repeat apply conj;
      first [ exact I | wf_fact ].
  Qed.

  Lemma wf_mech_7_ok (w : HonestInput) (Hv : valid w)
      (Hnd : nondegenerate w) : interpret_facts (Γw w) wf_mech_7.
  Proof.
    unfold wf_mech_7; cbn [interpret_facts]; repeat apply conj;
      first [ exact I | wf_fact ].
  Qed.

  Lemma wf_mech_8_ok (w : HonestInput) (Hv : valid w)
      (Hnd : nondegenerate w) : interpret_facts (Γw w) wf_mech_8.
  Proof.
    unfold wf_mech_8; cbn [interpret_facts]; repeat apply conj;
      first [ exact I | wf_fact ].
  Qed.

  Lemma wf_mech_9_ok (w : HonestInput) (Hv : valid w)
      (Hnd : nondegenerate w) : interpret_facts (Γw w) wf_mech_9.
  Proof.
    unfold wf_mech_9; cbn [interpret_facts]; repeat apply conj;
      first [ exact I | wf_fact ].
  Qed.

  Lemma wf_mech_10_ok (w : HonestInput) (Hv : valid w)
      (Hnd : nondegenerate w) : interpret_facts (Γw w) wf_mech_10.
  Proof.
    unfold wf_mech_10; cbn [interpret_facts]; repeat apply conj;
      first [ exact I | wf_fact ].
  Qed.

  Lemma wf_mech_11_ok (w : HonestInput) (Hv : valid w)
      (Hnd : nondegenerate w) : interpret_facts (Γw w) wf_mech_11.
  Proof.
    unfold wf_mech_11; cbn [interpret_facts]; repeat apply conj;
      first [ exact I | wf_fact ].
  Qed.

  Lemma wf_mech_12_ok (w : HonestInput) (Hv : valid w)
      (Hnd : nondegenerate w) : interpret_facts (Γw w) wf_mech_12.
  Proof.
    unfold wf_mech_12; cbn [interpret_facts]; repeat apply conj;
      first [ exact I | wf_fact ].
  Qed.

  Lemma wf_mech_13_ok (w : HonestInput) (Hv : valid w)
      (Hnd : nondegenerate w) : interpret_facts (Γw w) wf_mech_13.
  Proof.
    unfold wf_mech_13; cbn [interpret_facts]; repeat apply conj;
      first [ exact I | wf_fact ].
  Qed.

  Lemma wf_mech_14_ok (w : HonestInput) (Hv : valid w)
      (Hnd : nondegenerate w) : interpret_facts (Γw w) wf_mech_14.
  Proof.
    unfold wf_mech_14; cbn [interpret_facts]; repeat apply conj;
      first [ exact I | wf_fact ].
  Qed.

  Lemma wf_mech_15_ok (w : HonestInput) (Hv : valid w)
      (Hnd : nondegenerate w) : interpret_facts (Γw w) wf_mech_15.
  Proof.
    unfold wf_mech_15; cbn [interpret_facts]; repeat apply conj;
      first [ exact I | wf_fact ].
  Qed.

  Lemma wf_minit_0_ok (w : HonestInput) (Hv : valid w)
      (Hnd : nondegenerate w) : interpret_facts (Γw w) wf_minit_0.
  Proof.
    unfold wf_minit_0; cbn [interpret_facts]; repeat apply conj;
      first [ exact I | wf_minit ].
  Qed.

  Lemma wf_shape_0_ok (w : HonestInput) (Hv : valid w)
      (Hnd : nondegenerate w) : interpret_facts (Γw w) wf_shape_0.
  Proof.
    unfold wf_shape_0; cbn [interpret_facts]; repeat apply conj;
      first [ exact I | wf_shape ].
  Qed.

  Lemma nt_closed_ok (w : HonestInput) (Hv : valid w)
      (Hnd : nondegenerate w) : interpret_facts (Γw w) nt_closed.
  Proof.
    unfold nt_closed.
    repeat apply facts_app_intro;
      first
        [ exact (wf_mnode_0_ok w Hv Hnd)
        | exact (wf_mech_0_ok w Hv Hnd)
        | exact (wf_mech_1_ok w Hv Hnd)
        | exact (wf_mech_2_ok w Hv Hnd)
        | exact (wf_mech_3_ok w Hv Hnd)
        | exact (wf_mech_4_ok w Hv Hnd)
        | exact (wf_mech_5_ok w Hv Hnd)
        | exact (wf_mech_6_ok w Hv Hnd)
        | exact (wf_mech_7_ok w Hv Hnd)
        | exact (wf_mech_8_ok w Hv Hnd)
        | exact (wf_mech_9_ok w Hv Hnd)
        | exact (wf_mech_10_ok w Hv Hnd)
        | exact (wf_mech_11_ok w Hv Hnd)
        | exact (wf_mech_12_ok w Hv Hnd)
        | exact (wf_mech_13_ok w Hv Hnd)
        | exact (wf_mech_14_ok w Hv Hnd)
        | exact (wf_mech_15_ok w Hv Hnd)
        | exact (wf_minit_0_ok w Hv Hnd)
        | exact (wf_shape_0_ok w Hv Hnd) ].
  Qed.

  (** The open residue: the facts whose two sides are distinct
      derivations of one value. *)
  Lemma open_witness_facts (w : HonestInput) (Hv : valid w)
      (Hnd : nondegenerate w) : interpret_facts (Γw w) nt_open.
  Proof.
    unfold nt_open.
    repeat apply facts_app_intro.
    - exact (OrchardWitnessBitsColumn.orchardwitnessbitscolumn_ok w Hv Hnd).
    - exact (OrchardWitnessChainOutputs.orchardwitnesschainoutputs_ok w Hv Hnd).
    - exact (OrchardWitnessSliceBounds.orchardwitnessslicebounds_ok w Hv Hnd).
    - exact (OrchardWitnessFixedLegs.orchardwitnessfixedlegs_ok w Hv Hnd).
    - exact (OrchardWitnessVarBase.orchardwitnessvarbase_ok w Hv Hnd).
  Qed.

  Lemma nontrivial_witness_facts :
    forall w : HonestInput,
      valid w -> nondegenerate w ->
      forall fact : Fact.t columns RegionId.t,
        List.In fact (Complete.witness_facts facts) ->
        fact_trivial fact = false ->
        interpret_fact (Γw w) fact.
  Proof.
    intros w Hv Hnd fact Hin Htriv.
    assert (Hsplit : List.In fact (nt_closed ++ nt_open)).
    { apply in_of_beq.
      apply (proj1 (List.forallb_forall
        (fun f => List.existsb (fact_beq f) (nt_closed ++ nt_open))
        (List.filter (fun f => negb (fact_trivial f))
          (Complete.witness_facts facts))) nt_cover).
      apply List.filter_In.
      split; [exact Hin | rewrite Htriv; reflexivity]. }
    apply List.in_app_or in Hsplit.
    destruct Hsplit as [Hc | Ho].
    - exact (interpret_facts_In (Γw w) fact nt_closed
        (nt_closed_ok w Hv Hnd) Hc).
    - exact (interpret_facts_In (Γw w) fact nt_open
        (open_witness_facts w Hv Hnd) Ho).
  Qed.

  (** ** The witness-fact obligation *)

  Theorem witness_facts_ok : witness_facts_forward_ok.
  Proof.
    intros w Hv Hnd.
    apply Complete.interpret_facts_forall.
    intros fact Hin.
    destruct (fact_trivial fact) eqn:Htriv.
    - exact (fact_trivial_sound _ fact Htriv).
    - exact (nontrivial_witness_facts w Hv Hnd fact Hin Htriv).
  Qed.

End OrchardForwardLookupsWitness.
