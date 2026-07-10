Require Import Garden.Halo2.main.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.lemmas.
Require Import Garden.Orchard.columns.
Require Garden.Orchard.circuit.
Require Import Garden.Orchard.circuit_proof.facts.
Require Garden.Halo2.halo2_gadgets.sinsemilla.chip.
Require Garden.Halo2.halo2_gadgets.sinsemilla.chip_proof.
Require Import Garden.Halo2.halo2_gadgets.sinsemilla.chip_proof.
Require Import Garden.Halo2.halo2_gadgets.sinsemilla.hash_to_point_proof.
Require Import Garden.Halo2.halo2_gadgets.sinsemilla.hash_to_point_fold_proof.
Require Import Garden.Halo2.halo2_gadgets.sinsemilla.spec.
Require Import Garden.Halo2.halo2_gadgets.sinsemilla.merkle.chip_proof.
Require Import Garden.Halo2.halo2_gadgets.utilities.cond_swap_proof.
Require Import Garden.Halo2.halo2_gadgets.utilities_proof.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.spec.
Require Import Garden.Orchard.circuit_spec.
Require Import Garden.Field.Field.
Require Import Garden.Field.Lemmas.
Require Import Garden.Plonky3.M.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Lists.List.

#[local] Existing Instance Primes.PallasPIsPrime.

Global Open Scope Z_scope.

(* Lookup-carrying holds: the generator-table synthesis facts and
   the two per-variant generator-table lookup extractors, aligned to the
   table-row bound actually produced by [Garden.Orchard.circuit.synthesize].
   These are the inputs the Sinsemilla hash-to-point round and fold theorems
   ([hash_to_point_round_proof.v] / [hash_to_point_fold_proof.v]) need to
   invoke [GeneratorTable.sound] at any row of the Orchard circuit. *)
Module OrchardActionMerkle.
  Include OrchardActionFacts.

  Local Notation Holds Γ :=
    (circuit_holds Γ
      Garden.Orchard.circuit.synthesize
      (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)).

  (* The synthesis facts of loading the Sinsemilla generator table —
     [load_generator_table] is the first bind of [Garden.Orchard.circuit.synthesize],
     so a single [bind_left] extracts it. *)
  Lemma generator_table_facts
      (Γ : Assignment.t columns RegionId.t) :
    Holds Γ ->
    interpret_facts Γ (layouter_facts
      Garden.Halo2.halo2_gadgets.sinsemilla.chip.load_generator_table).
  Proof.
    intros Hcircuit.
    pose proof (holds_facts Γ Hcircuit) as Hfacts.
    unfold Garden.Orchard.circuit.synthesize in Hfacts.
    apply interpret_layouter_facts_bind_left in Hfacts.
    exact Hfacts.
  Qed.

  (* Table-rows alignment: [load_generator_table] is the only
     [InitLookupTables] call reachable from [synthesize] (the configure-time
     [CreateLookup]s do not contribute to [layouter_table_rows], which reads
     off the layouter-level table loads only), so the table-row bound produced
     by running the whole circuit equals the one baked into
     [GeneratorTable.table_rows]. This is what lets [holds_lookups] (stated at
     [layouter_table_rows synthesize]) feed [GeneratorTable.sound] (stated at
     [GeneratorTable.table_rows]) without a further hypothesis. *)
  Lemma orchard_table_rows_eq :
    layouter_table_rows Garden.Orchard.circuit.synthesize =
      Garden.Halo2.halo2_gadgets.sinsemilla.chip_proof.GeneratorTable.table_rows.
  Proof.
    unfold Garden.Halo2.halo2_gadgets.sinsemilla.chip_proof.GeneratorTable.table_rows.
    unfold Garden.Orchard.circuit.synthesize.
    vm_compute.
    reflexivity.
  Qed.

  (* Generic per-row lookup extractor: from [satisfies_lookups] plus
     membership of a concrete lookup argument in the constraint system's
     lookup list, the argument holds at every [(region, row)] — the
     lookup-side counterpart of [satisfies_gates_at] (Halo2/proof.v). *)
  Lemma satisfies_lookups_at
      (assignment : Assignment.t columns RegionId.t)
      (nb_table_rows : Z)
      (system : ConstraintSystem.t columns)
      (arg : LookupArgument.t columns)
      (region : RegionId.t) (row : Z)
      (Hin : List.In arg system.(ConstraintSystem.lookups))
      (Hsatisfies : satisfies_lookups assignment nb_table_rows system) :
    eval_lookup_argument assignment (region, row) nb_table_rows arg.
  Proof.
    specialize (Hsatisfies region row).
    rewrite List.Forall_forall in Hsatisfies.
    exact (Hsatisfies arg Hin).
  Qed.

  (* The generator-table lookup argument of Sinsemilla variant 1 (the columns
     used by [chip.configure_1]: [x_a := A0], [x_p := A1], [bits := A2],
     [lambda_1 := A3], [lambda_2 := A4]) holds at every [(region, row)] of any
     satisfying assignment, at the table-row bound [GeneratorTable.table_rows]. *)
  Lemma generator_table_lookup_holds_1
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ)
      (region : RegionId.t) (row : Z) :
    eval_lookup_argument Γ (region, row)
      Garden.Halo2.halo2_gadgets.sinsemilla.chip_proof.GeneratorTable.table_rows
      (Garden.Halo2.halo2_gadgets.sinsemilla.chip.generator_table_argument
        Selector.QSinsemilla1_1 Fixed.QSinsemilla2_1
        Advice.A0 Advice.A1 Advice.A2 Advice.A3 Advice.A4).
  Proof.
    rewrite <- orchard_table_rows_eq.
    apply
      (satisfies_lookups_at Γ
        (layouter_table_rows Garden.Orchard.circuit.synthesize)
        orchard_constraint_system
        (Garden.Halo2.halo2_gadgets.sinsemilla.chip.generator_table_argument
          Selector.QSinsemilla1_1 Fixed.QSinsemilla2_1
          Advice.A0 Advice.A1 Advice.A2 Advice.A3 Advice.A4)
        region row).
    - unfold orchard_constraint_system.
      cbn.
      repeat (first [left; reflexivity | right]).
    - exact (holds_lookups Γ Hcircuit).
  Qed.

  (* Same, for Sinsemilla variant 2 ([chip.configure_2]'s columns:
     [x_a := A5], [x_p := A6], [bits := A7], [lambda_1 := A8], [lambda_2 := A9]). *)
  Lemma generator_table_lookup_holds_2
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ)
      (region : RegionId.t) (row : Z) :
    eval_lookup_argument Γ (region, row)
      Garden.Halo2.halo2_gadgets.sinsemilla.chip_proof.GeneratorTable.table_rows
      (Garden.Halo2.halo2_gadgets.sinsemilla.chip.generator_table_argument
        Selector.QSinsemilla1_2 Fixed.QSinsemilla2_2
        Advice.A5 Advice.A6 Advice.A7 Advice.A8 Advice.A9).
  Proof.
    rewrite <- orchard_table_rows_eq.
    apply
      (satisfies_lookups_at Γ
        (layouter_table_rows Garden.Orchard.circuit.synthesize)
        orchard_constraint_system
        (Garden.Halo2.halo2_gadgets.sinsemilla.chip.generator_table_argument
          Selector.QSinsemilla1_2 Fixed.QSinsemilla2_2
          Advice.A5 Advice.A6 Advice.A7 Advice.A8 Advice.A9)
        region row).
    - unfold orchard_constraint_system.
      cbn.
      repeat (first [left; reflexivity | right]).
    - exact (holds_lookups Γ Hcircuit).
  Qed.

  (** * Per-layer Merkle CRH correctness

      The hash-to-point output cell of [synthesize_merkle_hash_layer_{1,2}]
      equals [SinsemillaSpec.merkle_layer] of the cond-swapped node/sibling
      pair.  Structure: pure list/[Z] helpers, the per-row evaluation lemmas
      (running-sum word slices, [q_s3]), fact extractors for the row
      schedules, then the column-generic core [merkle_hash_layer_core] and
      the two per-variant wrappers dispatched on [layer <? 16]. *)

  (** [digit_sum] of an append: the tail is shifted by the head's width.
      Alias of [SinsemillaHash.digit_sum_app] for files importing this
      module. *)
  Definition digit_sum_app := SinsemillaHash.digit_sum_app.

  Lemma map_seq_shift {A : Type} (f : nat -> A) (a n : nat) :
    List.map f (List.seq a n) = List.map (fun j => f (a + j)%nat) (List.seq 0 n).
  Proof.
    induction a as [| a IH] in f |- *.
    - apply List.map_ext. intros j. f_equal.
    - rewrite <- List.seq_shift, List.map_map.
      rewrite (IH (fun j => f (S j))).
      apply List.map_ext. intros j. f_equal.
  Qed.

  (** Splitting an offset-indexed word map into two consecutive runs. *)
  Lemma map_z_seq_split (f : Z -> Z) (offset : Z) (n m : nat) :
    List.map (fun j : nat => f (offset + Z.of_nat j)) (List.seq 0 (n + m)) =
    List.map (fun j : nat => f (offset + Z.of_nat j)) (List.seq 0 n) ++
    List.map (fun j : nat => f (offset + Z.of_nat n + Z.of_nat j)) (List.seq 0 m).
  Proof.
    rewrite List.seq_app, List.map_app.
    f_equal.
    cbn [Nat.add].
    rewrite (map_seq_shift (fun j : nat => f (offset + Z.of_nat j)) n m).
    apply List.map_ext. intros j. f_equal. lia.
  Qed.

  (** On a [q_s2 = 1] row, the evaluated [generator_table_word] definition
      rearranges into the running-sum step equation: the current running-sum
      cell is the row word plus the shifted next cell. *)
  Lemma word_at_step {RegionId : Set} (Γ : Assignment.t columns RegionId)
      (q2 : Fixed.t) (bits : Advice.t) (region : RegionId) (row : Z)
      (Hfix : Γ.(Assignment.fixed) q2 region row = 1) :
    Γ ⊢ ⟦ Expression.Advice bits Rotation.cur ⟧ (region, row) =
      SinsemillaHash.word_at Γ q2 bits region row +F
        (UnOp.from (2 ^ 10) *F
          (Γ ⊢ ⟦ Expression.Advice bits Rotation.cur ⟧ (region, row + 1))).
  Proof.
    unfold SinsemillaHash.word_at,
      Garden.Halo2.halo2_gadgets.sinsemilla.chip.generator_table_word,
      Garden.Halo2.halo2_gadgets.sinsemilla.chip.q_s3.
    with_strategy opaque [BinOp.add BinOp.sub BinOp.mul UnOp.from] cbn.
    assert (Hrow : rotated_row row Rotation.cur = row)
      by (unfold rotated_row; cbn; lia).
    assert (Hrow2 :
        rotated_row (row + 1) Rotation.cur = rotated_row row Rotation.next)
      by (unfold rotated_row; cbn; lia).
    rewrite Hrow, Hrow2, Hfix.
    set (z := UnOp.from (Γ.(Assignment.advice) bits region row)).
    set (z' := UnOp.from
      (Γ.(Assignment.advice) bits region (rotated_row row Rotation.next))).
    assert (Hz : UnOp.from z = z) by (apply FieldRewrite.from_from).
    assert (Hz' : UnOp.from z' = z') by (apply FieldRewrite.from_from).
    field_solve.
  Qed.

  (** On a [q_s2 ∈ {0, 2}] row the running flag [q_run = q_s2 - q_s3]
      vanishes, so the row word is the running-sum cell itself. *)
  Lemma word_at_last {RegionId : Set} (Γ : Assignment.t columns RegionId)
      (q2 : Fixed.t) (bits : Advice.t) (region : RegionId) (row : Z) (v : Z)
      (Hfix : Γ.(Assignment.fixed) q2 region row = v)
      (Hv : v = 0 \/ v = 2) :
    Γ ⊢ ⟦ Expression.Advice bits Rotation.cur ⟧ (region, row) =
      SinsemillaHash.word_at Γ q2 bits region row.
  Proof.
    unfold SinsemillaHash.word_at,
      Garden.Halo2.halo2_gadgets.sinsemilla.chip.generator_table_word,
      Garden.Halo2.halo2_gadgets.sinsemilla.chip.q_s3.
    with_strategy opaque [BinOp.add BinOp.sub BinOp.mul UnOp.from] cbn.
    assert (Hrow : rotated_row row Rotation.cur = row)
      by (unfold rotated_row; cbn; lia).
    rewrite Hrow, Hfix.
    set (z := UnOp.from (Γ.(Assignment.advice) bits region row)).
    set (z' := UnOp.from
      (Γ.(Assignment.advice) bits region (rotated_row row Rotation.next))).
    assert (Hz : UnOp.from z = z) by (apply FieldRewrite.from_from).
    assert (Hz' : UnOp.from z' = z') by (apply FieldRewrite.from_from).
    destruct Hv as [Hv | Hv]; subst v; field_solve.
  Qed.

  (** [q_s3 = q_s2 (q_s2 - 1)] evaluations at the scheduled fixed values. *)
  Lemma q_s3_eval_zero {RegionId : Set} (Γ : Assignment.t columns RegionId)
      (q2 : Fixed.t) (region : RegionId) (row : Z) (v : Z)
      (Hfix : Γ.(Assignment.fixed) q2 region row = v)
      (Hv : v = 0 \/ v = 1) :
    Γ ⊢ ⟦ Garden.Halo2.halo2_gadgets.sinsemilla.chip.q_s3 q2 ⟧ (region, row) = 0.
  Proof.
    unfold Garden.Halo2.halo2_gadgets.sinsemilla.chip.q_s3.
    with_strategy opaque [BinOp.add BinOp.sub BinOp.mul UnOp.from] cbn.
    assert (Hrow : rotated_row row Rotation.cur = row)
      by (unfold rotated_row; cbn; lia).
    rewrite Hrow, Hfix.
    clear Hfix.
    destruct Hv as [Hv | Hv]; subst v; field_solve.
  Qed.

  Lemma q_s3_eval_two {RegionId : Set} (Γ : Assignment.t columns RegionId)
      (q2 : Fixed.t) (region : RegionId) (row : Z)
      (Hfix : Γ.(Assignment.fixed) q2 region row = 2) :
    Γ ⊢ ⟦ Garden.Halo2.halo2_gadgets.sinsemilla.chip.q_s3 q2 ⟧ (region, row) = 2.
  Proof.
    unfold Garden.Halo2.halo2_gadgets.sinsemilla.chip.q_s3.
    with_strategy opaque [BinOp.add BinOp.sub BinOp.mul UnOp.from] cbn.
    assert (Hrow : rotated_row row Rotation.cur = row)
      by (unfold rotated_row; cbn; lia).
    rewrite Hrow, Hfix.
    field_solve.
  Qed.

  (** The generator-table lookup bounds every row word to ten bits. *)
  Lemma word_at_bound
      (Γ : Assignment.t columns RegionId.t) (region : RegionId.t) (row : Z)
      (q_sinsemilla1 : Selector.t) (q_sinsemilla2 : Fixed.t)
      (x_a x_p bits lambda_1 lambda_2 : Advice.t)
      (Hload :
        interpret_facts Γ (layouter_facts
          Garden.Halo2.halo2_gadgets.sinsemilla.chip.load_generator_table))
      (Hactive : Γ ⊢ ⟦ Expression.Selector q_sinsemilla1 ⟧ (region, row) = 1)
      (Hlookup :
        eval_lookup_argument Γ (region, row) GeneratorTable.table_rows
          (Garden.Halo2.halo2_gadgets.sinsemilla.chip.generator_table_argument
            q_sinsemilla1 q_sinsemilla2 x_a x_p bits lambda_1 lambda_2)) :
    0 <= SinsemillaHash.word_at Γ q_sinsemilla2 bits region row < 2 ^ 10.
  Proof.
    pose proof (GeneratorTable.sound Γ region row q_sinsemilla1 q_sinsemilla2
        x_a x_p bits lambda_1 lambda_2 Hload Hactive Hlookup)
      as (w & Hw & Hword & _ & _).
    unfold SinsemillaHash.word_at.
    rewrite Hword.
    exact Hw.
  Qed.

  (** Boolean decode of the cond-swap [ternary] outputs. *)
  Lemma cond_swap_output_if (a b swap : Z) (Hbool : IsBool.t swap) :
    CondSwap.output a b swap =
      {| CondSwap.a_swapped := UnOp.from (if swap =? 1 then b else a);
         CondSwap.b_swapped := UnOp.from (if swap =? 1 then a else b); |}.
  Proof.
    cbn in Hbool.
    assert (Hcase : swap = 0 \/ swap = 1)
      by (destruct (Z.odd swap); cbn in Hbool; lia).
    unfold CondSwap.output, Garden.Halo2.halo2_gadgets.utilities_proof.ternary.
    clear Hbool.
    destruct Hcase as [Hs | Hs]; subst swap; cbn [Z.eqb].
    all: cbn [Pos.eqb]; f_equal; field_solve.
  Qed.

  (** Fact extractors for the hash region's row schedules. *)
  Lemma enable_selector_rows_fact
      (region : RegionId.t) (selector : Selector.t) (offset : Z) (count i : nat) :
    (i < count)%nat ->
    List.In
      (Fact.SelectorOn selector region (offset + Z.of_nat i))
      (region_facts region
        (Garden.Halo2.halo2_gadgets.sinsemilla.chip.enable_selector_rows
          selector offset count)).
  Proof.
    revert offset i.
    induction count as [| count IH]; intros offset i Hi.
    - lia.
    - destruct i as [| i].
      + cbn [Garden.Halo2.halo2_gadgets.sinsemilla.chip.enable_selector_rows
          region_facts].
        left. f_equal. lia.
      + cbn [Garden.Halo2.halo2_gadgets.sinsemilla.chip.enable_selector_rows
          region_facts].
        right.
        replace (offset + Z.of_nat (S i)) with (offset + 1 + Z.of_nat i) by lia.
        apply IH. lia.
  Qed.

  Lemma assign_q_s2_rows_fact_step
      (region : RegionId.t) (q2 : Fixed.t) (offset : Z) (count i : nat)
      (final : bool) :
    (S i < count)%nat ->
    List.In
      (Fact.FixedIs q2 region (offset + Z.of_nat i) 1)
      (region_facts region
        (Garden.Halo2.halo2_gadgets.sinsemilla.chip.assign_q_s2_rows
          q2 offset count final)).
  Proof.
    revert offset i.
    induction count as [| count IH]; intros offset i Hi.
    - lia.
    - destruct count as [| count]; [lia |].
      destruct i as [| i].
      + cbn [Garden.Halo2.halo2_gadgets.sinsemilla.chip.assign_q_s2_rows
          region_facts].
        left. f_equal. lia.
      + cbn [Garden.Halo2.halo2_gadgets.sinsemilla.chip.assign_q_s2_rows
          region_facts].
        right.
        replace (offset + Z.of_nat (S i)) with (offset + 1 + Z.of_nat i) by lia.
        apply IH. lia.
  Qed.

  Lemma assign_q_s2_rows_fact_last
      (region : RegionId.t) (q2 : Fixed.t) (offset : Z) (count : nat)
      (final : bool) :
    (0 < count)%nat ->
    List.In
      (Fact.FixedIs q2 region (offset + Z.of_nat (count - 1))
        (if final then 2 else 0))
      (region_facts region
        (Garden.Halo2.halo2_gadgets.sinsemilla.chip.assign_q_s2_rows
          q2 offset count final)).
  Proof.
    revert offset.
    induction count as [| count IH]; intros offset Hcount.
    - lia.
    - destruct count as [| count].
      + cbn [Garden.Halo2.halo2_gadgets.sinsemilla.chip.assign_q_s2_rows
          region_facts].
        left. f_equal. lia.
      + cbn [Garden.Halo2.halo2_gadgets.sinsemilla.chip.assign_q_s2_rows
          region_facts].
        right.
        replace (offset + Z.of_nat (S (S count) - 1))
          with (offset + 1 + Z.of_nat (S count - 1)) by lia.
        apply IH. lia.
  Qed.

  (** The Merkle CRH domain point [Q("MerkleCRH")], as pinned by the
      hash-to-point synthesis constants. *)
  Definition merkle_Q : Point.t := {|
    Point.x := Garden.Orchard.circuit.merkle_q_x;
    Point.y := Garden.Orchard.circuit.merkle_q_y;
  |}.

  (** The column-generic core of the per-layer CRH proof: on a hash region
      [H] carrying the 52-row a/b/c schedule (selector on everywhere; [q_s2]
      one on the running rows, zero on the two inner piece boundaries, two on
      the final row), with the accumulator seeded at [merkle_Q], the
      decomposition-gate record equality routed to the region's running-sum
      cells, and the per-layer canonicity ([Hcanon1..3], no mod-[p] wrap in
      the three reconstruction identities) plus incomplete-add nondegeneracy,
      the output cell [x_a@52] is exactly
      [merkle_crh merkle_Q i left right]. *)
  Lemma merkle_hash_layer_core
      (Γ : Assignment.t columns RegionId.t)
      (q1 : Selector.t) (q2 : Fixed.t)
      (x_a x_p bits lambda_1 lambda_2 : Advice.t)
      (H : RegionId.t)
      (i left right beta1 beta2 : Z)
      (Hi : 0 <= i < 32)
      (Hload : interpret_facts Γ (layouter_facts
        Garden.Halo2.halo2_gadgets.sinsemilla.chip.load_generator_table))
      (Hsel : forall j : nat, (j < 52)%nat ->
        Γ ⊢ ⟦ Expression.Selector q1 ⟧ (H, Z.of_nat j) = 1)
      (Hgate : forall row : Z,
        Γ ⊢ ⟦ Garden.Halo2.halo2_gadgets.sinsemilla.chip.sinsemilla_gate
          q1 q2 x_a x_p lambda_1 lambda_2 ⟧ (H, row))
      (Hlookup : forall row : Z,
        eval_lookup_argument Γ (H, row) GeneratorTable.table_rows
          (Garden.Halo2.halo2_gadgets.sinsemilla.chip.generator_table_argument
            q1 q2 x_a x_p bits lambda_1 lambda_2))
      (Hq2_one : forall j : nat,
        (j < 52)%nat -> j <> 24%nat -> j <> 26%nat -> j <> 51%nat ->
        Γ.(Assignment.fixed) q2 H (Z.of_nat j) = 1)
      (Hq2_24 : Γ.(Assignment.fixed) q2 H 24 = 0)
      (Hq2_26 : Γ.(Assignment.fixed) q2 H 26 = 0)
      (Hq2_51 : Γ.(Assignment.fixed) q2 H 51 = 2)
      (Hacc0 : SinsemillaHash.acc_at Γ x_a x_p lambda_1 lambda_2 H 0 = merkle_Q)
      (Hnondeg : SinsemillaHash.nondegenerate merkle_Q
        (SinsemillaHash.hash_words Γ q2 bits H 52))
      (Hbeta1_red : UnOp.from beta1 = beta1)
      (Hbeta2_red : UnOp.from beta2 = beta2)
      (Hdec :
        {|
          DecompositionCheck.l_whole := UnOp.from i;
          DecompositionCheck.left_node := left;
          DecompositionCheck.right_node := right;
          DecompositionCheck.z1_b :=
            Γ ⊢ ⟦ Expression.Advice bits Rotation.cur ⟧ (H, 26);
        |} =
          DecompositionCheck.output
            (Γ ⊢ ⟦ Expression.Advice bits Rotation.cur ⟧ (H, 0))
            (Γ ⊢ ⟦ Expression.Advice bits Rotation.cur ⟧ (H, 25))
            (Γ ⊢ ⟦ Expression.Advice bits Rotation.cur ⟧ (H, 27))
            (Γ ⊢ ⟦ Expression.Advice bits Rotation.cur ⟧ (H, 1))
            beta1
            beta2)
      (Hcanon1 :
        (Γ ⊢ ⟦ Expression.Advice bits Rotation.cur ⟧ (H, 1)) +
          (SinsemillaHash.word_at Γ q2 bits H 25 + beta1 * 2 ^ 10) * 2 ^ 240
          < Primes.pallas_p)
      (Hcanon2 : beta1 + beta2 * 2 ^ 5 < Primes.pallas_p)
      (Hcanon3 :
        beta2 + (Γ ⊢ ⟦ Expression.Advice bits Rotation.cur ⟧ (H, 27)) * 2 ^ 5
          < Primes.pallas_p) :
    Γ ⊢ ⟦ Expression.Advice x_a Rotation.cur ⟧ (H, 52) =
      SinsemillaSpec.merkle_crh merkle_Q i left right.
  Proof.
    (* Row schedule: [q_s3 = 0] below the final row ([q_s2 ∈ {0, 1}]),
       [q_s3 = 2] on row 51. *)
    assert (Hq3 : forall j : nat, (S j < 52)%nat ->
        Γ ⊢ ⟦ Garden.Halo2.halo2_gadgets.sinsemilla.chip.q_s3 q2 ⟧
          (H, Z.of_nat j) = 0).
    { intros j Hj.
      destruct (Nat.eq_dec j 24) as [-> | Hj24].
      - apply (q_s3_eval_zero Γ q2 H (Z.of_nat 24) 0);
          [exact Hq2_24 | left; reflexivity].
      - destruct (Nat.eq_dec j 26) as [-> | Hj26].
        + apply (q_s3_eval_zero Γ q2 H (Z.of_nat 26) 0);
            [exact Hq2_26 | left; reflexivity].
        + apply (q_s3_eval_zero Γ q2 H (Z.of_nat j) 1);
            [apply Hq2_one; lia | right; reflexivity]. }
    assert (Hq3_final :
        Γ ⊢ ⟦ Garden.Halo2.halo2_gadgets.sinsemilla.chip.q_s3 q2 ⟧
          (H, Z.of_nat (52 - 1)) = 2).
    { apply q_s3_eval_two. exact Hq2_51. }
    (* The 52-round point fold ([SinsemillaHashFold.hash_to_point_rows_correct]). *)
    pose proof (SinsemillaHashFold.hash_to_point_rows_correct Γ H q1 q2
        x_a x_p bits lambda_1 lambda_2 52 ltac:(lia) merkle_Q
        Hload Hsel (fun j _ => Hgate (Z.of_nat j))
        (fun j _ => Hlookup (Z.of_nat j))
        Hq3 Hq3_final Hacc0 Hnondeg) as Hpoint.
    assert (Hbound : forall j : nat, (j < 52)%nat ->
        0 <= SinsemillaHash.word_at Γ q2 bits H (Z.of_nat j) < 2 ^ 10).
    { intros j Hj.
      apply (word_at_bound Γ H (Z.of_nat j) q1 q2 x_a x_p bits lambda_1
        lambda_2 Hload (Hsel j Hj) (Hlookup (Z.of_nat j))). }
    (* The four piece telescopes (a at 0, its z1 tail at 1, b at 25, c at
       27) and the b-piece's z1 cell. *)
    assert (HA : Γ ⊢ ⟦ Expression.Advice bits Rotation.cur ⟧ (H, 0) =
        SinsemillaHash.digit_sum (List.map
          (fun j : nat => SinsemillaHash.word_at Γ q2 bits H (0 + Z.of_nat j))
          (List.seq 0%nat 25%nat))).
    { apply SinsemillaHash.piece_telescope.
      - lia.
      - intros j Hj.
        replace (0 + Z.of_nat j) with (Z.of_nat j) by lia.
        apply word_at_step.
        apply Hq2_one; lia.
      - replace (0 + Z.of_nat (25 - 1)) with (Z.of_nat 24) by lia.
        apply (word_at_last Γ q2 bits H (Z.of_nat 24) 0);
          [exact Hq2_24 | left; reflexivity].
      - intros j Hj.
        replace (0 + Z.of_nat j) with (Z.of_nat j) by lia.
        apply Hbound; lia.
      - lia. }
    assert (HA1 : Γ ⊢ ⟦ Expression.Advice bits Rotation.cur ⟧ (H, 1) =
        SinsemillaHash.digit_sum (List.map
          (fun j : nat => SinsemillaHash.word_at Γ q2 bits H (1 + Z.of_nat j))
          (List.seq 0%nat 24%nat))).
    { apply SinsemillaHash.piece_telescope.
      - lia.
      - intros j Hj.
        replace (1 + Z.of_nat j) with (Z.of_nat (S j)) by lia.
        apply word_at_step.
        apply Hq2_one; lia.
      - replace (1 + Z.of_nat (24 - 1)) with (Z.of_nat 24) by lia.
        apply (word_at_last Γ q2 bits H (Z.of_nat 24) 0);
          [exact Hq2_24 | left; reflexivity].
      - intros j Hj.
        replace (1 + Z.of_nat j) with (Z.of_nat (S j)) by lia.
        apply Hbound; lia.
      - lia. }
    assert (HB : Γ ⊢ ⟦ Expression.Advice bits Rotation.cur ⟧ (H, 25) =
        SinsemillaHash.digit_sum (List.map
          (fun j : nat => SinsemillaHash.word_at Γ q2 bits H (25 + Z.of_nat j))
          (List.seq 0%nat 2%nat))).
    { apply SinsemillaHash.piece_telescope.
      - lia.
      - intros j Hj.
        replace (25 + Z.of_nat j) with (Z.of_nat 25) by lia.
        apply word_at_step.
        apply Hq2_one; lia.
      - replace (25 + Z.of_nat (2 - 1)) with (Z.of_nat 26) by lia.
        apply (word_at_last Γ q2 bits H (Z.of_nat 26) 0);
          [exact Hq2_26 | left; reflexivity].
      - intros j Hj.
        replace (25 + Z.of_nat j) with (Z.of_nat (25 + j)) by lia.
        apply Hbound; lia.
      - lia. }
    assert (HC : Γ ⊢ ⟦ Expression.Advice bits Rotation.cur ⟧ (H, 27) =
        SinsemillaHash.digit_sum (List.map
          (fun j : nat => SinsemillaHash.word_at Γ q2 bits H (27 + Z.of_nat j))
          (List.seq 0%nat 25%nat))).
    { apply SinsemillaHash.piece_telescope.
      - lia.
      - intros j Hj.
        replace (27 + Z.of_nat j) with (Z.of_nat (27 + j)) by lia.
        apply word_at_step.
        apply Hq2_one; lia.
      - replace (27 + Z.of_nat (25 - 1)) with (Z.of_nat 51) by lia.
        apply (word_at_last Γ q2 bits H (Z.of_nat 51) 2);
          [exact Hq2_51 | right; reflexivity].
      - intros j Hj.
        replace (27 + Z.of_nat j) with (Z.of_nat (27 + j)) by lia.
        apply Hbound; lia.
      - lia. }
    assert (HB1 : Γ ⊢ ⟦ Expression.Advice bits Rotation.cur ⟧ (H, 26) =
        SinsemillaHash.word_at Γ q2 bits H 26).
    { apply (word_at_last Γ q2 bits H 26 0);
        [exact Hq2_26 | left; reflexivity]. }
    set (w := SinsemillaHash.word_at Γ q2 bits H) in *.
    set (dsA := SinsemillaHash.digit_sum
      (List.map (fun j : nat => w (0 + Z.of_nat j)) (List.seq 0%nat 25%nat)))
      in *.
    set (dsA1 := SinsemillaHash.digit_sum
      (List.map (fun j : nat => w (1 + Z.of_nat j)) (List.seq 0%nat 24%nat)))
      in *.
    set (dsB := SinsemillaHash.digit_sum
      (List.map (fun j : nat => w (25 + Z.of_nat j)) (List.seq 0%nat 2%nat)))
      in *.
    set (dsC := SinsemillaHash.digit_sum
      (List.map (fun j : nat => w (27 + Z.of_nat j)) (List.seq 0%nat 25%nat)))
      in *.
    (* Structural digit-sum identities and bounds. *)
    assert (HheadA : dsA = w 0 + 2 ^ 10 * dsA1).
    { unfold dsA, w.
      rewrite (SinsemillaHash.digit_sum_words_head Γ q2 bits H 0 24%nat).
      unfold dsA1, w.
      f_equal. }
    assert (HdsB : dsB = w 25 + 2 ^ 10 * w 26).
    { unfold dsB.
      cbn [List.seq List.map SinsemillaHash.digit_sum].
      replace (25 + Z.of_nat 0) with 25 by lia.
      replace (25 + Z.of_nat 1) with 26 by lia.
      lia. }
    assert (HboundA1 : 0 <= dsA1 < 2 ^ 240).
    { unfold dsA1.
      pose proof (SinsemillaHash.digit_sum_bound
        (List.map (fun j : nat => w (1 + Z.of_nat j)) (List.seq 0%nat 24%nat)))
        as Hb.
      rewrite List.length_map, List.length_seq in Hb.
      apply Hb.
      rewrite List.Forall_map, List.Forall_forall.
      intros j Hj. rewrite List.in_seq in Hj.
      replace (1 + Z.of_nat j) with (Z.of_nat (S j)) by lia.
      apply Hbound. lia. }
    assert (HboundC : 0 <= dsC < 2 ^ 250).
    { unfold dsC.
      pose proof (SinsemillaHash.digit_sum_bound
        (List.map (fun j : nat => w (27 + Z.of_nat j)) (List.seq 0%nat 25%nat)))
        as Hb.
      rewrite List.length_map, List.length_seq in Hb.
      apply Hb.
      rewrite List.Forall_map, List.Forall_forall.
      intros j Hj. rewrite List.in_seq in Hj.
      replace (27 + Z.of_nat j) with (Z.of_nat (27 + j)) by lia.
      apply Hbound. lia. }
    assert (Hw0 : 0 <= w 0 < 2 ^ 10) by (apply (Hbound 0%nat); lia).
    assert (Hw25 : 0 <= w 25 < 2 ^ 10) by (apply (Hbound 25%nat); lia).
    assert (Hw26 : 0 <= w 26 < 2 ^ 10) by (apply (Hbound 26%nat); lia).
    (* The decomposition-gate components, one exact integer identity each:
       the canonicity hypotheses remove the mod-[p] wrap. *)
    rewrite HA1 in Hcanon1.
    rewrite HC in Hcanon3.
    pose proof (f_equal DecompositionCheck.l_whole Hdec) as Hl.
    pose proof (f_equal DecompositionCheck.left_node Hdec) as Hleft.
    pose proof (f_equal DecompositionCheck.right_node Hdec) as Hright.
    pose proof (f_equal DecompositionCheck.z1_b Hdec) as Hz1b.
    unfold DecompositionCheck.output in Hl, Hleft, Hright, Hz1b.
    cbn [DecompositionCheck.l_whole DecompositionCheck.left_node
      DecompositionCheck.right_node DecompositionCheck.z1_b]
      in Hl, Hleft, Hright, Hz1b.
    rewrite HA, HA1 in Hl.
    rewrite HA1, HB in Hleft.
    rewrite HC in Hright.
    rewrite HB1 in Hz1b.
    clear Hdec.
    assert (Hp_range :
        0 <= beta1 < Primes.pallas_p /\ 0 <= beta2 < Primes.pallas_p)
      by (clear -Hbeta1_red Hbeta2_red; unfold UnOp.from in *;
          change Primes.pallas_p with
            28948022309329048855892746252171976963363056481941560715954676764349967630337
            in *;
          lia).
    destruct Hp_range as [Hbeta1_range Hbeta2_range].
    assert (Hw26_int : w 26 = beta1 + beta2 * 2 ^ 5)
      by (clear -Hz1b Hcanon2 Hbeta1_range Hbeta2_range Hw26; field_solve).
    assert (Hbeta_small : 0 <= beta1 < 2 ^ 10 /\ 0 <= beta2 < 2 ^ 5)
      by (clear -Hw26_int Hw26 Hbeta1_range Hbeta2_range; lia).
    destruct Hbeta_small as [Hbeta1_small Hbeta2_small].
    assert (Hi_int : i = w 0)
      by (clear -Hl HheadA HboundA1 Hw0 Hi; field_solve).
    assert (Hleft_int : left = dsA1 + (w 25 + beta1 * 2 ^ 10) * 2 ^ 240)
      by (clear -Hleft HdsB Hw26_int Hcanon1 Hw25 Hw26 Hbeta1_small
            Hbeta2_small HboundA1; field_solve).
    assert (Hright_int : right = beta2 + dsC * 2 ^ 5)
      by (clear -Hright Hcanon3 HboundC Hbeta2_small; field_solve).
    (* Message identification: the 52 row words are exactly
       [merkle_message i left right]. *)
    assert (Hsplit : SinsemillaHash.hash_words Γ q2 bits H 52 =
      List.map (fun j : nat => w (0 + Z.of_nat j)) (List.seq 0%nat 25%nat) ++
      List.map (fun j : nat => w (25 + Z.of_nat j)) (List.seq 0%nat 2%nat) ++
      List.map (fun j : nat => w (27 + Z.of_nat j)) (List.seq 0%nat 25%nat)).
    { unfold SinsemillaHash.hash_words.
      transitivity (List.map (fun j : nat => w (0 + Z.of_nat j))
        (List.seq 0%nat (25 + 27)%nat)); [reflexivity |].
      rewrite (map_z_seq_split w 0 25 27).
      f_equal. }
    assert (Hall52 : List.Forall (fun x : Z => 0 <= x < 2 ^ 10)
        (SinsemillaHash.hash_words Γ q2 bits H 52)).
    { unfold SinsemillaHash.hash_words.
      rewrite List.Forall_map, List.Forall_forall.
      intros j Hj. rewrite List.in_seq in Hj.
      apply Hbound. lia. }
    assert (Hpack : i + left * 2 ^ 10 + right * 2 ^ 265 =
      SinsemillaHash.digit_sum (SinsemillaHash.hash_words Γ q2 bits H 52)).
    { rewrite Hsplit.
      rewrite !SinsemillaHash.digit_sum_app.
      rewrite !List.length_map, !List.length_seq.
      replace (10 * Z.of_nat 25) with 250 by lia.
      replace (10 * Z.of_nat 2) with 20 by lia.
      fold dsA dsB dsC.
      clear -Hi_int Hleft_int Hright_int HheadA HdsB Hw26_int HboundA1
        HboundC Hw0 Hw25 Hw26 Hbeta1_small Hbeta2_small.
      lia. }
    assert (Hmsg : SinsemillaSpec.merkle_message i left right =
        SinsemillaHash.hash_words Γ q2 bits H 52).
    { unfold SinsemillaSpec.merkle_message.
      change SinsemillaSpec.sinsemilla_k with 10.
      replace (10 + 255) with 265 by lia.
      rewrite Hpack.
      pose proof (SinsemillaHash.words_le_digit_sum _ Hall52) as Hw52.
      rewrite SinsemillaHash.hash_words_length in Hw52.
      exact Hw52. }
    unfold SinsemillaSpec.merkle_crh, SinsemillaSpec.sinsemilla_hash.
    rewrite Hmsg.
    rewrite <- Hpoint.
    unfold EccSpec.extract_x.
    cbn [Point.x].
    change (Z.of_nat 52) with 52.
    reflexivity.
  Qed.

  (** Layer-region shorthands and the per-layer side condition. *)
  Definition NP (i : Z) : RegionId.t :=
    Garden.Orchard.circuit.merkle_region i RegionId.Merkle.Region.NodePosition.
  Definition HTP (i : Z) : RegionId.t :=
    Garden.Orchard.circuit.merkle_region i RegionId.Merkle.Region.HashToPoint.

  (** Variant dispatch on [layer <? 16]: the running-sum column, the [q_s2]
      fixed column, and the message-piece witness column of the layer. *)
  Definition merkle_bits (i : Z) : Advice.t :=
    if i <? 16 then Advice.A2 else Advice.A7.
  Definition merkle_q2 (i : Z) : Fixed.t :=
    if i <? 16 then Fixed.QSinsemilla2_1 else Fixed.QSinsemilla2_2.
  Definition merkle_witness_col (i : Z) : Advice.t :=
    if i <? 16 then Advice.A6 else Advice.A7.

  (** The 52 message words consumed by layer [i]'s hash-to-point region. *)
  Definition merkle_words (Γ : Assignment.t columns RegionId.t) (i : Z)
      : list Z :=
    SinsemillaHash.hash_words Γ (merkle_q2 i) (merkle_bits i) (HTP i) 52.

  (** Canonicity of layer [i]'s witnessed decomposition: the three
      reconstruction identities of the decomposition gate hold without
      mod-[p] wrap ([left_check] at width 255, [b1_b2_check] at width 10 + a
      free [b_2], [right_check] at width 255).  A dishonest witness may
      satisfy the gate with the wrapped decomposition instead (the gate
      checks mod [p] only, and [2^255 > p]) — that non-canonical branch
      hashes a different 52-word message, which is why the per-layer
      statement is conditional. *)
  Definition merkle_layer_canonical
      (Γ : Assignment.t columns RegionId.t) (i : Z) : Prop :=
    UnOp.from (eval_cell Γ
        (Garden.Halo2.Synthesis.Cell.advice (HTP i) (merkle_bits i) 1)) +
      (SinsemillaHash.word_at Γ (merkle_q2 i) (merkle_bits i) (HTP i) 25 +
        UnOp.from (eval_cell Γ (Garden.Halo2.Synthesis.Cell.advice
          (Garden.Orchard.circuit.merkle_region i
            RegionId.Merkle.Region.RangeB1)
          Advice.A9 0)) * 2 ^ 10) * 2 ^ 240
      < Primes.pallas_p /\
    UnOp.from (eval_cell Γ (Garden.Halo2.Synthesis.Cell.advice
        (Garden.Orchard.circuit.merkle_region i RegionId.Merkle.Region.RangeB1)
        Advice.A9 0)) +
      UnOp.from (eval_cell Γ (Garden.Halo2.Synthesis.Cell.advice
        (Garden.Orchard.circuit.merkle_region i RegionId.Merkle.Region.RangeB2)
        Advice.A9 0)) * 2 ^ 5
      < Primes.pallas_p /\
    UnOp.from (eval_cell Γ (Garden.Halo2.Synthesis.Cell.advice
        (Garden.Orchard.circuit.merkle_region i RegionId.Merkle.Region.RangeB2)
        Advice.A9 0)) +
      UnOp.from (eval_cell Γ (Garden.Halo2.Synthesis.Cell.advice
        (Garden.Orchard.circuit.merkle_region i RegionId.Merkle.Region.WitnessC)
        (merkle_witness_col i) 0)) * 2 ^ 5
      < Primes.pallas_p.

  (** The per-layer side condition: canonical decomposition plus the
      incomplete-add nondegeneracy of the layer's 52-word message. *)
  Definition merkle_layer_ok
      (Γ : Assignment.t columns RegionId.t) (i : Z) : Prop :=
    merkle_layer_canonical Γ i /\
    SinsemillaHash.nondegenerate merkle_Q (merkle_words Γ i).

  Definition merkle_witness_ok (Γ : Assignment.t columns RegionId.t) : Prop :=
    forall i : Z, 0 <= i < 32 -> merkle_layer_ok Γ i.

  Lemma eval_advice_next_cell
      (Γ : Assignment.t columns RegionId.t)
      (region : RegionId.t) (column : Advice.t) (row : Z) :
    Γ ⊢ ⟦ Expression.Advice column Rotation.next ⟧ (region, row) =
      UnOp.from
        (eval_cell Γ
          (Garden.Halo2.Synthesis.Cell.advice region column (row + 1))).
  Proof.
    change (eval_expression Γ (region, row)
      (Expression.Advice column Rotation.next) =
      UnOp.from
        (eval_cell Γ
          (Garden.Halo2.Synthesis.Cell.advice region column (row + 1)))).
    unfold eval_expression, eval_cell, rotated_row, Rotation.next.
    cbn.
    reflexivity.
  Qed.

  Lemma merkle_q_x_reduced :
    UnOp.from Garden.Orchard.circuit.merkle_q_x =
      Garden.Orchard.circuit.merkle_q_x.
  Proof. vm_compute. reflexivity. Qed.

  Lemma merkle_q_y_reduced :
    UnOp.from Garden.Orchard.circuit.merkle_q_y =
      Garden.Orchard.circuit.merkle_q_y.
  Proof. vm_compute. reflexivity. Qed.

  (** Per-layer CRH, variant 1 (layers 0–15, columns A0–A4, witness column A6):
      the output cell of [synthesize_merkle_layer] is [merkle_layer] of the
      node and the [merkle_path_of] reads (sibling on A1, bit on A4). *)
  Lemma merkle_layer_correct_1
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : circuit_holds Γ Garden.Orchard.circuit.synthesize
        (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty))
      (i : Z) (Hi : 0 <= i < 32) (Hlt : (i <? 16) = true)
      (node : Garden.Halo2.Synthesis.Cell.t columns RegionId.t)
      (Hfacts : interpret_facts Γ (layouter_facts
        (Garden.Orchard.circuit.synthesize_merkle_layer i node)))
      (Hok : merkle_layer_ok Γ i) :
    UnOp.from (eval_cell Γ (layouter_value
        (Garden.Orchard.circuit.synthesize_merkle_layer i node))) =
      SinsemillaSpec.merkle_layer merkle_Q i
        (UnOp.from (eval_cell Γ node))
        (read1 Γ (NP i))
        (read4 Γ (NP i) =? 1).
  Proof.
    pose proof (holds_gates Γ Hcircuit) as Hgates.
    pose proof (generator_table_facts Γ Hcircuit) as Hload.
    unfold Garden.Orchard.circuit.synthesize_merkle_layer in Hfacts |- *.
    rewrite Hlt in Hfacts |- *.
    unfold merkle_layer_ok, merkle_layer_canonical, merkle_words,
      merkle_bits, merkle_q2, merkle_witness_col in Hok.
    rewrite Hlt in Hok.
    destruct Hok as [Hcanon Hnondeg].
    destruct Hcanon as (Hcanon1 & Hcanon2 & Hcanon3).
    (* Facts of the node-position region: selector and node copy. *)
    pose proof Hfacts as Hnp.
    apply interpret_layouter_facts_bind_left in Hnp.
    unfold Garden.Orchard.circuit.synthesize_node_position_1,
      Garden.Orchard.circuit.synthesize_node_position_instance in Hnp.
    apply interpret_layouter_facts_in_namespace in Hnp.
    apply interpret_layouter_facts_add_region in Hnp.
    cbn [region_facts region_value Monad.bind Monad.ret
      Garden.Halo2.Synthesis.RegionIsMonad List.app
      interpret_facts interpret_fact] in Hnp.
    destruct Hnp as (HselNP & Hcopy_node & _).
    (* Facts of the hash layer: hash region and decomposition region. *)
    pose proof Hfacts as Hh.
    apply interpret_layouter_facts_bind_right in Hh.
    unfold Garden.Orchard.circuit.synthesize_merkle_hash_layer_1 in Hh.
    apply interpret_layouter_facts_in_namespace in Hh.
    do 5 apply interpret_layouter_facts_bind_right in Hh.
    pose proof Hh as Hhash.
    apply interpret_layouter_facts_bind_left in Hhash.
    apply interpret_layouter_facts_in_namespace in Hhash.
    unfold Garden.Halo2.halo2_gadgets.sinsemilla.chip.synthesize_hash_to_point_1
      in Hhash.
    apply interpret_layouter_facts_add_region in Hhash.
    pose proof Hh as Hdecf.
    apply interpret_layouter_facts_bind_right,
      interpret_layouter_facts_bind_left in Hdecf.
    unfold Garden.Orchard.circuit.synthesize_merkle_decomposition_1,
      Garden.Orchard.circuit.synthesize_merkle_decomposition_instance in Hdecf.
    apply interpret_layouter_facts_add_region in Hdecf.
    cbn [region_facts region_value layouter_value Monad.bind Monad.ret
      Garden.Halo2.Synthesis.RegionIsMonad
      Garden.Halo2.Synthesis.LayouterIsMonad
      List.app interpret_facts interpret_fact] in Hdecf.
    destruct Hdecf as (HselD & Hc_a & Hc_b & Hc_c & Hc_left & Hc_right &
      Hc_z1a & Hc_z1b & Hc_b1 & Hc_b2 & Hconst_l & _).
    cbn in Hc_a, Hc_b, Hc_c, Hc_left, Hc_right, Hc_z1a, Hc_z1b, Hc_b1, Hc_b2.
    clear Hfacts Hh.
    (* Hash-region facts: seed selector/fixed/constant, per-piece schedules
       and piece copies. *)
    pose proof Hhash as HselY.
    apply interpret_region_facts_bind_left in HselY.
    cbn [region_facts interpret_facts interpret_fact] in HselY.
    destruct HselY as [HselY _].
    pose proof Hhash as HfixY.
    apply interpret_region_facts_bind_right,
      interpret_region_facts_bind_left in HfixY.
    cbn [region_facts interpret_facts interpret_fact] in HfixY.
    destruct HfixY as [HfixY _].
    pose proof Hhash as HconstX.
    do 2 apply interpret_region_facts_bind_right in HconstX.
    apply interpret_region_facts_bind_left in HconstX.
    cbn [region_facts interpret_facts interpret_fact] in HconstX.
    destruct HconstX as [HconstX _].
    pose proof Hhash as HpieceA.
    do 3 apply interpret_region_facts_bind_right in HpieceA.
    apply interpret_region_facts_bind_left in HpieceA.
    pose proof Hhash as HpieceB.
    do 4 apply interpret_region_facts_bind_right in HpieceB.
    apply interpret_region_facts_bind_left in HpieceB.
    pose proof Hhash as HpieceC.
    do 5 apply interpret_region_facts_bind_right in HpieceC.
    apply interpret_region_facts_bind_left in HpieceC.
    clear Hhash.
    pose proof HpieceA as HselA.
    unfold Garden.Halo2.halo2_gadgets.sinsemilla.chip.synthesize_hash_piece
      in HselA.
    apply interpret_region_facts_bind_left in HselA.
    pose proof HpieceA as Hq2A.
    unfold Garden.Halo2.halo2_gadgets.sinsemilla.chip.synthesize_hash_piece
      in Hq2A.
    apply interpret_region_facts_bind_right,
      interpret_region_facts_bind_left in Hq2A.
    pose proof HpieceA as HcopyA.
    unfold Garden.Halo2.halo2_gadgets.sinsemilla.chip.synthesize_hash_piece
      in HcopyA.
    do 2 apply interpret_region_facts_bind_right in HcopyA.
    apply interpret_region_facts_bind_left in HcopyA.
    cbn in HcopyA.
    destruct HcopyA as [HcopyA _].
    pose proof HpieceB as HselB.
    unfold Garden.Halo2.halo2_gadgets.sinsemilla.chip.synthesize_hash_piece
      in HselB.
    apply interpret_region_facts_bind_left in HselB.
    pose proof HpieceB as Hq2B.
    unfold Garden.Halo2.halo2_gadgets.sinsemilla.chip.synthesize_hash_piece
      in Hq2B.
    apply interpret_region_facts_bind_right,
      interpret_region_facts_bind_left in Hq2B.
    pose proof HpieceB as HcopyB.
    unfold Garden.Halo2.halo2_gadgets.sinsemilla.chip.synthesize_hash_piece
      in HcopyB.
    do 2 apply interpret_region_facts_bind_right in HcopyB.
    apply interpret_region_facts_bind_left in HcopyB.
    cbn in HcopyB.
    destruct HcopyB as [HcopyB _].
    pose proof HpieceC as HselC.
    unfold Garden.Halo2.halo2_gadgets.sinsemilla.chip.synthesize_hash_piece
      in HselC.
    apply interpret_region_facts_bind_left in HselC.
    pose proof HpieceC as Hq2C.
    unfold Garden.Halo2.halo2_gadgets.sinsemilla.chip.synthesize_hash_piece
      in Hq2C.
    apply interpret_region_facts_bind_right,
      interpret_region_facts_bind_left in Hq2C.
    pose proof HpieceC as HcopyC.
    unfold Garden.Halo2.halo2_gadgets.sinsemilla.chip.synthesize_hash_piece
      in HcopyC.
    do 2 apply interpret_region_facts_bind_right in HcopyC.
    apply interpret_region_facts_bind_left in HcopyC.
    cbn in HcopyC.
    destruct HcopyC as [HcopyC _].
    clear HpieceA HpieceB HpieceC.
    (* Row schedules assembled across the three pieces. *)
    assert (Hsel : forall j : nat, (j < 52)%nat ->
        Γ ⊢ ⟦ Expression.Selector Selector.QSinsemilla1_1 ⟧
          (Garden.Orchard.circuit.merkle_region i
            RegionId.Merkle.Region.HashToPoint,
            Z.of_nat j) = 1).
    { intros j Hj.
      apply SinsemillaHash.enabled_eq_one.
      destruct (Nat.lt_ge_cases j 25) as [Hj25 | Hj25].
      - pose proof (interpret_facts_In Γ _ _ HselA
          (enable_selector_rows_fact _ Selector.QSinsemilla1_1 0 25 j Hj25))
          as Hf.
        cbn [interpret_fact] in Hf.
        replace (Z.of_nat j) with (0 + Z.of_nat j) by lia.
        exact Hf.
      - destruct (Nat.lt_ge_cases j 27) as [Hj27 | Hj27].
        + pose proof (interpret_facts_In Γ _ _ HselB
            (enable_selector_rows_fact _ Selector.QSinsemilla1_1 25 2 (j - 25)
              ltac:(lia))) as Hf.
          cbn [interpret_fact] in Hf.
          replace (Z.of_nat j) with (25 + Z.of_nat (j - 25)) by lia.
          exact Hf.
        + pose proof (interpret_facts_In Γ _ _ HselC
            (enable_selector_rows_fact _ Selector.QSinsemilla1_1 27 25 (j - 27)
              ltac:(lia))) as Hf.
          cbn [interpret_fact] in Hf.
          replace (Z.of_nat j) with (27 + Z.of_nat (j - 27)) by lia.
          exact Hf. }
    assert (Hq2_one : forall j : nat,
        (j < 52)%nat -> j <> 24%nat -> j <> 26%nat -> j <> 51%nat ->
        Γ.(Assignment.fixed) Fixed.QSinsemilla2_1
          (Garden.Orchard.circuit.merkle_region i
            RegionId.Merkle.Region.HashToPoint)
          (Z.of_nat j) = 1).
    { intros j Hj H24 H26 H51.
      destruct (Nat.lt_ge_cases j 25) as [Hj25 | Hj25].
      - pose proof (interpret_facts_In Γ _ _ Hq2A
          (assign_q_s2_rows_fact_step _ Fixed.QSinsemilla2_1 0 25 j false
            ltac:(lia))) as Hf.
        cbn [interpret_fact] in Hf.
        replace (Z.of_nat j) with (0 + Z.of_nat j) by lia.
        exact Hf.
      - destruct (Nat.lt_ge_cases j 27) as [Hj27 | Hj27].
        + pose proof (interpret_facts_In Γ _ _ Hq2B
            (assign_q_s2_rows_fact_step _ Fixed.QSinsemilla2_1 25 2 (j - 25)
              false ltac:(lia))) as Hf.
          cbn [interpret_fact] in Hf.
          replace (Z.of_nat j) with (25 + Z.of_nat (j - 25)) by lia.
          exact Hf.
        + pose proof (interpret_facts_In Γ _ _ Hq2C
            (assign_q_s2_rows_fact_step _ Fixed.QSinsemilla2_1 27 25 (j - 27)
              true ltac:(lia))) as Hf.
          cbn [interpret_fact] in Hf.
          replace (Z.of_nat j) with (27 + Z.of_nat (j - 27)) by lia.
          exact Hf. }
    assert (Hq2_24 : Γ.(Assignment.fixed) Fixed.QSinsemilla2_1
        (Garden.Orchard.circuit.merkle_region i
          RegionId.Merkle.Region.HashToPoint)
        24 = 0).
    { pose proof (interpret_facts_In Γ _ _ Hq2A
        (assign_q_s2_rows_fact_last _ Fixed.QSinsemilla2_1 0 25 false
          ltac:(lia))) as Hf.
      cbn [interpret_fact] in Hf.
      replace (0 + Z.of_nat (25 - 1)) with 24 in Hf by lia.
      exact Hf. }
    assert (Hq2_26 : Γ.(Assignment.fixed) Fixed.QSinsemilla2_1
        (Garden.Orchard.circuit.merkle_region i
          RegionId.Merkle.Region.HashToPoint)
        26 = 0).
    { pose proof (interpret_facts_In Γ _ _ Hq2B
        (assign_q_s2_rows_fact_last _ Fixed.QSinsemilla2_1 25 2 false
          ltac:(lia))) as Hf.
      cbn [interpret_fact] in Hf.
      replace (25 + Z.of_nat (2 - 1)) with 26 in Hf by lia.
      exact Hf. }
    assert (Hq2_51 : Γ.(Assignment.fixed) Fixed.QSinsemilla2_1
        (Garden.Orchard.circuit.merkle_region i
          RegionId.Merkle.Region.HashToPoint)
        51 = 2).
    { pose proof (interpret_facts_In Γ _ _ Hq2C
        (assign_q_s2_rows_fact_last _ Fixed.QSinsemilla2_1 27 25 true
          ltac:(lia))) as Hf.
      cbn [interpret_fact] in Hf.
      replace (27 + Z.of_nat (25 - 1)) with 51 in Hf by lia.
      exact Hf. }
    clear HselA HselB HselC Hq2A Hq2B Hq2C.
    (* The four gates of the layer, from [satisfies_gates]. *)
    assert (Hgate_sin : forall row : Z,
        Γ ⊢ ⟦ Garden.Halo2.halo2_gadgets.sinsemilla.chip.sinsemilla_gate
          Selector.QSinsemilla1_1 Fixed.QSinsemilla2_1
          Advice.A0 Advice.A1 Advice.A3 Advice.A4 ⟧
        (Garden.Orchard.circuit.merkle_region i
          RegionId.Merkle.Region.HashToPoint,
          row)).
    { intros row.
      apply (satisfies_gates_at Γ
        (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)
        (Garden.Halo2.halo2_gadgets.sinsemilla.chip.sinsemilla_gate
          Selector.QSinsemilla1_1 Fixed.QSinsemilla2_1
          Advice.A0 Advice.A1 Advice.A3 Advice.A4)
        (Garden.Orchard.circuit.merkle_region i
          RegionId.Merkle.Region.HashToPoint)
        row
        ltac:(cbn; repeat (first [left; reflexivity | right]))
        Hgates). }
    assert (Hgate_yq :
        Γ ⊢ ⟦ Garden.Halo2.halo2_gadgets.sinsemilla.chip.initial_y_q_gate
          Selector.QSinsemilla4_1 Fixed.LagrangeCoeffs0
          Advice.A0 Advice.A1 Advice.A3 Advice.A4 ⟧
        (Garden.Orchard.circuit.merkle_region i
          RegionId.Merkle.Region.HashToPoint,
          0)).
    { apply (satisfies_gates_at Γ
        (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)
        (Garden.Halo2.halo2_gadgets.sinsemilla.chip.initial_y_q_gate
          Selector.QSinsemilla4_1 Fixed.LagrangeCoeffs0
          Advice.A0 Advice.A1 Advice.A3 Advice.A4)
        (Garden.Orchard.circuit.merkle_region i
          RegionId.Merkle.Region.HashToPoint)
        0
        ltac:(cbn; repeat (first [left; reflexivity | right]))
        Hgates). }
    assert (Hgate_cs :
        Γ ⊢ ⟦ Garden.Halo2.halo2_gadgets.utilities.cond_swap.cond_swap_gate
          Selector.QCondSwap1 Advice.A0 Advice.A1 Advice.A2 Advice.A3
          Advice.A4 ⟧
        (Garden.Orchard.circuit.merkle_region i
          RegionId.Merkle.Region.NodePosition,
          0)).
    { apply (satisfies_gates_at Γ
        (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)
        (Garden.Halo2.halo2_gadgets.utilities.cond_swap.cond_swap_gate
          Selector.QCondSwap1 Advice.A0 Advice.A1 Advice.A2 Advice.A3
          Advice.A4)
        (Garden.Orchard.circuit.merkle_region i
          RegionId.Merkle.Region.NodePosition)
        0
        ltac:(cbn; repeat (first [left; reflexivity | right]))
        Hgates). }
    assert (Hgate_dec :
        Γ ⊢ ⟦ Garden.Halo2.halo2_gadgets.sinsemilla.merkle.chip
            .decomposition_check_gate
          Selector.QMerkleDecompose1 Advice.A0 Advice.A1 Advice.A2 Advice.A3
          Advice.A4 ⟧
        (Garden.Orchard.circuit.merkle_region i
          RegionId.Merkle.Region.Decomposition,
          0)).
    { apply (satisfies_gates_at Γ
        (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)
        (Garden.Halo2.halo2_gadgets.sinsemilla.merkle.chip
          .decomposition_check_gate
          Selector.QMerkleDecompose1 Advice.A0 Advice.A1 Advice.A2 Advice.A3
          Advice.A4)
        (Garden.Orchard.circuit.merkle_region i
          RegionId.Merkle.Region.Decomposition)
        0
        ltac:(cbn; repeat (first [left; reflexivity | right]))
        Hgates). }
    (* Seed: the accumulator at row 0 is the domain point. *)
    pose proof (InitialYQ.deterministic Γ
        (Garden.Orchard.circuit.merkle_region i
          RegionId.Merkle.Region.HashToPoint)
        0 Selector.QSinsemilla4_1 Fixed.LagrangeCoeffs0
        Advice.A0 Advice.A1 Advice.A3 Advice.A4
        (enabled_nonzero Γ Selector.QSinsemilla4_1 _ 0 HselY) Hgate_yq) as Hy.
    rewrite (fixed_expression_eq Γ Fixed.LagrangeCoeffs0 _ 0
      Garden.Orchard.circuit.merkle_q_y HfixY) in Hy.
    pose proof (SinsemillaHash.acc_at_init Γ Advice.A0 Advice.A1 Advice.A3
      Advice.A4 _ 0 (UnOp.from Garden.Orchard.circuit.merkle_q_y) Hy) as Hacc0.
    rewrite (eval_advice_cur_cell Γ _ Advice.A0 0) in Hacc0.
    rewrite HconstX in Hacc0.
    rewrite merkle_q_x_reduced in Hacc0.
    rewrite FieldRewrite.from_from in Hacc0.
    rewrite merkle_q_y_reduced in Hacc0.
    (* The decomposition-gate record, routed through the copies to the hash
       region's running-sum cells and the range/swap cells. *)
    pose proof (DecompositionCheck.deterministic Γ
        (Garden.Orchard.circuit.merkle_region i
          RegionId.Merkle.Region.Decomposition)
        0 Selector.QMerkleDecompose1 Advice.A0 Advice.A1 Advice.A2 Advice.A3
        Advice.A4
        (enabled_nonzero Γ Selector.QMerkleDecompose1 _ 0 HselD) Hgate_dec)
      as Hdec.
    cbn in Hconst_l.
    rewrite !(eval_advice_cur_cell Γ) in Hdec.
    rewrite !(eval_advice_next_cell Γ) in Hdec.
    cbn [eval_cell Garden.Halo2.Synthesis.Cell.advice
      Garden.Halo2.Synthesis.Cell.column Garden.Halo2.Synthesis.Cell.region
      Garden.Halo2.Synthesis.Cell.row_offset] in Hdec.
    replace (0 + 1) with 1 in Hdec by lia.
    rewrite Hc_a, Hc_b, Hc_c, Hc_left, Hc_right, Hc_z1a, Hc_z1b, Hc_b1, Hc_b2,
      Hconst_l in Hdec.
    rewrite <- HcopyA, <- HcopyB, <- HcopyC in Hdec.
    cbn [eval_cell Garden.Halo2.Synthesis.Cell.advice
      Garden.Halo2.Synthesis.Cell.column Garden.Halo2.Synthesis.Cell.region
      Garden.Halo2.Synthesis.Cell.row_offset] in Hcanon3.
    rewrite <- HcopyC in Hcanon3.
    clear Hy Hgate_yq Hgate_dec Hc_a Hc_b Hc_c Hc_left Hc_right Hc_z1a Hc_z1b
      Hc_b1 Hc_b2 Hconst_l HselD HselY HfixY HconstX HcopyA HcopyB HcopyC.
    (* The column-generic core produces the CRH of the swapped pair. *)
    pose proof (merkle_hash_layer_core Γ Selector.QSinsemilla1_1
      Fixed.QSinsemilla2_1 Advice.A0 Advice.A1 Advice.A2 Advice.A3 Advice.A4
      (Garden.Orchard.circuit.merkle_region i
        RegionId.Merkle.Region.HashToPoint)
      i
      (UnOp.from (Γ.(Assignment.advice) Advice.A2
        (Garden.Orchard.circuit.merkle_region i
          RegionId.Merkle.Region.NodePosition) 0))
      (UnOp.from (Γ.(Assignment.advice) Advice.A3
        (Garden.Orchard.circuit.merkle_region i
          RegionId.Merkle.Region.NodePosition) 0))
      (UnOp.from (Γ.(Assignment.advice) Advice.A9
        (Garden.Orchard.circuit.merkle_region i
          RegionId.Merkle.Region.RangeB1) 0))
      (UnOp.from (Γ.(Assignment.advice) Advice.A9
        (Garden.Orchard.circuit.merkle_region i
          RegionId.Merkle.Region.RangeB2) 0))
      Hi Hload Hsel Hgate_sin
      (fun row => generator_table_lookup_holds_1 Γ Hcircuit _ row)
      Hq2_one Hq2_24 Hq2_26 Hq2_51 Hacc0 Hnondeg
      (FieldRewrite.from_from _) (FieldRewrite.from_from _)
      Hdec Hcanon1 Hcanon2 Hcanon3) as Hx.
    transitivity (SinsemillaSpec.merkle_crh merkle_Q i
      (UnOp.from (Γ.(Assignment.advice) Advice.A2
        (Garden.Orchard.circuit.merkle_region i
          RegionId.Merkle.Region.NodePosition) 0))
      (UnOp.from (Γ.(Assignment.advice) Advice.A3
        (Garden.Orchard.circuit.merkle_region i
          RegionId.Merkle.Region.NodePosition) 0)));
      [exact Hx |].
    (* Cond-swap decode: the swapped pair against the [merkle_path_of]
       reads. *)
    pose proof (CondSwap.deterministic Γ
        (Garden.Orchard.circuit.merkle_region i
          RegionId.Merkle.Region.NodePosition)
        0 Selector.QCondSwap1 Advice.A0 Advice.A1 Advice.A2 Advice.A3
        Advice.A4
        (enabled_nonzero Γ Selector.QCondSwap1 _ 0 HselNP) Hgate_cs) as Hcs.
    pose proof (CondSwap.swap_is_bool Γ
        (Garden.Orchard.circuit.merkle_region i
          RegionId.Merkle.Region.NodePosition)
        0 Selector.QCondSwap1 Advice.A0 Advice.A1 Advice.A2 Advice.A3
        Advice.A4
        (enabled_nonzero Γ Selector.QCondSwap1 _ 0 HselNP) Hgate_cs) as Hbool.
    rewrite (cond_swap_output_if _ _ _ Hbool) in Hcs.
    pose proof (f_equal CondSwap.a_swapped Hcs) as Hleft_sw.
    pose proof (f_equal CondSwap.b_swapped Hcs) as Hright_sw.
    with_strategy opaque [UnOp.from] cbn in Hleft_sw, Hright_sw.
    cbn in Hcopy_node.
    rewrite Hcopy_node in Hleft_sw, Hright_sw.
    setoid_rewrite Hleft_sw.
    setoid_rewrite Hright_sw.
    unfold SinsemillaSpec.merkle_layer, read1, read4, read_advice, NP.
    with_strategy opaque [UnOp.from SinsemillaSpec.merkle_crh] cbn.
    destruct (UnOp.from (Γ.(Assignment.advice) Advice.A4
      (Garden.Orchard.circuit.merkle_region i
        RegionId.Merkle.Region.NodePosition) 0)
      =? 1) eqn:Hbit.
    - rewrite !FieldRewrite.from_from. reflexivity.
    - rewrite !FieldRewrite.from_from. reflexivity.
  Qed.

  (** Per-layer CRH, variant 2 (layers 16–31, columns A5–A9, witness column A7):
      same statement with the layer-dependent reads (sibling on A6, bit on
      A9).  The proof is the variant-1 proof with the second column bundle. *)
  Lemma merkle_layer_correct_2
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : circuit_holds Γ Garden.Orchard.circuit.synthesize
        (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty))
      (i : Z) (Hi : 0 <= i < 32) (Hlt : (i <? 16) = false)
      (node : Garden.Halo2.Synthesis.Cell.t columns RegionId.t)
      (Hfacts : interpret_facts Γ (layouter_facts
        (Garden.Orchard.circuit.synthesize_merkle_layer i node)))
      (Hok : merkle_layer_ok Γ i) :
    UnOp.from (eval_cell Γ (layouter_value
        (Garden.Orchard.circuit.synthesize_merkle_layer i node))) =
      SinsemillaSpec.merkle_layer merkle_Q i
        (UnOp.from (eval_cell Γ node))
        (read6 Γ (NP i))
        (read9 Γ (NP i) =? 1).
  Proof.
    pose proof (holds_gates Γ Hcircuit) as Hgates.
    pose proof (generator_table_facts Γ Hcircuit) as Hload.
    unfold Garden.Orchard.circuit.synthesize_merkle_layer in Hfacts |- *.
    rewrite Hlt in Hfacts |- *.
    unfold merkle_layer_ok, merkle_layer_canonical, merkle_words,
      merkle_bits, merkle_q2, merkle_witness_col in Hok.
    rewrite Hlt in Hok.
    destruct Hok as [Hcanon Hnondeg].
    destruct Hcanon as (Hcanon1 & Hcanon2 & Hcanon3).
    pose proof Hfacts as Hnp.
    apply interpret_layouter_facts_bind_left in Hnp.
    unfold Garden.Orchard.circuit.synthesize_node_position_2,
      Garden.Orchard.circuit.synthesize_node_position_instance in Hnp.
    apply interpret_layouter_facts_in_namespace in Hnp.
    apply interpret_layouter_facts_add_region in Hnp.
    cbn [region_facts region_value Monad.bind Monad.ret
      Garden.Halo2.Synthesis.RegionIsMonad List.app
      interpret_facts interpret_fact] in Hnp.
    destruct Hnp as (HselNP & Hcopy_node & _).
    pose proof Hfacts as Hh.
    apply interpret_layouter_facts_bind_right in Hh.
    unfold Garden.Orchard.circuit.synthesize_merkle_hash_layer_2 in Hh.
    apply interpret_layouter_facts_in_namespace in Hh.
    do 5 apply interpret_layouter_facts_bind_right in Hh.
    pose proof Hh as Hhash.
    apply interpret_layouter_facts_bind_left in Hhash.
    apply interpret_layouter_facts_in_namespace in Hhash.
    unfold Garden.Halo2.halo2_gadgets.sinsemilla.chip.synthesize_hash_to_point_2
      in Hhash.
    apply interpret_layouter_facts_add_region in Hhash.
    pose proof Hh as Hdecf.
    apply interpret_layouter_facts_bind_right,
      interpret_layouter_facts_bind_left in Hdecf.
    unfold Garden.Orchard.circuit.synthesize_merkle_decomposition_2,
      Garden.Orchard.circuit.synthesize_merkle_decomposition_instance in Hdecf.
    apply interpret_layouter_facts_add_region in Hdecf.
    cbn [region_facts region_value layouter_value Monad.bind Monad.ret
      Garden.Halo2.Synthesis.RegionIsMonad
      Garden.Halo2.Synthesis.LayouterIsMonad
      List.app interpret_facts interpret_fact] in Hdecf.
    destruct Hdecf as (HselD & Hc_a & Hc_b & Hc_c & Hc_left & Hc_right &
      Hc_z1a & Hc_z1b & Hc_b1 & Hc_b2 & Hconst_l & _).
    cbn in Hc_a, Hc_b, Hc_c, Hc_left, Hc_right, Hc_z1a, Hc_z1b, Hc_b1, Hc_b2.
    clear Hfacts Hh.
    pose proof Hhash as HselY.
    apply interpret_region_facts_bind_left in HselY.
    cbn [region_facts interpret_facts interpret_fact] in HselY.
    destruct HselY as [HselY _].
    pose proof Hhash as HfixY.
    apply interpret_region_facts_bind_right,
      interpret_region_facts_bind_left in HfixY.
    cbn [region_facts interpret_facts interpret_fact] in HfixY.
    destruct HfixY as [HfixY _].
    pose proof Hhash as HconstX.
    do 2 apply interpret_region_facts_bind_right in HconstX.
    apply interpret_region_facts_bind_left in HconstX.
    cbn [region_facts interpret_facts interpret_fact] in HconstX.
    destruct HconstX as [HconstX _].
    pose proof Hhash as HpieceA.
    do 3 apply interpret_region_facts_bind_right in HpieceA.
    apply interpret_region_facts_bind_left in HpieceA.
    pose proof Hhash as HpieceB.
    do 4 apply interpret_region_facts_bind_right in HpieceB.
    apply interpret_region_facts_bind_left in HpieceB.
    pose proof Hhash as HpieceC.
    do 5 apply interpret_region_facts_bind_right in HpieceC.
    apply interpret_region_facts_bind_left in HpieceC.
    clear Hhash.
    pose proof HpieceA as HselA.
    unfold Garden.Halo2.halo2_gadgets.sinsemilla.chip.synthesize_hash_piece
      in HselA.
    apply interpret_region_facts_bind_left in HselA.
    pose proof HpieceA as Hq2A.
    unfold Garden.Halo2.halo2_gadgets.sinsemilla.chip.synthesize_hash_piece
      in Hq2A.
    apply interpret_region_facts_bind_right,
      interpret_region_facts_bind_left in Hq2A.
    pose proof HpieceA as HcopyA.
    unfold Garden.Halo2.halo2_gadgets.sinsemilla.chip.synthesize_hash_piece
      in HcopyA.
    do 2 apply interpret_region_facts_bind_right in HcopyA.
    apply interpret_region_facts_bind_left in HcopyA.
    cbn in HcopyA.
    destruct HcopyA as [HcopyA _].
    pose proof HpieceB as HselB.
    unfold Garden.Halo2.halo2_gadgets.sinsemilla.chip.synthesize_hash_piece
      in HselB.
    apply interpret_region_facts_bind_left in HselB.
    pose proof HpieceB as Hq2B.
    unfold Garden.Halo2.halo2_gadgets.sinsemilla.chip.synthesize_hash_piece
      in Hq2B.
    apply interpret_region_facts_bind_right,
      interpret_region_facts_bind_left in Hq2B.
    pose proof HpieceB as HcopyB.
    unfold Garden.Halo2.halo2_gadgets.sinsemilla.chip.synthesize_hash_piece
      in HcopyB.
    do 2 apply interpret_region_facts_bind_right in HcopyB.
    apply interpret_region_facts_bind_left in HcopyB.
    cbn in HcopyB.
    destruct HcopyB as [HcopyB _].
    pose proof HpieceC as HselC.
    unfold Garden.Halo2.halo2_gadgets.sinsemilla.chip.synthesize_hash_piece
      in HselC.
    apply interpret_region_facts_bind_left in HselC.
    pose proof HpieceC as Hq2C.
    unfold Garden.Halo2.halo2_gadgets.sinsemilla.chip.synthesize_hash_piece
      in Hq2C.
    apply interpret_region_facts_bind_right,
      interpret_region_facts_bind_left in Hq2C.
    pose proof HpieceC as HcopyC.
    unfold Garden.Halo2.halo2_gadgets.sinsemilla.chip.synthesize_hash_piece
      in HcopyC.
    do 2 apply interpret_region_facts_bind_right in HcopyC.
    apply interpret_region_facts_bind_left in HcopyC.
    cbn in HcopyC.
    destruct HcopyC as [HcopyC _].
    clear HpieceA HpieceB HpieceC.
    assert (Hsel : forall j : nat, (j < 52)%nat ->
        Γ ⊢ ⟦ Expression.Selector Selector.QSinsemilla1_2 ⟧
          (Garden.Orchard.circuit.merkle_region i
            RegionId.Merkle.Region.HashToPoint,
            Z.of_nat j) = 1).
    { intros j Hj.
      apply SinsemillaHash.enabled_eq_one.
      destruct (Nat.lt_ge_cases j 25) as [Hj25 | Hj25].
      - pose proof (interpret_facts_In Γ _ _ HselA
          (enable_selector_rows_fact _ Selector.QSinsemilla1_2 0 25 j Hj25))
          as Hf.
        cbn [interpret_fact] in Hf.
        replace (Z.of_nat j) with (0 + Z.of_nat j) by lia.
        exact Hf.
      - destruct (Nat.lt_ge_cases j 27) as [Hj27 | Hj27].
        + pose proof (interpret_facts_In Γ _ _ HselB
            (enable_selector_rows_fact _ Selector.QSinsemilla1_2 25 2 (j - 25)
              ltac:(lia))) as Hf.
          cbn [interpret_fact] in Hf.
          replace (Z.of_nat j) with (25 + Z.of_nat (j - 25)) by lia.
          exact Hf.
        + pose proof (interpret_facts_In Γ _ _ HselC
            (enable_selector_rows_fact _ Selector.QSinsemilla1_2 27 25 (j - 27)
              ltac:(lia))) as Hf.
          cbn [interpret_fact] in Hf.
          replace (Z.of_nat j) with (27 + Z.of_nat (j - 27)) by lia.
          exact Hf. }
    assert (Hq2_one : forall j : nat,
        (j < 52)%nat -> j <> 24%nat -> j <> 26%nat -> j <> 51%nat ->
        Γ.(Assignment.fixed) Fixed.QSinsemilla2_2
          (Garden.Orchard.circuit.merkle_region i
            RegionId.Merkle.Region.HashToPoint)
          (Z.of_nat j) = 1).
    { intros j Hj H24 H26 H51.
      destruct (Nat.lt_ge_cases j 25) as [Hj25 | Hj25].
      - pose proof (interpret_facts_In Γ _ _ Hq2A
          (assign_q_s2_rows_fact_step _ Fixed.QSinsemilla2_2 0 25 j false
            ltac:(lia))) as Hf.
        cbn [interpret_fact] in Hf.
        replace (Z.of_nat j) with (0 + Z.of_nat j) by lia.
        exact Hf.
      - destruct (Nat.lt_ge_cases j 27) as [Hj27 | Hj27].
        + pose proof (interpret_facts_In Γ _ _ Hq2B
            (assign_q_s2_rows_fact_step _ Fixed.QSinsemilla2_2 25 2 (j - 25)
              false ltac:(lia))) as Hf.
          cbn [interpret_fact] in Hf.
          replace (Z.of_nat j) with (25 + Z.of_nat (j - 25)) by lia.
          exact Hf.
        + pose proof (interpret_facts_In Γ _ _ Hq2C
            (assign_q_s2_rows_fact_step _ Fixed.QSinsemilla2_2 27 25 (j - 27)
              true ltac:(lia))) as Hf.
          cbn [interpret_fact] in Hf.
          replace (Z.of_nat j) with (27 + Z.of_nat (j - 27)) by lia.
          exact Hf. }
    assert (Hq2_24 : Γ.(Assignment.fixed) Fixed.QSinsemilla2_2
        (Garden.Orchard.circuit.merkle_region i
          RegionId.Merkle.Region.HashToPoint)
        24 = 0).
    { pose proof (interpret_facts_In Γ _ _ Hq2A
        (assign_q_s2_rows_fact_last _ Fixed.QSinsemilla2_2 0 25 false
          ltac:(lia))) as Hf.
      cbn [interpret_fact] in Hf.
      replace (0 + Z.of_nat (25 - 1)) with 24 in Hf by lia.
      exact Hf. }
    assert (Hq2_26 : Γ.(Assignment.fixed) Fixed.QSinsemilla2_2
        (Garden.Orchard.circuit.merkle_region i
          RegionId.Merkle.Region.HashToPoint)
        26 = 0).
    { pose proof (interpret_facts_In Γ _ _ Hq2B
        (assign_q_s2_rows_fact_last _ Fixed.QSinsemilla2_2 25 2 false
          ltac:(lia))) as Hf.
      cbn [interpret_fact] in Hf.
      replace (25 + Z.of_nat (2 - 1)) with 26 in Hf by lia.
      exact Hf. }
    assert (Hq2_51 : Γ.(Assignment.fixed) Fixed.QSinsemilla2_2
        (Garden.Orchard.circuit.merkle_region i
          RegionId.Merkle.Region.HashToPoint)
        51 = 2).
    { pose proof (interpret_facts_In Γ _ _ Hq2C
        (assign_q_s2_rows_fact_last _ Fixed.QSinsemilla2_2 27 25 true
          ltac:(lia))) as Hf.
      cbn [interpret_fact] in Hf.
      replace (27 + Z.of_nat (25 - 1)) with 51 in Hf by lia.
      exact Hf. }
    clear HselA HselB HselC Hq2A Hq2B Hq2C.
    assert (Hgate_sin : forall row : Z,
        Γ ⊢ ⟦ Garden.Halo2.halo2_gadgets.sinsemilla.chip.sinsemilla_gate
          Selector.QSinsemilla1_2 Fixed.QSinsemilla2_2
          Advice.A5 Advice.A6 Advice.A8 Advice.A9 ⟧
        (Garden.Orchard.circuit.merkle_region i
          RegionId.Merkle.Region.HashToPoint,
          row)).
    { intros row.
      apply (satisfies_gates_at Γ
        (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)
        (Garden.Halo2.halo2_gadgets.sinsemilla.chip.sinsemilla_gate
          Selector.QSinsemilla1_2 Fixed.QSinsemilla2_2
          Advice.A5 Advice.A6 Advice.A8 Advice.A9)
        (Garden.Orchard.circuit.merkle_region i
          RegionId.Merkle.Region.HashToPoint)
        row
        ltac:(cbn; repeat (first [left; reflexivity | right]))
        Hgates). }
    assert (Hgate_yq :
        Γ ⊢ ⟦ Garden.Halo2.halo2_gadgets.sinsemilla.chip.initial_y_q_gate
          Selector.QSinsemilla4_2 Fixed.LagrangeCoeffs1
          Advice.A5 Advice.A6 Advice.A8 Advice.A9 ⟧
        (Garden.Orchard.circuit.merkle_region i
          RegionId.Merkle.Region.HashToPoint,
          0)).
    { apply (satisfies_gates_at Γ
        (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)
        (Garden.Halo2.halo2_gadgets.sinsemilla.chip.initial_y_q_gate
          Selector.QSinsemilla4_2 Fixed.LagrangeCoeffs1
          Advice.A5 Advice.A6 Advice.A8 Advice.A9)
        (Garden.Orchard.circuit.merkle_region i
          RegionId.Merkle.Region.HashToPoint)
        0
        ltac:(cbn; repeat (first [left; reflexivity | right]))
        Hgates). }
    assert (Hgate_cs :
        Γ ⊢ ⟦ Garden.Halo2.halo2_gadgets.utilities.cond_swap.cond_swap_gate
          Selector.QCondSwap2 Advice.A5 Advice.A6 Advice.A7 Advice.A8
          Advice.A9 ⟧
        (Garden.Orchard.circuit.merkle_region i
          RegionId.Merkle.Region.NodePosition,
          0)).
    { apply (satisfies_gates_at Γ
        (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)
        (Garden.Halo2.halo2_gadgets.utilities.cond_swap.cond_swap_gate
          Selector.QCondSwap2 Advice.A5 Advice.A6 Advice.A7 Advice.A8
          Advice.A9)
        (Garden.Orchard.circuit.merkle_region i
          RegionId.Merkle.Region.NodePosition)
        0
        ltac:(cbn; repeat (first [left; reflexivity | right]))
        Hgates). }
    assert (Hgate_dec :
        Γ ⊢ ⟦ Garden.Halo2.halo2_gadgets.sinsemilla.merkle.chip
            .decomposition_check_gate
          Selector.QMerkleDecompose2 Advice.A5 Advice.A6 Advice.A7 Advice.A8
          Advice.A9 ⟧
        (Garden.Orchard.circuit.merkle_region i
          RegionId.Merkle.Region.Decomposition,
          0)).
    { apply (satisfies_gates_at Γ
        (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)
        (Garden.Halo2.halo2_gadgets.sinsemilla.merkle.chip
          .decomposition_check_gate
          Selector.QMerkleDecompose2 Advice.A5 Advice.A6 Advice.A7 Advice.A8
          Advice.A9)
        (Garden.Orchard.circuit.merkle_region i
          RegionId.Merkle.Region.Decomposition)
        0
        ltac:(cbn; repeat (first [left; reflexivity | right]))
        Hgates). }
    pose proof (InitialYQ.deterministic Γ
        (Garden.Orchard.circuit.merkle_region i
          RegionId.Merkle.Region.HashToPoint)
        0 Selector.QSinsemilla4_2 Fixed.LagrangeCoeffs1
        Advice.A5 Advice.A6 Advice.A8 Advice.A9
        (enabled_nonzero Γ Selector.QSinsemilla4_2 _ 0 HselY) Hgate_yq) as Hy.
    rewrite (fixed_expression_eq Γ Fixed.LagrangeCoeffs1 _ 0
      Garden.Orchard.circuit.merkle_q_y HfixY) in Hy.
    pose proof (SinsemillaHash.acc_at_init Γ Advice.A5 Advice.A6 Advice.A8
      Advice.A9 _ 0 (UnOp.from Garden.Orchard.circuit.merkle_q_y) Hy) as Hacc0.
    rewrite (eval_advice_cur_cell Γ _ Advice.A5 0) in Hacc0.
    rewrite HconstX in Hacc0.
    rewrite merkle_q_x_reduced in Hacc0.
    rewrite FieldRewrite.from_from in Hacc0.
    rewrite merkle_q_y_reduced in Hacc0.
    pose proof (DecompositionCheck.deterministic Γ
        (Garden.Orchard.circuit.merkle_region i
          RegionId.Merkle.Region.Decomposition)
        0 Selector.QMerkleDecompose2 Advice.A5 Advice.A6 Advice.A7 Advice.A8
        Advice.A9
        (enabled_nonzero Γ Selector.QMerkleDecompose2 _ 0 HselD) Hgate_dec)
      as Hdec.
    cbn in Hconst_l.
    rewrite !(eval_advice_cur_cell Γ) in Hdec.
    rewrite !(eval_advice_next_cell Γ) in Hdec.
    cbn [eval_cell Garden.Halo2.Synthesis.Cell.advice
      Garden.Halo2.Synthesis.Cell.column Garden.Halo2.Synthesis.Cell.region
      Garden.Halo2.Synthesis.Cell.row_offset] in Hdec.
    replace (0 + 1) with 1 in Hdec by lia.
    rewrite Hc_a, Hc_b, Hc_c, Hc_left, Hc_right, Hc_z1a, Hc_z1b, Hc_b1, Hc_b2,
      Hconst_l in Hdec.
    rewrite <- HcopyA, <- HcopyB, <- HcopyC in Hdec.
    cbn [eval_cell Garden.Halo2.Synthesis.Cell.advice
      Garden.Halo2.Synthesis.Cell.column Garden.Halo2.Synthesis.Cell.region
      Garden.Halo2.Synthesis.Cell.row_offset] in Hcanon3.
    rewrite <- HcopyC in Hcanon3.
    clear Hy Hgate_yq Hgate_dec Hc_a Hc_b Hc_c Hc_left Hc_right Hc_z1a Hc_z1b
      Hc_b1 Hc_b2 Hconst_l HselD HselY HfixY HconstX HcopyA HcopyB HcopyC.
    pose proof (merkle_hash_layer_core Γ Selector.QSinsemilla1_2
      Fixed.QSinsemilla2_2 Advice.A5 Advice.A6 Advice.A7 Advice.A8 Advice.A9
      (Garden.Orchard.circuit.merkle_region i
        RegionId.Merkle.Region.HashToPoint)
      i
      (UnOp.from (Γ.(Assignment.advice) Advice.A7
        (Garden.Orchard.circuit.merkle_region i
          RegionId.Merkle.Region.NodePosition) 0))
      (UnOp.from (Γ.(Assignment.advice) Advice.A8
        (Garden.Orchard.circuit.merkle_region i
          RegionId.Merkle.Region.NodePosition) 0))
      (UnOp.from (Γ.(Assignment.advice) Advice.A9
        (Garden.Orchard.circuit.merkle_region i
          RegionId.Merkle.Region.RangeB1) 0))
      (UnOp.from (Γ.(Assignment.advice) Advice.A9
        (Garden.Orchard.circuit.merkle_region i
          RegionId.Merkle.Region.RangeB2) 0))
      Hi Hload Hsel Hgate_sin
      (fun row => generator_table_lookup_holds_2 Γ Hcircuit _ row)
      Hq2_one Hq2_24 Hq2_26 Hq2_51 Hacc0 Hnondeg
      (FieldRewrite.from_from _) (FieldRewrite.from_from _)
      Hdec Hcanon1 Hcanon2 Hcanon3) as Hx.
    transitivity (SinsemillaSpec.merkle_crh merkle_Q i
      (UnOp.from (Γ.(Assignment.advice) Advice.A7
        (Garden.Orchard.circuit.merkle_region i
          RegionId.Merkle.Region.NodePosition) 0))
      (UnOp.from (Γ.(Assignment.advice) Advice.A8
        (Garden.Orchard.circuit.merkle_region i
          RegionId.Merkle.Region.NodePosition) 0)));
      [exact Hx |].
    pose proof (CondSwap.deterministic Γ
        (Garden.Orchard.circuit.merkle_region i
          RegionId.Merkle.Region.NodePosition)
        0 Selector.QCondSwap2 Advice.A5 Advice.A6 Advice.A7 Advice.A8
        Advice.A9
        (enabled_nonzero Γ Selector.QCondSwap2 _ 0 HselNP) Hgate_cs) as Hcs.
    pose proof (CondSwap.swap_is_bool Γ
        (Garden.Orchard.circuit.merkle_region i
          RegionId.Merkle.Region.NodePosition)
        0 Selector.QCondSwap2 Advice.A5 Advice.A6 Advice.A7 Advice.A8
        Advice.A9
        (enabled_nonzero Γ Selector.QCondSwap2 _ 0 HselNP) Hgate_cs) as Hbool.
    rewrite (cond_swap_output_if _ _ _ Hbool) in Hcs.
    pose proof (f_equal CondSwap.a_swapped Hcs) as Hleft_sw.
    pose proof (f_equal CondSwap.b_swapped Hcs) as Hright_sw.
    with_strategy opaque [UnOp.from] cbn in Hleft_sw, Hright_sw.
    cbn in Hcopy_node.
    rewrite Hcopy_node in Hleft_sw, Hright_sw.
    setoid_rewrite Hleft_sw.
    setoid_rewrite Hright_sw.
    unfold SinsemillaSpec.merkle_layer, read6, read9, read_advice, NP.
    with_strategy opaque [UnOp.from SinsemillaSpec.merkle_crh] cbn.
    destruct (UnOp.from (Γ.(Assignment.advice) Advice.A9
      (Garden.Orchard.circuit.merkle_region i
        RegionId.Merkle.Region.NodePosition) 0)
      =? 1) eqn:Hbit.
    - rewrite !FieldRewrite.from_from. reflexivity.
    - rewrite !FieldRewrite.from_from. reflexivity.
  Qed.

  (** The per-layer CRH statement, dispatched across the two
      column variants and reconciled with the layer-dependent
      [merkle_path_of] reads (sibling on A1/A6, position bit on A4/A9). *)
  Lemma merkle_layer_correct
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : circuit_holds Γ Garden.Orchard.circuit.synthesize
        (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty))
      (i : Z) (Hi : 0 <= i < 32)
      (node : Garden.Halo2.Synthesis.Cell.t columns RegionId.t)
      (Hfacts : interpret_facts Γ (layouter_facts
        (Garden.Orchard.circuit.synthesize_merkle_layer i node)))
      (Hok : merkle_layer_ok Γ i) :
    UnOp.from (eval_cell Γ (layouter_value
        (Garden.Orchard.circuit.synthesize_merkle_layer i node))) =
      SinsemillaSpec.merkle_layer merkle_Q i
        (UnOp.from (eval_cell Γ node))
        (if i <? 16 then read1 Γ (NP i) else read6 Γ (NP i))
        ((if i <? 16 then read4 Γ (NP i) else read9 Γ (NP i)) =? 1).
  Proof.
    destruct (i <? 16) eqn:Hlt.
    - exact (merkle_layer_correct_1 Γ Hcircuit i Hi Hlt node Hfacts Hok).
    - exact (merkle_layer_correct_2 Γ Hcircuit i Hi Hlt node Hfacts Hok).
  Qed.

  (** * The 32-layer Merkle fold ([Hmerkle])

      Folding [merkle_layer_correct] along [synthesize_merkle_layers 32 0]
      turns the Merkle-root output cell into [OrchardSpec.anchor] of the
      witnessed old note commitment and the [merkle_path_of] reads,
      conditional on the per-layer side condition [merkle_witness_ok]. *)

  (** The x-cell of the witnessed old note commitment — the Merkle path's
      leaf cell. *)
  Definition cm_old_x_cell : Garden.Halo2.Synthesis.Cell.t columns RegionId.t :=
    (layouter_value
      (Garden.Orchard.circuit.witness_point
        (Garden.Orchard.circuit.witness_input_region
          RegionId.WitnessInput.CmOld)
        "cm_old")).(Garden.Orchard.circuit.AssignedPoint.x).

  Lemma cm_old_x_cell_eq :
    cm_old_x_cell =
      Garden.Halo2.Synthesis.Cell.advice
        (RegionId.WitnessInput RegionId.WitnessInput.CmOld) Advice.A0 0.
  Proof. reflexivity. Qed.

  (** The layer fold, generalized over the starting layer [s] and the running
      node cell: the value cell of [synthesize_merkle_layers n s node] holds
      the [merkle_layer] fold of the authentication-path reads of layers
      [s .. s + n - 1] over the node's value. *)
  Lemma merkle_layers_correct_aux
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : circuit_holds Γ Garden.Orchard.circuit.synthesize
        (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty))
      (Hok : merkle_witness_ok Γ) :
    forall (n s : nat)
      (node : Garden.Halo2.Synthesis.Cell.t columns RegionId.t),
      (s + n = 32)%nat ->
      interpret_facts Γ (layouter_facts
        (Garden.Orchard.circuit.synthesize_merkle_layers
          n (Z.of_nat s) node)) ->
      UnOp.from (eval_cell Γ (layouter_value
          (Garden.Orchard.circuit.synthesize_merkle_layers
            n (Z.of_nat s) node))) =
        Stdlib.Lists.List.fold_left
          (fun node '(layer, sibling, b) =>
            SinsemillaSpec.merkle_layer merkle_Q layer node sibling b)
          (Stdlib.Lists.List.map
            (fun i : nat =>
              let region :=
                RegionId.Merkle (RegionId.Merkle.Layer.of_index (Z.of_nat i))
                  RegionId.Merkle.Region.NodePosition in
              if Z.of_nat i <? 16
              then (Z.of_nat i, read1 Γ region, Z.eqb (read4 Γ region) 1)
              else (Z.of_nat i, read6 Γ region, Z.eqb (read9 Γ region) 1))
            (Stdlib.Lists.List.seq s n))
          (UnOp.from (eval_cell Γ node)).
  Proof.
    intros n.
    induction n as [| n IH]; intros s node Hsn Hfacts.
    - reflexivity.
    - cbn [Garden.Orchard.circuit.synthesize_merkle_layers Monad.bind
        Garden.Halo2.Synthesis.LayouterIsMonad layouter_value
        Stdlib.Lists.List.seq Stdlib.Lists.List.map
        Stdlib.Lists.List.fold_left] in Hfacts |- *.
      pose proof Hfacts as Hlayer.
      apply interpret_layouter_facts_bind_left in Hlayer.
      apply interpret_layouter_facts_bind_right in Hfacts.
      cbv beta in Hfacts.
      assert (HeqS : Z.of_nat (S s) = Z.of_nat s + 1) by lia.
      rewrite <- HeqS in Hfacts |- *.
      pose proof (merkle_layer_correct Γ Hcircuit (Z.of_nat s)
        ltac:(lia) node Hlayer (Hok (Z.of_nat s) ltac:(lia))) as Hstep.
      rewrite (IH (S s)
        (layouter_value
          (Garden.Orchard.circuit.synthesize_merkle_layer (Z.of_nat s) node))
        ltac:(lia) Hfacts).
      destruct (Z.of_nat s <? 16); f_equal; exact Hstep.
  Qed.

  (** The conditional [Hmerkle]: the Merkle-root output cell of
      the path synthesized from the old note commitment's x-cell equals
      [OrchardSpec.anchor] of the [CmOld] witness read and the
      [merkle_path_of] reads.  The conclusion is verbatim the [Hmerkle]
      hypothesis of [anchor_correct_of_merkle_root]
      (Orchard/circuit_proof/bridges.v); the [merkle_witness_ok] hypothesis
      is the per-layer canonicity/nondegeneracy side condition that any
      [anchor_correct] statement must surface (an unconditional
      form is refutable — see [merkle_layer_canonical]). *)
  Theorem merkle_root_cell_correct
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : circuit_holds Γ Garden.Orchard.circuit.synthesize
        (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty))
      (Hok : merkle_witness_ok Γ) :
    UnOp.from
      (eval_cell Γ
        (layouter_value
          (Garden.Orchard.circuit.synthesize_merkle_path
            (layouter_value
              (Garden.Orchard.circuit.witness_point
                (Garden.Orchard.circuit.witness_input_region
                  RegionId.WitnessInput.CmOld)
                "cm_old"))
              .(Garden.Orchard.circuit.AssignedPoint.x)))) =
      OrchardSpec.anchor orchard_circuit_params
        (read Γ (RegionId.WitnessInput RegionId.WitnessInput.CmOld))
        (merkle_path_of Γ).
  Proof.
    pose proof (merkle_path_facts Γ Hcircuit) as Hfacts.
    change (interpret_facts Γ
      (layouter_facts
        (Garden.Orchard.circuit.synthesize_merkle_path cm_old_x_cell)))
      in Hfacts.
    unfold Garden.Orchard.circuit.synthesize_merkle_path in Hfacts.
    apply interpret_layouter_facts_in_namespace in Hfacts.
    pose proof (merkle_layers_correct_aux Γ Hcircuit Hok 32%nat 0%nat
      cm_old_x_cell ltac:(lia) Hfacts) as Hfold.
    change (Z.of_nat 0%nat) with 0 in Hfold.
    change (UnOp.from
      (eval_cell Γ
        (layouter_value
          (Garden.Orchard.circuit.synthesize_merkle_path cm_old_x_cell))) =
      OrchardSpec.anchor orchard_circuit_params
        (read Γ (RegionId.WitnessInput RegionId.WitnessInput.CmOld))
        (merkle_path_of Γ)).
    unfold Garden.Orchard.circuit.synthesize_merkle_path.
    cbn [layouter_value].
    rewrite Hfold.
    unfold OrchardSpec.anchor, SinsemillaSpec.merkle_root, merkle_path_of,
      merkle_Q, orchard_circuit_params.
    cbn [OrchardSpec.merkle_crh_q].
    f_equal.
  Qed.
End OrchardActionMerkle.
