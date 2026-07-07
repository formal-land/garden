(** * The note-commit-new Sinsemilla hash fold.

    The hash-to-point output point of [note_commit.synthesize_new] (the
    [Which.New] instance, Sinsemilla variant 2, synthesized through
    [synthesize_hash_to_point_note_commit_2]) equals
    [SinsemillaSpec.sinsemilla_hash_to_point] of the NoteCommit domain point
    [note_commit_q orchard_circuit_params] applied to the 109 grid words of
    the region's running-sum column, from a satisfying assignment.  The
    instantiation mirrors the per-layer Merkle one ([circuit_proof/merkle.v],
    52 words over three pieces) at the eight-piece [a..h] schedule of
    [synthesize_hash_to_point_note_commit_region]: piece offsets/word counts
    (0,25) (25,1) (26,25) (51,6) (57,1) (58,25) (83,25) (108,1), boundary
    [q_s2 = 0] rows {24, 25, 50, 56, 57, 82, 107} and the final [q_s2 = 2]
    row 108.

    The incomplete-add nondegeneracy of the witnessed 109-word message is the
    explicit side condition [SinsemillaHash.nondegenerate], exactly as in the
    Merkle precedent ([merkle_layer_ok]). *)

Require Import Garden.Halo2.main.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.lemmas.
Require Import Garden.Orchard.columns.
Require Garden.Orchard.circuit.
Require Garden.Orchard.circuit.note_commit.
Require Import Garden.Orchard.circuit_proof.facts.
Require Garden.Halo2.halo2_gadgets.sinsemilla.chip.
Require Import Garden.Halo2.halo2_gadgets.sinsemilla.chip_proof.
Require Import Garden.Halo2.halo2_gadgets.sinsemilla.hash_to_point_proof.
Require Import Garden.Halo2.halo2_gadgets.sinsemilla.hash_to_point_fold_proof.
Require Import Garden.Halo2.halo2_gadgets.sinsemilla.spec.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.spec.
Require Import Garden.Orchard.circuit_spec.
Require Import Garden.Orchard.circuit_proof.merkle.
Require Import Garden.Field.Field.
Require Import Garden.Field.Lemmas.
Require Import Garden.Plonky3.M.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Lists.List.

#[local] Existing Instance Primes.PallasPIsPrime.

Global Open Scope Z_scope.

Module NC := Garden.Orchard.circuit.note_commit.
Module SChip := Garden.Halo2.halo2_gadgets.sinsemilla.chip.

Module NoteCommitNewHash.
  Include OrchardActionMerkle.

  Local Notation Holds Γ :=
    (circuit_holds Γ
      Garden.Orchard.circuit.synthesize
      (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)).

  (** The hash-to-point region of the [Which.New] NoteCommit instance. *)
  Definition new_hash_region : RegionId.t :=
    NC.note_commit_region RegionId.NoteCommit.Which.New
      RegionId.NoteCommit.HashToPoint.

  (** The NoteCommit Sinsemilla domain point [Q("NoteCommit")], as pinned by
      the hash-to-point synthesis constants. *)
  Definition note_commit_Q : Point.t := {|
    Point.x := NC.q_note_commit_m_x;
    Point.y := NC.q_note_commit_m_y;
  |}.

  Lemma note_commit_Q_eq :
    note_commit_Q = OrchardSpec.note_commit_q orchard_circuit_params.
  Proof. reflexivity. Qed.

  (** The 109 message words consumed by the new-note hash-to-point region
      (variant 2: running-sum column A7, [q_s2] column [QSinsemilla2_2]). *)
  Definition note_commit_new_words (Γ : Assignment.t columns RegionId.t)
      : list Z :=
    SinsemillaHash.hash_words Γ Fixed.QSinsemilla2_2 Advice.A7
      new_hash_region 109.

  Lemma q_note_commit_m_x_reduced :
    UnOp.from NC.q_note_commit_m_x = NC.q_note_commit_m_x.
  Proof. vm_compute. reflexivity. Qed.

  Lemma q_note_commit_m_y_reduced :
    UnOp.from NC.q_note_commit_m_y = NC.q_note_commit_m_y.
  Proof. vm_compute. reflexivity. Qed.

  (** The output cells of the new-note hash synthesis: the [HashResult]
      record returned by [synthesize_hash_to_point_note_commit_2] reads the
      point off [x_a]/[lambda_1] (columns A5/A8) at row 109 — the cells the
      note-commit complete-add region copies its [m] input from. *)
  Lemma hash_result_x_cell
      (a b c d e f g h : Garden.Halo2.Synthesis.Cell.t columns RegionId.t) :
    (layouter_value
      (SChip.synthesize_hash_to_point_note_commit_2 new_hash_region
        NC.q_note_commit_m_x NC.q_note_commit_m_y
        a b c d e f g h)).(SChip.HashResult.x) =
      Garden.Halo2.Synthesis.Cell.advice new_hash_region Advice.A5 109.
  Proof. reflexivity. Qed.

  Lemma hash_result_y_cell
      (a b c d e f g h : Garden.Halo2.Synthesis.Cell.t columns RegionId.t) :
    (layouter_value
      (SChip.synthesize_hash_to_point_note_commit_2 new_hash_region
        NC.q_note_commit_m_x NC.q_note_commit_m_y
        a b c d e f g h)).(SChip.HashResult.y) =
      Garden.Halo2.Synthesis.Cell.advice new_hash_region Advice.A8 109.
  Proof. reflexivity. Qed.

  (** Per-piece schedule facts of [synthesize_hash_piece]: selector on all
      [num_words] rows, [q_s2 = 1] on the running rows, and the boundary
      value ([2] for the final piece, [0] between pieces) on the piece's
      last row. *)
  Lemma hash_piece_schedule
      (Γ : Assignment.t columns RegionId.t) (region : RegionId.t)
      (q1 : Selector.t) (q2 : Fixed.t)
      (x_a x_p bits lambda_1 lambda_2 : Advice.t)
      (piece : Garden.Halo2.Synthesis.Cell.t columns RegionId.t)
      (offset : Z) (num_words : nat) (final : bool)
      (Hpiece : interpret_facts Γ (region_facts region
        (SChip.synthesize_hash_piece region q1 q2 x_a x_p bits
          lambda_1 lambda_2 piece offset num_words final))) :
    (forall i : nat, (i < num_words)%nat ->
      Γ.(Assignment.selector) q1 region (offset + Z.of_nat i) = 1) /\
    (forall i : nat, (S i < num_words)%nat ->
      Γ.(Assignment.fixed) q2 region (offset + Z.of_nat i) = 1) /\
    ((0 < num_words)%nat ->
      Γ.(Assignment.fixed) q2 region (offset + Z.of_nat (num_words - 1)) =
        (if final then 2 else 0)).
  Proof.
    pose proof Hpiece as Hsel.
    unfold SChip.synthesize_hash_piece in Hsel.
    apply interpret_region_facts_bind_left in Hsel.
    pose proof Hpiece as Hq2.
    unfold SChip.synthesize_hash_piece in Hq2.
    apply interpret_region_facts_bind_right,
      interpret_region_facts_bind_left in Hq2.
    refine (conj _ (conj _ _)).
    - intros i Hi.
      exact (interpret_facts_In Γ _ _ Hsel
        (enable_selector_rows_fact region q1 offset num_words i Hi)).
    - intros i Hi.
      exact (interpret_facts_In Γ _ _ Hq2
        (assign_q_s2_rows_fact_step region q2 offset num_words i final Hi)).
    - intros Hn.
      exact (interpret_facts_In Γ _ _ Hq2
        (assign_q_s2_rows_fact_last region q2 offset num_words final Hn)).
  Qed.

  (** The region facts of the new-note hash-to-point region, extracted from
      the circuit facts along [synthesize → synthesize_note_commit_new →
      note_commit.synthesize_new → synthesize_hash_to_point_note_commit_2].
      The eight message-piece cells are packaged existentially: none of the
      schedule facts the fold consumes depends on them (they only appear as
      [Copy] payloads). *)
  Lemma new_hash_region_facts
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ) :
    exists a b c d e f g h :
        Garden.Halo2.Synthesis.Cell.t columns RegionId.t,
      interpret_facts Γ (region_facts new_hash_region
        (SChip.synthesize_hash_to_point_note_commit_region
          new_hash_region
          Selector.QSinsemilla1_2 Selector.QSinsemilla4_2
          Fixed.QSinsemilla2_2 Fixed.LagrangeCoeffs1
          Advice.A5 Advice.A6 Advice.A7 Advice.A8 Advice.A9
          NC.q_note_commit_m_x NC.q_note_commit_m_y
          a b c d e f g h)).
  Proof.
    pose proof (holds_facts Γ Hcircuit) as Hfacts.
    unfold Garden.Orchard.circuit.synthesize in Hfacts.
    do 9 apply interpret_layouter_facts_bind_right in Hfacts.
    apply interpret_layouter_facts_bind_left in Hfacts.
    unfold Garden.Orchard.circuit.synthesize_note_commit_new in Hfacts.
    do 4 apply interpret_layouter_facts_bind_right in Hfacts.
    apply interpret_layouter_facts_bind_left in Hfacts.
    apply interpret_layouter_facts_in_namespace in Hfacts.
    unfold NC.synthesize_new, NC.synthesize_instance in Hfacts.
    do 17 apply interpret_layouter_facts_bind_right in Hfacts.
    apply interpret_layouter_facts_bind_left in Hfacts.
    apply interpret_layouter_facts_in_namespace in Hfacts.
    apply interpret_layouter_facts_bind_right in Hfacts.
    apply interpret_layouter_facts_bind_left in Hfacts.
    apply interpret_layouter_facts_in_namespace in Hfacts.
    unfold SChip.synthesize_hash_to_point_note_commit_2 in Hfacts.
    apply interpret_layouter_facts_add_region in Hfacts.
    do 8 eexists.
    exact Hfacts.
  Qed.

  (** The point read off the output cells (A5/A8 at row 109)
      of the new-note hash-to-point region is [sinsemilla_hash_to_point] of
      the NoteCommit domain point over the region's 109 grid words —
      conditional on the incomplete-add nondegeneracy of that word list
      (the [merkle_layer_ok] precedent; an unconditional form is refutable
      because the incomplete-add gradients are free on the exceptional
      cases). *)
  Theorem note_commit_new_hash_point_correct
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (Hnondeg :
        SinsemillaHash.nondegenerate note_commit_Q
          (note_commit_new_words Γ)) :
    {|
      Point.x :=
        UnOp.from (eval_cell Γ
          (Garden.Halo2.Synthesis.Cell.advice new_hash_region Advice.A5 109));
      Point.y :=
        UnOp.from (eval_cell Γ
          (Garden.Halo2.Synthesis.Cell.advice new_hash_region Advice.A8 109));
    |} =
      SinsemillaSpec.sinsemilla_hash_to_point
        (OrchardSpec.note_commit_q orchard_circuit_params)
        (note_commit_new_words Γ).
  Proof.
    pose proof (holds_gates Γ Hcircuit) as Hgates.
    pose proof (generator_table_facts Γ Hcircuit) as Hload.
    destruct (new_hash_region_facts Γ Hcircuit)
      as (a & b & c & d & e & f & g & h & Hhash).
    (* Seed facts: [q_sinsemilla4] selector, fixed [y_q], constant [x_q]. *)
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
    (* The eight piece schedules: a b c d e f g h at offsets
       0 25 26 51 57 58 83 108 with word counts 25 1 25 6 1 25 25 1. *)
    pose proof Hhash as HpA.
    do 3 apply interpret_region_facts_bind_right in HpA.
    apply interpret_region_facts_bind_left in HpA.
    apply hash_piece_schedule in HpA.
    destruct HpA as (HselA & HstepA & HlastA).
    pose proof Hhash as HpB.
    do 4 apply interpret_region_facts_bind_right in HpB.
    apply interpret_region_facts_bind_left in HpB.
    apply hash_piece_schedule in HpB.
    destruct HpB as (HselB & HstepB & HlastB).
    pose proof Hhash as HpC.
    do 5 apply interpret_region_facts_bind_right in HpC.
    apply interpret_region_facts_bind_left in HpC.
    apply hash_piece_schedule in HpC.
    destruct HpC as (HselC & HstepC & HlastC).
    pose proof Hhash as HpD.
    do 6 apply interpret_region_facts_bind_right in HpD.
    apply interpret_region_facts_bind_left in HpD.
    apply hash_piece_schedule in HpD.
    destruct HpD as (HselD & HstepD & HlastD).
    pose proof Hhash as HpE.
    do 7 apply interpret_region_facts_bind_right in HpE.
    apply interpret_region_facts_bind_left in HpE.
    apply hash_piece_schedule in HpE.
    destruct HpE as (HselE & HstepE & HlastE).
    pose proof Hhash as HpF.
    do 8 apply interpret_region_facts_bind_right in HpF.
    apply interpret_region_facts_bind_left in HpF.
    apply hash_piece_schedule in HpF.
    destruct HpF as (HselF & HstepF & HlastF).
    pose proof Hhash as HpG.
    do 9 apply interpret_region_facts_bind_right in HpG.
    apply interpret_region_facts_bind_left in HpG.
    apply hash_piece_schedule in HpG.
    destruct HpG as (HselG & HstepG & HlastG).
    pose proof Hhash as HpH.
    do 10 apply interpret_region_facts_bind_right in HpH.
    apply interpret_region_facts_bind_left in HpH.
    apply hash_piece_schedule in HpH.
    destruct HpH as (HselH & HstepH & HlastH).
    clear Hhash.
    (* Boundary [q_s2] values: the last row of each piece. *)
    pose proof (HlastA ltac:(lia)) as Hq2_24.
    pose proof (HlastB ltac:(lia)) as Hq2_25.
    pose proof (HlastC ltac:(lia)) as Hq2_50.
    pose proof (HlastD ltac:(lia)) as Hq2_56.
    pose proof (HlastE ltac:(lia)) as Hq2_57.
    pose proof (HlastF ltac:(lia)) as Hq2_82.
    pose proof (HlastG ltac:(lia)) as Hq2_107.
    pose proof (HlastH ltac:(lia)) as Hq2_108.
    clear HlastA HlastB HlastC HlastD HlastE HlastF HlastG HlastH.
    (* Row schedules assembled across the eight pieces. *)
    assert (Hsel : forall j : nat, (j < 109)%nat ->
        Γ ⊢ ⟦ Expression.Selector Selector.QSinsemilla1_2 ⟧
          (new_hash_region, Z.of_nat j) = 1).
    { intros j Hj.
      apply SinsemillaHash.enabled_eq_one.
      destruct (Nat.lt_ge_cases j 25) as [Hc1 | Hc1].
      { replace (Z.of_nat j) with (0 + Z.of_nat j) by lia.
        apply HselA; lia. }
      destruct (Nat.lt_ge_cases j 26) as [Hc2 | Hc2].
      { replace (Z.of_nat j) with (25 + Z.of_nat (j - 25)) by lia.
        apply HselB; lia. }
      destruct (Nat.lt_ge_cases j 51) as [Hc3 | Hc3].
      { replace (Z.of_nat j) with (26 + Z.of_nat (j - 26)) by lia.
        apply HselC; lia. }
      destruct (Nat.lt_ge_cases j 57) as [Hc4 | Hc4].
      { replace (Z.of_nat j) with (51 + Z.of_nat (j - 51)) by lia.
        apply HselD; lia. }
      destruct (Nat.lt_ge_cases j 58) as [Hc5 | Hc5].
      { replace (Z.of_nat j) with (57 + Z.of_nat (j - 57)) by lia.
        apply HselE; lia. }
      destruct (Nat.lt_ge_cases j 83) as [Hc6 | Hc6].
      { replace (Z.of_nat j) with (58 + Z.of_nat (j - 58)) by lia.
        apply HselF; lia. }
      destruct (Nat.lt_ge_cases j 108) as [Hc7 | Hc7].
      { replace (Z.of_nat j) with (83 + Z.of_nat (j - 83)) by lia.
        apply HselG; lia. }
      replace (Z.of_nat j) with (108 + Z.of_nat (j - 108)) by lia.
      apply HselH; lia. }
    assert (Hq2_one : forall j : nat, (j < 109)%nat ->
        j <> 24%nat -> j <> 25%nat -> j <> 50%nat -> j <> 56%nat ->
        j <> 57%nat -> j <> 82%nat -> j <> 107%nat -> j <> 108%nat ->
        Γ.(Assignment.fixed) Fixed.QSinsemilla2_2 new_hash_region
          (Z.of_nat j) = 1).
    { intros j Hj H24 H25 H50 H56 H57 H82 H107 H108.
      destruct (Nat.lt_ge_cases j 25) as [Hc1 | Hc1].
      { replace (Z.of_nat j) with (0 + Z.of_nat j) by lia.
        apply HstepA; lia. }
      destruct (Nat.lt_ge_cases j 51) as [Hc3 | Hc3].
      { replace (Z.of_nat j) with (26 + Z.of_nat (j - 26)) by lia.
        apply HstepC; lia. }
      destruct (Nat.lt_ge_cases j 57) as [Hc4 | Hc4].
      { replace (Z.of_nat j) with (51 + Z.of_nat (j - 51)) by lia.
        apply HstepD; lia. }
      destruct (Nat.lt_ge_cases j 83) as [Hc6 | Hc6].
      { replace (Z.of_nat j) with (58 + Z.of_nat (j - 58)) by lia.
        apply HstepF; lia. }
      replace (Z.of_nat j) with (83 + Z.of_nat (j - 83)) by lia.
      apply HstepG; lia. }
    clear HselA HselB HselC HselD HselE HselF HselG HselH
      HstepA HstepB HstepC HstepD HstepE HstepF HstepG HstepH.
    (* [q_s3 = 0] below the final row, [q_s3 = 2] on row 108. *)
    assert (Hq3 : forall j : nat, (S j < 109)%nat ->
        Γ ⊢ ⟦ SChip.q_s3 Fixed.QSinsemilla2_2 ⟧
          (new_hash_region, Z.of_nat j) = 0).
    { intros j Hj.
      destruct (Nat.eq_dec j 24) as [-> | H24].
      { apply (q_s3_eval_zero Γ Fixed.QSinsemilla2_2 new_hash_region
          (Z.of_nat 24) 0); [exact Hq2_24 | left; reflexivity]. }
      destruct (Nat.eq_dec j 25) as [-> | H25].
      { apply (q_s3_eval_zero Γ Fixed.QSinsemilla2_2 new_hash_region
          (Z.of_nat 25) 0); [exact Hq2_25 | left; reflexivity]. }
      destruct (Nat.eq_dec j 50) as [-> | H50].
      { apply (q_s3_eval_zero Γ Fixed.QSinsemilla2_2 new_hash_region
          (Z.of_nat 50) 0); [exact Hq2_50 | left; reflexivity]. }
      destruct (Nat.eq_dec j 56) as [-> | H56].
      { apply (q_s3_eval_zero Γ Fixed.QSinsemilla2_2 new_hash_region
          (Z.of_nat 56) 0); [exact Hq2_56 | left; reflexivity]. }
      destruct (Nat.eq_dec j 57) as [-> | H57].
      { apply (q_s3_eval_zero Γ Fixed.QSinsemilla2_2 new_hash_region
          (Z.of_nat 57) 0); [exact Hq2_57 | left; reflexivity]. }
      destruct (Nat.eq_dec j 82) as [-> | H82].
      { apply (q_s3_eval_zero Γ Fixed.QSinsemilla2_2 new_hash_region
          (Z.of_nat 82) 0); [exact Hq2_82 | left; reflexivity]. }
      destruct (Nat.eq_dec j 107) as [-> | H107].
      { apply (q_s3_eval_zero Γ Fixed.QSinsemilla2_2 new_hash_region
          (Z.of_nat 107) 0); [exact Hq2_107 | left; reflexivity]. }
      apply (q_s3_eval_zero Γ Fixed.QSinsemilla2_2 new_hash_region
        (Z.of_nat j) 1); [apply Hq2_one; lia | right; reflexivity]. }
    assert (Hq3_final :
        Γ ⊢ ⟦ SChip.q_s3 Fixed.QSinsemilla2_2 ⟧
          (new_hash_region, Z.of_nat (109 - 1)) = 2).
    { apply q_s3_eval_two. exact Hq2_108. }
    clear Hq2_24 Hq2_25 Hq2_50 Hq2_56 Hq2_57 Hq2_82 Hq2_107 Hq2_108 Hq2_one.
    (* The two gates of the region, from [satisfies_gates]. *)
    assert (Hgate_sin : forall row : Z,
        Γ ⊢ ⟦ SChip.sinsemilla_gate
          Selector.QSinsemilla1_2 Fixed.QSinsemilla2_2
          Advice.A5 Advice.A6 Advice.A8 Advice.A9 ⟧
        (new_hash_region, row)).
    { intros row.
      apply (satisfies_gates_at Γ
        (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)
        (SChip.sinsemilla_gate
          Selector.QSinsemilla1_2 Fixed.QSinsemilla2_2
          Advice.A5 Advice.A6 Advice.A8 Advice.A9)
        new_hash_region
        row
        ltac:(cbn; repeat (first [left; reflexivity | right]))
        Hgates). }
    assert (Hgate_yq :
        Γ ⊢ ⟦ SChip.initial_y_q_gate
          Selector.QSinsemilla4_2 Fixed.LagrangeCoeffs1
          Advice.A5 Advice.A6 Advice.A8 Advice.A9 ⟧
        (new_hash_region, 0)).
    { apply (satisfies_gates_at Γ
        (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)
        (SChip.initial_y_q_gate
          Selector.QSinsemilla4_2 Fixed.LagrangeCoeffs1
          Advice.A5 Advice.A6 Advice.A8 Advice.A9)
        new_hash_region
        0
        ltac:(cbn; repeat (first [left; reflexivity | right]))
        Hgates). }
    (* Seed: the accumulator at row 0 is the domain point. *)
    pose proof (InitialYQ.deterministic Γ new_hash_region 0
        Selector.QSinsemilla4_2 Fixed.LagrangeCoeffs1
        Advice.A5 Advice.A6 Advice.A8 Advice.A9
        (enabled_nonzero Γ Selector.QSinsemilla4_2 _ 0 HselY) Hgate_yq) as Hy.
    rewrite (fixed_expression_eq Γ Fixed.LagrangeCoeffs1 _ 0
      NC.q_note_commit_m_y HfixY) in Hy.
    pose proof (SinsemillaHash.acc_at_init Γ Advice.A5 Advice.A6 Advice.A8
      Advice.A9 _ 0 (UnOp.from NC.q_note_commit_m_y) Hy) as Hacc0.
    rewrite (eval_advice_cur_cell Γ _ Advice.A5 0) in Hacc0.
    rewrite HconstX in Hacc0.
    rewrite q_note_commit_m_x_reduced in Hacc0.
    rewrite FieldRewrite.from_from in Hacc0.
    rewrite q_note_commit_m_y_reduced in Hacc0.
    (* The 109-round point fold at the note-commit schedule. *)
    pose proof (SinsemillaHashFold.hash_to_point_rows_correct Γ
        new_hash_region
        Selector.QSinsemilla1_2 Fixed.QSinsemilla2_2
        Advice.A5 Advice.A6 Advice.A7 Advice.A8 Advice.A9
        109%nat ltac:(lia) note_commit_Q
        Hload Hsel (fun j _ => Hgate_sin (Z.of_nat j))
        (fun j _ =>
          generator_table_lookup_holds_2 Γ Hcircuit new_hash_region
            (Z.of_nat j))
        Hq3 Hq3_final Hacc0 Hnondeg) as Hpoint.
    change (Z.of_nat 109) with 109 in Hpoint.
    rewrite (eval_advice_cur_cell Γ new_hash_region Advice.A5 109) in Hpoint.
    rewrite (eval_advice_cur_cell Γ new_hash_region Advice.A8 109) in Hpoint.
    exact Hpoint.
  Qed.
End NoteCommitNewHash.
