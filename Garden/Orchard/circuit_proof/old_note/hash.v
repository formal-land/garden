(** * The old-note Sinsemilla hash fold.

    The hash-to-point output point of [note_commit.synthesize_old] (the
    [Which.Old] instance, Sinsemilla variant 1, synthesized through
    [synthesize_hash_to_point_note_commit]) equals
    [SinsemillaSpec.sinsemilla_hash_to_point] of the NoteCommit domain point
    [note_commit_q orchard_circuit_params] applied to the 109 grid words of
    the region's running-sum column, from a satisfying assignment.  The
    [Which.New] counterpart is [NoteCommitNewHash.note_commit_new_hash_point_correct]
    ([circuit_proof/note_commit/hash.v]); the [Which.Old] instance runs at the
    variant-1 constants ([QSinsemilla1_1]/[QSinsemilla4_1]/[QSinsemilla2_1]/
    [LagrangeCoeffs0], columns [A0]/[A1]/[A2]/[A3]/[A4]), the column set of
    the per-layer Merkle lane ([circuit_proof/merkle.v],
    [generator_table_lookup_holds_1]).  Piece offsets/word counts, boundary
    rows and the final row are the shared eight-piece [a..h] schedule of
    [synthesize_hash_to_point_note_commit_region]: (0,25) (25,1) (26,25)
    (51,6) (57,1) (58,25) (83,25) (108,1), boundaries {24, 25, 50, 56, 57,
    82, 107}, final row 108.

    The region facts come from [OldNoteWords.old_hash_facts]
    ([circuit_proof/old_note/words.v]), which pins the eight message-piece
    cells to the [Which.Old] witness regions (column [A6]).

    The incomplete-add nondegeneracy of the witnessed 109-word message is the
    explicit side condition [SinsemillaHash.nondegenerate], exactly as in the
    Merkle precedent ([merkle_layer_ok]) and the [Which.New] lane. *)

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
Require Import Garden.Orchard.protocol_spec.
Require Import Garden.Orchard.circuit_proof.merkle.
Require Import Garden.Orchard.circuit_proof.note_commit.hash.
Require Import Garden.Orchard.circuit_proof.old_note.words.
Require Import Garden.Field.Field.
Require Import Garden.Field.Lemmas.
Require Import Garden.Plonky3.M.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Lists.List.

#[local] Existing Instance Primes.PallasPIsPrime.

Global Open Scope Z_scope.

Module NC := Garden.Orchard.circuit.note_commit.
Module SChip := Garden.Halo2.halo2_gadgets.sinsemilla.chip.

Module OldNoteHash.
  Import OrchardActionMerkle.

  Local Notation Holds Γ :=
    (circuit_holds Γ
      Garden.Orchard.circuit.synthesize
      (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)).

  (** The output cells of the old-note hash synthesis: the [HashResult]
      record returned by [synthesize_hash_to_point_note_commit] (variant 1)
      reads the point off [x_a]/[lambda_1] (columns A0/A3) at row 109 — the
      cells the old-note complete-add region copies its [m] input from. *)
  Lemma hash_result_x_cell
      (a b c d e f g h : Garden.Halo2.Synthesis.Cell.t columns RegionId.t) :
    (layouter_value
      (SChip.synthesize_hash_to_point_note_commit OldNoteWords.HR
        NC.q_note_commit_m_x NC.q_note_commit_m_y
        a b c d e f g h)).(SChip.HashResult.x) =
      Garden.Halo2.Synthesis.Cell.advice OldNoteWords.HR Advice.A0 109.
  Proof. reflexivity. Qed.

  Lemma hash_result_y_cell
      (a b c d e f g h : Garden.Halo2.Synthesis.Cell.t columns RegionId.t) :
    (layouter_value
      (SChip.synthesize_hash_to_point_note_commit OldNoteWords.HR
        NC.q_note_commit_m_x NC.q_note_commit_m_y
        a b c d e f g h)).(SChip.HashResult.y) =
      Garden.Halo2.Synthesis.Cell.advice OldNoteWords.HR Advice.A3 109.
  Proof. reflexivity. Qed.

  (** The point read off the output cells (A0/A3 at row 109)
      of the old-note hash-to-point region is [sinsemilla_hash_to_point] of
      the NoteCommit domain point over the region's 109 grid words —
      conditional on the incomplete-add nondegeneracy of that word list
      (the [merkle_layer_ok] precedent; an unconditional form is refutable
      because the incomplete-add gradients are free on the exceptional
      cases). *)
  Theorem note_commit_old_hash_point_correct
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (Hnondeg :
        SinsemillaHash.nondegenerate NoteCommitNewHash.note_commit_Q
          (OldNoteWords.old_note_words Γ)) :
    {|
      Point.x :=
        UnOp.from (eval_cell Γ
          (Garden.Halo2.Synthesis.Cell.advice OldNoteWords.HR Advice.A0 109));
      Point.y :=
        UnOp.from (eval_cell Γ
          (Garden.Halo2.Synthesis.Cell.advice OldNoteWords.HR Advice.A3 109));
    |} =
      SinsemillaSpec.sinsemilla_hash_to_point
        (OrchardSpec.note_commit_q orchard_circuit_params)
        (OldNoteWords.old_note_words Γ).
  Proof.
    pose proof (holds_gates Γ Hcircuit) as Hgates.
    pose proof (generator_table_facts Γ Hcircuit) as Hload.
    pose proof (OldNoteWords.old_hash_facts Γ Hcircuit) as Hhash.
    unfold SChip.synthesize_hash_to_point_note_commit_region in Hhash.
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
    apply NoteCommitNewHash.hash_piece_schedule in HpA.
    destruct HpA as (HselA & HstepA & HlastA).
    pose proof Hhash as HpB.
    do 4 apply interpret_region_facts_bind_right in HpB.
    apply interpret_region_facts_bind_left in HpB.
    apply NoteCommitNewHash.hash_piece_schedule in HpB.
    destruct HpB as (HselB & HstepB & HlastB).
    pose proof Hhash as HpC.
    do 5 apply interpret_region_facts_bind_right in HpC.
    apply interpret_region_facts_bind_left in HpC.
    apply NoteCommitNewHash.hash_piece_schedule in HpC.
    destruct HpC as (HselC & HstepC & HlastC).
    pose proof Hhash as HpD.
    do 6 apply interpret_region_facts_bind_right in HpD.
    apply interpret_region_facts_bind_left in HpD.
    apply NoteCommitNewHash.hash_piece_schedule in HpD.
    destruct HpD as (HselD & HstepD & HlastD).
    pose proof Hhash as HpE.
    do 7 apply interpret_region_facts_bind_right in HpE.
    apply interpret_region_facts_bind_left in HpE.
    apply NoteCommitNewHash.hash_piece_schedule in HpE.
    destruct HpE as (HselE & HstepE & HlastE).
    pose proof Hhash as HpF.
    do 8 apply interpret_region_facts_bind_right in HpF.
    apply interpret_region_facts_bind_left in HpF.
    apply NoteCommitNewHash.hash_piece_schedule in HpF.
    destruct HpF as (HselF & HstepF & HlastF).
    pose proof Hhash as HpG.
    do 9 apply interpret_region_facts_bind_right in HpG.
    apply interpret_region_facts_bind_left in HpG.
    apply NoteCommitNewHash.hash_piece_schedule in HpG.
    destruct HpG as (HselG & HstepG & HlastG).
    pose proof Hhash as HpH.
    do 10 apply interpret_region_facts_bind_right in HpH.
    apply interpret_region_facts_bind_left in HpH.
    apply NoteCommitNewHash.hash_piece_schedule in HpH.
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
        Γ ⊢ ⟦ Expression.Selector Selector.QSinsemilla1_1 ⟧
          (OldNoteWords.HR, Z.of_nat j) = 1).
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
        Γ.(Assignment.fixed) Fixed.QSinsemilla2_1 OldNoteWords.HR
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
        Γ ⊢ ⟦ SChip.q_s3 Fixed.QSinsemilla2_1 ⟧
          (OldNoteWords.HR, Z.of_nat j) = 0).
    { intros j Hj.
      destruct (Nat.eq_dec j 24) as [-> | H24].
      { apply (q_s3_eval_zero Γ Fixed.QSinsemilla2_1 OldNoteWords.HR
          (Z.of_nat 24) 0); [exact Hq2_24 | left; reflexivity]. }
      destruct (Nat.eq_dec j 25) as [-> | H25].
      { apply (q_s3_eval_zero Γ Fixed.QSinsemilla2_1 OldNoteWords.HR
          (Z.of_nat 25) 0); [exact Hq2_25 | left; reflexivity]. }
      destruct (Nat.eq_dec j 50) as [-> | H50].
      { apply (q_s3_eval_zero Γ Fixed.QSinsemilla2_1 OldNoteWords.HR
          (Z.of_nat 50) 0); [exact Hq2_50 | left; reflexivity]. }
      destruct (Nat.eq_dec j 56) as [-> | H56].
      { apply (q_s3_eval_zero Γ Fixed.QSinsemilla2_1 OldNoteWords.HR
          (Z.of_nat 56) 0); [exact Hq2_56 | left; reflexivity]. }
      destruct (Nat.eq_dec j 57) as [-> | H57].
      { apply (q_s3_eval_zero Γ Fixed.QSinsemilla2_1 OldNoteWords.HR
          (Z.of_nat 57) 0); [exact Hq2_57 | left; reflexivity]. }
      destruct (Nat.eq_dec j 82) as [-> | H82].
      { apply (q_s3_eval_zero Γ Fixed.QSinsemilla2_1 OldNoteWords.HR
          (Z.of_nat 82) 0); [exact Hq2_82 | left; reflexivity]. }
      destruct (Nat.eq_dec j 107) as [-> | H107].
      { apply (q_s3_eval_zero Γ Fixed.QSinsemilla2_1 OldNoteWords.HR
          (Z.of_nat 107) 0); [exact Hq2_107 | left; reflexivity]. }
      apply (q_s3_eval_zero Γ Fixed.QSinsemilla2_1 OldNoteWords.HR
        (Z.of_nat j) 1); [apply Hq2_one; lia | right; reflexivity]. }
    assert (Hq3_final :
        Γ ⊢ ⟦ SChip.q_s3 Fixed.QSinsemilla2_1 ⟧
          (OldNoteWords.HR, Z.of_nat (109 - 1)) = 2).
    { apply q_s3_eval_two. exact Hq2_108. }
    clear Hq2_24 Hq2_25 Hq2_50 Hq2_56 Hq2_57 Hq2_82 Hq2_107 Hq2_108 Hq2_one.
    (* The two gates of the region, from [satisfies_gates]. *)
    assert (Hgate_sin : forall row : Z,
        Γ ⊢ ⟦ SChip.sinsemilla_gate
          Selector.QSinsemilla1_1 Fixed.QSinsemilla2_1
          Advice.A0 Advice.A1 Advice.A3 Advice.A4 ⟧
        (OldNoteWords.HR, row)).
    { intros row.
      apply (satisfies_gates_at Γ
        (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)
        (SChip.sinsemilla_gate
          Selector.QSinsemilla1_1 Fixed.QSinsemilla2_1
          Advice.A0 Advice.A1 Advice.A3 Advice.A4)
        OldNoteWords.HR
        row
        ltac:(cbn; repeat (first [left; reflexivity | right]))
        Hgates). }
    assert (Hgate_yq :
        Γ ⊢ ⟦ SChip.initial_y_q_gate
          Selector.QSinsemilla4_1 Fixed.LagrangeCoeffs0
          Advice.A0 Advice.A1 Advice.A3 Advice.A4 ⟧
        (OldNoteWords.HR, 0)).
    { apply (satisfies_gates_at Γ
        (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)
        (SChip.initial_y_q_gate
          Selector.QSinsemilla4_1 Fixed.LagrangeCoeffs0
          Advice.A0 Advice.A1 Advice.A3 Advice.A4)
        OldNoteWords.HR
        0
        ltac:(cbn; repeat (first [left; reflexivity | right]))
        Hgates). }
    (* Seed: the accumulator at row 0 is the domain point. *)
    pose proof (InitialYQ.deterministic Γ OldNoteWords.HR 0
        Selector.QSinsemilla4_1 Fixed.LagrangeCoeffs0
        Advice.A0 Advice.A1 Advice.A3 Advice.A4
        (enabled_nonzero Γ Selector.QSinsemilla4_1 _ 0 HselY) Hgate_yq) as Hy.
    rewrite (fixed_expression_eq Γ Fixed.LagrangeCoeffs0 _ 0
      NC.q_note_commit_m_y HfixY) in Hy.
    pose proof (SinsemillaHash.acc_at_init Γ Advice.A0 Advice.A1 Advice.A3
      Advice.A4 _ 0 (UnOp.from NC.q_note_commit_m_y) Hy) as Hacc0.
    rewrite (eval_advice_cur_cell Γ _ Advice.A0 0) in Hacc0.
    rewrite HconstX in Hacc0.
    rewrite NoteCommitNewHash.q_note_commit_m_x_reduced in Hacc0.
    rewrite FieldRewrite.from_from in Hacc0.
    rewrite NoteCommitNewHash.q_note_commit_m_y_reduced in Hacc0.
    (* The 109-round point fold at the note-commit schedule. *)
    pose proof (SinsemillaHashFold.hash_to_point_rows_correct Γ
        OldNoteWords.HR
        Selector.QSinsemilla1_1 Fixed.QSinsemilla2_1
        Advice.A0 Advice.A1 Advice.A2 Advice.A3 Advice.A4
        109%nat ltac:(lia) NoteCommitNewHash.note_commit_Q
        Hload Hsel (fun j _ => Hgate_sin (Z.of_nat j))
        (fun j _ =>
          generator_table_lookup_holds_1 Γ Hcircuit OldNoteWords.HR
            (Z.of_nat j))
        Hq3 Hq3_final Hacc0 Hnondeg) as Hpoint.
    change (Z.of_nat 109) with 109 in Hpoint.
    rewrite (eval_advice_cur_cell Γ OldNoteWords.HR Advice.A0 109) in Hpoint.
    rewrite (eval_advice_cur_cell Γ OldNoteWords.HR Advice.A3 109) in Hpoint.
    exact Hpoint.
  Qed.
End OldNoteHash.
