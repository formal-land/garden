(** * The note-commit-old hashed words are the message

    The 109 grid words hashed by the [Which.Old] NoteCommit hash-to-point
    region (Sinsemilla variant 1: running-sum column [A2], word count under
    [Fixed.QSinsemilla2_1]) equal [OrchardSpec.note_commit_message] of the
    circuit's old-note reads: the witnessed [g_d_old] point
    ([WitnessInput.GDOld]), the witnessed [pk_d_old] point, the [VOld],
    [RhoOld] and [PsiOld] witness cells.

    The pk_d component: [synthesize_note_commit_old] receives the
    [AssignedPoint] returned by [synthesize_address_integrity], which is the
    WITNESSED [pk_d_old] point at
    [RegionId.AddressIntegrity AddressIntegrity.WitnessPkD] (A0/A1 at row 0 —
    exactly the cells [OrchardValidActionInputs.read_pk_d_old] reads), NOT
    the computed [[ivk] g_d_old] output of the variable-base mul.  So what
    the circuit enforces here is that the old-note message packs the
    witnessed [pk_d★_old]; the separate [AddressIntegrity.Equality] region
    (out of scope of this file) pins that witness to the computed point.
    This matches [OrchardValidActionInputs.old_note_commit_integrity]
    ([circuit_proof/valid_action_inputs.v]), whose conclusion is stated at
    [read_pk_d_old].

    Route (the [Which.New] mirror, [circuit_proof/note_commit/words.v]): the
    region's piece telescopes identify the eight [A6] piece cells with the
    digit sums of their word runs; the [message_piece_*]/[input_*]/
    [y_coordinate_checks] gates at the [Which.Old] regions force the
    [note_commit_proof.v] reconstructions; the running lookups supply the
    range facts that make each field-level decomposition an exact integer
    identity — the [+ 2^k - t_P] prime-check legs included; and
    [NoteCommitMessagePieces.hashed_words_of_note_commit_pieces] closes the
    word schedule.

    The one side condition ([old_note_short_lookup_ok]): the eleven
    short-lookup range cells ([b_0], [b_3], [d_2], [e_0], [e_1], [g_1],
    [h_0], and the [k_0]/[k_2] of both y-canonicity checks) lie in their bit
    ranges.  This is the same selector-plane idealization of the relational
    model as [note_commit_new_short_lookup_ok]: the halo2 short lookup
    constrains [z_cur] only where the [q_running] selector is 0, and the
    model pins selectors solely through the synthesis [SelectorOn] facts,
    leaving [QRunning] free at the short-range rows — so the short bound is
    underivable from [Holds] alone (see the [Which.New] file header and the
    [merkle_witness_ok] precedent). *)

Require Import Stdlib.Lists.List.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.ZArith.ZArith.
Require Import Garden.Halo2.main.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.lemmas.
Require Import Garden.Orchard.columns.
Require Garden.Orchard.circuit.
Require Garden.Orchard.circuit.note_commit.
Require Garden.Orchard.circuit.note_commit_proof.
Require Garden.Halo2.halo2_gadgets.sinsemilla.chip.
Require Import Garden.Halo2.halo2_gadgets.sinsemilla.chip_proof.
Require Import Garden.Halo2.halo2_gadgets.sinsemilla.hash_to_point_proof.
Require Import Garden.Halo2.halo2_gadgets.sinsemilla.spec.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.spec.
Require Import Garden.Orchard.protocol_spec.
Require Import Garden.Orchard.circuit_proof.inputs.
Require Import Garden.Orchard.circuit_proof.facts.
Require Import Garden.Orchard.circuit_proof.merkle.
Require Import Garden.Orchard.circuit_proof.base_field_canonicity.
Require Import Garden.Orchard.circuit_proof.note_commit.pieces.
Require Import Garden.Orchard.circuit_proof.note_commit.hash.
Require Import Garden.Field.Field.
Require Import Garden.Field.Lemmas.
Require Import Garden.Plonky3.M.

Import ListNotations.

#[local] Existing Instance Primes.PallasPIsPrime.

Global Open Scope Z_scope.

Module OldNoteWords.
  Import OrchardActionMerkle.

  Local Notation Holds Γ :=
    (circuit_holds Γ
      Garden.Orchard.circuit.synthesize
      (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)).

  (** ** Region and cell shorthands *)

  Definition ncr (r : RegionId.NoteCommit.t) : RegionId.t :=
    RegionId.NoteCommit RegionId.NoteCommit.Which.Old r.

  Definition nyr
      (s : RegionId.NoteCommit.YSubject.t)
      (r : RegionId.NoteCommit.YCanonicity.t) : RegionId.t :=
    ncr (RegionId.NoteCommit.YCanonicity s r).

  (** The [Which.Old] hash-to-point region. *)
  Definition HR : RegionId.t := ncr RegionId.NoteCommit.HashToPoint.

  Definition adv (r : RegionId.t) (c : Advice.t) (row : Z)
      : Garden.Halo2.Synthesis.Cell.t columns RegionId.t :=
    Garden.Halo2.Synthesis.Cell.advice r c row.

  (** Reduced cell value (matches how gates read advice cells). *)
  Definition val (Γ : Assignment.t columns RegionId.t)
      (c : Garden.Halo2.Synthesis.Cell.t columns RegionId.t) : Z :=
    UnOp.from (eval_cell Γ c).

  (** The message-input cells of [synthesize_note_commit_old]: the witnessed
      [g_d_old] point, the witnessed [pk_d_old] point (the return value of
      [synthesize_address_integrity]), and the [VOld]/[RhoOld]/[PsiOld]
      witness cells. *)

  (** [synthesize_address_integrity] returns the WITNESSED [pk_d_old] point
      (the [WitnessPkD] region), independent of its arguments. *)
  Lemma address_integrity_value_eq
      (ak nk : Garden.Halo2.Synthesis.Cell.t columns RegionId.t)
      (g_d_old : Garden.Orchard.circuit.AssignedPoint.t) :
    layouter_value
      (Garden.Orchard.circuit.synthesize_address_integrity ak nk g_d_old) =
    {|
      Garden.Orchard.circuit.AssignedPoint.x :=
        adv (RegionId.AddressIntegrity RegionId.AddressIntegrity.WitnessPkD)
          Advice.A0 0;
      Garden.Orchard.circuit.AssignedPoint.y :=
        adv (RegionId.AddressIntegrity RegionId.AddressIntegrity.WitnessPkD)
          Advice.A1 0;
    |}.
  Proof. reflexivity. Qed.

  (** The message word consumed at a hash-region row (variant 1: word count
      under [QSinsemilla2_1], running-sum column [A2]). *)
  Definition w (Γ : Assignment.t columns RegionId.t) (row : Z) : Z :=
    SinsemillaHash.word_at Γ Fixed.QSinsemilla2_1 Advice.A2 HR row.

  (** Advice at next rotation is advice at the next row. *)
  Lemma advice_next_cur
      (Γ : Assignment.t columns RegionId.t)
      (region : RegionId.t) (column : Advice.t) (row : Z) :
    Γ ⊢ ⟦ Expression.Advice column Rotation.next ⟧ (region, row) =
      Γ ⊢ ⟦ Expression.Advice column Rotation.cur ⟧ (region, row + 1).
  Proof.
    rewrite eval_advice_next_cell, eval_advice_cur_cell.
    reflexivity.
  Qed.

  (** Advice evaluations are reduced. *)
  Lemma advice_reduced
      (Γ : Assignment.t columns RegionId.t)
      (region : RegionId.t) (column : Advice.t) (row : Z) :
    UnOp.from (Γ ⊢ ⟦ Expression.Advice column Rotation.cur ⟧ (region, row)) =
      Γ ⊢ ⟦ Expression.Advice column Rotation.cur ⟧ (region, row).
  Proof.
    rewrite eval_advice_cur_cell.
    apply FieldRewrite.from_from.
  Qed.

  (** ** Fact extraction: down to [note_commit.synthesize_old]

      The peel along [synthesize → synthesize_note_commit_old →
      note_commit.synthesize_old] (synthesize bind 8; inside, bind 0 is the
      ["rcm_old"] namespace nop and bind 1 the commitment computation), with
      the seven message-input cells concrete: the witnessed [g_d_old] point
      cells, the witnessed [pk_d_old] point cells and the [VOld]/[RhoOld]/
      [PsiOld] witness-input cells. *)

  Lemma old_instance_facts
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ) :
    interpret_facts Γ (layouter_facts
      (Garden.Orchard.circuit.note_commit.synthesize_old
        (adv (RegionId.WitnessInput RegionId.WitnessInput.GDOld) Advice.A0 0)
        (adv (RegionId.WitnessInput RegionId.WitnessInput.GDOld) Advice.A1 0)
        (adv (RegionId.AddressIntegrity RegionId.AddressIntegrity.WitnessPkD)
          Advice.A0 0)
        (adv (RegionId.AddressIntegrity RegionId.AddressIntegrity.WitnessPkD)
          Advice.A1 0)
        (adv (RegionId.WitnessInput RegionId.WitnessInput.VOld) Advice.A0 0)
        (adv (RegionId.WitnessInput RegionId.WitnessInput.RhoOld) Advice.A0 0)
        (adv (RegionId.WitnessInput RegionId.WitnessInput.PsiOld)
          Advice.A0 0))).
  Proof.
    pose proof (holds_facts Γ Hcircuit) as Hfacts.
    unfold Garden.Orchard.circuit.synthesize in Hfacts.
    do 8 apply interpret_layouter_facts_bind_right in Hfacts.
    apply interpret_layouter_facts_bind_left in Hfacts.
    unfold Garden.Orchard.circuit.synthesize_note_commit_old in Hfacts.
    apply interpret_layouter_facts_bind_right in Hfacts.
    apply interpret_layouter_facts_bind_left in Hfacts.
    apply interpret_layouter_facts_in_namespace in Hfacts.
    exact Hfacts.
  Qed.

  (** ** Per-region facts of the [Which.Old] NoteCommit instance

      Each lemma peels [old_instance_facts] down to one region of
      [note_commit.synthesize_instance] (bind [k] reached by [k - 1]
      [bind_right]s), and returns the region's selector and copy facts
      with the source cells concrete.  The witness piece cells live on
      [A6] ([piece_column] with [use_second_sinsemilla = false]); the
      hash-region running-sum cells on [A2]. *)

  Tactic Notation "peel_instance" hyp(H) integer(k) :=
    unfold Garden.Orchard.circuit.note_commit.synthesize_old,
      Garden.Orchard.circuit.note_commit.synthesize_instance in H;
    do k (apply interpret_layouter_facts_bind_right in H);
    apply interpret_layouter_facts_bind_left in H.

  Lemma msg_b_facts
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ) :
    Γ.(Assignment.selector) Selector.QNoteCommitOldB
      (ncr RegionId.NoteCommit.MessagePieceB) 0 = 1 /\
    eval_cell Γ (adv (ncr RegionId.NoteCommit.MessagePieceB) Advice.A6 0) =
      eval_cell Γ (adv (ncr RegionId.NoteCommit.WitnessB) Advice.A6 0) /\
    eval_cell Γ (adv (ncr RegionId.NoteCommit.MessagePieceB) Advice.A7 0) =
      eval_cell Γ (adv (ncr RegionId.NoteCommit.RangeB0) Advice.A9 0) /\
    eval_cell Γ (adv (ncr RegionId.NoteCommit.MessagePieceB) Advice.A7 1) =
      eval_cell Γ
        (adv (nyr RegionId.NoteCommit.YSubject.GD
          RegionId.NoteCommit.YCanonicity.Gate) Advice.A6 0) /\
    eval_cell Γ (adv (ncr RegionId.NoteCommit.MessagePieceB) Advice.A8 1) =
      eval_cell Γ (adv (ncr RegionId.NoteCommit.RangeB3) Advice.A9 0).
  Proof.
    pose proof (old_instance_facts Γ Hcircuit) as H.
    peel_instance H 22.
    apply interpret_layouter_facts_add_region in H.
    cbn [region_facts interpret_facts interpret_fact List.app] in H.
    destruct H as (H1 & H2 & H3 & H4 & H5 & _).
    repeat split; assumption.
  Qed.

  Lemma msg_d_facts
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ) :
    Γ.(Assignment.selector) Selector.QNoteCommitOldD
      (ncr RegionId.NoteCommit.MessagePieceD) 0 = 1 /\
    eval_cell Γ (adv (ncr RegionId.NoteCommit.MessagePieceD) Advice.A6 0) =
      eval_cell Γ (adv (ncr RegionId.NoteCommit.WitnessD) Advice.A6 0) /\
    eval_cell Γ (adv (ncr RegionId.NoteCommit.MessagePieceD) Advice.A8 0) =
      eval_cell Γ
        (adv (nyr RegionId.NoteCommit.YSubject.PkD
          RegionId.NoteCommit.YCanonicity.Gate) Advice.A6 0) /\
    eval_cell Γ (adv (ncr RegionId.NoteCommit.MessagePieceD) Advice.A7 1) =
      eval_cell Γ (adv (ncr RegionId.NoteCommit.RangeD2) Advice.A9 0) /\
    eval_cell Γ (adv (ncr RegionId.NoteCommit.MessagePieceD) Advice.A8 1) =
      eval_cell Γ (adv HR Advice.A2 52).
  Proof.
    pose proof (old_instance_facts Γ Hcircuit) as H.
    peel_instance H 23.
    apply interpret_layouter_facts_add_region in H.
    cbn [region_facts interpret_facts interpret_fact List.app] in H.
    destruct H as (H1 & H2 & H3 & H4 & H5 & _).
    repeat split; assumption.
  Qed.

  Lemma msg_e_facts
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ) :
    Γ.(Assignment.selector) Selector.QNoteCommitOldE
      (ncr RegionId.NoteCommit.MessagePieceE) 0 = 1 /\
    eval_cell Γ (adv (ncr RegionId.NoteCommit.MessagePieceE) Advice.A6 0) =
      eval_cell Γ (adv (ncr RegionId.NoteCommit.WitnessE) Advice.A6 0) /\
    eval_cell Γ (adv (ncr RegionId.NoteCommit.MessagePieceE) Advice.A7 0) =
      eval_cell Γ (adv (ncr RegionId.NoteCommit.RangeE0) Advice.A9 0) /\
    eval_cell Γ (adv (ncr RegionId.NoteCommit.MessagePieceE) Advice.A8 0) =
      eval_cell Γ (adv (ncr RegionId.NoteCommit.RangeE1) Advice.A9 0).
  Proof.
    pose proof (old_instance_facts Γ Hcircuit) as H.
    peel_instance H 24.
    apply interpret_layouter_facts_add_region in H.
    cbn [region_facts interpret_facts interpret_fact List.app] in H.
    destruct H as (H1 & H2 & H3 & H4 & _).
    repeat split; assumption.
  Qed.

  Lemma msg_g_facts
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ) :
    Γ.(Assignment.selector) Selector.QNoteCommitOldG
      (ncr RegionId.NoteCommit.MessagePieceG) 0 = 1 /\
    eval_cell Γ (adv (ncr RegionId.NoteCommit.MessagePieceG) Advice.A6 0) =
      eval_cell Γ (adv (ncr RegionId.NoteCommit.WitnessG) Advice.A6 0) /\
    eval_cell Γ (adv (ncr RegionId.NoteCommit.MessagePieceG) Advice.A6 1) =
      eval_cell Γ (adv (ncr RegionId.NoteCommit.RangeG1) Advice.A9 0) /\
    eval_cell Γ (adv (ncr RegionId.NoteCommit.MessagePieceG) Advice.A7 1) =
      eval_cell Γ (adv HR Advice.A2 84).
  Proof.
    pose proof (old_instance_facts Γ Hcircuit) as H.
    peel_instance H 25.
    apply interpret_layouter_facts_add_region in H.
    cbn [region_facts interpret_facts interpret_fact List.app] in H.
    destruct H as (H1 & H2 & H3 & H4 & _).
    repeat split; assumption.
  Qed.

  Lemma msg_h_facts
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ) :
    Γ.(Assignment.selector) Selector.QNoteCommitOldH
      (ncr RegionId.NoteCommit.MessagePieceH) 0 = 1 /\
    eval_cell Γ (adv (ncr RegionId.NoteCommit.MessagePieceH) Advice.A6 0) =
      eval_cell Γ (adv (ncr RegionId.NoteCommit.WitnessH) Advice.A6 0) /\
    eval_cell Γ (adv (ncr RegionId.NoteCommit.MessagePieceH) Advice.A7 0) =
      eval_cell Γ (adv (ncr RegionId.NoteCommit.RangeH0) Advice.A9 0).
  Proof.
    pose proof (old_instance_facts Γ Hcircuit) as H.
    peel_instance H 26.
    apply interpret_layouter_facts_add_region in H.
    cbn [region_facts interpret_facts interpret_fact List.app] in H.
    destruct H as (H1 & H2 & H3 & _).
    repeat split; assumption.
  Qed.

  Lemma input_gd_facts
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ) :
    eval_cell Γ (adv (ncr RegionId.NoteCommit.InputGD) Advice.A6 0) =
      eval_cell Γ
        (adv (RegionId.WitnessInput RegionId.WitnessInput.GDOld)
          Advice.A0 0) /\
    eval_cell Γ (adv (ncr RegionId.NoteCommit.InputGD) Advice.A7 0) =
      eval_cell Γ (adv (ncr RegionId.NoteCommit.RangeB0) Advice.A9 0) /\
    eval_cell Γ (adv (ncr RegionId.NoteCommit.InputGD) Advice.A7 1) =
      eval_cell Γ (adv (ncr RegionId.NoteCommit.MessagePieceB) Advice.A8 0) /\
    eval_cell Γ (adv (ncr RegionId.NoteCommit.InputGD) Advice.A8 0) =
      eval_cell Γ (adv (ncr RegionId.NoteCommit.WitnessA) Advice.A6 0) /\
    eval_cell Γ (adv (ncr RegionId.NoteCommit.InputGD) Advice.A8 1) =
      eval_cell Γ (adv (ncr RegionId.NoteCommit.XGDLookup) Advice.A9 0) /\
    eval_cell Γ (adv (ncr RegionId.NoteCommit.InputGD) Advice.A9 0) =
      eval_cell Γ (adv HR Advice.A2 13) /\
    eval_cell Γ (adv (ncr RegionId.NoteCommit.InputGD) Advice.A9 1) =
      eval_cell Γ (adv (ncr RegionId.NoteCommit.XGDLookup) Advice.A9 13) /\
    Γ.(Assignment.selector) Selector.QNoteCommitOldGd
      (ncr RegionId.NoteCommit.InputGD) 0 = 1.
  Proof.
    pose proof (old_instance_facts Γ Hcircuit) as H.
    peel_instance H 27.
    apply interpret_layouter_facts_add_region in H.
    cbn [region_facts interpret_facts interpret_fact List.app] in H.
    destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & _).
    repeat split; assumption.
  Qed.

  Lemma input_pkd_facts
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ) :
    eval_cell Γ (adv (ncr RegionId.NoteCommit.InputPkD) Advice.A6 0) =
      eval_cell Γ
        (adv (RegionId.AddressIntegrity RegionId.AddressIntegrity.WitnessPkD)
          Advice.A0 0) /\
    eval_cell Γ (adv (ncr RegionId.NoteCommit.InputPkD) Advice.A7 0) =
      eval_cell Γ (adv (ncr RegionId.NoteCommit.RangeB3) Advice.A9 0) /\
    eval_cell Γ (adv (ncr RegionId.NoteCommit.InputPkD) Advice.A7 1) =
      eval_cell Γ (adv (ncr RegionId.NoteCommit.MessagePieceD) Advice.A7 0) /\
    eval_cell Γ (adv (ncr RegionId.NoteCommit.InputPkD) Advice.A8 0) =
      eval_cell Γ (adv (ncr RegionId.NoteCommit.WitnessC) Advice.A6 0) /\
    eval_cell Γ (adv (ncr RegionId.NoteCommit.InputPkD) Advice.A8 1) =
      eval_cell Γ (adv (ncr RegionId.NoteCommit.XPKDLookup) Advice.A9 0) /\
    eval_cell Γ (adv (ncr RegionId.NoteCommit.InputPkD) Advice.A9 0) =
      eval_cell Γ (adv HR Advice.A2 39) /\
    eval_cell Γ (adv (ncr RegionId.NoteCommit.InputPkD) Advice.A9 1) =
      eval_cell Γ (adv (ncr RegionId.NoteCommit.XPKDLookup) Advice.A9 14) /\
    Γ.(Assignment.selector) Selector.QNoteCommitOldPkd
      (ncr RegionId.NoteCommit.InputPkD) 0 = 1.
  Proof.
    pose proof (old_instance_facts Γ Hcircuit) as H.
    peel_instance H 28.
    apply interpret_layouter_facts_add_region in H.
    cbn [region_facts interpret_facts interpret_fact List.app] in H.
    destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & _).
    repeat split; assumption.
  Qed.

  Lemma input_value_facts
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ) :
    eval_cell Γ (adv (ncr RegionId.NoteCommit.InputValue) Advice.A6 0) =
      eval_cell Γ
        (adv (RegionId.WitnessInput RegionId.WitnessInput.VOld)
          Advice.A0 0) /\
    eval_cell Γ (adv (ncr RegionId.NoteCommit.InputValue) Advice.A7 0) =
      eval_cell Γ (adv (ncr RegionId.NoteCommit.RangeD2) Advice.A9 0) /\
    eval_cell Γ (adv (ncr RegionId.NoteCommit.InputValue) Advice.A8 0) =
      eval_cell Γ (adv HR Advice.A2 52) /\
    eval_cell Γ (adv (ncr RegionId.NoteCommit.InputValue) Advice.A9 0) =
      eval_cell Γ (adv (ncr RegionId.NoteCommit.RangeE0) Advice.A9 0) /\
    Γ.(Assignment.selector) Selector.QNoteCommitOldValue
      (ncr RegionId.NoteCommit.InputValue) 0 = 1.
  Proof.
    pose proof (old_instance_facts Γ Hcircuit) as H.
    peel_instance H 29.
    apply interpret_layouter_facts_add_region in H.
    cbn [region_facts interpret_facts interpret_fact List.app] in H.
    destruct H as (H1 & H2 & H3 & H4 & H5 & _).
    repeat split; assumption.
  Qed.

  Lemma input_rho_facts
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ) :
    eval_cell Γ (adv (ncr RegionId.NoteCommit.InputRho) Advice.A6 0) =
      eval_cell Γ
        (adv (RegionId.WitnessInput RegionId.WitnessInput.RhoOld)
          Advice.A0 0) /\
    eval_cell Γ (adv (ncr RegionId.NoteCommit.InputRho) Advice.A7 0) =
      eval_cell Γ (adv (ncr RegionId.NoteCommit.RangeE1) Advice.A9 0) /\
    eval_cell Γ (adv (ncr RegionId.NoteCommit.InputRho) Advice.A7 1) =
      eval_cell Γ (adv (ncr RegionId.NoteCommit.MessagePieceG) Advice.A7 0) /\
    eval_cell Γ (adv (ncr RegionId.NoteCommit.InputRho) Advice.A8 0) =
      eval_cell Γ (adv (ncr RegionId.NoteCommit.WitnessF) Advice.A6 0) /\
    eval_cell Γ (adv (ncr RegionId.NoteCommit.InputRho) Advice.A8 1) =
      eval_cell Γ (adv (ncr RegionId.NoteCommit.RhoLookup) Advice.A9 0) /\
    eval_cell Γ (adv (ncr RegionId.NoteCommit.InputRho) Advice.A9 0) =
      eval_cell Γ (adv HR Advice.A2 71) /\
    eval_cell Γ (adv (ncr RegionId.NoteCommit.InputRho) Advice.A9 1) =
      eval_cell Γ (adv (ncr RegionId.NoteCommit.RhoLookup) Advice.A9 14) /\
    Γ.(Assignment.selector) Selector.QNoteCommitOldRho
      (ncr RegionId.NoteCommit.InputRho) 0 = 1.
  Proof.
    pose proof (old_instance_facts Γ Hcircuit) as H.
    peel_instance H 30.
    apply interpret_layouter_facts_add_region in H.
    cbn [region_facts interpret_facts interpret_fact List.app] in H.
    destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & _).
    repeat split; assumption.
  Qed.

  Lemma input_psi_facts
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ) :
    eval_cell Γ (adv (ncr RegionId.NoteCommit.InputPsi) Advice.A6 0) =
      eval_cell Γ
        (adv (RegionId.WitnessInput RegionId.WitnessInput.PsiOld)
          Advice.A0 0) /\
    eval_cell Γ (adv (ncr RegionId.NoteCommit.InputPsi) Advice.A6 1) =
      eval_cell Γ (adv (ncr RegionId.NoteCommit.RangeH0) Advice.A9 0) /\
    eval_cell Γ (adv (ncr RegionId.NoteCommit.InputPsi) Advice.A7 0) =
      eval_cell Γ (adv (ncr RegionId.NoteCommit.RangeG1) Advice.A9 0) /\
    eval_cell Γ (adv (ncr RegionId.NoteCommit.InputPsi) Advice.A7 1) =
      eval_cell Γ (adv (ncr RegionId.NoteCommit.MessagePieceH) Advice.A8 0) /\
    eval_cell Γ (adv (ncr RegionId.NoteCommit.InputPsi) Advice.A8 0) =
      eval_cell Γ (adv HR Advice.A2 84) /\
    eval_cell Γ (adv (ncr RegionId.NoteCommit.InputPsi) Advice.A8 1) =
      eval_cell Γ (adv (ncr RegionId.NoteCommit.PsiLookup) Advice.A9 0) /\
    eval_cell Γ (adv (ncr RegionId.NoteCommit.InputPsi) Advice.A9 0) =
      eval_cell Γ (adv HR Advice.A2 96) /\
    eval_cell Γ (adv (ncr RegionId.NoteCommit.InputPsi) Advice.A9 1) =
      eval_cell Γ (adv (ncr RegionId.NoteCommit.PsiLookup) Advice.A9 13) /\
    Γ.(Assignment.selector) Selector.QNoteCommitOldPsi
      (ncr RegionId.NoteCommit.InputPsi) 0 = 1.
  Proof.
    pose proof (old_instance_facts Γ Hcircuit) as H.
    peel_instance H 31.
    apply interpret_layouter_facts_add_region in H.
    cbn [region_facts interpret_facts interpret_fact List.app] in H.
    destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & _).
    repeat split; assumption.
  Qed.

  (** ** Running-lookup regions: selector schedules and the strict tail *)

  Lemma nc_running_rows_fact
      (region : RegionId.t) (offset : Z) (count i : nat) :
    (i < count)%nat ->
    List.In
      (Fact.SelectorOn Selector.QLookup region (offset + Z.of_nat i))
      (region_facts region
        (Garden.Orchard.circuit.note_commit.enable_lookup_running_rows
          offset count)) /\
    List.In
      (Fact.SelectorOn Selector.QRunning region (offset + Z.of_nat i))
      (region_facts region
        (Garden.Orchard.circuit.note_commit.enable_lookup_running_rows
          offset count)).
  Proof.
    revert offset i.
    induction count as [| count IH]; intros offset i Hi.
    - lia.
    - destruct i as [| i].
      + cbn [Garden.Orchard.circuit.note_commit.enable_lookup_running_rows
          region_facts List.app].
        split.
        * left. f_equal. lia.
        * right. left. f_equal. lia.
      + cbn [Garden.Orchard.circuit.note_commit.enable_lookup_running_rows
          region_facts List.app].
        destruct (IH (offset + 1) i ltac:(lia)) as [H1 H2].
        replace (offset + Z.of_nat (S i)) with (offset + 1 + Z.of_nat i)
          by lia.
        split; right; right; assumption.
  Qed.

  Lemma running_selectors_of_facts
      (Γ : Assignment.t columns RegionId.t) (region : RegionId.t) (count : nat)
      (H : interpret_facts Γ (region_facts region
        (Garden.Orchard.circuit.note_commit.enable_lookup_running_rows
          0 count)))
      (j : nat) (Hj : (j < count)%nat) :
    Γ.(Assignment.selector) Selector.QLookup region (Z.of_nat j) = 1 /\
    Γ.(Assignment.selector) Selector.QRunning region (Z.of_nat j) = 1.
  Proof.
    destruct (nc_running_rows_fact region 0 count j Hj) as [Hin1 Hin2].
    rewrite Z.add_0_l in Hin1, Hin2.
    split.
    - exact (interpret_facts_In Γ _ _ H Hin1).
    - exact (interpret_facts_In Γ _ _ H Hin2).
  Qed.

  Lemma xgd_lookup_selectors
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ)
      (j : nat) (Hj : (j < 13)%nat) :
    Γ.(Assignment.selector) Selector.QLookup
      (ncr RegionId.NoteCommit.XGDLookup) (Z.of_nat j) = 1 /\
    Γ.(Assignment.selector) Selector.QRunning
      (ncr RegionId.NoteCommit.XGDLookup) (Z.of_nat j) = 1.
  Proof.
    pose proof (old_instance_facts Γ Hcircuit) as H.
    peel_instance H 18.
    apply interpret_layouter_facts_in_namespace in H.
    unfold Garden.Orchard.circuit.note_commit.synthesize_running_lookup in H.
    apply interpret_layouter_facts_in_namespace in H.
    apply interpret_layouter_facts_add_region in H.
    apply interpret_region_facts_bind_left in H.
    exact (running_selectors_of_facts Γ _ 13 H j Hj).
  Qed.

  Lemma xpkd_lookup_selectors
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ)
      (j : nat) (Hj : (j < 14)%nat) :
    Γ.(Assignment.selector) Selector.QLookup
      (ncr RegionId.NoteCommit.XPKDLookup) (Z.of_nat j) = 1 /\
    Γ.(Assignment.selector) Selector.QRunning
      (ncr RegionId.NoteCommit.XPKDLookup) (Z.of_nat j) = 1.
  Proof.
    pose proof (old_instance_facts Γ Hcircuit) as H.
    peel_instance H 19.
    apply interpret_layouter_facts_in_namespace in H.
    unfold Garden.Orchard.circuit.note_commit.synthesize_running_lookup in H.
    apply interpret_layouter_facts_in_namespace in H.
    apply interpret_layouter_facts_add_region in H.
    apply interpret_region_facts_bind_left in H.
    exact (running_selectors_of_facts Γ _ 14 H j Hj).
  Qed.

  Lemma rho_lookup_selectors
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ)
      (j : nat) (Hj : (j < 14)%nat) :
    Γ.(Assignment.selector) Selector.QLookup
      (ncr RegionId.NoteCommit.RhoLookup) (Z.of_nat j) = 1 /\
    Γ.(Assignment.selector) Selector.QRunning
      (ncr RegionId.NoteCommit.RhoLookup) (Z.of_nat j) = 1.
  Proof.
    pose proof (old_instance_facts Γ Hcircuit) as H.
    peel_instance H 20.
    apply interpret_layouter_facts_in_namespace in H.
    unfold Garden.Orchard.circuit.note_commit.synthesize_running_lookup in H.
    apply interpret_layouter_facts_in_namespace in H.
    apply interpret_layouter_facts_add_region in H.
    apply interpret_region_facts_bind_left in H.
    exact (running_selectors_of_facts Γ _ 14 H j Hj).
  Qed.

  Lemma psi_lookup_selectors
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ)
      (j : nat) (Hj : (j < 13)%nat) :
    Γ.(Assignment.selector) Selector.QLookup
      (ncr RegionId.NoteCommit.PsiLookup) (Z.of_nat j) = 1 /\
    Γ.(Assignment.selector) Selector.QRunning
      (ncr RegionId.NoteCommit.PsiLookup) (Z.of_nat j) = 1.
  Proof.
    pose proof (old_instance_facts Γ Hcircuit) as H.
    peel_instance H 21.
    apply interpret_layouter_facts_in_namespace in H.
    unfold Garden.Orchard.circuit.note_commit.synthesize_running_lookup in H.
    apply interpret_layouter_facts_in_namespace in H.
    apply interpret_layouter_facts_add_region in H.
    apply interpret_region_facts_bind_left in H.
    exact (running_selectors_of_facts Γ _ 13 H j Hj).
  Qed.

  (** ** Y-canonicity sub-regions ([GD] at instance bind 16, [PkD] at 17) *)

  Tactic Notation "peel_y" hyp(H) integer(k) integer(j) :=
    unfold Garden.Orchard.circuit.note_commit.synthesize_old,
      Garden.Orchard.circuit.note_commit.synthesize_instance in H;
    do k (apply interpret_layouter_facts_bind_right in H);
    apply interpret_layouter_facts_bind_left in H;
    unfold Garden.Orchard.circuit.note_commit.synthesize_y_canonicity in H;
    apply interpret_layouter_facts_in_namespace in H;
    do j (apply interpret_layouter_facts_bind_right in H).

  Lemma j_lookup_facts_gd
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ) :
    (forall j : nat, (j < 25)%nat ->
      Γ.(Assignment.selector) Selector.QLookup
        (nyr RegionId.NoteCommit.YSubject.GD
          RegionId.NoteCommit.YCanonicity.JLookup) (Z.of_nat j) = 1 /\
      Γ.(Assignment.selector) Selector.QRunning
        (nyr RegionId.NoteCommit.YSubject.GD
          RegionId.NoteCommit.YCanonicity.JLookup) (Z.of_nat j) = 1) /\
    eval_cell Γ
      (adv (nyr RegionId.NoteCommit.YSubject.GD
        RegionId.NoteCommit.YCanonicity.JLookup) Advice.A9 25) = 0.
  Proof.
    pose proof (old_instance_facts Γ Hcircuit) as H.
    peel_y H 15 2.
    apply interpret_layouter_facts_bind_left in H.
    unfold Garden.Orchard.circuit.note_commit.synthesize_running_lookup in H.
    apply interpret_layouter_facts_in_namespace in H.
    apply interpret_layouter_facts_add_region in H.
    pose proof H as Hsel.
    apply interpret_region_facts_bind_left in Hsel.
    apply interpret_region_facts_bind_right in H.
    apply interpret_region_facts_bind_left in H.
    cbn [region_facts interpret_facts interpret_fact List.app] in H.
    destruct H as [Hconst _].
    split.
    - intros j Hj. exact (running_selectors_of_facts Γ _ 25 Hsel j Hj).
    - exact Hconst.
  Qed.

  Lemma j_lookup_facts_pkd
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ) :
    (forall j : nat, (j < 25)%nat ->
      Γ.(Assignment.selector) Selector.QLookup
        (nyr RegionId.NoteCommit.YSubject.PkD
          RegionId.NoteCommit.YCanonicity.JLookup) (Z.of_nat j) = 1 /\
      Γ.(Assignment.selector) Selector.QRunning
        (nyr RegionId.NoteCommit.YSubject.PkD
          RegionId.NoteCommit.YCanonicity.JLookup) (Z.of_nat j) = 1) /\
    eval_cell Γ
      (adv (nyr RegionId.NoteCommit.YSubject.PkD
        RegionId.NoteCommit.YCanonicity.JLookup) Advice.A9 25) = 0.
  Proof.
    pose proof (old_instance_facts Γ Hcircuit) as H.
    peel_y H 16 2.
    apply interpret_layouter_facts_bind_left in H.
    unfold Garden.Orchard.circuit.note_commit.synthesize_running_lookup in H.
    apply interpret_layouter_facts_in_namespace in H.
    apply interpret_layouter_facts_add_region in H.
    pose proof H as Hsel.
    apply interpret_region_facts_bind_left in Hsel.
    apply interpret_region_facts_bind_right in H.
    apply interpret_region_facts_bind_left in H.
    cbn [region_facts interpret_facts interpret_fact List.app] in H.
    destruct H as [Hconst _].
    split.
    - intros j Hj. exact (running_selectors_of_facts Γ _ 25 Hsel j Hj).
    - exact Hconst.
  Qed.

  Lemma j_prime_lookup_selectors_gd
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ)
      (j : nat) (Hj : (j < 13)%nat) :
    Γ.(Assignment.selector) Selector.QLookup
      (nyr RegionId.NoteCommit.YSubject.GD
        RegionId.NoteCommit.YCanonicity.JPrimeLookup) (Z.of_nat j) = 1 /\
    Γ.(Assignment.selector) Selector.QRunning
      (nyr RegionId.NoteCommit.YSubject.GD
        RegionId.NoteCommit.YCanonicity.JPrimeLookup) (Z.of_nat j) = 1.
  Proof.
    pose proof (old_instance_facts Γ Hcircuit) as H.
    peel_y H 15 3.
    apply interpret_layouter_facts_bind_left in H.
    apply interpret_layouter_facts_in_namespace in H.
    unfold Garden.Orchard.circuit.note_commit.synthesize_running_lookup in H.
    apply interpret_layouter_facts_in_namespace in H.
    apply interpret_layouter_facts_add_region in H.
    apply interpret_region_facts_bind_left in H.
    exact (running_selectors_of_facts Γ _ 13 H j Hj).
  Qed.

  Lemma j_prime_lookup_selectors_pkd
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ)
      (j : nat) (Hj : (j < 13)%nat) :
    Γ.(Assignment.selector) Selector.QLookup
      (nyr RegionId.NoteCommit.YSubject.PkD
        RegionId.NoteCommit.YCanonicity.JPrimeLookup) (Z.of_nat j) = 1 /\
    Γ.(Assignment.selector) Selector.QRunning
      (nyr RegionId.NoteCommit.YSubject.PkD
        RegionId.NoteCommit.YCanonicity.JPrimeLookup) (Z.of_nat j) = 1.
  Proof.
    pose proof (old_instance_facts Γ Hcircuit) as H.
    peel_y H 16 3.
    apply interpret_layouter_facts_bind_left in H.
    apply interpret_layouter_facts_in_namespace in H.
    unfold Garden.Orchard.circuit.note_commit.synthesize_running_lookup in H.
    apply interpret_layouter_facts_in_namespace in H.
    apply interpret_layouter_facts_add_region in H.
    apply interpret_region_facts_bind_left in H.
    exact (running_selectors_of_facts Γ _ 13 H j Hj).
  Qed.

  Lemma y_gate_facts_gd
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ) :
    let YG := nyr RegionId.NoteCommit.YSubject.GD
      RegionId.NoteCommit.YCanonicity.Gate in
    let JL := nyr RegionId.NoteCommit.YSubject.GD
      RegionId.NoteCommit.YCanonicity.JLookup in
    let JP := nyr RegionId.NoteCommit.YSubject.GD
      RegionId.NoteCommit.YCanonicity.JPrimeLookup in
    Γ.(Assignment.selector) Selector.QNoteCommitOldYCanon YG 0 = 1 /\
    eval_cell Γ (adv YG Advice.A5 0) =
      eval_cell Γ
        (adv (RegionId.WitnessInput RegionId.WitnessInput.GDOld)
          Advice.A1 0) /\
    eval_cell Γ (adv YG Advice.A7 0) =
      eval_cell Γ (adv (nyr RegionId.NoteCommit.YSubject.GD
        RegionId.NoteCommit.YCanonicity.RangeK0) Advice.A9 0) /\
    eval_cell Γ (adv YG Advice.A8 0) =
      eval_cell Γ (adv (nyr RegionId.NoteCommit.YSubject.GD
        RegionId.NoteCommit.YCanonicity.RangeK2) Advice.A9 0) /\
    eval_cell Γ (adv YG Advice.A5 1) = eval_cell Γ (adv JL Advice.A9 0) /\
    eval_cell Γ (adv YG Advice.A6 1) = eval_cell Γ (adv JL Advice.A9 1) /\
    eval_cell Γ (adv YG Advice.A7 1) = eval_cell Γ (adv JL Advice.A9 13) /\
    eval_cell Γ (adv YG Advice.A8 1) = eval_cell Γ (adv JP Advice.A9 0) /\
    eval_cell Γ (adv YG Advice.A9 1) = eval_cell Γ (adv JP Advice.A9 13).
  Proof.
    pose proof (old_instance_facts Γ Hcircuit) as H.
    peel_y H 15 4.
    apply interpret_layouter_facts_add_region in H.
    cbn [region_facts interpret_facts interpret_fact List.app] in H.
    destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & _).
    repeat split; assumption.
  Qed.

  Lemma y_gate_facts_pkd
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ) :
    let YG := nyr RegionId.NoteCommit.YSubject.PkD
      RegionId.NoteCommit.YCanonicity.Gate in
    let JL := nyr RegionId.NoteCommit.YSubject.PkD
      RegionId.NoteCommit.YCanonicity.JLookup in
    let JP := nyr RegionId.NoteCommit.YSubject.PkD
      RegionId.NoteCommit.YCanonicity.JPrimeLookup in
    Γ.(Assignment.selector) Selector.QNoteCommitOldYCanon YG 0 = 1 /\
    eval_cell Γ (adv YG Advice.A5 0) =
      eval_cell Γ
        (adv (RegionId.AddressIntegrity RegionId.AddressIntegrity.WitnessPkD)
          Advice.A1 0) /\
    eval_cell Γ (adv YG Advice.A7 0) =
      eval_cell Γ (adv (nyr RegionId.NoteCommit.YSubject.PkD
        RegionId.NoteCommit.YCanonicity.RangeK0) Advice.A9 0) /\
    eval_cell Γ (adv YG Advice.A8 0) =
      eval_cell Γ (adv (nyr RegionId.NoteCommit.YSubject.PkD
        RegionId.NoteCommit.YCanonicity.RangeK2) Advice.A9 0) /\
    eval_cell Γ (adv YG Advice.A5 1) = eval_cell Γ (adv JL Advice.A9 0) /\
    eval_cell Γ (adv YG Advice.A6 1) = eval_cell Γ (adv JL Advice.A9 1) /\
    eval_cell Γ (adv YG Advice.A7 1) = eval_cell Γ (adv JL Advice.A9 13) /\
    eval_cell Γ (adv YG Advice.A8 1) = eval_cell Γ (adv JP Advice.A9 0) /\
    eval_cell Γ (adv YG Advice.A9 1) = eval_cell Γ (adv JP Advice.A9 13).
  Proof.
    pose proof (old_instance_facts Γ Hcircuit) as H.
    peel_y H 16 4.
    apply interpret_layouter_facts_add_region in H.
    cbn [region_facts interpret_facts interpret_fact List.app] in H.
    destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & _).
    repeat split; assumption.
  Qed.

  (** ** The hash-to-point region: facts with concrete piece cells

      Variant 1 ([use_second_sinsemilla = false]): the hash program is
      [synthesize_hash_to_point_note_commit] — selectors [QSinsemilla1_1]/
      [QSinsemilla4_1], fixed [QSinsemilla2_1]/[LagrangeCoeffs0], columns
      [A0]/[A1]/[A2]/[A3]/[A4] — and the witnessed piece cells live on
      [A6]. *)

  Lemma old_hash_facts
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ) :
    interpret_facts Γ (region_facts HR
      (Garden.Halo2.halo2_gadgets.sinsemilla.chip
        .synthesize_hash_to_point_note_commit_region
        HR
        Selector.QSinsemilla1_1 Selector.QSinsemilla4_1
        Fixed.QSinsemilla2_1 Fixed.LagrangeCoeffs0
        Advice.A0 Advice.A1 Advice.A2 Advice.A3 Advice.A4
        Garden.Orchard.circuit.note_commit.q_note_commit_m_x
        Garden.Orchard.circuit.note_commit.q_note_commit_m_y
        (adv (ncr RegionId.NoteCommit.WitnessA) Advice.A6 0)
        (adv (ncr RegionId.NoteCommit.WitnessB) Advice.A6 0)
        (adv (ncr RegionId.NoteCommit.WitnessC) Advice.A6 0)
        (adv (ncr RegionId.NoteCommit.WitnessD) Advice.A6 0)
        (adv (ncr RegionId.NoteCommit.WitnessE) Advice.A6 0)
        (adv (ncr RegionId.NoteCommit.WitnessF) Advice.A6 0)
        (adv (ncr RegionId.NoteCommit.WitnessG) Advice.A6 0)
        (adv (ncr RegionId.NoteCommit.WitnessH) Advice.A6 0))).
  Proof.
    pose proof (old_instance_facts Γ Hcircuit) as H.
    peel_instance H 17.
    apply interpret_layouter_facts_in_namespace in H.
    apply interpret_layouter_facts_bind_right in H.
    apply interpret_layouter_facts_bind_left in H.
    apply interpret_layouter_facts_in_namespace in H.
    unfold Garden.Halo2.halo2_gadgets.sinsemilla.chip
      .synthesize_hash_to_point_note_commit in H.
    apply interpret_layouter_facts_add_region in H.
    exact H.
  Qed.

  (** The eight piece copies: the running-sum cell at each piece offset is
      the witnessed piece cell. *)

  Tactic Notation "peel_hash_piece" hyp(H) integer(k) :=
    do k (apply interpret_region_facts_bind_right in H);
    apply interpret_region_facts_bind_left in H;
    do 2 (apply interpret_region_facts_bind_right in H);
    apply interpret_region_facts_bind_left in H;
    cbn [region_facts interpret_facts interpret_fact List.app] in H;
    destruct H as [H _].

  Lemma old_hash_piece_copies
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ) :
    eval_cell Γ (adv HR Advice.A2 0) =
      eval_cell Γ (adv (ncr RegionId.NoteCommit.WitnessA) Advice.A6 0) /\
    eval_cell Γ (adv HR Advice.A2 25) =
      eval_cell Γ (adv (ncr RegionId.NoteCommit.WitnessB) Advice.A6 0) /\
    eval_cell Γ (adv HR Advice.A2 26) =
      eval_cell Γ (adv (ncr RegionId.NoteCommit.WitnessC) Advice.A6 0) /\
    eval_cell Γ (adv HR Advice.A2 51) =
      eval_cell Γ (adv (ncr RegionId.NoteCommit.WitnessD) Advice.A6 0) /\
    eval_cell Γ (adv HR Advice.A2 57) =
      eval_cell Γ (adv (ncr RegionId.NoteCommit.WitnessE) Advice.A6 0) /\
    eval_cell Γ (adv HR Advice.A2 58) =
      eval_cell Γ (adv (ncr RegionId.NoteCommit.WitnessF) Advice.A6 0) /\
    eval_cell Γ (adv HR Advice.A2 83) =
      eval_cell Γ (adv (ncr RegionId.NoteCommit.WitnessG) Advice.A6 0) /\
    eval_cell Γ (adv HR Advice.A2 108) =
      eval_cell Γ (adv (ncr RegionId.NoteCommit.WitnessH) Advice.A6 0).
  Proof.
    pose proof (old_hash_facts Γ Hcircuit) as Hbase.
    unfold Garden.Halo2.halo2_gadgets.sinsemilla.chip
      .synthesize_hash_to_point_note_commit_region in Hbase.
    repeat split.
    - pose proof Hbase as H. peel_hash_piece H 3. exact H.
    - pose proof Hbase as H. peel_hash_piece H 4. exact H.
    - pose proof Hbase as H. peel_hash_piece H 5. exact H.
    - pose proof Hbase as H. peel_hash_piece H 6. exact H.
    - pose proof Hbase as H. peel_hash_piece H 7. exact H.
    - pose proof Hbase as H. peel_hash_piece H 8. exact H.
    - pose proof Hbase as H. peel_hash_piece H 9. exact H.
    - pose proof Hbase as H. peel_hash_piece H 10. exact H.
  Qed.

  (** The whole-region row schedule: [q_sinsemilla1] on all 109 rows,
      [q_s2 = 1] on the running rows, the seven inter-piece zeros and the
      final [2]. *)
  Lemma old_hash_schedule
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ) :
    (forall j : nat, (j < 109)%nat ->
      Γ.(Assignment.selector) Selector.QSinsemilla1_1 HR (Z.of_nat j) = 1) /\
    (forall j : nat, (j < 109)%nat ->
      j <> 24%nat -> j <> 25%nat -> j <> 50%nat -> j <> 56%nat ->
      j <> 57%nat -> j <> 82%nat -> j <> 107%nat -> j <> 108%nat ->
      Γ.(Assignment.fixed) Fixed.QSinsemilla2_1 HR (Z.of_nat j) = 1) /\
    Γ.(Assignment.fixed) Fixed.QSinsemilla2_1 HR 24 = 0 /\
    Γ.(Assignment.fixed) Fixed.QSinsemilla2_1 HR 25 = 0 /\
    Γ.(Assignment.fixed) Fixed.QSinsemilla2_1 HR 50 = 0 /\
    Γ.(Assignment.fixed) Fixed.QSinsemilla2_1 HR 56 = 0 /\
    Γ.(Assignment.fixed) Fixed.QSinsemilla2_1 HR 57 = 0 /\
    Γ.(Assignment.fixed) Fixed.QSinsemilla2_1 HR 82 = 0 /\
    Γ.(Assignment.fixed) Fixed.QSinsemilla2_1 HR 107 = 0 /\
    Γ.(Assignment.fixed) Fixed.QSinsemilla2_1 HR 108 = 2.
  Proof.
    pose proof (old_hash_facts Γ Hcircuit) as Hbase.
    unfold Garden.Halo2.halo2_gadgets.sinsemilla.chip
      .synthesize_hash_to_point_note_commit_region in Hbase.
    pose proof Hbase as HpA.
    do 3 apply interpret_region_facts_bind_right in HpA.
    apply interpret_region_facts_bind_left in HpA.
    apply NoteCommitNewHash.hash_piece_schedule in HpA.
    destruct HpA as (HselA & HstepA & HlastA).
    pose proof Hbase as HpB.
    do 4 apply interpret_region_facts_bind_right in HpB.
    apply interpret_region_facts_bind_left in HpB.
    apply NoteCommitNewHash.hash_piece_schedule in HpB.
    destruct HpB as (HselB & HstepB & HlastB).
    pose proof Hbase as HpC.
    do 5 apply interpret_region_facts_bind_right in HpC.
    apply interpret_region_facts_bind_left in HpC.
    apply NoteCommitNewHash.hash_piece_schedule in HpC.
    destruct HpC as (HselC & HstepC & HlastC).
    pose proof Hbase as HpD.
    do 6 apply interpret_region_facts_bind_right in HpD.
    apply interpret_region_facts_bind_left in HpD.
    apply NoteCommitNewHash.hash_piece_schedule in HpD.
    destruct HpD as (HselD & HstepD & HlastD).
    pose proof Hbase as HpE.
    do 7 apply interpret_region_facts_bind_right in HpE.
    apply interpret_region_facts_bind_left in HpE.
    apply NoteCommitNewHash.hash_piece_schedule in HpE.
    destruct HpE as (HselE & HstepE & HlastE).
    pose proof Hbase as HpF.
    do 8 apply interpret_region_facts_bind_right in HpF.
    apply interpret_region_facts_bind_left in HpF.
    apply NoteCommitNewHash.hash_piece_schedule in HpF.
    destruct HpF as (HselF & HstepF & HlastF).
    pose proof Hbase as HpG.
    do 9 apply interpret_region_facts_bind_right in HpG.
    apply interpret_region_facts_bind_left in HpG.
    apply NoteCommitNewHash.hash_piece_schedule in HpG.
    destruct HpG as (HselG & HstepG & HlastG).
    pose proof Hbase as HpH.
    do 10 apply interpret_region_facts_bind_right in HpH.
    apply interpret_region_facts_bind_left in HpH.
    apply NoteCommitNewHash.hash_piece_schedule in HpH.
    destruct HpH as (HselH & HstepH & HlastH).
    clear Hbase.
    pose proof (HlastA ltac:(lia)) as Hq2_24.
    pose proof (HlastB ltac:(lia)) as Hq2_25.
    pose proof (HlastC ltac:(lia)) as Hq2_50.
    pose proof (HlastD ltac:(lia)) as Hq2_56.
    pose proof (HlastE ltac:(lia)) as Hq2_57.
    pose proof (HlastF ltac:(lia)) as Hq2_82.
    pose proof (HlastG ltac:(lia)) as Hq2_107.
    pose proof (HlastH ltac:(lia)) as Hq2_108.
    replace (0 + Z.of_nat (25 - 1)) with 24 in Hq2_24 by lia.
    replace (25 + Z.of_nat (1 - 1)) with 25 in Hq2_25 by lia.
    replace (26 + Z.of_nat (25 - 1)) with 50 in Hq2_50 by lia.
    replace (51 + Z.of_nat (6 - 1)) with 56 in Hq2_56 by lia.
    replace (57 + Z.of_nat (1 - 1)) with 57 in Hq2_57 by lia.
    replace (58 + Z.of_nat (25 - 1)) with 82 in Hq2_82 by lia.
    replace (83 + Z.of_nat (25 - 1)) with 107 in Hq2_107 by lia.
    replace (108 + Z.of_nat (1 - 1)) with 108 in Hq2_108 by lia.
    split.
    { intros j Hj.
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
    split.
    { intros j Hj Hb24 Hb25 Hb50 Hb56 Hb57 Hb82 Hb107 Hb108.
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
    repeat split; assumption.
  Qed.

  (** ** Ten-bit word bounds: hash-region words and running-lookup words *)

  Lemma old_hash_word_bound
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ)
      (j : nat) (Hj : (j < 109)%nat) :
    0 <= w Γ (Z.of_nat j) < 2 ^ 10.
  Proof.
    destruct (old_hash_schedule Γ Hcircuit) as (Hsel & _).
    exact (word_at_bound Γ HR (Z.of_nat j)
      Selector.QSinsemilla1_1 Fixed.QSinsemilla2_1
      Advice.A0 Advice.A1 Advice.A2 Advice.A3 Advice.A4
      (generator_table_facts Γ Hcircuit)
      (SinsemillaHash.enabled_eq_one Γ Selector.QSinsemilla1_1 HR
        (Z.of_nat j) (Hsel j Hj))
      (generator_table_lookup_holds_1 Γ Hcircuit HR (Z.of_nat j))).
  Qed.

  (** The [A9] running-sum reader of a lookup region, and its row word. *)
  Definition zv (Γ : Assignment.t columns RegionId.t)
      (region : RegionId.t) (k : nat) : Z :=
    Γ ⊢ ⟦ Expression.Advice Advice.A9 Rotation.cur ⟧ (region, Z.of_nat k).

  Definition lw (Γ : Assignment.t columns RegionId.t)
      (region : RegionId.t) (k : nat) : Z :=
    zv Γ region k -F zv Γ region (S k) *F UnOp.from (2 ^ 10).

  (** The range-check lookup bounds a running-sum row word to ten bits
      (the running branch: both selectors enabled on the row). *)
  Lemma running_word_range_row
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ)
      (region : RegionId.t) (row : Z)
      (Hl : Γ.(Assignment.selector) Selector.QLookup region row = 1)
      (Hr : Γ.(Assignment.selector) Selector.QRunning region row = 1) :
    0 <=
      (Γ ⊢ ⟦ Expression.Advice Advice.A9 Rotation.cur ⟧ (region, row)) -F
        (Γ ⊢ ⟦ Expression.Advice Advice.A9 Rotation.next ⟧ (region, row)) *F
        UnOp.from (2 ^ 10) <
      2 ^ 10.
  Proof.
    pose proof
      (BaseFieldCanonicity.range_check_lookup_holds Γ Hcircuit region row)
      as Hlookup.
    with_strategy opaque [BinOp.add BinOp.sub BinOp.mul UnOp.from
      Garden.Halo2.halo2_gadgets.sinsemilla.chip_proof.GeneratorTable
        .table_rows]
      cbn in Hlookup.
    destruct Hlookup as (table_row & Hbound & Hpairs).
    rewrite Garden.Halo2.halo2_gadgets.sinsemilla.chip_proof.GeneratorTable
      .table_rows_eq in Hbound.
    unfold BaseFieldCanonicity.range_check_lookup_argument in Hpairs.
    cbn [LookupArgument.pairs] in Hpairs.
    rewrite Forall_cons_iff in Hpairs.
    destruct Hpairs as [Hpair _].
    with_strategy opaque [BinOp.add BinOp.sub BinOp.mul UnOp.from]
      cbn in Hpair.
    rewrite Hl, Hr in Hpair.
    rewrite (Garden.Halo2.halo2_gadgets.sinsemilla.chip_proof.GeneratorTable
      .loaded Γ
      (generator_table_facts Γ Hcircuit)
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

  Lemma running_word_range
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ)
      (region : RegionId.t) (k : nat)
      (Hl : Γ.(Assignment.selector) Selector.QLookup region (Z.of_nat k) = 1)
      (Hr : Γ.(Assignment.selector) Selector.QRunning region (Z.of_nat k) = 1) :
    0 <= lw Γ region k < 2 ^ 10.
  Proof.
    unfold lw, zv.
    replace (Z.of_nat (S k)) with (Z.of_nat k + 1) by lia.
    rewrite <- advice_next_cur.
    exact (running_word_range_row Γ Hcircuit region (Z.of_nat k) Hl Hr).
  Qed.

  (** The running-sum chain: with each row word ten-bit and the tail zero,
      every [z] cell is the exact digit sum of its remaining words. *)
  Lemma running_chain
      (Γ : Assignment.t columns RegionId.t) (region : RegionId.t) (n : nat)
      (Hn : (n <= 25)%nat)
      (Hword : forall k : nat, (k < n)%nat -> 0 <= lw Γ region k < 2 ^ 10)
      (Hend : zv Γ region n = 0) :
    forall (m k : nat), (k + m = n)%nat ->
      zv Γ region k =
        SinsemillaHash.digit_sum
          (List.map (fun i : nat => lw Γ region (k + i)%nat)
            (List.seq 0%nat m)).
  Proof.
    induction m as [| m IH]; intros k Hk.
    - cbn [List.seq List.map SinsemillaHash.digit_sum].
      replace k with n by lia.
      exact Hend.
    - pose proof (IH (S k) ltac:(lia)) as Htail.
      assert (Htail_bound : 0 <= zv Γ region (S k) < 2 ^ (10 * Z.of_nat m)).
      { rewrite Htail.
        pose proof (SinsemillaHash.digit_sum_bound
          (List.map (fun i : nat => lw Γ region (S k + i)%nat)
            (List.seq 0%nat m))) as Hb.
        rewrite List.length_map, List.length_seq in Hb.
        apply Hb.
        rewrite List.Forall_map, List.Forall_forall.
        intros i Hi. rewrite List.in_seq in Hi.
        apply Hword. lia. }
      assert (Hzk :
          lw Γ region k +F zv Γ region (S k) *F UnOp.from (2 ^ 10) =
          zv Γ region k).
      { unfold lw.
        rewrite OrchardActionInputs.sub_then_add.
        unfold zv. apply advice_reduced. }
      assert (Hpow : 2 ^ (10 * Z.of_nat m) * 2 ^ 10 <= 2 ^ 250).
      { rewrite <- Z.pow_add_r by lia.
        apply Z.pow_le_mono_r; lia. }
      assert (Hp250 : 2 ^ 250 + 2 ^ 10 < Primes.pallas_p)
        by (vm_compute; reflexivity).
      assert (Hwk : 0 <= lw Γ region k < 2 ^ 10) by (apply Hword; lia).
      assert (Hexact :
          zv Γ region k = lw Γ region k + zv Γ region (S k) * 2 ^ 10).
      { rewrite <- Hzk.
        apply NoteCommitMessagePieces.addF_mulF_exact.
        - lia.
        - lia.
        - split; [lia |].
          change (2 ^ 10) with 1024.
          vm_compute; reflexivity.
        - nia. }
      rewrite Hexact.
      cbn [List.seq List.map SinsemillaHash.digit_sum].
      rewrite <- List.seq_shift, List.map_map.
      rewrite (List.map_ext
        (fun i : nat => lw Γ region (k + S i)%nat)
        (fun i : nat => lw Γ region (S k + i)%nat))
        by (intros i; f_equal; lia).
      rewrite <- Htail.
      replace (k + 0)%nat with k by lia.
      ring.
  Qed.

  (** Bound corollary: [z_k] is below [2^(10 (n - k))]. *)
  Lemma running_chain_bound
      (Γ : Assignment.t columns RegionId.t) (region : RegionId.t) (n : nat)
      (Hn : (n <= 25)%nat)
      (Hword : forall k : nat, (k < n)%nat -> 0 <= lw Γ region k < 2 ^ 10)
      (Hend : zv Γ region n = 0)
      (k : nat) (Hk : (k <= n)%nat) :
    0 <= zv Γ region k < 2 ^ (10 * Z.of_nat (n - k)).
  Proof.
    rewrite (running_chain Γ region n Hn Hword Hend (n - k)%nat k
      ltac:(lia)).
    pose proof (SinsemillaHash.digit_sum_bound
      (List.map (fun i : nat => lw Γ region (k + i)%nat)
        (List.seq 0%nat (n - k)%nat))) as Hb.
    rewrite List.length_map, List.length_seq in Hb.
    apply Hb.
    rewrite List.Forall_map, List.Forall_forall.
    intros i Hi. rewrite List.in_seq in Hi.
    apply Hword. lia.
  Qed.

  (** ** Piece telescopes on the hash region *)

  (** Splitting a word run at an interior offset. *)
  Lemma run_split
      (Γ : Assignment.t columns RegionId.t) (off m k : nat) :
    List.map (fun j : nat => w Γ (Z.of_nat off + Z.of_nat j))
      (List.seq 0%nat (m + k)%nat) =
    List.map (fun j : nat => w Γ (Z.of_nat off + Z.of_nat j))
      (List.seq 0%nat m) ++
    List.map (fun j : nat => w Γ (Z.of_nat (off + m) + Z.of_nat j))
      (List.seq 0%nat k).
  Proof.
    rewrite (map_z_seq_split (w Γ) (Z.of_nat off) m k).
    f_equal.
    apply List.map_ext. intros j. f_equal. lia.
  Qed.

  (** Digit-sum bound of a word run. *)
  Lemma run_bound
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ)
      (off n : nat) (Hrange : (off + n <= 109)%nat) :
    0 <=
      SinsemillaHash.digit_sum
        (List.map (fun j : nat => w Γ (Z.of_nat off + Z.of_nat j))
          (List.seq 0%nat n)) <
      2 ^ (10 * Z.of_nat n).
  Proof.
    pose proof (SinsemillaHash.digit_sum_bound
      (List.map (fun j : nat => w Γ (Z.of_nat off + Z.of_nat j))
        (List.seq 0%nat n))) as Hb.
    rewrite List.length_map, List.length_seq in Hb.
    apply Hb.
    rewrite List.Forall_map, List.Forall_forall.
    intros j Hj. rewrite List.in_seq in Hj.
    replace (Z.of_nat off + Z.of_nat j) with (Z.of_nat (off + j)%nat) by lia.
    apply old_hash_word_bound; [exact Hcircuit | lia].
  Qed.

  (** The generic piece telescope at a hash-region offset, fed by the row
      schedule of [old_hash_schedule]. *)
  Lemma old_piece_telescope
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ)
      (off n : nat)
      (Hn : (0 < n)%nat) (Hrange : (off + n <= 109)%nat)
      (Hlen : 10 * Z.of_nat n <= 250)
      (Hsteps : forall j : nat, (S j < n)%nat ->
        Γ.(Assignment.fixed) Fixed.QSinsemilla2_1 HR
          (Z.of_nat off + Z.of_nat j) = 1)
      (v : Z) (Hv : v = 0 \/ v = 2)
      (Hlast :
        Γ.(Assignment.fixed) Fixed.QSinsemilla2_1 HR
          (Z.of_nat off + Z.of_nat (n - 1)%nat) = v) :
    Γ ⊢ ⟦ Expression.Advice Advice.A2 Rotation.cur ⟧ (HR, Z.of_nat off) =
      SinsemillaHash.digit_sum
        (List.map (fun j : nat => w Γ (Z.of_nat off + Z.of_nat j))
          (List.seq 0%nat n)).
  Proof.
    unfold w.
    apply SinsemillaHash.piece_telescope.
    - exact Hn.
    - intros j Hj.
      apply word_at_step.
      apply Hsteps. exact Hj.
    - apply (word_at_last Γ Fixed.QSinsemilla2_1 Advice.A2 HR
        (Z.of_nat off + Z.of_nat (n - 1)%nat) v Hlast Hv).
    - intros j Hj.
      replace (Z.of_nat off + Z.of_nat j) with (Z.of_nat (off + j)%nat)
        by lia.
      apply old_hash_word_bound; [exact Hcircuit | lia].
    - exact Hlen.
  Qed.

  (** ** The eleven [Which.Old] NoteCommit gates, at any region and row *)

  Ltac old_gate_tac :=
    match goal with
    | Hcircuit : circuit_holds _ _ _ |- _ =>
        apply (satisfies_gates_at _
          (𝓒.run_unit Garden.Orchard.circuit.configure
            ConstraintSystem.empty));
        [ cbn; repeat (first [left; reflexivity | right])
        | exact (holds_gates _ Hcircuit) ]
    end.

  Lemma old_gate_msg_b
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ)
      (region : RegionId.t) (row : Z) :
    Γ ⊢ ⟦ Garden.Orchard.circuit.note_commit.message_piece_b_gate
      Selector.QNoteCommitOldB ⟧ (region, row).
  Proof. old_gate_tac. Qed.

  Lemma old_gate_msg_d
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ)
      (region : RegionId.t) (row : Z) :
    Γ ⊢ ⟦ Garden.Orchard.circuit.note_commit.message_piece_d_gate
      Selector.QNoteCommitOldD ⟧ (region, row).
  Proof. old_gate_tac. Qed.

  Lemma old_gate_msg_e
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ)
      (region : RegionId.t) (row : Z) :
    Γ ⊢ ⟦ Garden.Orchard.circuit.note_commit.message_piece_e_gate
      Selector.QNoteCommitOldE ⟧ (region, row).
  Proof. old_gate_tac. Qed.

  Lemma old_gate_msg_g
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ)
      (region : RegionId.t) (row : Z) :
    Γ ⊢ ⟦ Garden.Orchard.circuit.note_commit.message_piece_g_gate
      Selector.QNoteCommitOldG ⟧ (region, row).
  Proof. old_gate_tac. Qed.

  Lemma old_gate_msg_h
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ)
      (region : RegionId.t) (row : Z) :
    Γ ⊢ ⟦ Garden.Orchard.circuit.note_commit.message_piece_h_gate
      Selector.QNoteCommitOldH ⟧ (region, row).
  Proof. old_gate_tac. Qed.

  Lemma old_gate_input_gd
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ)
      (region : RegionId.t) (row : Z) :
    Γ ⊢ ⟦ Garden.Orchard.circuit.note_commit.input_g_d_gate
      Selector.QNoteCommitOldGd ⟧ (region, row).
  Proof. old_gate_tac. Qed.

  Lemma old_gate_input_pkd
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ)
      (region : RegionId.t) (row : Z) :
    Γ ⊢ ⟦ Garden.Orchard.circuit.note_commit.input_pk_d_gate
      Selector.QNoteCommitOldPkd ⟧ (region, row).
  Proof. old_gate_tac. Qed.

  Lemma old_gate_input_value
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ)
      (region : RegionId.t) (row : Z) :
    Γ ⊢ ⟦ Garden.Orchard.circuit.note_commit.input_value_gate
      Selector.QNoteCommitOldValue ⟧ (region, row).
  Proof. old_gate_tac. Qed.

  Lemma old_gate_input_rho
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ)
      (region : RegionId.t) (row : Z) :
    Γ ⊢ ⟦ Garden.Orchard.circuit.note_commit.input_rho_gate
      Selector.QNoteCommitOldRho ⟧ (region, row).
  Proof. old_gate_tac. Qed.

  Lemma old_gate_input_psi
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ)
      (region : RegionId.t) (row : Z) :
    Γ ⊢ ⟦ Garden.Orchard.circuit.note_commit.input_psi_gate
      Selector.QNoteCommitOldPsi ⟧ (region, row).
  Proof. old_gate_tac. Qed.

  Lemma old_gate_y_canon
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ)
      (region : RegionId.t) (row : Z) :
    Γ ⊢ ⟦ Garden.Orchard.circuit.note_commit.y_coordinate_checks_gate
      Selector.QNoteCommitOldYCanon ⟧ (region, row).
  Proof. old_gate_tac. Qed.

  (** ** Canonical value names

      Every quantity of the decomposition, as the reduced value of its home
      cell.  Pieces live on the [A6] witness cells (equal, by the
      hash-region copies, to the [A2] running-sum cells at the piece
      offsets); the sub-piece bits/chunks live on their range/gate home
      cells. *)

  Definition av (Γ : Assignment.t columns RegionId.t) : Z :=
    val Γ (adv (ncr RegionId.NoteCommit.WitnessA) Advice.A6 0).
  Definition bv (Γ : Assignment.t columns RegionId.t) : Z :=
    val Γ (adv (ncr RegionId.NoteCommit.WitnessB) Advice.A6 0).
  Definition cv (Γ : Assignment.t columns RegionId.t) : Z :=
    val Γ (adv (ncr RegionId.NoteCommit.WitnessC) Advice.A6 0).
  Definition dv (Γ : Assignment.t columns RegionId.t) : Z :=
    val Γ (adv (ncr RegionId.NoteCommit.WitnessD) Advice.A6 0).
  Definition ev (Γ : Assignment.t columns RegionId.t) : Z :=
    val Γ (adv (ncr RegionId.NoteCommit.WitnessE) Advice.A6 0).
  Definition fv (Γ : Assignment.t columns RegionId.t) : Z :=
    val Γ (adv (ncr RegionId.NoteCommit.WitnessF) Advice.A6 0).
  Definition gv (Γ : Assignment.t columns RegionId.t) : Z :=
    val Γ (adv (ncr RegionId.NoteCommit.WitnessG) Advice.A6 0).
  Definition hv (Γ : Assignment.t columns RegionId.t) : Z :=
    val Γ (adv (ncr RegionId.NoteCommit.WitnessH) Advice.A6 0).

  Definition b0v (Γ : Assignment.t columns RegionId.t) : Z :=
    val Γ (adv (ncr RegionId.NoteCommit.RangeB0) Advice.A9 0).
  Definition b3v (Γ : Assignment.t columns RegionId.t) : Z :=
    val Γ (adv (ncr RegionId.NoteCommit.RangeB3) Advice.A9 0).
  Definition d2v (Γ : Assignment.t columns RegionId.t) : Z :=
    val Γ (adv (ncr RegionId.NoteCommit.RangeD2) Advice.A9 0).
  Definition e0v (Γ : Assignment.t columns RegionId.t) : Z :=
    val Γ (adv (ncr RegionId.NoteCommit.RangeE0) Advice.A9 0).
  Definition e1v (Γ : Assignment.t columns RegionId.t) : Z :=
    val Γ (adv (ncr RegionId.NoteCommit.RangeE1) Advice.A9 0).
  Definition g1v (Γ : Assignment.t columns RegionId.t) : Z :=
    val Γ (adv (ncr RegionId.NoteCommit.RangeG1) Advice.A9 0).
  Definition h0v (Γ : Assignment.t columns RegionId.t) : Z :=
    val Γ (adv (ncr RegionId.NoteCommit.RangeH0) Advice.A9 0).

  Definition b1v (Γ : Assignment.t columns RegionId.t) : Z :=
    val Γ (adv (ncr RegionId.NoteCommit.MessagePieceB) Advice.A8 0).
  Definition d0v (Γ : Assignment.t columns RegionId.t) : Z :=
    val Γ (adv (ncr RegionId.NoteCommit.MessagePieceD) Advice.A7 0).
  Definition g0v (Γ : Assignment.t columns RegionId.t) : Z :=
    val Γ (adv (ncr RegionId.NoteCommit.MessagePieceG) Advice.A7 0).
  Definition h1v (Γ : Assignment.t columns RegionId.t) : Z :=
    val Γ (adv (ncr RegionId.NoteCommit.MessagePieceH) Advice.A8 0).

  Definition b2v (Γ : Assignment.t columns RegionId.t) : Z :=
    val Γ (adv (nyr RegionId.NoteCommit.YSubject.GD
      RegionId.NoteCommit.YCanonicity.Gate) Advice.A6 0).
  Definition d1v (Γ : Assignment.t columns RegionId.t) : Z :=
    val Γ (adv (nyr RegionId.NoteCommit.YSubject.PkD
      RegionId.NoteCommit.YCanonicity.Gate) Advice.A6 0).

  Definition z13av (Γ : Assignment.t columns RegionId.t) : Z :=
    val Γ (adv HR Advice.A2 13).
  Definition z13cv (Γ : Assignment.t columns RegionId.t) : Z :=
    val Γ (adv HR Advice.A2 39).
  Definition z1dv (Γ : Assignment.t columns RegionId.t) : Z :=
    val Γ (adv HR Advice.A2 52).
  Definition z13fv (Γ : Assignment.t columns RegionId.t) : Z :=
    val Γ (adv HR Advice.A2 71).
  Definition z1gv (Γ : Assignment.t columns RegionId.t) : Z :=
    val Γ (adv HR Advice.A2 84).
  Definition z13gv (Γ : Assignment.t columns RegionId.t) : Z :=
    val Γ (adv HR Advice.A2 96).

  Definition gdxv (Γ : Assignment.t columns RegionId.t) : Z :=
    val Γ (adv (RegionId.WitnessInput RegionId.WitnessInput.GDOld)
      Advice.A0 0).
  Definition gdyv (Γ : Assignment.t columns RegionId.t) : Z :=
    val Γ (adv (RegionId.WitnessInput RegionId.WitnessInput.GDOld)
      Advice.A1 0).
  Definition pkdxv (Γ : Assignment.t columns RegionId.t) : Z :=
    val Γ (adv (RegionId.AddressIntegrity RegionId.AddressIntegrity.WitnessPkD)
      Advice.A0 0).
  Definition pkdyv (Γ : Assignment.t columns RegionId.t) : Z :=
    val Γ (adv (RegionId.AddressIntegrity RegionId.AddressIntegrity.WitnessPkD)
      Advice.A1 0).
  Definition voldv (Γ : Assignment.t columns RegionId.t) : Z :=
    val Γ (adv (RegionId.WitnessInput RegionId.WitnessInput.VOld)
      Advice.A0 0).
  Definition rhov (Γ : Assignment.t columns RegionId.t) : Z :=
    val Γ (adv (RegionId.WitnessInput RegionId.WitnessInput.RhoOld)
      Advice.A0 0).
  Definition psiv (Γ : Assignment.t columns RegionId.t) : Z :=
    val Γ (adv (RegionId.WitnessInput RegionId.WitnessInput.PsiOld)
      Advice.A0 0).

  (** Rewriting bridges between expression reads and cell values. *)

  Lemma cur_val
      (Γ : Assignment.t columns RegionId.t)
      (r : RegionId.t) (c : Advice.t) (row : Z) :
    Γ ⊢ ⟦ Expression.Advice c Rotation.cur ⟧ (r, row) =
      val Γ (adv r c row).
  Proof. apply eval_advice_cur_cell. Qed.

  Lemma cur_eq
      (Γ : Assignment.t columns RegionId.t)
      (r : RegionId.t) (c : Advice.t) (row : Z)
      (c2 : Garden.Halo2.Synthesis.Cell.t columns RegionId.t)
      (H : eval_cell Γ (adv r c row) = eval_cell Γ c2) :
    Γ ⊢ ⟦ Expression.Advice c Rotation.cur ⟧ (r, row) = val Γ c2.
  Proof.
    rewrite cur_val.
    unfold val.
    rewrite H.
    reflexivity.
  Qed.

  Lemma next_eq
      (Γ : Assignment.t columns RegionId.t)
      (r : RegionId.t) (c : Advice.t) (row row' : Z)
      (Hrow : row + 1 = row')
      (c2 : Garden.Halo2.Synthesis.Cell.t columns RegionId.t)
      (H : eval_cell Γ (adv r c row') = eval_cell Γ c2) :
    Γ ⊢ ⟦ Expression.Advice c Rotation.next ⟧ (r, row) = val Γ c2.
  Proof.
    rewrite eval_advice_next_cell.
    rewrite Hrow.
    unfold val, adv in *.
    rewrite H.
    reflexivity.
  Qed.

  Lemma zv_val
      (Γ : Assignment.t columns RegionId.t)
      (region : RegionId.t) (k : nat) (row : Z)
      (Hrow : row = Z.of_nat k) :
    val Γ (adv region Advice.A9 row) = zv Γ region k.
  Proof.
    subst row.
    unfold zv.
    symmetry.
    apply cur_val.
  Qed.

  (** ** The word runs and the piece telescopes *)

  Definition Lrun (Γ : Assignment.t columns RegionId.t) (off n : nat)
      : list Z :=
    List.map (fun j : nat => w Γ (Z.of_nat off + Z.of_nat j))
      (List.seq 0%nat n).

  Lemma Lrun_bound
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ)
      (off n : nat) (Hrange : (off + n <= 109)%nat) :
    0 <= SinsemillaHash.digit_sum (Lrun Γ off n) < 2 ^ (10 * Z.of_nat n).
  Proof. exact (run_bound Γ Hcircuit off n Hrange). Qed.

  Lemma Lrun_forall
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ)
      (off n : nat) (Hrange : (off + n <= 109)%nat) :
    List.Forall (fun x : Z => 0 <= x < 2 ^ 10) (Lrun Γ off n).
  Proof.
    unfold Lrun.
    rewrite List.Forall_map, List.Forall_forall.
    intros j Hj. rewrite List.in_seq in Hj.
    replace (Z.of_nat off + Z.of_nat j) with (Z.of_nat (off + j)%nat) by lia.
    apply old_hash_word_bound; [exact Hcircuit | lia].
  Qed.

  Lemma Lrun_length
      (Γ : Assignment.t columns RegionId.t) (off n : nat) :
    List.length (Lrun Γ off n) = n.
  Proof. unfold Lrun. now rewrite List.length_map, List.length_seq. Qed.

  (** The fourteen telescope identities: the eight piece values and the six
      interior running-sum cells the input gates consume. *)
  Lemma telescopes
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ) :
    av Γ = SinsemillaHash.digit_sum (Lrun Γ 0 25) /\
    bv Γ = w Γ 25 /\
    cv Γ = SinsemillaHash.digit_sum (Lrun Γ 26 25) /\
    dv Γ = SinsemillaHash.digit_sum (Lrun Γ 51 6) /\
    ev Γ = w Γ 57 /\
    fv Γ = SinsemillaHash.digit_sum (Lrun Γ 58 25) /\
    gv Γ = SinsemillaHash.digit_sum (Lrun Γ 83 25) /\
    hv Γ = w Γ 108 /\
    z13av Γ = SinsemillaHash.digit_sum (Lrun Γ 13 12) /\
    z13cv Γ = SinsemillaHash.digit_sum (Lrun Γ 39 12) /\
    z1dv Γ = SinsemillaHash.digit_sum (Lrun Γ 52 5) /\
    z13fv Γ = SinsemillaHash.digit_sum (Lrun Γ 71 12) /\
    z1gv Γ = SinsemillaHash.digit_sum (Lrun Γ 84 24) /\
    z13gv Γ = SinsemillaHash.digit_sum (Lrun Γ 96 12).
  Proof.
    destruct (old_hash_schedule Γ Hcircuit)
      as (Hsel & Hq2one & Hq24 & Hq25 & Hq50 & Hq56 & Hq57 & Hq82 & Hq107
        & Hq108).
    destruct (old_hash_piece_copies Γ Hcircuit)
      as (HcA & HcB & HcC & HcD & HcE & HcF & HcG & HcH).
    assert (Htel : forall (off n : nat) (vlast : Z),
      (0 < n)%nat -> (off + n <= 109)%nat -> 10 * Z.of_nat n <= 250 ->
      (forall j : nat, (S j < n)%nat ->
        Γ.(Assignment.fixed) Fixed.QSinsemilla2_1 HR
          (Z.of_nat off + Z.of_nat j) = 1) ->
      (vlast = 0 \/ vlast = 2) ->
      Γ.(Assignment.fixed) Fixed.QSinsemilla2_1 HR
        (Z.of_nat off + Z.of_nat (n - 1)%nat) = vlast ->
      Γ ⊢ ⟦ Expression.Advice Advice.A2 Rotation.cur ⟧ (HR, Z.of_nat off) =
        SinsemillaHash.digit_sum (Lrun Γ off n)).
    { intros off n vlast Hn Hrange Hlen Hsteps Hvl Hlast.
      exact (old_piece_telescope Γ Hcircuit off n Hn Hrange Hlen Hsteps
        vlast Hvl Hlast). }
    assert (Hstep_gen : forall (off n : nat),
      (off + n <= 109)%nat ->
      ((forall i : nat, (i < n)%nat ->
        (off + i)%nat <> 24%nat /\ (off + i)%nat <> 25%nat /\
        (off + i)%nat <> 50%nat /\ (off + i)%nat <> 56%nat /\
        (off + i)%nat <> 57%nat /\ (off + i)%nat <> 82%nat /\
        (off + i)%nat <> 107%nat /\ (off + i)%nat <> 108%nat)) ->
      forall j : nat, (S j < S n)%nat ->
        Γ.(Assignment.fixed) Fixed.QSinsemilla2_1 HR
          (Z.of_nat off + Z.of_nat j) = 1).
    { intros off n Hrange Hok j Hj.
      replace (Z.of_nat off + Z.of_nat j) with (Z.of_nat (off + j)%nat)
        by lia.
      destruct (Hok j ltac:(lia)) as (? & ? & ? & ? & ? & ? & ? & ?).
      apply Hq2one; lia. }
    (* Piece a: rows 0..24, boundary 24. *)
    assert (Ta :
        Γ ⊢ ⟦ Expression.Advice Advice.A2 Rotation.cur ⟧ (HR, Z.of_nat 0) =
        SinsemillaHash.digit_sum (Lrun Γ 0 25)).
    { apply (Htel 0%nat 25%nat 0); try lia.
      - apply (Hstep_gen 0%nat 24%nat); [lia |].
        intros i Hi. lia.
      - replace (Z.of_nat 0 + Z.of_nat (25 - 1)%nat) with 24 by lia.
        exact Hq24. }
    (* Sub-run of a: rows 13..24. *)
    assert (T13 :
        Γ ⊢ ⟦ Expression.Advice Advice.A2 Rotation.cur ⟧ (HR, Z.of_nat 13) =
        SinsemillaHash.digit_sum (Lrun Γ 13 12)).
    { apply (Htel 13%nat 12%nat 0); try lia.
      - apply (Hstep_gen 13%nat 11%nat); [lia |].
        intros i Hi. lia.
      - replace (Z.of_nat 13 + Z.of_nat (12 - 1)%nat) with 24 by lia.
        exact Hq24. }
    (* Piece c: rows 26..50, boundary 50. *)
    assert (Tc :
        Γ ⊢ ⟦ Expression.Advice Advice.A2 Rotation.cur ⟧ (HR, Z.of_nat 26) =
        SinsemillaHash.digit_sum (Lrun Γ 26 25)).
    { apply (Htel 26%nat 25%nat 0); try lia.
      - apply (Hstep_gen 26%nat 24%nat); [lia |].
        intros i Hi. lia.
      - replace (Z.of_nat 26 + Z.of_nat (25 - 1)%nat) with 50 by lia.
        exact Hq50. }
    (* Sub-run of c: rows 39..50. *)
    assert (T39 :
        Γ ⊢ ⟦ Expression.Advice Advice.A2 Rotation.cur ⟧ (HR, Z.of_nat 39) =
        SinsemillaHash.digit_sum (Lrun Γ 39 12)).
    { apply (Htel 39%nat 12%nat 0); try lia.
      - apply (Hstep_gen 39%nat 11%nat); [lia |].
        intros i Hi. lia.
      - replace (Z.of_nat 39 + Z.of_nat (12 - 1)%nat) with 50 by lia.
        exact Hq50. }
    (* Piece d: rows 51..56, boundary 56. *)
    assert (Td :
        Γ ⊢ ⟦ Expression.Advice Advice.A2 Rotation.cur ⟧ (HR, Z.of_nat 51) =
        SinsemillaHash.digit_sum (Lrun Γ 51 6)).
    { apply (Htel 51%nat 6%nat 0); try lia.
      - apply (Hstep_gen 51%nat 5%nat); [lia |].
        intros i Hi. lia.
      - replace (Z.of_nat 51 + Z.of_nat (6 - 1)%nat) with 56 by lia.
        exact Hq56. }
    (* Sub-run of d: rows 52..56. *)
    assert (T52 :
        Γ ⊢ ⟦ Expression.Advice Advice.A2 Rotation.cur ⟧ (HR, Z.of_nat 52) =
        SinsemillaHash.digit_sum (Lrun Γ 52 5)).
    { apply (Htel 52%nat 5%nat 0); try lia.
      - apply (Hstep_gen 52%nat 4%nat); [lia |].
        intros i Hi. lia.
      - replace (Z.of_nat 52 + Z.of_nat (5 - 1)%nat) with 56 by lia.
        exact Hq56. }
    (* Piece f: rows 58..82, boundary 82. *)
    assert (Tf :
        Γ ⊢ ⟦ Expression.Advice Advice.A2 Rotation.cur ⟧ (HR, Z.of_nat 58) =
        SinsemillaHash.digit_sum (Lrun Γ 58 25)).
    { apply (Htel 58%nat 25%nat 0); try lia.
      - apply (Hstep_gen 58%nat 24%nat); [lia |].
        intros i Hi. lia.
      - replace (Z.of_nat 58 + Z.of_nat (25 - 1)%nat) with 82 by lia.
        exact Hq82. }
    (* Sub-run of f: rows 71..82. *)
    assert (T71 :
        Γ ⊢ ⟦ Expression.Advice Advice.A2 Rotation.cur ⟧ (HR, Z.of_nat 71) =
        SinsemillaHash.digit_sum (Lrun Γ 71 12)).
    { apply (Htel 71%nat 12%nat 0); try lia.
      - apply (Hstep_gen 71%nat 11%nat); [lia |].
        intros i Hi. lia.
      - replace (Z.of_nat 71 + Z.of_nat (12 - 1)%nat) with 82 by lia.
        exact Hq82. }
    (* Piece g: rows 83..107, boundary 107. *)
    assert (Tg :
        Γ ⊢ ⟦ Expression.Advice Advice.A2 Rotation.cur ⟧ (HR, Z.of_nat 83) =
        SinsemillaHash.digit_sum (Lrun Γ 83 25)).
    { apply (Htel 83%nat 25%nat 0); try lia.
      - apply (Hstep_gen 83%nat 24%nat); [lia |].
        intros i Hi. lia.
      - replace (Z.of_nat 83 + Z.of_nat (25 - 1)%nat) with 107 by lia.
        exact Hq107. }
    (* Sub-runs of g: rows 84..107 and 96..107. *)
    assert (T84 :
        Γ ⊢ ⟦ Expression.Advice Advice.A2 Rotation.cur ⟧ (HR, Z.of_nat 84) =
        SinsemillaHash.digit_sum (Lrun Γ 84 24)).
    { apply (Htel 84%nat 24%nat 0); try lia.
      - apply (Hstep_gen 84%nat 23%nat); [lia |].
        intros i Hi. lia.
      - replace (Z.of_nat 84 + Z.of_nat (24 - 1)%nat) with 107 by lia.
        exact Hq107. }
    assert (T96 :
        Γ ⊢ ⟦ Expression.Advice Advice.A2 Rotation.cur ⟧ (HR, Z.of_nat 96) =
        SinsemillaHash.digit_sum (Lrun Γ 96 12)).
    { apply (Htel 96%nat 12%nat 0); try lia.
      - apply (Hstep_gen 96%nat 11%nat); [lia |].
        intros i Hi. lia.
      - replace (Z.of_nat 96 + Z.of_nat (12 - 1)%nat) with 107 by lia.
        exact Hq107. }
    (* Single-word pieces b, e, h. *)
    assert (Tb :
        Γ ⊢ ⟦ Expression.Advice Advice.A2 Rotation.cur ⟧ (HR, 25) = w Γ 25).
    { apply (word_at_last Γ Fixed.QSinsemilla2_1 Advice.A2 HR 25 0 Hq25).
      left. reflexivity. }
    assert (Te :
        Γ ⊢ ⟦ Expression.Advice Advice.A2 Rotation.cur ⟧ (HR, 57) = w Γ 57).
    { apply (word_at_last Γ Fixed.QSinsemilla2_1 Advice.A2 HR 57 0 Hq57).
      left. reflexivity. }
    assert (Th :
        Γ ⊢ ⟦ Expression.Advice Advice.A2 Rotation.cur ⟧ (HR, 108) =
          w Γ 108).
    { apply (word_at_last Γ Fixed.QSinsemilla2_1 Advice.A2 HR 108 2 Hq108).
      right. reflexivity. }
    unfold av, bv, cv, dv, ev, fv, gv, hv, z13av, z13cv, z1dv, z13fv, z1gv,
      z13gv, val.
    rewrite <- HcA, <- HcB, <- HcC, <- HcD, <- HcE, <- HcF, <- HcG, <- HcH.
    unfold adv.
    repeat rewrite <- eval_advice_cur_cell.
    repeat split.
    - exact Ta.
    - exact Tb.
    - exact Tc.
    - exact Td.
    - exact Te.
    - exact Tf.
    - exact Tg.
    - exact Th.
    - exact T13.
    - exact T39.
    - exact T52.
    - exact T71.
    - exact T84.
    - exact T96.
  Qed.

  (** ** Running-lookup chain corollaries *)

  Lemma zv_zero_of_eval
      (Γ : Assignment.t columns RegionId.t)
      (region : RegionId.t) (k : nat) (row : Z)
      (Hrow : row = Z.of_nat k)
      (H : eval_cell Γ (adv region Advice.A9 row) = 0) :
    zv Γ region k = 0.
  Proof.
    subst row.
    unfold zv.
    rewrite cur_val.
    unfold val.
    rewrite H.
    unfold UnOp.from.
    apply Zmod_0_l.
  Qed.

  Lemma zv_zero_of_val
      (Γ : Assignment.t columns RegionId.t)
      (region : RegionId.t) (k : nat) (row : Z)
      (Hrow : row = Z.of_nat k)
      (H : val Γ (adv region Advice.A9 row) = 0) :
    zv Γ region k = 0.
  Proof.
    subst row.
    unfold zv.
    rewrite cur_val.
    exact H.
  Qed.

  Lemma lookup_z_bound
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ)
      (region : RegionId.t) (count : nat) (Hcount : (count <= 25)%nat)
      (Hsel : forall j : nat, (j < count)%nat ->
        Γ.(Assignment.selector) Selector.QLookup region (Z.of_nat j) = 1 /\
        Γ.(Assignment.selector) Selector.QRunning region (Z.of_nat j) = 1)
      (n : nat) (Hn : (n <= count)%nat)
      (Hend : zv Γ region n = 0)
      (k : nat) (Hk : (k <= n)%nat) :
    0 <= zv Γ region k < 2 ^ (10 * Z.of_nat (n - k)%nat).
  Proof.
    apply (running_chain_bound Γ region n ltac:(lia));
      [| exact Hend | exact Hk].
    intros k' Hk'.
    destruct (Hsel k' ltac:(lia)) as [Hl Hr].
    exact (running_word_range Γ Hcircuit region k' Hl Hr).
  Qed.

  (** ** Piece-level integer identities *)

  Lemma piece_b_int
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ)
      (Hb0 : 0 <= b0v Γ < 2 ^ 4) (Hb3 : 0 <= b3v Γ < 2 ^ 4) :
    bv Γ = b0v Γ + b1v Γ * 2 ^ 4 + b2v Γ * 2 ^ 5 + b3v Γ * 2 ^ 6 /\
    0 <= bv Γ < 2 ^ 10 /\
    (b1v Γ = 0 \/ b1v Γ = 1) /\
    (b2v Γ = 0 \/ b2v Γ = 1).
  Proof.
    destruct (msg_b_facts Γ Hcircuit) as (Hsel & Hcb & Hcb0 & Hcb2 & Hcb3).
    destruct (NoteCommitMessagePieces.message_piece_b_sound Γ
      Selector.QNoteCommitOldB (ncr RegionId.NoteCommit.MessagePieceB) 0
      (enabled_nonzero Γ Selector.QNoteCommitOldB _ 0 Hsel)
      (old_gate_msg_b Γ Hcircuit (ncr RegionId.NoteCommit.MessagePieceB) 0))
      as (Hb1bool & Hb2bool & Hdec).
    assert (Eb : Γ ⊢ ⟦ Expression.Advice Advice.A6 Rotation.cur ⟧
        (ncr RegionId.NoteCommit.MessagePieceB, 0) = bv Γ)
      by (exact (cur_eq Γ _ _ _ _ Hcb)).
    assert (Eb0 : Γ ⊢ ⟦ Expression.Advice Advice.A7 Rotation.cur ⟧
        (ncr RegionId.NoteCommit.MessagePieceB, 0) = b0v Γ)
      by (exact (cur_eq Γ _ _ _ _ Hcb0)).
    assert (Eb1 : Γ ⊢ ⟦ Expression.Advice Advice.A8 Rotation.cur ⟧
        (ncr RegionId.NoteCommit.MessagePieceB, 0) = b1v Γ)
      by (exact (cur_val Γ _ Advice.A8 0)).
    assert (Eb2 : Γ ⊢ ⟦ Expression.Advice Advice.A7 Rotation.next ⟧
        (ncr RegionId.NoteCommit.MessagePieceB, 0) = b2v Γ)
      by (exact (next_eq Γ _ Advice.A7 0 1 eq_refl _ Hcb2)).
    assert (Eb3 : Γ ⊢ ⟦ Expression.Advice Advice.A8 Rotation.next ⟧
        (ncr RegionId.NoteCommit.MessagePieceB, 0) = b3v Γ)
      by (exact (next_eq Γ _ Advice.A8 0 1 eq_refl _ Hcb3)).
    rewrite Eb, Eb0, Eb1, Eb2, Eb3 in Hdec.
    rewrite Eb1 in Hb1bool.
    rewrite Eb2 in Hb2bool.
    unfold NCP.MessagePieceB.output in Hdec.
    cbn [NCP.MessagePieceB.b] in Hdec.
    pose proof (NoteCommitMessagePieces.isbool_cases _ Hb1bool) as Hb1c.
    pose proof (NoteCommitMessagePieces.isbool_cases _ Hb2bool) as Hb2c.
    destruct (NoteCommitMessagePieces.piece_b_exact _ _ _ _ _ Hdec Hb0 Hb1c
      Hb2c Hb3) as [Hint Hrange].
    exact (conj Hint (conj Hrange (conj Hb1c Hb2c))).
  Qed.

  Lemma piece_d_int
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ)
      (Hd2 : 0 <= d2v Γ < 2 ^ 8) :
    dv Γ = d0v Γ + d1v Γ * 2 + d2v Γ * 2 ^ 2 + z1dv Γ * 2 ^ 10 /\
    0 <= dv Γ < 2 ^ 60 /\
    (d0v Γ = 0 \/ d0v Γ = 1) /\
    (d1v Γ = 0 \/ d1v Γ = 1).
  Proof.
    destruct (telescopes Γ Hcircuit)
      as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ht52 & _ & _ & _).
    destruct (msg_d_facts Γ Hcircuit) as (Hsel & Hcd & Hcd1 & Hcd2 & Hcz).
    destruct (NoteCommitMessagePieces.message_piece_d_sound Γ
      Selector.QNoteCommitOldD (ncr RegionId.NoteCommit.MessagePieceD) 0
      (enabled_nonzero Γ Selector.QNoteCommitOldD _ 0 Hsel)
      (old_gate_msg_d Γ Hcircuit (ncr RegionId.NoteCommit.MessagePieceD) 0))
      as (Hd0bool & Hd1bool & Hdec).
    assert (Ed : Γ ⊢ ⟦ Expression.Advice Advice.A6 Rotation.cur ⟧
        (ncr RegionId.NoteCommit.MessagePieceD, 0) = dv Γ)
      by (exact (cur_eq Γ _ _ _ _ Hcd)).
    assert (Ed0 : Γ ⊢ ⟦ Expression.Advice Advice.A7 Rotation.cur ⟧
        (ncr RegionId.NoteCommit.MessagePieceD, 0) = d0v Γ)
      by (exact (cur_val Γ _ Advice.A7 0)).
    assert (Ed1 : Γ ⊢ ⟦ Expression.Advice Advice.A8 Rotation.cur ⟧
        (ncr RegionId.NoteCommit.MessagePieceD, 0) = d1v Γ)
      by (exact (cur_eq Γ _ _ _ _ Hcd1)).
    assert (Ed2 : Γ ⊢ ⟦ Expression.Advice Advice.A7 Rotation.next ⟧
        (ncr RegionId.NoteCommit.MessagePieceD, 0) = d2v Γ)
      by (exact (next_eq Γ _ Advice.A7 0 1 eq_refl _ Hcd2)).
    assert (Ed3 : Γ ⊢ ⟦ Expression.Advice Advice.A8 Rotation.next ⟧
        (ncr RegionId.NoteCommit.MessagePieceD, 0) = z1dv Γ)
      by (exact (next_eq Γ _ Advice.A8 0 1 eq_refl _ Hcz)).
    rewrite Ed, Ed0, Ed1, Ed2, Ed3 in Hdec.
    rewrite Ed0 in Hd0bool.
    rewrite Ed1 in Hd1bool.
    unfold NCP.MessagePieceD.output in Hdec.
    cbn [NCP.MessagePieceD.d] in Hdec.
    pose proof (NoteCommitMessagePieces.isbool_cases _ Hd0bool) as Hd0c.
    pose proof (NoteCommitMessagePieces.isbool_cases _ Hd1bool) as Hd1c.
    assert (Hz1d : 0 <= z1dv Γ < 2 ^ 50).
    { rewrite Ht52.
      pose proof (Lrun_bound Γ Hcircuit 52 5 ltac:(lia)) as HB.
      change (10 * Z.of_nat 5) with 50 in HB.
      exact HB. }
    destruct (NoteCommitMessagePieces.piece_d_exact _ _ _ _ _ Hdec Hd0c Hd1c
      Hd2 Hz1d) as [Hint Hrange].
    exact (conj Hint (conj Hrange (conj Hd0c Hd1c))).
  Qed.

  Lemma piece_e_int
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ)
      (He0 : 0 <= e0v Γ < 2 ^ 6) (He1 : 0 <= e1v Γ < 2 ^ 4) :
    ev Γ = e0v Γ + e1v Γ * 2 ^ 6 /\ 0 <= ev Γ < 2 ^ 10.
  Proof.
    destruct (msg_e_facts Γ Hcircuit) as (Hsel & Hce & Hce0 & Hce1).
    pose proof (NoteCommitMessagePieces.message_piece_e_sound Γ
      Selector.QNoteCommitOldE (ncr RegionId.NoteCommit.MessagePieceE) 0
      (enabled_nonzero Γ Selector.QNoteCommitOldE _ 0 Hsel)
      (old_gate_msg_e Γ Hcircuit (ncr RegionId.NoteCommit.MessagePieceE) 0))
      as Hdec.
    assert (Ee : Γ ⊢ ⟦ Expression.Advice Advice.A6 Rotation.cur ⟧
        (ncr RegionId.NoteCommit.MessagePieceE, 0) = ev Γ)
      by (exact (cur_eq Γ _ _ _ _ Hce)).
    assert (Ee0 : Γ ⊢ ⟦ Expression.Advice Advice.A7 Rotation.cur ⟧
        (ncr RegionId.NoteCommit.MessagePieceE, 0) = e0v Γ)
      by (exact (cur_eq Γ _ _ _ _ Hce0)).
    assert (Ee1 : Γ ⊢ ⟦ Expression.Advice Advice.A8 Rotation.cur ⟧
        (ncr RegionId.NoteCommit.MessagePieceE, 0) = e1v Γ)
      by (exact (cur_eq Γ _ _ _ _ Hce1)).
    rewrite Ee, Ee0, Ee1 in Hdec.
    unfold NCP.MessagePieceE.output in Hdec.
    cbn [NCP.MessagePieceE.e] in Hdec.
    exact (NoteCommitMessagePieces.piece_e_exact _ _ _ Hdec He0 He1).
  Qed.

  Lemma piece_g_int
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ)
      (Hg1 : 0 <= g1v Γ < 2 ^ 9) :
    gv Γ = g0v Γ + g1v Γ * 2 + z1gv Γ * 2 ^ 10 /\
    0 <= gv Γ < 2 ^ 250 /\
    (g0v Γ = 0 \/ g0v Γ = 1).
  Proof.
    destruct (telescopes Γ Hcircuit)
      as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ht84 & _).
    destruct (msg_g_facts Γ Hcircuit) as (Hsel & Hcg & Hcg1 & Hcg2).
    destruct (NoteCommitMessagePieces.message_piece_g_sound Γ
      Selector.QNoteCommitOldG (ncr RegionId.NoteCommit.MessagePieceG) 0
      (enabled_nonzero Γ Selector.QNoteCommitOldG _ 0 Hsel)
      (old_gate_msg_g Γ Hcircuit (ncr RegionId.NoteCommit.MessagePieceG) 0))
      as (Hg0bool & Hdec).
    assert (Eg : Γ ⊢ ⟦ Expression.Advice Advice.A6 Rotation.cur ⟧
        (ncr RegionId.NoteCommit.MessagePieceG, 0) = gv Γ)
      by (exact (cur_eq Γ _ _ _ _ Hcg)).
    assert (Eg0 : Γ ⊢ ⟦ Expression.Advice Advice.A7 Rotation.cur ⟧
        (ncr RegionId.NoteCommit.MessagePieceG, 0) = g0v Γ)
      by (exact (cur_val Γ _ Advice.A7 0)).
    assert (Eg1 : Γ ⊢ ⟦ Expression.Advice Advice.A6 Rotation.next ⟧
        (ncr RegionId.NoteCommit.MessagePieceG, 0) = g1v Γ)
      by (exact (next_eq Γ _ Advice.A6 0 1 eq_refl _ Hcg1)).
    assert (Eg2 : Γ ⊢ ⟦ Expression.Advice Advice.A7 Rotation.next ⟧
        (ncr RegionId.NoteCommit.MessagePieceG, 0) = z1gv Γ)
      by (exact (next_eq Γ _ Advice.A7 0 1 eq_refl _ Hcg2)).
    rewrite Eg, Eg0, Eg1, Eg2 in Hdec.
    rewrite Eg0 in Hg0bool.
    unfold NCP.MessagePieceG.output in Hdec.
    cbn [NCP.MessagePieceG.g] in Hdec.
    pose proof (NoteCommitMessagePieces.isbool_cases _ Hg0bool) as Hg0c.
    assert (Hz1g : 0 <= z1gv Γ < 2 ^ 240).
    { rewrite Ht84.
      pose proof (Lrun_bound Γ Hcircuit 84 24 ltac:(lia)) as HB.
      change (10 * Z.of_nat 24) with 240 in HB.
      exact HB. }
    destruct (NoteCommitMessagePieces.piece_g_exact _ _ _ _ Hdec Hg0c Hg1
      Hz1g) as [Hint Hrange].
    exact (conj Hint (conj Hrange Hg0c)).
  Qed.

  Lemma piece_h_int
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ)
      (Hh0 : 0 <= h0v Γ < 2 ^ 5) :
    hv Γ = h0v Γ + h1v Γ * 2 ^ 5 /\
    0 <= hv Γ < 2 ^ 10 /\
    (h1v Γ = 0 \/ h1v Γ = 1).
  Proof.
    destruct (msg_h_facts Γ Hcircuit) as (Hsel & Hch & Hch0).
    destruct (NoteCommitMessagePieces.message_piece_h_sound Γ
      Selector.QNoteCommitOldH (ncr RegionId.NoteCommit.MessagePieceH) 0
      (enabled_nonzero Γ Selector.QNoteCommitOldH _ 0 Hsel)
      (old_gate_msg_h Γ Hcircuit (ncr RegionId.NoteCommit.MessagePieceH) 0))
      as (Hh1bool & Hdec).
    assert (Eh : Γ ⊢ ⟦ Expression.Advice Advice.A6 Rotation.cur ⟧
        (ncr RegionId.NoteCommit.MessagePieceH, 0) = hv Γ)
      by (exact (cur_eq Γ _ _ _ _ Hch)).
    assert (Eh0 : Γ ⊢ ⟦ Expression.Advice Advice.A7 Rotation.cur ⟧
        (ncr RegionId.NoteCommit.MessagePieceH, 0) = h0v Γ)
      by (exact (cur_eq Γ _ _ _ _ Hch0)).
    assert (Eh1 : Γ ⊢ ⟦ Expression.Advice Advice.A8 Rotation.cur ⟧
        (ncr RegionId.NoteCommit.MessagePieceH, 0) = h1v Γ)
      by (exact (cur_val Γ _ Advice.A8 0)).
    rewrite Eh, Eh0, Eh1 in Hdec.
    rewrite Eh1 in Hh1bool.
    unfold NCP.MessagePieceH.output in Hdec.
    cbn [NCP.MessagePieceH.h] in Hdec.
    pose proof (NoteCommitMessagePieces.isbool_cases _ Hh1bool) as Hh1c.
    destruct (NoteCommitMessagePieces.piece_h_exact _ _ _ Hdec Hh0 Hh1c)
      as [Hint Hrange].
    exact (conj Hint (conj Hrange Hh1c)).
  Qed.

  (** ** Input-level integer identities *)

  Definition apv (Γ : Assignment.t columns RegionId.t) : Z :=
    val Γ (adv (ncr RegionId.NoteCommit.XGDLookup) Advice.A9 0).
  Definition bcpv (Γ : Assignment.t columns RegionId.t) : Z :=
    val Γ (adv (ncr RegionId.NoteCommit.XPKDLookup) Advice.A9 0).
  Definition efpv (Γ : Assignment.t columns RegionId.t) : Z :=
    val Γ (adv (ncr RegionId.NoteCommit.RhoLookup) Advice.A9 0).
  Definition ggpv (Γ : Assignment.t columns RegionId.t) : Z :=
    val Γ (adv (ncr RegionId.NoteCommit.PsiLookup) Advice.A9 0).

  Definition k0gv (Γ : Assignment.t columns RegionId.t) : Z :=
    val Γ (adv (nyr RegionId.NoteCommit.YSubject.GD
      RegionId.NoteCommit.YCanonicity.RangeK0) Advice.A9 0).
  Definition k2gv (Γ : Assignment.t columns RegionId.t) : Z :=
    val Γ (adv (nyr RegionId.NoteCommit.YSubject.GD
      RegionId.NoteCommit.YCanonicity.RangeK2) Advice.A9 0).
  Definition k0pv (Γ : Assignment.t columns RegionId.t) : Z :=
    val Γ (adv (nyr RegionId.NoteCommit.YSubject.PkD
      RegionId.NoteCommit.YCanonicity.RangeK0) Advice.A9 0).
  Definition k2pv (Γ : Assignment.t columns RegionId.t) : Z :=
    val Γ (adv (nyr RegionId.NoteCommit.YSubject.PkD
      RegionId.NoteCommit.YCanonicity.RangeK2) Advice.A9 0).

  Lemma gd_x_int
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ)
      (Hb0 : 0 <= b0v Γ < 2 ^ 4) :
    gdxv Γ = av Γ + b0v Γ * 2 ^ 250 + b1v Γ * 2 ^ 254 /\
    0 <= av Γ < 2 ^ 250.
  Proof.
    destruct (telescopes Γ Hcircuit)
      as (Hta & _ & _ & _ & _ & _ & _ & _ & Ht13 & _ & _ & _ & _ & _).
    destruct (input_gd_facts Γ Hcircuit)
      as (Hcx & Hcb0 & Hcb1 & Hca & Hcap & Hcz13 & Hczp & Hsel).
    destruct (NoteCommitMessagePieces.input_g_d_sound Γ
      Selector.QNoteCommitOldGd (ncr RegionId.NoteCommit.InputGD) 0
      (enabled_nonzero Γ Selector.QNoteCommitOldGd _ 0 Hsel)
      (old_gate_input_gd Γ Hcircuit (ncr RegionId.NoteCommit.InputGD) 0))
      as (Hdec & Hap & He1 & He2 & He3).
    destruct (msg_b_facts Γ Hcircuit) as (HselB & _ & _ & _ & _).
    destruct (NoteCommitMessagePieces.message_piece_b_sound Γ
      Selector.QNoteCommitOldB (ncr RegionId.NoteCommit.MessagePieceB) 0
      (enabled_nonzero Γ Selector.QNoteCommitOldB _ 0 HselB)
      (old_gate_msg_b Γ Hcircuit (ncr RegionId.NoteCommit.MessagePieceB) 0))
      as (Hb1bool & _ & _).
    assert (EbB : Γ ⊢ ⟦ Expression.Advice Advice.A8 Rotation.cur ⟧
        (ncr RegionId.NoteCommit.MessagePieceB, 0) = b1v Γ)
      by (exact (cur_val Γ _ Advice.A8 0)).
    rewrite EbB in Hb1bool.
    pose proof (NoteCommitMessagePieces.isbool_cases _ Hb1bool) as Hb1c.
    assert (E6 : Γ ⊢ ⟦ Expression.Advice Advice.A6 Rotation.cur ⟧
        (ncr RegionId.NoteCommit.InputGD, 0) = gdxv Γ)
      by (exact (cur_eq Γ _ _ _ _ Hcx)).
    assert (E7 : Γ ⊢ ⟦ Expression.Advice Advice.A7 Rotation.cur ⟧
        (ncr RegionId.NoteCommit.InputGD, 0) = b0v Γ)
      by (exact (cur_eq Γ _ _ _ _ Hcb0)).
    assert (E7n : Γ ⊢ ⟦ Expression.Advice Advice.A7 Rotation.next ⟧
        (ncr RegionId.NoteCommit.InputGD, 0) = b1v Γ)
      by (exact (next_eq Γ _ Advice.A7 0 1 eq_refl _ Hcb1)).
    assert (E8 : Γ ⊢ ⟦ Expression.Advice Advice.A8 Rotation.cur ⟧
        (ncr RegionId.NoteCommit.InputGD, 0) = av Γ)
      by (exact (cur_eq Γ _ _ _ _ Hca)).
    assert (E8n : Γ ⊢ ⟦ Expression.Advice Advice.A8 Rotation.next ⟧
        (ncr RegionId.NoteCommit.InputGD, 0) = apv Γ)
      by (exact (next_eq Γ _ Advice.A8 0 1 eq_refl _ Hcap)).
    assert (E9 : Γ ⊢ ⟦ Expression.Advice Advice.A9 Rotation.cur ⟧
        (ncr RegionId.NoteCommit.InputGD, 0) = z13av Γ)
      by (exact (cur_eq Γ _ _ _ _ Hcz13)).
    assert (E9n : Γ ⊢ ⟦ Expression.Advice Advice.A9 Rotation.next ⟧
        (ncr RegionId.NoteCommit.InputGD, 0) =
        val Γ (adv (ncr RegionId.NoteCommit.XGDLookup) Advice.A9 13))
      by (exact (next_eq Γ _ Advice.A9 0 1 eq_refl _ Hczp)).
    rewrite E6, E7, E7n, E8 in Hdec.
    rewrite E7, E7n, E8, E8n in Hap.
    rewrite E7, E7n in He1.
    rewrite E7n, E9 in He2.
    rewrite E7n, E9n in He3.
    unfold NCP.InputGD.output in Hdec, Hap.
    cbn [NCP.InputGD.gd_x NCP.InputGD.a_prime] in Hdec, Hap.
    assert (Hav : 0 <= av Γ < 2 ^ 250).
    { rewrite Hta.
      pose proof (Lrun_bound Γ Hcircuit 0 25 ltac:(lia)) as HB.
      change (10 * Z.of_nat 25) with 250 in HB.
      exact HB. }
    assert (Hsplit : av Γ =
        SinsemillaHash.digit_sum (Lrun Γ 0 13) + 2 ^ 130 * z13av Γ).
    { assert (L : Lrun Γ 0 25 = Lrun Γ 0 13 ++ Lrun Γ 13 12).
      { unfold Lrun. exact (run_split Γ 0 13 12). }
      rewrite Hta, L, digit_sum_app, Lrun_length.
      change (10 * Z.of_nat 13) with 130.
      rewrite <- Ht13.
      reflexivity. }
    assert (Ha130 : b1v Γ = 1 -> av Γ < 2 ^ 130).
    { intros H1.
      destruct He2 as [Hz | Hz]; [lia |].
      rewrite Hz in Hsplit.
      pose proof (Lrun_bound Γ Hcircuit 0 13 ltac:(lia)) as HB.
      change (10 * Z.of_nat 13) with 130 in HB.
      lia. }
    assert (Hap_range : b1v Γ = 1 -> 0 <= apv Γ < 2 ^ 130).
    { intros H1.
      destruct He3 as [Hz | Hz]; [lia |].
      assert (Hend : zv Γ (ncr RegionId.NoteCommit.XGDLookup) 13 = 0)
        by (exact (zv_zero_of_val Γ _ 13 13 eq_refl Hz)).
      pose proof (lookup_z_bound Γ Hcircuit _ 13 ltac:(lia)
        (xgd_lookup_selectors Γ Hcircuit) 13 ltac:(lia) Hend 0 ltac:(lia))
        as HB.
      change (10 * Z.of_nat (13 - 0)) with 130 in HB.
      rewrite <- (zv_val Γ _ 0 0 eq_refl) in HB.
      change (val Γ (adv (ncr RegionId.NoteCommit.XGDLookup) Advice.A9 0))
        with (apv Γ) in HB.
      exact HB. }
    destruct (NoteCommitMessagePieces.decomposition_250_4_1
      (gdxv Γ) (av Γ) (b0v Γ) (b1v Γ) (apv Γ)
      Hdec Hap Hav Hb0 Hb1c He1 Ha130 Hap_range) as [Hint _].
    exact (conj Hint Hav).
  Qed.

  Lemma pkd_x_int
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ)
      (Hb3 : 0 <= b3v Γ < 2 ^ 4) :
    pkdxv Γ = b3v Γ + cv Γ * 2 ^ 4 + d0v Γ * 2 ^ 254 /\
    0 <= cv Γ < 2 ^ 250.
  Proof.
    destruct (telescopes Γ Hcircuit)
      as (_ & _ & Htc & _ & _ & _ & _ & _ & _ & Ht39 & _ & _ & _ & _).
    destruct (input_pkd_facts Γ Hcircuit)
      as (Hcx & Hcb3 & Hcd0 & Hcc & Hcbcp & Hcz13 & Hczp & Hsel).
    destruct (NoteCommitMessagePieces.input_pk_d_sound Γ
      Selector.QNoteCommitOldPkd (ncr RegionId.NoteCommit.InputPkD) 0
      (enabled_nonzero Γ Selector.QNoteCommitOldPkd _ 0 Hsel)
      (old_gate_input_pkd Γ Hcircuit (ncr RegionId.NoteCommit.InputPkD) 0))
      as (Hdec & Hap & He1 & He2).
    destruct (msg_d_facts Γ Hcircuit) as (HselD & _ & _ & _ & _).
    destruct (NoteCommitMessagePieces.message_piece_d_sound Γ
      Selector.QNoteCommitOldD (ncr RegionId.NoteCommit.MessagePieceD) 0
      (enabled_nonzero Γ Selector.QNoteCommitOldD _ 0 HselD)
      (old_gate_msg_d Γ Hcircuit (ncr RegionId.NoteCommit.MessagePieceD) 0))
      as (Hd0bool & _ & _).
    assert (EdD : Γ ⊢ ⟦ Expression.Advice Advice.A7 Rotation.cur ⟧
        (ncr RegionId.NoteCommit.MessagePieceD, 0) = d0v Γ)
      by (exact (cur_val Γ _ Advice.A7 0)).
    rewrite EdD in Hd0bool.
    pose proof (NoteCommitMessagePieces.isbool_cases _ Hd0bool) as Hd0c.
    assert (E6 : Γ ⊢ ⟦ Expression.Advice Advice.A6 Rotation.cur ⟧
        (ncr RegionId.NoteCommit.InputPkD, 0) = pkdxv Γ)
      by (exact (cur_eq Γ _ _ _ _ Hcx)).
    assert (E7 : Γ ⊢ ⟦ Expression.Advice Advice.A7 Rotation.cur ⟧
        (ncr RegionId.NoteCommit.InputPkD, 0) = b3v Γ)
      by (exact (cur_eq Γ _ _ _ _ Hcb3)).
    assert (E7n : Γ ⊢ ⟦ Expression.Advice Advice.A7 Rotation.next ⟧
        (ncr RegionId.NoteCommit.InputPkD, 0) = d0v Γ)
      by (exact (next_eq Γ _ Advice.A7 0 1 eq_refl _ Hcd0)).
    assert (E8 : Γ ⊢ ⟦ Expression.Advice Advice.A8 Rotation.cur ⟧
        (ncr RegionId.NoteCommit.InputPkD, 0) = cv Γ)
      by (exact (cur_eq Γ _ _ _ _ Hcc)).
    assert (E8n : Γ ⊢ ⟦ Expression.Advice Advice.A8 Rotation.next ⟧
        (ncr RegionId.NoteCommit.InputPkD, 0) = bcpv Γ)
      by (exact (next_eq Γ _ Advice.A8 0 1 eq_refl _ Hcbcp)).
    assert (E9 : Γ ⊢ ⟦ Expression.Advice Advice.A9 Rotation.cur ⟧
        (ncr RegionId.NoteCommit.InputPkD, 0) = z13cv Γ)
      by (exact (cur_eq Γ _ _ _ _ Hcz13)).
    assert (E9n : Γ ⊢ ⟦ Expression.Advice Advice.A9 Rotation.next ⟧
        (ncr RegionId.NoteCommit.InputPkD, 0) =
        val Γ (adv (ncr RegionId.NoteCommit.XPKDLookup) Advice.A9 14))
      by (exact (next_eq Γ _ Advice.A9 0 1 eq_refl _ Hczp)).
    rewrite E6, E7, E7n, E8 in Hdec.
    rewrite E7, E7n, E8, E8n in Hap.
    rewrite E7n, E9 in He1.
    rewrite E7n, E9n in He2.
    unfold NCP.InputPKD.output in Hdec, Hap.
    cbn [NCP.InputPKD.pkd_x NCP.InputPKD.b3_c_prime] in Hdec, Hap.
    assert (Hcv : 0 <= cv Γ < 2 ^ 250).
    { rewrite Htc.
      pose proof (Lrun_bound Γ Hcircuit 26 25 ltac:(lia)) as HB.
      change (10 * Z.of_nat 25) with 250 in HB.
      exact HB. }
    assert (Hsplit : cv Γ =
        SinsemillaHash.digit_sum (Lrun Γ 26 13) + 2 ^ 130 * z13cv Γ).
    { assert (L : Lrun Γ 26 25 = Lrun Γ 26 13 ++ Lrun Γ 39 12).
      { unfold Lrun. exact (run_split Γ 26 13 12). }
      rewrite Htc, L, digit_sum_app, Lrun_length.
      change (10 * Z.of_nat 13) with 130.
      rewrite <- Ht39.
      reflexivity. }
    assert (Hc130 : d0v Γ = 1 -> cv Γ < 2 ^ 130).
    { intros H1.
      destruct He1 as [Hz | Hz]; [lia |].
      rewrite Hz in Hsplit.
      pose proof (Lrun_bound Γ Hcircuit 26 13 ltac:(lia)) as HB.
      change (10 * Z.of_nat 13) with 130 in HB.
      lia. }
    assert (Hbcp_range : d0v Γ = 1 -> 0 <= bcpv Γ < 2 ^ 140).
    { intros H1.
      destruct He2 as [Hz | Hz]; [lia |].
      assert (Hend : zv Γ (ncr RegionId.NoteCommit.XPKDLookup) 14 = 0)
        by (exact (zv_zero_of_val Γ _ 14 14 eq_refl Hz)).
      pose proof (lookup_z_bound Γ Hcircuit _ 14 ltac:(lia)
        (xpkd_lookup_selectors Γ Hcircuit) 14 ltac:(lia) Hend 0 ltac:(lia))
        as HB.
      change (10 * Z.of_nat (14 - 0)) with 140 in HB.
      rewrite <- (zv_val Γ _ 0 0 eq_refl) in HB.
      change (val Γ (adv (ncr RegionId.NoteCommit.XPKDLookup) Advice.A9 0))
        with (bcpv Γ) in HB.
      exact HB. }
    destruct (NoteCommitMessagePieces.decomposition_4_250_1
      (pkdxv Γ) (b3v Γ) (cv Γ) (d0v Γ) (bcpv Γ)
      Hdec Hap Hb3 Hcv Hd0c Hc130 Hbcp_range) as [Hint _].
    exact (conj Hint Hcv).
  Qed.

  Lemma value_int
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ)
      (Hd2 : 0 <= d2v Γ < 2 ^ 8) (He0 : 0 <= e0v Γ < 2 ^ 6) :
    voldv Γ = d2v Γ + z1dv Γ * 2 ^ 8 + e0v Γ * 2 ^ 58 /\
    0 <= voldv Γ < 2 ^ 64.
  Proof.
    destruct (telescopes Γ Hcircuit)
      as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ht52 & _ & _ & _).
    destruct (input_value_facts Γ Hcircuit)
      as (Hcv0 & Hcd2 & Hcz1d & Hce0 & Hsel).
    pose proof (NoteCommitMessagePieces.input_value_sound Γ
      Selector.QNoteCommitOldValue (ncr RegionId.NoteCommit.InputValue) 0
      (enabled_nonzero Γ Selector.QNoteCommitOldValue _ 0 Hsel)
      (old_gate_input_value Γ Hcircuit (ncr RegionId.NoteCommit.InputValue) 0))
      as Hdec.
    assert (E6 : Γ ⊢ ⟦ Expression.Advice Advice.A6 Rotation.cur ⟧
        (ncr RegionId.NoteCommit.InputValue, 0) = voldv Γ)
      by (exact (cur_eq Γ _ _ _ _ Hcv0)).
    assert (E7 : Γ ⊢ ⟦ Expression.Advice Advice.A7 Rotation.cur ⟧
        (ncr RegionId.NoteCommit.InputValue, 0) = d2v Γ)
      by (exact (cur_eq Γ _ _ _ _ Hcd2)).
    assert (E8 : Γ ⊢ ⟦ Expression.Advice Advice.A8 Rotation.cur ⟧
        (ncr RegionId.NoteCommit.InputValue, 0) = z1dv Γ)
      by (exact (cur_eq Γ _ _ _ _ Hcz1d)).
    assert (E9 : Γ ⊢ ⟦ Expression.Advice Advice.A9 Rotation.cur ⟧
        (ncr RegionId.NoteCommit.InputValue, 0) = e0v Γ)
      by (exact (cur_eq Γ _ _ _ _ Hce0)).
    rewrite E6, E7, E8, E9 in Hdec.
    unfold NCP.InputValue.output in Hdec.
    cbn [NCP.InputValue.value] in Hdec.
    assert (Hz1d : 0 <= z1dv Γ < 2 ^ 50).
    { rewrite Ht52.
      pose proof (Lrun_bound Γ Hcircuit 52 5 ltac:(lia)) as HB.
      change (10 * Z.of_nat 5) with 50 in HB.
      exact HB. }
    destruct (NoteCommitMessagePieces.decomposition_value _ _ _ _ Hdec Hd2
      Hz1d He0) as [Hint Hrange].
    split; [exact Hint | rewrite Hint; exact Hrange].
  Qed.

  Lemma rho_int
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ)
      (He1r : 0 <= e1v Γ < 2 ^ 4) :
    rhov Γ = e1v Γ + fv Γ * 2 ^ 4 + g0v Γ * 2 ^ 254 /\
    0 <= fv Γ < 2 ^ 250.
  Proof.
    destruct (telescopes Γ Hcircuit)
      as (_ & _ & _ & _ & _ & Htf & _ & _ & _ & _ & _ & Ht71 & _ & _).
    destruct (input_rho_facts Γ Hcircuit)
      as (Hcr & Hce1 & Hcg0 & Hcf & Hcefp & Hcz13 & Hczp & Hsel).
    destruct (NoteCommitMessagePieces.input_rho_sound Γ
      Selector.QNoteCommitOldRho (ncr RegionId.NoteCommit.InputRho) 0
      (enabled_nonzero Γ Selector.QNoteCommitOldRho _ 0 Hsel)
      (old_gate_input_rho Γ Hcircuit (ncr RegionId.NoteCommit.InputRho) 0))
      as (Hdec & Hap & He1 & He2).
    destruct (msg_g_facts Γ Hcircuit) as (HselG & _ & _ & _).
    destruct (NoteCommitMessagePieces.message_piece_g_sound Γ
      Selector.QNoteCommitOldG (ncr RegionId.NoteCommit.MessagePieceG) 0
      (enabled_nonzero Γ Selector.QNoteCommitOldG _ 0 HselG)
      (old_gate_msg_g Γ Hcircuit (ncr RegionId.NoteCommit.MessagePieceG) 0))
      as (Hg0bool & _).
    assert (EgG : Γ ⊢ ⟦ Expression.Advice Advice.A7 Rotation.cur ⟧
        (ncr RegionId.NoteCommit.MessagePieceG, 0) = g0v Γ)
      by (exact (cur_val Γ _ Advice.A7 0)).
    rewrite EgG in Hg0bool.
    pose proof (NoteCommitMessagePieces.isbool_cases _ Hg0bool) as Hg0c.
    assert (E6 : Γ ⊢ ⟦ Expression.Advice Advice.A6 Rotation.cur ⟧
        (ncr RegionId.NoteCommit.InputRho, 0) = rhov Γ)
      by (exact (cur_eq Γ _ _ _ _ Hcr)).
    assert (E7 : Γ ⊢ ⟦ Expression.Advice Advice.A7 Rotation.cur ⟧
        (ncr RegionId.NoteCommit.InputRho, 0) = e1v Γ)
      by (exact (cur_eq Γ _ _ _ _ Hce1)).
    assert (E7n : Γ ⊢ ⟦ Expression.Advice Advice.A7 Rotation.next ⟧
        (ncr RegionId.NoteCommit.InputRho, 0) = g0v Γ)
      by (exact (next_eq Γ _ Advice.A7 0 1 eq_refl _ Hcg0)).
    assert (E8 : Γ ⊢ ⟦ Expression.Advice Advice.A8 Rotation.cur ⟧
        (ncr RegionId.NoteCommit.InputRho, 0) = fv Γ)
      by (exact (cur_eq Γ _ _ _ _ Hcf)).
    assert (E8n : Γ ⊢ ⟦ Expression.Advice Advice.A8 Rotation.next ⟧
        (ncr RegionId.NoteCommit.InputRho, 0) = efpv Γ)
      by (exact (next_eq Γ _ Advice.A8 0 1 eq_refl _ Hcefp)).
    assert (E9 : Γ ⊢ ⟦ Expression.Advice Advice.A9 Rotation.cur ⟧
        (ncr RegionId.NoteCommit.InputRho, 0) = z13fv Γ)
      by (exact (cur_eq Γ _ _ _ _ Hcz13)).
    assert (E9n : Γ ⊢ ⟦ Expression.Advice Advice.A9 Rotation.next ⟧
        (ncr RegionId.NoteCommit.InputRho, 0) =
        val Γ (adv (ncr RegionId.NoteCommit.RhoLookup) Advice.A9 14))
      by (exact (next_eq Γ _ Advice.A9 0 1 eq_refl _ Hczp)).
    rewrite E6, E7, E7n, E8 in Hdec.
    rewrite E7, E7n, E8, E8n in Hap.
    rewrite E7n, E9 in He1.
    rewrite E7n, E9n in He2.
    unfold NCP.InputRho.output in Hdec, Hap.
    cbn [NCP.InputRho.rho NCP.InputRho.e1_f_prime] in Hdec, Hap.
    assert (Hfv : 0 <= fv Γ < 2 ^ 250).
    { rewrite Htf.
      pose proof (Lrun_bound Γ Hcircuit 58 25 ltac:(lia)) as HB.
      change (10 * Z.of_nat 25) with 250 in HB.
      exact HB. }
    assert (Hsplit : fv Γ =
        SinsemillaHash.digit_sum (Lrun Γ 58 13) + 2 ^ 130 * z13fv Γ).
    { assert (L : Lrun Γ 58 25 = Lrun Γ 58 13 ++ Lrun Γ 71 12).
      { unfold Lrun. exact (run_split Γ 58 13 12). }
      rewrite Htf, L, digit_sum_app, Lrun_length.
      change (10 * Z.of_nat 13) with 130.
      rewrite <- Ht71.
      reflexivity. }
    assert (Hf130 : g0v Γ = 1 -> fv Γ < 2 ^ 130).
    { intros H1.
      destruct He1 as [Hz | Hz]; [lia |].
      rewrite Hz in Hsplit.
      pose proof (Lrun_bound Γ Hcircuit 58 13 ltac:(lia)) as HB.
      change (10 * Z.of_nat 13) with 130 in HB.
      lia. }
    assert (Hefp_range : g0v Γ = 1 -> 0 <= efpv Γ < 2 ^ 140).
    { intros H1.
      destruct He2 as [Hz | Hz]; [lia |].
      assert (Hend : zv Γ (ncr RegionId.NoteCommit.RhoLookup) 14 = 0)
        by (exact (zv_zero_of_val Γ _ 14 14 eq_refl Hz)).
      pose proof (lookup_z_bound Γ Hcircuit _ 14 ltac:(lia)
        (rho_lookup_selectors Γ Hcircuit) 14 ltac:(lia) Hend 0 ltac:(lia))
        as HB.
      change (10 * Z.of_nat (14 - 0)) with 140 in HB.
      rewrite <- (zv_val Γ _ 0 0 eq_refl) in HB.
      change (val Γ (adv (ncr RegionId.NoteCommit.RhoLookup) Advice.A9 0))
        with (efpv Γ) in HB.
      exact HB. }
    destruct (NoteCommitMessagePieces.decomposition_4_250_1
      (rhov Γ) (e1v Γ) (fv Γ) (g0v Γ) (efpv Γ)
      Hdec Hap He1r Hfv Hg0c Hf130 Hefp_range) as [Hint _].
    exact (conj Hint Hfv).
  Qed.

  Lemma psi_int
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ)
      (Hg1 : 0 <= g1v Γ < 2 ^ 9) (Hh0 : 0 <= h0v Γ < 2 ^ 5) :
    psiv Γ = g1v Γ + z1gv Γ * 2 ^ 9 + h0v Γ * 2 ^ 249 + h1v Γ * 2 ^ 254 /\
    0 <= z1gv Γ < 2 ^ 240.
  Proof.
    destruct (telescopes Γ Hcircuit)
      as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ht84 & Ht96).
    destruct (input_psi_facts Γ Hcircuit)
      as (Hcp & Hch0 & Hcg1 & Hch1 & Hcg2 & Hcggp & Hcz13 & Hczp & Hsel).
    destruct (NoteCommitMessagePieces.input_psi_sound Γ
      Selector.QNoteCommitOldPsi (ncr RegionId.NoteCommit.InputPsi) 0
      (enabled_nonzero Γ Selector.QNoteCommitOldPsi _ 0 Hsel)
      (old_gate_input_psi Γ Hcircuit (ncr RegionId.NoteCommit.InputPsi) 0))
      as (Hdec & Hap & He1 & He2 & He3).
    destruct (msg_h_facts Γ Hcircuit) as (HselH & _ & _).
    destruct (NoteCommitMessagePieces.message_piece_h_sound Γ
      Selector.QNoteCommitOldH (ncr RegionId.NoteCommit.MessagePieceH) 0
      (enabled_nonzero Γ Selector.QNoteCommitOldH _ 0 HselH)
      (old_gate_msg_h Γ Hcircuit (ncr RegionId.NoteCommit.MessagePieceH) 0))
      as (Hh1bool & _).
    assert (EhH : Γ ⊢ ⟦ Expression.Advice Advice.A8 Rotation.cur ⟧
        (ncr RegionId.NoteCommit.MessagePieceH, 0) = h1v Γ)
      by (exact (cur_val Γ _ Advice.A8 0)).
    rewrite EhH in Hh1bool.
    pose proof (NoteCommitMessagePieces.isbool_cases _ Hh1bool) as Hh1c.
    assert (E6 : Γ ⊢ ⟦ Expression.Advice Advice.A6 Rotation.cur ⟧
        (ncr RegionId.NoteCommit.InputPsi, 0) = psiv Γ)
      by (exact (cur_eq Γ _ _ _ _ Hcp)).
    assert (E6n : Γ ⊢ ⟦ Expression.Advice Advice.A6 Rotation.next ⟧
        (ncr RegionId.NoteCommit.InputPsi, 0) = h0v Γ)
      by (exact (next_eq Γ _ Advice.A6 0 1 eq_refl _ Hch0)).
    assert (E7 : Γ ⊢ ⟦ Expression.Advice Advice.A7 Rotation.cur ⟧
        (ncr RegionId.NoteCommit.InputPsi, 0) = g1v Γ)
      by (exact (cur_eq Γ _ _ _ _ Hcg1)).
    assert (E7n : Γ ⊢ ⟦ Expression.Advice Advice.A7 Rotation.next ⟧
        (ncr RegionId.NoteCommit.InputPsi, 0) = h1v Γ)
      by (exact (next_eq Γ _ Advice.A7 0 1 eq_refl _ Hch1)).
    assert (E8 : Γ ⊢ ⟦ Expression.Advice Advice.A8 Rotation.cur ⟧
        (ncr RegionId.NoteCommit.InputPsi, 0) = z1gv Γ)
      by (exact (cur_eq Γ _ _ _ _ Hcg2)).
    assert (E8n : Γ ⊢ ⟦ Expression.Advice Advice.A8 Rotation.next ⟧
        (ncr RegionId.NoteCommit.InputPsi, 0) = ggpv Γ)
      by (exact (next_eq Γ _ Advice.A8 0 1 eq_refl _ Hcggp)).
    assert (E9 : Γ ⊢ ⟦ Expression.Advice Advice.A9 Rotation.cur ⟧
        (ncr RegionId.NoteCommit.InputPsi, 0) = z13gv Γ)
      by (exact (cur_eq Γ _ _ _ _ Hcz13)).
    assert (E9n : Γ ⊢ ⟦ Expression.Advice Advice.A9 Rotation.next ⟧
        (ncr RegionId.NoteCommit.InputPsi, 0) =
        val Γ (adv (ncr RegionId.NoteCommit.PsiLookup) Advice.A9 13))
      by (exact (next_eq Γ _ Advice.A9 0 1 eq_refl _ Hczp)).
    rewrite E6, E6n, E7, E7n, E8 in Hdec.
    rewrite E7, E7n, E8, E8n in Hap.
    rewrite E7n, E6n in He1.
    rewrite E7n, E9 in He2.
    rewrite E7n, E9n in He3.
    unfold NCP.InputPsi.output in Hdec, Hap.
    cbn [NCP.InputPsi.psi NCP.InputPsi.g1_g2_prime] in Hdec, Hap.
    assert (Hz1g : 0 <= z1gv Γ < 2 ^ 240).
    { rewrite Ht84.
      pose proof (Lrun_bound Γ Hcircuit 84 24 ltac:(lia)) as HB.
      change (10 * Z.of_nat 24) with 240 in HB.
      exact HB. }
    assert (Hsplit : z1gv Γ =
        SinsemillaHash.digit_sum (Lrun Γ 84 12) + 2 ^ 120 * z13gv Γ).
    { assert (L : Lrun Γ 84 24 = Lrun Γ 84 12 ++ Lrun Γ 96 12).
      { unfold Lrun. exact (run_split Γ 84 12 12). }
      rewrite Ht84, L, digit_sum_app, Lrun_length.
      change (10 * Z.of_nat 12) with 120.
      rewrite <- Ht96.
      reflexivity. }
    assert (Hlow130 : h1v Γ = 1 -> g1v Γ + z1gv Γ * 2 ^ 9 < 2 ^ 130).
    { intros H1.
      destruct He2 as [Hz | Hz]; [lia |].
      rewrite Hz in Hsplit.
      pose proof (Lrun_bound Γ Hcircuit 84 12 ltac:(lia)) as HB.
      change (10 * Z.of_nat 12) with 120 in HB.
      lia. }
    assert (Hggp_range : h1v Γ = 1 -> 0 <= ggpv Γ < 2 ^ 130).
    { intros H1.
      destruct He3 as [Hz | Hz]; [lia |].
      assert (Hend : zv Γ (ncr RegionId.NoteCommit.PsiLookup) 13 = 0)
        by (exact (zv_zero_of_val Γ _ 13 13 eq_refl Hz)).
      pose proof (lookup_z_bound Γ Hcircuit _ 13 ltac:(lia)
        (psi_lookup_selectors Γ Hcircuit) 13 ltac:(lia) Hend 0 ltac:(lia))
        as HB.
      change (10 * Z.of_nat (13 - 0)) with 130 in HB.
      rewrite <- (zv_val Γ _ 0 0 eq_refl) in HB.
      change (val Γ (adv (ncr RegionId.NoteCommit.PsiLookup) Advice.A9 0))
        with (ggpv Γ) in HB.
      exact HB. }
    destruct (NoteCommitMessagePieces.decomposition_9_240_5_1
      (psiv Γ) (g1v Γ) (z1gv Γ) (h0v Γ) (h1v Γ) (ggpv Γ)
      Hdec Hap Hg1 Hz1g Hh0 Hh1c He1 Hlow130 Hggp_range) as [Hint _].
    exact (conj Hint Hz1g).
  Qed.

  (** ** Y-canonicity: the [b_2]/[d_1] cells are the y-parity bits *)

  Lemma y_parity_gd
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ)
      (Hk0 : 0 <= k0gv Γ < 2 ^ 9) (Hk2 : 0 <= k2gv Γ < 2 ^ 4)
      (Hb2c : b2v Γ = 0 \/ b2v Γ = 1) :
    b2v Γ = gdyv Γ mod 2.
  Proof.
    set (YG := nyr RegionId.NoteCommit.YSubject.GD
      RegionId.NoteCommit.YCanonicity.Gate).
    set (JL := nyr RegionId.NoteCommit.YSubject.GD
      RegionId.NoteCommit.YCanonicity.JLookup).
    set (JP := nyr RegionId.NoteCommit.YSubject.GD
      RegionId.NoteCommit.YCanonicity.JPrimeLookup).
    destruct (y_gate_facts_gd Γ Hcircuit)
      as (Hsel & Hcy & Hck0 & Hck2 & Hcj0 & Hcj1 & Hcj13 & Hcjp0 & Hcjp13).
    destruct (NoteCommitMessagePieces.y_coordinate_checks_sound Γ
      Selector.QNoteCommitOldYCanon YG 0
      (enabled_nonzero Γ Selector.QNoteCommitOldYCanon _ 0 Hsel)
      (old_gate_y_canon Γ Hcircuit YG 0))
      as (Hk3bool & Hj & Hy & Hjp & He1 & He2 & He3).
    assert (E5 : Γ ⊢ ⟦ Expression.Advice Advice.A5 Rotation.cur ⟧ (YG, 0) =
        gdyv Γ)
      by (exact (cur_eq Γ _ _ _ _ Hcy)).
    assert (E6 : Γ ⊢ ⟦ Expression.Advice Advice.A6 Rotation.cur ⟧ (YG, 0) =
        b2v Γ)
      by (exact (cur_val Γ _ Advice.A6 0)).
    assert (E7 : Γ ⊢ ⟦ Expression.Advice Advice.A7 Rotation.cur ⟧ (YG, 0) =
        k0gv Γ)
      by (exact (cur_eq Γ _ _ _ _ Hck0)).
    assert (E8 : Γ ⊢ ⟦ Expression.Advice Advice.A8 Rotation.cur ⟧ (YG, 0) =
        k2gv Γ)
      by (exact (cur_eq Γ _ _ _ _ Hck2)).
    assert (E9 : Γ ⊢ ⟦ Expression.Advice Advice.A9 Rotation.cur ⟧ (YG, 0) =
        val Γ (adv YG Advice.A9 0))
      by (exact (cur_val Γ _ Advice.A9 0)).
    assert (E5n : Γ ⊢ ⟦ Expression.Advice Advice.A5 Rotation.next ⟧ (YG, 0) =
        val Γ (adv JL Advice.A9 0))
      by (exact (next_eq Γ _ Advice.A5 0 1 eq_refl _ Hcj0)).
    assert (E6n : Γ ⊢ ⟦ Expression.Advice Advice.A6 Rotation.next ⟧ (YG, 0) =
        val Γ (adv JL Advice.A9 1))
      by (exact (next_eq Γ _ Advice.A6 0 1 eq_refl _ Hcj1)).
    assert (E7n : Γ ⊢ ⟦ Expression.Advice Advice.A7 Rotation.next ⟧ (YG, 0) =
        val Γ (adv JL Advice.A9 13))
      by (exact (next_eq Γ _ Advice.A7 0 1 eq_refl _ Hcj13)).
    assert (E8n : Γ ⊢ ⟦ Expression.Advice Advice.A8 Rotation.next ⟧ (YG, 0) =
        val Γ (adv JP Advice.A9 0))
      by (exact (next_eq Γ _ Advice.A8 0 1 eq_refl _ Hcjp0)).
    assert (E9n : Γ ⊢ ⟦ Expression.Advice Advice.A9 Rotation.next ⟧ (YG, 0) =
        val Γ (adv JP Advice.A9 13))
      by (exact (next_eq Γ _ Advice.A9 0 1 eq_refl _ Hcjp13)).
    rewrite E9 in Hk3bool.
    rewrite E5n, E6, E7, E6n, E8, E9 in Hj.
    rewrite E5, E6, E7, E6n, E8, E9 in Hy.
    rewrite E8n, E6, E7, E6n, E8, E9 in Hjp.
    rewrite E9, E8 in He1.
    rewrite E9, E7n in He2.
    rewrite E9, E9n in He3.
    unfold NCP.YCoordinateChecks.output in Hj, Hy, Hjp.
    cbn [NCP.YCoordinateChecks.j NCP.YCoordinateChecks.y
      NCP.YCoordinateChecks.j_prime] in Hj, Hy, Hjp.
    rewrite <- Hj in Hy, Hjp.
    pose proof (NoteCommitMessagePieces.isbool_cases _ Hk3bool) as Hk3c.
    (* J-lookup chain: strict, 25 rows. *)
    destruct (j_lookup_facts_gd Γ Hcircuit) as (HselJL & Hz25).
    assert (Hend25 : zv Γ JL 25 = 0)
      by (exact (zv_zero_of_eval Γ JL 25 25 eq_refl Hz25)).
    assert (Hjb : 0 <= val Γ (adv JL Advice.A9 0) < 2 ^ 250).
    { rewrite (zv_val Γ JL 0 0 eq_refl).
      pose proof (lookup_z_bound Γ Hcircuit JL 25 ltac:(lia) HselJL 25
        ltac:(lia) Hend25 0 ltac:(lia)) as HB.
      change (10 * Z.of_nat (25 - 0)) with 250 in HB.
      exact HB. }
    assert (Hz1jb : 0 <= val Γ (adv JL Advice.A9 1) < 2 ^ 240).
    { rewrite (zv_val Γ JL 1 1 eq_refl).
      pose proof (lookup_z_bound Γ Hcircuit JL 25 ltac:(lia) HselJL 25
        ltac:(lia) Hend25 1 ltac:(lia)) as HB.
      change (10 * Z.of_nat (25 - 1)) with 240 in HB.
      exact HB. }
    assert (Hj130 : val Γ (adv YG Advice.A9 0) = 1 ->
        val Γ (adv JL Advice.A9 0) < 2 ^ 130).
    { intros H1.
      destruct He2 as [Hz | Hz]; [lia |].
      assert (Hend13 : zv Γ JL 13 = 0)
        by (exact (zv_zero_of_val Γ JL 13 13 eq_refl Hz)).
      pose proof (lookup_z_bound Γ Hcircuit JL 25 ltac:(lia) HselJL 13
        ltac:(lia) Hend13 0 ltac:(lia)) as HB.
      change (10 * Z.of_nat (13 - 0)) with 130 in HB.
      rewrite <- (zv_val Γ JL 0 0 eq_refl) in HB.
      lia. }
    assert (Hjp130 : val Γ (adv YG Advice.A9 0) = 1 ->
        0 <= val Γ (adv JP Advice.A9 0) < 2 ^ 130).
    { intros H1.
      destruct He3 as [Hz | Hz]; [lia |].
      assert (Hend13 : zv Γ JP 13 = 0)
        by (exact (zv_zero_of_val Γ JP 13 13 eq_refl Hz)).
      pose proof (lookup_z_bound Γ Hcircuit JP 13 ltac:(lia)
        (j_prime_lookup_selectors_gd Γ Hcircuit) 13
        ltac:(lia) Hend13 0 ltac:(lia)) as HB.
      change (10 * Z.of_nat (13 - 0)) with 130 in HB.
      rewrite <- (zv_val Γ JP 0 0 eq_refl) in HB.
      exact HB. }
    destruct (NoteCommitMessagePieces.decomposition_250_4_1
      (gdyv Γ) (val Γ (adv JL Advice.A9 0)) (k2gv Γ)
      (val Γ (adv YG Advice.A9 0)) (val Γ (adv JP Advice.A9 0))
      Hy Hjp Hjb Hk2 Hk3c He1 Hj130 Hjp130) as [Hyint _].
    destruct (NoteCommitMessagePieces.piece_j_exact
      (val Γ (adv JL Advice.A9 0)) (b2v Γ) (k0gv Γ)
      (val Γ (adv JL Advice.A9 1)) Hj Hb2c Hk0 Hz1jb) as [Hjint _].
    apply (NoteCommitMessagePieces.lsb_parity (gdyv Γ) (b2v Γ)
      (k0gv Γ + val Γ (adv JL Advice.A9 1) * 2 ^ 9 +
        k2gv Γ * 2 ^ 249 + val Γ (adv YG Advice.A9 0) * 2 ^ 253)
      Hb2c).
    lia.
  Qed.

  Lemma y_parity_pkd
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ)
      (Hk0 : 0 <= k0pv Γ < 2 ^ 9) (Hk2 : 0 <= k2pv Γ < 2 ^ 4)
      (Hd1c : d1v Γ = 0 \/ d1v Γ = 1) :
    d1v Γ = pkdyv Γ mod 2.
  Proof.
    set (YG := nyr RegionId.NoteCommit.YSubject.PkD
      RegionId.NoteCommit.YCanonicity.Gate).
    set (JL := nyr RegionId.NoteCommit.YSubject.PkD
      RegionId.NoteCommit.YCanonicity.JLookup).
    set (JP := nyr RegionId.NoteCommit.YSubject.PkD
      RegionId.NoteCommit.YCanonicity.JPrimeLookup).
    destruct (y_gate_facts_pkd Γ Hcircuit)
      as (Hsel & Hcy & Hck0 & Hck2 & Hcj0 & Hcj1 & Hcj13 & Hcjp0 & Hcjp13).
    destruct (NoteCommitMessagePieces.y_coordinate_checks_sound Γ
      Selector.QNoteCommitOldYCanon YG 0
      (enabled_nonzero Γ Selector.QNoteCommitOldYCanon _ 0 Hsel)
      (old_gate_y_canon Γ Hcircuit YG 0))
      as (Hk3bool & Hj & Hy & Hjp & He1 & He2 & He3).
    assert (E5 : Γ ⊢ ⟦ Expression.Advice Advice.A5 Rotation.cur ⟧ (YG, 0) =
        pkdyv Γ)
      by (exact (cur_eq Γ _ _ _ _ Hcy)).
    assert (E6 : Γ ⊢ ⟦ Expression.Advice Advice.A6 Rotation.cur ⟧ (YG, 0) =
        d1v Γ)
      by (exact (cur_val Γ _ Advice.A6 0)).
    assert (E7 : Γ ⊢ ⟦ Expression.Advice Advice.A7 Rotation.cur ⟧ (YG, 0) =
        k0pv Γ)
      by (exact (cur_eq Γ _ _ _ _ Hck0)).
    assert (E8 : Γ ⊢ ⟦ Expression.Advice Advice.A8 Rotation.cur ⟧ (YG, 0) =
        k2pv Γ)
      by (exact (cur_eq Γ _ _ _ _ Hck2)).
    assert (E9 : Γ ⊢ ⟦ Expression.Advice Advice.A9 Rotation.cur ⟧ (YG, 0) =
        val Γ (adv YG Advice.A9 0))
      by (exact (cur_val Γ _ Advice.A9 0)).
    assert (E5n : Γ ⊢ ⟦ Expression.Advice Advice.A5 Rotation.next ⟧ (YG, 0) =
        val Γ (adv JL Advice.A9 0))
      by (exact (next_eq Γ _ Advice.A5 0 1 eq_refl _ Hcj0)).
    assert (E6n : Γ ⊢ ⟦ Expression.Advice Advice.A6 Rotation.next ⟧ (YG, 0) =
        val Γ (adv JL Advice.A9 1))
      by (exact (next_eq Γ _ Advice.A6 0 1 eq_refl _ Hcj1)).
    assert (E7n : Γ ⊢ ⟦ Expression.Advice Advice.A7 Rotation.next ⟧ (YG, 0) =
        val Γ (adv JL Advice.A9 13))
      by (exact (next_eq Γ _ Advice.A7 0 1 eq_refl _ Hcj13)).
    assert (E8n : Γ ⊢ ⟦ Expression.Advice Advice.A8 Rotation.next ⟧ (YG, 0) =
        val Γ (adv JP Advice.A9 0))
      by (exact (next_eq Γ _ Advice.A8 0 1 eq_refl _ Hcjp0)).
    assert (E9n : Γ ⊢ ⟦ Expression.Advice Advice.A9 Rotation.next ⟧ (YG, 0) =
        val Γ (adv JP Advice.A9 13))
      by (exact (next_eq Γ _ Advice.A9 0 1 eq_refl _ Hcjp13)).
    rewrite E9 in Hk3bool.
    rewrite E5n, E6, E7, E6n, E8, E9 in Hj.
    rewrite E5, E6, E7, E6n, E8, E9 in Hy.
    rewrite E8n, E6, E7, E6n, E8, E9 in Hjp.
    rewrite E9, E8 in He1.
    rewrite E9, E7n in He2.
    rewrite E9, E9n in He3.
    unfold NCP.YCoordinateChecks.output in Hj, Hy, Hjp.
    cbn [NCP.YCoordinateChecks.j NCP.YCoordinateChecks.y
      NCP.YCoordinateChecks.j_prime] in Hj, Hy, Hjp.
    rewrite <- Hj in Hy, Hjp.
    pose proof (NoteCommitMessagePieces.isbool_cases _ Hk3bool) as Hk3c.
    destruct (j_lookup_facts_pkd Γ Hcircuit) as (HselJL & Hz25).
    assert (Hend25 : zv Γ JL 25 = 0)
      by (exact (zv_zero_of_eval Γ JL 25 25 eq_refl Hz25)).
    assert (Hjb : 0 <= val Γ (adv JL Advice.A9 0) < 2 ^ 250).
    { rewrite (zv_val Γ JL 0 0 eq_refl).
      pose proof (lookup_z_bound Γ Hcircuit JL 25 ltac:(lia) HselJL 25
        ltac:(lia) Hend25 0 ltac:(lia)) as HB.
      change (10 * Z.of_nat (25 - 0)) with 250 in HB.
      exact HB. }
    assert (Hz1jb : 0 <= val Γ (adv JL Advice.A9 1) < 2 ^ 240).
    { rewrite (zv_val Γ JL 1 1 eq_refl).
      pose proof (lookup_z_bound Γ Hcircuit JL 25 ltac:(lia) HselJL 25
        ltac:(lia) Hend25 1 ltac:(lia)) as HB.
      change (10 * Z.of_nat (25 - 1)) with 240 in HB.
      exact HB. }
    assert (Hj130 : val Γ (adv YG Advice.A9 0) = 1 ->
        val Γ (adv JL Advice.A9 0) < 2 ^ 130).
    { intros H1.
      destruct He2 as [Hz | Hz]; [lia |].
      assert (Hend13 : zv Γ JL 13 = 0)
        by (exact (zv_zero_of_val Γ JL 13 13 eq_refl Hz)).
      pose proof (lookup_z_bound Γ Hcircuit JL 25 ltac:(lia) HselJL 13
        ltac:(lia) Hend13 0 ltac:(lia)) as HB.
      change (10 * Z.of_nat (13 - 0)) with 130 in HB.
      rewrite <- (zv_val Γ JL 0 0 eq_refl) in HB.
      lia. }
    assert (Hjp130 : val Γ (adv YG Advice.A9 0) = 1 ->
        0 <= val Γ (adv JP Advice.A9 0) < 2 ^ 130).
    { intros H1.
      destruct He3 as [Hz | Hz]; [lia |].
      assert (Hend13 : zv Γ JP 13 = 0)
        by (exact (zv_zero_of_val Γ JP 13 13 eq_refl Hz)).
      pose proof (lookup_z_bound Γ Hcircuit JP 13 ltac:(lia)
        (j_prime_lookup_selectors_pkd Γ Hcircuit) 13
        ltac:(lia) Hend13 0 ltac:(lia)) as HB.
      change (10 * Z.of_nat (13 - 0)) with 130 in HB.
      rewrite <- (zv_val Γ JP 0 0 eq_refl) in HB.
      exact HB. }
    destruct (NoteCommitMessagePieces.decomposition_250_4_1
      (pkdyv Γ) (val Γ (adv JL Advice.A9 0)) (k2pv Γ)
      (val Γ (adv YG Advice.A9 0)) (val Γ (adv JP Advice.A9 0))
      Hy Hjp Hjb Hk2 Hk3c He1 Hj130 Hjp130) as [Hyint _].
    destruct (NoteCommitMessagePieces.piece_j_exact
      (val Γ (adv JL Advice.A9 0)) (d1v Γ) (k0pv Γ)
      (val Γ (adv JL Advice.A9 1)) Hj Hd1c Hk0 Hz1jb) as [Hjint _].
    apply (NoteCommitMessagePieces.lsb_parity (pkdyv Γ) (d1v Γ)
      (k0pv Γ + val Γ (adv JL Advice.A9 1) * 2 ^ 9 +
        k2pv Γ * 2 ^ 249 + val Γ (adv YG Advice.A9 0) * 2 ^ 253)
      Hd1c).
    lia.
  Qed.

  (** ** The side condition: the eleven short-lookup range cells

      The [Which.Old] instance of the selector-plane idealization (see the
      file header and [note_commit_new_short_lookup_ok]).  The predicate
      names exactly the missing bounds; the [A9] short-range column is
      variant-independent ([synthesize_short_range]). *)

  Definition short_ok
      (Γ : Assignment.t columns RegionId.t) (r : RegionId.t) (bits : Z)
      : Prop :=
    0 <= val Γ (adv r Advice.A9 0) < 2 ^ bits.

  Definition old_note_short_lookup_ok
      (Γ : Assignment.t columns RegionId.t) : Prop :=
    short_ok Γ (ncr RegionId.NoteCommit.RangeB0) 4 /\
    short_ok Γ (ncr RegionId.NoteCommit.RangeB3) 4 /\
    short_ok Γ (ncr RegionId.NoteCommit.RangeD2) 8 /\
    short_ok Γ (ncr RegionId.NoteCommit.RangeE0) 6 /\
    short_ok Γ (ncr RegionId.NoteCommit.RangeE1) 4 /\
    short_ok Γ (ncr RegionId.NoteCommit.RangeG1) 9 /\
    short_ok Γ (ncr RegionId.NoteCommit.RangeH0) 5 /\
    short_ok Γ (nyr RegionId.NoteCommit.YSubject.GD
      RegionId.NoteCommit.YCanonicity.RangeK0) 9 /\
    short_ok Γ (nyr RegionId.NoteCommit.YSubject.GD
      RegionId.NoteCommit.YCanonicity.RangeK2) 4 /\
    short_ok Γ (nyr RegionId.NoteCommit.YSubject.PkD
      RegionId.NoteCommit.YCanonicity.RangeK0) 9 /\
    short_ok Γ (nyr RegionId.NoteCommit.YSubject.PkD
      RegionId.NoteCommit.YCanonicity.RangeK2) 4.

  (** ** The word-list split and the per-piece [words_le] identification *)

  (** The 109 grid words of the [Which.Old] hash-to-point region — the
      definition matches [OrchardValidActionInputs.old_note_words]
      ([circuit_proof/valid_action_inputs.v]) definitionally ([HR] unfolds
      to [RegionId.NoteCommit Which.Old HashToPoint]).  Kept local so this
      file stays upstream of [valid_action_inputs.v]. *)
  Definition old_note_words (Γ : Assignment.t columns RegionId.t) : list Z :=
    SinsemillaHash.hash_words Γ Fixed.QSinsemilla2_1 Advice.A2 HR 109.

  Lemma old_words_split
      (Γ : Assignment.t columns RegionId.t) :
    SinsemillaHash.hash_words Γ Fixed.QSinsemilla2_1 Advice.A2 HR 109 =
      Lrun Γ 0 25 ++ Lrun Γ 25 1 ++ Lrun Γ 26 25 ++ Lrun Γ 51 6 ++
      Lrun Γ 57 1 ++ Lrun Γ 58 25 ++ Lrun Γ 83 25 ++ Lrun Γ 108 1.
  Proof. reflexivity. Qed.

  Lemma words_le_run
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ)
      (off n : nat) (Hrange : (off + n <= 109)%nat)
      (x : Z) (Hx : x = SinsemillaHash.digit_sum (Lrun Γ off n)) :
    SinsemillaSpec.words_le n x = Lrun Γ off n.
  Proof.
    subst x.
    rewrite <- (Lrun_length Γ off n) at 1.
    apply SinsemillaHash.words_le_digit_sum.
    exact (Lrun_forall Γ Hcircuit off n Hrange).
  Qed.

  Lemma Lrun_single
      (Γ : Assignment.t columns RegionId.t) (off : nat) :
    SinsemillaHash.digit_sum (Lrun Γ off 1) = w Γ (Z.of_nat off).
  Proof.
    unfold Lrun.
    cbn [List.seq List.map SinsemillaHash.digit_sum].
    replace (Z.of_nat off + Z.of_nat 0) with (Z.of_nat off) by lia.
    lia.
  Qed.

  (** ** The hashed words are the old-note commitment message

      The 109 grid words of the [Which.Old] hash-to-point region equal
      [OrchardSpec.note_commit_message] at the circuit's old-note reads:
      the [GDOld] witness point, the WITNESSED [pk_d_old] point (the
      [AddressIntegrity.WitnessPkD] cells — [read_pk_d_old]'s cells; see the
      file header), and the [VOld]/[RhoOld]/[PsiOld] witness cells.  This is
      the words-canonicity leg of the old-note integrity proof, derived from
      [Holds] plus the short-lookup side condition
      ([old_note_short_lookup_ok] — the second conjunct of
      [OrchardValidActionInputs.old_note_witness_ok]). *)
  Theorem note_commit_old_words_correct
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (Hshort : old_note_short_lookup_ok Γ) :
    old_note_words Γ =
      OrchardSpec.note_commit_message
        (OrchardActionInputs.read_point Γ
          (RegionId.WitnessInput RegionId.WitnessInput.GDOld))
        (OrchardActionInputs.read_point Γ
          (RegionId.AddressIntegrity RegionId.AddressIntegrity.WitnessPkD))
        (OrchardActionInputs.read Γ
          (RegionId.WitnessInput RegionId.WitnessInput.VOld))
        (OrchardActionInputs.read Γ
          (RegionId.WitnessInput RegionId.WitnessInput.RhoOld))
        (OrchardActionInputs.read Γ
          (RegionId.WitnessInput RegionId.WitnessInput.PsiOld)).
  Proof.
    destruct Hshort
      as (Hb0 & Hb3 & Hd2 & He0 & He1s & Hg1 & Hh0 & Hk0g & Hk2g & Hk0p
        & Hk2p).
    destruct (telescopes Γ Hcircuit)
      as (Hta & Htb & Htc & Htd & Hte & Htf & Htg & Hth & Ht13 & Ht39
        & Ht52 & Ht71 & Ht84 & Ht96).
    destruct (piece_b_int Γ Hcircuit Hb0 Hb3) as (HbI & HbR & Hb1c & Hb2c).
    destruct (piece_d_int Γ Hcircuit Hd2) as (HdI & HdR & Hd0c & Hd1c).
    destruct (piece_e_int Γ Hcircuit He0 He1s) as (HeI & HeR).
    destruct (piece_g_int Γ Hcircuit Hg1) as (HgI & HgR & Hg0c).
    destruct (piece_h_int Γ Hcircuit Hh0) as (HhI & HhR & Hh1c).
    destruct (gd_x_int Γ Hcircuit Hb0) as (HgdI & HaR).
    destruct (pkd_x_int Γ Hcircuit Hb3) as (HpkdI & HcR).
    destruct (value_int Γ Hcircuit Hd2 He0) as (HvI & _).
    destruct (rho_int Γ Hcircuit He1s) as (HrI & HfR).
    destruct (psi_int Γ Hcircuit Hg1 Hh0) as (HpI & Hz1gR).
    pose proof (y_parity_gd Γ Hcircuit Hk0g Hk2g Hb2c) as Hb2par.
    pose proof (y_parity_pkd Γ Hcircuit Hk0p Hk2p Hd1c) as Hd1par.
    assert (Hz1d50 : 0 <= z1dv Γ < 2 ^ 50).
    { rewrite Ht52.
      pose proof (Lrun_bound Γ Hcircuit 52 5 ltac:(lia)) as HB.
      change (10 * Z.of_nat 5) with 50 in HB.
      exact HB. }
    pose proof (NoteCommitMessagePieces.hashed_words_of_note_commit_pieces
      (av Γ) (bv Γ) (cv Γ) (dv Γ) (ev Γ) (fv Γ) (gv Γ) (hv Γ)
      (b0v Γ) (b1v Γ) (b2v Γ) (b3v Γ)
      (d0v Γ) (d1v Γ) (d2v Γ) (z1dv Γ)
      (e0v Γ) (e1v Γ)
      (g0v Γ) (g1v Γ) (z1gv Γ)
      (h0v Γ) (h1v Γ)
      (gdxv Γ) (pkdxv Γ) (voldv Γ) (rhov Γ) (psiv Γ)
      HaR HcR HfR
      Hb0 Hb1c Hb2c Hb3
      Hd0c Hd1c Hd2 Hz1d50
      He0 He1s
      Hg0c Hg1 Hz1gR
      Hh0 Hh1c
      HbI HdI HeI HgI HhI
      HgdI HpkdI HvI HrI HpI) as Hwords.
    (* Per-piece word-list identification. *)
    assert (Wa : SinsemillaSpec.words_le 25 (av Γ) = Lrun Γ 0 25)
      by (exact (words_le_run Γ Hcircuit 0 25 ltac:(lia) _ Hta)).
    assert (Wb : SinsemillaSpec.words_le 1 (bv Γ) = Lrun Γ 25 1).
    { apply (words_le_run Γ Hcircuit 25 1 ltac:(lia)).
      rewrite Lrun_single.
      exact Htb. }
    assert (Wc : SinsemillaSpec.words_le 25 (cv Γ) = Lrun Γ 26 25)
      by (exact (words_le_run Γ Hcircuit 26 25 ltac:(lia) _ Htc)).
    assert (Wd : SinsemillaSpec.words_le 6 (dv Γ) = Lrun Γ 51 6)
      by (exact (words_le_run Γ Hcircuit 51 6 ltac:(lia) _ Htd)).
    assert (We : SinsemillaSpec.words_le 1 (ev Γ) = Lrun Γ 57 1).
    { apply (words_le_run Γ Hcircuit 57 1 ltac:(lia)).
      rewrite Lrun_single.
      exact Hte. }
    assert (Wf : SinsemillaSpec.words_le 25 (fv Γ) = Lrun Γ 58 25)
      by (exact (words_le_run Γ Hcircuit 58 25 ltac:(lia) _ Htf)).
    assert (Wg : SinsemillaSpec.words_le 25 (gv Γ) = Lrun Γ 83 25)
      by (exact (words_le_run Γ Hcircuit 83 25 ltac:(lia) _ Htg)).
    assert (Wh : SinsemillaSpec.words_le 1 (hv Γ) = Lrun Γ 108 1).
    { apply (words_le_run Γ Hcircuit 108 1 ltac:(lia)).
      rewrite Lrun_single.
      exact Hth. }
    (* Assembly. *)
    transitivity (SinsemillaSpec.words_le 109
      (NoteCommitMessagePieces.note_commit_packed
        (gdxv Γ) (b2v Γ) (pkdxv Γ) (d1v Γ) (voldv Γ) (rhov Γ) (psiv Γ))).
    { unfold old_note_words.
      rewrite (old_words_split Γ).
      rewrite <- Wa, <- Wb, <- Wc, <- Wd, <- We, <- Wf, <- Wg, <- Wh.
      exact Hwords. }
    unfold OrchardSpec.note_commit_message.
    f_equal.
    rewrite Hb2par, Hd1par.
    reflexivity.
  Qed.
End OldNoteWords.
