(** * Old-note commitment opening: the end-to-end integrity theorem

    From a satisfying assignment, the witnessed old-note fields open the
    witnessed [cm_old]:

    [NoteCommit^Orchard_rcm_old(g⋆_d_old, pk⋆_d_old, v_old, ρ_old, ψ_old)
      = cm_old]

    with the protocol-level (group-multiple) blinding term — the honest
    branch of §4.18.4 'Old note commitment integrity', in exactly the shape
    of [OrchardValidActionInputs.old_note_commit_integrity]
    ([circuit_proof/valid_action_inputs.v]).  Structure, mirroring the
    [Which.New] CMX lane at [Which.Old]:

    - the NoteCommitR fixed-base leg ([Which.Old] instance of
      [circuit_proof/note_commit_r/out.v]'s K-out): ladder facts peeled from
      [OldNoteWords.old_instance_facts], the per-window/distinctness chain of
      [circuit_proof/ladder/{main,note_commit_r}.v] (the certificate bridges
      are Γ-free and reused), and [full_with_rows_scalar_mul_correct];
    - witness elimination at the [Which.Old] region
      ([table_us_free_of_oncurve] with the on-curve and non-residue
      discriminant facts) and the protocol bridge
      [NoteCommitRMulProtocol.note_commit_r_mul_protocol]: the blinding
      point is [mul_note_commit_r rcm_old] for the windowed scalar read off
      the region;
    - the "M + [r] R" complete addition ([circuit_proof/note_commit/add.v]
      mirror), the variant-1 hash fold
      ([OldNoteHash.note_commit_old_hash_point_correct]) and the word
      identification ([OldNoteWords.note_commit_old_words_correct]);
    - the [NoteCommitOldEquality] region's two [Copy] facts, pinning the
      computed commitment point to the witnessed [cm_old] cells (both
      coordinates — [in_cm_old] is a full point).

    Side conditions ([old_note_witness_ok]): the Sinsemilla incomplete-add
    nondegeneracy of the witnessed 109-word old-note message and the eleven
    short-lookup range facts ([OldNoteWords.old_note_short_lookup_ok]) — the
    [note_commit_witness_ok] shape of the [Which.New] lane
    ([circuit_proof/note_commit/cmx.v]). *)

Require Import Garden.Halo2.main.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.lemmas.
Require Import Garden.Orchard.columns.
Require Garden.Orchard.circuit.
Require Garden.Orchard.circuit.note_commit.
Require Garden.Orchard.constants.fixed_bases.note_commit_r.
Require Garden.Halo2.halo2_gadgets.sinsemilla.chip.
Require Import Garden.Halo2.halo2_gadgets.sinsemilla.chip_proof.
Require Import Garden.Halo2.halo2_gadgets.sinsemilla.hash_to_point_proof.
Require Import Garden.Halo2.halo2_gadgets.sinsemilla.spec.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.spec.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.window_disc.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.fixed_window_canonical.
Require Import Garden.EllipticCurve.Pallas.
Require Import Garden.Orchard.Pallas.Generators.
Require Import Garden.Orchard.Pallas.GeneratorsOrder.
Require Import Garden.Halo2.PallasModel.
Require Import Garden.Orchard.protocol_spec.
Require Import Garden.Orchard.circuit_proof.internal_spec.
Require Import Garden.Orchard.circuit_proof.inputs.
Require Import Garden.Orchard.circuit_proof.facts.
Require Import Garden.Orchard.circuit_proof.merkle.
Require Import Garden.Orchard.circuit_proof.fixed_base.main.
Require Import Garden.Orchard.circuit_proof.us_free.main.
Require Import Garden.Orchard.circuit_proof.ladder.main.
Require Import Garden.Orchard.circuit_proof.ladder.note_commit_r.
Require Import Garden.Orchard.circuit_proof.note_commit_r.out.
Require Import Garden.Orchard.circuit_proof.note_commit_r.sign_cert.
Require Import Garden.Orchard.circuit_proof.note_commit_r.disc_cert.
Require Import Garden.Orchard.circuit_proof.protocol_mul.note_commit_r.
Require Import Garden.Orchard.circuit_proof.typed_inputs.full_width.
Require Import Garden.Orchard.circuit_proof.note_commit.hash.
Require Import Garden.Orchard.circuit_proof.note_commit.add.
Require Import Garden.Orchard.circuit_proof.old_note.words.
Require Import Garden.Orchard.circuit_proof.old_note.hash.
Require Import Garden.Field.Field.
Require Import Garden.Field.Lemmas.
Require Import Garden.Field.Sqrt.
Require Import Garden.Plonky3.M.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Lists.List.
Require Import Stdlib.micromega.Lia.

Import ListNotations.

#[local] Existing Instance Primes.PallasPIsPrime.

Global Open Scope Z_scope.

Module NC := Garden.Orchard.circuit.note_commit.
Module SChip := Garden.Halo2.halo2_gadgets.sinsemilla.chip.

Module OldNoteOpen.
  Import OrchardActionFixedBase.
  Import FixedBaseLadder.

  (* The consumed ladder/certificate lemmas carry [is_square]/[field_sqrt]/
     [fixed_window_point_canonical] over the concrete Pallas modulus;
     conversion must compare them by congruence, never unfold ([modpow] at
     the ~2^253 exponent blows the term up). *)
  Strategy opaque
    [is_square modpow modpow_pos field_sqrt fixed_window_point_canonical].

  Local Notation Holds Γ :=
    (circuit_holds Γ
      Garden.Orchard.circuit.synthesize
      (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)).

  (* The [Which.Old] NoteCommitR incomplete-additions region. *)
  Local Notation NCRO :=
    (RegionId.NoteCommit RegionId.NoteCommit.Which.Old
      RegionId.NoteCommit.FixedBaseIncomplete).

  (** ** Ownership-track readers

      Byte-identical to the [OrchardValidActionInputs] readers
      ([circuit_proof/valid_action_inputs.v]); kept local so this file stays
      upstream of the consumer. *)

  Definition read_pk_d_old (Γ : Assignment.t columns RegionId.t) : Point.t :=
    OrchardActionInputs.read_point Γ
      (RegionId.AddressIntegrity RegionId.AddressIntegrity.WitnessPkD).

  Definition read_rcm_old (Γ : Assignment.t columns RegionId.t) : Z :=
    OrchardActionInputs.read_scalar_from_windows Γ NCRO 85.

  Lemma read_pk_d_old_read (Γ : Assignment.t columns RegionId.t) :
    read_pk_d_old Γ =
    OrchardActionInputs.read_point Γ
      (RegionId.AddressIntegrity RegionId.AddressIntegrity.WitnessPkD).
  Proof. reflexivity. Qed.

  Lemma read_rcm_old_eq (Γ : Assignment.t columns RegionId.t) :
    read_rcm_old Γ = read_scalar_from_windows Γ NCRO 85.
  Proof. reflexivity. Qed.

  Lemma in_g_d_old_read (Γ : Assignment.t columns RegionId.t) :
    OrchardSpec.in_g_d_old (OrchardActionInputs.read_action_inputs Γ) =
    OrchardActionInputs.read_point Γ
      (RegionId.WitnessInput RegionId.WitnessInput.GDOld).
  Proof. reflexivity. Qed.

  Lemma in_v_old_read (Γ : Assignment.t columns RegionId.t) :
    OrchardSpec.in_v_old (OrchardActionInputs.read_action_inputs Γ) =
    OrchardActionInputs.read Γ
      (RegionId.WitnessInput RegionId.WitnessInput.VOld).
  Proof. reflexivity. Qed.

  Lemma in_rho_old_read (Γ : Assignment.t columns RegionId.t) :
    OrchardSpec.in_rho_old (OrchardActionInputs.read_action_inputs Γ) =
    OrchardActionInputs.read Γ
      (RegionId.WitnessInput RegionId.WitnessInput.RhoOld).
  Proof. reflexivity. Qed.

  Lemma in_psi_old_read (Γ : Assignment.t columns RegionId.t) :
    OrchardSpec.in_psi_old (OrchardActionInputs.read_action_inputs Γ) =
    OrchardActionInputs.read Γ
      (RegionId.WitnessInput RegionId.WitnessInput.PsiOld).
  Proof. reflexivity. Qed.

  (** ** Facts of the [Which.Old] NoteCommitR ladder, from [Holds]

      The [Which.Old] mirror of [OrchardActionUsFree]'s New-side peels: down
      the [old_instance_facts] path (the ladder is bind 17 of
      [note_commit.synthesize_instance], wrapped in the "Process NoteCommit
      inputs" / "[r] R" / "fixed-base mul of NoteCommitR" namespaces),
      bridged to [circuit.v]'s generic region synthesizers by the verbatim-copy
      computational equalities. *)

  Lemma old_note_commit_r_incomplete_facts_raw
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    interpret_facts Γ
      (layouter_facts
        (NC.synth_note_commit_r_mul_incomplete
          (NC.note_commit_region RegionId.NoteCommit.Which.Old
            RegionId.NoteCommit.FixedBaseIncomplete))).
  Proof.
    pose proof (OldNoteWords.old_instance_facts Γ Hcircuit) as Hfacts.
    unfold NC.synthesize_old, NC.synthesize_instance in Hfacts.
    cbv zeta in Hfacts.
    do 17 apply interpret_layouter_facts_bind_right in Hfacts.
    apply interpret_layouter_facts_bind_left in Hfacts.
    apply interpret_layouter_facts_in_namespace in Hfacts.
    apply interpret_layouter_facts_bind_left in Hfacts.
    do 2 apply interpret_layouter_facts_in_namespace in Hfacts.
    unfold NC.synthesize_full_fixed_base_mul_note_commit_r in Hfacts.
    apply interpret_layouter_facts_bind_left in Hfacts.
    exact Hfacts.
  Qed.

  Lemma old_note_commit_r_incomplete_facts_eq :
    layouter_facts
      (NC.synth_note_commit_r_mul_incomplete
        (NC.note_commit_region RegionId.NoteCommit.Which.Old
          RegionId.NoteCommit.FixedBaseIncomplete)) =
    layouter_facts
      (Garden.Orchard.circuit.synth_full_mul_incomplete_with_rows
        NCRO
        Garden.Orchard.constants.fixed_bases.note_commit_r.full_fixed_rows).
  Proof. reflexivity. Qed.

  Lemma old_note_commit_r_incomplete_facts
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    interpret_facts Γ
      (layouter_facts
        (Garden.Orchard.circuit.synth_full_mul_incomplete_with_rows
          NCRO
          Garden.Orchard.constants.fixed_bases.note_commit_r.full_fixed_rows)).
  Proof.
    pose proof (old_note_commit_r_incomplete_facts_raw Γ Hcircuit) as Hfacts.
    rewrite old_note_commit_r_incomplete_facts_eq in Hfacts.
    exact Hfacts.
  Qed.

  (** The whole two-region ladder program (incomplete + last region), in the
      generic synthesizer form. *)

  Lemma old_note_commit_r_fixed_base_facts_eq :
    layouter_facts
      (NC.synthesize_full_fixed_base_mul_note_commit_r
        RegionId.NoteCommit.Which.Old) =
    layouter_facts
      (let🞵 result :=
        Garden.Orchard.circuit.synth_full_mul_incomplete_with_rows
          NCRO
          Garden.Orchard.constants.fixed_bases.note_commit_r.full_fixed_rows in
       Garden.Orchard.circuit.synthesize_full_fixed_base_mul_last_region
         (RegionId.NoteCommit RegionId.NoteCommit.Which.Old
           RegionId.NoteCommit.FixedBaseLast)
         result).
  Proof. reflexivity. Qed.

  Lemma old_note_commit_r_value_eq
      (Γ : Assignment.t columns RegionId.t) :
    NoteCommitROut.note_commit_assigned_point_value Γ
      (layouter_value
        (NC.synthesize_full_fixed_base_mul_note_commit_r
          RegionId.NoteCommit.Which.Old)) =
    assigned_point_value Γ
      (layouter_value
        (let🞵 result :=
          Garden.Orchard.circuit.synth_full_mul_incomplete_with_rows
            NCRO
            Garden.Orchard.constants.fixed_bases.note_commit_r.full_fixed_rows in
         Garden.Orchard.circuit.synthesize_full_fixed_base_mul_last_region
           (RegionId.NoteCommit RegionId.NoteCommit.Which.Old
             RegionId.NoteCommit.FixedBaseLast)
           result)).
  Proof. reflexivity. Qed.

  Lemma old_note_commit_r_fixed_base_facts
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    interpret_facts Γ
      (layouter_facts
        (let🞵 result :=
          Garden.Orchard.circuit.synth_full_mul_incomplete_with_rows
            NCRO
            Garden.Orchard.constants.fixed_bases.note_commit_r.full_fixed_rows in
         Garden.Orchard.circuit.synthesize_full_fixed_base_mul_last_region
           (RegionId.NoteCommit RegionId.NoteCommit.Which.Old
             RegionId.NoteCommit.FixedBaseLast)
           result)).
  Proof.
    pose proof (OldNoteWords.old_instance_facts Γ Hcircuit) as Hfacts.
    unfold NC.synthesize_old, NC.synthesize_instance in Hfacts.
    cbv zeta in Hfacts.
    do 17 apply interpret_layouter_facts_bind_right in Hfacts.
    apply interpret_layouter_facts_bind_left in Hfacts.
    apply interpret_layouter_facts_in_namespace in Hfacts.
    apply interpret_layouter_facts_bind_left in Hfacts.
    do 2 apply interpret_layouter_facts_in_namespace in Hfacts.
    rewrite old_note_commit_r_fixed_base_facts_eq in Hfacts.
    exact Hfacts.
  Qed.

  (** ** Per-window full correctness and ladder distinctness at [Which.Old]

      The [circuit_proof/ladder/note_commit_r.v] chain re-instantiated at the
      [Which.Old] region: the table-entry and x-coordinate certificate
      bridges are Γ-free and reused verbatim. *)

  Lemma old_note_commit_r_full_window_correct
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ)
      (j : nat) (Hj : (j < 85)%nat) :
    incomplete_additions_window_point Γ NCRO (Z.of_nat j) =
    PallasModel.repr
      (Pallas.mul
        (window_scalar 85 j
          (EccSpec.window_digit
            (read_scalar_from_windows Γ NCRO 85) j))
        PallasGenerators.note_commit_r_G).
  Proof.
    pose proof (old_note_commit_r_incomplete_facts Γ Hcircuit) as Hfacts.
    pose proof (holds_gates Γ Hcircuit) as Hgates.
    refine (full_window_correct_gen Γ NCRO
      PallasGenerators.note_commit_r_G
      PallasGenerators.note_commit_r_on_curve
      PallasGenerators.note_commit_r_reduced
      85
      (fun i => EccSpec.window_digit
        (read_scalar_from_windows Γ NCRO 85) i)
      (fun i _ => window_digit_bound
        (read_scalar_from_windows Γ NCRO 85) i)
      (OrchardCircuitSpec.note_commit_r orchard_internal_params)
      _ _ _ _ _ j Hj).
    - (* Hwindow_eq *)
      intros i Hi.
      exact (OrchardActionUsFree.full_width_table_window_correct Γ NCRO
        Garden.Orchard.constants.fixed_bases.note_commit_r.full_fixed_rows
        OrchardActionUsFree.note_commit_r_rows_standard
        OrchardActionUsFree.note_commit_r_rows_length
        Hfacts Hgates i Hi).
    - (* Hwindow_on_curve *)
      intros i Hi.
      exact (OrchardActionUsFree.full_width_spec_window_on_curve Γ NCRO
        Garden.Orchard.constants.fixed_bases.note_commit_r.full_fixed_rows
        OrchardActionUsFree.note_commit_r_rows_standard
        OrchardActionUsFree.note_commit_r_rows_length
        Hfacts Hgates i Hi).
    - (* Hwindow_disc *)
      intros i Hi.
      exact (window_disc_qr_note_commit_r_all_Z i
        (EccSpec.window_digit
          (read_scalar_from_windows Γ NCRO 85) i)
        Hi
        (window_digit_bound
          (read_scalar_from_windows Γ NCRO 85) i)).
    - (* Hwindow_qr *)
      intros i Hi.
      pose proof (window_digit_bound
        (read_scalar_from_windows Γ NCRO 85) i) as Hdj.
      set (dj := EccSpec.window_digit
        (read_scalar_from_windows Γ NCRO 85) i) in *.
      pose proof (NoteCommitRWindowSignCert.y_check_entry i (Z.to_nat dj) Hi
        ltac:(lia)) as Hfc.
      rewrite (NoteCommitRLadder.note_commit_r_full_table_entry_eq_mul
        i dj Hi Hdj) in Hfc.
      exact Hfc.
    - (* Hwindow_x *)
      intros i d u Hi Hd.
      exact (NoteCommitRLadder.note_commit_r_fixed_window_point_x_eq_mul
        i d u Hi Hd).
  Qed.

  Lemma old_note_commit_r_distinct_holds
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    incomplete_additions_distinct_precondition Γ NCRO 1 83
      (incomplete_additions_window_point Γ NCRO 0).
  Proof.
    refine (ladder_distinct_precondition_holds_gen Γ NCRO
      PallasGenerators.note_commit_r_G
      PallasGenerators.note_commit_r_on_curve
      PallasGenerators.note_commit_r_reduced
      85
      (fun i => EccSpec.window_digit
        (read_scalar_from_windows Γ NCRO 85) i)
      (fun i _ => window_digit_bound
        (read_scalar_from_windows Γ NCRO 85) i)
      PallasGenerators.note_commit_r_ne_identity
      PallasGeneratorsOrder.note_commit_r_order
      ltac:(lia)
      (fun j Hj => old_note_commit_r_full_window_correct Γ Hcircuit j Hj)
      83 eq_refl).
  Qed.

  (** ** The [Which.Old] K-out (mirror of [NoteCommitROut], whose table-split
      plumbing is Γ-free and reused) *)

  Lemma old_note_commit_r_window_correct
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (j : nat) (w : EccSpec.fixed_window)
      (Hnth :
        List.nth_error
          (NoteCommitROut.note_commit_r_first ::
            NoteCommitROut.note_commit_r_middle ++
            [NoteCommitROut.note_commit_r_last]) j = Some w) :
    incomplete_additions_window_point Γ NCRO (Z.of_nat j) =
    EccSpec.fixed_window_point w
      (EccSpec.window_digit
        (read_scalar_from_windows Γ NCRO 85)
        j)
      (List.nth j (read_us Γ NCRO 85) 0).
  Proof.
    rewrite <- NoteCommitROut.note_commit_r_spec_table_split in Hnth.
    assert (Hj : (j < 85)%nat).
    { pose proof (proj1 (List.nth_error_Some
        (OrchardCircuitSpec.note_commit_r orchard_internal_params) j)) as Hlt.
      rewrite OrchardActionUsFree.note_commit_r_table_length in Hlt.
      apply Hlt.
      rewrite Hnth.
      discriminate. }
    apply List.nth_error_nth with (d := fixed_window_default) in Hnth.
    rewrite <- Hnth.
    exact
      (OrchardActionUsFree.full_width_table_window_correct Γ NCRO
        Garden.Orchard.constants.fixed_bases.note_commit_r.full_fixed_rows
        OrchardActionUsFree.note_commit_r_rows_standard
        OrchardActionUsFree.note_commit_r_rows_length
        (old_note_commit_r_incomplete_facts Γ Hcircuit)
        (holds_gates Γ Hcircuit)
        j Hj).
  Qed.

  Lemma old_note_commit_r_window_x_nonzero
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (i : nat) (Hi : (i < 85)%nat) :
    UnOp.from
      (Point.x
        (incomplete_additions_window_point Γ NCRO (Z.of_nat i))) <> 0.
  Proof.
    apply (full_width_incomplete_window_x_nonzero Γ NCRO
      Garden.Orchard.constants.fixed_bases.note_commit_r.full_fixed_rows
      i
      (old_note_commit_r_incomplete_facts Γ Hcircuit)
      (holds_gates Γ Hcircuit)
      Hi).
  Qed.

  Lemma old_note_commit_r_complete_of_holds
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    incomplete_additions_complete_precondition Γ NCRO 1 83
      (incomplete_additions_window_point Γ NCRO 0).
  Proof.
    pose proof (old_note_commit_r_incomplete_facts Γ Hcircuit) as Hfacts.
    apply incomplete_complete_precondition_of_distinct.
    - replace 0 with (Z.of_nat 0) by reflexivity.
      apply (full_width_incomplete_region_window_on_curve Γ NCRO
        Garden.Orchard.constants.fixed_bases.note_commit_r.full_fixed_rows
        0%nat Hfacts (holds_gates Γ Hcircuit)).
      lia.
    - replace 0 with (Z.of_nat 0) by reflexivity.
      apply (old_note_commit_r_window_x_nonzero Γ Hcircuit 0%nat).
      lia.
    - intros i Hi.
      replace (1 + Z.of_nat i) with (Z.of_nat (S i)) by lia.
      apply (full_width_incomplete_region_window_on_curve Γ NCRO
        Garden.Orchard.constants.fixed_bases.note_commit_r.full_fixed_rows
        (S i) Hfacts (holds_gates Γ Hcircuit)).
      lia.
    - intros i Hi.
      replace (1 + Z.of_nat i) with (Z.of_nat (S i)) by lia.
      apply (old_note_commit_r_window_x_nonzero Γ Hcircuit (S i)).
      lia.
    - exact (old_note_commit_r_distinct_holds Γ Hcircuit).
  Qed.

  Lemma old_note_commit_r_incomplete_of_holds
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    incomplete_additions_precondition Γ NCRO 1 83
      (incomplete_additions_window_point Γ NCRO 0).
  Proof.
    apply incomplete_complete_implies_precondition.
    exact (old_note_commit_r_complete_of_holds Γ Hcircuit).
  Qed.

  Lemma old_note_commit_r_circuit_precondition_of_holds
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    fixed_scalar_mul_circuit_precondition
      (OrchardCircuitSpec.note_commit_r orchard_internal_params)
      (read_scalar_from_windows Γ NCRO 85)
      (read_us Γ NCRO 85).
  Proof.
    pose proof (old_note_commit_r_window_correct Γ Hcircuit 0%nat
      NoteCommitROut.note_commit_r_first eq_refl) as Hfirst.
    pose proof (old_note_commit_r_incomplete_facts Γ Hcircuit) as Hfacts.
    rewrite NoteCommitROut.note_commit_r_spec_table_split.
    cbn [fixed_scalar_mul_circuit_precondition].
    rewrite <- Hfirst.
    eapply circuit_tail_precondition_of_complete
      with (n := 83%nat).
    - rewrite List.length_app, NoteCommitROut.note_commit_r_middle_length.
      reflexivity.
    - exact (old_note_commit_r_complete_of_holds Γ Hcircuit).
    - intros j w Hnth.
      replace (1 + Z.of_nat j) with (Z.of_nat (S j)) by lia.
      replace (1 + j)%nat with (S j) by lia.
      apply (old_note_commit_r_window_correct Γ Hcircuit).
      cbn [List.nth_error].
      exact Hnth.
    - apply (full_width_incomplete_region_window_on_curve Γ NCRO
        Garden.Orchard.constants.fixed_bases.note_commit_r.full_fixed_rows
        0%nat Hfacts (holds_gates Γ Hcircuit)).
      lia.
    - exact (proj1 (incomplete_additions_window_point_reduced Γ NCRO
        (Z.of_nat 0))).
    - exact (proj2 (incomplete_additions_window_point_reduced Γ NCRO
        (Z.of_nat 0))).
    - intros j Hj.
      rewrite List.length_app, NoteCommitROut.note_commit_r_middle_length in Hj.
      cbn [List.length] in Hj.
      replace (1 + Z.of_nat j) with (Z.of_nat (S j)) by lia.
      apply (full_width_incomplete_region_window_on_curve Γ NCRO
        Garden.Orchard.constants.fixed_bases.note_commit_r.full_fixed_rows
        (S j) Hfacts (holds_gates Γ Hcircuit)).
      lia.
    - intros j Hj.
      exact (proj1 (incomplete_additions_window_point_reduced Γ NCRO
        (1 + Z.of_nat j))).
    - intros j Hj.
      exact (proj2 (incomplete_additions_window_point_reduced Γ NCRO
        (1 + Z.of_nat j))).
  Qed.

  (** K-out: the [Which.Old] blinding-point output as [fixed_scalar_mul] of
      the NoteCommitR spec table at the region's read scalar/us. *)
  Lemma full_old_note_commit_r_scalar_mul_correct
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    Field.map_mod
      (NoteCommitROut.note_commit_assigned_point_value Γ
        (layouter_value
          (NC.synthesize_full_fixed_base_mul_note_commit_r
            RegionId.NoteCommit.Which.Old))) =
    EccSpec.fixed_scalar_mul
      (OrchardCircuitSpec.note_commit_r orchard_internal_params)
      (read_scalar_from_windows Γ NCRO 85)
      (read_us Γ NCRO 85).
  Proof.
    pose proof (old_note_commit_r_fixed_base_facts Γ Hcircuit) as Hfacts.
    rewrite (old_note_commit_r_value_eq Γ).
    rewrite NoteCommitROut.note_commit_r_spec_table_split.
    eapply full_with_rows_scalar_mul_correct
      with (first := NoteCommitROut.note_commit_r_first)
           (middle := NoteCommitROut.note_commit_r_middle)
           (last := NoteCommitROut.note_commit_r_last).
    - exact Hfacts.
    - exact (holds_gates Γ Hcircuit).
    - exact (old_note_commit_r_incomplete_of_holds Γ Hcircuit).
    - exact NoteCommitROut.note_commit_r_table_split.
    - exact NoteCommitROut.note_commit_r_middle_length.
    - intros j w Hnth.
      exact (old_note_commit_r_window_correct Γ Hcircuit j w Hnth).
    - rewrite <- NoteCommitROut.note_commit_r_spec_table_split.
      exact (old_note_commit_r_circuit_precondition_of_holds Γ Hcircuit).
  Qed.

  (** ** Witness elimination and the protocol bridge at [Which.Old]

      The read scalar's window range ([TypedInputsFullWidth] mirror), the
      us-elimination ([table_us_free_of_oncurve] at the [Which.Old] on-curve
      and non-residue facts), and the group-multiple form through
      [NoteCommitRMulProtocol.note_commit_r_mul_protocol]. *)

  Lemma old_rcm_windows_range
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    List.Forall (fun w => 0 <= w < 8) (read_windows Γ NCRO 85).
  Proof.
    exact (full_width_incomplete_region_windows_range Γ NCRO _
      (old_note_commit_r_incomplete_facts Γ Hcircuit)
      (holds_gates Γ Hcircuit)).
  Qed.

  Lemma read_rcm_old_range
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    0 <= read_scalar_from_windows Γ NCRO 85 < 8 ^ 85.
  Proof.
    apply TypedInputsFullWidth.read_scalar_from_windows_85_range.
    exact (old_rcm_windows_range Γ Hcircuit).
  Qed.

  Lemma old_note_commit_r_us_eq
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    EccSpec.fixed_scalar_mul
      (OrchardCircuitSpec.note_commit_r orchard_internal_params)
      (read_scalar_from_windows Γ NCRO 85)
      (read_us Γ NCRO 85) =
    EccSpec.fixed_scalar_mul
      (OrchardCircuitSpec.note_commit_r orchard_internal_params)
      (read_scalar_from_windows Γ NCRO 85)
      (canonical_us_for
        (OrchardCircuitSpec.note_commit_r orchard_internal_params)
        (read_scalar_from_windows Γ NCRO 85)).
  Proof.
    apply (table_us_free_of_oncurve
      (OrchardCircuitSpec.note_commit_r orchard_internal_params)
      (read_scalar_from_windows Γ NCRO 85)
      (read_us Γ NCRO 85)
      fixed_window_default).
    - rewrite OrchardActionUsFree.read_us_length,
        OrchardActionUsFree.note_commit_r_table_length.
      reflexivity.
    - intros i Hi.
      rewrite OrchardActionUsFree.note_commit_r_table_length in Hi.
      split.
      + cbv zeta.
        exact (OrchardActionUsFree.full_width_spec_window_on_curve Γ NCRO
          Garden.Orchard.constants.fixed_bases.note_commit_r.full_fixed_rows
          OrchardActionUsFree.note_commit_r_rows_standard
          OrchardActionUsFree.note_commit_r_rows_length
          (old_note_commit_r_incomplete_facts Γ Hcircuit)
          (holds_gates Γ Hcircuit)
          i Hi).
      + apply (window_disc_qr_note_commit_r_all_Z i).
        * exact Hi.
        * unfold EccSpec.window_digit. apply Z.mod_pos_bound. lia.
  Qed.

  (** The blinding leg in protocol form: the [Which.Old] ladder output point
      is the group multiple [mul_note_commit_r rcm_old]. *)
  Lemma old_note_commit_r_mul_leg
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    Field.map_mod
      (NoteCommitROut.note_commit_assigned_point_value Γ
        (layouter_value
          (NC.synthesize_full_fixed_base_mul_note_commit_r
            RegionId.NoteCommit.Which.Old))) =
    OrchardProtocolSpec.mul_note_commit_r
      (read_scalar_from_windows Γ NCRO 85).
  Proof.
    rewrite (full_old_note_commit_r_scalar_mul_correct Γ Hcircuit).
    rewrite (old_note_commit_r_us_eq Γ Hcircuit).
    exact (NoteCommitRMulProtocol.note_commit_r_mul_protocol
      (read_scalar_from_windows Γ NCRO 85)
      (read_rcm_old_range Γ Hcircuit)).
  Qed.

  (** ** The "M + [r] R" complete addition of the old-note commitment
      (mirror of [NoteCommitNewAdd] at [Which.Old]) *)

  Definition old_note_piece
      (region : RegionId.NoteCommit.t) (name : string)
      : Garden.Halo2.Synthesis.Cell.t columns RegionId.t :=
    layouter_value
      (NC.witness_message_piece
        (NC.note_commit_region RegionId.NoteCommit.Which.Old region)
        Advice.A6
        name).

  Definition old_cm_hash_result : SChip.HashResult.t :=
    layouter_value
      (SChip.synthesize_hash_to_point_note_commit
        (NC.note_commit_region RegionId.NoteCommit.Which.Old
          RegionId.NoteCommit.HashToPoint)
        NC.q_note_commit_m_x
        NC.q_note_commit_m_y
        (old_note_piece RegionId.NoteCommit.WitnessA "a")
        (old_note_piece RegionId.NoteCommit.WitnessB "b")
        (old_note_piece RegionId.NoteCommit.WitnessC "c")
        (old_note_piece RegionId.NoteCommit.WitnessD "d")
        (old_note_piece RegionId.NoteCommit.WitnessE "e")
        (old_note_piece RegionId.NoteCommit.WitnessF "f")
        (old_note_piece RegionId.NoteCommit.WitnessG "g")
        (old_note_piece RegionId.NoteCommit.WitnessH "h")).

  (** The [m] operand of the "M + [r] R" complete addition: the variant-1
      hash point's x/y cells. *)
  Definition old_cm_hash_m : NC.AssignedPoint.t := {|
    NC.AssignedPoint.x := old_cm_hash_result.(SChip.HashResult.x);
    NC.AssignedPoint.y := old_cm_hash_result.(SChip.HashResult.y);
  |}.

  (** The blinding operand: the output point of the NoteCommitR fixed-base
      ladder at [Which.Old]. *)
  Definition old_cm_blind : NC.AssignedPoint.t :=
    layouter_value
      (NC.synthesize_full_fixed_base_mul_note_commit_r
        RegionId.NoteCommit.Which.Old).

  Lemma old_cm_complete_add_facts
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    interpret_facts Γ
      (layouter_facts
        (Garden.Orchard.circuit.synthesize_complete_point_add
          (RegionId.NoteCommit RegionId.NoteCommit.Which.Old
            RegionId.NoteCommit.CompletePointAdd)
          "M + [r] R"
          (NoteCommitNewAdd.to_circuit_point old_cm_hash_m)
          (NoteCommitNewAdd.to_circuit_point old_cm_blind))).
  Proof.
    pose proof (OldNoteWords.old_instance_facts Γ Hcircuit) as Hfacts.
    unfold NC.synthesize_old, NC.synthesize_instance in Hfacts.
    cbv zeta in Hfacts.
    do 17 apply interpret_layouter_facts_bind_right in Hfacts.
    apply interpret_layouter_facts_bind_left in Hfacts.
    apply interpret_layouter_facts_in_namespace in Hfacts.
    do 2 apply interpret_layouter_facts_bind_right in Hfacts.
    cbv beta zeta in Hfacts.
    apply interpret_layouter_facts_bind_left in Hfacts.
    exact Hfacts.
  Qed.

  (** The complete-add bridge: cm_old point = M + [r] R as spec points.  The
      seven message cells are arbitrary: neither the output cells nor the two
      operand records depend on them. *)
  Lemma synthesize_old_cm_point_add_correct
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (g_d_x g_d_y pk_d_x pk_d_y value_cell rho_cell psi_cell :
        Garden.Halo2.Synthesis.Cell.t columns RegionId.t) :
    Field.map_mod
      (NoteCommitROut.note_commit_assigned_point_value Γ
        (layouter_value
          (NC.synthesize_old
            g_d_x g_d_y pk_d_x pk_d_y value_cell rho_cell psi_cell))) =
    EccSpec.point_add
      (Field.map_mod
        (NoteCommitROut.note_commit_assigned_point_value Γ old_cm_hash_m))
      (Field.map_mod
        (NoteCommitROut.note_commit_assigned_point_value Γ
          (layouter_value
            (NC.synthesize_full_fixed_base_mul_note_commit_r
              RegionId.NoteCommit.Which.Old)))).
  Proof.
    pose proof
      (complete_point_add_correct Γ
        (RegionId.NoteCommit RegionId.NoteCommit.Which.Old
          RegionId.NoteCommit.CompletePointAdd)
        "M + [r] R"
        (NoteCommitNewAdd.to_circuit_point old_cm_hash_m)
        (NoteCommitNewAdd.to_circuit_point old_cm_blind)
        (old_cm_complete_add_facts Γ Hcircuit)
        (holds_gates Γ Hcircuit)) as Hadd.
    exact Hadd.
  Qed.

  (** Combined form: cm_old point = M + [rcm_old] NoteCommitR, with the
      blinding leg in the protocol's group-multiple form. *)
  Lemma synthesize_old_cm_point_add_rcm_correct
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (g_d_x g_d_y pk_d_x pk_d_y value_cell rho_cell psi_cell :
        Garden.Halo2.Synthesis.Cell.t columns RegionId.t) :
    Field.map_mod
      (NoteCommitROut.note_commit_assigned_point_value Γ
        (layouter_value
          (NC.synthesize_old
            g_d_x g_d_y pk_d_x pk_d_y value_cell rho_cell psi_cell))) =
    EccSpec.point_add
      (Field.map_mod
        (NoteCommitROut.note_commit_assigned_point_value Γ old_cm_hash_m))
      (OrchardProtocolSpec.mul_note_commit_r
        (read_scalar_from_windows Γ NCRO 85)).
  Proof.
    rewrite
      (synthesize_old_cm_point_add_correct Γ Hcircuit
        g_d_x g_d_y pk_d_x pk_d_y value_cell rho_cell psi_cell).
    rewrite (old_note_commit_r_mul_leg Γ Hcircuit).
    reflexivity.
  Qed.

  (** ** The hash operand's cells and evaluated point *)

  Lemma old_hash_m_x_cell :
    old_cm_hash_m.(NC.AssignedPoint.x) =
    Garden.Halo2.Synthesis.Cell.advice OldNoteWords.HR Advice.A0 109.
  Proof. reflexivity. Qed.

  Lemma old_hash_m_y_cell :
    old_cm_hash_m.(NC.AssignedPoint.y) =
    Garden.Halo2.Synthesis.Cell.advice OldNoteWords.HR Advice.A3 109.
  Proof. reflexivity. Qed.

  Lemma old_hash_m_value_eq (Γ : Assignment.t columns RegionId.t) :
    Field.map_mod
      (NoteCommitROut.note_commit_assigned_point_value Γ old_cm_hash_m) =
    {|
      Point.x :=
        UnOp.from (eval_cell Γ
          (Garden.Halo2.Synthesis.Cell.advice OldNoteWords.HR Advice.A0 109));
      Point.y :=
        UnOp.from (eval_cell Γ
          (Garden.Halo2.Synthesis.Cell.advice OldNoteWords.HR Advice.A3 109));
    |}.
  Proof.
    unfold NoteCommitROut.note_commit_assigned_point_value.
    rewrite old_hash_m_x_cell.
    rewrite old_hash_m_y_cell.
    reflexivity.
  Qed.

  (** ** The [NoteCommitOldEquality] region: cm point = witnessed cm_old

      Both coordinates are [Copy]-pinned ([circuit.v],
      [synthesize_note_commit_old]) — [in_cm_old] is a full point, unlike the
      New side's single [ConstrainInstance] on x. *)

  (** The output point of [note_commit.synthesize_old]: the complete-add
      result cells (A2/A3 at row 1 of the [Which.Old] [CompletePointAdd]
      region), independent of the message-input cells. *)
  Lemma old_cm_value_eq
      (Γ : Assignment.t columns RegionId.t)
      (g_d_x g_d_y pk_d_x pk_d_y value_cell rho_cell psi_cell :
        Garden.Halo2.Synthesis.Cell.t columns RegionId.t) :
    NoteCommitROut.note_commit_assigned_point_value Γ
      (layouter_value
        (NC.synthesize_old
          g_d_x g_d_y pk_d_x pk_d_y value_cell rho_cell psi_cell)) =
    {|
      Point.x :=
        eval_cell Γ
          (Garden.Halo2.Synthesis.Cell.advice
            (RegionId.NoteCommit RegionId.NoteCommit.Which.Old
              RegionId.NoteCommit.CompletePointAdd) Advice.A2 1);
      Point.y :=
        eval_cell Γ
          (Garden.Halo2.Synthesis.Cell.advice
            (RegionId.NoteCommit RegionId.NoteCommit.Which.Old
              RegionId.NoteCommit.CompletePointAdd) Advice.A3 1);
    |}.
  Proof. reflexivity. Qed.

  Lemma old_cm_copy_facts
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    eval_cell Γ
      (Garden.Halo2.Synthesis.Cell.advice
        (RegionId.NoteCommit RegionId.NoteCommit.Which.Old
          RegionId.NoteCommit.CompletePointAdd) Advice.A2 1) =
      eval_cell Γ
        (Garden.Halo2.Synthesis.Cell.advice
          (RegionId.WitnessInput RegionId.WitnessInput.CmOld) Advice.A0 0) /\
    eval_cell Γ
      (Garden.Halo2.Synthesis.Cell.advice
        (RegionId.NoteCommit RegionId.NoteCommit.Which.Old
          RegionId.NoteCommit.CompletePointAdd) Advice.A3 1) =
      eval_cell Γ
        (Garden.Halo2.Synthesis.Cell.advice
          (RegionId.WitnessInput RegionId.WitnessInput.CmOld) Advice.A1 0).
  Proof.
    pose proof (holds_facts Γ Hcircuit) as Hfacts.
    unfold Garden.Orchard.circuit.synthesize in Hfacts.
    do 8 apply interpret_layouter_facts_bind_right in Hfacts.
    apply interpret_layouter_facts_bind_left in Hfacts.
    unfold Garden.Orchard.circuit.synthesize_note_commit_old in Hfacts.
    do 2 apply interpret_layouter_facts_bind_right in Hfacts.
    apply interpret_layouter_facts_in_namespace in Hfacts.
    apply interpret_layouter_facts_add_region in Hfacts.
    pose proof Hfacts as Hx.
    apply interpret_region_facts_bind_left in Hx.
    cbn [region_facts interpret_facts interpret_fact] in Hx.
    destruct Hx as [Hx _].
    pose proof Hfacts as Hy.
    apply interpret_region_facts_bind_right in Hy.
    apply interpret_region_facts_bind_left in Hy.
    cbn [region_facts interpret_facts interpret_fact] in Hy.
    destruct Hy as [Hy _].
    exact (conj Hx Hy).
  Qed.

  (** The complete-add output cells carry the witnessed [cm_old] point. *)
  Lemma old_cm_point_pins_cm_old
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    Field.map_mod
      {|
        Point.x :=
          eval_cell Γ
            (Garden.Halo2.Synthesis.Cell.advice
              (RegionId.NoteCommit RegionId.NoteCommit.Which.Old
                RegionId.NoteCommit.CompletePointAdd) Advice.A2 1);
        Point.y :=
          eval_cell Γ
            (Garden.Halo2.Synthesis.Cell.advice
              (RegionId.NoteCommit RegionId.NoteCommit.Which.Old
                RegionId.NoteCommit.CompletePointAdd) Advice.A3 1);
      |} =
    OrchardSpec.in_cm_old (OrchardActionInputs.read_action_inputs Γ).
  Proof.
    destruct (old_cm_copy_facts Γ Hcircuit) as [Hx Hy].
    rewrite Hx, Hy.
    exact (assigned_point_value_witness_point Γ
      (Garden.Orchard.circuit.witness_input_region RegionId.WitnessInput.CmOld)
      "cm_old").
  Qed.

  (** ** The protocol commitment, unfolded at the circuit's readers

      The anti-blowup discipline of [circuit_proof/note_commit/cmx.v]: a
      projection lemma over VARIABLE arguments (both sides unfold without
      touching the hash fold), then syntactic reader rewrites, each constant
      spelled exactly as the corresponding leg lemma states it. *)

  Lemma note_commit_generic
      (prm : OrchardSpec.Params) (g_d pk_d : Point.t) (v rho psi rcm : Z) :
    OrchardProtocolSpec.note_commit prm g_d pk_d v rho psi rcm =
    EccSpec.point_add
      (SinsemillaSpec.sinsemilla_hash_to_point
        (OrchardSpec.note_commit_q prm)
        (OrchardSpec.note_commit_message g_d pk_d v rho psi))
      (OrchardProtocolSpec.mul_note_commit_r rcm).
  Proof. reflexivity. Qed.

  Lemma note_commit_Q_params_eq :
    NoteCommitNewHash.note_commit_Q =
    OrchardSpec.note_commit_q OrchardActionInputs.orchard_circuit_params.
  Proof. reflexivity. Qed.

  Lemma note_commit_spec_eq (Γ : Assignment.t columns RegionId.t) :
    OrchardProtocolSpec.note_commit OrchardActionInputs.orchard_circuit_params
      (OrchardSpec.in_g_d_old (OrchardActionInputs.read_action_inputs Γ))
      (read_pk_d_old Γ)
      (OrchardSpec.in_v_old (OrchardActionInputs.read_action_inputs Γ))
      (OrchardSpec.in_rho_old (OrchardActionInputs.read_action_inputs Γ))
      (OrchardSpec.in_psi_old (OrchardActionInputs.read_action_inputs Γ))
      (read_rcm_old Γ) =
    EccSpec.point_add
      (SinsemillaSpec.sinsemilla_hash_to_point
        (OrchardSpec.note_commit_q OrchardActionInputs.orchard_circuit_params)
        (OrchardSpec.note_commit_message
          (OrchardActionInputs.read_point Γ
            (RegionId.WitnessInput RegionId.WitnessInput.GDOld))
          (OrchardActionInputs.read_point Γ
            (RegionId.AddressIntegrity RegionId.AddressIntegrity.WitnessPkD))
          (OrchardActionInputs.read Γ
            (RegionId.WitnessInput RegionId.WitnessInput.VOld))
          (OrchardActionInputs.read Γ
            (RegionId.WitnessInput RegionId.WitnessInput.RhoOld))
          (OrchardActionInputs.read Γ
            (RegionId.WitnessInput RegionId.WitnessInput.PsiOld))))
      (OrchardProtocolSpec.mul_note_commit_r
        (read_scalar_from_windows Γ NCRO 85)).
  Proof.
    rewrite (note_commit_generic OrchardActionInputs.orchard_circuit_params
      (OrchardSpec.in_g_d_old (OrchardActionInputs.read_action_inputs Γ))
      (read_pk_d_old Γ)
      (OrchardSpec.in_v_old (OrchardActionInputs.read_action_inputs Γ))
      (OrchardSpec.in_rho_old (OrchardActionInputs.read_action_inputs Γ))
      (OrchardSpec.in_psi_old (OrchardActionInputs.read_action_inputs Γ))
      (read_rcm_old Γ)).
    rewrite (in_g_d_old_read Γ).
    rewrite (read_pk_d_old_read Γ).
    rewrite (in_v_old_read Γ).
    rewrite (in_rho_old_read Γ).
    rewrite (in_psi_old_read Γ).
    rewrite (read_rcm_old_eq Γ).
    reflexivity.
  Qed.

  (** ** Old note commitment integrity (§4.18.4, honest branch)

      The exact conclusion of
      [OrchardValidActionInputs.old_note_commit_integrity], from [Holds Γ]
      and the two witness-honesty side conditions in the
      [note_commit_witness_ok] shape: Sinsemilla incomplete-add
      nondegeneracy of the witnessed 109-word old-note message, and the
      eleven short-lookup range facts. *)
  Theorem old_note_commit_integrity
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (Hnondeg :
        SinsemillaHash.nondegenerate
          (OrchardSpec.note_commit_q OrchardActionInputs.orchard_circuit_params)
          (OldNoteWords.old_note_words Γ))
      (Hshort : OldNoteWords.old_note_short_lookup_ok Γ) :
    OrchardProtocolSpec.note_commit OrchardActionInputs.orchard_circuit_params
      (OrchardSpec.in_g_d_old (OrchardActionInputs.read_action_inputs Γ))
      (read_pk_d_old Γ)
      (OrchardSpec.in_v_old (OrchardActionInputs.read_action_inputs Γ))
      (OrchardSpec.in_rho_old (OrchardActionInputs.read_action_inputs Γ))
      (OrchardSpec.in_psi_old (OrchardActionInputs.read_action_inputs Γ))
      (read_rcm_old Γ) =
    OrchardSpec.in_cm_old (OrchardActionInputs.read_action_inputs Γ).
  Proof.
    rewrite <- note_commit_Q_params_eq in Hnondeg.
    pose proof
      (synthesize_old_cm_point_add_rcm_correct Γ Hcircuit
        (Garden.Halo2.Synthesis.Cell.advice
          (RegionId.WitnessInput RegionId.WitnessInput.GDOld) Advice.A0 0)
        (Garden.Halo2.Synthesis.Cell.advice
          (RegionId.WitnessInput RegionId.WitnessInput.GDOld) Advice.A1 0)
        (Garden.Halo2.Synthesis.Cell.advice
          (RegionId.AddressIntegrity RegionId.AddressIntegrity.WitnessPkD)
          Advice.A0 0)
        (Garden.Halo2.Synthesis.Cell.advice
          (RegionId.AddressIntegrity RegionId.AddressIntegrity.WitnessPkD)
          Advice.A1 0)
        (Garden.Halo2.Synthesis.Cell.advice
          (RegionId.WitnessInput RegionId.WitnessInput.VOld) Advice.A0 0)
        (Garden.Halo2.Synthesis.Cell.advice
          (RegionId.WitnessInput RegionId.WitnessInput.RhoOld) Advice.A0 0)
        (Garden.Halo2.Synthesis.Cell.advice
          (RegionId.WitnessInput RegionId.WitnessInput.PsiOld) Advice.A0 0))
      as Hadd.
    rewrite (old_cm_value_eq Γ _ _ _ _ _ _ _) in Hadd.
    rewrite (old_hash_m_value_eq Γ) in Hadd.
    rewrite (OldNoteHash.note_commit_old_hash_point_correct Γ Hcircuit Hnondeg)
      in Hadd.
    rewrite (OldNoteWords.note_commit_old_words_correct Γ Hcircuit Hshort)
      in Hadd.
    rewrite (note_commit_spec_eq Γ).
    rewrite <- Hadd.
    exact (old_cm_point_pins_cm_old Γ Hcircuit).
  Qed.

  (** ** The bundled witness-honesty side condition

      The [note_commit_witness_ok] shape of the New lane
      ([circuit_proof/note_commit/cmx.v]): the refinement target for
      [OrchardValidActionInputs.old_note_witness_ok] — Sinsemilla
      incomplete-add nondegeneracy plus the short-lookup range facts.  The
      words-canonicity leg is a theorem
      ([OldNoteWords.note_commit_old_words_correct]), not a conjunct here. *)
  Definition old_note_witness_ok
      (Γ : Assignment.t columns RegionId.t) : Prop :=
    SinsemillaHash.nondegenerate
      (OrchardSpec.note_commit_q OrchardActionInputs.orchard_circuit_params)
      (OldNoteWords.old_note_words Γ) /\
    OldNoteWords.old_note_short_lookup_ok Γ.

  Theorem old_note_commit_integrity_of_witness_ok
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (Hok : old_note_witness_ok Γ) :
    OrchardProtocolSpec.note_commit OrchardActionInputs.orchard_circuit_params
      (OrchardSpec.in_g_d_old (OrchardActionInputs.read_action_inputs Γ))
      (read_pk_d_old Γ)
      (OrchardSpec.in_v_old (OrchardActionInputs.read_action_inputs Γ))
      (OrchardSpec.in_rho_old (OrchardActionInputs.read_action_inputs Γ))
      (OrchardSpec.in_psi_old (OrchardActionInputs.read_action_inputs Γ))
      (read_rcm_old Γ) =
    OrchardSpec.in_cm_old (OrchardActionInputs.read_action_inputs Γ).
  Proof.
    destruct Hok as [Hnondeg Hshort].
    exact (old_note_commit_integrity Γ Hcircuit Hnondeg Hshort).
  Qed.

End OldNoteOpen.
