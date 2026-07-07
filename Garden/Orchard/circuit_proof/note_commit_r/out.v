(** * NoteCommitR K-out: the blinding-leg output equality from [Holds] alone

    Composes the generic full-width wrapper
    [full_with_rows_scalar_mul_correct]
    ([circuit_proof/fixed_base/main.v]) with:
    - the whole full-width program facts peeled from [Holds]
      ([note_commit_r_fixed_base_facts], both regions of [note_commit.v]'s
      LOCAL ladder [synthesize_full_fixed_base_mul_note_commit_r] at
      [Which.New], bridged to [circuit.v]'s generic region synthesizers by
      the computational equalities [note_commit_r_fixed_base_facts_eq] /
      [note_commit_r_value_eq] — the local combinators are verbatim copies
      whose fact lists and output cells never mention the local record
      types, so both bridges are [reflexivity]);
    - the ladder-distinctness certificate
      [NoteCommitRLadder.note_commit_r_distinct_holds]
      ([circuit_proof/ladder/note_commit_r.v]), lifted
      through [incomplete_complete_precondition_of_distinct] and
      [incomplete_complete_implies_precondition]
      into the incomplete-additions precondition;
    - the circuit precondition
      [note_commit_r_circuit_precondition_of_holds]
      (the counterpart of the ValueCommitR form);
    - the per-window spec-table match [note_commit_r_window_correct],
      built from the generic
      [OrchardActionUsFree.full_width_table_window_correct].

    The final lemma
    [full_note_commit_r_scalar_mul_correct]
    states the blinding-point output of the new-note commitment's fixed-base
    ladder as [EccSpec.fixed_scalar_mul] of the NoteCommitR spec table at the
    read scalar/us — the NoteCommitR counterpart of
    [ValueCommitROut.value_commit_r_hblind]
    ([circuit_proof/value_commit_r/out.v]), phrased over
    [note_commit.v]'s own [AssignedPoint] record (what the CMX [Hnote]
    bridge will consume). *)

Require Import Garden.Halo2.main.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.lemmas.
Require Import Garden.Orchard.columns.
Require Garden.Orchard.circuit.
Require Garden.Orchard.circuit.note_commit.
Require Garden.Orchard.constants.fixed_bases.note_commit_r.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.spec.
Require Import Garden.Orchard.circuit_spec.
Require Import Garden.Orchard.circuit_proof.inputs.
Require Import Garden.Orchard.circuit_proof.facts.
Require Import Garden.Orchard.circuit_proof.fixed_base.main.
Require Import Garden.Orchard.circuit_proof.us_free.main.
Require Import Garden.Orchard.circuit_proof.ladder.note_commit_r.
Require Import Garden.Field.Field.
Require Import Garden.Field.Lemmas.
Require Import Garden.Field.Sqrt.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.fixed_window_canonical.
Require Import Garden.Plonky3.M.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Lists.List.
Require Import Stdlib.micromega.Lia.

Import ListNotations.

#[local] Existing Instance Primes.PallasPIsPrime.

Global Open Scope Z_scope.


Module NoteCommitROut.
  Import OrchardActionFixedBase.

  (* The consumed ladder/cert lemmas carry [is_square]/[field_sqrt]/
     [fixed_window_point_canonical] over the concrete Pallas modulus;
     conversion must compare them by congruence, never unfold ([modpow] at the
     ~2^253 exponent blows the term up). *)
  Strategy opaque
    [is_square modpow modpow_pos field_sqrt fixed_window_point_canonical].

  Local Notation Holds Γ :=
    (circuit_holds Γ
      Garden.Orchard.circuit.synthesize
      (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)).

  (** ** Table split of the 85-window NoteCommitR spec table *)

  Definition note_commit_r_first : EccSpec.fixed_window :=
    List.hd fixed_window_default
      (OrchardSpec.note_commit_r orchard_circuit_params).

  Definition note_commit_r_middle : EccSpec.fixed_table :=
    List.firstn 83
      (List.skipn 1 (OrchardSpec.note_commit_r orchard_circuit_params)).

  Definition note_commit_r_last : EccSpec.fixed_window :=
    List.nth 84 (OrchardSpec.note_commit_r orchard_circuit_params)
      fixed_window_default.

  Lemma note_commit_r_table_split :
    EccSpec.fixed_table_of_rows
      Garden.Orchard.constants.fixed_bases.note_commit_r.full_fixed_rows =
    note_commit_r_first :: note_commit_r_middle ++ [note_commit_r_last].
  Proof. reflexivity. Qed.

  Lemma note_commit_r_spec_table_split :
    OrchardSpec.note_commit_r orchard_circuit_params =
    note_commit_r_first :: note_commit_r_middle ++ [note_commit_r_last].
  Proof. reflexivity. Qed.

  Lemma note_commit_r_middle_length :
    List.length note_commit_r_middle = 83%nat.
  Proof. reflexivity. Qed.

  (** ** The whole-program bridge from [note_commit.v]'s local combinators

      [note_commit.v]'s two region synthesizers are verbatim copies of
      [circuit.v]'s (only the [AssignedPoint]/[FullFixedResult] return record
      types differ, which neither the fact list nor the output cells
      mention), so the emitted fact lists and the output point's cells are
      computationally equal.  Extends
      [OrchardActionUsFree.note_commit_r_incomplete_facts_eq] from the
      incomplete region to the whole two-region ladder program. *)

  Lemma note_commit_r_fixed_base_facts_eq :
    layouter_facts
      (Garden.Orchard.circuit.note_commit
        .synthesize_full_fixed_base_mul_note_commit_r
        RegionId.NoteCommit.Which.New) =
    layouter_facts
      (let🞵 result :=
        Garden.Orchard.circuit
          .synth_full_mul_incomplete_with_rows
          (RegionId.NoteCommit RegionId.NoteCommit.Which.New
            RegionId.NoteCommit.FixedBaseIncomplete)
          Garden.Orchard.constants.fixed_bases.note_commit_r.full_fixed_rows in
       Garden.Orchard.circuit.synthesize_full_fixed_base_mul_last_region
         (RegionId.NoteCommit RegionId.NoteCommit.Which.New
           RegionId.NoteCommit.FixedBaseLast)
         result).
  Proof. reflexivity. Qed.

  (** The output point of the local ladder, as a [Point.t] of cell values
      (the [note_commit.AssignedPoint.t] analogue of [assigned_point_value]). *)
  Definition note_commit_assigned_point_value
      (Γ : Assignment.t columns RegionId.t)
      (point : Garden.Orchard.circuit.note_commit.AssignedPoint.t)
      : Point.t := {|
    Point.x :=
      eval_cell Γ point.(Garden.Orchard.circuit.note_commit.AssignedPoint.x);
    Point.y :=
      eval_cell Γ point.(Garden.Orchard.circuit.note_commit.AssignedPoint.y);
  |}.

  Lemma note_commit_r_value_eq
      (Γ : Assignment.t columns RegionId.t) :
    note_commit_assigned_point_value Γ
      (layouter_value
        (Garden.Orchard.circuit.note_commit
          .synthesize_full_fixed_base_mul_note_commit_r
          RegionId.NoteCommit.Which.New)) =
    assigned_point_value Γ
      (layouter_value
        (let🞵 result :=
          Garden.Orchard.circuit
            .synth_full_mul_incomplete_with_rows
            (RegionId.NoteCommit RegionId.NoteCommit.Which.New
              RegionId.NoteCommit.FixedBaseIncomplete)
            Garden.Orchard.constants.fixed_bases.note_commit_r.full_fixed_rows in
         Garden.Orchard.circuit.synthesize_full_fixed_base_mul_last_region
           (RegionId.NoteCommit RegionId.NoteCommit.Which.New
             RegionId.NoteCommit.FixedBaseLast)
           result)).
  Proof. reflexivity. Qed.

  (** ** Facts of the whole full-width program (incomplete + last region),
      from [Holds].  Same peel as
      [OrchardActionUsFree.note_commit_r_incomplete_facts_raw], stopped before
      its final [bind_left] so both regions of the local ladder are kept,
      then transported to the generic region synthesizers by the
      computational bridge above. *)

  Lemma note_commit_r_fixed_base_facts
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    interpret_facts Γ
      (layouter_facts
        (let🞵 result :=
          Garden.Orchard.circuit
            .synth_full_mul_incomplete_with_rows
            (RegionId.NoteCommit RegionId.NoteCommit.Which.New
              RegionId.NoteCommit.FixedBaseIncomplete)
            Garden.Orchard.constants.fixed_bases.note_commit_r.full_fixed_rows in
         Garden.Orchard.circuit.synthesize_full_fixed_base_mul_last_region
           (RegionId.NoteCommit RegionId.NoteCommit.Which.New
             RegionId.NoteCommit.FixedBaseLast)
           result)).
  Proof.
    pose proof (holds_facts Γ Hcircuit) as Hfacts.
    unfold Garden.Orchard.circuit.synthesize in Hfacts.
    do 9 apply interpret_layouter_facts_bind_right in Hfacts.
    apply interpret_layouter_facts_bind_left in Hfacts.
    unfold Garden.Orchard.circuit.synthesize_note_commit_new in Hfacts.
    do 4 apply interpret_layouter_facts_bind_right in Hfacts.
    apply interpret_layouter_facts_bind_left in Hfacts.
    apply interpret_layouter_facts_in_namespace in Hfacts.
    unfold Garden.Orchard.circuit.note_commit.synthesize_new in Hfacts.
    unfold Garden.Orchard.circuit.note_commit.synthesize_instance in Hfacts.
    cbv zeta in Hfacts.
    do 17 apply interpret_layouter_facts_bind_right in Hfacts.
    apply interpret_layouter_facts_bind_left in Hfacts.
    apply interpret_layouter_facts_in_namespace in Hfacts.
    apply interpret_layouter_facts_bind_left in Hfacts.
    do 2 apply interpret_layouter_facts_in_namespace in Hfacts.
    rewrite note_commit_r_fixed_base_facts_eq in Hfacts.
    exact Hfacts.
  Qed.

  (** ** Per-window correctness against the split spec table (through the
      generic [full_width_table_window_correct], not a [do 85] case split) *)

  Lemma note_commit_r_window_correct
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (j : nat) (w : EccSpec.fixed_window)
      (Hnth :
        List.nth_error
          (note_commit_r_first :: note_commit_r_middle ++
            [note_commit_r_last]) j = Some w) :
    incomplete_additions_window_point Γ
      (RegionId.NoteCommit RegionId.NoteCommit.Which.New
        RegionId.NoteCommit.FixedBaseIncomplete) (Z.of_nat j) =
    EccSpec.fixed_window_point w
      (EccSpec.window_digit
        (read_scalar_from_windows Γ
          (RegionId.NoteCommit RegionId.NoteCommit.Which.New
            RegionId.NoteCommit.FixedBaseIncomplete) 85)
        j)
      (List.nth j
        (read_us Γ
          (RegionId.NoteCommit RegionId.NoteCommit.Which.New
            RegionId.NoteCommit.FixedBaseIncomplete) 85)
        0).
  Proof.
    rewrite <- note_commit_r_spec_table_split in Hnth.
    assert (Hj : (j < 85)%nat).
    { pose proof (proj1 (List.nth_error_Some
        (OrchardSpec.note_commit_r orchard_circuit_params) j)) as Hlt.
      rewrite OrchardActionUsFree.note_commit_r_table_length in Hlt.
      apply Hlt.
      rewrite Hnth.
      discriminate. }
    apply List.nth_error_nth with (d := fixed_window_default) in Hnth.
    rewrite <- Hnth.
    exact
      (OrchardActionUsFree.full_width_table_window_correct Γ
        (RegionId.NoteCommit RegionId.NoteCommit.Which.New
          RegionId.NoteCommit.FixedBaseIncomplete)
        Garden.Orchard.constants.fixed_bases.note_commit_r.full_fixed_rows
        OrchardActionUsFree.note_commit_r_rows_standard
        OrchardActionUsFree.note_commit_r_rows_length
        (OrchardActionUsFree.note_commit_r_incomplete_facts Γ Hcircuit)
        (holds_gates Γ Hcircuit)
        j Hj).
  Qed.

  (** ** Window x-nonzero for the 85 NoteCommitR windows (from the on-curve
      coordinates check; the counterpart of [spend_auth_g_window_x_nonzero]) *)

  Lemma note_commit_r_window_x_nonzero
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (i : nat) (Hi : (i < 85)%nat) :
    UnOp.from
      (Point.x
        (incomplete_additions_window_point Γ
          (RegionId.NoteCommit RegionId.NoteCommit.Which.New
            RegionId.NoteCommit.FixedBaseIncomplete)
          (Z.of_nat i))) <> 0.
  Proof.
    apply (full_width_incomplete_window_x_nonzero Γ
      (RegionId.NoteCommit RegionId.NoteCommit.Which.New
        RegionId.NoteCommit.FixedBaseIncomplete)
      Garden.Orchard.constants.fixed_bases.note_commit_r.full_fixed_rows
      i
      (OrchardActionUsFree.note_commit_r_incomplete_facts Γ Hcircuit)
      (holds_gates Γ Hcircuit)
      Hi).
  Qed.

  (** ** The complete precondition from [Holds]: ladder distinctness +
      on-curve + x-nonzero, through
      [incomplete_complete_precondition_of_distinct] *)

  Lemma note_commit_r_complete_of_holds
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    incomplete_additions_complete_precondition Γ
      (RegionId.NoteCommit RegionId.NoteCommit.Which.New
        RegionId.NoteCommit.FixedBaseIncomplete) 1 83
      (incomplete_additions_window_point Γ
        (RegionId.NoteCommit RegionId.NoteCommit.Which.New
          RegionId.NoteCommit.FixedBaseIncomplete) 0).
  Proof.
    pose proof (OrchardActionUsFree.note_commit_r_incomplete_facts Γ Hcircuit)
      as Hfacts.
    apply incomplete_complete_precondition_of_distinct.
    - replace 0 with (Z.of_nat 0) by reflexivity.
      apply (full_width_incomplete_region_window_on_curve Γ
        (RegionId.NoteCommit RegionId.NoteCommit.Which.New
          RegionId.NoteCommit.FixedBaseIncomplete)
        Garden.Orchard.constants.fixed_bases.note_commit_r.full_fixed_rows
        0%nat Hfacts (holds_gates Γ Hcircuit)).
      lia.
    - replace 0 with (Z.of_nat 0) by reflexivity.
      apply (note_commit_r_window_x_nonzero Γ Hcircuit 0%nat).
      lia.
    - intros i Hi.
      replace (1 + Z.of_nat i) with (Z.of_nat (S i)) by lia.
      apply (full_width_incomplete_region_window_on_curve Γ
        (RegionId.NoteCommit RegionId.NoteCommit.Which.New
          RegionId.NoteCommit.FixedBaseIncomplete)
        Garden.Orchard.constants.fixed_bases.note_commit_r.full_fixed_rows
        (S i) Hfacts (holds_gates Γ Hcircuit)).
      lia.
    - intros i Hi.
      replace (1 + Z.of_nat i) with (Z.of_nat (S i)) by lia.
      apply (note_commit_r_window_x_nonzero Γ Hcircuit (S i)).
      lia.
    - exact
        (NoteCommitRLadder.note_commit_r_distinct_holds
          Γ Hcircuit).
  Qed.

  Lemma note_commit_r_incomplete_of_holds
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    incomplete_additions_precondition Γ
      (RegionId.NoteCommit RegionId.NoteCommit.Which.New
        RegionId.NoteCommit.FixedBaseIncomplete) 1 83
      (incomplete_additions_window_point Γ
        (RegionId.NoteCommit RegionId.NoteCommit.Which.New
          RegionId.NoteCommit.FixedBaseIncomplete) 0).
  Proof.
    apply incomplete_complete_implies_precondition.
    exact (note_commit_r_complete_of_holds Γ Hcircuit).
  Qed.

  (** ** The circuit precondition from [Holds] (the counterpart of
      [value_commit_r_circuit_precondition_of_holds]) *)

  Lemma note_commit_r_circuit_precondition_of_holds
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    fixed_scalar_mul_circuit_precondition
      (OrchardSpec.note_commit_r orchard_circuit_params)
      (read_scalar_from_windows Γ
        (RegionId.NoteCommit RegionId.NoteCommit.Which.New
          RegionId.NoteCommit.FixedBaseIncomplete) 85)
      (read_us Γ
        (RegionId.NoteCommit RegionId.NoteCommit.Which.New
          RegionId.NoteCommit.FixedBaseIncomplete) 85).
  Proof.
    pose proof (note_commit_r_window_correct Γ Hcircuit 0%nat
      note_commit_r_first eq_refl) as Hfirst.
    pose proof (OrchardActionUsFree.note_commit_r_incomplete_facts Γ Hcircuit)
      as Hfacts.
    rewrite note_commit_r_spec_table_split.
    cbn [fixed_scalar_mul_circuit_precondition].
    rewrite <- Hfirst.
    eapply circuit_tail_precondition_of_complete
      with (n := 83%nat).
    - rewrite List.length_app, note_commit_r_middle_length. reflexivity.
    - exact (note_commit_r_complete_of_holds Γ Hcircuit).
    - intros j w Hnth.
      replace (1 + Z.of_nat j) with (Z.of_nat (S j)) by lia.
      replace (1 + j)%nat with (S j) by lia.
      apply (note_commit_r_window_correct Γ Hcircuit).
      cbn [List.nth_error].
      exact Hnth.
    - apply (full_width_incomplete_region_window_on_curve Γ
        (RegionId.NoteCommit RegionId.NoteCommit.Which.New
          RegionId.NoteCommit.FixedBaseIncomplete)
        Garden.Orchard.constants.fixed_bases.note_commit_r.full_fixed_rows
        0%nat Hfacts (holds_gates Γ Hcircuit)).
      lia.
    - exact (proj1 (incomplete_additions_window_point_reduced Γ
        (RegionId.NoteCommit RegionId.NoteCommit.Which.New
          RegionId.NoteCommit.FixedBaseIncomplete)
        (Z.of_nat 0))).
    - exact (proj2 (incomplete_additions_window_point_reduced Γ
        (RegionId.NoteCommit RegionId.NoteCommit.Which.New
          RegionId.NoteCommit.FixedBaseIncomplete)
        (Z.of_nat 0))).
    - intros j Hj.
      rewrite List.length_app, note_commit_r_middle_length in Hj.
      cbn [List.length] in Hj.
      replace (1 + Z.of_nat j) with (Z.of_nat (S j)) by lia.
      apply (full_width_incomplete_region_window_on_curve Γ
        (RegionId.NoteCommit RegionId.NoteCommit.Which.New
          RegionId.NoteCommit.FixedBaseIncomplete)
        Garden.Orchard.constants.fixed_bases.note_commit_r.full_fixed_rows
        (S j) Hfacts (holds_gates Γ Hcircuit)).
      lia.
    - intros j Hj.
      exact (proj1 (incomplete_additions_window_point_reduced Γ
        (RegionId.NoteCommit RegionId.NoteCommit.Which.New
          RegionId.NoteCommit.FixedBaseIncomplete)
        (1 + Z.of_nat j))).
    - intros j Hj.
      exact (proj2 (incomplete_additions_window_point_reduced Γ
        (RegionId.NoteCommit RegionId.NoteCommit.Which.New
          RegionId.NoteCommit.FixedBaseIncomplete)
        (1 + Z.of_nat j))).
  Qed.

  (** ** K-out — the blinding-leg output equality, from [Holds] alone,
      phrased over [note_commit.v]'s own ladder program and [AssignedPoint]
      record (what the CMX [Hnote] bridge will consume). *)

  Lemma full_note_commit_r_scalar_mul_correct
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    Field.map_mod
      (note_commit_assigned_point_value Γ
        (layouter_value
          (Garden.Orchard.circuit.note_commit
            .synthesize_full_fixed_base_mul_note_commit_r
            RegionId.NoteCommit.Which.New))) =
    EccSpec.fixed_scalar_mul
      (OrchardSpec.note_commit_r orchard_circuit_params)
      (read_scalar_from_windows Γ
        (RegionId.NoteCommit RegionId.NoteCommit.Which.New
          RegionId.NoteCommit.FixedBaseIncomplete) 85)
      (read_us Γ
        (RegionId.NoteCommit RegionId.NoteCommit.Which.New
          RegionId.NoteCommit.FixedBaseIncomplete) 85).
  Proof.
    pose proof (note_commit_r_fixed_base_facts Γ Hcircuit) as Hfacts.
    rewrite (note_commit_r_value_eq Γ).
    rewrite note_commit_r_spec_table_split.
    eapply full_with_rows_scalar_mul_correct
      with (first := note_commit_r_first)
           (middle := note_commit_r_middle)
           (last := note_commit_r_last).
    - exact Hfacts.
    - exact (holds_gates Γ Hcircuit).
    - exact
        (note_commit_r_incomplete_of_holds Γ Hcircuit).
    - exact note_commit_r_table_split.
    - exact note_commit_r_middle_length.
    - intros j w Hnth.
      exact (note_commit_r_window_correct Γ Hcircuit j w Hnth).
    - rewrite <- note_commit_r_spec_table_split.
      exact
        (note_commit_r_circuit_precondition_of_holds
          Γ Hcircuit).
  Qed.

End NoteCommitROut.
