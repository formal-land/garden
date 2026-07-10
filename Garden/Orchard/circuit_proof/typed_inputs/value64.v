(** * Typed inputs: the 64-bit ranges of the two note values

    The [v_old]/[v_new] range facts consumed by the true-ℤ value reading
    ([circuit_proof/cv_net_value.v]): the [VOld]/[VNew] free-witness cells —
    the sources of [in_v_old]/[in_v_new] in [read_action_inputs] — lie in
    [0, 2^64).

    Route (the note-commit piece machinery, not the standalone
    lookup-range-check region): each note-commit circuit packs its 64-bit
    value slot as [d_2 + z1_d·2^8 + e_0·2^58], and the [input_value] gate
    ties that decomposition to the value witness cell through the [Copy]
    graph.  [OldNoteWords.value_int] / [NoteCommitNewWords.value_int]
    already derive the exact integer identity AND the [2^64] bound from
    [Holds] plus the [d_2]/[e_0] short-lookup range facts, so the only
    hypotheses here are the respective short-lookup honesty predicates
    ([OldNoteWords.old_note_short_lookup_ok],
    [NoteCommitNewWords.note_commit_new_short_lookup_ok] — the same
    selector-plane idealization carried, for the new side, inside
    [NoteCommitNewCmx.note_commit_witness_ok], and, for the old side,
    inside [OrchardValidActionInputs.old_note_witness_ok]). *)

Require Import Garden.Halo2.main.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.lemmas.
Require Import Garden.Orchard.columns.
Require Garden.Orchard.circuit.
Require Import Garden.Orchard.protocol_spec.
Require Import Garden.Orchard.circuit_proof.inputs.
Require Import Garden.Orchard.circuit_proof.old_note.words.
Require Import Garden.Orchard.circuit_proof.note_commit.words.
Require Import Garden.Field.Field.
Require Import Garden.Plonky3.M.
Require Import Stdlib.ZArith.ZArith.

#[local] Existing Instance Primes.PallasPIsPrime.

Global Open Scope Z_scope.

Module TypedInputsValue64.

  Local Notation Holds Γ :=
    (circuit_holds Γ
      Garden.Orchard.circuit.synthesize
      (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)).

  (** ** The old-note value cell

      [OldNoteWords.value_int] bounds [voldv Γ] — the reduced value of the
      [WitnessInput.VOld] [A0] cell, exactly the cell
      [read_action_inputs] reads for [in_v_old] — under the [d_2] (8-bit)
      and [e_0] (6-bit) short-lookup facts, the third and fourth conjuncts
      of [old_note_short_lookup_ok]. *)
  Lemma v_old_read_64
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (Hshort : OldNoteWords.old_note_short_lookup_ok Γ) :
    0 <=
      OrchardActionInputs.read Γ
        (RegionId.WitnessInput RegionId.WitnessInput.VOld) <
      2 ^ 64.
  Proof.
    destruct Hshort as (_ & _ & Hd2 & He0 & _).
    pose proof (OldNoteWords.value_int Γ Hcircuit Hd2 He0) as [_ Hrange].
    unfold OrchardActionInputs.read, OrchardActionInputs.read_advice.
    rewrite (OldNoteWords.cur_val Γ
      (RegionId.WitnessInput RegionId.WitnessInput.VOld) Advice.A0 0).
    exact Hrange.
  Qed.

  (** ** The new-note value cell

      The [Which.New] mirror: [NoteCommitNewWords.value_int] bounds
      [vnewv Γ] — the [WitnessInput.VNew] [A0] cell, the source of
      [in_v_new]. *)
  Lemma v_new_read_64
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (Hshort : NoteCommitNewWords.note_commit_new_short_lookup_ok Γ) :
    0 <=
      OrchardActionInputs.read Γ
        (RegionId.WitnessInput RegionId.WitnessInput.VNew) <
      2 ^ 64.
  Proof.
    destruct Hshort as (_ & _ & Hd2 & He0 & _).
    pose proof (NoteCommitNewWords.value_int Γ Hcircuit Hd2 He0)
      as [_ Hrange].
    unfold OrchardActionInputs.read, OrchardActionInputs.read_advice.
    rewrite (NoteCommitNewWords.cur_val Γ
      (RegionId.WitnessInput RegionId.WitnessInput.VNew) Advice.A0 0).
    exact Hrange.
  Qed.

  (** ** The [read_action_inputs] spellings consumed downstream *)

  Lemma in_v_old_64
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (Hshort : OldNoteWords.old_note_short_lookup_ok Γ) :
    0 <=
      OrchardSpec.in_v_old (OrchardActionInputs.read_action_inputs Γ) <
      2 ^ 64.
  Proof.
    exact (v_old_read_64 Γ Hcircuit Hshort).
  Qed.

  Lemma in_v_new_64
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (Hshort : NoteCommitNewWords.note_commit_new_short_lookup_ok Γ) :
    0 <=
      OrchardSpec.in_v_new (OrchardActionInputs.read_action_inputs Γ) <
      2 ^ 64.
  Proof.
    exact (v_new_read_64 Γ Hcircuit Hshort).
  Qed.

End TypedInputsValue64.
