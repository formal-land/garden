(** * The [Hnote] hypothesis of the CMX bridge

    Composition of the four CMX legs into the [Hnote] hypothesis of
    [OrchardActionBridges.cmx_correct_of_note_commit_new]:

    - the complete-add + rcm leg
      ([NoteCommitNewAdd.synthesize_new_cm_point_add_rcm_correct]): the
      output point of [note_commit.synthesize_new] is [point_add] of the
      hash point [new_cm_hash_m] and the spec blinding leg
      [fixed_scalar_mul (note_commit_r prm) (in_rcm_new inp) (w_us_rcm wit)];
    - the Sinsemilla hash fold
      ([NoteCommitNewHash.note_commit_new_hash_point_correct]): the hash
      point equals [sinsemilla_hash_to_point] of the NoteCommit domain point
      on the 109 grid words, under the incomplete-add nondegeneracy side
      condition;
    - the word identification
      ([NoteCommitNewWords.note_commit_new_words_correct]): the grid words
      are [OrchardSpec.note_commit_message] of the circuit's new-note reads,
      under the short-lookup side condition;
    - the nullifier leg ([NullifierKOut.nullifier_cell_correct]): the
      [rho_new] cell of the message carries
      [OrchardSpec.out_nf_old (action_spec_of Γ)].

    [cmx_hnote] states the hypothesis verbatim; [cmx_correct] applies the
    bridge, closing [read_public_instance Γ CMX = out_cmx (action_spec_of Γ)]
    under the two side conditions. *)

Require Import Garden.Halo2.main.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.lemmas.
Require Import Garden.Orchard.columns.
Require Garden.Orchard.circuit.
Require Garden.Orchard.circuit.note_commit.
Require Garden.Halo2.halo2_gadgets.sinsemilla.chip.
Require Import Garden.Halo2.halo2_gadgets.sinsemilla.hash_to_point_proof.
Require Import Garden.Halo2.halo2_gadgets.sinsemilla.spec.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.spec.
Require Import Garden.Orchard.protocol_spec.
Require Import Garden.Orchard.circuit_proof.internal_spec.
Require Import Garden.Orchard.circuit_proof.inputs.
Require Import Garden.Orchard.circuit_proof.facts.
Require Import Garden.Orchard.circuit_proof.fixed_base.main.
Require Import Garden.Orchard.circuit_proof.note_commit_r.out.
Require Import Garden.Orchard.circuit_proof.nullifier_k.out.
Require Import Garden.Orchard.circuit_proof.bridges.
Require Import Garden.Orchard.circuit_proof.note_commit.hash.
Require Import Garden.Orchard.circuit_proof.note_commit.words.
Require Import Garden.Orchard.circuit_proof.note_commit.add.
Require Import Garden.Field.Field.
Require Import Garden.Plonky3.M.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Lists.List.

Import ListNotations.

#[local] Existing Instance Primes.PallasPIsPrime.

Global Open Scope Z_scope.


Module NoteCommitNewCmx.
  Import OrchardActionFixedBase.

  Local Notation Holds Γ :=
    (circuit_holds Γ
      Garden.Orchard.circuit.synthesize
      (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)).

  (** ** [out_cmx] unfolded, in small steps

      The monolithic [reflexivity] on the unfolded [out_cmx] equation is
      catastrophically slow: as soon as one argument pair of the two
      [sinsemilla_hash_to_point] applications fails the syntactic check,
      unification falls back to normalising the hash fold over its 109
      symbolic words (each incomplete-add step duplicates the accumulator
      inside [mod_inverse] terms).  The lemmas below keep every conversion
      one-projection small and make every remaining step a syntactic
      rewrite. *)

  (** [action_spec_of] as its body — two delta steps, no field access. *)
  Lemma action_spec_of_eq (Γ : Assignment.t columns RegionId.t) :
    action_spec_of Γ =
    OrchardCircuitSpec.orchard_action_spec orchard_internal_params
      (read_action_inputs Γ) (read_action_witness Γ).
  Proof. reflexivity. Qed.

  (** [out_cmx] of the spec record over VARIABLE parameters/inputs/witness:
      both sides unfold to the same application without touching the hash
      fold. *)
  Lemma out_cmx_generic
      (prm : OrchardCircuitSpec.Params)
      (inp : OrchardSpec.ActionInputs) (wit : OrchardCircuitSpec.ActionWitness) :
    OrchardSpec.out_cmx (OrchardCircuitSpec.orchard_action_spec prm inp wit) =
    Point.x
      (EccSpec.point_add
        (SinsemillaSpec.sinsemilla_hash_to_point
          (OrchardSpec.note_commit_q (OrchardCircuitSpec.domain prm))
          (OrchardSpec.note_commit_message
            (OrchardSpec.in_g_d_new inp)
            (OrchardSpec.in_pk_d_new inp)
            (OrchardSpec.in_v_new inp)
            (OrchardSpec.out_nf_old
              (OrchardCircuitSpec.orchard_action_spec prm inp wit))
            (OrchardSpec.in_psi_new inp)))
        (EccSpec.fixed_scalar_mul
          (OrchardCircuitSpec.note_commit_r prm)
          (OrchardSpec.in_rcm_new inp)
          (OrchardCircuitSpec.w_us_rcm wit))).
  Proof. reflexivity. Qed.

  (** The new-note input fields of [read_action_inputs], as the raw readers
      (the [in_rcm_new_read]/[w_us_rcm_read] pattern of the add lane). *)
  Lemma in_g_d_new_read (Γ : Assignment.t columns RegionId.t) :
    OrchardSpec.in_g_d_new (read_action_inputs Γ) =
    OrchardActionInputs.read_point Γ RegionId.NoteCommitNewWitnessGD.
  Proof. reflexivity. Qed.

  Lemma in_pk_d_new_read (Γ : Assignment.t columns RegionId.t) :
    OrchardSpec.in_pk_d_new (read_action_inputs Γ) =
    OrchardActionInputs.read_point Γ RegionId.NoteCommitNewWitnessPkD.
  Proof. reflexivity. Qed.

  Lemma in_v_new_read (Γ : Assignment.t columns RegionId.t) :
    OrchardSpec.in_v_new (read_action_inputs Γ) =
    OrchardActionInputs.read Γ
      (RegionId.WitnessInput RegionId.WitnessInput.VNew).
  Proof. reflexivity. Qed.

  Lemma in_psi_new_read (Γ : Assignment.t columns RegionId.t) :
    OrchardSpec.in_psi_new (read_action_inputs Γ) =
    OrchardActionInputs.read Γ RegionId.NoteCommitNewWitnessPsi.
  Proof. reflexivity. Qed.

  (** [out_cmx] of the action spec, unfolded to its two legs at the
      circuit-read arguments — each written with the exact constant the
      corresponding leg lemma is stated at, so the leg rewrites in
      [cmx_hnote] fire syntactically. *)
  Lemma out_cmx_spec_eq (Γ : Assignment.t columns RegionId.t) :
    OrchardSpec.out_cmx (action_spec_of Γ) =
    Point.x
      (EccSpec.point_add
        (SinsemillaSpec.sinsemilla_hash_to_point
          (OrchardSpec.note_commit_q NoteCommitNewHash.orchard_circuit_params)
          (OrchardSpec.note_commit_message
            (OrchardActionInputs.read_point Γ RegionId.NoteCommitNewWitnessGD)
            (OrchardActionInputs.read_point Γ RegionId.NoteCommitNewWitnessPkD)
            (OrchardActionInputs.read Γ
              (RegionId.WitnessInput RegionId.WitnessInput.VNew))
            (OrchardSpec.out_nf_old (action_spec_of Γ))
            (OrchardActionInputs.read Γ RegionId.NoteCommitNewWitnessPsi)))
        (EccSpec.fixed_scalar_mul
          (OrchardCircuitSpec.note_commit_r orchard_internal_params)
          (OrchardSpec.in_rcm_new (read_action_inputs Γ))
          (OrchardCircuitSpec.w_us_rcm (read_action_witness Γ)))).
  Proof.
    rewrite (action_spec_of_eq Γ).
    rewrite
      (out_cmx_generic orchard_internal_params
        (read_action_inputs Γ) (read_action_witness Γ)).
    rewrite orchard_internal_domain_eq.
    rewrite (in_g_d_new_read Γ).
    rewrite (in_pk_d_new_read Γ).
    rewrite (in_v_new_read Γ).
    rewrite (in_psi_new_read Γ).
    reflexivity.
  Qed.

  (** ** The hash operand of the "M + [r] R" complete addition

      The x/y cells of [NoteCommitNewAdd.new_cm_hash_m] are the hash lane's
      A5/A8 row-109 cells ([hash_result_{x,y}_cell] at the genuine piece
      arguments), so its evaluated point is the record the hash capstone
      speaks about. *)

  Lemma hash_m_x_cell :
    NoteCommitNewAdd.new_cm_hash_m
      .(Garden.Orchard.circuit.note_commit.AssignedPoint.x) =
    Garden.Halo2.Synthesis.Cell.advice
      NoteCommitNewHash.new_hash_region Advice.A5 109.
  Proof. exact (NoteCommitNewHash.hash_result_x_cell _ _ _ _ _ _ _ _). Qed.

  Lemma hash_m_y_cell :
    NoteCommitNewAdd.new_cm_hash_m
      .(Garden.Orchard.circuit.note_commit.AssignedPoint.y) =
    Garden.Halo2.Synthesis.Cell.advice
      NoteCommitNewHash.new_hash_region Advice.A8 109.
  Proof. exact (NoteCommitNewHash.hash_result_y_cell _ _ _ _ _ _ _ _). Qed.

  Lemma hash_m_value_eq (Γ : Assignment.t columns RegionId.t) :
    Field.map_mod
      (NoteCommitROut.note_commit_assigned_point_value Γ
        NoteCommitNewAdd.new_cm_hash_m) =
    {|
      Point.x :=
        UnOp.from (eval_cell Γ
          (Garden.Halo2.Synthesis.Cell.advice
            NoteCommitNewHash.new_hash_region Advice.A5 109));
      Point.y :=
        UnOp.from (eval_cell Γ
          (Garden.Halo2.Synthesis.Cell.advice
            NoteCommitNewHash.new_hash_region Advice.A8 109));
    |}.
  Proof.
    unfold NoteCommitROut.note_commit_assigned_point_value.
    rewrite hash_m_x_cell.
    rewrite hash_m_y_cell.
    reflexivity.
  Qed.

  (** The [Hnote] hypothesis of
      [OrchardActionBridges.cmx_correct_of_note_commit_new], verbatim: the
      x-cell of [note_commit.synthesize_new] at the action's witnessed
      new-note arguments carries [out_cmx (action_spec_of Γ)].  The two
      leading side conditions are the lanes': the Sinsemilla incomplete-add
      nondegeneracy of the witnessed 109-word message and the short-lookup
      range facts of the message pieces. *)
  Theorem cmx_hnote
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (Hnondeg :
        SinsemillaHash.nondegenerate NoteCommitNewHash.note_commit_Q
          (NoteCommitNewHash.note_commit_new_words Γ))
      (Hshort : NoteCommitNewWords.note_commit_new_short_lookup_ok Γ) :
    let psi_old :=
      layouter_value
        (Garden.Orchard.circuit.assign_free_advice
          (Garden.Orchard.circuit.witness_input_region
            RegionId.WitnessInput.PsiOld)
          "witness psi_old" Advice.A0 0) in
    let rho_old :=
      layouter_value
        (Garden.Orchard.circuit.assign_free_advice
          (Garden.Orchard.circuit.witness_input_region
            RegionId.WitnessInput.RhoOld)
          "witness rho_old" Advice.A0 0) in
    let cm_old :=
      layouter_value
        (Garden.Orchard.circuit.witness_point
          (Garden.Orchard.circuit.witness_input_region
            RegionId.WitnessInput.CmOld)
          "cm_old") in
    let nk :=
      layouter_value
        (Garden.Orchard.circuit.assign_free_advice
          (Garden.Orchard.circuit.witness_input_region
            RegionId.WitnessInput.Nk)
          "witness nk" Advice.A0 0) in
    let v_new :=
      layouter_value
        (Garden.Orchard.circuit.assign_free_advice
          (Garden.Orchard.circuit.witness_input_region
            RegionId.WitnessInput.VNew)
          "witness v_new" Advice.A0 0) in
    let rho_new :=
      layouter_value
        (Garden.Orchard.circuit.synthesize_nullifier
          rho_old psi_old nk cm_old) in
    let g_d_new_star :=
      layouter_value
        (Garden.Orchard.circuit.witness_non_identity_point
          RegionId.NoteCommitNewWitnessGD
          "witness g_d_new_star") in
    let pk_d_new :=
      layouter_value
        (Garden.Orchard.circuit.witness_non_identity_point
          RegionId.NoteCommitNewWitnessPkD
          "witness pk_d_new") in
    let psi_new :=
      layouter_value
        (Garden.Orchard.circuit.assign_free_advice
          RegionId.NoteCommitNewWitnessPsi
          "witness psi_new" Advice.A0 0) in
    UnOp.from
      (eval_cell Γ
        (layouter_value
          (Garden.Orchard.circuit.note_commit.synthesize_new
            g_d_new_star.(Garden.Orchard.circuit.AssignedPoint.x)
            g_d_new_star.(Garden.Orchard.circuit.AssignedPoint.y)
            pk_d_new.(Garden.Orchard.circuit.AssignedPoint.x)
            pk_d_new.(Garden.Orchard.circuit.AssignedPoint.y)
            v_new
            rho_new
            psi_new)).(Garden.Orchard.circuit.note_commit.AssignedPoint.x)) =
      OrchardSpec.out_cmx (action_spec_of Γ).
  Proof.
    cbv zeta.
    pose proof
      (NoteCommitNewAdd.synthesize_new_cm_point_add_rcm_correct Γ Hcircuit
        (layouter_value
          (Garden.Orchard.circuit.witness_non_identity_point
            RegionId.NoteCommitNewWitnessGD
            "witness g_d_new_star")).(Garden.Orchard.circuit.AssignedPoint.x)
        (layouter_value
          (Garden.Orchard.circuit.witness_non_identity_point
            RegionId.NoteCommitNewWitnessGD
            "witness g_d_new_star")).(Garden.Orchard.circuit.AssignedPoint.y)
        (layouter_value
          (Garden.Orchard.circuit.witness_non_identity_point
            RegionId.NoteCommitNewWitnessPkD
            "witness pk_d_new")).(Garden.Orchard.circuit.AssignedPoint.x)
        (layouter_value
          (Garden.Orchard.circuit.witness_non_identity_point
            RegionId.NoteCommitNewWitnessPkD
            "witness pk_d_new")).(Garden.Orchard.circuit.AssignedPoint.y)
        (layouter_value
          (Garden.Orchard.circuit.assign_free_advice
            (Garden.Orchard.circuit.witness_input_region
              RegionId.WitnessInput.VNew)
            "witness v_new" Advice.A0 0))
        (layouter_value
          (Garden.Orchard.circuit.synthesize_nullifier
            (layouter_value
              (Garden.Orchard.circuit.assign_free_advice
                (Garden.Orchard.circuit.witness_input_region
                  RegionId.WitnessInput.RhoOld)
                "witness rho_old" Advice.A0 0))
            (layouter_value
              (Garden.Orchard.circuit.assign_free_advice
                (Garden.Orchard.circuit.witness_input_region
                  RegionId.WitnessInput.PsiOld)
                "witness psi_old" Advice.A0 0))
            (layouter_value
              (Garden.Orchard.circuit.assign_free_advice
                (Garden.Orchard.circuit.witness_input_region
                  RegionId.WitnessInput.Nk)
                "witness nk" Advice.A0 0))
            (layouter_value
              (Garden.Orchard.circuit.witness_point
                (Garden.Orchard.circuit.witness_input_region
                  RegionId.WitnessInput.CmOld)
                "cm_old"))))
        (layouter_value
          (Garden.Orchard.circuit.assign_free_advice
            RegionId.NoteCommitNewWitnessPsi
            "witness psi_new" Advice.A0 0)))
      as Hadd.
    refine (eq_trans (f_equal Point.x Hadd) _).
    rewrite (hash_m_value_eq Γ).
    rewrite (NoteCommitNewHash.note_commit_new_hash_point_correct
      Γ Hcircuit Hnondeg).
    pose proof
      (NoteCommitNewWords.note_commit_new_words_correct Γ Hcircuit Hshort)
      as Hwords.
    cbv zeta in Hwords.
    rewrite Hwords.
    pose proof (NullifierKOut.nullifier_cell_correct Γ Hcircuit) as Hnf.
    cbv zeta in Hnf.
    rewrite Hnf.
    exact (eq_sym (out_cmx_spec_eq Γ)).
  Qed.

  (** The assembled CMX bridge: the public [CMX] instance equals the spec's
      new-note commitment x-coordinate, from [Holds] and the two lane side
      conditions.  The [exact] application certifies that [cmx_hnote] is the
      [Hnote] hypothesis of the bridge lemma. *)
  Theorem cmx_correct
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (Hnondeg :
        SinsemillaHash.nondegenerate NoteCommitNewHash.note_commit_Q
          (NoteCommitNewHash.note_commit_new_words Γ))
      (Hshort : NoteCommitNewWords.note_commit_new_short_lookup_ok Γ) :
    read_public_instance Γ Garden.Orchard.circuit.CMX =
      OrchardSpec.out_cmx (action_spec_of Γ).
  Proof.
    exact
      (OrchardActionBridges.cmx_correct_of_note_commit_new Γ Hcircuit
        (cmx_hnote Γ Hcircuit Hnondeg Hshort)).
  Qed.

  (** ** The bundled witness-honesty side condition

      The two CMX side conditions packaged as a single per-assignment
      predicate, the [merkle_witness_ok] shape consumed by the top-level
      [satisfies_specification] / [deterministic] theorems:

      - the Sinsemilla incomplete-add nondegeneracy of the witnessed
        109-word new-note message (the hash fold's gradients are
        unconstrained on the exceptional x-collision cases);
      - the short-lookup range facts of the message pieces (the halo2 short
        lookup constrains [z_cur] only where [q_running = 0], and the
        relational selector model leaves [q_running] free at those rows). *)
  Definition note_commit_witness_ok
      (Γ : Assignment.t columns RegionId.t) : Prop :=
    SinsemillaHash.nondegenerate NoteCommitNewHash.note_commit_Q
      (NoteCommitNewHash.note_commit_new_words Γ) /\
    NoteCommitNewWords.note_commit_new_short_lookup_ok Γ.

  Theorem cmx_correct_of_witness_ok
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (Hok : note_commit_witness_ok Γ) :
    read_public_instance Γ Garden.Orchard.circuit.CMX =
      OrchardSpec.out_cmx (action_spec_of Γ).
  Proof.
    destruct Hok as [Hnondeg Hshort].
    exact (cmx_correct Γ Hcircuit Hnondeg Hshort).
  Qed.

End NoteCommitNewCmx.
