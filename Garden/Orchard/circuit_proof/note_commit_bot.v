(** * The two note-commitment ⊥ clauses of §4.18.4, from acceptance alone

    §4.18.4 'Action Statement (Orchard)' of the Zcash protocol specification
    ([docs/protocol.pdf]) states the two note-commitment clauses
    disjunctively:

    - 'New note commitment integrity':
      [Extract⊥_P(NoteCommit^Orchard_rcm_new(g⋆_d_new, pk⋆_d_new, v_new,
      ρ_new, ψ_new)) ∈ {cm_x, ⊥}] with [ρ_new = nf_old];
    - 'Old note commitment integrity':
      [NoteCommit^Orchard_rcm_old(g⋆_d_old, pk⋆_d_old, v_old, ρ_old, ψ_old)
      ∈ {cm^old, ⊥}].

    The ⊥ member is not slack the model invents: §5.4.1.9 'Sinsemilla Hash
    Function' defines [SinsemillaHashToPoint] through the partial
    incomplete addition [⊞], whose exceptional operand pairs
    ([(x, y) ⊞ (x′, y′) = ⊥ if x = x′]) the circuit's gates leave
    unconstrained, and the §4.18.4 non-normative note says so: "If
    NoteCommit^Orchard returns ⊥ for the old or new note, then the
    corresponding note commitment integrity check is satisfied.  This
    models the fact that the implemented circuit uses incomplete point
    addition to compute SinsemillaHashToPoint."

    This file discharges both clauses in the ⊥-carrying form of
    [circuit_proof/adversarial_api.v] — [cmx_obligation] and
    [old_note_obligation] — from circuit acceptance and the short-lookup
    range families alone.  No nondegeneracy and no canonicity hypothesis
    appears.

    Proof shape.  The ⊥-carrying fold of [circuit_proof/protocol_spec_bot.v]
    is [None] exactly when the total fold's incomplete additions meet an
    exceptional pair ([hash_to_point_bot_iff] — the bot fold tracks the
    total fold until the first exceptional step, at which point it is
    [None] and stays [None]).  So each clause is a case split on that fold
    over the *witnessed* message: on [None] the ⊥ disjunct closes
    definitionally through the [option_map] commitment shells; otherwise
    the equivalence hands the existing nondegeneracy-conditioned theorem
    ([NoteCommitNewCmx.cmx_correct],
    [OrchardValidActionInputs.old_note_commit_integrity]) exactly the
    hypothesis it wants, and the honest branch is reused verbatim.  The
    only new content is the transport of the fold's word list between the
    circuit spelling (the hash region's grid words) and the protocol
    spelling ([OrchardSpec.note_commit_message] of the read inputs), which
    the words-canonicity theorems already provide.

    Anti-blowup discipline ([docs/compile-performance.md]): every bridge is
    stated over variable inputs or composed as a term
    ([eq_trans]/[eq_sym]/[f_equal]), so no unification ever compares two
    sides differing underneath a [sinsemilla_hash_to_point] application. *)

Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Lists.List.
Require Import Garden.Halo2.main.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.lemmas.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.spec.
Require Import Garden.Halo2.halo2_gadgets.sinsemilla.spec.
Require Import Garden.Halo2.halo2_gadgets.sinsemilla.hash_to_point_proof.
Require Import Garden.Orchard.columns.
Require Garden.Orchard.circuit.
Require Import Garden.Orchard.protocol_spec.
Require Import Garden.Orchard.circuit_proof.internal_spec.
Require Import Garden.Orchard.circuit_proof.inputs.
Require Import Garden.Orchard.circuit_proof.protocol_equiv.
Require Import Garden.Orchard.circuit_proof.valid_action_inputs.
Require Import Garden.Orchard.circuit_proof.note_commit.hash.
Require Import Garden.Orchard.circuit_proof.note_commit.words.
Require Import Garden.Orchard.circuit_proof.note_commit.cmx.
Require Import Garden.Orchard.circuit_proof.old_note.words.
Require Import Garden.Orchard.circuit_proof.old_note.open.
Require Import Garden.Orchard.circuit_proof.nullifier_k.out.
Require Import Garden.Orchard.circuit_proof.us_free.nullifier_k.
Require Import Garden.Orchard.circuit_proof.protocol_spec_bot.
Require Import Garden.Orchard.circuit_proof.adversarial_api.
Require Import Garden.Field.Field.
Require Import Garden.Plonky3.M.

#[local] Existing Instance Primes.PallasPIsPrime.

Global Open Scope Z_scope.

Module OrchardNoteCommitBot.
  Import OrchardActionInputs.
  Import OrchardProtocolSpecBot.
  Import OrchardAdversarialApi.

  Local Notation Holds Γ :=
    (circuit_holds Γ
      Garden.Orchard.circuit.synthesize
      (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)).

  (** ** The protocol-layer reading of the circuit-structured action spec

      [OrchardAction.satisfies_specification] composes the per-output
      bridges with the witness elimination and the protocol equivalence
      inside one theorem; the two clauses here need the same composition
      but only two of its fields, and without the Merkle side condition
      that theorem carries.  The composition is stated once, at the record
      level, and projected. *)

  Lemma action_spec_protocol
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ) :
    action_spec_of Γ =
    OrchardProtocolSpec.orchard_action_spec orchard_circuit_params
      (read_action_inputs Γ).
  Proof.
    exact (eq_trans
      (OrchardActionUsFreeNullifierK.action_spec_us_free Γ Hcircuit)
      (OrchardProtocolEquiv.output_protocol_eq (read_action_inputs Γ)
        (OrchardValidActionInputs.protocol_typed_inputs_of_holds
          Γ Hcircuit))).
  Qed.

  (** Record projections of the protocol action spec, over VARIABLE
      parameters and inputs: both sides are the same application, so
      neither the Sinsemilla fold nor the nullifier is ever reduced. *)

  Lemma out_nf_old_of_action_spec
      (prm : OrchardSpec.Params) (inp : OrchardSpec.ActionInputs) :
    OrchardSpec.out_nf_old
      (OrchardProtocolSpec.orchard_action_spec prm inp) =
    OrchardProtocolSpec.nullifier
      (OrchardSpec.in_nk inp) (OrchardSpec.in_rho_old inp)
      (OrchardSpec.in_psi_old inp) (OrchardSpec.in_cm_old inp).
  Proof. reflexivity. Qed.

  Lemma out_cmx_of_action_spec
      (prm : OrchardSpec.Params) (inp : OrchardSpec.ActionInputs) :
    OrchardSpec.out_cmx
      (OrchardProtocolSpec.orchard_action_spec prm inp) =
    OrchardProtocolSpec.OrchardCmx prm
      (OrchardSpec.in_g_d_new inp) (OrchardSpec.in_pk_d_new inp)
      (OrchardSpec.in_v_new inp)
      (OrchardProtocolSpec.nullifier
        (OrchardSpec.in_nk inp) (OrchardSpec.in_rho_old inp)
        (OrchardSpec.in_psi_old inp) (OrchardSpec.in_cm_old inp))
      (OrchardSpec.in_psi_new inp) (OrchardSpec.in_rcm_new inp).
  Proof. reflexivity. Qed.

  (** ** The new-note lane

      The hashed message of the [Which.New] hash-to-point region, in the
      protocol spelling: the ρ_new argument is the (total, ⊥-free)
      nullifier of the old-note inputs, which is what makes the whole
      commitment a function of [read_action_inputs] alone. *)

  Local Notation new_msg Γ :=
    (OrchardSpec.note_commit_message
      (OrchardSpec.in_g_d_new (read_action_inputs Γ))
      (OrchardSpec.in_pk_d_new (read_action_inputs Γ))
      (OrchardSpec.in_v_new (read_action_inputs Γ))
      (OrchardProtocolSpec.nullifier
        (OrchardSpec.in_nk (read_action_inputs Γ))
        (OrchardSpec.in_rho_old (read_action_inputs Γ))
        (OrchardSpec.in_psi_old (read_action_inputs Γ))
        (OrchardSpec.in_cm_old (read_action_inputs Γ)))
      (OrchardSpec.in_psi_new (read_action_inputs Γ))).

  (** Reader read-offs of the new-note fields (record-literal projections),
      named so the word identification closes on syntactically identical
      terms. *)

  Lemma in_g_d_new_read (Γ : Assignment.t columns RegionId.t) :
    OrchardSpec.in_g_d_new (read_action_inputs Γ) =
    read_point Γ RegionId.NoteCommitNewWitnessGD.
  Proof. reflexivity. Qed.

  Lemma in_pk_d_new_read (Γ : Assignment.t columns RegionId.t) :
    OrchardSpec.in_pk_d_new (read_action_inputs Γ) =
    read_point Γ RegionId.NoteCommitNewWitnessPkD.
  Proof. reflexivity. Qed.

  Lemma in_v_new_read (Γ : Assignment.t columns RegionId.t) :
    OrchardSpec.in_v_new (read_action_inputs Γ) =
    read Γ (RegionId.WitnessInput RegionId.WitnessInput.VNew).
  Proof. reflexivity. Qed.

  Lemma in_psi_new_read (Γ : Assignment.t columns RegionId.t) :
    OrchardSpec.in_psi_new (read_action_inputs Γ) =
    read Γ RegionId.NoteCommitNewWitnessPsi.
  Proof. reflexivity. Qed.

  (** The 109 grid words of the [Which.New] hash-to-point region are the
      protocol's note-commitment message of the read inputs: the word
      identification ([NoteCommitNewWords.note_commit_new_words_correct],
      from acceptance and the short lookups) with the witnessed ρ_new cell
      resolved to the protocol nullifier ([NullifierKOut.nullifier_cell_correct]
      through the record-level composition). *)
  Lemma new_words_protocol
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (Hshort : NoteCommitNewWords.note_commit_new_short_lookup_ok Γ) :
    NoteCommitNewHash.note_commit_new_words Γ = new_msg Γ.
  Proof.
    pose proof
      (NoteCommitNewWords.note_commit_new_words_correct Γ Hcircuit Hshort)
      as Hw.
    cbv zeta in Hw.
    pose proof (NullifierKOut.nullifier_cell_correct Γ Hcircuit) as Hnf.
    cbv zeta in Hnf.
    rewrite (action_spec_protocol Γ Hcircuit) in Hnf.
    rewrite
      (out_nf_old_of_action_spec orchard_circuit_params (read_action_inputs Γ))
      in Hnf.
    rewrite Hnf in Hw.
    rewrite (in_g_d_new_read Γ), (in_pk_d_new_read Γ), (in_v_new_read Γ),
      (in_psi_new_read Γ).
    exact Hw.
  Qed.

  (** The nondegeneracy of the ⊥-carrying fold over the protocol message is
      the nondegeneracy the [Which.New] hash theorem asks for. *)
  Lemma new_nondegenerate_transport
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (Hshort : NoteCommitNewWords.note_commit_new_short_lookup_ok Γ)
      (Hnd :
        SinsemillaHash.nondegenerate
          (OrchardSpec.note_commit_q orchard_circuit_params) (new_msg Γ)) :
    SinsemillaHash.nondegenerate NoteCommitNewHash.note_commit_Q
      (NoteCommitNewHash.note_commit_new_words Γ).
  Proof.
    rewrite NoteCommitNewHash.note_commit_Q_eq.
    rewrite (new_words_protocol Γ Hcircuit Hshort).
    exact Hnd.
  Qed.

  (** The tracking branch of 'New note commitment integrity': where the
      ⊥-carrying fold is defined, the protocol's new-note commitment
      x-coordinate is the public [CMX] row. *)
  (* The two record steps below are taken by [rewrite] inside the
     hypothesis, not by an [f_equal] on the projection:
     [OrchardSpec.out_cmx] is a primitive projection, so
     [f_equal OrchardSpec.out_cmx Hspec] hands unification a [Proj] node
     against a projection application and it falls back to normalizing the
     shared [orchard_action_spec] argument — the 109-step Sinsemilla fold
     ([docs/compile-performance.md], "Never normalize Poseidon round
     chains" / "Never hand unification sides that differ under a big
     fold").  Rewriting leaves the fold untouched. *)
  Lemma cmx_spec_value
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (Hshort : NoteCommitNewWords.note_commit_new_short_lookup_ok Γ)
      (Hnd :
        SinsemillaHash.nondegenerate
          (OrchardSpec.note_commit_q orchard_circuit_params) (new_msg Γ)) :
    OrchardProtocolSpec.OrchardCmx orchard_circuit_params
      (OrchardSpec.in_g_d_new (read_action_inputs Γ))
      (OrchardSpec.in_pk_d_new (read_action_inputs Γ))
      (OrchardSpec.in_v_new (read_action_inputs Γ))
      (OrchardProtocolSpec.nullifier
        (OrchardSpec.in_nk (read_action_inputs Γ))
        (OrchardSpec.in_rho_old (read_action_inputs Γ))
        (OrchardSpec.in_psi_old (read_action_inputs Γ))
        (OrchardSpec.in_cm_old (read_action_inputs Γ)))
      (OrchardSpec.in_psi_new (read_action_inputs Γ))
      (OrchardSpec.in_rcm_new (read_action_inputs Γ)) =
    read_public_instance Γ Garden.Orchard.circuit.CMX.
  Proof.
    pose proof (NoteCommitNewCmx.cmx_correct Γ Hcircuit
      (new_nondegenerate_transport Γ Hcircuit Hshort Hnd) Hshort) as Hcmx.
    rewrite (action_spec_protocol Γ Hcircuit) in Hcmx.
    rewrite
      (out_cmx_of_action_spec orchard_circuit_params (read_action_inputs Γ))
      in Hcmx.
    exact (eq_sym Hcmx).
  Qed.

  (** §4.18.4 'New note commitment integrity', adversarial reading:
      [Extract⊥_P(NoteCommit^Orchard_rcm_new(…)) ∈ {cm_x, ⊥}], from
      acceptance and the new-note short-lookup ranges alone.  The ⊥
      disjunct is the concrete statement that the witnessed 109-word
      message drives the [SinsemillaHashToPoint] fold into an exceptional
      incomplete addition (§5.4.1.9), never a trivial branch. *)
  Theorem cmx_obligation_of_holds
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (Hshort : NoteCommitNewWords.note_commit_new_short_lookup_ok Γ) :
    cmx_obligation Γ.
  Proof.
    unfold cmx_obligation, cmx_bot_of_inputs.
    destruct (sinsemilla_hash_to_point_bot
      (OrchardSpec.note_commit_q orchard_circuit_params) (new_msg Γ))
      as [M |] eqn:Efold.
    - right.
      assert (Hnd :
        SinsemillaHash.nondegenerate
          (OrchardSpec.note_commit_q orchard_circuit_params) (new_msg Γ)).
      { apply (proj1 (hash_to_point_bot_iff _ _)).
        rewrite Efold. discriminate. }
      rewrite (OrchardCmx_bot_some orchard_circuit_params
        (OrchardSpec.in_g_d_new (read_action_inputs Γ))
        (OrchardSpec.in_pk_d_new (read_action_inputs Γ))
        (OrchardSpec.in_v_new (read_action_inputs Γ))
        (OrchardProtocolSpec.nullifier
          (OrchardSpec.in_nk (read_action_inputs Γ))
          (OrchardSpec.in_rho_old (read_action_inputs Γ))
          (OrchardSpec.in_psi_old (read_action_inputs Γ))
          (OrchardSpec.in_cm_old (read_action_inputs Γ)))
        (OrchardSpec.in_psi_new (read_action_inputs Γ))
        (OrchardSpec.in_rcm_new (read_action_inputs Γ)) Hnd).
      exact (f_equal Some (cmx_spec_value Γ Hcircuit Hshort Hnd)).
    - left.
      unfold OrchardCmx_bot, note_commit_bot.
      rewrite Efold.
      reflexivity.
  Qed.

  (** ** The old-note lane

      The hashed message of the [Which.Old] hash-to-point region, in the
      protocol spelling.  [pk_d_old] and [rcm_old] are ownership-track
      witnesses ([OrchardValidActionInputs] readers), not fields of
      [read_action_inputs]: no public output depends on them. *)

  Local Notation old_msg Γ :=
    (OrchardSpec.note_commit_message
      (OrchardSpec.in_g_d_old (read_action_inputs Γ))
      (OrchardValidActionInputs.read_pk_d_old Γ)
      (OrchardSpec.in_v_old (read_action_inputs Γ))
      (OrchardSpec.in_rho_old (read_action_inputs Γ))
      (OrchardSpec.in_psi_old (read_action_inputs Γ))).

  Lemma old_note_words_eq (Γ : Assignment.t columns RegionId.t) :
    OrchardValidActionInputs.old_note_words Γ = OldNoteWords.old_note_words Γ.
  Proof. reflexivity. Qed.

  Lemma read_pk_d_old_eq (Γ : Assignment.t columns RegionId.t) :
    OrchardValidActionInputs.read_pk_d_old Γ =
    read_point Γ
      (RegionId.AddressIntegrity RegionId.AddressIntegrity.WitnessPkD).
  Proof. reflexivity. Qed.

  (** The 109 grid words of the [Which.Old] hash-to-point region are the
      protocol's note-commitment message of the witnessed old-note fields
      ([OldNoteWords.note_commit_old_words_correct], from acceptance and
      the old-note short lookups). *)
  Lemma old_words_protocol
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (Hshort : OldNoteWords.old_note_short_lookup_ok Γ) :
    OrchardValidActionInputs.old_note_words Γ = old_msg Γ.
  Proof.
    rewrite (old_note_words_eq Γ).
    rewrite (OldNoteWords.note_commit_old_words_correct Γ Hcircuit Hshort).
    rewrite (OldNoteOpen.in_g_d_old_read Γ), (read_pk_d_old_eq Γ),
      (OldNoteOpen.in_v_old_read Γ), (OldNoteOpen.in_rho_old_read Γ),
      (OldNoteOpen.in_psi_old_read Γ).
    reflexivity.
  Qed.

  (** The tracking branch of 'Old note commitment integrity': where the
      ⊥-carrying fold is defined, the witnessed old-note fields open the
      witnessed [cm^old]. *)
  Lemma old_note_spec_value
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (Hshort : OldNoteWords.old_note_short_lookup_ok Γ)
      (Hnd :
        SinsemillaHash.nondegenerate
          (OrchardSpec.note_commit_q orchard_circuit_params) (old_msg Γ)) :
    OrchardProtocolSpec.note_commit orchard_circuit_params
      (OrchardSpec.in_g_d_old (read_action_inputs Γ))
      (OrchardValidActionInputs.read_pk_d_old Γ)
      (OrchardSpec.in_v_old (read_action_inputs Γ))
      (OrchardSpec.in_rho_old (read_action_inputs Γ))
      (OrchardSpec.in_psi_old (read_action_inputs Γ))
      (OrchardValidActionInputs.read_rcm_old Γ) =
    OrchardSpec.in_cm_old (read_action_inputs Γ).
  Proof.
    refine (OrchardValidActionInputs.old_note_commit_integrity Γ Hcircuit
      (conj _ Hshort)).
    rewrite (old_words_protocol Γ Hcircuit Hshort).
    exact Hnd.
  Qed.

  (** §4.18.4 'Old note commitment integrity', adversarial reading:
      [NoteCommit^Orchard_rcm_old(…) ∈ {cm^old, ⊥}], from acceptance and
      the old-note short-lookup ranges alone. *)
  Theorem old_note_obligation_of_holds
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (Hshort : OldNoteWords.old_note_short_lookup_ok Γ) :
    old_note_obligation Γ.
  Proof.
    unfold old_note_obligation, old_note_bot_of.
    destruct (sinsemilla_hash_to_point_bot
      (OrchardSpec.note_commit_q orchard_circuit_params) (old_msg Γ))
      as [M |] eqn:Efold.
    - right.
      assert (Hnd :
        SinsemillaHash.nondegenerate
          (OrchardSpec.note_commit_q orchard_circuit_params) (old_msg Γ)).
      { apply (proj1 (hash_to_point_bot_iff _ _)).
        rewrite Efold. discriminate. }
      rewrite (note_commit_bot_some orchard_circuit_params
        (OrchardSpec.in_g_d_old (read_action_inputs Γ))
        (OrchardValidActionInputs.read_pk_d_old Γ)
        (OrchardSpec.in_v_old (read_action_inputs Γ))
        (OrchardSpec.in_rho_old (read_action_inputs Γ))
        (OrchardSpec.in_psi_old (read_action_inputs Γ))
        (OrchardValidActionInputs.read_rcm_old Γ) Hnd).
      exact (f_equal Some (old_note_spec_value Γ Hcircuit Hshort Hnd)).
    - left.
      unfold note_commit_bot.
      rewrite Efold.
      reflexivity.
  Qed.

End OrchardNoteCommitBot.
