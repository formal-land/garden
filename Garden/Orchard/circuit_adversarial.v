(** * The Action statement at the acceptance levels: conditional and
      adversarial

    [orchard_action_statement_operational] ([circuit_operational.v]) and
    [orchard_algebraic_action_statement] ([compiled/algebraic.v]) carry the
    §4.18.4 Action statement from acceptance of the pinned Orchard circuit,
    conditioned on four witness-honesty packages.  Three of those packages
    split into a nondegeneracy conjunct and a short-lookup range conjunct
    ([note_commit/cmx.v], [valid_action_inputs.v]).  The short-lookup
    conjuncts are model artifacts rather than real assumptions: the
    deployed circuit enforces them through its range-check lookup argument,
    and only the relational selector model leaves them free
    ([docs/chip-model-caveats.md]).  They are discharged against the pinned
    circuit in [circuit_proof/lookup_closure.v],
    [circuit_proof/lookup_closure_old_note.v] and
    [circuit_proof/lookup_closure_ivk.v].

    The first half of the file restates the two acceptance-level Action
    statements with those conjuncts discharged.  The residual hypotheses
    are exactly the Sinsemilla incomplete-add nondegeneracy of the three
    hashed message folds and the Merkle package, one predicate per package
    ([note_commit_nondegenerate], [old_note_nondegenerate],
    [commit_ivk_nondegenerate]).  The variable-base mul chip's
    nondegeneracy is not among them: §4.18.4 grants the
    multiplication of 'Diversified address integrity' no exceptional
    escape, and [OrchardOwnershipBot.mul_nondegenerate_of_holds]
    ([circuit_proof/ownership_bot.v]) derives it from the gates.

    The second half is the adversarial statement — the §4.18.4 clauses in
    the disjunctive form the protocol states them, with the exceptional
    branches as disjuncts of the conclusion rather than as hypotheses
    ([circuit_proof/adversarial.v]).  At the acceptance levels every
    remaining side condition of that statement is a short-lookup range
    family, so the closure files discharge them all: the only surviving
    premise is [OrchardAdversarialApi.WellTypedInstance], the typing of the
    decoded primary input that transaction decoding and consensus enforce.
    The determinism corollary is likewise conditioned on the inputs alone.

    The heavy certificate files are consumed read-only. *)

Require Import Stdlib.Lists.List.
Require Import Stdlib.ZArith.ZArith.
Require Import Garden.Halo2.main.
Require Import Garden.Halo2.Synthesis.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.serialize.
Require Import Garden.Halo2.realize.main.
Require Import Garden.Halo2.realize.sound.
Require Import Garden.Halo2.plonkish.poly.
Require Import Garden.Halo2.halo2_gadgets.sinsemilla.hash_to_point_proof.
Require Import Garden.Orchard.columns.
Require Import Garden.Orchard.circuit_synthesis_layout.
Require Import Garden.Orchard.protocol_spec.
Require Import Garden.Orchard.circuit_proof.inputs.
Require Import Garden.Orchard.circuit_proof.merkle.
Require Import Garden.Orchard.circuit_proof.note_commit.hash.
Require Import Garden.Orchard.circuit_proof.note_commit.cmx.
Require Import Garden.Orchard.circuit_proof.ownership.var_base_mul.
Require Import Garden.Orchard.circuit_proof.valid_action_inputs.
Require Import Garden.Orchard.circuit_proof.lookup_closure.
Require Import Garden.Orchard.circuit_proof.lookup_closure_old_note.
Require Import Garden.Orchard.circuit_proof.lookup_closure_ivk.
Require Import Garden.Orchard.circuit_proof.note_commit.words.
Require Import Garden.Orchard.circuit_proof.old_note.words.
Require Import Garden.Orchard.circuit_proof.ownership.commit_ivk_hash.
Require Import Garden.Orchard.circuit_proof.protocol_spec_bot.
Require Import Garden.Orchard.circuit_proof.adversarial_api.
Require Import Garden.Orchard.circuit_proof.merkle_bot.
Require Import Garden.Orchard.circuit_proof.ownership_bot.
Require Import Garden.Orchard.circuit_proof.adversarial.
Require Import Garden.Orchard.circuit_operational.
Require Import Garden.Orchard.compiled.algebraic.
Require Import Garden.Field.Field.
Require Import Garden.Plonky3.M.

Import ListNotations.

#[local] Existing Instance Primes.PallasPIsPrime.

Module OrchardAdversarialAction.
  Import OrchardActionInputs.

  (** ** The residual witness-honesty conditions, one per package

      Each is the witness-honesty package of
      [circuit_proof/valid_action_inputs.v] and
      [circuit_proof/note_commit/cmx.v] with its short-lookup conjunct
      removed.  The Merkle package is carried whole: its
      [merkle_layer_canonical] conjunct bounds wrapped 255-bit
      reconstructions, which no acceptance level derives — the deployed
      decomposition gate checks the sum modulo the field prime only
      ([circuit_proof/merkle.v]). *)

  (** Sinsemilla nondegeneracy of the 109-word new-note commitment fold. *)
  Definition note_commit_nondegenerate
      (Γ : Assignment.t columns RegionId.t) : Prop :=
    SinsemillaHash.nondegenerate NoteCommitNewHash.note_commit_Q
      (NoteCommitNewHash.note_commit_new_words Γ).

  (** Sinsemilla nondegeneracy of the 109-word old-note commitment fold. *)
  Definition old_note_nondegenerate
      (Γ : Assignment.t columns RegionId.t) : Prop :=
    SinsemillaHash.nondegenerate
      (OrchardSpec.note_commit_q orchard_circuit_params)
      (OrchardValidActionInputs.old_note_words Γ).

  (** Sinsemilla nondegeneracy of the 51-word [Commit^ivk] fold — the only
      chip-level exceptional-case condition of the ownership lane.  The
      variable-base mul chip's incomplete-addition nondegeneracy is not
      part of the residue: §4.18.4's 'Diversified address integrity' gives
      ⊥ to the [Commit^ivk] fold alone and requires the [ivk]
      decomposition to be canonical, so the multiplication must hold
      exactly; [OrchardOwnershipBot.mul_nondegenerate_of_holds] derives the
      chip condition from the gates. *)
  Definition commit_ivk_nondegenerate
      (Γ : Assignment.t columns RegionId.t) : Prop :=
    SinsemillaHash.nondegenerate
      (OrchardSpec.commit_ivk_q orchard_circuit_params)
      (OrchardValidActionInputs.commit_ivk_words Γ).

  (** ** Reassembling the packages from operational acceptance

      Each package is its residue paired with the short-lookup family the
      closure files derive from replay success and ideal acceptance. *)

  Lemma note_commit_witness_ok_of_nondegenerate
      (advice instance_ : Z -> Z -> Z) (grid : RawGrid.t)
      (Hreplay :
        apply_events orchard_events (initial_grid advice instance_) =
          Some grid)
      (Hmock :
        mock_prover_accepts orchard_indexed_system orchard_events grid
          orchard_table_rows)
      (Hnd :
        note_commit_nondegenerate (realize Index.indices region_start_of grid)) :
    NoteCommitNewCmx.note_commit_witness_ok
      (realize Index.indices region_start_of grid).
  Proof.
    exact (conj Hnd
      (OrchardShortLookupClosure.note_commit_new_short_lookup_ok_operational
        advice instance_ grid Hreplay Hmock)).
  Qed.

  Lemma old_note_witness_ok_of_nondegenerate
      (advice instance_ : Z -> Z -> Z) (grid : RawGrid.t)
      (Hreplay :
        apply_events orchard_events (initial_grid advice instance_) =
          Some grid)
      (Hmock :
        mock_prover_accepts orchard_indexed_system orchard_events grid
          orchard_table_rows)
      (Hnd :
        old_note_nondegenerate (realize Index.indices region_start_of grid)) :
    OrchardValidActionInputs.old_note_witness_ok
      (realize Index.indices region_start_of grid).
  Proof.
    exact (conj Hnd
      (OrchardOldNoteLookupClosure.old_note_short_lookup_ok_operational
        advice instance_ grid Hreplay Hmock)).
  Qed.

  Lemma commit_ivk_witness_ok_of_nondegenerate
      (advice instance_ : Z -> Z -> Z) (grid : RawGrid.t)
      (Hreplay :
        apply_events orchard_events (initial_grid advice instance_) =
          Some grid)
      (Hmock :
        mock_prover_accepts orchard_indexed_system orchard_events grid
          orchard_table_rows)
      (Hnd :
        commit_ivk_nondegenerate (realize Index.indices region_start_of grid)) :
    OrchardValidActionInputs.commit_ivk_witness_ok
      (realize Index.indices region_start_of grid).
  Proof.
    exact (OrchardOwnershipBot.commit_ivk_witness_ok_of_nondegenerate
      (realize Index.indices region_start_of grid)
      (orchard_operational_sound advice instance_ grid Hreplay Hmock)
      Hnd
      (OrchardCommitIvkLookupClosure.commit_ivk_short_lookup_ok_operational
        advice instance_ grid Hreplay Hmock)).
  Qed.

  (** ** The Action statement at the ideal operational checker

      [orchard_action_statement_operational] ([circuit_operational.v:543])
      with the three short-lookup conjuncts discharged.  The premises are
      replay success, ideal acceptance, and the four residual honesty
      conditions. *)

  Corollary orchard_action_statement_operational_short_closed
      (advice instance_ : Z -> Z -> Z) (grid : RawGrid.t)
      (Hreplay :
        apply_events orchard_events (initial_grid advice instance_) =
          Some grid)
      (Hmock :
        mock_prover_accepts orchard_indexed_system orchard_events grid
          orchard_table_rows)
      (Hmerkle_ok :
        Garden.Orchard.circuit_proof.merkle.OrchardActionMerkle
          .merkle_witness_ok
          (realize Index.indices region_start_of grid))
      (Hnote_nd :
        note_commit_nondegenerate (realize Index.indices region_start_of grid))
      (Hold_note_nd :
        old_note_nondegenerate (realize Index.indices region_start_of grid))
      (Hivk_nd :
        commit_ivk_nondegenerate (realize Index.indices region_start_of grid)) :
    (Garden.Orchard.circuit_proof.inputs.OrchardActionInputs
        .read_action_outputs
        (realize Index.indices region_start_of grid) =
      Garden.Orchard.protocol_spec.OrchardProtocolSpec.orchard_action_spec
        Garden.Orchard.circuit_proof.inputs.OrchardActionInputs
          .orchard_circuit_params
        (Garden.Orchard.circuit_proof.inputs.OrchardActionInputs
          .read_action_inputs
          (realize Index.indices region_start_of grid))) /\
    Garden.Orchard.circuit_proof.valid_action_inputs.OrchardValidActionInputs
      .ValidActionInputs
      (realize Index.indices region_start_of grid).
  Proof.
    exact (orchard_action_statement_operational advice instance_ grid
      Hreplay Hmock Hmerkle_ok
      (note_commit_witness_ok_of_nondegenerate advice instance_ grid
        Hreplay Hmock Hnote_nd)
      (old_note_witness_ok_of_nondegenerate advice instance_ grid
        Hreplay Hmock Hold_note_nd)
      (commit_ivk_witness_ok_of_nondegenerate advice instance_ grid
        Hreplay Hmock Hivk_nd)).
  Qed.

  (** ** The Action statement at the polynomial-identity layer

      [orchard_algebraic_action_statement] ([compiled/algebraic.v]) with
      the same three conjuncts discharged.  The ideal acceptance the
      closure theorems consume is obtained from the algebraic premises by
      [orchard_algebraic_mock_accepts], so this corollary's premises are
      those of the algebraic statement, minus the short lookups. *)

  Corollary orchard_algebraic_action_statement_short_closed
      (advice instance_ : Z -> Z -> Z) (grid : RawGrid.t) (Es : list Poly.t)
      (Hreplay :
        apply_events orchard_events (initial_grid advice instance_) =
          Some grid)
      (Hcanon : OrchardCompiledAlgebraic.orchard_perm_values_canonical grid)
      (Haccepts : OrchardCompiledAlgebraic.orchard_algebraic_accepts grid Es)
      (Hmerkle_ok :
        Garden.Orchard.circuit_proof.merkle.OrchardActionMerkle
          .merkle_witness_ok
          (realize Index.indices region_start_of grid))
      (Hnote_nd :
        note_commit_nondegenerate (realize Index.indices region_start_of grid))
      (Hold_note_nd :
        old_note_nondegenerate (realize Index.indices region_start_of grid))
      (Hivk_nd :
        commit_ivk_nondegenerate (realize Index.indices region_start_of grid)) :
    (Garden.Orchard.circuit_proof.inputs.OrchardActionInputs
        .read_action_outputs
        (realize Index.indices region_start_of grid) =
      Garden.Orchard.protocol_spec.OrchardProtocolSpec.orchard_action_spec
        Garden.Orchard.circuit_proof.inputs.OrchardActionInputs
          .orchard_circuit_params
        (Garden.Orchard.circuit_proof.inputs.OrchardActionInputs
          .read_action_inputs
          (realize Index.indices region_start_of grid))) /\
    Garden.Orchard.circuit_proof.valid_action_inputs.OrchardValidActionInputs
      .ValidActionInputs
      (realize Index.indices region_start_of grid).
  Proof.
    pose proof (OrchardCompiledAlgebraic.orchard_algebraic_mock_accepts advice instance_ grid Es
      Hreplay Hcanon Haccepts) as Hmock.
    exact (OrchardCompiledAlgebraic.orchard_algebraic_action_statement advice instance_ grid Es
      Hreplay Hcanon Haccepts Hmerkle_ok
      (note_commit_witness_ok_of_nondegenerate advice instance_ grid
        Hreplay Hmock Hnote_nd)
      (old_note_witness_ok_of_nondegenerate advice instance_ grid
        Hreplay Hmock Hold_note_nd)
      (commit_ivk_witness_ok_of_nondegenerate advice instance_ grid
        Hreplay Hmock Hivk_nd)).
  Qed.

  (** ** The adversarial Action statement at the acceptance levels

      [OrchardAdversarial.action_statement_adversarial]
      ([circuit_proof/adversarial.v]) states the §4.18.4 clause set with
      the protocol's own ⊥ disjunctions in the conclusion, so no
      nondegeneracy, canonicity or Merkle hypothesis appears.  Its four
      remaining side conditions are short-lookup range families of the
      relational selector model, and all four are discharged here from
      acceptance of the pinned circuit: the three note/ownership families
      by the closure files, the 64 Merkle [b_1]/[b_2] sites by
      [OrchardMerkleBot.merkle_b_range_ok_operational].

      What is left is [OrchardAdversarialApi.WellTypedInstance] alone —
      Boolean [enableSpends]/[enableOutputs], the consensus rule
      [rk ≠ 𝒪_P] (§4.6), and the reducedness of the decoded instance
      rows. *)

  Corollary orchard_action_statement_adversarial_operational
      (advice instance_ : Z -> Z -> Z) (grid : RawGrid.t)
      (Hreplay :
        apply_events orchard_events (initial_grid advice instance_) =
          Some grid)
      (Hmock :
        mock_prover_accepts orchard_indexed_system orchard_events grid
          orchard_table_rows)
      (Hwti :
        OrchardAdversarialApi.WellTypedInstance
          (realize Index.indices region_start_of grid)) :
    OrchardAdversarialApi.adversarial_action_conclusion
      (realize Index.indices region_start_of grid).
  Proof.
    exact (OrchardAdversarial.action_statement_adversarial
      (realize Index.indices region_start_of grid)
      (orchard_operational_sound advice instance_ grid Hreplay Hmock)
      Hwti
      (OrchardShortLookupClosure.note_commit_new_short_lookup_ok_operational
        advice instance_ grid Hreplay Hmock)
      (OrchardOldNoteLookupClosure.old_note_short_lookup_ok_operational
        advice instance_ grid Hreplay Hmock)
      (OrchardCommitIvkLookupClosure.commit_ivk_short_lookup_ok_operational
        advice instance_ grid Hreplay Hmock)
      (OrchardMerkleBot.merkle_b_range_ok_operational
        advice instance_ grid Hreplay Hmock)).
  Qed.

  (** The same statement at the polynomial-identity layer: the ideal
      acceptance the closure theorems consume is produced from the
      algebraic premises by [orchard_algebraic_mock_accepts]. *)

  Corollary orchard_action_statement_adversarial_algebraic
      (advice instance_ : Z -> Z -> Z) (grid : RawGrid.t) (Es : list Poly.t)
      (Hreplay :
        apply_events orchard_events (initial_grid advice instance_) =
          Some grid)
      (Hcanon : OrchardCompiledAlgebraic.orchard_perm_values_canonical grid)
      (Haccepts : OrchardCompiledAlgebraic.orchard_algebraic_accepts grid Es)
      (Hwti :
        OrchardAdversarialApi.WellTypedInstance
          (realize Index.indices region_start_of grid)) :
    OrchardAdversarialApi.adversarial_action_conclusion
      (realize Index.indices region_start_of grid).
  Proof.
    exact (orchard_action_statement_adversarial_operational advice instance_
      grid Hreplay
      (OrchardCompiledAlgebraic.orchard_algebraic_mock_accepts
        advice instance_ grid Es Hreplay Hcanon Haccepts)
      Hwti).
  Qed.

  (** ** Determinism conditioned on the inputs alone, at the acceptance
         levels

      Two accepted assignments agreeing on [read_action_inputs], on which
      the ⊥-carrying new-note commitment of those inputs is defined, agree
      on every public output row.  Both premises are properties of the
      input record: no witness-honesty condition survives. *)

  Corollary orchard_deterministic_adversarial_operational
      (advice1 instance1 advice2 instance2 : Z -> Z -> Z)
      (grid1 grid2 : RawGrid.t)
      (Hreplay1 :
        apply_events orchard_events (initial_grid advice1 instance1) =
          Some grid1)
      (Hmock1 :
        mock_prover_accepts orchard_indexed_system orchard_events grid1
          orchard_table_rows)
      (Hreplay2 :
        apply_events orchard_events (initial_grid advice2 instance2) =
          Some grid2)
      (Hmock2 :
        mock_prover_accepts orchard_indexed_system orchard_events grid2
          orchard_table_rows)
      (Hinputs :
        read_action_inputs (realize Index.indices region_start_of grid1) =
        read_action_inputs (realize Index.indices region_start_of grid2))
      (Hdef :
        OrchardAdversarialApi.cmx_bot_of_inputs orchard_circuit_params
          (read_action_inputs (realize Index.indices region_start_of grid1))
          <> None) :
    forall row : Z,
      row = Garden.Orchard.circuit.ANCHOR \/
      row = Garden.Orchard.circuit.CV_NET_X \/
      row = Garden.Orchard.circuit.CV_NET_Y \/
      row = Garden.Orchard.circuit.NF_OLD \/
      row = Garden.Orchard.circuit.RK_X \/
      row = Garden.Orchard.circuit.RK_Y \/
      row = Garden.Orchard.circuit.CMX ->
      read_public_instance (realize Index.indices region_start_of grid1) row =
      read_public_instance (realize Index.indices region_start_of grid2) row.
  Proof.
    exact (OrchardAdversarial.deterministic_adversarial
      (realize Index.indices region_start_of grid1)
      (realize Index.indices region_start_of grid2)
      (orchard_operational_sound advice1 instance1 grid1 Hreplay1 Hmock1)
      (orchard_operational_sound advice2 instance2 grid2 Hreplay2 Hmock2)
      (OrchardShortLookupClosure.note_commit_new_short_lookup_ok_operational
        advice1 instance1 grid1 Hreplay1 Hmock1)
      (OrchardShortLookupClosure.note_commit_new_short_lookup_ok_operational
        advice2 instance2 grid2 Hreplay2 Hmock2)
      Hinputs Hdef).
  Qed.

  Corollary orchard_deterministic_adversarial_algebraic
      (advice1 instance1 advice2 instance2 : Z -> Z -> Z)
      (grid1 grid2 : RawGrid.t) (Es1 Es2 : list Poly.t)
      (Hreplay1 :
        apply_events orchard_events (initial_grid advice1 instance1) =
          Some grid1)
      (Hcanon1 : OrchardCompiledAlgebraic.orchard_perm_values_canonical grid1)
      (Haccepts1 :
        OrchardCompiledAlgebraic.orchard_algebraic_accepts grid1 Es1)
      (Hreplay2 :
        apply_events orchard_events (initial_grid advice2 instance2) =
          Some grid2)
      (Hcanon2 : OrchardCompiledAlgebraic.orchard_perm_values_canonical grid2)
      (Haccepts2 :
        OrchardCompiledAlgebraic.orchard_algebraic_accepts grid2 Es2)
      (Hinputs :
        read_action_inputs (realize Index.indices region_start_of grid1) =
        read_action_inputs (realize Index.indices region_start_of grid2))
      (Hdef :
        OrchardAdversarialApi.cmx_bot_of_inputs orchard_circuit_params
          (read_action_inputs (realize Index.indices region_start_of grid1))
          <> None) :
    forall row : Z,
      row = Garden.Orchard.circuit.ANCHOR \/
      row = Garden.Orchard.circuit.CV_NET_X \/
      row = Garden.Orchard.circuit.CV_NET_Y \/
      row = Garden.Orchard.circuit.NF_OLD \/
      row = Garden.Orchard.circuit.RK_X \/
      row = Garden.Orchard.circuit.RK_Y \/
      row = Garden.Orchard.circuit.CMX ->
      read_public_instance (realize Index.indices region_start_of grid1) row =
      read_public_instance (realize Index.indices region_start_of grid2) row.
  Proof.
    exact (orchard_deterministic_adversarial_operational
      advice1 instance1 advice2 instance2 grid1 grid2 Hreplay1
      (OrchardCompiledAlgebraic.orchard_algebraic_mock_accepts
        advice1 instance1 grid1 Es1 Hreplay1 Hcanon1 Haccepts1)
      Hreplay2
      (OrchardCompiledAlgebraic.orchard_algebraic_mock_accepts
        advice2 instance2 grid2 Es2 Hreplay2 Hcanon2 Haccepts2)
      Hinputs Hdef).
  Qed.

  (** ** The operational bundle package

      [OrchardBundleSpec.action_ok] ([bundle/spec.v]) is circuit
      satisfaction plus the two short-lookup families the per-action
      balance fact needs; both are discharged from acceptance of the
      pinned circuit, so an accepted action satisfies the package
      outright.  Stated here rather than under
      [bundle/] so that the bundle layer keeps its lean dependency
      closure. *)

  Corollary action_ok_operational
      (advice instance_ : Z -> Z -> Z) (grid : RawGrid.t)
      (Hreplay :
        apply_events orchard_events (initial_grid advice instance_) =
          Some grid)
      (Hmock :
        mock_prover_accepts orchard_indexed_system orchard_events grid
          orchard_table_rows) :
    circuit_holds (realize Index.indices region_start_of grid)
      Garden.Orchard.circuit.synthesize
      (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty) /\
    NoteCommitNewWords.note_commit_new_short_lookup_ok
      (realize Index.indices region_start_of grid) /\
    OldNoteWords.old_note_short_lookup_ok
      (realize Index.indices region_start_of grid).
  Proof.
    exact (conj (orchard_operational_sound advice instance_ grid Hreplay Hmock)
      (conj
        (OrchardShortLookupClosure.note_commit_new_short_lookup_ok_operational
          advice instance_ grid Hreplay Hmock)
        (OrchardOldNoteLookupClosure.old_note_short_lookup_ok_operational
          advice instance_ grid Hreplay Hmock))).
  Qed.
End OrchardAdversarialAction.
