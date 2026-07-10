Require Import Garden.Halo2.main.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.lemmas.
Require Import Garden.Orchard.columns.
Require Garden.Orchard.circuit.
Require Import Garden.Orchard.circuit.gadget.add_chip_proof.
Require Garden.Orchard.circuit.note_commit.
Require Garden.Orchard.circuit.commit_ivk.
Require Garden.Orchard.constants.fixed_bases.spend_auth_g.
Require Garden.Orchard.constants.fixed_bases.value_commit_v.
Require Garden.Orchard.constants.fixed_bases.value_commit_r.
Require Garden.Orchard.constants.fixed_bases.nullifier_k.
Require Garden.Orchard.constants.fixed_bases.note_commit_r.
Require Garden.Orchard.constants.fixed_bases.commit_ivk_r.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.spec.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.mul_fixed_proof.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.mul_fixed.full_width_proof.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.witness_point_proof.
Require Import Garden.Halo2.halo2_gadgets.poseidon.spec.
Require Import Garden.Orchard.protocol_spec.
Require Import Garden.Orchard.circuit_proof.internal_spec.
Require Import Garden.Orchard.circuit_proof.inputs.
Require Import Garden.Orchard.circuit_proof.bridges.
Require Import Garden.Orchard.circuit_proof.ladder.main.
Require Import Garden.Orchard.circuit_proof.merkle.
Require Import Garden.Orchard.circuit_proof.value_commit_v.out.
Require Import Garden.Orchard.circuit_proof.value_commit_r.out.
Require Import Garden.Orchard.circuit_proof.us_free.nullifier_k.
Require Import Garden.Orchard.circuit_proof.nullifier_k.out.
Require Import Garden.Orchard.circuit_proof.note_commit.cmx.
Require Import Garden.Orchard.circuit_proof.protocol_equiv.
Require Import Garden.Orchard.circuit_proof.valid_action_inputs.
Require Import Garden.Field.Field.
Require Import Garden.Field.Div.
Require Import Garden.Field.Lemmas.
Require Import Garden.Plonky3.M.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Lists.List.
Require Import Stdlib.setoid_ring.Ring.

#[local] Existing Instance Primes.PallasPIsPrime.

Global Open Scope Z_scope.

(** * The Orchard action theorem surface

    The two public theorems about the whole Orchard action circuit, both
    against the protocol-aligned specification [OrchardProtocolSpec]
    ([Orchard/protocol_spec.v]):

    - [OrchardAction.satisfies_specification] — functional correctness: the
      seven public outputs of a satisfying assignment equal the §4.18.4
      output functions (group multiples of the real-coordinate Zcash
      generators) applied to the genuine inputs read from the assignment.
    - [OrchardAction.deterministic] — determinism, derived as a corollary:
      two satisfying assignments agreeing on the genuine inputs agree on
      every public output row.

    Proof structure: the seven per-output bridge lemmas land on the
    circuit-structured layer ([OrchardCircuitSpec]), and
    [OrchardProtocolEquiv.output_protocol_eq]
    ([circuit_proof/protocol_equiv.v]) carries that layer onto the protocol
    specification — both composed inside [satisfies_specification]. *)

Module OrchardCircuitChecks.
  Record t : Set := {
    v_old : Z;
  }.

  Definition output {p : Z} `{Prime p}
      (v_new magnitude sign : Z)
      : t := {|
    v_old := v_new +F magnitude *F sign;
  |}.
End OrchardCircuitChecks.

Module OrchardAction.
  Include OrchardActionBridges.

  Local Notation Holds Γ :=
    (circuit_holds Γ
      Garden.Orchard.circuit.synthesize
      (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)).

  (* ** Per-output bridges

     [satisfies_specification] decomposes, output by output, into seven equalities between
     an evaluated public [Instance_] expression and the corresponding component of
     [action_spec_of Γ].  These are the per-output functional theorems
     (the [ANCHOR] / [CV_NET] / [NF_OLD] / [RK] / [CMX]
     rows), each the shape of a chip [synthesize_correct] but for a whole
     sub-gadget of [circuit.synthesize].

     Each follows the same route: from [Holds Γ] one extracts the
     [ConstrainInstance] fact pinning the row to the gadget's output cell, then
     propagates determination back along the [Copy] graph through the gadget's
     gates — composing the per-chip [synthesize_correct] / [deterministic]
     results (Poseidon rounds, the windowed [FullWidthFixedBaseScalarMul] /
     [RunningSumCoordinatesCheck], Sinsemilla rounds + [GeneratorTable.sound],
     [CompleteAddition]) into the crypto function.  All seven are closed this
     way: [anchor_correct] (under the [merkle_witness_ok] side condition),
     [cv_net_x_correct] / [cv_net_y_correct], [nf_old_correct],
     [rk_x_correct] / [rk_y_correct], and [cmx_correct] (under the
     [note_commit_witness_ok] side condition). *)
  (* The dummy-spend branch ([v_old = 0]) is content-free: the spec's
     [out_anchor] returns [in_anchor_public], which [read_action_inputs] reads
     from the same [ANCHOR] public row this equates it with.  The equality thus
     holds by construction and asserts nothing about the anchor — matching the
     gate, which imposes no [root = anchor] link when [v_old = 0].  The genuine
     anchor content lives entirely in the [v_old <> 0] case ([anchor_correct]). *)
  Lemma anchor_correct_disabled
      (Γ : Assignment.t columns RegionId.t)
      (Hvold :
        read Γ (RegionId.WitnessInput RegionId.WitnessInput.VOld) = 0) :
    read_public_instance Γ Garden.Orchard.circuit.ANCHOR =
      OrchardSpec.out_anchor (action_spec_of Γ).
  Proof.
    unfold action_spec_of, output_with_witness, read_action_inputs,
      read_action_inputs_with_anchor.
    cbn [OrchardSpec.out_anchor OrchardCircuitSpec.orchard_action_spec
      OrchardSpec.in_v_old OrchardSpec.in_anchor_public].
    rewrite Hvold, Z.eqb_refl.
    reflexivity.
  Qed.

  (* ANCHOR: the [v_old <> 0] branch reduces by [anchor_correct_of_merkle_root]
     to the synthesized Merkle-root output cell, which
     [OrchardActionMerkle.merkle_root_cell_correct] evaluates to
     [OrchardSpec.anchor] of the [CmOld] read and the [merkle_path_of] reads.

     The [merkle_witness_ok] hypothesis is the per-layer
     canonicity/nondegeneracy side condition of the Merkle decomposition
     witnesses: each layer's decomposition gate checks its three
     reconstruction identities mod [p] only, and the 255-bit packings cross
     the field size, so a wrapped (non-canonical) witness satisfies the gate
     while hashing a different 52-word message — the unconditional statement
     is refutable (see [merkle_layer_canonical] in [circuit_proof/merkle.v]).
     The hypothesis is threaded through [satisfies_specification] /
     [deterministic] as a documented witness-honesty side
     condition. *)
  Lemma anchor_correct (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ)
      (Hmerkle_ok : OrchardActionMerkle.merkle_witness_ok Γ) :
    read_public_instance Γ Garden.Orchard.circuit.ANCHOR =
      OrchardSpec.out_anchor (action_spec_of Γ).
  Proof.
    apply (anchor_correct_of_merkle_root Γ Hcircuit).
    exact (OrchardActionMerkle.merkle_root_cell_correct Γ Hcircuit Hmerkle_ok).
  Qed.

  (* CV_NET: the complete-add bridge splits the commitment into the short
     magnitude/sign leg ([Hvalue], closed by
     [ValueCommitVOut.value_commit_v_hvalue]) and the 85-window blinding leg
     ([Hblind], closed by [ValueCommitROut.value_commit_r_hblind]), both from
     [Holds] alone. *)
  Lemma cv_net_x_correct (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ) :
    read_public_instance Γ Garden.Orchard.circuit.CV_NET_X =
      Point.x (OrchardSpec.out_cv_net (action_spec_of Γ)).
  Proof.
    exact (cv_net_x_correct_of_fixed_base Γ Hcircuit
      (ValueCommitVOut.value_commit_v_hvalue Γ Hcircuit)
      (ValueCommitROut.value_commit_r_hblind Γ Hcircuit)).
  Qed.

  Lemma cv_net_y_correct (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ) :
    read_public_instance Γ Garden.Orchard.circuit.CV_NET_Y =
      Point.y (OrchardSpec.out_cv_net (action_spec_of Γ)).
  Proof.
    exact (cv_net_y_correct_of_fixed_base Γ Hcircuit
      (ValueCommitVOut.value_commit_v_hvalue Γ Hcircuit)
      (ValueCommitROut.value_commit_r_hblind Γ Hcircuit)).
  Qed.

  (* NF_OLD: the [nf_old_correct_of_fixed_base] bridge with both hypotheses
     ([Hfixed], the nullifier_k base-field fixed-base ladder output, and
     [Hcomm_x], the x-coordinate commutation of the [cm_old] complete add)
     closed from [Holds] in [circuit_proof/nullifier_k/out.v]. *)
  Lemma nf_old_correct (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ) :
    read_public_instance Γ Garden.Orchard.circuit.NF_OLD =
      OrchardSpec.out_nf_old (action_spec_of Γ).
  Proof.
    exact (NullifierKOut.nf_old_correct_of_holds Γ Hcircuit).
  Qed.

  (* RK_X: the uniform prime-order-subgroup ladder argument — the full 83-edge
     SpendAuthG ladder distinctness
     [FixedBaseLadder.spend_auth_g_distinct_holds] (from
     the group law, full per-window correctness, and the window range
     bounds) fed into the bridge wrapper
     [rk_x_correct_of_spend_auth_g_ladder_distinct]. *)
  Lemma rk_x_correct (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ) :
    read_public_instance Γ Garden.Orchard.circuit.RK_X =
      Point.x (OrchardSpec.out_rk (action_spec_of Γ)).
  Proof.
    apply rk_x_correct_of_spend_auth_g_ladder_distinct.
    - exact Hcircuit.
    - exact
        (FixedBaseLadder.spend_auth_g_distinct_holds
          Γ Hcircuit).
  Qed.

  Lemma rk_y_correct (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ) :
    read_public_instance Γ Garden.Orchard.circuit.RK_Y =
      Point.y (OrchardSpec.out_rk (action_spec_of Γ)).
  Proof.
    apply rk_y_correct_of_spend_auth_g_ladder_distinct.
    - exact Hcircuit.
    - exact
        (FixedBaseLadder.spend_auth_g_distinct_holds
          Γ Hcircuit).
  Qed.

  (* CMX: the [cmx_correct_of_note_commit_new] bridge with its [Hnote]
     hypothesis assembled in [circuit_proof/note_commit/cmx.v]
     ([NoteCommitNewCmx.cmx_hnote]) from the four legs: the "M + [r] R"
     complete-add + rcm_new fixed-base scalar leg
     ([NoteCommitNewAdd.synthesize_new_cm_point_add_rcm_correct]), the
     109-word Sinsemilla hash fold
     ([NoteCommitNewHash.note_commit_new_hash_point_correct]), the word
     identification with [OrchardSpec.note_commit_message]
     ([NoteCommitNewWords.note_commit_new_words_correct]), and the ρ_new
     nullifier leg ([NullifierKOut.nullifier_cell_correct]).

     The [note_commit_witness_ok] hypothesis is the bundled witness-honesty
     side condition of the new-note commitment (the [merkle_witness_ok]
     analogue): the Sinsemilla incomplete-add nondegeneracy of the witnessed
     109-word message (the hash gate's gradients are unconstrained on the
     exceptional x-collision cases), and the short-lookup range facts of the
     message pieces (halo2's short lookup constrains the checked cell only
     where [q_running = 0], and the relational model pins selectors only
     through [SelectorOn] facts, leaving [q_running] a free prover value at
     the short-range rows).  Both are refutable without the hypothesis, so
     it is threaded through [satisfies_specification] /
     [deterministic] as
     a documented witness-honesty side condition. *)
  Lemma cmx_correct (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ)
      (Hnote_ok : NoteCommitNewCmx.note_commit_witness_ok Γ) :
    read_public_instance Γ Garden.Orchard.circuit.CMX =
      OrchardSpec.out_cmx (action_spec_of Γ).
  Proof.
    exact (NoteCommitNewCmx.cmx_correct_of_witness_ok Γ Hcircuit Hnote_ok).
  Qed.

  (* Record eta for [ActionOutputs] with the two point fields split into
     coordinates — the exact shape [read_action_outputs] expands to.  Proving it
     generically (over a fresh [o]) keeps the large spec term out of the kernel
     check entirely. *)
  Lemma outputs_eta (o : OrchardSpec.ActionOutputs) :
    {|
      OrchardSpec.out_anchor := OrchardSpec.out_anchor o;
      OrchardSpec.out_cv_net := {|
        Point.x := Point.x (OrchardSpec.out_cv_net o);
        Point.y := Point.y (OrchardSpec.out_cv_net o);
      |};
      OrchardSpec.out_nf_old := OrchardSpec.out_nf_old o;
      OrchardSpec.out_rk := {|
        Point.x := Point.x (OrchardSpec.out_rk o);
        Point.y := Point.y (OrchardSpec.out_rk o);
      |};
      OrchardSpec.out_cmx := OrchardSpec.out_cmx o;
    |} = o.
  Proof. destruct o. reflexivity. Qed.

  (** ** The theorem surface *)

  (** [satisfies_specification] — whole-circuit Orchard action functional
      correctness, against the protocol-aligned specification of record
      ([OrchardProtocolSpec.orchard_action_spec]): every public output is
      the §4.18.4 function — with fixed-base multiplications as group
      multiples of the real-coordinate Zcash generators — of the genuine
      inputs read from the assignment.

      Hypotheses: the circuit accepts Γ ([Hcircuit]) and the two
      witness-honesty side conditions ([Hmerkle_ok], [Hnote_ok] —
      protocol-sanctioned incomplete-add/canonicity slack, see
      [docs/orchard-determinism-proof.md]).  The protocol input typing
      ([OrchardProtocolEquiv.ProtocolTypedInputs]: the input ranges under
      which the circuit-structured and protocol layers coincide) is not
      assumed — every conjunct is circuit-enforced on a satisfying
      assignment, and the proof derives the predicate from [Holds Γ] via
      [OrchardValidActionInputs.protocol_typed_inputs_of_holds].
      [Hmerkle_ok] is surfaced because the anchor output is refutable
      without it, [Hnote_ok] because the CMX output is.

      Proof: carry the protocol-aligned right-hand side back onto the
      circuit-structured layer ([OrchardProtocolEquiv.output_protocol_eq]),
      eliminate the square-root witnesses
      ([OrchardActionUsFreeNullifierK.action_spec_us_free], turning the
      us-free [output] into [action_spec_of]), then reduce field by field
      onto the seven per-output bridges and close by record eta
      ([outputs_eta] — no rewrite ever reduces the large spec term). *)
  Theorem satisfies_specification
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ)
      (Hmerkle_ok : OrchardActionMerkle.merkle_witness_ok Γ)
      (Hnote_ok : NoteCommitNewCmx.note_commit_witness_ok Γ) :
    OrchardActionInputs.read_action_outputs Γ =
    OrchardProtocolSpec.orchard_action_spec
      OrchardActionInputs.orchard_circuit_params
      (OrchardActionInputs.read_action_inputs Γ).
  Proof.
    rewrite <- (OrchardProtocolEquiv.output_protocol_eq
      (OrchardActionInputs.read_action_inputs Γ)
      (OrchardValidActionInputs.protocol_typed_inputs_of_holds Γ Hcircuit)).
    rewrite <- (OrchardActionUsFreeNullifierK.action_spec_us_free Γ Hcircuit).
    change (read_action_outputs Γ = action_spec_of Γ).
    unfold read_action_outputs.
    rewrite (anchor_correct Γ Hcircuit Hmerkle_ok), (cv_net_x_correct Γ Hcircuit),
      (cv_net_y_correct Γ Hcircuit), (nf_old_correct Γ Hcircuit),
      (rk_x_correct Γ Hcircuit), (rk_y_correct Γ Hcircuit),
      (cmx_correct Γ Hcircuit Hnote_ok).
    exact (outputs_eta (action_spec_of Γ)).
  Qed.

  (** [deterministic] — whole-circuit Orchard action determinism, derived
      from [satisfies_specification]: two satisfying assignments that agree
      on the genuine inputs ([read_action_inputs], which carries no
      square-root witnesses) agree on every evaluated public [Instance_]
      output.  Both output records equal the protocol specification of the
      same inputs, so they coincide row by row.  The anchor needs no side
      condition: the public anchor row is itself a genuine input
      ([in_anchor_public]), so even the dummy-spend passthrough agrees by
      the same hypothesis.  The input typing is derived from each [Holds]
      inside [satisfies_specification], not assumed. *)
  Theorem deterministic
      (Γ1 Γ2 : Assignment.t columns RegionId.t)
      (H1 : Holds Γ1) (H2 : Holds Γ2)
      (Hmerkle_ok1 : OrchardActionMerkle.merkle_witness_ok Γ1)
      (Hmerkle_ok2 : OrchardActionMerkle.merkle_witness_ok Γ2)
      (Hnote_ok1 : NoteCommitNewCmx.note_commit_witness_ok Γ1)
      (Hnote_ok2 : NoteCommitNewCmx.note_commit_witness_ok Γ2)
      (Hinputs :
        OrchardActionInputs.read_action_inputs Γ1 =
        OrchardActionInputs.read_action_inputs Γ2) :
      forall row : Z,
        row = Garden.Orchard.circuit.ANCHOR \/
        row = Garden.Orchard.circuit.CV_NET_X \/
        row = Garden.Orchard.circuit.CV_NET_Y \/
        row = Garden.Orchard.circuit.NF_OLD \/
        row = Garden.Orchard.circuit.RK_X \/
        row = Garden.Orchard.circuit.RK_Y \/
        row = Garden.Orchard.circuit.CMX ->
        OrchardActionInputs.read_public_instance Γ1 row =
        OrchardActionInputs.read_public_instance Γ2 row.
  Proof.
    pose proof
      (satisfies_specification Γ1 H1 Hmerkle_ok1 Hnote_ok1) as Hdet1.
    pose proof
      (satisfies_specification Γ2 H2 Hmerkle_ok2 Hnote_ok2) as Hdet2.
    (* Both output records equal the protocol spec of the same inputs, so
       the records are equal. *)
    rewrite Hinputs in Hdet1.
    rewrite <- Hdet2 in Hdet1.
    (* Project the record equality onto the requested public row. *)
    intros row Hrow.
    destruct Hrow as [E | Hrow];
      [ subst row; exact (f_equal OrchardSpec.out_anchor Hdet1) | ].
    destruct Hrow as [E | Hrow];
      [ subst row;
        exact (f_equal (fun o => Point.x (OrchardSpec.out_cv_net o)) Hdet1) | ].
    destruct Hrow as [E | Hrow];
      [ subst row;
        exact (f_equal (fun o => Point.y (OrchardSpec.out_cv_net o)) Hdet1) | ].
    destruct Hrow as [E | Hrow];
      [ subst row; exact (f_equal OrchardSpec.out_nf_old Hdet1) | ].
    destruct Hrow as [E | Hrow];
      [ subst row;
        exact (f_equal (fun o => Point.x (OrchardSpec.out_rk o)) Hdet1) | ].
    destruct Hrow as [E | E]; subst row;
      [ exact (f_equal (fun o => Point.y (OrchardSpec.out_rk o)) Hdet1)
      | exact (f_equal OrchardSpec.out_cmx Hdet1) ].
  Qed.

  (** ** The composed Action statement

      [satisfies_specification] and the input-side half
      ([OrchardValidActionInputs.ValidActionInputs],
      [circuit_proof/valid_action_inputs.v]) conjoined: the in-model
      formalization of §4.18.4 'Action Statement (Orchard)' of the Zcash
      protocol specification — the outputs are the protocol's output
      functions of the genuine inputs, and the witnessed inputs satisfy the
      input-side conditions.  Hypotheses: [Holds Γ] plus the four
      witness-honesty conditions (Merkle, new-note, old-note, [Commit^ivk] —
      the protocol's own ⊥-slack; [commit_ivk_witness_ok] additionally
      carries the variable-base-mul nondegeneracy and the [g_d_old]
      base-order fact, see [circuit_proof/valid_action_inputs.v]).
      The two ownership conditions [Hold_note_ok] and [Hivk_ok] feed only the
      [ValidActionInputs] conjunct, discharged by delegation
      ([circuit_proof/old_note/open.v],
      [circuit_proof/ownership/diversified_address.v]) over the
      variable-base-mul chain ([circuit_proof/ownership/var_base_mul.v] and
      its leaf files); [satisfies_specification] depends on neither.  The
      theorem's assumptions reduce to the repo-wide baseline
      ([PrimString.string] and impredicative [Set]). *)
  Theorem action_statement
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ)
      (Hmerkle_ok : OrchardActionMerkle.merkle_witness_ok Γ)
      (Hnote_ok : NoteCommitNewCmx.note_commit_witness_ok Γ)
      (Hold_note_ok : OrchardValidActionInputs.old_note_witness_ok Γ)
      (Hivk_ok : OrchardValidActionInputs.commit_ivk_witness_ok Γ) :
    (OrchardActionInputs.read_action_outputs Γ =
     OrchardProtocolSpec.orchard_action_spec
       OrchardActionInputs.orchard_circuit_params
       (OrchardActionInputs.read_action_inputs Γ)) /\
    OrchardValidActionInputs.ValidActionInputs Γ.
  Proof.
    exact
      (conj (satisfies_specification Γ Hcircuit Hmerkle_ok Hnote_ok)
            (OrchardValidActionInputs.valid_action_inputs_of_holds
              Γ Hcircuit Hold_note_ok Hivk_ok)).
  Qed.

End OrchardAction.
