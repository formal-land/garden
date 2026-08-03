(** * The adversarial Action statement API

    The per-output obligations of §4.18.4 'Action Statement (Orchard)' of
    the Zcash protocol specification ([docs/protocol.pdf]) in their
    disjunctive, witness-honesty-free form, and the statements of the
    assembled adversarial Action theorem and its determinism corollary.
    This file is the statement surface only: the obligations are proved
    from circuit acceptance by the track files
    ([circuit_proof/note_commit_bot.v], [circuit_proof/ownership_bot.v],
    [circuit_proof/merkle_bot.v]) and assembled in
    [circuit_proof/adversarial.v] / [circuit_adversarial.v].

    The existing theorem surface ([circuit_proof/main.v],
    [circuit_proof/valid_action_inputs.v]) states the §4.18.4 clauses as
    exact equalities conditioned on nondegeneracy/canonicity hypotheses —
    the protocol's non-⊥ branch.  The protocol itself states four clauses
    disjunctively, sanctioning the circuit's incomplete-addition slack:
    'Merkle path validity' (via the §4.9 escape), 'Old note commitment
    integrity' ([∈ {cm_old, ⊥}]), 'New note commitment integrity'
    ([∈ {cm_x, ⊥}]) and 'Diversified address integrity'
    ([ivk = ⊥ ∨ pk_d = [ivk] g_d]).  The obligations below transcribe those
    clauses over the ⊥-carrying spec variants
    ([circuit_proof/protocol_spec_bot.v]); the other five public outputs
    are ⊥-free and stay exact equalities.

    Residual model-artifact hypotheses: the short-lookup range families
    (the relational selector model leaves the range-check lookup's
    [q_running] free, [docs/chip-model-caveats.md]) appear as hypotheses of
    the relational statements and are discharged at the acceptance levels
    by the lookup-closure files.  No nondegeneracy or canonicity hypothesis
    appears anywhere. *)

Require Import Stdlib.Lists.List.
Require Import Stdlib.ZArith.ZArith.
Require Import Garden.Halo2.main.
Require Import Garden.Halo2.Synthesis.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.lemmas.
Require Import Garden.Halo2.PallasModel.
Require Import Garden.EllipticCurve.Pallas.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.spec.
Require Import Garden.Halo2.halo2_gadgets.sinsemilla.spec.
Require Import Garden.Halo2.halo2_gadgets.sinsemilla.hash_to_point_proof.
Require Import Garden.Orchard.columns.
Require Garden.Orchard.circuit.
Require Import Garden.Orchard.protocol_spec.
Require Import Garden.Orchard.circuit_proof.inputs.
Require Import Garden.Orchard.circuit_proof.merkle.
Require Import Garden.Orchard.circuit_proof.protocol_equiv.
Require Import Garden.Orchard.circuit_proof.valid_action_inputs.
Require Import Garden.Orchard.circuit_proof.protocol_spec_bot.
Require Import Garden.Orchard.circuit_proof.note_commit.words.
Require Import Garden.Orchard.circuit_proof.old_note.words.
Require Import Garden.Orchard.circuit_proof.ownership.commit_ivk_hash.
Require Import Garden.Field.Field.
Require Import Garden.Plonky3.M.

Import ListNotations.

#[local] Existing Instance Primes.PallasPIsPrime.

Global Open Scope Z_scope.

Module OrchardAdversarialApi.
  Import OrchardActionInputs.
  Import OrchardProtocolSpecBot.

  Local Notation Holds Γ :=
    (circuit_holds Γ
      Garden.Orchard.circuit.synthesize
      (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)).

  (** ** Merkle path readers

      The per-layer authentication-path cells, in the spelling of
      [OrchardActionInputs.merkle_path_of] ([circuit_proof/inputs.v]): the
      cond-swap layout reads the sibling on [A1]/[A6] and the position bit
      on [A4]/[A9] of the layer's [NodePosition] region ([QCondSwap1] for
      layers 0–15, [QCondSwap2] for 16–31). *)

  Definition merkle_node_position (i : Z) : RegionId.t :=
    RegionId.Merkle (RegionId.Merkle.Layer.of_index i)
      RegionId.Merkle.Region.NodePosition.

  Definition merkle_sibling_at
      (Γ : Assignment.t columns RegionId.t) (i : Z) : Z :=
    if i <? 16
    then read1 Γ (merkle_node_position i)
    else read6 Γ (merkle_node_position i).

  Definition merkle_swap_cell
      (Γ : Assignment.t columns RegionId.t) (i : Z) : Z :=
    if i <? 16
    then read4 Γ (merkle_node_position i)
    else read9 Γ (merkle_node_position i).

  Definition merkle_swap_at
      (Γ : Assignment.t columns RegionId.t) (i : Z) : bool :=
    merkle_swap_cell Γ i =? 1.

  (** Booleanity of the 32 position bits — circuit-derived (the cond-swap
      gate constrains the swap cell to a boolean,
      [CondSwap.swap_is_bool]), conjoined by the adversarial statement so
      the [merkle_swap_at] decode is a faithful reading of the §4.9 path
      position. *)
  Definition merkle_swap_bits_boolean
      (Γ : Assignment.t columns RegionId.t) : Prop :=
    forall i : Z, 0 <= i < 32 ->
      merkle_swap_cell Γ i = 0 \/ merkle_swap_cell Γ i = 1.

  (** ** The running Merkle node cells

      The cell chain [circuit.synthesize_merkle_path] threads: the
      witnessed old-note-commitment x-cell at the leaf, then each layer's
      hash output cell.  The recursion is a higher-order iterator over an
      abstract step so the fixpoint body never mentions the synthesis
      constants. *)

  Fixpoint node_cell_iter
      (step : Z -> Garden.Halo2.Synthesis.Cell.t columns RegionId.t ->
        Garden.Halo2.Synthesis.Cell.t columns RegionId.t)
      (leaf : Garden.Halo2.Synthesis.Cell.t columns RegionId.t)
      (n : nat) : Garden.Halo2.Synthesis.Cell.t columns RegionId.t :=
    match n with
    | O => leaf
    | S m => step (Z.of_nat m) (node_cell_iter step leaf m)
    end.

  Definition merkle_node_cell (n : nat)
      : Garden.Halo2.Synthesis.Cell.t columns RegionId.t :=
    node_cell_iter
      (fun layer node =>
        layouter_value
          (Garden.Orchard.circuit.synthesize_merkle_layer layer node))
      OrchardActionMerkle.cm_old_x_cell
      n.

  (** The node value carried after [n] layers: [Extract_P(cm_old)] at
      [n = 0], then each layer's output cell, read reduced. *)
  Definition merkle_node_at
      (Γ : Assignment.t columns RegionId.t) (n : nat) : Z :=
    UnOp.from (eval_cell Γ (merkle_node_cell n)).

  (** ** Residual short-lookup hypothesis of the Merkle track

      The 5-bit ranges of the [RangeB1]/[RangeB2] cells of every layer —
      the [b_1]/[b_2] pieces of the decomposition.  Together they bound
      the layer's [b_1 + b_2·2^5] reconstruction below [2^10 < p], the one
      canonicity conjunct the witnessed-message identity of
      [anchor_path_tracks] needs.  A short-lookup range family like the
      note-commitment ones: free in the relational selector model,
      discharged from operational acceptance by the [ShortSite] machinery
      ([circuit_proof/lookup_closure.v]) in [circuit_proof/merkle_bot.v]. *)
  Definition merkle_b_range_ok
      (Γ : Assignment.t columns RegionId.t) : Prop :=
    forall i : Z, 0 <= i < 32 ->
      0 <=
        UnOp.from (eval_cell Γ
          (Garden.Halo2.Synthesis.Cell.advice
            (Garden.Orchard.circuit.merkle_region i
              RegionId.Merkle.Region.RangeB1)
            Advice.A9 0)) < 2 ^ 5 /\
      0 <=
        UnOp.from (eval_cell Γ
          (Garden.Halo2.Synthesis.Cell.advice
            (Garden.Orchard.circuit.merkle_region i
              RegionId.Merkle.Region.RangeB2)
            Advice.A9 0)) < 2 ^ 5.

  (** ** Obligation: Merkle path validity (§4.18.4, adversarial reading)

      §4.18.4: "Either v^old = 0; or (path, pos) is a valid Merkle path of
      depth MerkleDepth^Orchard, as defined in section 4.9 'Merkle Path
      Validity', from Extract_P(cm^old) to the anchor rt^OrchardPool."

      [anchor_path_tracks] is the path-validity disjunct over the
      *witnessed* per-layer messages: each layer's hashed 52-word message
      is a [merkle_message] of some integer pair congruent mod [p] to the
      running node and the witnessed sibling — not necessarily their
      canonical 255-bit encodings.  The §4.18.4 note licenses exactly this:
      "In the Merkle path validity check, each layer does not check that
      its input bit sequence is a canonical encoding (in {0 .. q_P − 1}) of
      the integer from the previous layer."  Under
      [OrchardActionMerkle.merkle_witness_ok] the witnessed pair collapses
      to the canonical one and the clause becomes the
      [merkle_root_cell_correct] conclusion. *)
  Definition anchor_path_tracks
      (Γ : Assignment.t columns RegionId.t) : Prop :=
    (forall i : nat, (i < 32)%nat ->
       Some (merkle_node_at Γ (S i)) =
         sinsemilla_hash_bot OrchardActionMerkle.merkle_Q
           (OrchardActionMerkle.merkle_words Γ (Z.of_nat i))) /\
    (forall i : nat, (i < 32)%nat ->
       exists left right : Z,
         OrchardActionMerkle.merkle_words Γ (Z.of_nat i) =
           SinsemillaSpec.merkle_message (Z.of_nat i) left right /\
         UnOp.from left =
           (if merkle_swap_at Γ (Z.of_nat i)
            then merkle_sibling_at Γ (Z.of_nat i)
            else merkle_node_at Γ i) /\
         UnOp.from right =
           (if merkle_swap_at Γ (Z.of_nat i)
            then merkle_node_at Γ i
            else merkle_sibling_at Γ (Z.of_nat i))) /\
    merkle_node_at Γ 0%nat =
      EccSpec.extract_x (OrchardSpec.in_cm_old (read_action_inputs Γ)) /\
    merkle_node_at Γ 32%nat =
      read_public_instance Γ Garden.Orchard.circuit.ANCHOR.

  (** The full clause.  Disjunct 1 is §4.18.4's own "Either v^old = 0";
      disjunct 2 is the §4.9 escape — "the validity check is permitted to
      be implemented in such a way that it can pass if any hash value on
      the path, including the root, is 0", which by §5.4.1.3
      ([MerkleCRH^Orchard(…) := 0 if hash = ⊥]) happens exactly when that
      layer's Sinsemilla fold is ⊥; disjunct 3 is path validity over the
      witnessed messages.  There is no ⊥-carrying Merkle *root*: §5.4.1.3
      makes [MerkleCRH^Orchard] total (⊥ ↦ 0) while the circuit's output
      at an exceptional layer is an unconstrained prover value, so after a
      first exception neither the true nor the witnessed root is tracked —
      the escape is an existential over layers, not a root value. *)
  Definition anchor_obligation
      (Γ : Assignment.t columns RegionId.t) : Prop :=
    OrchardSpec.in_v_old (read_action_inputs Γ) = 0 \/
    (exists i : nat, (i < 32)%nat /\
       sinsemilla_hash_to_point_bot OrchardActionMerkle.merkle_Q
         (OrchardActionMerkle.merkle_words Γ (Z.of_nat i)) = None) \/
    anchor_path_tracks Γ.

  (** ** Obligation: new note commitment integrity (§4.18.4)

      "Extract⊥_P(NoteCommit^Orchard_rcm_new(g⋆_d_new, pk⋆_d_new, v_new,
      ρ_new, ψ_new)) ∈ {cm_x, ⊥}" with [ρ_new = nf_old].  The commitment
      is a function of the input record alone — [ρ_new] is the (total)
      nullifier of the old-note inputs — which is what makes
      [deterministic_adversarial_claim] conditioned on inputs only. *)
  Definition cmx_bot_of_inputs
      (prm : OrchardSpec.Params) (inp : OrchardSpec.ActionInputs)
      : option Z :=
    OrchardCmx_bot prm
      (OrchardSpec.in_g_d_new inp)
      (OrchardSpec.in_pk_d_new inp)
      (OrchardSpec.in_v_new inp)
      (OrchardProtocolSpec.nullifier
        (OrchardSpec.in_nk inp) (OrchardSpec.in_rho_old inp)
        (OrchardSpec.in_psi_old inp) (OrchardSpec.in_cm_old inp))
      (OrchardSpec.in_psi_new inp)
      (OrchardSpec.in_rcm_new inp).

  Definition cmx_obligation (Γ : Assignment.t columns RegionId.t) : Prop :=
    cmx_bot_of_inputs orchard_circuit_params (read_action_inputs Γ) = None \/
    cmx_bot_of_inputs orchard_circuit_params (read_action_inputs Γ) =
      Some (read_public_instance Γ Garden.Orchard.circuit.CMX).

  (** ** Obligation: old note commitment integrity (§4.18.4)

      "NoteCommit^Orchard_rcm_old(g⋆_d_old, pk⋆_d_old, v_old, ρ_old,
      ψ_old) ∈ {cm_old, ⊥}" — the literal protocol clause, over the
      ownership-track readers of [circuit_proof/valid_action_inputs.v]. *)
  Definition old_note_bot_of
      (Γ : Assignment.t columns RegionId.t) : option Point.t :=
    note_commit_bot orchard_circuit_params
      (OrchardSpec.in_g_d_old (read_action_inputs Γ))
      (OrchardValidActionInputs.read_pk_d_old Γ)
      (OrchardSpec.in_v_old (read_action_inputs Γ))
      (OrchardSpec.in_rho_old (read_action_inputs Γ))
      (OrchardSpec.in_psi_old (read_action_inputs Γ))
      (OrchardValidActionInputs.read_rcm_old Γ).

  Definition old_note_obligation
      (Γ : Assignment.t columns RegionId.t) : Prop :=
    old_note_bot_of Γ = None \/
    old_note_bot_of Γ =
      Some (OrchardSpec.in_cm_old (read_action_inputs Γ)).

  (** ** Obligation: diversified address integrity (§4.18.4)

      "ivk = ⊥ or pk_d^old = [ivk] g_d^old" with
      [ivk = Commit^ivk_rivk(ak, nk)].  The ⊥ belongs to the [Commit^ivk]
      Sinsemilla fold only; the protocol grants the variable-base
      multiplication no exceptional escape (its p.67 note *requires* the
      [ivk] decomposition to be canonical), so on the tracking branch the
      multiplication holds exactly — the mul chip's nondegeneracy is
      derived from the gates by the ownership track, never disjuncted. *)
  Definition commit_ivk_bot_of
      (Γ : Assignment.t columns RegionId.t) : option Z :=
    commit_ivk_bot orchard_circuit_params
      (EccSpec.extract_x (OrchardSpec.in_ak (read_action_inputs Γ)))
      (OrchardSpec.in_nk (read_action_inputs Γ))
      (OrchardValidActionInputs.read_rivk Γ).

  Definition diversified_address_obligation
      (Γ : Assignment.t columns RegionId.t) : Prop :=
    commit_ivk_bot_of Γ = None \/
    (exists ivk : Z,
       commit_ivk_bot_of Γ = Some ivk /\
       OrchardValidActionInputs.read_pk_d_old Γ =
         PallasModel.repr
           (Pallas.mul ivk
             (PallasModel.unrepr
               (OrchardSpec.in_g_d_old (read_action_inputs Γ))))).

  (** ** The five ⊥-free outputs — exact equalities

      Spend authority, value commitment integrity and nullifier integrity
      use complete addition and total group multiples only (§4.18.4 with
      §5.4.7.1 / §5.4.8.3 / §4.16); the protocol states them as equalities
      and so does the adversarial statement. *)

  Definition cv_net_output_exact
      (Γ : Assignment.t columns RegionId.t) : Prop :=
    {| Point.x := read_public_instance Γ Garden.Orchard.circuit.CV_NET_X;
       Point.y := read_public_instance Γ Garden.Orchard.circuit.CV_NET_Y |} =
    OrchardProtocolSpec.value_commit
      (OrchardProtocolSpec.signed_net_value
        (OrchardSpec.in_magnitude (read_action_inputs Γ))
        (OrchardSpec.in_sign (read_action_inputs Γ)))
      (OrchardSpec.in_rcv (read_action_inputs Γ)).

  Definition nf_old_output_exact
      (Γ : Assignment.t columns RegionId.t) : Prop :=
    read_public_instance Γ Garden.Orchard.circuit.NF_OLD =
    OrchardProtocolSpec.nullifier
      (OrchardSpec.in_nk (read_action_inputs Γ))
      (OrchardSpec.in_rho_old (read_action_inputs Γ))
      (OrchardSpec.in_psi_old (read_action_inputs Γ))
      (OrchardSpec.in_cm_old (read_action_inputs Γ)).

  Definition rk_output_exact
      (Γ : Assignment.t columns RegionId.t) : Prop :=
    {| Point.x := read_public_instance Γ Garden.Orchard.circuit.RK_X;
       Point.y := read_public_instance Γ Garden.Orchard.circuit.RK_Y |} =
    OrchardProtocolSpec.spend_auth_randomize
      (OrchardSpec.in_ak (read_action_inputs Γ))
      (OrchardSpec.in_alpha (read_action_inputs Γ)).

  (** ** The conjoined typing surface

      §4.18.4: "Primary and auxiliary inputs MUST be constrained to have
      the types specified. In particular, g_d^old, pk_d^old, g_d^new,
      pk_d^new, and ak_P cannot be 𝒪_P."  Everything below is
      circuit-derived on a satisfying assignment — the five listed points
      through the unconditional [QWitnessPointNonId] curve-equation gate
      (non-identity because no Pallas point has [x = 0]), [cm_old] through
      the plain [QWitnessPoint] gate (on-curve or the identity sentinel,
      matching [cm^old : P]), the scalar ranges through the running-sum
      window bounds, and the 64-bit note values through the short-lookup
      families.  §4.18.4 does not ask for [< r_P] on the full-width
      scalars ("It is not checked that rcv < r_P or that rcm^old < r_P or
      that rcm^new < r_P"); the [8^85 = 2^255] window bounds are the
      circuit-granularity reading. *)

  (** A reduced affine on-curve non-identity Pallas point, at the
      represented (Weierstrass) reading of an affine coordinate record. *)
  Definition wpoint_typed (P : Point.t) : Prop :=
    Pallas.reduced (PallasModel.unrepr P) /\
    Pallas.on_curve (PallasModel.unrepr P) /\
    PallasModel.unrepr P <> Pallas.identity.

  Definition typed_inputs_extended
      (Γ : Assignment.t columns RegionId.t) : Prop :=
    OrchardProtocolEquiv.ProtocolTypedInputs (read_action_inputs Γ) /\
    0 <= OrchardSpec.in_v_old (read_action_inputs Γ) < 2 ^ 64 /\
    0 <= OrchardSpec.in_v_new (read_action_inputs Γ) < 2 ^ 64 /\
    0 <= OrchardSpec.in_magnitude (read_action_inputs Γ) < 2 ^ 64 /\
    0 <= OrchardValidActionInputs.read_rcm_old Γ < 8 ^ 85 /\
    0 <= OrchardValidActionInputs.read_rivk Γ < 8 ^ 85 /\
    wpoint_typed (OrchardSpec.in_g_d_old (read_action_inputs Γ)) /\
    wpoint_typed (OrchardSpec.in_ak (read_action_inputs Γ)) /\
    wpoint_typed (OrchardValidActionInputs.read_pk_d_old Γ) /\
    wpoint_typed (OrchardSpec.in_g_d_new (read_action_inputs Γ)) /\
    wpoint_typed (OrchardSpec.in_pk_d_new (read_action_inputs Γ)) /\
    (OrchardSpec.in_cm_old (read_action_inputs Γ) = EccSpec.identity \/
     wpoint_typed (OrchardSpec.in_cm_old (read_action_inputs Γ))) /\
    Pallas.mul Pallas.pallas_q
      (PallasModel.unrepr (OrchardSpec.in_g_d_old (read_action_inputs Γ))) =
      Pallas.identity /\
    merkle_swap_bits_boolean Γ.

  (** ** [WellTypedInstance] — the external typing premise

      Exactly the §4.18.4 typing facts that transaction decoding or
      consensus enforces and the circuit does not; everything the circuit
      does enforce is conjoined by [typed_inputs_extended] rather than
      assumed.  Row 9 ([DISABLE_CROSS_ADDRESS]) carries no member on
      purpose: [OrchardValidActionInputs.cross_address_restriction] is
      proved for zero against every nonzero value, which subsumes a
      boolean reading. *)
  Record WellTypedInstance
      (Γ : Assignment.t columns RegionId.t) : Prop := {
    (* §4.18.4 primary input [enableSpends : B].  The [QOrchard] gate
       ("v_old = 0 or enable_spend = 1", [circuit.v]) forces the flag to 1
       only when [v_old <> 0]; at [v_old = 0] the row is a free field
       element.  Enforcement point: transaction decoding of the Action
       description's flags. *)
    wti_enable_spend_bool :
      read_public_instance Γ Garden.Orchard.circuit.ENABLE_SPEND = 0 \/
      read_public_instance Γ Garden.Orchard.circuit.ENABLE_SPEND = 1;

    (* §4.18.4 primary input [enableOutputs : B]; the same asymmetry
       through "v_new = 0 or enable_output = 1". *)
    wti_enable_output_bool :
      read_public_instance Γ Garden.Orchard.circuit.ENABLE_OUTPUT = 0 \/
      read_public_instance Γ Garden.Orchard.circuit.ENABLE_OUTPUT = 1;

    (* §4.18.4 note: "The case rk = 𝒪_P will not occur, due to the
       consensus rule in section 4.6 'Action Descriptions' that rk MUST
       NOT be the identity point."  Enforcement point: consensus. *)
    wti_rk_non_identity :
      ~ (read_public_instance Γ Garden.Orchard.circuit.RK_X = 0 /\
         read_public_instance Γ Garden.Orchard.circuit.RK_Y = 0);

    (* §4.18.4 note: the primary input is the sequence [rt, x(cv^net),
       y(cv^net), nf^old, x(rk), y(rk), cm_x, enableSpends, enableOutputs]
       (rows 0..8; row 9 the cross-address flag), each an F_{q_P} element.
       The member records the decoded rows as already-reduced residues on
       the raw instance plane (the model's evaluated reads reduce
       unconditionally, so the raw plane is where the encoding assumption
       has content).  Enforcement point: the Action-description encoding /
       transaction decoding. *)
    wti_instance_rows_reduced :
      forall row : Z, 0 <= row < 10 ->
        UnOp.from (Γ.(Assignment.instance_) Instance_.Primary row) =
          Γ.(Assignment.instance_) Instance_.Primary row;
  }.

  (** ** The assembled adversarial conclusion

      The §4.18.4 clause set with no witness-honesty hypotheses: the four
      disjunctive clauses, the five exact outputs, the input-side gate
      clauses (value balance, the two enable flags, the cross-address
      restriction — verbatim the corresponding
      [OrchardValidActionInputs.ValidActionInputs] conjuncts), and the
      conjoined typing surface. *)
  Definition adversarial_action_conclusion
      (Γ : Assignment.t columns RegionId.t) : Prop :=
    anchor_obligation Γ /\
    cv_net_output_exact Γ /\
    nf_old_output_exact Γ /\
    rk_output_exact Γ /\
    cmx_obligation Γ /\
    (OrchardSpec.in_v_old (read_action_inputs Γ) -F
       OrchardSpec.in_v_new (read_action_inputs Γ) =
     OrchardSpec.in_magnitude (read_action_inputs Γ) *F
       OrchardSpec.in_sign (read_action_inputs Γ)) /\
    (OrchardSpec.in_v_old (read_action_inputs Γ) = 0 \/
     read_public_instance Γ Garden.Orchard.circuit.ENABLE_SPEND = 1) /\
    (OrchardSpec.in_v_new (read_action_inputs Γ) = 0 \/
     read_public_instance Γ Garden.Orchard.circuit.ENABLE_OUTPUT = 1) /\
    (read_public_instance Γ
       Garden.Orchard.circuit.DISABLE_CROSS_ADDRESS = 0 \/
     (OrchardSpec.in_g_d_old (read_action_inputs Γ) =
        OrchardSpec.in_g_d_new (read_action_inputs Γ) /\
      OrchardValidActionInputs.read_pk_d_old Γ =
        OrchardSpec.in_pk_d_new (read_action_inputs Γ))) /\
    old_note_obligation Γ /\
    diversified_address_obligation Γ /\
    typed_inputs_extended Γ.

  (** The relational adversarial Action statement.  Premises: acceptance,
      the external typing interface, and the residual short-lookup range
      families (model artifacts, discharged at the acceptance levels by
      the lookup-closure machinery).  [WellTypedInstance] carries the
      §4.18.4 typing of the decoded primary input; no conclusion below
      consumes it, and it is part of the statement as the interface under
      which the conclusion set is the §4.18.4 clause set. *)
  Definition action_statement_adversarial_claim : Prop :=
    forall (Γ : Assignment.t columns RegionId.t),
      Holds Γ ->
      WellTypedInstance Γ ->
      NoteCommitNewWords.note_commit_new_short_lookup_ok Γ ->
      OldNoteWords.old_note_short_lookup_ok Γ ->
      CommitIvkHash.commit_ivk_short_lookup_ok Γ ->
      merkle_b_range_ok Γ ->
      adversarial_action_conclusion Γ.

  (** ** Determinism conditioned on inputs alone

      Two satisfying assignments that agree on the input record and on
      which the ⊥-carrying new-note commitment is defined agree on every
      public output row.  Definedness is a predicate on the input record
      ([cmx_bot_of_inputs] reads nothing but the record); no
      nondegeneracy, canonicity or Merkle hypothesis appears.  The anchor
      row needs no side condition — it is itself an input
      ([in_anchor_public]); the five remaining ⊥-free output rows are
      exact from acceptance alone.  The two short-lookup premises are the same
      residual model artifacts as above. *)
  Definition deterministic_adversarial_claim : Prop :=
    forall (Γ1 Γ2 : Assignment.t columns RegionId.t),
      Holds Γ1 ->
      Holds Γ2 ->
      NoteCommitNewWords.note_commit_new_short_lookup_ok Γ1 ->
      NoteCommitNewWords.note_commit_new_short_lookup_ok Γ2 ->
      read_action_inputs Γ1 = read_action_inputs Γ2 ->
      cmx_bot_of_inputs orchard_circuit_params (read_action_inputs Γ1) <>
        None ->
      forall row : Z,
        row = Garden.Orchard.circuit.ANCHOR \/
        row = Garden.Orchard.circuit.CV_NET_X \/
        row = Garden.Orchard.circuit.CV_NET_Y \/
        row = Garden.Orchard.circuit.NF_OLD \/
        row = Garden.Orchard.circuit.RK_X \/
        row = Garden.Orchard.circuit.RK_Y \/
        row = Garden.Orchard.circuit.CMX ->
        read_public_instance Γ1 row = read_public_instance Γ2 row.

  (** ** The discrete-logarithm reading of the ⊥ escapes

      §5.4.1.9's security requirement backs the ⊥ and collision cases
      cryptographically: Theorem 5.4.3 (a fixed-length collision yields a
      nontrivial discrete logarithm relation) and Theorem 5.4.4 (an
      exceptional case — a ⊥ output — yields one).  Both enter only as
      named hypotheses in the style of the balance proof's
      [OrchardBundleSpec.dlog_relation] reduction: an explicit relation,
      never an injectivity or independence axiom.  Nothing here is proved
      or assumed by the adversarial statement itself. *)

  (** A linear combination of the Sinsemilla domain point and table
      generators: [c0]·[Q] plus [Σ c·S(j)] over the listed [(j, c)]
      pairs, in the Pallas group. *)
  Definition sinsemilla_generator_combination
      (Q : Point.t) (c0 : Z) (cs : list (Z * Z)) : Pallas.point :=
    Stdlib.Lists.List.fold_left
      (fun acc jc =>
        Pallas.add acc
          (Pallas.mul (snd jc)
            (PallasModel.unrepr (SinsemillaSpec.generator (fst jc)))))
      cs
      (Pallas.mul c0 (PallasModel.unrepr Q)).

  (** A nontrivial discrete-logarithm relation among [Q] and the [S(j)]:
      the combination vanishes while not every coefficient vanishes
      mod the group order. *)
  Definition sinsemilla_dlog_relation
      (Q : Point.t) (c0 : Z) (cs : list (Z * Z)) : Prop :=
    sinsemilla_generator_combination Q c0 cs = Pallas.identity /\
    ~ (c0 mod Pallas.pallas_q = 0 /\
       List.Forall (fun jc => snd jc mod Pallas.pallas_q = 0) cs).

  (** Theorem 5.4.3 as a named reduction hypothesis: a fixed-length
      collision of the ⊥-carrying hash-to-point yields a relation. *)
  Definition SinsemillaCollisionReduction : Prop :=
    forall (Q : Point.t) (ws ws' : list Z),
      List.length ws = List.length ws' ->
      ws <> ws' ->
      sinsemilla_hash_to_point_bot Q ws =
        sinsemilla_hash_to_point_bot Q ws' ->
      sinsemilla_hash_to_point_bot Q ws <> None ->
      exists (c0 : Z) (cs : list (Z * Z)),
        sinsemilla_dlog_relation Q c0 cs.

  (** Theorem 5.4.4 as a named reduction hypothesis: a ⊥ output of the
      hash-to-point yields a relation (the exceptional operand pair is a
      linear identity among the accumulator's combination and one
      generator). *)
  Definition SinsemillaExceptionalDlogReduction : Prop :=
    forall (Q : Point.t) (ws : list Z),
      sinsemilla_hash_to_point_bot Q ws = None ->
      exists (c0 : Z) (cs : list (Z * Z)),
        sinsemilla_dlog_relation Q c0 cs.

  (** Statement only — no proof is attempted in this development.  Under
      the Theorem 5.4.4 reduction, [anchor_obligation]'s §4.9 escape
      converts into an explicit discrete-logarithm disjunct: an accepted
      assignment either is a dummy spend, or exhibits a relation among the
      Merkle domain point and the Sinsemilla generators, or carries a
      valid witnessed path to the anchor.  This is the §4.9 note's own
      argument — "a ⊥ output from SinsemillaHash yields a nontrivial
      discrete logarithm relation.  Since we assume finding such a
      relation to be infeasible, we can argue that it is safe to allow an
      adversary to create a proof that passes the Merkle validity check in
      such a case." *)
  Definition anchor_exceptional_or_dlog_claim : Prop :=
    SinsemillaExceptionalDlogReduction ->
    forall (Γ : Assignment.t columns RegionId.t),
      Holds Γ ->
      merkle_b_range_ok Γ ->
      OrchardSpec.in_v_old (read_action_inputs Γ) = 0 \/
      (exists (c0 : Z) (cs : list (Z * Z)),
         sinsemilla_dlog_relation OrchardActionMerkle.merkle_Q c0 cs) \/
      anchor_path_tracks Γ.

End OrchardAdversarialApi.
