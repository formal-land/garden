(** * The assembled adversarial Action statement

    §4.18.4 'Action Statement (Orchard)' of the Zcash protocol
    specification ([docs/protocol.pdf]), in the form the protocol itself
    states it: four of the clauses disjunctively, with the ⊥ member of the
    disjunction carried by the option-valued spec variants of
    [circuit_proof/protocol_spec_bot.v], the other five public outputs as
    exact equalities, and the whole input-typing surface conjoined.

    The three track files discharge the four disjunctive clauses from
    circuit acceptance alone ([circuit_proof/merkle_bot.v],
    [circuit_proof/note_commit_bot.v], [circuit_proof/ownership_bot.v]);
    this file adds the ⊥-free output equalities and the typing surface,
    and assembles [OrchardAdversarialApi.adversarial_action_conclusion].

    What is *not* a hypothesis, in contrast with
    [OrchardAction.action_statement] ([circuit_proof/main.v]): the Merkle
    package, the two note-commitment nondegeneracy conditions, the
    [Commit^ivk] nondegeneracy, and the variable-base mul chip's
    nondegeneracy.  What remains: circuit acceptance, the external typing
    interface [OrchardAdversarialApi.WellTypedInstance] (facts belonging to
    transaction decoding or consensus, never to the circuit), and the four
    short-lookup range families — model artifacts of the relational
    selector plane ([docs/chip-model-caveats.md]), discharged at the
    acceptance levels in [circuit_adversarial.v].

    The typing surface is circuit-derived throughout.  The five points
    §4.18.4 requires to be non-identity ([g_d^old], [ak_P], [pk_d^old],
    [g_d^new], [pk_d^new]) are witnessed through the
    [Selector.QWitnessPointNonId] gate, whose single constraint is the
    unconditional curve equation; no Pallas point has [x = 0]
    ([EccSpec.pallas_curve_x_nonzero]), so non-identity follows.  [cm^old]
    is witnessed through the plain [Selector.QWitnessPoint] gate, whose
    disjunctive constraint gives on-curve or the identity sentinel —
    matching the protocol's [cm^old : P].

    Anti-blowup discipline ([docs/compile-performance.md]): every bridge
    onto the protocol action spec is stated over *variable* parameters and
    inputs, so no unification ever compares two sides differing underneath
    a [sinsemilla_hash_to_point] or Poseidon application; the assembly is
    [conj] term composition. *)

Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Lists.List.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.ZArith.ZArith.
Require Import Garden.Halo2.main.
Require Import Garden.Halo2.Synthesis.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.lemmas.
Require Import Garden.Halo2.PallasModel.
Require Import Garden.EllipticCurve.Pallas.
Require Import Garden.EllipticCurve.PallasOrder.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.spec.
Require Garden.Halo2.halo2_gadgets.ecc.chip.witness_point.
Require Garden.Halo2.halo2_gadgets.utilities.cond_swap.
Require Import Garden.Halo2.halo2_gadgets.utilities.cond_swap_proof.
Require Import Garden.Halo2.halo2_gadgets.sinsemilla.spec.
Require Import Garden.Halo2.halo2_gadgets.sinsemilla.hash_to_point_proof.
Require Import Garden.Orchard.columns.
Require Garden.Orchard.circuit.
Require Import Garden.Orchard.protocol_spec.
Require Import Garden.Orchard.circuit_proof.facts.
Require Import Garden.Orchard.circuit_proof.inputs.
Require Import Garden.Orchard.circuit_proof.merkle.
Require Import Garden.Orchard.circuit_proof.fixed_base.main.
Require Import Garden.Orchard.circuit_proof.protocol_equiv.
Require Import Garden.Orchard.circuit_proof.valid_action_inputs.
Require Import Garden.Orchard.circuit_proof.typed_inputs.value64.
Require Import Garden.Orchard.circuit_proof.typed_inputs.magnitude64.
Require Import Garden.Orchard.circuit_proof.note_commit.words.
Require Import Garden.Orchard.circuit_proof.old_note.words.
Require Import Garden.Orchard.circuit_proof.old_note.open.
Require Import Garden.Orchard.circuit_proof.ownership.commit_ivk_hash.
Require Import Garden.Orchard.circuit_proof.ownership.diversified_address.
Require Import Garden.Orchard.circuit_proof.main.
Require Import Garden.Orchard.circuit_proof.protocol_spec_bot.
Require Import Garden.Orchard.circuit_proof.adversarial_api.
Require Import Garden.Orchard.circuit_proof.note_commit_bot.
Require Import Garden.Orchard.circuit_proof.ownership_bot.
Require Import Garden.Orchard.circuit_proof.merkle_bot.
Require Import Garden.Field.Field.
Require Import Garden.Plonky3.M.

Import ListNotations.

#[local] Existing Instance Primes.PallasPIsPrime.

Global Open Scope Z_scope.

Module OrchardAdversarial.
  Import OrchardActionInputs.
  Import OrchardProtocolSpecBot.
  Import OrchardAdversarialApi.

  Local Notation Holds Γ :=
    (circuit_holds Γ
      Garden.Orchard.circuit.synthesize
      (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)).

  (** ** Record projections of the protocol action spec

      Over VARIABLE parameters and inputs: both sides are the same
      application, so neither the Sinsemilla folds nor the Poseidon round
      chain is ever reduced. *)

  Lemma out_cv_net_of_action_spec
      (prm : OrchardSpec.Params) (inp : OrchardSpec.ActionInputs) :
    OrchardSpec.out_cv_net
      (OrchardProtocolSpec.orchard_action_spec prm inp) =
    OrchardProtocolSpec.value_commit
      (OrchardProtocolSpec.signed_net_value
        (OrchardSpec.in_magnitude inp) (OrchardSpec.in_sign inp))
      (OrchardSpec.in_rcv inp).
  Proof. reflexivity. Qed.

  Lemma out_rk_of_action_spec
      (prm : OrchardSpec.Params) (inp : OrchardSpec.ActionInputs) :
    OrchardSpec.out_rk
      (OrchardProtocolSpec.orchard_action_spec prm inp) =
    OrchardProtocolSpec.spend_auth_randomize
      (OrchardSpec.in_ak inp) (OrchardSpec.in_alpha inp).
  Proof. reflexivity. Qed.

  Lemma point_eta (P : Point.t) :
    {| Point.x := Point.x P; Point.y := Point.y P |} = P.
  Proof. destruct P; reflexivity. Qed.

  (** The public anchor row is itself an input: [read_action_inputs]
      carries it as [in_anchor_public]. *)
  Lemma in_anchor_public_read (Γ : Assignment.t columns RegionId.t) :
    OrchardSpec.in_anchor_public (read_action_inputs Γ) =
      read_public_instance Γ Garden.Orchard.circuit.ANCHOR.
  Proof. reflexivity. Qed.

  (** ** The three ⊥-free output clauses

      §4.18.4 'Value commitment integrity', 'Nullifier integrity' and
      'Spend authority' use complete addition and total group multiples
      only, so the protocol states them — and the circuit satisfies them —
      as equalities, with acceptance the only hypothesis. *)

  Lemma cv_net_output_of_holds
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ) :
    cv_net_output_exact Γ.
  Proof.
    unfold cv_net_output_exact.
    rewrite (OrchardAction.cv_net_x_correct Γ Hcircuit).
    rewrite (OrchardAction.cv_net_y_correct Γ Hcircuit).
    rewrite (OrchardNoteCommitBot.action_spec_protocol Γ Hcircuit).
    rewrite (out_cv_net_of_action_spec orchard_circuit_params
      (read_action_inputs Γ)).
    apply point_eta.
  Qed.

  Lemma nf_old_output_of_holds
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ) :
    nf_old_output_exact Γ.
  Proof.
    unfold nf_old_output_exact.
    rewrite (OrchardAction.nf_old_correct Γ Hcircuit).
    rewrite (OrchardNoteCommitBot.action_spec_protocol Γ Hcircuit).
    exact (OrchardNoteCommitBot.out_nf_old_of_action_spec
      orchard_circuit_params (read_action_inputs Γ)).
  Qed.

  Lemma rk_output_of_holds
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ) :
    rk_output_exact Γ.
  Proof.
    unfold rk_output_exact.
    rewrite (OrchardAction.rk_x_correct Γ Hcircuit).
    rewrite (OrchardAction.rk_y_correct Γ Hcircuit).
    rewrite (OrchardNoteCommitBot.action_spec_protocol Γ Hcircuit).
    rewrite (out_rk_of_action_spec orchard_circuit_params
      (read_action_inputs Γ)).
    apply point_eta.
  Qed.

  (** ** Witnessed-point typing

      §4.18.4: "Primary and auxiliary inputs MUST be constrained to have
      the types specified.  In particular, g_d^old, pk_d^old, g_d^new,
      pk_d^new, and ak_P cannot be 𝒪_P."  All five are constrained by the
      circuit: the [Selector.QWitnessPointNonId] gate is the unconditional
      curve equation, and no Pallas affine point has [x = 0], so the
      identity sentinel [(0, 0)] is excluded. *)

  Lemma wpoint_typed_of_curve_eqn
      (Γ : Assignment.t columns RegionId.t) (region : RegionId.t)
      (Hcurve :
        Γ ⊢ ⟦ Garden.Halo2.halo2_gadgets.ecc.chip.witness_point
            .curve_eqn Advice.A0 Advice.A1 ⟧ (region, 0) = 0) :
    wpoint_typed (read_point Γ region).
  Proof.
    unfold Garden.Halo2.halo2_gadgets.ecc.chip.witness_point.curve_eqn,
      Garden.Halo2.halo2_gadgets.utilities.square in Hcurve.
    cbn [Evaluation.eval ExpressionIsEvaluable eval_expression rotated_row
      Rotation.cur] in Hcurve.
    change (rotated_row 0 Rotation.cur) with 0 in Hcurve.
    assert (Hb_red :
      UnOp.from Garden.Halo2.halo2_gadgets.ecc.chip.constants.pallas_b
        = Garden.Halo2.halo2_gadgets.ecc.chip.constants.pallas_b)
      by (vm_compute; reflexivity).
    rewrite Hb_red in Hcurve.
    set (x := UnOp.from (Γ.(Assignment.advice) Advice.A0 region 0)) in Hcurve.
    set (y := UnOp.from (Γ.(Assignment.advice) Advice.A1 region 0)) in Hcurve.
    pose proof (EccSpec.pallas_curve_x_nonzero x y Hcurve) as Hxnz.
    assert (Hxr : UnOp.from x = x) by (subst x; apply FieldRewrite.from_from).
    assert (Hxne : x <> 0) by (rewrite <- Hxr; exact Hxnz).
    assert (Hpt : PallasModel.unrepr (read_point Γ region)
        = Weierstrass.Weierstrass.Affine x y).
    { unfold read_point, read, read1, read_advice, PallasModel.unrepr.
      cbn [Evaluation.eval ExpressionIsEvaluable eval_expression
        Point.x Point.y].
      change (rotated_row 0 Rotation.cur) with 0.
      fold x. fold y.
      destruct (Z.eqb_spec x 0) as [E|E].
      - exfalso. apply Hxne. exact E.
      - cbn [andb]. reflexivity. }
    unfold wpoint_typed.
    rewrite Hpt.
    refine (conj _ (conj _ _)).
    - split; [exact Hxr | subst y; apply FieldRewrite.from_from].
    - exact (PallasModel.affine_on_curve_of_poly x y Hcurve).
    - intro Hid. discriminate Hid.
  Qed.

  (** The four remaining [QWitnessPointNonId] call sites of
      [circuit.synthesize], reached by the layouter-fact navigation of
      their binding positions ([g_d^old] is
      [DiversifiedAddress.g_d_old_curve_eqn]). *)

  Lemma ak_p_curve_eqn
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ) :
    Γ ⊢ ⟦ Garden.Halo2.halo2_gadgets.ecc.chip.witness_point
        .curve_eqn Advice.A0 Advice.A1 ⟧
      (RegionId.WitnessInput RegionId.WitnessInput.AkP, 0) = 0.
  Proof.
    destruct Hcircuit as [Hfacts HSatisfies].
    destruct HSatisfies as [Hgates Hlookups].
    apply (OrchardActionFixedBase.witness_non_identity_point_on_curve Γ
      (Garden.Orchard.circuit.witness_input_region RegionId.WitnessInput.AkP)
      "witness ak_P").
    - unfold Garden.Orchard.circuit.synthesize in Hfacts.
      apply interpret_layouter_facts_bind_right in Hfacts.
      apply interpret_layouter_facts_bind_left in Hfacts.
      unfold Garden.Orchard.circuit.synthesize_witness_inputs in Hfacts.
      do 4 apply interpret_layouter_facts_bind_right in Hfacts.
      apply interpret_layouter_facts_bind_left in Hfacts.
      exact Hfacts.
    - exact Hgates.
  Qed.

  Lemma pk_d_old_curve_eqn
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ) :
    Γ ⊢ ⟦ Garden.Halo2.halo2_gadgets.ecc.chip.witness_point
        .curve_eqn Advice.A0 Advice.A1 ⟧
      (RegionId.AddressIntegrity RegionId.AddressIntegrity.WitnessPkD, 0) = 0.
  Proof.
    destruct Hcircuit as [Hfacts HSatisfies].
    destruct HSatisfies as [Hgates Hlookups].
    apply (OrchardActionFixedBase.witness_non_identity_point_on_curve Γ
      (Garden.Orchard.circuit.address_integrity_region
        RegionId.AddressIntegrity.WitnessPkD)
      "witness pk_d_old").
    - unfold Garden.Orchard.circuit.synthesize in Hfacts.
      do 7 apply interpret_layouter_facts_bind_right in Hfacts.
      apply interpret_layouter_facts_bind_left in Hfacts.
      unfold Garden.Orchard.circuit.synthesize_address_integrity in Hfacts.
      do 4 apply interpret_layouter_facts_bind_right in Hfacts.
      apply interpret_layouter_facts_bind_left in Hfacts.
      exact Hfacts.
    - exact Hgates.
  Qed.

  Lemma g_d_new_curve_eqn
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ) :
    Γ ⊢ ⟦ Garden.Halo2.halo2_gadgets.ecc.chip.witness_point
        .curve_eqn Advice.A0 Advice.A1 ⟧
      (RegionId.NoteCommitNewWitnessGD, 0) = 0.
  Proof.
    destruct Hcircuit as [Hfacts HSatisfies].
    destruct HSatisfies as [Hgates Hlookups].
    apply (OrchardActionFixedBase.witness_non_identity_point_on_curve Γ
      RegionId.NoteCommitNewWitnessGD "witness g_d_new_star").
    - unfold Garden.Orchard.circuit.synthesize in Hfacts.
      do 9 apply interpret_layouter_facts_bind_right in Hfacts.
      apply interpret_layouter_facts_bind_left in Hfacts.
      unfold Garden.Orchard.circuit.synthesize_note_commit_new in Hfacts.
      apply interpret_layouter_facts_bind_left in Hfacts.
      exact Hfacts.
    - exact Hgates.
  Qed.

  Lemma pk_d_new_curve_eqn
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ) :
    Γ ⊢ ⟦ Garden.Halo2.halo2_gadgets.ecc.chip.witness_point
        .curve_eqn Advice.A0 Advice.A1 ⟧
      (RegionId.NoteCommitNewWitnessPkD, 0) = 0.
  Proof.
    destruct Hcircuit as [Hfacts HSatisfies].
    destruct HSatisfies as [Hgates Hlookups].
    apply (OrchardActionFixedBase.witness_non_identity_point_on_curve Γ
      RegionId.NoteCommitNewWitnessPkD "witness pk_d_new").
    - unfold Garden.Orchard.circuit.synthesize in Hfacts.
      do 9 apply interpret_layouter_facts_bind_right in Hfacts.
      apply interpret_layouter_facts_bind_left in Hfacts.
      unfold Garden.Orchard.circuit.synthesize_note_commit_new in Hfacts.
      apply interpret_layouter_facts_bind_right in Hfacts.
      apply interpret_layouter_facts_bind_left in Hfacts.
      exact Hfacts.
    - exact Hgates.
  Qed.

  (** [cm^old] is witnessed by the plain [Selector.QWitnessPoint] gate,
      whose constraint is [x = 0 ∨ on_curve] together with
      [y = 0 ∨ on_curve]: on-curve or the identity sentinel, which is
      §4.18.4's [cm^old : P]. *)
  Lemma cm_old_typed_of_holds
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ) :
    OrchardSpec.in_cm_old (read_action_inputs Γ) = EccSpec.identity \/
    wpoint_typed (OrchardSpec.in_cm_old (read_action_inputs Γ)).
  Proof.
    assert (Hcm : OrchardSpec.in_cm_old (read_action_inputs Γ) =
        read_point Γ (RegionId.WitnessInput RegionId.WitnessInput.CmOld))
      by reflexivity.
    rewrite Hcm.
    destruct Hcircuit as [Hfacts HSatisfies].
    destruct HSatisfies as [Hgates Hlookups].
    assert (Hpt : interpret_facts Γ (layouter_facts
        (Garden.Orchard.circuit.witness_point
          (Garden.Orchard.circuit.witness_input_region
            RegionId.WitnessInput.CmOld) "cm_old"))).
    { unfold Garden.Orchard.circuit.synthesize in Hfacts.
      apply interpret_layouter_facts_bind_right in Hfacts.
      apply interpret_layouter_facts_bind_left in Hfacts.
      unfold Garden.Orchard.circuit.synthesize_witness_inputs in Hfacts.
      do 2 apply interpret_layouter_facts_bind_right in Hfacts.
      apply interpret_layouter_facts_bind_left in Hfacts.
      exact Hfacts. }
    destruct (OrchardActionFixedBase.witness_point_sound Γ
      (Garden.Orchard.circuit.witness_input_region
        RegionId.WitnessInput.CmOld)
      "cm_old" Hpt Hgates) as [ [Hx Hy] | Hcurve ].
    - left.
      unfold read_point, read, read1, read_advice, EccSpec.identity.
      f_equal; assumption.
    - right. exact (wpoint_typed_of_curve_eqn Γ _ Hcurve).
  Qed.

  (** ** Merkle position-bit booleanity

      The cond-swap gate of each layer's [NodePosition] region constrains
      the swap cell to a boolean ([CondSwap.swap_is_bool]), so the
      [merkle_swap_at] decode of [OrchardAdversarialApi.anchor_path_tracks]
      is a faithful reading of the §4.9 authentication path. *)

  Lemma is_bool_z (z : Z) (H : IsBool.ZIsBool.(IsBool.t) z) :
    z = 0 \/ z = 1.
  Proof.
    cbn in H. destruct (Z.odd z); [right | left]; exact H.
  Qed.

  Lemma merkle_layer_facts_at
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ)
      (i : nat) (Hi : (i < 32)%nat) :
    interpret_facts Γ (layouter_facts
      (Garden.Orchard.circuit.synthesize_merkle_layer (Z.of_nat i)
        (merkle_node_cell i))).
  Proof.
    pose proof (OrchardActionFacts.merkle_path_facts Γ Hcircuit) as Hpath.
    change (interpret_facts Γ
      (layouter_facts
        (Garden.Orchard.circuit.synthesize_merkle_path
          OrchardActionMerkle.cm_old_x_cell))) in Hpath.
    unfold Garden.Orchard.circuit.synthesize_merkle_path in Hpath.
    apply interpret_layouter_facts_in_namespace in Hpath.
    pose proof (OrchardMerkleBot.layers_facts Γ 32%nat 0
      OrchardActionMerkle.cm_old_x_cell Hpath i Hi) as Hf.
    change (0 + Z.of_nat i) with (Z.of_nat i) in Hf.
    rewrite (OrchardMerkleBot.merkle_node_cell_eq i).
    exact Hf.
  Qed.

  Lemma merkle_swap_bits_of_holds
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ) :
    merkle_swap_bits_boolean Γ.
  Proof.
    intros i Hi.
    pose proof (OrchardActionFixedBase.holds_gates Γ Hcircuit) as Hgates.
    assert (Hz : i = Z.of_nat (Z.to_nat i)) by lia.
    pose proof (merkle_layer_facts_at Γ Hcircuit (Z.to_nat i)
      ltac:(lia)) as Hfacts.
    rewrite <- Hz in Hfacts.
    unfold merkle_swap_cell, merkle_node_position.
    unfold Garden.Orchard.circuit.synthesize_merkle_layer in Hfacts.
    destruct (i <? 16) eqn:Hlt.
    - apply interpret_layouter_facts_bind_left in Hfacts.
      unfold Garden.Orchard.circuit.synthesize_node_position_1,
        Garden.Orchard.circuit.synthesize_node_position_instance in Hfacts.
      apply interpret_layouter_facts_in_namespace in Hfacts.
      apply interpret_layouter_facts_add_region in Hfacts.
      cbn [region_facts region_value Monad.bind Monad.ret
        Garden.Halo2.Synthesis.RegionIsMonad List.app
        interpret_facts interpret_fact] in Hfacts.
      destruct Hfacts as (HselNP & _ & _).
      apply is_bool_z.
      exact (CondSwap.swap_is_bool Γ
        (Garden.Orchard.circuit.merkle_region i
          RegionId.Merkle.Region.NodePosition)
        0 Selector.QCondSwap1 Advice.A0 Advice.A1 Advice.A2 Advice.A3
        Advice.A4
        (enabled_nonzero Γ Selector.QCondSwap1 _ 0 HselNP)
        (satisfies_gates_at Γ
          (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)
          (Garden.Halo2.halo2_gadgets.utilities.cond_swap.cond_swap_gate
            Selector.QCondSwap1 Advice.A0 Advice.A1 Advice.A2 Advice.A3
            Advice.A4)
          (Garden.Orchard.circuit.merkle_region i
            RegionId.Merkle.Region.NodePosition)
          0
          ltac:(cbn; repeat (first [left; reflexivity | right]))
          Hgates)).
    - apply interpret_layouter_facts_bind_left in Hfacts.
      unfold Garden.Orchard.circuit.synthesize_node_position_2,
        Garden.Orchard.circuit.synthesize_node_position_instance in Hfacts.
      apply interpret_layouter_facts_in_namespace in Hfacts.
      apply interpret_layouter_facts_add_region in Hfacts.
      cbn [region_facts region_value Monad.bind Monad.ret
        Garden.Halo2.Synthesis.RegionIsMonad List.app
        interpret_facts interpret_fact] in Hfacts.
      destruct Hfacts as (HselNP & _ & _).
      apply is_bool_z.
      exact (CondSwap.swap_is_bool Γ
        (Garden.Orchard.circuit.merkle_region i
          RegionId.Merkle.Region.NodePosition)
        0 Selector.QCondSwap2 Advice.A5 Advice.A6 Advice.A7 Advice.A8
        Advice.A9
        (enabled_nonzero Γ Selector.QCondSwap2 _ 0 HselNP)
        (satisfies_gates_at Γ
          (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)
          (Garden.Halo2.halo2_gadgets.utilities.cond_swap.cond_swap_gate
            Selector.QCondSwap2 Advice.A5 Advice.A6 Advice.A7 Advice.A8
            Advice.A9)
          (Garden.Orchard.circuit.merkle_region i
            RegionId.Merkle.Region.NodePosition)
          0
          ltac:(cbn; repeat (first [left; reflexivity | right]))
          Hgates)).
  Qed.

  (** ** The conjoined typing surface

      Every conjunct is circuit-derived on a satisfying assignment.  The
      two 64-bit note-value bounds are the only ones needing a short-lookup
      family; §4.18.4 asks for no [< r_P] bound on the full-width scalars
      ("It is not checked that rcv < r_P or that rcm^old < r_P or that
      rcm^new < r_P"), and the [8^85 = 2^255] window reconstruction bounds
      are the circuit-granularity reading. *)

  Theorem typed_inputs_extended_of_holds
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (Hnew_short : NoteCommitNewWords.note_commit_new_short_lookup_ok Γ)
      (Hold_short : OldNoteWords.old_note_short_lookup_ok Γ) :
    typed_inputs_extended Γ.
  Proof.
    unfold typed_inputs_extended.
    refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _
      (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))))))))).
    - exact (OrchardValidActionInputs.protocol_typed_inputs_of_holds
        Γ Hcircuit).
    - exact (TypedInputsValue64.in_v_old_64 Γ Hcircuit Hold_short).
    - exact (TypedInputsValue64.in_v_new_64 Γ Hcircuit Hnew_short).
    - exact (TypedInputsMagnitude64.in_magnitude_range_64 Γ Hcircuit).
    - exact (OldNoteOpen.read_rcm_old_range Γ Hcircuit).
    - exact (DiversifiedAddress.read_rivk_range Γ Hcircuit).
    - exact (wpoint_typed_of_curve_eqn Γ _
        (DiversifiedAddress.g_d_old_curve_eqn Γ Hcircuit)).
    - exact (wpoint_typed_of_curve_eqn Γ _ (ak_p_curve_eqn Γ Hcircuit)).
    - exact (wpoint_typed_of_curve_eqn Γ _ (pk_d_old_curve_eqn Γ Hcircuit)).
    - exact (wpoint_typed_of_curve_eqn Γ _ (g_d_new_curve_eqn Γ Hcircuit)).
    - exact (wpoint_typed_of_curve_eqn Γ _ (pk_d_new_curve_eqn Γ Hcircuit)).
    - exact (cm_old_typed_of_holds Γ Hcircuit).
    - exact (DiversifiedAddress.base_point_order Γ Hcircuit).
    - exact (merkle_swap_bits_of_holds Γ Hcircuit).
  Qed.

  (** ** The adversarial Action statement

      The §4.18.4 clause set with no witness-honesty hypothesis: the four
      disjunctive clauses from the track files, the three ⊥-free output
      equalities, the four input-side gate clauses, and the typing surface.
      [WellTypedInstance] carries the §4.18.4 typing of the decoded primary
      input — the facts enforced by transaction decoding and consensus
      rather than by the circuit; it is the interface under which the
      conclusion is the protocol's clause set.

      The remaining premises are the four short-lookup range families: the
      relational selector model leaves the range-check lookup's
      [q_running] free at the checked rows, so they are model artifacts
      rather than assumptions about the witness, and
      [circuit_adversarial.v] discharges all four from acceptance of the
      pinned circuit. *)

  Theorem action_statement_adversarial
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (Hwti : WellTypedInstance Γ)
      (Hnew_short : NoteCommitNewWords.note_commit_new_short_lookup_ok Γ)
      (Hold_short : OldNoteWords.old_note_short_lookup_ok Γ)
      (Hivk_short : CommitIvkHash.commit_ivk_short_lookup_ok Γ)
      (Hmerkle_b : merkle_b_range_ok Γ) :
    adversarial_action_conclusion Γ.
  Proof.
    unfold adversarial_action_conclusion.
    refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _
      (conj _ (conj _ (conj _ (conj _ _))))))))))).
    - exact (OrchardMerkleBot.anchor_obligation_of_holds Γ Hcircuit Hmerkle_b).
    - exact (cv_net_output_of_holds Γ Hcircuit).
    - exact (nf_old_output_of_holds Γ Hcircuit).
    - exact (rk_output_of_holds Γ Hcircuit).
    - exact (OrchardNoteCommitBot.cmx_obligation_of_holds
        Γ Hcircuit Hnew_short).
    - exact (OrchardValidActionInputs.value_balance_gate Γ Hcircuit).
    - exact (OrchardValidActionInputs.enable_spend_flag Γ Hcircuit).
    - exact (OrchardValidActionInputs.enable_output_flag Γ Hcircuit).
    - exact (OrchardValidActionInputs.cross_address_restriction Γ Hcircuit).
    - exact (OrchardNoteCommitBot.old_note_obligation_of_holds
        Γ Hcircuit Hold_short).
    - exact (OrchardOwnershipBot.diversified_address_obligation_of_holds
        Γ Hcircuit Hivk_short).
    - exact (typed_inputs_extended_of_holds
        Γ Hcircuit Hnew_short Hold_short).
  Qed.

  Corollary action_statement_adversarial_ok :
    action_statement_adversarial_claim.
  Proof.
    intros Γ Hcircuit Hwti Hnew_short Hold_short Hivk_short Hmerkle_b.
    exact (action_statement_adversarial Γ Hcircuit Hwti
      Hnew_short Hold_short Hivk_short Hmerkle_b).
  Qed.

  (** ** Determinism conditioned on inputs alone

      Two satisfying assignments agreeing on [read_action_inputs], on which
      the ⊥-carrying new-note commitment of those inputs is defined, agree
      on every public output row.  The definedness side condition is a
      predicate on the input record alone — that is what makes the
      statement conditioned on inputs and nothing else; on the exceptional
      branch §4.18.4 licenses the prover to choose [cm_x], so no
      determinism statement can hold there.

      The five ⊥-free output rows and the anchor need no side condition at
      all: their three output clauses are exact from acceptance, and the
      anchor row is itself an input. *)

  Theorem deterministic_adversarial
      (Γ1 Γ2 : Assignment.t columns RegionId.t)
      (H1 : Holds Γ1) (H2 : Holds Γ2)
      (Hnew1 : NoteCommitNewWords.note_commit_new_short_lookup_ok Γ1)
      (Hnew2 : NoteCommitNewWords.note_commit_new_short_lookup_ok Γ2)
      (Hinputs : read_action_inputs Γ1 = read_action_inputs Γ2)
      (Hdef :
        cmx_bot_of_inputs orchard_circuit_params (read_action_inputs Γ1) <>
          None) :
    forall row : Z,
      row = Garden.Orchard.circuit.ANCHOR \/
      row = Garden.Orchard.circuit.CV_NET_X \/
      row = Garden.Orchard.circuit.CV_NET_Y \/
      row = Garden.Orchard.circuit.NF_OLD \/
      row = Garden.Orchard.circuit.RK_X \/
      row = Garden.Orchard.circuit.RK_Y \/
      row = Garden.Orchard.circuit.CMX ->
      read_public_instance Γ1 row = read_public_instance Γ2 row.
  Proof.
    (* The anchor row is an input. *)
    assert (Eanchor : read_public_instance Γ1 Garden.Orchard.circuit.ANCHOR =
        read_public_instance Γ2 Garden.Orchard.circuit.ANCHOR).
    { rewrite <- (in_anchor_public_read Γ1), <- (in_anchor_public_read Γ2).
      rewrite Hinputs. reflexivity. }
    (* The value commitment. *)
    pose proof (cv_net_output_of_holds Γ1 H1) as Ecv1.
    pose proof (cv_net_output_of_holds Γ2 H2) as Ecv2.
    unfold cv_net_output_exact in Ecv1, Ecv2.
    rewrite Hinputs in Ecv1.
    rewrite <- Ecv2 in Ecv1.
    (* The nullifier. *)
    pose proof (nf_old_output_of_holds Γ1 H1) as Enf1.
    pose proof (nf_old_output_of_holds Γ2 H2) as Enf2.
    unfold nf_old_output_exact in Enf1, Enf2.
    rewrite Hinputs in Enf1.
    rewrite <- Enf2 in Enf1.
    (* The randomized spend-authority key. *)
    pose proof (rk_output_of_holds Γ1 H1) as Erk1.
    pose proof (rk_output_of_holds Γ2 H2) as Erk2.
    unfold rk_output_exact in Erk1, Erk2.
    rewrite Hinputs in Erk1.
    rewrite <- Erk2 in Erk1.
    (* The new-note commitment, on the defined branch of the clause. *)
    assert (Ecmx : read_public_instance Γ1 Garden.Orchard.circuit.CMX =
        read_public_instance Γ2 Garden.Orchard.circuit.CMX).
    { destruct (OrchardNoteCommitBot.cmx_obligation_of_holds Γ1 H1 Hnew1)
        as [Hnone | Hs1]; [exfalso; exact (Hdef Hnone) |].
      destruct (OrchardNoteCommitBot.cmx_obligation_of_holds Γ2 H2 Hnew2)
        as [Hnone | Hs2].
      { exfalso. apply Hdef. rewrite Hinputs. exact Hnone. }
      rewrite Hinputs in Hs1.
      injection (eq_trans (eq_sym Hs1) Hs2) as Hrow.
      exact Hrow. }
    intros row Hrow.
    destruct Hrow as [E | Hrow]; [subst row; exact Eanchor |].
    destruct Hrow as [E | Hrow];
      [subst row; exact (f_equal Point.x Ecv1) |].
    destruct Hrow as [E | Hrow];
      [subst row; exact (f_equal Point.y Ecv1) |].
    destruct Hrow as [E | Hrow]; [subst row; exact Enf1 |].
    destruct Hrow as [E | Hrow];
      [subst row; exact (f_equal Point.x Erk1) |].
    destruct Hrow as [E | E]; subst row;
      [exact (f_equal Point.y Erk1) | exact Ecmx].
  Qed.

  Corollary deterministic_adversarial_ok :
    deterministic_adversarial_claim.
  Proof.
    intros Γ1 Γ2 H1 H2 Hnew1 Hnew2 Hinputs Hdef.
    exact (deterministic_adversarial Γ1 Γ2 H1 H2 Hnew1 Hnew2 Hinputs Hdef).
  Qed.
End OrchardAdversarial.
