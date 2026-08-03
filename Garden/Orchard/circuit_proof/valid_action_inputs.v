Require Import Garden.Halo2.main.
Require Import Garden.Halo2.Synthesis.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.lemmas.
Require Import Garden.Orchard.columns.
Require Garden.Orchard.circuit.
Require Import Garden.Orchard.protocol_spec.
Require Import Garden.Orchard.circuit_proof.internal_spec.
Require Import Garden.Orchard.circuit_proof.inputs.
Require Import Garden.Orchard.circuit_proof.protocol_equiv.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.spec.
Require Import Garden.Halo2.PallasModel.
Require Import Garden.EllipticCurve.Pallas.
Require Import Garden.Halo2.halo2_gadgets.sinsemilla.hash_to_point_proof.
Require Import Garden.Orchard.circuit_proof.typed_inputs.full_width.
Require Import Garden.Orchard.circuit_proof.typed_inputs.magnitude.
Require Import Garden.Orchard.circuit_proof.typed_inputs.sign.
Require Import Garden.Orchard.circuit_proof.old_note.words.
Require Import Garden.Orchard.circuit_proof.old_note.open.
Require Import Garden.Orchard.circuit_proof.ownership.commit_ivk_hash.
Require Import Garden.Orchard.circuit_proof.ownership.var_base_mul.
Require Import Garden.Orchard.circuit_proof.ownership.diversified_address.
Require Import Garden.Field.Field.
Require Import Garden.Plonky3.M.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Lists.List.

#[local] Existing Instance Primes.PallasPIsPrime.

Global Open Scope Z_scope.

(** * The ValidActionInputs track

    The input-side conditions of §4.18.4 'Action Statement (Orchard)' of the
    Zcash protocol specification ([docs/protocol.pdf]): the facts a
    satisfying assignment's witnessed inputs are forced to satisfy, beyond
    the output functions of [OrchardAction.satisfies_specification]
    ([circuit_proof/main.v]).  A functional theorem [outputs = f(inputs)]
    cannot express these — they constrain the inputs themselves — and they
    carry the security content the output functions alone cannot: the
    value-balance binding is the anti-inflation keystone.

    Proved here (each from [Holds Γ] alone):

    - [protocol_typed_inputs_of_holds] — the input-typing ranges
      ([OrchardProtocolEquiv.ProtocolTypedInputs]; §4.18.4's "inputs MUST be
      constrained to have the types specified", at circuit granularity),
      assembled from the [circuit_proof/typed_inputs/] slices;
    - [value_balance_gate] — [v_old − v_new = magnitude · sign] (field
      arithmetic), from the [QOrchard] gate;
    - [ValidActionInputs] / [valid_action_inputs_of_holds] — the umbrella
      predicate conjoining the input-side conditions;
    - [enable_spend_flag] / [enable_output_flag] — the two flag clauses;
    - [cross_address_restriction] — the post-NU6.3 conditional equality of
      the old and new expanded receivers;
    - [old_note_commit_integrity] — the witnessed old-note fields open the
      witnessed [cm_old], delegated to
      [OldNoteOpen.old_note_commit_integrity]
      ([circuit_proof/old_note/open.v]), under [old_note_witness_ok];
    - [diversified_address_integrity] — [pk_d_old = [ivk] g_d_old] with
      [ivk = Commit^ivk_rivk(Extract_P(ak_P), nk)], delegated to
      [DiversifiedAddress.diversified_address_integrity]
      ([circuit_proof/ownership/diversified_address.v]), under
      [commit_ivk_witness_ok].

    Value-clause companion: [circuit_proof/cv_net_value.v] (module
    [CvNetValue]) consumes [value_balance_gate] and
    [satisfies_specification] downstream and delivers the §4.18.4 'Value
    commitment integrity' reading — [cv_net = ValueCommit_rcv(v_old −
    v_new)] over the signed net value.

    Assumptions: the four variable-base-mul segment lemmas of
    [circuit_proof/ownership/var_base_mul.v] delegate to the leaf files
    [var_base_incomplete.v], [var_base_complete.v] and
    [var_base_overflow.v], and [valid_action_inputs_of_holds] reduces to the
    repo-wide baseline — the [PrimString.string] primitive and impredicative
    [Set].

    Sharpenings beyond the ranges stated here, kept in their own
    [typed_inputs/] leaves (the [ProtocolTypedInputs] statement itself is
    unchanged — [8²²] remains the magnitude bound it carries):

    - [TypedInputsMagnitude64.in_magnitude_range_64]
      ([circuit_proof/typed_inputs/magnitude64.v]): the unconditional
      [0 ≤ magnitude < 2⁶⁴] bound, derived from the short-fixed-base mul's
      [last_window_check] gate (not from the lookup chip — the pinned
      implementation does not lookup-range-check the magnitude).
    - [TypedInputsValue64.in_v_old_64] / [in_v_new_64]
      ([circuit_proof/typed_inputs/value64.v]): [0 ≤ v_old, v_new < 2⁶⁴]
      from the note-commitment word decompositions, under the respective
      short-lookup honesty conditions ([old_note_short_lookup_ok] is the
      second conjunct of [old_note_witness_ok] below;
      [note_commit_new_short_lookup_ok] is the second conjunct of
      [NoteCommitNewCmx.note_commit_witness_ok]).
    - [CvNetValue.cv_net_commits_net_value_Z]
      ([circuit_proof/cv_net_value.v]): the signed-ℤ reading of 'Value
      commitment integrity' — [cv_net = ValueCommit_rcv(v_old − v_new)]
      with the subtraction over ℤ — under [Holds] plus the Merkle,
      new-note and old-note short-lookup honesty conditions. *)

Module OrchardValidActionInputs.
  Import OrchardActionInputs.

  Local Notation Holds Γ :=
    (circuit_holds Γ
      Garden.Orchard.circuit.synthesize
      (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)).

  (** The inputs read from any satisfying assignment are protocol-typed —
      each conjunct extracted from the circuit's own constraints in
      [circuit_proof/typed_inputs/]: the three full-width scalars from the
      incomplete-mul running-sum window ranges ([TypedInputsFullWidth]), the
      magnitude from the 22-window short-mul running sum ([TypedInputsMagnitude]),
      and the sign from the short-mul sign-square gate ([TypedInputsSign]). *)
  Theorem protocol_typed_inputs_of_holds
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    OrchardProtocolEquiv.ProtocolTypedInputs (read_action_inputs Γ).
  Proof.
    exact
      (conj (TypedInputsFullWidth.in_alpha_range Γ Hcircuit)
      (conj (TypedInputsFullWidth.in_rcv_range Γ Hcircuit)
      (conj (TypedInputsFullWidth.in_rcm_new_range Γ Hcircuit)
      (conj (TypedInputsMagnitude.in_magnitude_range Γ Hcircuit)
            (TypedInputsSign.in_sign_typed Γ Hcircuit))))).
  Qed.

  (** ** ValidActionInputs: value-balance binding

      §4.18.4 'Value commitment integrity' commits [v_old − v_new]; the
      output function alone commits the independent [magnitude]/[sign]
      inputs.  The circuit closes that distance with the [QOrchard] gate
      constraint ["v_old - v_new = magnitude * sign"]
      ([circuit.v], [orchard_circuit_checks_gate]), copied against the same
      witness cells [read_action_inputs] reads.  This lemma extracts it: the
      first input-side condition of the [ValidActionInputs] layer, and the
      anti-inflation keystone tying the committed value to the note value
      difference.  Proof: gate plumbing along the
      [orchard_gate_active_root_eq_anchor_target] template
      ([circuit_proof/bridges.v]) — the first [QOrchard] gate conjunct,
      rewritten along the [v_old]/[v_new]/[magnitude]/[sign] [Copy] facts of
      [synthesize_orchard_gate]. *)
  Theorem value_balance_gate
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    OrchardSpec.in_v_old (read_action_inputs Γ) -F
      OrchardSpec.in_v_new (read_action_inputs Γ) =
    OrchardSpec.in_magnitude (read_action_inputs Γ) *F
      OrchardSpec.in_sign (read_action_inputs Γ).
  Proof.
    destruct Hcircuit as [Hfacts HSatisfies].
    destruct HSatisfies as [Hgates Hlookups].
    pose proof Hfacts as Horchard_facts.
    unfold Garden.Orchard.circuit.synthesize in Horchard_facts.
    do 10 apply interpret_layouter_facts_bind_right in Horchard_facts.
    apply interpret_layouter_facts_bind_left in Horchard_facts.
    unfold Garden.Orchard.circuit.synthesize_orchard_gate in Horchard_facts.
    apply interpret_layouter_facts_add_region in Horchard_facts.
    pose proof Horchard_facts as Hcopy_vold.
    apply interpret_region_facts_bind_left in Hcopy_vold.
    cbn [region_facts interpret_facts interpret_fact eval_cell] in Hcopy_vold.
    destruct Hcopy_vold as [Hcopy_vold _].
    cbn in Hcopy_vold.
    pose proof Horchard_facts as Hcopy_vnew.
    apply interpret_region_facts_bind_right in Hcopy_vnew.
    apply interpret_region_facts_bind_left in Hcopy_vnew.
    cbn [region_facts interpret_facts interpret_fact eval_cell] in Hcopy_vnew.
    destruct Hcopy_vnew as [Hcopy_vnew _].
    cbn in Hcopy_vnew.
    pose proof Horchard_facts as Hcopy_mag.
    do 2 apply interpret_region_facts_bind_right in Hcopy_mag.
    apply interpret_region_facts_bind_left in Hcopy_mag.
    cbn [region_facts interpret_facts interpret_fact eval_cell] in Hcopy_mag.
    destruct Hcopy_mag as [Hcopy_mag _].
    cbn in Hcopy_mag.
    pose proof Horchard_facts as Hcopy_sign.
    do 3 apply interpret_region_facts_bind_right in Hcopy_sign.
    apply interpret_region_facts_bind_left in Hcopy_sign.
    cbn [region_facts interpret_facts interpret_fact eval_cell] in Hcopy_sign.
    destruct Hcopy_sign as [Hcopy_sign _].
    cbn in Hcopy_sign.
    pose proof Horchard_facts as Hselector_fact.
    do 8 apply interpret_region_facts_bind_right in Hselector_fact.
    cbn [region_facts interpret_facts interpret_fact] in Hselector_fact.
    destruct Hselector_fact as [Hselector_fact _].
    pose proof
      (enabled_nonzero Γ Selector.QOrchard RegionId.OrchardCircuitChecks 0
        Hselector_fact) as Hselector.
    pose proof
      (satisfies_gates_at Γ
        (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)
        Garden.Orchard.circuit.orchard_circuit_checks_gate
        RegionId.OrchardCircuitChecks 0
        ltac:(cbn; repeat (first [left; reflexivity | right]))
        Hgates) as Hgate.
    cbn [eval_gate Garden.Orchard.circuit.orchard_circuit_checks_gate
      Gate.constraints Constraints.with_selector eval_constraints
      eval_named_constraint eval_constraint eval_selector eval_expression
      rotated_row Rotation.cur] in Hgate.
    cbn in Hgate.
    destruct Hgate as [Hbalance _].
    specialize (Hbalance Hselector).
    rewrite Hcopy_vold, Hcopy_vnew, Hcopy_mag, Hcopy_sign in Hbalance.
    unfold read_action_inputs, read_action_inputs_with_anchor.
    cbn [OrchardSpec.in_v_old OrchardSpec.in_v_new
      OrchardSpec.in_magnitude OrchardSpec.in_sign].
    unfold read, read9, read_advice.
    cbn [eval_expression rotated_row Rotation.cur].
    exact Hbalance.
  Qed.

  (** ** Enable flags (§4.18.4 'Enable spend flag' / 'Enable output flag')

      [v_old = 0 ∨ enableSpends = 1] and [v_new = 0 ∨ enableOutputs = 1]:
      the transaction layer's global switches, gating value-bearing spends
      and outputs on the two public flag rows.  These are the two §4.18.4
      primary inputs the output theorems do not touch ([ENABLE_SPEND] /
      [ENABLE_OUTPUT], instance rows 7/8); with them every primary input of
      the Action statement is covered by some theorem of the surface.
      Extraction: the third and fourth [QOrchard] gate conjuncts
      ([circuit.v], [orchard_circuit_checks_gate]), the [v_old]/[v_new]
      [Copy] facts, and the two instance-row [Copy] facts of
      [synthesize_orchard_gate]. *)
  Theorem enable_spend_flag
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    OrchardSpec.in_v_old (read_action_inputs Γ) = 0 \/
    read_public_instance Γ Garden.Orchard.circuit.ENABLE_SPEND = 1.
  Proof.
    destruct Hcircuit as [Hfacts HSatisfies].
    destruct HSatisfies as [Hgates Hlookups].
    pose proof Hfacts as Horchard_facts.
    unfold Garden.Orchard.circuit.synthesize in Horchard_facts.
    do 10 apply interpret_layouter_facts_bind_right in Horchard_facts.
    apply interpret_layouter_facts_bind_left in Horchard_facts.
    unfold Garden.Orchard.circuit.synthesize_orchard_gate in Horchard_facts.
    apply interpret_layouter_facts_add_region in Horchard_facts.
    pose proof Horchard_facts as Hcopy_vold.
    apply interpret_region_facts_bind_left in Hcopy_vold.
    cbn [region_facts interpret_facts interpret_fact eval_cell] in Hcopy_vold.
    destruct Hcopy_vold as [Hcopy_vold _].
    cbn in Hcopy_vold.
    pose proof Horchard_facts as Hcopy_es.
    do 6 apply interpret_region_facts_bind_right in Hcopy_es.
    apply interpret_region_facts_bind_left in Hcopy_es.
    cbn [region_facts interpret_facts interpret_fact eval_cell] in Hcopy_es.
    destruct Hcopy_es as [Hcopy_es _].
    cbn in Hcopy_es.
    pose proof Horchard_facts as Hselector_fact.
    do 8 apply interpret_region_facts_bind_right in Hselector_fact.
    cbn [region_facts interpret_facts interpret_fact] in Hselector_fact.
    destruct Hselector_fact as [Hselector_fact _].
    pose proof
      (enabled_nonzero Γ Selector.QOrchard RegionId.OrchardCircuitChecks 0
        Hselector_fact) as Hselector.
    pose proof
      (satisfies_gates_at Γ
        (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)
        Garden.Orchard.circuit.orchard_circuit_checks_gate
        RegionId.OrchardCircuitChecks 0
        ltac:(cbn; repeat (first [left; reflexivity | right]))
        Hgates) as Hgate.
    cbn [eval_gate Garden.Orchard.circuit.orchard_circuit_checks_gate
      Gate.constraints Constraints.with_selector eval_constraints
      eval_named_constraint eval_constraint eval_selector eval_expression
      rotated_row Rotation.cur] in Hgate.
    cbn in Hgate.
    destruct Hgate as (_ & _ & Hspend & _).
    specialize (Hspend Hselector).
    rewrite Hcopy_vold, Hcopy_es in Hspend.
    destruct Hspend as [Hv | He].
    - left. exact Hv.
    - right. symmetry. exact He.
  Qed.

  Theorem enable_output_flag
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    OrchardSpec.in_v_new (read_action_inputs Γ) = 0 \/
    read_public_instance Γ Garden.Orchard.circuit.ENABLE_OUTPUT = 1.
  Proof.
    destruct Hcircuit as [Hfacts HSatisfies].
    destruct HSatisfies as [Hgates Hlookups].
    pose proof Hfacts as Horchard_facts.
    unfold Garden.Orchard.circuit.synthesize in Horchard_facts.
    do 10 apply interpret_layouter_facts_bind_right in Horchard_facts.
    apply interpret_layouter_facts_bind_left in Horchard_facts.
    unfold Garden.Orchard.circuit.synthesize_orchard_gate in Horchard_facts.
    apply interpret_layouter_facts_add_region in Horchard_facts.
    pose proof Horchard_facts as Hcopy_vnew.
    apply interpret_region_facts_bind_right in Hcopy_vnew.
    apply interpret_region_facts_bind_left in Hcopy_vnew.
    cbn [region_facts interpret_facts interpret_fact eval_cell] in Hcopy_vnew.
    destruct Hcopy_vnew as [Hcopy_vnew _].
    cbn in Hcopy_vnew.
    pose proof Horchard_facts as Hcopy_eo.
    do 7 apply interpret_region_facts_bind_right in Hcopy_eo.
    apply interpret_region_facts_bind_left in Hcopy_eo.
    cbn [region_facts interpret_facts interpret_fact eval_cell] in Hcopy_eo.
    destruct Hcopy_eo as [Hcopy_eo _].
    cbn in Hcopy_eo.
    pose proof Horchard_facts as Hselector_fact.
    do 8 apply interpret_region_facts_bind_right in Hselector_fact.
    cbn [region_facts interpret_facts interpret_fact] in Hselector_fact.
    destruct Hselector_fact as [Hselector_fact _].
    pose proof
      (enabled_nonzero Γ Selector.QOrchard RegionId.OrchardCircuitChecks 0
        Hselector_fact) as Hselector.
    pose proof
      (satisfies_gates_at Γ
        (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)
        Garden.Orchard.circuit.orchard_circuit_checks_gate
        RegionId.OrchardCircuitChecks 0
        ltac:(cbn; repeat (first [left; reflexivity | right]))
        Hgates) as Hgate.
    cbn [eval_gate Garden.Orchard.circuit.orchard_circuit_checks_gate
      Gate.constraints Constraints.with_selector eval_constraints
      eval_named_constraint eval_constraint eval_selector eval_expression
      rotated_row Rotation.cur] in Hgate.
    cbn in Hgate.
    destruct Hgate as (_ & _ & _ & Hout).
    specialize (Hout Hselector).
    rewrite Hcopy_vnew, Hcopy_eo in Hout.
    destruct Hout as [Hv | He].
    - left. exact Hv.
    - right. symmetry. exact He.
  Qed.

  (** ** Post-NU6.3 cross-address restriction

      The final synthesis region enables [QOrchard] on four rows, one for
      each coordinate of [(g_d, pk_d)].  On those rows the first gate
      constraint is neutralized as [d - 0 = d * 1], the enable constraints
      are neutralized with ones, and the Merkle product becomes
      [d * (old - new) = 0].  The public API supplies [d] as a Boolean, but
      the circuit proves the stronger field statement below for every
      nonzero value. *)
  Lemma cross_address_coordinate_from_row
      (Γ : Assignment.t columns RegionId.t)
      (row : Z)
      (old_coordinate new_coordinate : Cell.t columns RegionId.t)
      (Hrow :
        interpret_facts Γ
          (region_facts RegionId.PostNu63CrossAddressChecks
            (Garden.Orchard.circuit.synthesize_cross_address_check_row
              RegionId.PostNu63CrossAddressChecks row
              old_coordinate new_coordinate)))
      (Hgates :
        satisfies_gates Γ
          (𝓒.run_unit
            Garden.Orchard.circuit.configure ConstraintSystem.empty)) :
    UnOp.from
      (Γ.(Assignment.instance_) Instance_.Primary
        Garden.Orchard.circuit.DISABLE_CROSS_ADDRESS) = 0 \/
    UnOp.from (eval_cell Γ old_coordinate) =
      UnOp.from (eval_cell Γ new_coordinate).
  Proof.
    pose proof Hrow as Hcopy_disable.
    unfold Garden.Orchard.circuit.synthesize_cross_address_check_row
      in Hcopy_disable.
    apply interpret_region_facts_bind_left in Hcopy_disable.
    cbn [region_facts interpret_facts interpret_fact eval_cell]
      in Hcopy_disable.
    destruct Hcopy_disable as [Hcopy_disable _].
    cbn in Hcopy_disable.

    pose proof Hrow as Hcopy_old.
    unfold Garden.Orchard.circuit.synthesize_cross_address_check_row
      in Hcopy_old.
    do 4 apply interpret_region_facts_bind_right in Hcopy_old.
    apply interpret_region_facts_bind_left in Hcopy_old.
    cbn [region_facts interpret_facts interpret_fact eval_cell] in Hcopy_old.
    destruct Hcopy_old as [Hcopy_old _].
    cbn in Hcopy_old.

    pose proof Hrow as Hcopy_new.
    unfold Garden.Orchard.circuit.synthesize_cross_address_check_row
      in Hcopy_new.
    do 5 apply interpret_region_facts_bind_right in Hcopy_new.
    apply interpret_region_facts_bind_left in Hcopy_new.
    cbn [region_facts interpret_facts interpret_fact eval_cell] in Hcopy_new.
    destruct Hcopy_new as [Hcopy_new _].
    cbn in Hcopy_new.

    pose proof Hrow as Hselector_fact.
    unfold Garden.Orchard.circuit.synthesize_cross_address_check_row
      in Hselector_fact.
    do 10 apply interpret_region_facts_bind_right in Hselector_fact.
    cbn [region_facts interpret_facts interpret_fact] in Hselector_fact.
    destruct Hselector_fact as [Hselector_fact _].
    pose proof
      (enabled_nonzero Γ Selector.QOrchard
        RegionId.PostNu63CrossAddressChecks row Hselector_fact) as Hselector.

    pose proof
      (satisfies_gates_at Γ
        (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)
        Garden.Orchard.circuit.orchard_circuit_checks_gate
        RegionId.PostNu63CrossAddressChecks row
        ltac:(cbn; repeat (first [left; reflexivity | right]))
        Hgates) as Hgate.
    cbn [eval_gate Garden.Orchard.circuit.orchard_circuit_checks_gate
      Gate.constraints Constraints.with_selector eval_constraints
      eval_named_constraint eval_constraint eval_selector eval_expression
      rotated_row Rotation.cur] in Hgate.
    cbn in Hgate.
    destruct Hgate as (_ & Hsame & _ & _).
    specialize (Hsame Hselector).
    unfold rotated_row, Rotation.cur in Hsame.
    cbn [Rotation.offset] in Hsame.
    rewrite Z.add_0_r in Hsame.
    rewrite Hcopy_disable, Hcopy_old, Hcopy_new in Hsame.
    exact Hsame.
  Qed.

  (** ** Ownership-track readers

      The witnesses the input-side conditions below constrain.  They are
      deliberately NOT part of [read_action_inputs]: no public output
      depends on them, so adding them there would weaken
      [OrchardAction.deterministic]. *)

  (** The witnessed old-note recipient key ([witness_non_identity_point] of
      the address-integrity block). *)
  Definition read_pk_d_old (Γ : Assignment.t columns RegionId.t) : Point.t :=
    read_point Γ
      (RegionId.AddressIntegrity RegionId.AddressIntegrity.WitnessPkD).

  (** The complete post-NU6.3 input relation enforced by the four final
      coordinate rows.  The zero branch permits ordinary cross-address
      actions.  Every nonzero field value forces equality of both expanded
      receiver points; no Booleanity claim is made at circuit level. *)
  Theorem cross_address_restriction
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    read_public_instance Γ
      Garden.Orchard.circuit.DISABLE_CROSS_ADDRESS = 0 \/
    (OrchardSpec.in_g_d_old (read_action_inputs Γ) =
       OrchardSpec.in_g_d_new (read_action_inputs Γ) /\
     read_pk_d_old Γ =
       OrchardSpec.in_pk_d_new (read_action_inputs Γ)).
  Proof.
    destruct Hcircuit as [Hfacts HSatisfies].
    destruct HSatisfies as [Hgates Hlookups].
    pose proof Hfacts as Hcross.
    unfold Garden.Orchard.circuit.synthesize in Hcross.
    do 11 apply interpret_layouter_facts_bind_right in Hcross.
    unfold Garden.Orchard.circuit.synthesize_cross_address_checks in Hcross.
    apply interpret_layouter_facts_add_region in Hcross.

    pose proof Hcross as Hrow0.
    apply interpret_region_facts_bind_left in Hrow0.
    pose proof Hcross as Hrow1.
    apply interpret_region_facts_bind_right in Hrow1.
    apply interpret_region_facts_bind_left in Hrow1.
    pose proof Hcross as Hrow2.
    do 2 apply interpret_region_facts_bind_right in Hrow2.
    apply interpret_region_facts_bind_left in Hrow2.
    pose proof Hcross as Hrow3.
    do 3 apply interpret_region_facts_bind_right in Hrow3.

    pose proof
      (cross_address_coordinate_from_row Γ 0
        (Cell.advice
          (RegionId.WitnessInput RegionId.WitnessInput.GDOld) Advice.A0 0)
        (Cell.advice RegionId.NoteCommitNewWitnessGD Advice.A0 0)
        Hrow0 Hgates) as Hgd_x.
    pose proof
      (cross_address_coordinate_from_row Γ 1
        (Cell.advice
          (RegionId.WitnessInput RegionId.WitnessInput.GDOld) Advice.A1 0)
        (Cell.advice RegionId.NoteCommitNewWitnessGD Advice.A1 0)
        Hrow1 Hgates) as Hgd_y.
    pose proof
      (cross_address_coordinate_from_row Γ 2
        (Cell.advice
          (RegionId.AddressIntegrity RegionId.AddressIntegrity.WitnessPkD)
          Advice.A0 0)
        (Cell.advice RegionId.NoteCommitNewWitnessPkD Advice.A0 0)
        Hrow2 Hgates) as Hpk_x.
    pose proof
      (cross_address_coordinate_from_row Γ 3
        (Cell.advice
          (RegionId.AddressIntegrity RegionId.AddressIntegrity.WitnessPkD)
          Advice.A1 0)
        (Cell.advice RegionId.NoteCommitNewWitnessPkD Advice.A1 0)
        Hrow3 Hgates) as Hpk_y.

    destruct Hgd_x as [Hdisabled | Hgd_x].
    { left.
      unfold read_public_instance.
      cbn [eval_expression rotated_row Rotation.cur].
      exact Hdisabled. }
    destruct Hgd_y as [Hdisabled | Hgd_y].
    { left.
      unfold read_public_instance.
      cbn [eval_expression rotated_row Rotation.cur].
      exact Hdisabled. }
    destruct Hpk_x as [Hdisabled | Hpk_x].
    { left.
      unfold read_public_instance.
      cbn [eval_expression rotated_row Rotation.cur].
      exact Hdisabled. }
    destruct Hpk_y as [Hdisabled | Hpk_y].
    { left.
      unfold read_public_instance.
      cbn [eval_expression rotated_row Rotation.cur].
      exact Hdisabled. }
    right.
    split.
    - unfold read_action_inputs, read_action_inputs_with_anchor.
      cbn [OrchardSpec.in_g_d_old OrchardSpec.in_g_d_new].
      unfold read_point, read, read1, read_advice.
      cbn [eval_expression eval_cell rotated_row Rotation.cur] in *.
      f_equal; assumption.
    - unfold read_pk_d_old, read_action_inputs, read_action_inputs_with_anchor.
      cbn [OrchardSpec.in_pk_d_new].
      unfold read_point, read, read1, read_advice.
      cbn [eval_expression eval_cell rotated_row Rotation.cur] in *.
      f_equal; assumption.
  Qed.

  (** The old-note commitment randomness, reconstructed from its 85 witnessed
      windows (the old-note [NoteCommitR] fixed-base leg). *)
  Definition read_rcm_old (Γ : Assignment.t columns RegionId.t) : Z :=
    read_scalar_from_windows Γ
      (RegionId.NoteCommit RegionId.NoteCommit.Which.Old
        RegionId.NoteCommit.FixedBaseIncomplete) 85.

  (** The [Commit^ivk] trapdoor, reconstructed from its 85 witnessed windows
      (the [CommitIvkR] fixed-base leg). *)
  Definition read_rivk (Γ : Assignment.t columns RegionId.t) : Z :=
    read_scalar_from_windows Γ
      (RegionId.CommitIvk RegionId.CommitIvk.FixedBaseIncomplete) 85.

  (** The 109 grid words hashed by the [Which.Old] NoteCommit hash-to-point
      (Sinsemilla variant 1: [bits := A2], word count under
      [Fixed.QSinsemilla2_1]) and the 51 grid words of the [Commit^ivk]
      hash-to-point (same variant). *)
  Definition old_note_words (Γ : Assignment.t columns RegionId.t) : list Z :=
    SinsemillaHash.hash_words Γ Fixed.QSinsemilla2_1 Advice.A2
      (RegionId.NoteCommit RegionId.NoteCommit.Which.Old
        RegionId.NoteCommit.HashToPoint) 109.
  Definition commit_ivk_words (Γ : Assignment.t columns RegionId.t) : list Z :=
    SinsemillaHash.hash_words Γ Fixed.QSinsemilla2_1 Advice.A2
      (RegionId.CommitIvk RegionId.CommitIvk.HashToPoint) 51.

  (** ** Old note commitment integrity (§4.18.4, honest branch)

      [NoteCommit^Orchard_rcm_old(g⋆_d_old, pk⋆_d_old, v_old, ρ_old, ψ_old)
      ∈ {cm_old, ⊥}]: the witnessed old-note fields open the witnessed
      [cm_old].  The witness-honesty condition is the [note_commit_witness_ok]
      shape of the new-note lane ([circuit_proof/note_commit/cmx.v]):
      Sinsemilla incomplete-add nondegeneracy of the old-note fold plus the
      eleven [Which.Old] short-lookup range facts
      ([OldNoteWords.old_note_short_lookup_ok]); words-canonicity is not
      assumed — it follows from [Holds] and the short-lookups by
      [OldNoteWords.note_commit_old_words_correct].  Proof: delegation to
      [OldNoteOpen.old_note_commit_integrity]
      ([circuit_proof/old_note/open.v]). *)
  Definition old_note_witness_ok (Γ : Assignment.t columns RegionId.t) : Prop :=
    SinsemillaHash.nondegenerate
      (OrchardSpec.note_commit_q orchard_circuit_params) (old_note_words Γ) /\
    OldNoteWords.old_note_short_lookup_ok Γ.

  Theorem old_note_commit_integrity
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (Hok : old_note_witness_ok Γ) :
    OrchardProtocolSpec.note_commit orchard_circuit_params
      (OrchardSpec.in_g_d_old (read_action_inputs Γ)) (read_pk_d_old Γ)
      (OrchardSpec.in_v_old (read_action_inputs Γ))
      (OrchardSpec.in_rho_old (read_action_inputs Γ))
      (OrchardSpec.in_psi_old (read_action_inputs Γ))
      (read_rcm_old Γ) =
    OrchardSpec.in_cm_old (read_action_inputs Γ).
  Proof.
    destruct Hok as [Hnondeg Hshort].
    exact (OldNoteOpen.old_note_commit_integrity Γ Hcircuit Hnondeg Hshort).
  Qed.

  (** ** Diversified address integrity (§4.18.4, honest branch)

      [ivk = ⊥ ∨ pk_d_old = [ivk] g_d_old] with
      [ivk = Commit^ivk_rivk(Extract_P(ak_P), nk)]: the private link from
      the old note's recipient address to the spending authority.  The
      honesty condition:

      - the [Commit^ivk] Sinsemilla fold's nondegeneracy and its three
        short-lookup range facts
        ([CommitIvkHash.commit_ivk_short_lookup_ok]); words-canonicity (the
        second §4.18.4 canonicity MUST, [ivk] being used as a variable-base
        scalar) follows from [Holds] and the short-lookups by
        [CommitIvkHash.commit_ivk_words_correct];
      - [VarBaseMul.mul_nondegenerate] — the variable-base mul chip's
        incomplete-addition halves never meet a degenerate case (the
        chip-level analogue of Sinsemilla nondegeneracy, surfaced by the
        mul composition).

      The base-order fact [Pallas.mul pallas_q g_d_old = identity] is not
      part of the honesty condition: it holds for every reduced on-curve
      Pallas point ([PallasOrder.pallas_mul_q_on_curve],
      [EllipticCurve/PallasOrder.v]) and is derived from [Holds] by
      [DiversifiedAddress.base_point_order].

      Proof: delegation to
      [DiversifiedAddress.diversified_address_integrity]
      ([circuit_proof/ownership/diversified_address.v]) over the [VarBaseMul]
      chain; the theorem carries no assumptions beyond the repo-wide
      baseline. *)
  Definition commit_ivk_witness_ok (Γ : Assignment.t columns RegionId.t) : Prop :=
    SinsemillaHash.nondegenerate
      (OrchardSpec.commit_ivk_q orchard_circuit_params) (commit_ivk_words Γ) /\
    CommitIvkHash.commit_ivk_short_lookup_ok Γ /\
    VarBaseMul.mul_nondegenerate Γ.

  Theorem diversified_address_integrity
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (Hok : commit_ivk_witness_ok Γ) :
    read_pk_d_old Γ =
    PallasModel.repr
      (Pallas.mul
        (OrchardProtocolSpec.commit_ivk orchard_circuit_params
          (EccSpec.extract_x (OrchardSpec.in_ak (read_action_inputs Γ)))
          (OrchardSpec.in_nk (read_action_inputs Γ))
          (read_rivk Γ))
        (PallasModel.unrepr (OrchardSpec.in_g_d_old (read_action_inputs Γ)))).
  Proof.
    destruct Hok as (Hnondeg & Hshort & Hmulnd).
    exact (DiversifiedAddress.diversified_address_integrity Γ Hcircuit
      Hnondeg Hshort Hmulnd).
  Qed.

  (** ** The umbrella predicate: the input-side half of §4.18.4

      The conjunction of the Action statement's input-side conditions, as a
      Γ-level predicate (the ownership conditions constrain witnesses
      [read_action_inputs] pins to constants, so Γ — not the input record —
      is the domain).  The first conjunct is
      [OrchardProtocolEquiv.ProtocolTypedInputs] — the part of §4.18.4's
      input-typing MUST the protocol equivalence consumes, namely the three
      full-width scalar ranges ([α], [rcv], [rcm^new] under [8^85]), the
      [8^22] magnitude bound and the sign condition.  It is *not* the whole
      §4.18.4 typing surface: the 64-bit bounds on [v_old]/[v_new], the
      [rcm^old]/[rivk] ranges, the non-identity and on-curve typing of the
      witnessed points, and the Boolean reading of the enable flags at zero
      note values are all outside it.  Those facts are assembled — the
      circuit-derived ones proved, the decoding/consensus ones named — by
      [OrchardAdversarialApi.typed_inputs_extended] and
      [OrchardAdversarialApi.WellTypedInstance]
      ([circuit_proof/adversarial_api.v]).

      The second conjunct is the value-balance binding (the circuit's
      realization of the [v_old − v_new] argument of 'Value commitment
      integrity'); then the two enable-flag clauses, the post-NU6.3
      cross-address restriction, and the two ownership clauses (honest
      branches).

      [OrchardAction.action_statement] ([circuit_proof/main.v]) conjoins
      this with [satisfies_specification]: together they are the in-model
      formalization of §4.18.4 on the protocol's non-⊥ branch.  The
      disjunctive reading, with the exceptional branches in the conclusion
      and the full typing surface conjoined, is
      [OrchardAdversarial.action_statement_adversarial]
      ([circuit_proof/adversarial.v]). *)
  Definition ValidActionInputs (Γ : Assignment.t columns RegionId.t) : Prop :=
    OrchardProtocolEquiv.ProtocolTypedInputs (read_action_inputs Γ) /\
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
       read_pk_d_old Γ =
         OrchardSpec.in_pk_d_new (read_action_inputs Γ))) /\
    (OrchardProtocolSpec.note_commit orchard_circuit_params
       (OrchardSpec.in_g_d_old (read_action_inputs Γ)) (read_pk_d_old Γ)
       (OrchardSpec.in_v_old (read_action_inputs Γ))
       (OrchardSpec.in_rho_old (read_action_inputs Γ))
       (OrchardSpec.in_psi_old (read_action_inputs Γ))
       (read_rcm_old Γ) =
     OrchardSpec.in_cm_old (read_action_inputs Γ)) /\
    (read_pk_d_old Γ =
     PallasModel.repr
       (Pallas.mul
         (OrchardProtocolSpec.commit_ivk orchard_circuit_params
           (EccSpec.extract_x (OrchardSpec.in_ak (read_action_inputs Γ)))
           (OrchardSpec.in_nk (read_action_inputs Γ))
           (read_rivk Γ))
         (PallasModel.unrepr
           (OrchardSpec.in_g_d_old (read_action_inputs Γ))))).

  (** [Holds Γ] delivers every input-side condition, under the two
      witness-honesty hypotheses of the ownership clauses (the same
      protocol-sanctioned ⊥-slack as [satisfies_specification]'s
      [Hmerkle_ok]/[Hnote_ok], plus the mul-chip nondegeneracy
      condition of [commit_ivk_witness_ok]).  The theorem's
      assumptions reduce to the repo-wide baseline ([PrimString.string] and
      impredicative [Set]). *)
  Theorem valid_action_inputs_of_holds
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (Hold_note_ok : old_note_witness_ok Γ)
      (Hivk_ok : commit_ivk_witness_ok Γ) :
    ValidActionInputs Γ.
  Proof.
    exact
      (conj (protocol_typed_inputs_of_holds Γ Hcircuit)
      (conj (value_balance_gate Γ Hcircuit)
      (conj (enable_spend_flag Γ Hcircuit)
      (conj (enable_output_flag Γ Hcircuit)
      (conj (cross_address_restriction Γ Hcircuit)
      (conj (old_note_commit_integrity Γ Hcircuit Hold_note_ok)
            (diversified_address_integrity Γ Hcircuit Hivk_ok))))))).
  Qed.
End OrchardValidActionInputs.
