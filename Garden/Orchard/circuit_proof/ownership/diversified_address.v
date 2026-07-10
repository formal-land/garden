(** * Diversified address integrity: the end-to-end composition

    From a satisfying assignment, the witnessed old-note recipient key is the
    variable-base multiple of the witnessed diversified base by the
    [Commit^ivk] identity-derived scalar:

    [pk_d_old = [Commit^ivk_rivk(Extract_P(ak_P), nk)] g_d_old]

    — the honest branch of §4.18.4 'Diversified address integrity', in
    exactly the shape of
    [OrchardValidActionInputs.diversified_address_integrity]
    ([circuit_proof/valid_action_inputs.v]).  Structure:

    - the CommitIvkR fixed-base ladder chain
      ([circuit_proof/ladder/note_commit_r.v] pattern at the
      [CommitIvk.FixedBaseIncomplete] region): the Γ-free certificate
      bridges over [circuit_proof/commit_ivk_r/{table,x_cert,sign_cert,
      disc_cert}.v], per-window full correctness, and the full 83-edge
      ladder-distinctness predicate ([commit_ivk_r_distinct_holds]) — the
      [Hdistinct] hypothesis of [CommitIvkHash.commit_ivk_point_correct]
      discharged from [Holds];
    - witness elimination ([table_us_free_of_oncurve] at the CommitIvkR
      on-curve and non-residue facts) and the protocol bridge
      [CommitIvkRMulProtocol.commit_ivk_r_mul_protocol]: the blinding leg is
      [mul_commit_ivk_r rivk] for the windowed scalar read off the region
      ([commit_ivk_r_mul_leg], with [read_rivk_range]);
    - the ivk scalar ([ivk_scalar_correct]): the x-cell of the
      [CommitIvk.CompletePointAdd] output — [VarBaseMul.alpha_value], the
      scalar the variable-base [mul] chip consumes — equals
      [OrchardProtocolSpec.commit_ivk] of the witnessed [ak] x-coordinate,
      [nk] and [rivk], through [CommitIvkHash.commit_ivk_words_correct] /
      [commit_ivk_point_correct];
    - the witnessed base ([base_point_facts]): the [QWitnessPointNonId] gate
      at the [GDOld] witness region makes [g_d_old] a reduced affine
      on-curve non-identity point (curve membership via
      [PallasModel.affine_on_curve_of_poly]; [x ≠ 0] — hence not the
      [(0, 0)] sentinel — via [EccSpec.pallas_curve_x_nonzero]);
    - the [AddressIntegrity.Equality] region's two [Copy] facts, pinning the
      witnessed [pk_d_old] point to the mul chip's output cells
      ([pk_d_old_pinned]);
    - the capstone [diversified_address_integrity], composing the above
      with [VarBaseMul.address_integrity_mul_correct]
      ([circuit_proof/ownership/var_base_mul.v]).

    Side conditions ([commit_ivk_witness_ok]), the refinement target for
    [OrchardValidActionInputs.commit_ivk_witness_ok]:
    - Sinsemilla incomplete-add nondegeneracy of the witnessed 51-word
      [Commit^ivk] message (the [merkle_witness_ok] shape);
    - the three [Commit^ivk] short-lookup range facts
      ([CommitIvkHash.commit_ivk_short_lookup_ok]);
    - variable-base incomplete-add nondegeneracy
      ([VarBaseMul.mul_nondegenerate]) — the mul chip's honesty condition;
    - the base-order fact [Pallas.mul pallas_q g_d_old = identity].  This
      one is NOT witness honesty but a true statement about every Pallas
      point (the curve group has prime order [q]); that cardinality fact is
      not part of the formalized Weierstrass interface, so it is carried as
      a hypothesis on the witnessed base until a curve-order certificate
      exists (see [VarBaseMul]'s header).

    Proof status: everything in this file is [Qed], as is the whole
    [VarBaseMul] chain it consumes (the four segment lemmas of
    [circuit_proof/ownership/var_base_mul.v] delegate to the [Qed] leaf
    files [var_base_incomplete.v], [var_base_complete.v],
    [var_base_overflow.v]). *)

Require Import Garden.Halo2.main.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.lemmas.
Require Import Garden.Orchard.columns.
Require Garden.Orchard.circuit.
Require Garden.Orchard.circuit.commit_ivk.
Require Garden.Orchard.constants.fixed_bases.commit_ivk_r.
Require Import Garden.Halo2.halo2_gadgets.sinsemilla.hash_to_point_proof.
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
Require Import Garden.Orchard.circuit_proof.fixed_base.main.
Require Import Garden.Orchard.circuit_proof.us_free.main.
Require Import Garden.Orchard.circuit_proof.ladder.main.
Require Import Garden.Orchard.circuit_proof.table_defs.
Require Import Garden.Orchard.circuit_proof.commit_ivk_r.table.
Require Import Garden.Orchard.circuit_proof.commit_ivk_r.x_cert.
Require Import Garden.Orchard.circuit_proof.commit_ivk_r.sign_cert.
Require Import Garden.Orchard.circuit_proof.commit_ivk_r.disc_cert.
Require Import Garden.Orchard.circuit_proof.protocol_mul.commit_ivk_r.
Require Import Garden.Orchard.circuit_proof.typed_inputs.full_width.
Require Import Garden.Orchard.circuit_proof.ownership.commit_ivk_hash.
Require Import Garden.Orchard.circuit_proof.ownership.var_base_mul.
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

(* The consumed fixed-base lemmas carry [is_square]/[field_sqrt]/
   [fixed_window_point_canonical] over the concrete Pallas modulus;
   conversion must compare them by congruence, never unfold. *)
Strategy opaque
  [is_square modpow modpow_pos field_sqrt fixed_window_point_canonical].

Module DiversifiedAddress.
  Import OrchardActionInputs.
  Import OrchardActionFacts.
  Import FixedBaseLadder.

  Local Notation Holds Γ :=
    (circuit_holds Γ
      Garden.Orchard.circuit.synthesize
      (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)).

  (* The CommitIvkR incomplete-additions region, spelled out (not aliased) so
     downstream consumers match syntactically. *)
  Local Notation CIR :=
    (RegionId.CommitIvk RegionId.CommitIvk.FixedBaseIncomplete).

  (** ** The CommitIvkR ladder chain ([ladder/note_commit_r.v] pattern)

      Make scalar multiplication opaque to conversion for the x-coordinate
      instances (the same opaque window as in [circuit_proof/ladder/main.v]). *)
  Strategy opaque [Pallas.mul Weierstrass.Weierstrass.mul].

  (** Table-entry bridge: window [w], digit [d]'s entry of
      [CommitIvkRFullTable.full_table] is the abstract multiple
      [window_scalar 85 w d · commit_ivk_r_G]. *)
  Lemma commit_ivk_r_full_table_entry_eq_mul (w : nat) (d : Z)
      (Hw : (w < 85)%nat) (Hd : 0 <= d < 8) :
    List.nth (Z.to_nat d)
      (List.nth w CommitIvkRFullTable.full_table []) Pallas.identity
    = Pallas.mul (window_scalar 85 w d) PallasGenerators.commit_ivk_r_G.
  Proof.
    unfold CommitIvkRFullTable.full_table, CommitIvkRFullTable.G.
    exact (full_table_entry_eq_mul_gen PallasGenerators.commit_ivk_r_G
             PallasGenerators.commit_ivk_r_on_curve
             PallasGenerators.commit_ivk_r_reduced 84 w d Hw Hd).
  Qed.

  (** Window-point x-coordinate agreement, from the Lagrange x-coordinate
      certificate [CommitIvkRFixedWindowCert.x_check_entry]. *)
  Lemma commit_ivk_r_fixed_window_point_x_eq_mul (w : nat) (d u : Z)
      (Hw : (w < 85)%nat) (Hd : 0 <= d < 8) :
    Point.x
      (EccSpec.fixed_window_point
        (List.nth w (OrchardCircuitSpec.commit_ivk_r orchard_internal_params)
          OrchardActionFixedBase.fixed_window_default) d u) =
    Point.x
      (PallasModel.repr
        (Pallas.mul (window_scalar 85 w d) PallasGenerators.commit_ivk_r_G)).
  Proof.
    refine (fixed_window_point_x_eq_mul_gen PallasGenerators.commit_ivk_r_G
              PallasGenerators.commit_ivk_r_on_curve
              PallasGenerators.commit_ivk_r_reduced 84
              (OrchardCircuitSpec.commit_ivk_r orchard_internal_params)
              _ w d u Hw Hd).
    intros w' i' Hw' Hi'.
    pose proof (CommitIvkRFixedWindowCert.x_check_entry w' i' Hw' Hi') as Hx.
    unfold CommitIvkRFixedWindowCert.table, CommitIvkRFixedWindowCert.default
      in Hx.
    unfold CommitIvkRFullTable.full_table, CommitIvkRFullTable.G in Hx.
    exact Hx.
  Qed.

  (** Restore [mul] transparency for the downstream lemmas. *)
  Strategy transparent [Pallas.mul Weierstrass.Weierstrass.mul].

  (** Per-window full correctness from a satisfying assignment
      ([full_window_correct_gen] at the CommitIvkR base; the region facts
      and shape lemmas are [CommitIvkHash]'s). *)
  Lemma commit_ivk_r_full_window_correct
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ)
      (j : nat) (Hj : (j < 85)%nat) :
    OrchardActionFixedBase.incomplete_additions_window_point Γ CIR (Z.of_nat j) =
    PallasModel.repr
      (Pallas.mul
        (window_scalar 85 j
          (EccSpec.window_digit
            (read_scalar_from_windows Γ CIR 85) j))
        PallasGenerators.commit_ivk_r_G).
  Proof.
    pose proof (CommitIvkHash.commit_ivk_r_incomplete_facts Γ Hcircuit) as Hfacts.
    pose proof (OrchardActionFixedBase.holds_gates Γ Hcircuit) as Hgates.
    refine (full_window_correct_gen Γ CIR
      PallasGenerators.commit_ivk_r_G
      PallasGenerators.commit_ivk_r_on_curve
      PallasGenerators.commit_ivk_r_reduced
      85
      (fun i => EccSpec.window_digit
        (read_scalar_from_windows Γ CIR 85) i)
      (fun i _ => window_digit_bound
        (read_scalar_from_windows Γ CIR 85) i)
      (OrchardCircuitSpec.commit_ivk_r orchard_internal_params)
      _ _ _ _ _ j Hj).
    - (* Hwindow_eq *)
      intros i Hi.
      exact (OrchardActionUsFree.full_width_table_window_correct Γ CIR
        Garden.Orchard.constants.fixed_bases.commit_ivk_r.full_fixed_rows
        CommitIvkHash.commit_ivk_r_rows_standard
        CommitIvkHash.commit_ivk_r_rows_length
        Hfacts Hgates i Hi).
    - (* Hwindow_on_curve *)
      intros i Hi.
      exact (OrchardActionUsFree.full_width_spec_window_on_curve Γ CIR
        Garden.Orchard.constants.fixed_bases.commit_ivk_r.full_fixed_rows
        CommitIvkHash.commit_ivk_r_rows_standard
        CommitIvkHash.commit_ivk_r_rows_length
        Hfacts Hgates i Hi).
    - (* Hwindow_disc *)
      intros i Hi.
      exact (window_disc_qr_commit_ivk_r_all_Z i
        (EccSpec.window_digit
          (read_scalar_from_windows Γ CIR 85) i)
        Hi
        (window_digit_bound
          (read_scalar_from_windows Γ CIR 85) i)).
    - (* Hwindow_qr *)
      intros i Hi.
      pose proof (window_digit_bound
        (read_scalar_from_windows Γ CIR 85) i) as Hdj.
      set (dj := EccSpec.window_digit
        (read_scalar_from_windows Γ CIR 85) i) in *.
      pose proof (CommitIvkRWindowSignCert.y_check_entry i (Z.to_nat dj) Hi
        ltac:(lia)) as Hfc.
      rewrite (commit_ivk_r_full_table_entry_eq_mul i dj Hi Hdj) in Hfc.
      exact Hfc.
    - (* Hwindow_x *)
      intros i d u Hi Hd.
      exact (commit_ivk_r_fixed_window_point_x_eq_mul i d u Hi Hd).
  Qed.

  (** The FULL CommitIvkR ladder-distinctness predicate — the [Hdistinct]
      hypothesis of the [CommitIvkHash] K-out chain, from [Holds] alone. *)
  Lemma commit_ivk_r_distinct_holds
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    OrchardActionFixedBase.incomplete_additions_distinct_precondition Γ CIR 1 83
      (OrchardActionFixedBase.incomplete_additions_window_point Γ CIR 0).
  Proof.
    refine (ladder_distinct_precondition_holds_gen Γ CIR
      PallasGenerators.commit_ivk_r_G
      PallasGenerators.commit_ivk_r_on_curve
      PallasGenerators.commit_ivk_r_reduced
      85
      (fun i => EccSpec.window_digit
        (read_scalar_from_windows Γ CIR 85) i)
      (fun i _ => window_digit_bound
        (read_scalar_from_windows Γ CIR 85) i)
      PallasGenerators.commit_ivk_r_ne_identity
      PallasGeneratorsOrder.commit_ivk_r_order
      ltac:(lia)
      (fun j Hj => commit_ivk_r_full_window_correct Γ Hcircuit j Hj)
      83 eq_refl).
  Qed.

  (** ** Witness elimination and the protocol bridge *)

  Lemma rivk_windows_range
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    List.Forall (fun w => 0 <= w < 8) (read_windows Γ CIR 85).
  Proof.
    exact (OrchardActionFixedBase.full_width_incomplete_region_windows_range
      Γ CIR _
      (CommitIvkHash.commit_ivk_r_incomplete_facts Γ Hcircuit)
      (OrchardActionFixedBase.holds_gates Γ Hcircuit)).
  Qed.

  Lemma read_rivk_range
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    0 <= read_scalar_from_windows Γ CIR 85 < 8 ^ 85.
  Proof.
    apply TypedInputsFullWidth.read_scalar_from_windows_85_range.
    exact (rivk_windows_range Γ Hcircuit).
  Qed.

  Lemma commit_ivk_r_us_eq
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    EccSpec.fixed_scalar_mul
      (OrchardCircuitSpec.commit_ivk_r orchard_internal_params)
      (read_scalar_from_windows Γ CIR 85)
      (read_us Γ CIR 85) =
    EccSpec.fixed_scalar_mul
      (OrchardCircuitSpec.commit_ivk_r orchard_internal_params)
      (read_scalar_from_windows Γ CIR 85)
      (canonical_us_for
        (OrchardCircuitSpec.commit_ivk_r orchard_internal_params)
        (read_scalar_from_windows Γ CIR 85)).
  Proof.
    apply (table_us_free_of_oncurve
      (OrchardCircuitSpec.commit_ivk_r orchard_internal_params)
      (read_scalar_from_windows Γ CIR 85)
      (read_us Γ CIR 85)
      OrchardActionFixedBase.fixed_window_default).
    - rewrite OrchardActionUsFree.read_us_length,
        CommitIvkHash.commit_ivk_r_table_length.
      reflexivity.
    - intros i Hi.
      rewrite CommitIvkHash.commit_ivk_r_table_length in Hi.
      split.
      + cbv zeta.
        exact (OrchardActionUsFree.full_width_spec_window_on_curve Γ CIR
          Garden.Orchard.constants.fixed_bases.commit_ivk_r.full_fixed_rows
          CommitIvkHash.commit_ivk_r_rows_standard
          CommitIvkHash.commit_ivk_r_rows_length
          (CommitIvkHash.commit_ivk_r_incomplete_facts Γ Hcircuit)
          (OrchardActionFixedBase.holds_gates Γ Hcircuit)
          i Hi).
      + apply (window_disc_qr_commit_ivk_r_all_Z i).
        * exact Hi.
        * unfold EccSpec.window_digit. apply Z.mod_pos_bound. lia.
  Qed.

  (** The blinding leg in protocol form: the CommitIvkR fold at the read
      scalar/us is the group multiple [mul_commit_ivk_r rivk]. *)
  Lemma commit_ivk_r_mul_leg
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    EccSpec.fixed_scalar_mul
      (OrchardCircuitSpec.commit_ivk_r orchard_internal_params)
      (read_scalar_from_windows Γ CIR 85)
      (read_us Γ CIR 85) =
    OrchardProtocolSpec.mul_commit_ivk_r
      (read_scalar_from_windows Γ CIR 85).
  Proof.
    rewrite (commit_ivk_r_us_eq Γ Hcircuit).
    exact (CommitIvkRMulProtocol.commit_ivk_r_mul_protocol
      (read_scalar_from_windows Γ CIR 85)
      (read_rivk_range Γ Hcircuit)).
  Qed.

  (** ** The ivk scalar: the [CompletePointAdd] x-cell is [Commit^ivk] *)

  (** The ivk output point's x-cell — [commit_ivk.synthesize]'s returned
      record does not depend on the [ak]/[nk] argument cells. *)
  Lemma civk_x_cell (ak nk : Garden.Halo2.Synthesis.Cell.t columns RegionId.t) :
    (Garden.Orchard.circuit.commit_ivk.AssignedPoint.x
      (layouter_value (Garden.Orchard.circuit.commit_ivk.synthesize ak nk))) =
    Garden.Halo2.Synthesis.Cell.advice
      (RegionId.CommitIvk RegionId.CommitIvk.CompletePointAdd) Advice.A2 1.
  Proof. reflexivity. Qed.

  (** ... and its evaluation is exactly the scalar cell the variable-base
      [mul] chip consumes ([VarBaseMul.alpha_value]). *)
  Lemma alpha_of_civk
      (Γ : Assignment.t columns RegionId.t)
      (ak nk : Garden.Halo2.Synthesis.Cell.t columns RegionId.t) :
    Point.x
      (Field.map_mod
        (CommitIvkHash.civk_point_value Γ
          (layouter_value (Garden.Orchard.circuit.commit_ivk.synthesize ak nk)))) =
    VarBaseMul.alpha_value Γ.
  Proof.
    unfold VarBaseMul.alpha_value, read_advice, CommitIvkHash.civk_point_value.
    rewrite (civk_x_cell ak nk).
    cbn [Field.map_mod Point.IsMapMod Point.x Point.y eval_cell
      eval_expression rotated_row Rotation.cur].
    unfold VarBaseMul.ivk_add_region; cbn; reflexivity.
  Qed.

  (** The scalar cell equals [OrchardProtocolSpec.commit_ivk] of the
      witnessed [ak] x-coordinate, [nk] and the windowed [rivk] — the
      [CommitIvkHash] chain with [Hdistinct] discharged and the blinding
      fold switched to the group multiple. *)
  Lemma ivk_scalar_correct
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (Hnondeg :
        SinsemillaHash.nondegenerate
          (OrchardSpec.commit_ivk_q orchard_circuit_params)
          (CommitIvkHash.commit_ivk_words Γ))
      (Hshort : CommitIvkHash.commit_ivk_short_lookup_ok Γ) :
    VarBaseMul.alpha_value Γ =
    OrchardProtocolSpec.commit_ivk orchard_circuit_params
      (EccSpec.extract_x (OrchardSpec.in_ak (read_action_inputs Γ)))
      (OrchardSpec.in_nk (read_action_inputs Γ))
      (read_scalar_from_windows Γ CIR 85).
  Proof.
    assert (HnondegQ :
        SinsemillaHash.nondegenerate CommitIvkHash.commit_ivk_Q
          (CommitIvkHash.commit_ivk_words Γ)).
    { rewrite CommitIvkHash.commit_ivk_Q_eq. exact Hnondeg. }
    pose proof
      (CommitIvkHash.commit_ivk_point_correct Γ Hcircuit HnondegQ
        (commit_ivk_r_distinct_holds Γ Hcircuit)
        CommitIvkHash.ak_cell CommitIvkHash.nk_cell) as H.
    rewrite (CommitIvkHash.commit_ivk_words_correct Γ Hcircuit Hshort) in H.
    rewrite (commit_ivk_r_mul_leg Γ Hcircuit) in H.
    unfold OrchardProtocolSpec.commit_ivk.
    rewrite <- H.
    symmetry.
    exact (alpha_of_civk Γ CommitIvkHash.ak_cell CommitIvkHash.nk_cell).
  Qed.

  (** ** The witnessed base: [g_d_old] is a reduced affine on-curve
      non-identity point ([QWitnessPointNonId] at the [GDOld] region) *)

  Lemma g_d_old_curve_eqn
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    Γ ⊢ ⟦ Garden.Halo2.halo2_gadgets.ecc.chip.witness_point
        .curve_eqn Advice.A0 Advice.A1 ⟧
      (Garden.Orchard.circuit.witness_input_region
        RegionId.WitnessInput.GDOld, 0) = 0.
  Proof.
    destruct Hcircuit as [Hfacts HSatisfies].
    destruct HSatisfies as [Hgates Hlookups].
    apply (OrchardActionFixedBase.witness_non_identity_point_on_curve Γ
      (Garden.Orchard.circuit.witness_input_region RegionId.WitnessInput.GDOld)
      "gd_old").
    - pose proof Hfacts as Hgd_facts.
      unfold Garden.Orchard.circuit.synthesize in Hgd_facts.
      apply interpret_layouter_facts_bind_right in Hgd_facts.
      apply interpret_layouter_facts_bind_left in Hgd_facts.
      unfold Garden.Orchard.circuit.synthesize_witness_inputs in Hgd_facts.
      do 3 apply interpret_layouter_facts_bind_right in Hgd_facts.
      apply interpret_layouter_facts_bind_left in Hgd_facts.
      exact Hgd_facts.
    - exact Hgates.
  Qed.

  Lemma base_point_facts
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    Pallas.reduced (VarBaseMul.base_wpoint Γ) /\
    Pallas.on_curve (VarBaseMul.base_wpoint Γ) /\
    VarBaseMul.base_wpoint Γ <> Pallas.identity.
  Proof.
    pose proof (g_d_old_curve_eqn Γ Hcircuit) as Hcurve.
    unfold Garden.Halo2.halo2_gadgets.ecc.chip.witness_point.curve_eqn,
      Garden.Halo2.halo2_gadgets.utilities.square in Hcurve.
    cbn [Evaluation.eval ExpressionIsEvaluable eval_expression rotated_row
      Rotation.cur] in Hcurve.
    change (rotated_row 0 Rotation.cur) with 0 in Hcurve.
    change (Garden.Orchard.circuit.witness_input_region RegionId.WitnessInput.GDOld)
      with (RegionId.WitnessInput RegionId.WitnessInput.GDOld) in Hcurve.
    assert (Hb_red : UnOp.from Garden.Halo2.halo2_gadgets.ecc.chip.constants.pallas_b
      = Garden.Halo2.halo2_gadgets.ecc.chip.constants.pallas_b)
      by (vm_compute; reflexivity).
    rewrite Hb_red in Hcurve.
    set (x := UnOp.from
      (Γ.(Assignment.advice) Advice.A0
        (RegionId.WitnessInput RegionId.WitnessInput.GDOld) 0)) in Hcurve.
    set (y := UnOp.from
      (Γ.(Assignment.advice) Advice.A1
        (RegionId.WitnessInput RegionId.WitnessInput.GDOld) 0)) in Hcurve.
    pose proof (EccSpec.pallas_curve_x_nonzero x y Hcurve) as Hxnz.
    assert (Hxr : UnOp.from x = x) by (subst x; apply FieldRewrite.from_from).
    assert (Hyr : UnOp.from y = y) by (subst y; apply FieldRewrite.from_from).
    assert (Hxne : x <> 0) by (rewrite <- Hxr; exact Hxnz).
    assert (Hbase : VarBaseMul.base_wpoint Γ = Weierstrass.Weierstrass.Affine x y).
    { unfold VarBaseMul.base_wpoint, VarBaseMul.base_point, VarBaseMul.gd_old_region,
        read_point, read, read1, read_advice, PallasModel.unrepr.
      cbn [Evaluation.eval ExpressionIsEvaluable eval_expression Point.x Point.y].
      change (rotated_row 0 Rotation.cur) with 0.
      fold x. fold y.
      destruct (Z.eqb_spec x 0) as [E|E].
      - exfalso. apply Hxne. exact E.
      - cbn [andb]. reflexivity. }
    rewrite Hbase.
    refine (conj _ (conj _ _)).
    - split; assumption.
    - exact (PallasModel.affine_on_curve_of_poly x y Hcurve).
    - intro Hid. discriminate Hid.
  Qed.

  (** ** The [AddressIntegrity.Equality] region: witnessed pk_d = computed *)

  Lemma pk_d_old_pinned
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    read_point Γ
      (RegionId.AddressIntegrity RegionId.AddressIntegrity.WitnessPkD) =
    VarBaseMul.result_point Γ.
  Proof.
    pose proof (holds_facts Γ Hcircuit) as Hfacts.
    unfold Garden.Orchard.circuit.synthesize in Hfacts.
    do 7 apply interpret_layouter_facts_bind_right in Hfacts.
    apply interpret_layouter_facts_bind_left in Hfacts.
    unfold Garden.Orchard.circuit.synthesize_address_integrity in Hfacts.
    do 5 apply interpret_layouter_facts_bind_right in Hfacts.
    apply interpret_layouter_facts_bind_left in Hfacts.
    apply interpret_layouter_facts_in_namespace in Hfacts.
    apply interpret_layouter_facts_add_region in Hfacts.
    pose proof Hfacts as Hcx.
    apply interpret_region_facts_bind_left in Hcx.
    cbn [region_facts interpret_facts interpret_fact eval_cell] in Hcx.
    destruct Hcx as [Hcx _].
    cbn in Hcx.
    pose proof Hfacts as Hcy.
    apply interpret_region_facts_bind_right in Hcy.
    apply interpret_region_facts_bind_left in Hcy.
    cbn [region_facts interpret_facts interpret_fact eval_cell] in Hcy.
    destruct Hcy as [Hcy _].
    cbn in Hcy.
    clear Hfacts.
    unfold VarBaseMul.result_point, VarBaseMul.av, VarBaseMul.mul_region,
      read_point, read, read1, read_advice.
    cbn [Evaluation.eval ExpressionIsEvaluable eval_expression Point.x Point.y].
    change (rotated_row 0 Rotation.cur) with 0.
    change (rotated_row 136 Rotation.cur) with 136.
    change (RegionId.AddressIntegrity RegionId.AddressIntegrity.WitnessPkD)
      with (Garden.Orchard.circuit.address_integrity_region
        RegionId.AddressIntegrity.WitnessPkD).
    change (RegionId.AddressIntegrity
        (RegionId.AddressIntegrity.Mul RegionId.AddressIntegrity.Mul.VariableBase))
      with (Garden.Orchard.circuit.address_integrity_mul_region
        RegionId.AddressIntegrity.Mul.VariableBase).
    rewrite <- Hcx, <- Hcy.
    reflexivity.
  Qed.

  (** ** The capstone

      The readers, byte-identical to
      [OrchardValidActionInputs.read_pk_d_old]/[read_rivk] (this file stays
      upstream: no [Require] of [valid_action_inputs.v]). *)
  Definition read_pk_d_old (Γ : Assignment.t columns RegionId.t) : Point.t :=
    read_point Γ
      (RegionId.AddressIntegrity RegionId.AddressIntegrity.WitnessPkD).
  Definition read_rivk (Γ : Assignment.t columns RegionId.t) : Z :=
    read_scalar_from_windows Γ
      (RegionId.CommitIvk RegionId.CommitIvk.FixedBaseIncomplete) 85.

  Lemma base_wpoint_read (Γ : Assignment.t columns RegionId.t) :
    VarBaseMul.base_wpoint Γ =
    PallasModel.unrepr (OrchardSpec.in_g_d_old (read_action_inputs Γ)).
  Proof. reflexivity. Qed.

  Lemma read_rivk_eq (Γ : Assignment.t columns RegionId.t) :
    read_rivk Γ = read_scalar_from_windows Γ CIR 85.
  Proof. reflexivity. Qed.

  (** §4.18.4 'Diversified address integrity', honest branch — the exact
      conclusion of
      [OrchardValidActionInputs.diversified_address_integrity]. *)
  Theorem diversified_address_integrity
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (Hnondeg :
        SinsemillaHash.nondegenerate
          (OrchardSpec.commit_ivk_q orchard_circuit_params)
          (CommitIvkHash.commit_ivk_words Γ))
      (Hshort : CommitIvkHash.commit_ivk_short_lookup_ok Γ)
      (Hmulnd : VarBaseMul.mul_nondegenerate Γ)
      (Horder :
        Pallas.mul Pallas.pallas_q (VarBaseMul.base_wpoint Γ) =
        Pallas.identity) :
    read_pk_d_old Γ =
    PallasModel.repr
      (Pallas.mul
        (OrchardProtocolSpec.commit_ivk orchard_circuit_params
          (EccSpec.extract_x (OrchardSpec.in_ak (read_action_inputs Γ)))
          (OrchardSpec.in_nk (read_action_inputs Γ))
          (read_rivk Γ))
        (PallasModel.unrepr (OrchardSpec.in_g_d_old (read_action_inputs Γ)))).
  Proof.
    destruct (base_point_facts Γ Hcircuit) as (HBred & HBoc & HBne).
    unfold read_pk_d_old.
    rewrite (pk_d_old_pinned Γ Hcircuit).
    rewrite (VarBaseMul.address_integrity_mul_correct Γ Hcircuit
      HBred HBoc HBne Horder Hmulnd).
    rewrite (ivk_scalar_correct Γ Hcircuit Hnondeg Hshort).
    rewrite <- (base_wpoint_read Γ).
    rewrite (read_rivk_eq Γ).
    reflexivity.
  Qed.

  (** ** The bundled witness-honesty side condition

      The refinement target for
      [OrchardValidActionInputs.commit_ivk_witness_ok]: the Sinsemilla
      nondegeneracy + short-lookup shape of the other honesty predicates,
      extended by the two variable-base-mul side conditions surfaced in
      [VarBaseMul] — the incomplete-add nondegeneracy (genuine witness
      honesty) and the base-order fact (a curve-cardinality truth carried as
      a hypothesis until certified; see the header). *)
  Definition commit_ivk_witness_ok
      (Γ : Assignment.t columns RegionId.t) : Prop :=
    SinsemillaHash.nondegenerate
      (OrchardSpec.commit_ivk_q orchard_circuit_params)
      (CommitIvkHash.commit_ivk_words Γ) /\
    CommitIvkHash.commit_ivk_short_lookup_ok Γ /\
    VarBaseMul.mul_nondegenerate Γ /\
    Pallas.mul Pallas.pallas_q (VarBaseMul.base_wpoint Γ) = Pallas.identity.

  Theorem diversified_address_integrity_of_witness_ok
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
    destruct Hok as (Hnondeg & Hshort & Hmulnd & Horder).
    exact (diversified_address_integrity Γ Hcircuit
      Hnondeg Hshort Hmulnd Horder).
  Qed.

End DiversifiedAddress.
