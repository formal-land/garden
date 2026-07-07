(** * NullifierK K-out: the [Hfixed] and [Hcomm_x] hypotheses of
    [nf_old_correct_of_fixed_base] from [Holds] alone, and the closed
    [NF_OLD] output correctness.

    The base-field (85-window) counterpart of
    [ValueCommitROut] ([circuit_proof/value_commit_r/out.v]).
    Composes:
    - the base-field structure wrapper
      [BaseFieldFixedBaseStructure
        .base_field_nullifier_k_scalar_mul_correct]
      ([circuit_proof/fixed_base/base_field.v]) with the whole-program facts
      [BaseFieldCanonicity.nullifier_k_mul_facts];
    - the per-window spec-table match at the spec scalar
      [poseidon_hash2 nk rho_old +F psi_old]
      ([OrchardActionUsFreeNullifierK.nullifier_k_table_window_correct],
      the canonicity digit match composed with Poseidon soundness);
    - the ladder-distinctness certificate
      [NullifierKLadder.nullifier_k_distinct_holds]
      ([circuit_proof/ladder/nullifier_k.v]), lifted into
      the complete and plain incomplete-additions preconditions;
    - the complete-addition commutativity on the closed domain
      {curve points} ∪ {identity} on BOTH operands
      ([point_add_comm_curve_or_identity_both]): the [cm_old] witness point
      is only constrained to curve-or-(0,0) ([cm_old_witness_sound]), and the
      fixed-base multiple can be the identity (the [scalar ≡ 0] windows-cancel
      case), so the [rk]-leg form (second operand strictly on curve) does not
      apply.

    The final theorems: [nf_old_correct_of_holds] (the [NF_OLD] public
    instance equals the spec nullifier) and [nullifier_cell_correct] (the
    [synthesize_nullifier] output cell — the [rho_new] fed to the new-note
    commitment — carries the same value), the latter stated for reuse by the
    CMX bridge. *)

Require Import Garden.Halo2.main.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.lemmas.
Require Import Garden.Orchard.columns.
Require Garden.Orchard.circuit.
Require Garden.Orchard.constants.fixed_bases.nullifier_k.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.spec.
Require Import Garden.Halo2.halo2_gadgets.poseidon.spec.
Require Import Garden.Halo2.PallasModel.
Require Import Garden.Orchard.circuit_spec.
Require Import Garden.Orchard.circuit_proof.inputs.
Require Import Garden.Orchard.circuit_proof.facts.
Require Import Garden.Orchard.circuit_proof.fixed_base.main.
Require Import Garden.Orchard.circuit_proof.fixed_base.base_field.
Require Import Garden.Orchard.circuit_proof.base_field_canonicity.
Require Import Garden.Orchard.circuit_proof.us_free.nullifier_k.
Require Import Garden.Orchard.circuit_proof.ladder.nullifier_k.
Require Import Garden.Orchard.circuit_proof.bridges.
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


Module NullifierKOut.
  Import OrchardActionFixedBase.

  (* Keep the square-root / QR chain opaque to the conversion oracle (the
     consumed ladder and window lemmas mention these constants over the
     concrete Pallas modulus). *)
  Strategy opaque
    [is_square modpow modpow_pos field_sqrt fixed_window_point_canonical].

  Local Notation Holds Γ :=
    (circuit_holds Γ
      Garden.Orchard.circuit.synthesize
      (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)).

  Local Notation bf_region :=
    (RegionId.Nullifier RegionId.Nullifier.BaseFieldIncomplete).
  Local Notation scalar_add_region :=
    (RegionId.Nullifier RegionId.Nullifier.ScalarAdd).

  (** The base-field scalar as the spec computes it from the read-out inputs:
      the base-field sum of the Poseidon PRF output and [psi_old]. *)
  Local Notation nf_scalar Γ :=
    (Poseidon.poseidon_hash2
      (read Γ (RegionId.WitnessInput RegionId.WitnessInput.Nk))
      (read Γ (RegionId.WitnessInput RegionId.WitnessInput.RhoOld)) +F
      read Γ (RegionId.WitnessInput RegionId.WitnessInput.PsiOld)).

  (* ---------------------------------------------------------------------- *)
  (* Table split of the 85-window NullifierK spec table.                     *)
  (* ---------------------------------------------------------------------- *)

  Definition nullifier_k_first : EccSpec.fixed_window :=
    List.hd fixed_window_default
      (OrchardSpec.nullifier_k orchard_circuit_params).

  Definition nullifier_k_middle : EccSpec.fixed_table :=
    List.firstn 83
      (List.skipn 1 (OrchardSpec.nullifier_k orchard_circuit_params)).

  Definition nullifier_k_last : EccSpec.fixed_window :=
    List.nth 84 (OrchardSpec.nullifier_k orchard_circuit_params)
      fixed_window_default.

  Lemma nullifier_k_spec_table_split :
    OrchardSpec.nullifier_k orchard_circuit_params =
    nullifier_k_first :: nullifier_k_middle ++ [nullifier_k_last].
  Proof. reflexivity. Qed.

  Lemma nullifier_k_middle_length :
    List.length nullifier_k_middle = 83%nat.
  Proof. reflexivity. Qed.

  (* ---------------------------------------------------------------------- *)
  (* Per-window correctness against the split spec table (nth_error form).   *)
  (* ---------------------------------------------------------------------- *)

  Lemma nullifier_k_window_correct
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (j : nat) (w : EccSpec.fixed_window)
      (Hnth :
        List.nth_error
          (nullifier_k_first :: nullifier_k_middle ++ [nullifier_k_last])
          j = Some w) :
    incomplete_additions_window_point Γ bf_region (Z.of_nat j) =
    EccSpec.fixed_window_point w
      (EccSpec.window_digit (nf_scalar Γ) j)
      (List.nth j (read_us Γ bf_region 85) 0).
  Proof.
    rewrite <- nullifier_k_spec_table_split in Hnth.
    assert (Hj : (j < 85)%nat).
    { pose proof (proj1 (List.nth_error_Some
        (OrchardSpec.nullifier_k orchard_circuit_params) j)) as Hlt.
      rewrite OrchardActionUsFreeNullifierK.nullifier_k_table_length in Hlt.
      apply Hlt.
      rewrite Hnth.
      discriminate. }
    apply List.nth_error_nth with (d := fixed_window_default) in Hnth.
    rewrite <- Hnth.
    exact (OrchardActionUsFreeNullifierK.nullifier_k_table_window_correct
      Γ Hcircuit j Hj).
  Qed.

  (* ---------------------------------------------------------------------- *)
  (* Window on-curve and x-nonzero facts of the base-field region.           *)
  (* ---------------------------------------------------------------------- *)

  Lemma nullifier_k_window_on_curve
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (i : nat) (Hi : (i < 85)%nat) :
    point_on_curve
      (incomplete_additions_window_point Γ bf_region (Z.of_nat i)).
  Proof.
    apply (base_field_incomplete_region_window_on_curve Γ bf_region
      (Garden.Halo2.Synthesis.Cell.advice scalar_add_region Advice.A6 0) i
      (BaseFieldCanonicity.nullifier_k_incomplete_facts Γ Hcircuit)
      (holds_gates Γ Hcircuit)
      Hi).
  Qed.

  Lemma nullifier_k_window_x_nonzero
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (i : nat) (Hi : (i < 85)%nat) :
    UnOp.from
      (Point.x
        (incomplete_additions_window_point Γ bf_region (Z.of_nat i))) <> 0.
  Proof.
    pose proof (nullifier_k_window_on_curve Γ Hcircuit i Hi) as Honc.
    unfold point_on_curve in Honc.
    exact (EccSpec.pallas_curve_x_nonzero
      (Point.x (incomplete_additions_window_point Γ bf_region (Z.of_nat i)))
      (Point.y (incomplete_additions_window_point Γ bf_region (Z.of_nat i)))
      Honc).
  Qed.

  (* ---------------------------------------------------------------------- *)
  (* The incomplete-additions preconditions from [Holds] (via the           *)
  (* ladder-distinctness certificate).                                       *)
  (* ---------------------------------------------------------------------- *)

  Lemma nullifier_k_complete_of_holds
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    incomplete_additions_complete_precondition Γ bf_region 1 83
      (incomplete_additions_window_point Γ bf_region 0).
  Proof.
    apply incomplete_complete_precondition_of_distinct.
    - replace 0 with (Z.of_nat 0) by reflexivity.
      apply (nullifier_k_window_on_curve Γ Hcircuit 0%nat).
      lia.
    - replace 0 with (Z.of_nat 0) by reflexivity.
      apply (nullifier_k_window_x_nonzero Γ Hcircuit 0%nat).
      lia.
    - intros i Hi.
      replace (1 + Z.of_nat i) with (Z.of_nat (S i)) by lia.
      apply (nullifier_k_window_on_curve Γ Hcircuit (S i)).
      lia.
    - intros i Hi.
      replace (1 + Z.of_nat i) with (Z.of_nat (S i)) by lia.
      apply (nullifier_k_window_x_nonzero Γ Hcircuit (S i)).
      lia.
    - exact
        (NullifierKLadder.nullifier_k_distinct_holds
          Γ Hcircuit).
  Qed.

  Lemma nullifier_k_incomplete_of_holds
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    incomplete_additions_precondition Γ bf_region 1 83
      (incomplete_additions_window_point Γ bf_region 0).
  Proof.
    apply incomplete_complete_implies_precondition.
    exact (nullifier_k_complete_of_holds Γ Hcircuit).
  Qed.

  (* ---------------------------------------------------------------------- *)
  (* The circuit precondition at the spec scalar.                            *)
  (* ---------------------------------------------------------------------- *)

  Lemma nullifier_k_circuit_precondition_of_holds
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    fixed_scalar_mul_circuit_precondition
      (OrchardSpec.nullifier_k orchard_circuit_params)
      (nf_scalar Γ)
      (read_us Γ bf_region 85).
  Proof.
    pose proof (nullifier_k_window_correct Γ Hcircuit 0%nat
      nullifier_k_first eq_refl) as Hfirst.
    rewrite nullifier_k_spec_table_split.
    cbn [fixed_scalar_mul_circuit_precondition].
    rewrite <- Hfirst.
    eapply circuit_tail_precondition_of_complete
      with (n := 83%nat).
    - rewrite List.length_app, nullifier_k_middle_length. reflexivity.
    - exact (nullifier_k_complete_of_holds Γ Hcircuit).
    - intros j w Hnth.
      replace (1 + Z.of_nat j) with (Z.of_nat (S j)) by lia.
      replace (1 + j)%nat with (S j) by lia.
      apply (nullifier_k_window_correct Γ Hcircuit).
      cbn [List.nth_error].
      exact Hnth.
    - apply (nullifier_k_window_on_curve Γ Hcircuit 0%nat).
      lia.
    - exact (proj1 (incomplete_additions_window_point_reduced Γ bf_region
        (Z.of_nat 0))).
    - exact (proj2 (incomplete_additions_window_point_reduced Γ bf_region
        (Z.of_nat 0))).
    - intros j Hj.
      rewrite List.length_app, nullifier_k_middle_length in Hj.
      cbn [List.length] in Hj.
      replace (1 + Z.of_nat j) with (Z.of_nat (S j)) by lia.
      apply (nullifier_k_window_on_curve Γ Hcircuit (S j)).
      lia.
    - intros j Hj.
      exact (proj1 (incomplete_additions_window_point_reduced Γ bf_region
        (1 + Z.of_nat j))).
    - intros j Hj.
      exact (proj2 (incomplete_additions_window_point_reduced Γ bf_region
        (1 + Z.of_nat j))).
  Qed.

  (* ---------------------------------------------------------------------- *)
  (* Hfixed: the program output is the spec fixed-base multiple.             *)
  (* ---------------------------------------------------------------------- *)

  (** The [Hfixed] core, stated at the concrete scalar cell ([A6[0]] of the
      [ScalarAdd] region — the value [synthesize_nullifier] pipes into the
      base-field multiplication). *)
  Lemma nullifier_k_hfixed_cell
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    Field.map_mod
      (assigned_point_value Γ
        (layouter_value
          (Garden.Orchard.circuit.synth_nullifier_k_mul
            (Garden.Halo2.Synthesis.Cell.advice scalar_add_region
              Advice.A6 0)))) =
    EccSpec.fixed_scalar_mul
      (OrchardSpec.nullifier_k orchard_circuit_params)
      (nf_scalar Γ)
      (read_us Γ bf_region 85).
  Proof.
    rewrite nullifier_k_spec_table_split.
    eapply
      BaseFieldFixedBaseStructure
        .base_field_nullifier_k_scalar_mul_correct
      with (first := nullifier_k_first)
           (middle := nullifier_k_middle)
           (last := nullifier_k_last).
    - exact (BaseFieldCanonicity.nullifier_k_mul_facts Γ Hcircuit).
    - exact (holds_gates Γ Hcircuit).
    - exact
        (nullifier_k_incomplete_of_holds Γ Hcircuit).
    - exact nullifier_k_middle_length.
    - intros j w Hnth.
      exact (nullifier_k_window_correct Γ Hcircuit j w Hnth).
    - rewrite <- nullifier_k_spec_table_split.
      exact
        (nullifier_k_circuit_precondition_of_holds
          Γ Hcircuit).
  Qed.

  (** [Hfixed] verbatim as [nf_old_correct_of_fixed_base]
      ([circuit_proof/bridges.v]) expects it: the scalar spelled as the
      [synthesize_scalar_add] layouter value over the Poseidon hash output and
      the [psi_old] witness cell. *)
  Lemma nullifier_k_hfixed
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
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
    let nk :=
      layouter_value
        (Garden.Orchard.circuit.assign_free_advice
          (Garden.Orchard.circuit.witness_input_region
            RegionId.WitnessInput.Nk)
          "witness nk" Advice.A0 0) in
    let poseidon_output :=
      layouter_value
        (Garden.Halo2.halo2_gadgets.poseidon.pow5.synthesize_hash
          nk rho_old) in
    let scalar :=
      layouter_value
        (Garden.Orchard.circuit.synthesize_scalar_add
          (Garden.Orchard.circuit.nullifier_region
            RegionId.Nullifier.ScalarAdd)
          "scalar = poseidon_hash(nk, rho) + psi"
          poseidon_output
          psi_old) in
    Field.map_mod
      (assigned_point_value Γ
        (layouter_value
          (Garden.Orchard.circuit
            .synth_nullifier_k_mul scalar))) =
    EccSpec.fixed_scalar_mul
      (OrchardSpec.nullifier_k orchard_circuit_params)
      (Poseidon.poseidon_hash2
        (read Γ (RegionId.WitnessInput RegionId.WitnessInput.Nk))
        (read Γ (RegionId.WitnessInput RegionId.WitnessInput.RhoOld)) +F
       read Γ (RegionId.WitnessInput RegionId.WitnessInput.PsiOld))
      (read_us Γ
        (RegionId.Nullifier RegionId.Nullifier.BaseFieldIncomplete) 85).
  Proof.
    cbv zeta.
    exact (nullifier_k_hfixed_cell Γ Hcircuit).
  Qed.

  (* ---------------------------------------------------------------------- *)
  (* Curve-or-identity and reducedness of the fixed-base multiple.           *)
  (* ---------------------------------------------------------------------- *)

  (** The NullifierK fixed-base multiple is on the curve OR is the [(0, 0)]
      identity (the [scalar ≡ 0] windows-cancel case).  The base-field
      counterpart of [spend_auth_g_mul_curve_poly_or_identity]. *)
  Lemma nullifier_k_mul_curve_poly_or_identity
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    point_on_curve
      (EccSpec.fixed_scalar_mul
        (OrchardSpec.nullifier_k orchard_circuit_params)
        (nf_scalar Γ)
        (read_us Γ bf_region 85)) \/
    EccSpec.fixed_scalar_mul
      (OrchardSpec.nullifier_k orchard_circuit_params)
      (nf_scalar Γ)
      (read_us Γ bf_region 85) = EccSpec.identity.
  Proof.
    pose proof (nullifier_k_complete_of_holds Γ Hcircuit)
      as Hladder.
    pose proof
      (complete_additions_output_reduced Γ bf_region 1 83
        (incomplete_additions_window_point Γ bf_region 0)
        (proj1 (incomplete_additions_window_point_reduced Γ bf_region 0))
        (proj2 (incomplete_additions_window_point_reduced Γ bf_region 0)))
      as [Hacc_xr Hacc_yr].
    assert (Hacc_curve :
        point_on_curve
          (complete_additions_output Γ bf_region 1 83
            (incomplete_additions_window_point Γ bf_region 0))).
    { apply complete_additions_output_on_curve.
      - replace 0 with (Z.of_nat 0) by reflexivity.
        apply (nullifier_k_window_on_curve Γ Hcircuit 0%nat).
        lia.
      - intros i Hi.
        replace (1 + Z.of_nat i) with (Z.of_nat (S i)) by lia.
        apply (nullifier_k_window_on_curve Γ Hcircuit (S i)).
        lia.
      - exact Hladder. }
    assert (Hlast_curve :
        point_on_curve (incomplete_additions_window_point Γ bf_region 84)).
    { replace 84 with (Z.of_nat 84) by reflexivity.
      apply (nullifier_k_window_on_curve Γ Hcircuit 84%nat).
      lia. }
    pose proof (incomplete_additions_window_point_reduced Γ bf_region 84)
      as [Hlast_xr Hlast_yr].
    pose proof
      (BaseFieldFixedBaseStructure
        .base_field_nullifier_k_correct Γ
        (Garden.Halo2.Synthesis.Cell.advice scalar_add_region Advice.A6 0)
        (BaseFieldCanonicity.nullifier_k_mul_facts Γ Hcircuit)
        (holds_gates Γ Hcircuit)
        (nullifier_k_incomplete_of_holds Γ Hcircuit))
      as Hcomplete.
    rewrite (incomplete_output_eq_complete_output Γ
      bf_region 1 83
      (incomplete_additions_window_point Γ bf_region 0) Hladder)
      in Hcomplete.
    rewrite <- (nullifier_k_hfixed_cell Γ Hcircuit).
    rewrite Hcomplete.
    exact (PallasModel.point_add_curve_poly_or_identity
      (incomplete_additions_window_point Γ bf_region 84)
      (complete_additions_output Γ bf_region 1 83
        (incomplete_additions_window_point Γ bf_region 0))
      Hlast_xr Hlast_yr Hacc_xr Hacc_yr Hlast_curve Hacc_curve).
  Qed.

  Lemma nullifier_k_fixed_scalar_mul_x_reduced
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    UnOp.from
      (Point.x
        (EccSpec.fixed_scalar_mul
          (OrchardSpec.nullifier_k orchard_circuit_params)
          (nf_scalar Γ)
          (read_us Γ bf_region 85))) =
    Point.x
      (EccSpec.fixed_scalar_mul
        (OrchardSpec.nullifier_k orchard_circuit_params)
        (nf_scalar Γ)
        (read_us Γ bf_region 85)).
  Proof.
    eapply OrchardActionBridges.point_map_mod_x_reduced_of_eq.
    exact (nullifier_k_hfixed_cell Γ Hcircuit).
  Qed.

  Lemma nullifier_k_fixed_scalar_mul_y_reduced
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    UnOp.from
      (Point.y
        (EccSpec.fixed_scalar_mul
          (OrchardSpec.nullifier_k orchard_circuit_params)
          (nf_scalar Γ)
          (read_us Γ bf_region 85))) =
    Point.y
      (EccSpec.fixed_scalar_mul
        (OrchardSpec.nullifier_k orchard_circuit_params)
        (nf_scalar Γ)
        (read_us Γ bf_region 85)).
  Proof.
    eapply OrchardActionBridges.point_map_mod_y_reduced_of_eq.
    exact (nullifier_k_hfixed_cell Γ Hcircuit).
  Qed.

  (* ---------------------------------------------------------------------- *)
  (* The [cm_old] witness point: curve-or-identity.                          *)
  (* ---------------------------------------------------------------------- *)

  (** [cm_old] is witnessed through [witness_point], whose gate constrains it
      to the curve OR to the [(0, 0)] sentinel — unlike the non-identity
      witness used for [ak]. *)
  Lemma cm_old_point_curve_or_identity
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    point_on_curve
      (read_point Γ (RegionId.WitnessInput RegionId.WitnessInput.CmOld)) \/
    read_point Γ (RegionId.WitnessInput RegionId.WitnessInput.CmOld) =
      EccSpec.identity.
  Proof.
    destruct (cm_old_witness_sound Γ Hcircuit) as [ [Hx Hy] | Hcurve].
    - right.
      unfold read_point, read, read1, read_advice, EccSpec.identity.
      f_equal.
      + exact Hx.
      + exact Hy.
    - left.
      unfold point_on_curve, read_point, read, read1, read_advice.
      change (Γ ⊢ ⟦ Garden.Halo2.halo2_gadgets.ecc.chip.witness_point
          .curve_eqn Advice.A0 Advice.A1 ⟧
        (Garden.Orchard.circuit.witness_input_region
          RegionId.WitnessInput.CmOld, 0) = 0).
      exact Hcurve.
  Qed.

  (* ---------------------------------------------------------------------- *)
  (* Complete-addition commutativity with identity allowed on BOTH sides.    *)
  (* ---------------------------------------------------------------------- *)

  (** [point_add P Q = point_add Q P] when each operand is on-curve or the
      identity and both are reduced.  Extends
      [point_add_comm_curve_or_identity_reduced] (which requires [Q] strictly
      on curve) with the [Q = identity] cases. *)
  Lemma point_add_comm_curve_or_identity_both (P Q : Point.t)
      (HP : point_on_curve P \/ P = EccSpec.identity)
      (HQ : point_on_curve Q \/ Q = EccSpec.identity)
      (HPxr : UnOp.from (Point.x P) = Point.x P)
      (HPyr : UnOp.from (Point.y P) = Point.y P)
      (HQxr : UnOp.from (Point.x Q) = Point.x Q)
      (HQyr : UnOp.from (Point.y Q) = Point.y Q) :
    EccSpec.point_add P Q = EccSpec.point_add Q P.
  Proof.
    destruct HQ as [HQcurve | HQid].
    - exact (OrchardActionBridges.point_add_comm_curve_or_identity_reduced
        P Q HP HQcurve HPxr HPyr HQxr HQyr).
    - subst Q.
      rewrite EccSpec.point_add_identity_left.
      destruct HP as [HPcurve | HPid].
      + apply OrchardActionBridges.point_add_identity_right.
        * exact HPxr.
        * apply (EccSpec.pallas_curve_x_nonzero (Point.x P) (Point.y P)).
          exact HPcurve.
      + subst P.
        rewrite EccSpec.point_add_identity_left.
        reflexivity.
  Qed.

  Lemma point_add_comm_curve_or_identity_both_x (P Q : Point.t)
      (HP : point_on_curve P \/ P = EccSpec.identity)
      (HQ : point_on_curve Q \/ Q = EccSpec.identity)
      (HPxr : UnOp.from (Point.x P) = Point.x P)
      (HPyr : UnOp.from (Point.y P) = Point.y P)
      (HQxr : UnOp.from (Point.x Q) = Point.x Q)
      (HQyr : UnOp.from (Point.y Q) = Point.y Q) :
    Point.x (EccSpec.point_add P Q) = Point.x (EccSpec.point_add Q P).
  Proof.
    exact (f_equal Point.x
      (point_add_comm_curve_or_identity_both P Q HP HQ
        HPxr HPyr HQxr HQyr)).
  Qed.

  (* ---------------------------------------------------------------------- *)
  (* Hcomm_x: the add-order swap of the NF_OLD complete addition.            *)
  (* ---------------------------------------------------------------------- *)

  (** [Hcomm_x] verbatim as [nf_old_correct_of_fixed_base] expects it: the
      circuit adds [cm_old + [scalar]·K], the spec adds
      [[scalar]·K + cm_old]. *)
  Lemma nullifier_k_point_add_comm_x
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    Point.x
      (EccSpec.point_add
        (read_point Γ
          (RegionId.WitnessInput RegionId.WitnessInput.CmOld))
        (EccSpec.fixed_scalar_mul
          (OrchardSpec.nullifier_k orchard_circuit_params)
          (Poseidon.poseidon_hash2
            (read Γ (RegionId.WitnessInput RegionId.WitnessInput.Nk))
            (read Γ (RegionId.WitnessInput RegionId.WitnessInput.RhoOld)) +F
           read Γ (RegionId.WitnessInput RegionId.WitnessInput.PsiOld))
          (read_us Γ
            (RegionId.Nullifier RegionId.Nullifier.BaseFieldIncomplete) 85))) =
    Point.x
      (EccSpec.point_add
        (EccSpec.fixed_scalar_mul
          (OrchardSpec.nullifier_k orchard_circuit_params)
          (Poseidon.poseidon_hash2
            (read Γ (RegionId.WitnessInput RegionId.WitnessInput.Nk))
            (read Γ (RegionId.WitnessInput RegionId.WitnessInput.RhoOld)) +F
           read Γ (RegionId.WitnessInput RegionId.WitnessInput.PsiOld))
          (read_us Γ
            (RegionId.Nullifier RegionId.Nullifier.BaseFieldIncomplete) 85))
        (read_point Γ
          (RegionId.WitnessInput RegionId.WitnessInput.CmOld))).
  Proof.
    apply point_add_comm_curve_or_identity_both_x.
    - exact (cm_old_point_curve_or_identity Γ Hcircuit).
    - exact (nullifier_k_mul_curve_poly_or_identity Γ Hcircuit).
    - exact (OrchardActionBridges.read_point_x_reduced Γ
        (RegionId.WitnessInput RegionId.WitnessInput.CmOld)).
    - exact (OrchardActionBridges.read_point_y_reduced Γ
        (RegionId.WitnessInput RegionId.WitnessInput.CmOld)).
    - exact (nullifier_k_fixed_scalar_mul_x_reduced Γ Hcircuit).
    - exact (nullifier_k_fixed_scalar_mul_y_reduced Γ Hcircuit).
  Qed.

  (* ---------------------------------------------------------------------- *)
  (* NF_OLD output correctness and the nullifier cell value.                 *)
  (* ---------------------------------------------------------------------- *)

  (** The [NF_OLD] public instance equals the spec nullifier — the
      [nf_old_correct_of_fixed_base] bridge with both hypotheses closed from
      [Holds]. *)
  Theorem nf_old_correct_of_holds
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    read_public_instance Γ Garden.Orchard.circuit.NF_OLD =
      OrchardSpec.out_nf_old (action_spec_of Γ).
  Proof.
    apply (OrchardActionBridges.nf_old_correct_of_fixed_base Γ Hcircuit).
    - exact (nullifier_k_hfixed Γ Hcircuit).
    - exact (nullifier_k_point_add_comm_x Γ Hcircuit).
  Qed.

  (** The [synthesize_nullifier] output cell — the [rho_new] value the
      new-note commitment consumes — carries the spec nullifier.  Stated on
      the same layouter values as the CMX bridge
      ([cmx_instance_eq_note_commit_new]) for direct
      reuse. *)
  Theorem nullifier_cell_correct
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
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
    UnOp.from
      (eval_cell Γ
        (layouter_value
          (Garden.Orchard.circuit.synthesize_nullifier
            rho_old psi_old nk cm_old))) =
    OrchardSpec.out_nf_old (action_spec_of Γ).
  Proof.
    cbv zeta.
    transitivity (read_public_instance Γ Garden.Orchard.circuit.NF_OLD).
    - symmetry.
      apply read_public_instance_eq_cell.
      pose proof (holds_facts Γ Hcircuit) as Hfacts.
      unfold Garden.Orchard.circuit.synthesize in Hfacts.
      do 5 apply interpret_layouter_facts_bind_right in Hfacts.
      apply interpret_layouter_facts_bind_left in Hfacts.
      cbn [layouter_facts interpret_facts interpret_fact eval_cell] in Hfacts.
      destruct Hfacts as [Hinstance _].
      exact Hinstance.
    - exact (nf_old_correct_of_holds Γ Hcircuit).
  Qed.

End NullifierKOut.
