(** * The [Ek] (nullifier_k) table equality and the final
    witness-elimination lemma [action_spec_us_free].

    [OrchardActionUsFree.action_spec_us_free_of_nullifier_k]
    ([circuit_proof/us_free/main.v]) reduces the witness elimination to the single
    [Ek] table equality — the base-field ([NullifierK]) fixed-base mul at the
    scalar [poseidon_hash2 nk rho_old +F psi_old], witnessed [u]-list versus
    canonical [u]-list.  This file discharges [Ek] from [Holds Γ]:

    - the scalar-value identification: the [ScalarAdd] region's output cell
      [A6[0]] carries [poseidon_hash2 nk rho_old +F psi_old] — Poseidon
      full-permutation soundness ([OrchardPoseidon.poseidon_hash_cell_correct])
      composed through the region's [QAdd] gate and the two [Copy] constraints
      feeding it ([nullifier_k_scalar_value]);
    - the base-field digit match: the canonical base-8 digits of the
      (reduced) scalar cell are the running-sum words of the
      [BaseFieldIncomplete] region
      ([BaseFieldCanonicity.nullifier_k_window_digit_scalar_cell]);
    - the per-window on-curve lift
      ([base_field_incomplete_region_window_on_curve]) and the
      non-residue certificate ([window_disc_qr_nullifier_k_all_Z]),
      assembled by [table_us_free_of_oncurve] exactly as in the four
      full-width/short legs of [circuit_proof/us_free/main.v].

    The final [action_spec_us_free] is then
    [action_spec_us_free_of_nullifier_k] applied to [nullifier_k_table_eq]. *)

Require Import Garden.Halo2.main.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.lemmas.
Require Import Garden.Orchard.columns.
Require Garden.Orchard.circuit.
Require Garden.Orchard.circuit.gadget.add_chip.
Require Import Garden.Orchard.circuit.gadget.add_chip_proof.
Require Garden.Orchard.constants.fixed_bases.nullifier_k.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.spec.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.window_disc.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.fixed_window_canonical.
Require Import Garden.Halo2.halo2_gadgets.poseidon.spec.
Require Import Garden.Orchard.protocol_spec.
Require Import Garden.Orchard.circuit_proof.internal_spec.
Require Import Garden.Orchard.circuit_proof.inputs.
Require Import Garden.Orchard.circuit_proof.facts.
Require Import Garden.Orchard.circuit_proof.fixed_base.main.
Require Import Garden.Orchard.circuit_proof.base_field_canonicity.
Require Import Garden.Orchard.circuit_proof.poseidon.
Require Import Garden.Orchard.circuit_proof.us_free.main.
Require Import Garden.Orchard.circuit_proof.nullifier_k.disc_cert.
Require Import Garden.Field.Field.
Require Import Garden.Field.Sqrt.
Require Import Garden.Plonky3.M.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Lists.List.
Require Import Stdlib.micromega.Lia.

Import ListNotations.

#[local] Existing Instance Primes.PallasPIsPrime.

Global Open Scope Z_scope.


Module OrchardActionUsFreeNullifierK.
  Import OrchardActionFixedBase.

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

  (* Keep the square-root / QR chain opaque to the conversion oracle (as in
     [circuit_proof/us_free/main.v]): the statements below mention
     [canonical_us_for] and [is_square] over the concrete Pasta modulus. *)
  Strategy opaque
    [is_square modpow modpow_pos field_sqrt fixed_window_point_canonical].

  (* ---------------------------------------------------------------------- *)
  (* Scalar-value identification: the [ScalarAdd] output cell.               *)
  (* ---------------------------------------------------------------------- *)

  (** Facts of the [ScalarAdd] region, peeled from [Holds]: the region adds
      the Poseidon hash output cell and the [psi_old] witness cell. *)
  Lemma nullifier_k_scalar_add_facts
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
    interpret_facts Γ
      (layouter_facts
        (Garden.Orchard.circuit.synthesize_scalar_add
          (Garden.Orchard.circuit.nullifier_region
            RegionId.Nullifier.ScalarAdd)
          "scalar = poseidon_hash(nk, rho) + psi"
          (layouter_value
            (Garden.Halo2.halo2_gadgets.poseidon.pow5.synthesize_hash
              nk rho_old))
          psi_old)).
  Proof.
    cbv zeta.
    pose proof (holds_facts Γ Hcircuit) as Hfacts.
    unfold Garden.Orchard.circuit.synthesize in Hfacts.
    do 4 apply interpret_layouter_facts_bind_right in Hfacts.
    apply interpret_layouter_facts_bind_left in Hfacts.
    unfold Garden.Orchard.circuit.synthesize_nullifier in Hfacts.
    apply interpret_layouter_facts_bind_left in Hfacts.
    apply interpret_layouter_facts_in_namespace in Hfacts.
    apply interpret_layouter_facts_bind_right in Hfacts.
    apply interpret_layouter_facts_bind_left in Hfacts.
    exact Hfacts.
  Qed.

  (** The region's components: the [QAdd] selector at row 0 and the two
      [Copy] constraints pinning [A7[0]]/[A8[0]] to the Poseidon output cell
      and the [psi_old] witness cell. *)
  Lemma nullifier_k_scalar_add_components
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
    Γ.(Assignment.selector) Selector.QAdd scalar_add_region 0 = 1 /\
    eval_cell Γ
      (Garden.Halo2.Synthesis.Cell.advice scalar_add_region Advice.A7 0) =
      eval_cell Γ
        (layouter_value
          (Garden.Halo2.halo2_gadgets.poseidon.pow5.synthesize_hash
            nk rho_old)) /\
    eval_cell Γ
      (Garden.Halo2.Synthesis.Cell.advice scalar_add_region Advice.A8 0) =
      eval_cell Γ psi_old.
  Proof.
    cbv zeta.
    pose proof (nullifier_k_scalar_add_facts Γ Hcircuit) as Hfacts.
    cbv zeta in Hfacts.
    unfold Garden.Orchard.circuit.synthesize_scalar_add in Hfacts.
    apply interpret_layouter_facts_in_namespace in Hfacts.
    apply interpret_layouter_facts_add_region in Hfacts.
    cbn [region_facts region_value layouter_value Monad.bind
      Garden.Halo2.Synthesis.RegionIsMonad
      List.app interpret_facts interpret_fact] in Hfacts.
    tauto.
  Qed.

  (** The scalar-value identification: the [ScalarAdd] output cell [A6[0]]
      carries the base-field sum [poseidon_hash2 nk rho_old +F psi_old]. *)
  Lemma nullifier_k_scalar_value
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    UnOp.from
      (eval_cell Γ
        (Garden.Halo2.Synthesis.Cell.advice scalar_add_region Advice.A6 0)) =
    nf_scalar Γ.
  Proof.
    pose proof (nullifier_k_scalar_add_components Γ Hcircuit) as Hcomponents.
    cbv zeta in Hcomponents.
    destruct Hcomponents as (Hsel & Hcopy_a & Hcopy_b).
    (* The [QAdd] gate at the region's row 0. *)
    assert (Hgate :
        Γ ⊢ ⟦ Garden.Orchard.circuit.gadget.add_chip.addition_gate ⟧
          (scalar_add_region, 0)).
    { apply (satisfies_gates_at Γ
        (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)
        Garden.Orchard.circuit.gadget.add_chip.addition_gate
        scalar_add_region 0).
      - cbn. repeat (first [left; reflexivity | right]).
      - exact (holds_gates Γ Hcircuit). }
    pose proof (Addition.deterministic Γ scalar_add_region 0
      (enabled_nonzero Γ Selector.QAdd scalar_add_region 0 Hsel)
      Hgate) as Hadd.
    assert (Hc :
        Γ ⊢ ⟦ Expression.Advice Advice.A6 Rotation.cur ⟧
          (scalar_add_region, 0) =
        (Γ ⊢ ⟦ Expression.Advice Advice.A7 Rotation.cur ⟧
          (scalar_add_region, 0)) +F
        (Γ ⊢ ⟦ Expression.Advice Advice.A8 Rotation.cur ⟧
          (scalar_add_region, 0))).
    { exact (f_equal Addition.c Hadd). }
    rewrite <- (eval_advice_cur_cell Γ scalar_add_region Advice.A6 0).
    rewrite Hc.
    rewrite (eval_advice_cur_cell Γ scalar_add_region Advice.A7 0).
    rewrite (eval_advice_cur_cell Γ scalar_add_region Advice.A8 0).
    rewrite Hcopy_a, Hcopy_b.
    rewrite (OrchardPoseidon.poseidon_hash_value_correct Γ Hcircuit).
    reflexivity.
  Qed.

  (* ---------------------------------------------------------------------- *)
  (* The digit match at the spec scalar.                                     *)
  (* ---------------------------------------------------------------------- *)

  (** Digit [i] of the spec scalar [poseidon_hash2 nk rho_old +F psi_old] is
      the [i]-th running-sum word of the base-field region — the canonicity
      digit match composed with the scalar-value identification. *)
  Lemma nullifier_k_window_digit_value
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (i : nat) (Hi : (i < 85)%nat) :
    EccSpec.window_digit (nf_scalar Γ) i =
      (Γ ⊢ ⟦ Expression.Advice Advice.A4 Rotation.cur ⟧
        (bf_region, Z.of_nat i)) -F
        (Γ ⊢ ⟦ Expression.Advice Advice.A4 Rotation.next ⟧
          (bf_region, Z.of_nat i)) *F
        UnOp.from Garden.Halo2.halo2_gadgets.ecc.chip.constants.h.
  Proof.
    rewrite <- (nullifier_k_scalar_value Γ Hcircuit).
    exact (BaseFieldCanonicity.nullifier_k_window_digit_scalar_cell
      Γ Hcircuit i Hi).
  Qed.

  (* ---------------------------------------------------------------------- *)
  (* Window correctness of the base-field region at the spec scalar digit.   *)
  (* ---------------------------------------------------------------------- *)

  (** Fixed-column facts of the base-field incomplete region: the base-field
      sibling of [short_incomplete_fixed_fact]. *)
  Lemma base_field_mul_incomplete_fixed_fact
      (region : RegionId.t)
      (scalar : Garden.Halo2.Synthesis.Cell.t columns RegionId.t)
      (i : nat) (row : Garden.Orchard.circuit.fixed_base_row)
      (column : Fixed.t) (annotation : string) (value : Z) :
    List.nth_error
      Garden.Orchard.constants.fixed_bases.nullifier_k.base_field_fixed_rows
      i =
      Some row ->
    List.In (column, annotation, value) row ->
    List.In
      (Fact.FixedIs column region (Z.of_nat i) value)
      (layouter_facts
        (Garden.Orchard.circuit
          .synth_base_field_mul_incomplete
          region scalar)).
  Proof.
    intros Hrow Hin.
    unfold Garden.Orchard.circuit
      .synth_base_field_mul_incomplete.
    cbn [layouter_facts region_facts].
    apply List.in_or_app.
    right.
    apply List.in_or_app.
    right.
    apply List.in_or_app.
    right.
    apply List.in_or_app.
    left.
    replace (Z.of_nat i) with (0 + Z.of_nat i) by lia.
    apply (assign_fixed_rows_with_selector_fixed_fact region
      Selector.QMulFixedRunningSum 0
      Garden.Orchard.constants.fixed_bases.nullifier_k.base_field_fixed_rows
      i row column annotation value Hrow Hin).
  Qed.

  (** Correctness of a base-field window row at the spec scalar's digit: the
      assigned point (A0, A1) equals the spec window point at
      [window_digit (poseidon_hash2 nk rho_old +F psi_old) i].  The
      base-field analogue of
      [short_incomplete_window_correct]. *)
  Lemma base_field_incomplete_window_correct
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (i : nat)
      (a0 a1 a2 a3 a4 a5 a6 a7 az : string)
      (c0 c1 c2 c3 c4 c5 c6 c7 z : Z)
      (Hrow :
        List.nth_error
          Garden.Orchard.constants.fixed_bases.nullifier_k
            .base_field_fixed_rows
          i =
          Some [
            (Fixed.LagrangeCoeffs0, a0, c0);
            (Fixed.LagrangeCoeffs1, a1, c1);
            (Fixed.LagrangeCoeffs2, a2, c2);
            (Fixed.LagrangeCoeffs3, a3, c3);
            (Fixed.LagrangeCoeffs4, a4, c4);
            (Fixed.LagrangeCoeffs5, a5, c5);
            (Fixed.LagrangeCoeffs6, a6, c6);
            (Fixed.LagrangeCoeffs7, a7, c7);
            (Fixed.FixedZ, az, z)
          ])
      (Hi : (i < 85)%nat) :
    Field.map_mod {|
      Point.x :=
        Γ ⊢ ⟦ Expression.Advice Advice.A0 Rotation.cur ⟧
          (bf_region, Z.of_nat i);
      Point.y :=
        Γ ⊢ ⟦ Expression.Advice Advice.A1 Rotation.cur ⟧
          (bf_region, Z.of_nat i);
    |} =
      EccSpec.fixed_window_point
        (EccSpec.fixed_window_of_row [
          (Fixed.LagrangeCoeffs0, a0, c0);
          (Fixed.LagrangeCoeffs1, a1, c1);
          (Fixed.LagrangeCoeffs2, a2, c2);
          (Fixed.LagrangeCoeffs3, a3, c3);
          (Fixed.LagrangeCoeffs4, a4, c4);
          (Fixed.LagrangeCoeffs5, a5, c5);
          (Fixed.LagrangeCoeffs6, a6, c6);
          (Fixed.LagrangeCoeffs7, a7, c7);
          (Fixed.FixedZ, az, z)
        ])
        (EccSpec.window_digit (nf_scalar Γ) i)
        (List.nth i (read_us Γ bf_region 85) 0).
  Proof.
    rewrite (nullifier_k_window_digit_value Γ Hcircuit i Hi).
    rewrite (read_us_nth Γ bf_region 85 i Hi).
    cbn [EccSpec.fixed_window_of_row EccSpec.fw_coeffs EccSpec.fw_z
      List.firstn List.map List.nth_error snd].
    apply (running_sum_fixed_window_correct_of_facts Γ
      (layouter_facts
        (Garden.Orchard.circuit
          .synth_base_field_mul_incomplete
          bf_region
          (Garden.Halo2.Synthesis.Cell.advice scalar_add_region Advice.A6 0)))
      bf_region (Z.of_nat i) c0 c1 c2 c3 c4 c5 c6 c7 z
      (BaseFieldCanonicity.nullifier_k_incomplete_facts Γ Hcircuit)).
    - apply BaseFieldCanonicity.base_field_incomplete_selector_fact.
      exact Hi.
    - apply (base_field_mul_incomplete_fixed_fact
        bf_region _ i _ Fixed.LagrangeCoeffs0 a0 c0 Hrow).
      cbn. left. reflexivity.
    - apply (base_field_mul_incomplete_fixed_fact
        bf_region _ i _ Fixed.LagrangeCoeffs1 a1 c1 Hrow).
      cbn. right. left. reflexivity.
    - apply (base_field_mul_incomplete_fixed_fact
        bf_region _ i _ Fixed.LagrangeCoeffs2 a2 c2 Hrow).
      cbn. do 2 right. left. reflexivity.
    - apply (base_field_mul_incomplete_fixed_fact
        bf_region _ i _ Fixed.LagrangeCoeffs3 a3 c3 Hrow).
      cbn. do 3 right. left. reflexivity.
    - apply (base_field_mul_incomplete_fixed_fact
        bf_region _ i _ Fixed.LagrangeCoeffs4 a4 c4 Hrow).
      cbn. do 4 right. left. reflexivity.
    - apply (base_field_mul_incomplete_fixed_fact
        bf_region _ i _ Fixed.LagrangeCoeffs5 a5 c5 Hrow).
      cbn. do 5 right. left. reflexivity.
    - apply (base_field_mul_incomplete_fixed_fact
        bf_region _ i _ Fixed.LagrangeCoeffs6 a6 c6 Hrow).
      cbn. do 6 right. left. reflexivity.
    - apply (base_field_mul_incomplete_fixed_fact
        bf_region _ i _ Fixed.LagrangeCoeffs7 a7 c7 Hrow).
      cbn. do 7 right. left. reflexivity.
    - apply (base_field_mul_incomplete_fixed_fact
        bf_region _ i _ Fixed.FixedZ az z Hrow).
      cbn. do 8 right. left. reflexivity.
    - exact (holds_gates Γ Hcircuit).
  Qed.

  (* ---------------------------------------------------------------------- *)
  (* Table-level assembly at the base-field table.                           *)
  (* ---------------------------------------------------------------------- *)

  Lemma nullifier_k_rows_standard :
    List.forallb OrchardActionUsFree.standard_row_shape
      Garden.Orchard.constants.fixed_bases.nullifier_k.base_field_fixed_rows =
    true.
  Proof. vm_compute. reflexivity. Qed.

  Lemma nullifier_k_rows_length :
    List.length
      Garden.Orchard.constants.fixed_bases.nullifier_k.base_field_fixed_rows =
    85%nat.
  Proof. reflexivity. Qed.

  Lemma nullifier_k_table_length :
    List.length (OrchardCircuitSpec.nullifier_k orchard_internal_params) = 85%nat.
  Proof. reflexivity. Qed.

  (** Window correctness at a row known through its shape bit (the base-field
      sibling of [OrchardActionUsFree.standard_row_window_correct]). *)
  Lemma nullifier_k_standard_row_window_correct
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (i : nat) (row : Garden.Orchard.circuit.fixed_base_row)
      (Hrow :
        List.nth_error
          Garden.Orchard.constants.fixed_bases.nullifier_k
            .base_field_fixed_rows
          i = Some row)
      (Hshape : OrchardActionUsFree.standard_row_shape row = true)
      (Hi : (i < 85)%nat) :
    incomplete_additions_window_point Γ bf_region (Z.of_nat i) =
    EccSpec.fixed_window_point (EccSpec.fixed_window_of_row row)
      (EccSpec.window_digit (nf_scalar Γ) i)
      (List.nth i (read_us Γ bf_region 85) 0).
  Proof.
    destruct row as [| ((col0, a0), c0) row]; [discriminate Hshape |].
    destruct col0; try discriminate Hshape.
    destruct row as [| ((col1, a1), c1) row]; [discriminate Hshape |].
    destruct col1; try discriminate Hshape.
    destruct row as [| ((col2, a2), c2) row]; [discriminate Hshape |].
    destruct col2; try discriminate Hshape.
    destruct row as [| ((col3, a3), c3) row]; [discriminate Hshape |].
    destruct col3; try discriminate Hshape.
    destruct row as [| ((col4, a4), c4) row]; [discriminate Hshape |].
    destruct col4; try discriminate Hshape.
    destruct row as [| ((col5, a5), c5) row]; [discriminate Hshape |].
    destruct col5; try discriminate Hshape.
    destruct row as [| ((col6, a6), c6) row]; [discriminate Hshape |].
    destruct col6; try discriminate Hshape.
    destruct row as [| ((col7, a7), c7) row]; [discriminate Hshape |].
    destruct col7; try discriminate Hshape.
    destruct row as [| ((colz, az), z) row]; [discriminate Hshape |].
    destruct colz; try discriminate Hshape.
    destruct row as [| e row]; [| discriminate Hshape].
    rewrite <- incomplete_additions_window_point_map_mod.
    unfold incomplete_additions_window_point.
    exact (base_field_incomplete_window_correct Γ Hcircuit i
      a0 a1 a2 a3 a4 a5 a6 a7 az c0 c1 c2 c3 c4 c5 c6 c7 z
      Hrow Hi).
  Qed.

  (** Per-window correctness against the whole nullifier_k spec table. *)
  Lemma nullifier_k_table_window_correct
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (i : nat) (Hi : (i < 85)%nat) :
    incomplete_additions_window_point Γ bf_region (Z.of_nat i) =
    EccSpec.fixed_window_point
      (List.nth i (OrchardCircuitSpec.nullifier_k orchard_internal_params)
        fixed_window_default)
      (EccSpec.window_digit (nf_scalar Γ) i)
      (List.nth i (read_us Γ bf_region 85) 0).
  Proof.
    change (OrchardCircuitSpec.nullifier_k orchard_internal_params) with
      (EccSpec.fixed_table_of_rows
        Garden.Orchard.constants.fixed_bases.nullifier_k
          .base_field_fixed_rows).
    rewrite OrchardActionUsFree.fixed_table_of_rows_nth.
    apply (nullifier_k_standard_row_window_correct Γ Hcircuit i
      (List.nth i
        Garden.Orchard.constants.fixed_bases.nullifier_k.base_field_fixed_rows
        nil)).
    - apply List.nth_error_nth'.
      rewrite nullifier_k_rows_length.
      exact Hi.
    - eapply List.forallb_forall; [exact nullifier_k_rows_standard |].
      apply List.nth_In.
      rewrite nullifier_k_rows_length.
      exact Hi.
    - exact Hi.
  Qed.

  (** On-curve fact at the spec digit, per window of the base-field region. *)
  Lemma nullifier_k_spec_window_on_curve
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (i : nat) (Hi : (i < 85)%nat) :
    point_on_curve
      (EccSpec.fixed_window_point
        (List.nth i (OrchardCircuitSpec.nullifier_k orchard_internal_params)
          fixed_window_default)
        (EccSpec.window_digit (nf_scalar Γ) i)
        (List.nth i (read_us Γ bf_region 85) 0)).
  Proof.
    pose proof
      (base_field_incomplete_region_window_on_curve Γ bf_region
        (Garden.Halo2.Synthesis.Cell.advice scalar_add_region Advice.A6 0) i
        (BaseFieldCanonicity.nullifier_k_incomplete_facts Γ Hcircuit)
        (holds_gates Γ Hcircuit) Hi) as Honc.
    rewrite (nullifier_k_table_window_correct Γ Hcircuit i Hi) in Honc.
    exact Honc.
  Qed.

  (** The [Ek] table equality: the nullifier_k fixed-base mul at the scalar
      [poseidon_hash2 nk rho_old +F psi_old] is witness-free — the witnessed
      [u]-list gives the same fold as the canonical one. *)
  Lemma nullifier_k_table_eq
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    EccSpec.fixed_scalar_mul
      (OrchardCircuitSpec.nullifier_k orchard_internal_params)
      (Poseidon.poseidon_hash2
         (OrchardSpec.in_nk (read_action_inputs Γ))
         (OrchardSpec.in_rho_old (read_action_inputs Γ)) +F
         OrchardSpec.in_psi_old (read_action_inputs Γ))
      (OrchardCircuitSpec.w_us_k (read_action_witness Γ)) =
    EccSpec.fixed_scalar_mul
      (OrchardCircuitSpec.nullifier_k orchard_internal_params)
      (Poseidon.poseidon_hash2
         (OrchardSpec.in_nk (read_action_inputs Γ))
         (OrchardSpec.in_rho_old (read_action_inputs Γ)) +F
         OrchardSpec.in_psi_old (read_action_inputs Γ))
      (OrchardCircuitSpec.w_us_k (canonical_witness (read_action_inputs Γ))).
  Proof.
    unfold read_action_witness, canonical_witness, read_action_inputs,
      read_action_inputs_with_anchor.
    cbn [OrchardCircuitSpec.w_us_k OrchardSpec.in_nk OrchardSpec.in_rho_old
      OrchardSpec.in_psi_old].
    apply (table_us_free_of_oncurve
      (OrchardCircuitSpec.nullifier_k orchard_internal_params)
      (nf_scalar Γ)
      (read_us Γ bf_region 85)
      fixed_window_default).
    - rewrite OrchardActionUsFree.read_us_length, nullifier_k_table_length.
      reflexivity.
    - intros i Hi.
      rewrite nullifier_k_table_length in Hi.
      split.
      + cbv zeta.
        exact (nullifier_k_spec_window_on_curve Γ Hcircuit i Hi).
      + apply (window_disc_qr_nullifier_k_all_Z i).
        * exact Hi.
        * unfold EccSpec.window_digit. apply Z.mod_pos_bound. lia.
  Qed.

  (* ---------------------------------------------------------------------- *)
  (* The witness-elimination capstone.                                       *)
  (* ---------------------------------------------------------------------- *)

  (** Under [Holds] the witnessed and the canonical square roots give
      the same action output — the reduction
      [action_spec_us_free_of_nullifier_k] applied to the [Ek] leg. *)
  Theorem action_spec_us_free
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ) :
    action_spec_of Γ = output (read_action_inputs Γ).
  Proof.
    exact (OrchardActionUsFree.action_spec_us_free_of_nullifier_k Γ Hcircuit
      (nullifier_k_table_eq Γ Hcircuit)).
  Qed.

End OrchardActionUsFreeNullifierK.
