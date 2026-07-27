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
Require Import Garden.Field.Field.
Require Import Garden.Field.Div.
Require Import Garden.Field.Lemmas.
Require Import Garden.Plonky3.M.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Lists.List.
Require Import Stdlib.setoid_ring.Ring.

Require Import Garden.Orchard.circuit_proof.facts.

#[local] Existing Instance Primes.PallasPIsPrime.

Global Open Scope Z_scope.


Module OrchardActionFixedBase.
  Include OrchardActionFacts.

  Local Notation Holds Γ :=
    (circuit_holds Γ
      Garden.Orchard.circuit.synthesize
      (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)).

  Definition assigned_point_value
      (Γ : Assignment.t columns RegionId.t)
      (point : Garden.Orchard.circuit.AssignedPoint.t)
      : Point.t := {|
    Point.x := eval_cell Γ point.(Garden.Orchard.circuit.AssignedPoint.x);
    Point.y := eval_cell Γ point.(Garden.Orchard.circuit.AssignedPoint.y);
  |}.

  Lemma full_width_fixed_window_correct
      (Γ : Assignment.t columns RegionId.t)
      (region : RegionId.t) (row : Z)
      (c0 c1 c2 c3 c4 c5 c6 c7 z : Z)
      (Hselector :
        Γ ⊢ ⟦ Selector.QMulFixedFull ⟧ (region, row) <> 0)
      (Hgate :
        Γ ⊢ ⟦ Garden.Halo2.halo2_gadgets.ecc.chip.mul_fixed.full_width
            .full_width_fixed_base_scalar_mul_gate ⟧ (region, row))
      (Hc0 :
        Γ ⊢ ⟦ Expression.Fixed Fixed.LagrangeCoeffs0 Rotation.cur ⟧
          (region, row) = UnOp.from c0)
      (Hc1 :
        Γ ⊢ ⟦ Expression.Fixed Fixed.LagrangeCoeffs1 Rotation.cur ⟧
          (region, row) = UnOp.from c1)
      (Hc2 :
        Γ ⊢ ⟦ Expression.Fixed Fixed.LagrangeCoeffs2 Rotation.cur ⟧
          (region, row) = UnOp.from c2)
      (Hc3 :
        Γ ⊢ ⟦ Expression.Fixed Fixed.LagrangeCoeffs3 Rotation.cur ⟧
          (region, row) = UnOp.from c3)
      (Hc4 :
        Γ ⊢ ⟦ Expression.Fixed Fixed.LagrangeCoeffs4 Rotation.cur ⟧
          (region, row) = UnOp.from c4)
      (Hc5 :
        Γ ⊢ ⟦ Expression.Fixed Fixed.LagrangeCoeffs5 Rotation.cur ⟧
          (region, row) = UnOp.from c5)
      (Hc6 :
        Γ ⊢ ⟦ Expression.Fixed Fixed.LagrangeCoeffs6 Rotation.cur ⟧
          (region, row) = UnOp.from c6)
      (Hc7 :
        Γ ⊢ ⟦ Expression.Fixed Fixed.LagrangeCoeffs7 Rotation.cur ⟧
          (region, row) = UnOp.from c7)
      (Hz :
        Γ ⊢ ⟦ Expression.Fixed Fixed.FixedZ Rotation.cur ⟧
          (region, row) = UnOp.from z) :
    Field.map_mod {|
      Point.x := Γ ⊢ ⟦ Expression.Advice Advice.A0 Rotation.cur ⟧ (region, row);
      Point.y := Γ ⊢ ⟦ Expression.Advice Advice.A1 Rotation.cur ⟧ (region, row);
    |} =
      EccSpec.fixed_window_point {|
        EccSpec.fw_coeffs := [c0; c1; c2; c3; c4; c5; c6; c7];
        EccSpec.fw_z := z;
      |}
        (Γ ⊢ ⟦ Expression.Advice Advice.A4 Rotation.cur ⟧ (region, row))
        (Γ ⊢ ⟦ Expression.Advice Advice.A5 Rotation.cur ⟧ (region, row)).
  Proof.
    pose proof
      (FullWidthFixedBaseScalarMul.deterministic Γ region row
        Hselector Hgate) as Hdet.
    rewrite Hdet.
    unfold FullWidthFixedBaseScalarMul.output, CoordsCheck.output,
      EccSpec.fixed_window_point.
    cbn [Field.map_mod Point.IsMapMod EccSpec.fw_coeffs EccSpec.fw_z].
    rewrite Hc0, Hc1, Hc2, Hc3, Hc4, Hc5, Hc6, Hc7, Hz.
    rewrite <- EccSpec.fixed_interp_8_eq_interpolated_x_from.
    f_equal.
    - apply FieldRewrite.from_from.
    - unfold Garden.Halo2.halo2_gadgets.utilities_proof.square.
      rewrite FieldRewrite.sub_from_right.
      cbn [Point.y].
      apply FieldRewrite.from_sub.
  Qed.

  Lemma full_width_fixed_window_range
      (Γ : Assignment.t columns RegionId.t)
      (region : RegionId.t) (row : Z)
      (Hselector :
        Γ ⊢ ⟦ Selector.QMulFixedFull ⟧ (region, row) <> 0)
      (Hgate :
        Γ ⊢ ⟦ Garden.Halo2.halo2_gadgets.ecc.chip.mul_fixed.full_width
            .full_width_fixed_base_scalar_mul_gate ⟧ (region, row)) :
    0 <=
      Γ ⊢ ⟦ Expression.Advice Advice.A4 Rotation.cur ⟧ (region, row) <
      8.
  Proof.
    cbn [eval_gate Gate.constraints Constraints.with_selector eval_constraints
      eval_named_constraint eval_constraint eval_selector eval_expression
      rotated_row Rotation.cur
      Garden.Halo2.halo2_gadgets.ecc.chip.mul_fixed.full_width
        .full_width_fixed_base_scalar_mul_gate
      Garden.Halo2.halo2_gadgets.ecc.chip.mul_fixed.coords_check
      Garden.Halo2.halo2_gadgets.ecc.chip.mul_fixed.interpolated_x
      Garden.Halo2.halo2_gadgets.utilities.square
      List.map List.app] in Hgate.
    destruct Hgate as [_ Hgate].
    destruct Hgate as [_ Hgate].
    destruct Hgate as [_ Hrange].
    exact (Hrange Hselector).
  Qed.

  Lemma full_width_fixed_window_on_curve
      (Γ : Assignment.t columns RegionId.t)
      (region : RegionId.t) (row : Z)
      (Hselector :
        Γ ⊢ ⟦ Selector.QMulFixedFull ⟧ (region, row) <> 0)
      (Hgate :
        Γ ⊢ ⟦ Garden.Halo2.halo2_gadgets.ecc.chip.mul_fixed.full_width
            .full_width_fixed_base_scalar_mul_gate ⟧ (region, row)) :
    Γ ⊢ ⟦ Garden.Halo2.halo2_gadgets.ecc.chip.witness_point
        .curve_eqn Advice.A0 Advice.A1 ⟧ (region, row) = 0.
  Proof.
    cbn [eval_gate Gate.constraints Constraints.with_selector eval_constraints
      eval_named_constraint eval_constraint eval_selector eval_expression
      rotated_row Rotation.cur
      Garden.Halo2.halo2_gadgets.ecc.chip.mul_fixed.full_width
        .full_width_fixed_base_scalar_mul_gate
      Garden.Halo2.halo2_gadgets.ecc.chip.mul_fixed.coords_check
      Garden.Halo2.halo2_gadgets.ecc.chip.mul_fixed.interpolated_x
      Garden.Halo2.halo2_gadgets.ecc.chip.witness_point.curve_eqn
      Garden.Halo2.halo2_gadgets.utilities.square
      List.map List.app] in Hgate |- *.
    destruct Hgate as [_ Hgate].
    destruct Hgate as [_ Hgate].
    destruct Hgate as [Hon_curve _].
    exact (Hon_curve Hselector).
  Qed.

  Lemma full_width_fixed_window_correct_of_facts
      (Γ : Assignment.t columns RegionId.t)
      (facts : list (Fact.t columns RegionId.t))
      (region : RegionId.t) (row : Z)
      (c0 c1 c2 c3 c4 c5 c6 c7 z : Z)
      (Hfacts : interpret_facts Γ facts)
      (Hselector :
        List.In (Fact.SelectorOn Selector.QMulFixedFull region row) facts)
      (Hc0 :
        List.In (Fact.FixedIs Fixed.LagrangeCoeffs0 region row c0) facts)
      (Hc1 :
        List.In (Fact.FixedIs Fixed.LagrangeCoeffs1 region row c1) facts)
      (Hc2 :
        List.In (Fact.FixedIs Fixed.LagrangeCoeffs2 region row c2) facts)
      (Hc3 :
        List.In (Fact.FixedIs Fixed.LagrangeCoeffs3 region row c3) facts)
      (Hc4 :
        List.In (Fact.FixedIs Fixed.LagrangeCoeffs4 region row c4) facts)
      (Hc5 :
        List.In (Fact.FixedIs Fixed.LagrangeCoeffs5 region row c5) facts)
      (Hc6 :
        List.In (Fact.FixedIs Fixed.LagrangeCoeffs6 region row c6) facts)
      (Hc7 :
        List.In (Fact.FixedIs Fixed.LagrangeCoeffs7 region row c7) facts)
      (Hz :
        List.In (Fact.FixedIs Fixed.FixedZ region row z) facts)
      (Hgates :
        satisfies_gates Γ
          (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)) :
    Field.map_mod {|
      Point.x := Γ ⊢ ⟦ Expression.Advice Advice.A0 Rotation.cur ⟧ (region, row);
      Point.y := Γ ⊢ ⟦ Expression.Advice Advice.A1 Rotation.cur ⟧ (region, row);
    |} =
      EccSpec.fixed_window_point {|
        EccSpec.fw_coeffs := [c0; c1; c2; c3; c4; c5; c6; c7];
        EccSpec.fw_z := z;
      |}
        (Γ ⊢ ⟦ Expression.Advice Advice.A4 Rotation.cur ⟧ (region, row))
        (Γ ⊢ ⟦ Expression.Advice Advice.A5 Rotation.cur ⟧ (region, row)).
  Proof.
    apply (full_width_fixed_window_correct Γ region row
      c0 c1 c2 c3 c4 c5 c6 c7 z).
    - exact (selector_nonzero_of_facts Γ facts
        Selector.QMulFixedFull region row Hfacts Hselector).
    - apply (satisfies_gates_at Γ
        (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)
        Garden.Halo2.halo2_gadgets.ecc.chip.mul_fixed.full_width
          .full_width_fixed_base_scalar_mul_gate
        region row); [| exact Hgates].
      cbn. repeat (first [left; reflexivity | right]).
    - exact (fixed_expression_eq_of_facts Γ facts
        Fixed.LagrangeCoeffs0 region row c0 Hfacts Hc0).
    - exact (fixed_expression_eq_of_facts Γ facts
        Fixed.LagrangeCoeffs1 region row c1 Hfacts Hc1).
    - exact (fixed_expression_eq_of_facts Γ facts
        Fixed.LagrangeCoeffs2 region row c2 Hfacts Hc2).
    - exact (fixed_expression_eq_of_facts Γ facts
        Fixed.LagrangeCoeffs3 region row c3 Hfacts Hc3).
    - exact (fixed_expression_eq_of_facts Γ facts
        Fixed.LagrangeCoeffs4 region row c4 Hfacts Hc4).
    - exact (fixed_expression_eq_of_facts Γ facts
        Fixed.LagrangeCoeffs5 region row c5 Hfacts Hc5).
    - exact (fixed_expression_eq_of_facts Γ facts
        Fixed.LagrangeCoeffs6 region row c6 Hfacts Hc6).
    - exact (fixed_expression_eq_of_facts Γ facts
        Fixed.LagrangeCoeffs7 region row c7 Hfacts Hc7).
    - exact (fixed_expression_eq_of_facts Γ facts
        Fixed.FixedZ region row z Hfacts Hz).
  Qed.

  Lemma full_width_fixed_window_on_curve_of_facts
      (Γ : Assignment.t columns RegionId.t)
      (facts : list (Fact.t columns RegionId.t))
      (region : RegionId.t) (row : Z)
      (Hfacts : interpret_facts Γ facts)
      (Hselector :
        List.In (Fact.SelectorOn Selector.QMulFixedFull region row) facts)
      (Hgates :
        satisfies_gates Γ
          (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)) :
    Γ ⊢ ⟦ Garden.Halo2.halo2_gadgets.ecc.chip.witness_point
        .curve_eqn Advice.A0 Advice.A1 ⟧ (region, row) = 0.
  Proof.
    apply (full_width_fixed_window_on_curve Γ region row).
    - exact (selector_nonzero_of_facts Γ facts
        Selector.QMulFixedFull region row Hfacts Hselector).
    - apply (satisfies_gates_at Γ
        (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)
        Garden.Halo2.halo2_gadgets.ecc.chip.mul_fixed.full_width
          .full_width_fixed_base_scalar_mul_gate
        region row); [| exact Hgates].
      cbn. repeat (first [left; reflexivity | right]).
  Qed.

  Lemma full_width_fixed_window_range_of_facts
      (Γ : Assignment.t columns RegionId.t)
      (facts : list (Fact.t columns RegionId.t))
      (region : RegionId.t) (row : Z)
      (Hfacts : interpret_facts Γ facts)
      (Hselector :
        List.In (Fact.SelectorOn Selector.QMulFixedFull region row) facts)
      (Hgates :
        satisfies_gates Γ
          (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)) :
    0 <=
      Γ ⊢ ⟦ Expression.Advice Advice.A4 Rotation.cur ⟧ (region, row) <
      8.
  Proof.
    apply (full_width_fixed_window_range Γ region row).
    - exact (selector_nonzero_of_facts Γ facts
        Selector.QMulFixedFull region row Hfacts Hselector).
    - apply (satisfies_gates_at Γ
        (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)
        Garden.Halo2.halo2_gadgets.ecc.chip.mul_fixed.full_width
          .full_width_fixed_base_scalar_mul_gate
        region row); [| exact Hgates].
      cbn. repeat (first [left; reflexivity | right]).
  Qed.

  Lemma read_windows_range_of_full_width_facts
      (Γ : Assignment.t columns RegionId.t)
      (facts : list (Fact.t columns RegionId.t))
      (region : RegionId.t) (count : nat)
      (Hfacts : interpret_facts Γ facts)
      (Hselectors :
        forall i : nat,
          (i < count)%nat ->
          List.In
            (Fact.SelectorOn Selector.QMulFixedFull region (Z.of_nat i))
            facts)
      (Hgates :
        satisfies_gates Γ
          (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)) :
    List.Forall (fun w => 0 <= w < 8) (read_windows Γ region count).
  Proof.
    unfold read_windows.
    apply List.Forall_forall.
    intros w Hin.
    apply List.in_map_iff in Hin.
    destruct Hin as [i Hin].
    destruct Hin as [Hw Hin].
    apply List.in_seq in Hin.
    subst w.
    apply (full_width_fixed_window_range_of_facts Γ facts region (Z.of_nat i)
      Hfacts).
    - apply Hselectors. lia.
    - exact Hgates.
  Qed.

  Lemma full_width_incomplete_region_windows_range
      (Γ : Assignment.t columns RegionId.t)
      (region : RegionId.t)
      (rows : list Garden.Orchard.circuit.fixed_base_row)
      (Hfacts :
        interpret_facts Γ
          (layouter_facts
            (Garden.Orchard.circuit
              .synth_full_mul_incomplete_with_rows
              region rows)))
      (Hgates :
        satisfies_gates Γ
          (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)) :
    List.Forall (fun w => 0 <= w < 8) (read_windows Γ region 85).
  Proof.
    unfold Garden.Orchard.circuit
      .synth_full_mul_incomplete_with_rows in Hfacts.
    apply interpret_layouter_facts_add_region in Hfacts.
    pose proof Hfacts as Hwindow_facts.
    apply interpret_region_facts_bind_left in Hwindow_facts.
    apply (read_windows_range_of_full_width_facts Γ
      (region_facts region
        (Garden.Orchard.circuit.assign_full_window_witnesses 0 85))
      region 85 Hwindow_facts).
    - intros i Hi.
      replace (Z.of_nat i) with (0 + Z.of_nat i) by lia.
      apply assign_full_window_witnesses_selector_fact.
      exact Hi.
    - exact Hgates.
  Qed.

  Lemma full_width_incomplete_region_window_digit
      (Γ : Assignment.t columns RegionId.t)
      (region : RegionId.t)
      (rows : list Garden.Orchard.circuit.fixed_base_row)
      (i : nat)
      (Hfacts :
        interpret_facts Γ
          (layouter_facts
            (Garden.Orchard.circuit
              .synth_full_mul_incomplete_with_rows
              region rows)))
      (Hgates :
        satisfies_gates Γ
          (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty))
      (Hi : (i < 85)%nat) :
    EccSpec.window_digit (read_scalar_from_windows Γ region 85) i =
      read_advice Γ Advice.A4 region (Z.of_nat i).
  Proof.
    apply window_digit_read_scalar_from_windows.
    - exact (full_width_incomplete_region_windows_range Γ region rows
        Hfacts Hgates).
    - exact Hi.
  Qed.

  Lemma full_incomplete_selector_fact
      (region : RegionId.t)
      (rows : list Garden.Orchard.circuit.fixed_base_row)
      (i : nat) :
    (i < 85)%nat ->
    List.In
      (Fact.SelectorOn Selector.QMulFixedFull region (Z.of_nat i))
      (layouter_facts
        (Garden.Orchard.circuit
          .synth_full_mul_incomplete_with_rows
          region rows)).
  Proof.
    intros Hi.
    unfold Garden.Orchard.circuit
      .synth_full_mul_incomplete_with_rows.
    cbn [layouter_facts region_facts].
    apply List.in_or_app.
    left.
    replace (Z.of_nat i) with (0 + Z.of_nat i) by lia.
    apply assign_full_window_witnesses_selector_fact.
    exact Hi.
  Qed.

  Lemma full_incomplete_fixed_fact
      (region : RegionId.t)
      (rows : list Garden.Orchard.circuit.fixed_base_row)
      (i : nat) (row : Garden.Orchard.circuit.fixed_base_row)
      (column : Fixed.t) (annotation : string) (value : Z) :
    List.nth_error rows i = Some row ->
    List.In (column, annotation, value) row ->
    List.In
      (Fact.FixedIs column region (Z.of_nat i) value)
      (layouter_facts
        (Garden.Orchard.circuit
          .synth_full_mul_incomplete_with_rows
          region rows)).
  Proof.
    intros Hrow Hin.
    unfold Garden.Orchard.circuit
      .synth_full_mul_incomplete_with_rows.
    cbn [layouter_facts region_facts].
    apply List.in_or_app.
    right.
    apply List.in_or_app.
    left.
    replace (Z.of_nat i) with (0 + Z.of_nat i) by lia.
    apply (assign_fixed_rows_with_selector_fixed_fact region
      Selector.QMulFixedFull 0 rows i row column annotation value Hrow Hin).
  Qed.

  Lemma full_width_incomplete_window_correct
      (Γ : Assignment.t columns RegionId.t)
      (region : RegionId.t)
      (rows : list Garden.Orchard.circuit.fixed_base_row)
      (i : nat)
      (a0 a1 a2 a3 a4 a5 a6 a7 az : string)
      (c0 c1 c2 c3 c4 c5 c6 c7 z : Z)
      (Hrow :
        List.nth_error rows i =
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
      (Hfacts :
        interpret_facts Γ
          (layouter_facts
            (Garden.Orchard.circuit
              .synth_full_mul_incomplete_with_rows
              region rows)))
      (Hgates :
        satisfies_gates Γ
          (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty))
      (Hi : (i < 85)%nat) :
    Field.map_mod {|
      Point.x :=
        Γ ⊢ ⟦ Expression.Advice Advice.A0 Rotation.cur ⟧
          (region, Z.of_nat i);
      Point.y :=
        Γ ⊢ ⟦ Expression.Advice Advice.A1 Rotation.cur ⟧
          (region, Z.of_nat i);
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
        (EccSpec.window_digit (read_scalar_from_windows Γ region 85) i)
        (List.nth i (read_us Γ region 85) 0).
  Proof.
    rewrite (full_width_incomplete_region_window_digit Γ region rows i
      Hfacts Hgates Hi).
    rewrite (read_us_nth Γ region 85 i Hi).
    cbn [EccSpec.fixed_window_of_row EccSpec.fw_coeffs EccSpec.fw_z
      List.firstn List.map List.nth_error snd].
    apply (full_width_fixed_window_correct_of_facts Γ
      (layouter_facts
        (Garden.Orchard.circuit
          .synth_full_mul_incomplete_with_rows
          region rows))
      region (Z.of_nat i) c0 c1 c2 c3 c4 c5 c6 c7 z Hfacts).
    - apply full_incomplete_selector_fact.
      exact Hi.
    - apply (full_incomplete_fixed_fact region rows
        i _ Fixed.LagrangeCoeffs0 a0 c0 Hrow).
      cbn. left. reflexivity.
    - apply (full_incomplete_fixed_fact region rows
        i _ Fixed.LagrangeCoeffs1 a1 c1 Hrow).
      cbn. right. left. reflexivity.
    - apply (full_incomplete_fixed_fact region rows
        i _ Fixed.LagrangeCoeffs2 a2 c2 Hrow).
      cbn. do 2 right. left. reflexivity.
    - apply (full_incomplete_fixed_fact region rows
        i _ Fixed.LagrangeCoeffs3 a3 c3 Hrow).
      cbn. do 3 right. left. reflexivity.
    - apply (full_incomplete_fixed_fact region rows
        i _ Fixed.LagrangeCoeffs4 a4 c4 Hrow).
      cbn. do 4 right. left. reflexivity.
    - apply (full_incomplete_fixed_fact region rows
        i _ Fixed.LagrangeCoeffs5 a5 c5 Hrow).
      cbn. do 5 right. left. reflexivity.
    - apply (full_incomplete_fixed_fact region rows
        i _ Fixed.LagrangeCoeffs6 a6 c6 Hrow).
      cbn. do 6 right. left. reflexivity.
    - apply (full_incomplete_fixed_fact region rows
        i _ Fixed.LagrangeCoeffs7 a7 c7 Hrow).
      cbn. do 7 right. left. reflexivity.
    - apply (full_incomplete_fixed_fact region rows
        i _ Fixed.FixedZ az z Hrow).
      cbn. do 8 right. left. reflexivity.
    - exact Hgates.
  Qed.

  Lemma assigned_point_value_witness_point
      (Γ : Assignment.t columns RegionId.t)
      (region : RegionId.t) (name : string) :
    Field.map_mod
      (assigned_point_value Γ
        (layouter_value (Garden.Orchard.circuit.witness_point region name))) =
    read_point Γ region.
  Proof.
    unfold Garden.Orchard.circuit.witness_point,
      Garden.Orchard.circuit.witness_point_region,
      assigned_point_value, read_point, read, read1, read_advice.
    cbn [layouter_value region_value eval_cell eval_expression rotated_row
      Rotation.cur Field.map_mod Point.IsMapMod].
    cbn. reflexivity.
  Qed.

  Lemma witness_non_identity_point_value
      (Γ : Assignment.t columns RegionId.t)
      (region : RegionId.t) (name : string) :
    Field.map_mod
      (assigned_point_value Γ
        (layouter_value
          (Garden.Orchard.circuit.witness_non_identity_point region name))) =
    read_point Γ region.
  Proof.
    unfold Garden.Orchard.circuit.witness_non_identity_point,
      Garden.Orchard.circuit.witness_point_region,
      assigned_point_value, read_point, read, read1, read_advice.
    cbn [layouter_value region_value eval_cell eval_expression rotated_row
      Rotation.cur Field.map_mod Point.IsMapMod].
    cbn. reflexivity.
  Qed.

  Lemma witness_non_identity_point_on_curve
      (Γ : Assignment.t columns RegionId.t)
      (region : RegionId.t) (name : string)
      (Hfacts :
        interpret_facts Γ
          (layouter_facts
            (Garden.Orchard.circuit.witness_non_identity_point region name)))
      (Hgates :
        satisfies_gates Γ
          (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)) :
    Γ ⊢ ⟦ Garden.Halo2.halo2_gadgets.ecc.chip.witness_point
        .curve_eqn Advice.A0 Advice.A1 ⟧ (region, 0) = 0.
  Proof.
    unfold Garden.Orchard.circuit.witness_non_identity_point in Hfacts.
    apply interpret_layouter_facts_in_namespace in Hfacts.
    apply interpret_layouter_facts_add_region in Hfacts.
    unfold Garden.Orchard.circuit.witness_point_region in Hfacts.
    cbn [region_facts interpret_facts interpret_fact] in Hfacts.
    destruct Hfacts as [Hselector_fact _].
    exact (WitnessPoint.sound_non_identity Γ region 0
      (enabled_nonzero Γ Selector.QWitnessPointNonId region 0 Hselector_fact)
      (satisfies_gates_at Γ
        (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)
        Garden.Halo2.halo2_gadgets.ecc.chip.witness_point
          .witness_non_identity_point_gate
        region 0 ltac:(cbn; repeat (first [left; reflexivity | right]))
        Hgates)).
  Qed.

  Lemma witness_point_sound
      (Γ : Assignment.t columns RegionId.t)
      (region : RegionId.t) (name : string)
      (Hfacts :
        interpret_facts Γ
          (layouter_facts
            (Garden.Orchard.circuit.witness_point region name)))
      (Hgates :
        satisfies_gates Γ
          (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)) :
    (Γ ⊢ ⟦ Expression.Advice Advice.A0 Rotation.cur ⟧ (region, 0) = 0 /\
     Γ ⊢ ⟦ Expression.Advice Advice.A1 Rotation.cur ⟧ (region, 0) = 0) \/
    Γ ⊢ ⟦ Garden.Halo2.halo2_gadgets.ecc.chip.witness_point
        .curve_eqn Advice.A0 Advice.A1 ⟧ (region, 0) = 0.
  Proof.
    unfold Garden.Orchard.circuit.witness_point in Hfacts.
    apply interpret_layouter_facts_in_namespace in Hfacts.
    apply interpret_layouter_facts_add_region in Hfacts.
    unfold Garden.Orchard.circuit.witness_point_region in Hfacts.
    cbn [region_facts interpret_facts interpret_fact] in Hfacts.
    destruct Hfacts as [Hselector_fact _].
    exact (WitnessPoint.sound Γ region 0
      (enabled_nonzero Γ Selector.QWitnessPoint region 0 Hselector_fact)
      (satisfies_gates_at Γ
        (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)
        Garden.Halo2.halo2_gadgets.ecc.chip.witness_point
          .witness_point_gate
        region 0 ltac:(cbn; repeat (first [left; reflexivity | right]))
        Hgates)).
  Qed.

  Lemma curve_eqn_x_nonzero
      (Γ : Assignment.t columns RegionId.t)
      (region : RegionId.t) (row : Z)
      (Hcurve :
        Γ ⊢ ⟦ Garden.Halo2.halo2_gadgets.ecc.chip.witness_point
            .curve_eqn Advice.A0 Advice.A1 ⟧ (region, row) = 0) :
    UnOp.from
      (Γ ⊢ ⟦ Expression.Advice Advice.A0 Rotation.cur ⟧ (region, row)) <> 0.
  Proof.
    apply (EccSpec.pallas_curve_x_nonzero
      (Γ ⊢ ⟦ Expression.Advice Advice.A0 Rotation.cur ⟧ (region, row))
      (Γ ⊢ ⟦ Expression.Advice Advice.A1 Rotation.cur ⟧ (region, row))).
    cbn [eval_expression rotated_row Rotation.cur] in Hcurve.
    exact Hcurve.
  Qed.

  Lemma cm_old_witness_sound
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    (Γ ⊢ ⟦ Expression.Advice Advice.A0 Rotation.cur ⟧
      (Garden.Orchard.circuit.witness_input_region
        RegionId.WitnessInput.CmOld, 0) = 0 /\
     Γ ⊢ ⟦ Expression.Advice Advice.A1 Rotation.cur ⟧
      (Garden.Orchard.circuit.witness_input_region
        RegionId.WitnessInput.CmOld, 0) = 0) \/
    Γ ⊢ ⟦ Garden.Halo2.halo2_gadgets.ecc.chip.witness_point
        .curve_eqn Advice.A0 Advice.A1 ⟧
      (Garden.Orchard.circuit.witness_input_region
        RegionId.WitnessInput.CmOld, 0) = 0.
  Proof.
    destruct Hcircuit as [Hfacts HSatisfies].
    destruct HSatisfies as [Hgates Hlookups].
    apply (witness_point_sound Γ
      (Garden.Orchard.circuit.witness_input_region RegionId.WitnessInput.CmOld)
      "cm_old").
    - pose proof Hfacts as Hcm_facts.
      unfold Garden.Orchard.circuit.synthesize in Hcm_facts.
      apply interpret_layouter_facts_bind_right in Hcm_facts.
      apply interpret_layouter_facts_bind_left in Hcm_facts.
      unfold Garden.Orchard.circuit.synthesize_witness_inputs in Hcm_facts.
      do 2 apply interpret_layouter_facts_bind_right in Hcm_facts.
      apply interpret_layouter_facts_bind_left in Hcm_facts.
      exact Hcm_facts.
    - exact Hgates.
  Qed.

  Lemma ak_P_on_curve
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    Γ ⊢ ⟦ Garden.Halo2.halo2_gadgets.ecc.chip.witness_point
        .curve_eqn Advice.A0 Advice.A1 ⟧
      (Garden.Orchard.circuit.witness_input_region
        RegionId.WitnessInput.AkP, 0) = 0.
  Proof.
    destruct Hcircuit as [Hfacts HSatisfies].
    destruct HSatisfies as [Hgates Hlookups].
    apply (witness_non_identity_point_on_curve Γ
      (Garden.Orchard.circuit.witness_input_region RegionId.WitnessInput.AkP)
      "witness ak_P").
    - pose proof Hfacts as Hak_facts.
      unfold Garden.Orchard.circuit.synthesize in Hak_facts.
      apply interpret_layouter_facts_bind_right in Hak_facts.
      apply interpret_layouter_facts_bind_left in Hak_facts.
      unfold Garden.Orchard.circuit.synthesize_witness_inputs in Hak_facts.
      do 4 apply interpret_layouter_facts_bind_right in Hak_facts.
      apply interpret_layouter_facts_bind_left in Hak_facts.
      exact Hak_facts.
    - exact Hgates.
  Qed.

  Lemma assigned_free_advice_value
      (Γ : Assignment.t columns RegionId.t)
      (region : RegionId.t) (name : string) (column : Advice.t) :
    UnOp.from
      (eval_cell Γ
        (layouter_value
          (Garden.Orchard.circuit.assign_free_advice region name column 0))) =
    read_advice Γ column region 0.
  Proof.
    unfold Garden.Orchard.circuit.assign_free_advice, read_advice.
    cbn [layouter_value region_value eval_cell eval_expression rotated_row
      Rotation.cur].
    cbn. reflexivity.
  Qed.

  Lemma complete_point_add_correct
      (Γ : Assignment.t columns RegionId.t)
      (region : RegionId.t) (name : string)
      (p q : Garden.Orchard.circuit.AssignedPoint.t)
      (Hfacts :
        interpret_facts Γ
          (layouter_facts
            (Garden.Orchard.circuit.synthesize_complete_point_add
              region name p q)))
      (Hgates :
        satisfies_gates Γ
          (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)) :
    Field.map_mod
      (assigned_point_value Γ
        (layouter_value
          (Garden.Orchard.circuit.synthesize_complete_point_add
            region name p q))) =
      EccSpec.point_add
        (Field.map_mod (assigned_point_value Γ p))
        (Field.map_mod (assigned_point_value Γ q)).
  Proof.
    unfold Garden.Orchard.circuit.synthesize_complete_point_add in Hfacts.
    apply interpret_layouter_facts_in_namespace in Hfacts.
    apply interpret_layouter_facts_add_region in Hfacts.
    unfold Garden.Orchard.circuit.assign_complete_add in Hfacts.
    pose proof Hfacts as Hselector_fact.
    apply interpret_region_facts_bind_left in Hselector_fact.
    cbn [region_facts interpret_facts interpret_fact] in Hselector_fact.
    destruct Hselector_fact as [Hselector_fact _].
    pose proof Hfacts as Hcopy_xp.
    apply interpret_region_facts_bind_right in Hcopy_xp.
    apply interpret_region_facts_bind_left in Hcopy_xp.
    cbn [region_facts interpret_facts interpret_fact eval_cell region_value]
      in Hcopy_xp.
    destruct Hcopy_xp as [Hcopy_xp _].
    pose proof Hfacts as Hcopy_yp.
    do 2 apply interpret_region_facts_bind_right in Hcopy_yp.
    apply interpret_region_facts_bind_left in Hcopy_yp.
    cbn [region_facts interpret_facts interpret_fact eval_cell region_value]
      in Hcopy_yp.
    destruct Hcopy_yp as [Hcopy_yp _].
    pose proof Hfacts as Hcopy_xq.
    do 3 apply interpret_region_facts_bind_right in Hcopy_xq.
    apply interpret_region_facts_bind_left in Hcopy_xq.
    cbn [region_facts interpret_facts interpret_fact eval_cell region_value]
      in Hcopy_xq.
    destruct Hcopy_xq as [Hcopy_xq _].
    pose proof Hfacts as Hcopy_yq.
    do 4 apply interpret_region_facts_bind_right in Hcopy_yq.
    apply interpret_region_facts_bind_left in Hcopy_yq.
    cbn [region_facts interpret_facts interpret_fact eval_cell region_value]
      in Hcopy_yq.
    destruct Hcopy_yq as [Hcopy_yq _].
    pose proof
      (add_proof.CompleteAddition.deterministic Γ region 0
        (enabled_nonzero Γ Selector.QEccAdd region 0 Hselector_fact)
        (satisfies_gates_at Γ
          (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)
          Garden.Halo2.halo2_gadgets.ecc.chip.add.complete_addition_gate
          region 0 ltac:(cbn; repeat (first [left; reflexivity | right]))
          Hgates)) as Hdet.
    unfold EccSpec.point_add.
    cbn [assigned_point_value
      Garden.Orchard.circuit.synthesize_complete_point_add
      Garden.Orchard.circuit.assign_complete_add layouter_value region_value
      eval_cell Field.map_mod Point.IsMapMod].
    change ({|
      Point.x := Γ ⊢ ⟦ Expression.Advice Advice.A2 Rotation.next ⟧ (region, 0);
      Point.y := Γ ⊢ ⟦ Expression.Advice Advice.A3 Rotation.next ⟧ (region, 0)
    |} =
      add_proof.CompleteAddition.output
        (UnOp.from
          (eval_cell Γ p.(Garden.Orchard.circuit.AssignedPoint.x)))
        (UnOp.from
          (eval_cell Γ p.(Garden.Orchard.circuit.AssignedPoint.y)))
        (UnOp.from
          (eval_cell Γ q.(Garden.Orchard.circuit.AssignedPoint.x)))
        (UnOp.from
          (eval_cell Γ q.(Garden.Orchard.circuit.AssignedPoint.y)))).
    rewrite Hdet.
    cbn [eval_expression eval_cell rotated_row Rotation.cur Rotation.next] in *.
    change (add_proof.CompleteAddition.output
      (UnOp.from (eval_cell Γ (Synthesis.Cell.advice region Advice.A0 0)))
      (UnOp.from (eval_cell Γ (Synthesis.Cell.advice region Advice.A1 0)))
      (UnOp.from (eval_cell Γ (Synthesis.Cell.advice region Advice.A2 0)))
      (UnOp.from (eval_cell Γ (Synthesis.Cell.advice region Advice.A3 0))) =
      add_proof.CompleteAddition.output
        (UnOp.from
          (eval_cell Γ p.(Garden.Orchard.circuit.AssignedPoint.x)))
        (UnOp.from
          (eval_cell Γ p.(Garden.Orchard.circuit.AssignedPoint.y)))
        (UnOp.from
          (eval_cell Γ q.(Garden.Orchard.circuit.AssignedPoint.x)))
        (UnOp.from
          (eval_cell Γ q.(Garden.Orchard.circuit.AssignedPoint.y)))).
    rewrite Hcopy_xp, Hcopy_yp, Hcopy_xq, Hcopy_yq.
    reflexivity.
  Qed.

  Lemma assign_mul_fixed_window_correct
      (Γ : Assignment.t columns RegionId.t)
      (region : RegionId.t) (offset : Z) :
    Field.map_mod
      (assigned_point_value Γ
        (region_value
          (Garden.Orchard.circuit.assign_mul_fixed_window region offset))) =
      {|
        Point.x :=
          Γ ⊢ ⟦ Expression.Advice Advice.A0 Rotation.cur ⟧ (region, offset);
        Point.y :=
          Γ ⊢ ⟦ Expression.Advice Advice.A1 Rotation.cur ⟧ (region, offset);
      |}.
  Proof.
    cbn [Garden.Orchard.circuit.assign_mul_fixed_window region_value
      assigned_point_value Field.map_mod Point.IsMapMod eval_cell].
    rewrite !eval_advice_cur_cell.
    reflexivity.
  Qed.

  Lemma assign_add_incomplete_correct
      (Γ : Assignment.t columns RegionId.t)
      (region : RegionId.t) (offset : Z)
      (p q : Garden.Orchard.circuit.AssignedPoint.t)
      (Hfacts :
        interpret_facts Γ
          (region_facts region
            (Garden.Orchard.circuit.assign_add_incomplete
              region offset p q)))
      (Hgates :
        satisfies_gates Γ
          (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty))
      (Hx_distinct :
        Point.x (Field.map_mod (assigned_point_value Γ p)) <>
        Point.x (Field.map_mod (assigned_point_value Γ q))) :
    Field.map_mod
      (assigned_point_value Γ
        (region_value
          (Garden.Orchard.circuit.assign_add_incomplete region offset p q))) =
      EccSpec.point_add_incomplete
        (Field.map_mod (assigned_point_value Γ p))
        (Field.map_mod (assigned_point_value Γ q)).
  Proof.
    unfold Garden.Orchard.circuit.assign_add_incomplete in Hfacts.
    pose proof Hfacts as Hselector_fact.
    apply interpret_region_facts_bind_left in Hselector_fact.
    cbn [region_facts interpret_facts interpret_fact] in Hselector_fact.
    destruct Hselector_fact as [Hselector_fact _].
    pose proof Hfacts as Hcopy_xp.
    apply interpret_region_facts_bind_right in Hcopy_xp.
    apply interpret_region_facts_bind_left in Hcopy_xp.
    cbn [region_facts interpret_facts interpret_fact eval_cell region_value]
      in Hcopy_xp.
    destruct Hcopy_xp as [Hcopy_xp _].
    pose proof Hfacts as Hcopy_yp.
    do 2 apply interpret_region_facts_bind_right in Hcopy_yp.
    apply interpret_region_facts_bind_left in Hcopy_yp.
    cbn [region_facts interpret_facts interpret_fact eval_cell region_value]
      in Hcopy_yp.
    destruct Hcopy_yp as [Hcopy_yp _].
    pose proof Hfacts as Hcopy_xq.
    do 3 apply interpret_region_facts_bind_right in Hcopy_xq.
    apply interpret_region_facts_bind_left in Hcopy_xq.
    cbn [region_facts interpret_facts interpret_fact eval_cell region_value]
      in Hcopy_xq.
    destruct Hcopy_xq as [Hcopy_xq _].
    pose proof Hfacts as Hcopy_yq.
    do 4 apply interpret_region_facts_bind_right in Hcopy_yq.
    apply interpret_region_facts_bind_left in Hcopy_yq.
    cbn [region_facts interpret_facts interpret_fact eval_cell region_value]
      in Hcopy_yq.
    destruct Hcopy_yq as [Hcopy_yq _].
    assert (Hx_row :
        Γ ⊢ ⟦ Expression.Advice Advice.A0 Rotation.cur ⟧ (region, offset) <>
        Γ ⊢ ⟦ Expression.Advice Advice.A2 Rotation.cur ⟧ (region, offset)).
    { cbn [assigned_point_value Field.map_mod Point.IsMapMod] in Hx_distinct.
      rewrite !eval_advice_cur_cell.
      rewrite Hcopy_xp, Hcopy_xq.
      exact Hx_distinct. }
    pose proof
      (add_incomplete_proof.IncompleteAddition.deterministic Γ region offset
        (enabled_nonzero Γ Selector.QAddIncomplete region offset
          Hselector_fact)
        Hx_row
        (satisfies_gates_at Γ
          (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)
          Garden.Halo2.halo2_gadgets.ecc.chip.add_incomplete
            .incomplete_addition_gate
          region offset ltac:(cbn; repeat (first [left; reflexivity | right]))
          Hgates)) as Hdet.
    cbn [assigned_point_value Field.map_mod Point.IsMapMod] in *.
    change ({|
      Point.x :=
        Γ ⊢ ⟦ Expression.Advice Advice.A2 Rotation.next ⟧ (region, offset);
      Point.y :=
        Γ ⊢ ⟦ Expression.Advice Advice.A3 Rotation.next ⟧ (region, offset)
    |} =
      add_incomplete_proof.IncompleteAddition.output
        (Γ ⊢ ⟦ Expression.Advice Advice.A0 Rotation.cur ⟧ (region, offset))
        (Γ ⊢ ⟦ Expression.Advice Advice.A1 Rotation.cur ⟧ (region, offset))
        (Γ ⊢ ⟦ Expression.Advice Advice.A2 Rotation.cur ⟧ (region, offset))
        (Γ ⊢ ⟦ Expression.Advice Advice.A3 Rotation.cur ⟧ (region, offset)))
      in Hdet.
    unfold EccSpec.point_add_incomplete.
    cbn [Garden.Orchard.circuit.assign_add_incomplete region_value
      assigned_point_value Field.map_mod Point.IsMapMod eval_cell].
    change ({|
      Point.x :=
        Γ ⊢ ⟦ Expression.Advice Advice.A2 Rotation.next ⟧ (region, offset);
      Point.y :=
        Γ ⊢ ⟦ Expression.Advice Advice.A3 Rotation.next ⟧ (region, offset)
    |} =
      add_incomplete_proof.IncompleteAddition.output
        (UnOp.from
          (eval_cell Γ p.(Garden.Orchard.circuit.AssignedPoint.x)))
        (UnOp.from
          (eval_cell Γ p.(Garden.Orchard.circuit.AssignedPoint.y)))
        (UnOp.from
          (eval_cell Γ q.(Garden.Orchard.circuit.AssignedPoint.x)))
        (UnOp.from
          (eval_cell Γ q.(Garden.Orchard.circuit.AssignedPoint.y)))).
    rewrite Hdet.
    repeat first
      [ rewrite eval_advice_cur_cell
      | rewrite Hcopy_xp
      | rewrite Hcopy_yp
      | rewrite Hcopy_xq
      | rewrite Hcopy_yq
      | progress cbn
      | reflexivity ].
  Qed.

  Lemma point_add_incomplete_eq_point_add_swap
      (P Q : Point.t)
      (HPx : UnOp.from (Point.x P) <> 0)
      (HQx : UnOp.from (Point.x Q) <> 0)
      (Hx_distinct : UnOp.from (Point.x P) <> UnOp.from (Point.x Q)) :
    EccSpec.point_add_incomplete P Q = EccSpec.point_add Q P.
  Proof.
    destruct P as [xp yp].
    destruct Q as [xq yq].
    cbn [Point.x Point.y] in *.
    unfold EccSpec.point_add_incomplete, EccSpec.point_add.
    cbn [Point.x Point.y].
    unfold add_incomplete_proof.IncompleteAddition.output,
      add_proof.CompleteAddition.output,
      Garden.Halo2.halo2_gadgets.utilities_proof.square.
    destruct (xq =? 0) eqn:Hxq0.
    - apply Z.eqb_eq in Hxq0. subst xq. contradiction.
    - destruct (xp =? 0) eqn:Hxp0.
      + apply Z.eqb_eq in Hxp0. subst xp. contradiction.
      + destruct ((xq =? xp) && (yq +F yp =? 0)) eqn:Hpmq.
        * apply Bool.andb_true_iff in Hpmq.
          destruct Hpmq as [Heq _].
          apply Z.eqb_eq in Heq. subst xq. contradiction.
        * destruct (xq =? xp) eqn:Heqx.
          -- apply Z.eqb_eq in Heqx. subst xq. contradiction.
          -- set (L := BinOp.div (yp -F yq) (xp -F xq)).
             assert (Hd : UnOp.from (xp -F xq) <> 0).
             { rewrite FieldRewrite.from_sub. intro Hc.
               apply sub_zero_equiv in Hc. exact (Hx_distinct Hc). }
             assert (Hlam : L *F (xp -F xq) = yp -F yq).
             { unfold L. rewrite div_mul.
               - apply FieldRewrite.from_sub.
               - unfold Primes.pallas_p, Primes.t_p; lia.
               - exact Hd. }
             subst L.
             f_equal.
             { field_solve. }
             rewrite field_mul_sub_distr.
             rewrite field_mul_sub_distr.
             field_solve.
  Qed.

  Definition incomplete_additions_window_point
      (Γ : Assignment.t columns RegionId.t)
      (region : RegionId.t) (offset : Z) : Point.t := {|
    Point.x := Γ ⊢ ⟦ Expression.Advice Advice.A0 Rotation.cur ⟧ (region, offset);
    Point.y := Γ ⊢ ⟦ Expression.Advice Advice.A1 Rotation.cur ⟧ (region, offset);
  |}.

  Lemma incomplete_additions_window_point_map_mod
      (Γ : Assignment.t columns RegionId.t)
      (region : RegionId.t) (offset : Z) :
    Field.map_mod (incomplete_additions_window_point Γ region offset) =
    incomplete_additions_window_point Γ region offset.
  Proof.
    unfold incomplete_additions_window_point.
    cbn [Field.map_mod Point.IsMapMod Point.x Point.y].
    rewrite !eval_advice_cur_cell.
    rewrite !FieldRewrite.from_from.
    reflexivity.
  Qed.

  Definition point_on_curve (P : Point.t) : Prop :=
    Point.y P *F Point.y P -F
      (Point.x P *F Point.x P *F Point.x P) -F
      Garden.Halo2.halo2_gadgets.ecc.chip.constants.pallas_b = 0.

  (** Complete addition of reduced points has reduced output coordinates: every
      branch of [CompleteAddition.output] returns either an input coordinate
      (reduced by hypothesis), the literal [0], or a field-subtraction (reduced
      by [from_sub_reduced]). *)
  Lemma point_add_reduced (P Q : Point.t)
      (HPx : UnOp.from (Point.x P) = Point.x P)
      (HPy : UnOp.from (Point.y P) = Point.y P)
      (HQx : UnOp.from (Point.x Q) = Point.x Q)
      (HQy : UnOp.from (Point.y Q) = Point.y Q) :
    UnOp.from (Point.x (EccSpec.point_add P Q)) =
      Point.x (EccSpec.point_add P Q) /\
    UnOp.from (Point.y (EccSpec.point_add P Q)) =
      Point.y (EccSpec.point_add P Q).
  Proof.
    destruct P as [xp yp]; destruct Q as [xq yq].
    cbn [Point.x Point.y] in *.
    unfold EccSpec.point_add, add_proof.CompleteAddition.output,
      Garden.Halo2.halo2_gadgets.utilities_proof.square.
    cbn [Point.x Point.y].
    destruct (xp =? 0).
    - cbn [Point.x Point.y]. split; [exact HQx | exact HQy].
    - destruct (xq =? 0).
      + cbn [Point.x Point.y]. split; [exact HPx | exact HPy].
      + destruct ((xp =? xq) && (yp +F yq =? 0))%bool.
        * cbn [Point.x Point.y]. split; apply FieldRewrite.from_zero.
        * cbn [Point.x Point.y]. split; apply from_sub_reduced.
  Qed.

  (** Window points read off the circuit have reduced coordinates (each is a
      [UnOp.from] of an advice cell). *)
  Lemma incomplete_additions_window_point_reduced
      (Γ : Assignment.t columns RegionId.t)
      (region : RegionId.t) (offset : Z) :
    UnOp.from
      (Point.x (incomplete_additions_window_point Γ region offset)) =
      Point.x (incomplete_additions_window_point Γ region offset) /\
    UnOp.from
      (Point.y (incomplete_additions_window_point Γ region offset)) =
      Point.y (incomplete_additions_window_point Γ region offset).
  Proof.
    unfold incomplete_additions_window_point.
    cbn [Point.x Point.y].
    rewrite !eval_advice_cur_cell.
    split; apply FieldRewrite.from_from.
  Qed.

  Lemma full_width_incomplete_window_x_nonzero
      (Γ : Assignment.t columns RegionId.t)
      (region : RegionId.t)
      (rows : list Garden.Orchard.circuit.fixed_base_row)
      (i : nat)
      (Hfacts :
        interpret_facts Γ
          (layouter_facts
            (Garden.Orchard.circuit
              .synth_full_mul_incomplete_with_rows
              region rows)))
      (Hgates :
        satisfies_gates Γ
          (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty))
      (Hi : (i < 85)%nat) :
    UnOp.from
      (Point.x
        (incomplete_additions_window_point Γ region (Z.of_nat i))) <> 0.
  Proof.
    unfold incomplete_additions_window_point.
    apply curve_eqn_x_nonzero.
    apply (full_width_fixed_window_on_curve_of_facts Γ
      (layouter_facts
        (Garden.Orchard.circuit
          .synth_full_mul_incomplete_with_rows
          region rows))
      region (Z.of_nat i) Hfacts).
    - apply full_incomplete_selector_fact.
      exact Hi.
    - exact Hgates.
  Qed.

  Fixpoint incomplete_additions_output
      (Γ : Assignment.t columns RegionId.t)
      (region : RegionId.t) (offset : Z) (count : nat) (acc : Point.t)
      : Point.t :=
    match count with
    | O => acc
    | S count =>
        incomplete_additions_output Γ region (offset + 1) count
          (EccSpec.point_add_incomplete
            (incomplete_additions_window_point Γ region offset)
            acc)
    end.

  Fixpoint complete_additions_output
      (Γ : Assignment.t columns RegionId.t)
      (region : RegionId.t) (offset : Z) (count : nat) (acc : Point.t)
      : Point.t :=
    match count with
    | O => acc
    | S count =>
        complete_additions_output Γ region (offset + 1) count
          (EccSpec.point_add acc
            (incomplete_additions_window_point Γ region offset))
    end.

  Lemma complete_additions_output_succ
      (Γ : Assignment.t columns RegionId.t)
      (region : RegionId.t) (offset : Z) (count : nat) (acc : Point.t) :
    complete_additions_output Γ region offset (S count) acc =
      EccSpec.point_add
        (complete_additions_output Γ region offset count acc)
        (incomplete_additions_window_point Γ region
          (offset + Z.of_nat count)).
  Proof.
    generalize dependent acc.
    generalize dependent offset.
    induction count as [| count IH]; intros offset acc.
    - cbn [complete_additions_output].
      replace (offset + Z.of_nat 0) with offset by lia.
      reflexivity.
    - change (complete_additions_output Γ region (offset + 1) (S count)
        (EccSpec.point_add acc
          (incomplete_additions_window_point Γ region offset)) =
        EccSpec.point_add
          (complete_additions_output Γ region (offset + 1) count
            (EccSpec.point_add acc
              (incomplete_additions_window_point Γ region offset)))
          (incomplete_additions_window_point Γ region
            (offset + Z.of_nat (S count)))).
      rewrite (IH (offset + 1)
        (EccSpec.point_add acc
          (incomplete_additions_window_point Γ region offset))).
      replace (offset + 1 + Z.of_nat count) with
        (offset + Z.of_nat (S count)) by lia.
      reflexivity.
  Qed.

  Fixpoint incomplete_additions_precondition
      (Γ : Assignment.t columns RegionId.t)
      (region : RegionId.t) (offset : Z) (count : nat) (acc : Point.t)
      : Prop :=
    match count with
    | O => True
    | S count =>
        Point.x (incomplete_additions_window_point Γ region offset) <>
          Point.x acc /\
        incomplete_additions_precondition Γ region (offset + 1) count
          (EccSpec.point_add_incomplete
            (incomplete_additions_window_point Γ region offset)
            acc)
    end.

  Fixpoint incomplete_additions_complete_precondition
      (Γ : Assignment.t columns RegionId.t)
      (region : RegionId.t) (offset : Z) (count : nat) (acc : Point.t)
      : Prop :=
    match count with
    | O => True
    | S count =>
        UnOp.from
          (Point.x (incomplete_additions_window_point Γ region offset)) <> 0 /\
        UnOp.from (Point.x acc) <> 0 /\
        UnOp.from
          (Point.x (incomplete_additions_window_point Γ region offset)) <>
          UnOp.from (Point.x acc) /\
        incomplete_additions_complete_precondition Γ region (offset + 1) count
          (EccSpec.point_add acc
            (incomplete_additions_window_point Γ region offset))
    end.

  Fixpoint incomplete_additions_distinct_precondition
      (Γ : Assignment.t columns RegionId.t)
      (region : RegionId.t) (offset : Z) (count : nat) (acc : Point.t)
      : Prop :=
    match count with
    | O => True
    | S count =>
        UnOp.from
          (Point.x (incomplete_additions_window_point Γ region offset)) <>
          UnOp.from (Point.x acc) /\
        incomplete_additions_distinct_precondition Γ region (offset + 1) count
          (EccSpec.point_add acc
            (incomplete_additions_window_point Γ region offset))
    end.

  Lemma incomplete_output_eq_complete_output
      (Γ : Assignment.t columns RegionId.t)
      (region : RegionId.t) (offset : Z) (count : nat) (acc : Point.t)
      (Hpre :
        incomplete_additions_complete_precondition Γ region offset count acc) :
    incomplete_additions_output Γ region offset count acc =
      complete_additions_output Γ region offset count acc.
  Proof.
    generalize dependent acc.
    generalize dependent offset.
    induction count as [| count IH]; intros offset acc Hpre.
    - reflexivity.
    - cbn [incomplete_additions_output complete_additions_output
        incomplete_additions_complete_precondition] in *.
      destruct Hpre as [Hpx Hpre].
      destruct Hpre as [Haccx Hpre].
      destruct Hpre as [Hdistinct Hpre].
      rewrite (point_add_incomplete_eq_point_add_swap
        (incomplete_additions_window_point Γ region offset) acc
        Hpx Haccx Hdistinct).
      exact (IH (offset + 1)
        (EccSpec.point_add acc
          (incomplete_additions_window_point Γ region offset))
        Hpre).
  Qed.

  Lemma incomplete_complete_precondition_of_distinct
      (Γ : Assignment.t columns RegionId.t)
      (region : RegionId.t) (offset : Z) (count : nat) (acc : Point.t)
      (Hacc_curve : point_on_curve acc)
      (Hacc_x : UnOp.from (Point.x acc) <> 0)
      (Hwindows_curve :
        forall i : nat,
          (i < count)%nat ->
          point_on_curve
            (incomplete_additions_window_point Γ region
              (offset + Z.of_nat i)))
      (Hwindows_x :
        forall i : nat,
          (i < count)%nat ->
          UnOp.from
            (Point.x
              (incomplete_additions_window_point Γ region
                (offset + Z.of_nat i))) <> 0)
      (Hdistinct :
        incomplete_additions_distinct_precondition Γ region offset count acc) :
    incomplete_additions_complete_precondition Γ region offset count acc.
  Proof.
    revert offset acc Hacc_curve Hacc_x Hwindows_curve Hwindows_x Hdistinct.
    induction count as [| count IH]; intros offset acc Hacc_curve Hacc_x
      Hwindows_curve Hwindows_x Hdistinct.
    - exact I.
    - cbn [incomplete_additions_complete_precondition
        incomplete_additions_distinct_precondition] in Hdistinct |- *.
      destruct Hdistinct as [Hdistinct Htail].
      set (window := incomplete_additions_window_point Γ region offset).
      assert (Hwindow_curve : point_on_curve window).
      { subst window.
        replace offset with (offset + Z.of_nat 0) by lia.
        apply Hwindows_curve. lia. }
      assert (Hwindow_x : UnOp.from (Point.x window) <> 0).
      { subst window.
        replace offset with (offset + Z.of_nat 0) by lia.
        apply Hwindows_x. lia. }
      repeat split.
      + exact Hwindow_x.
      + exact Hacc_x.
      + subst window. exact Hdistinct.
      + apply IH.
        * subst window.
          apply (EccSpec.point_add_on_curve_x_distinct acc
            (incomplete_additions_window_point Γ region offset)).
          -- exact Hacc_curve.
          -- exact Hwindow_curve.
          -- exact Hacc_x.
          -- exact Hwindow_x.
          -- intro Heq. apply Hdistinct. symmetry. exact Heq.
        * subst window.
          apply (EccSpec.point_add_x_nonzero_x_distinct acc
            (incomplete_additions_window_point Γ region offset)).
          -- exact Hacc_curve.
          -- exact Hwindow_curve.
          -- exact Hacc_x.
          -- exact Hwindow_x.
          -- intro Heq. apply Hdistinct. symmetry. exact Heq.
        * intros i Hi.
          replace (offset + 1 + Z.of_nat i)
            with (offset + Z.of_nat (S i)) by lia.
          apply Hwindows_curve. lia.
        * intros i Hi.
          replace (offset + 1 + Z.of_nat i)
            with (offset + Z.of_nat (S i)) by lia.
          apply Hwindows_x. lia.
        * exact Htail.
  Qed.

  Lemma incomplete_complete_implies_precondition
      (Γ : Assignment.t columns RegionId.t)
      (region : RegionId.t) (offset : Z) (count : nat) (acc : Point.t)
      (Hpre :
        incomplete_additions_complete_precondition Γ region offset count acc) :
    incomplete_additions_precondition Γ region offset count acc.
  Proof.
    generalize dependent acc.
    generalize dependent offset.
    induction count as [| count IH]; intros offset acc Hpre.
    - exact I.
    - cbn [incomplete_additions_precondition
        incomplete_additions_complete_precondition] in *.
      destruct Hpre as [Hpx Hpre].
      destruct Hpre as [Haccx Hpre].
      destruct Hpre as [Hdistinct Hpre].
      split.
      + intro Heq.
        apply Hdistinct.
        rewrite Heq.
        reflexivity.
      + rewrite (point_add_incomplete_eq_point_add_swap
          (incomplete_additions_window_point Γ region offset) acc
          Hpx Haccx Hdistinct).
        exact (IH (offset + 1)
          (EccSpec.point_add acc
            (incomplete_additions_window_point Γ region offset))
          Hpre).
  Qed.

  Lemma complete_additions_output_on_curve
      (Γ : Assignment.t columns RegionId.t)
      (region : RegionId.t) (offset : Z)
      (count : nat) (acc : Point.t)
      (Hacc : point_on_curve acc)
      (Hwindows :
        forall i : nat,
          (i < count)%nat ->
          point_on_curve
            (incomplete_additions_window_point Γ region
              (offset + Z.of_nat i)))
      (Hpre :
        incomplete_additions_complete_precondition Γ region offset count acc) :
    point_on_curve (complete_additions_output Γ region offset count acc).
  Proof.
    revert offset acc Hacc Hwindows Hpre.
    induction count as [| count IH]; intros offset acc Hacc Hwindows Hpre.
    - exact Hacc.
    - cbn [complete_additions_output incomplete_additions_complete_precondition]
        in Hpre |- *.
      destruct Hpre as [Hpx Hpre].
      destruct Hpre as [Haccx Hpre].
      destruct Hpre as [Hdistinct Hpre].
      apply IH.
      + unfold point_on_curve in *.
        refine (EccSpec.point_add_on_curve_x_distinct
          acc (incomplete_additions_window_point Γ region offset)
          _ _ _ _ _).
        * exact Hacc.
        * replace offset with (offset + Z.of_nat 0) by lia.
          apply Hwindows. lia.
        * exact Haccx.
        * exact Hpx.
        * intro Heq. apply Hdistinct. symmetry. exact Heq.
      + intros i Hi.
        replace (offset + 1 + Z.of_nat i) with
          (offset + Z.of_nat (S i)) by lia.
        apply Hwindows. lia.
      + exact Hpre.
  Qed.

  (** The running complete-add accumulator stays reduced (each step is a
      [point_add] of reduced points). *)
  Lemma complete_additions_output_reduced
      (Γ : Assignment.t columns RegionId.t)
      (region : RegionId.t) (offset : Z)
      (count : nat) (acc : Point.t)
      (Hacc_x : UnOp.from (Point.x acc) = Point.x acc)
      (Hacc_y : UnOp.from (Point.y acc) = Point.y acc) :
    UnOp.from
      (Point.x (complete_additions_output Γ region offset count acc)) =
      Point.x (complete_additions_output Γ region offset count acc) /\
    UnOp.from
      (Point.y (complete_additions_output Γ region offset count acc)) =
      Point.y (complete_additions_output Γ region offset count acc).
  Proof.
    revert offset acc Hacc_x Hacc_y.
    induction count as [| count IH]; intros offset acc Hacc_x Hacc_y.
    - split; [exact Hacc_x | exact Hacc_y].
    - cbn [complete_additions_output].
      pose proof
        (incomplete_additions_window_point_reduced Γ region offset)
        as [Hwx Hwy].
      pose proof
        (point_add_reduced acc
          (incomplete_additions_window_point Γ region offset)
          Hacc_x Hacc_y Hwx Hwy) as [Hrx Hry].
      apply IH.
      + exact Hrx.
      + exact Hry.
  Qed.

  Lemma assign_incomplete_additions_correct
      (Γ : Assignment.t columns RegionId.t)
      (region : RegionId.t) (offset : Z) (count : nat)
      (acc : Garden.Orchard.circuit.AssignedPoint.t)
      (Hfacts :
        interpret_facts Γ
          (region_facts region
            (Garden.Orchard.circuit.assign_incomplete_additions
              region offset count acc)))
      (Hgates :
        satisfies_gates Γ
          (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty))
      (Hpre :
        incomplete_additions_precondition Γ region offset count
          (Field.map_mod (assigned_point_value Γ acc))) :
    Field.map_mod
      (assigned_point_value Γ
        (region_value
          (Garden.Orchard.circuit.assign_incomplete_additions
            region offset count acc))) =
      incomplete_additions_output Γ region offset count
          (Field.map_mod (assigned_point_value Γ acc)).
  Proof.
    generalize dependent acc.
    generalize dependent offset.
    induction count as [| count IH]; intros offset acc Hfacts Hpre.
    - reflexivity.
    - cbn [incomplete_additions_precondition incomplete_additions_output]
        in Hpre |- *.
      destruct Hpre as [Hdistinct Hpre].
      cbn [Garden.Orchard.circuit.assign_incomplete_additions
        Monad.bind Garden.Halo2.Synthesis.RegionIsMonad
        region_facts region_value] in Hfacts |- *.
      repeat rewrite interpret_facts_app in Hfacts.
      destruct Hfacts as [_ Hfacts].
      destruct Hfacts as [Hadd_facts Htail_facts].
      set (mul_b :=
        region_value
          (Garden.Orchard.circuit.assign_mul_fixed_window region offset)).
      set (acc' :=
        region_value
          (Garden.Orchard.circuit.assign_add_incomplete region offset mul_b acc)).
      assert (Hdistinct' :
          Point.x (Field.map_mod (assigned_point_value Γ mul_b)) <>
          Point.x (Field.map_mod (assigned_point_value Γ acc))).
      { subst mul_b.
        unfold incomplete_additions_window_point in Hdistinct.
        rewrite assign_mul_fixed_window_correct.
        exact Hdistinct. }
      assert (Hadd :
          Field.map_mod (assigned_point_value Γ acc') =
          EccSpec.point_add_incomplete
            (incomplete_additions_window_point Γ region offset)
            (Field.map_mod (assigned_point_value Γ acc))).
      { subst acc' mul_b.
        rewrite (assign_add_incomplete_correct Γ region offset
          (region_value
            (Garden.Orchard.circuit.assign_mul_fixed_window region offset))
          acc Hadd_facts Hgates Hdistinct').
        rewrite assign_mul_fixed_window_correct.
        reflexivity. }
      rewrite (IH (offset + 1) acc' Htail_facts).
      + rewrite Hadd. reflexivity.
      + rewrite Hadd. exact Hpre.
  Qed.

  Lemma full_last_region_correct
      (Γ : Assignment.t columns RegionId.t)
      (region : RegionId.t)
      (result : Garden.Orchard.circuit.FullFixedResult.t)
      (Hfacts :
        interpret_facts Γ
          (layouter_facts
            (Garden.Orchard.circuit
              .synthesize_full_fixed_base_mul_last_region region result)))
      (Hgates :
        satisfies_gates Γ
          (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)) :
    Field.map_mod
      (assigned_point_value Γ
        (layouter_value
          (Garden.Orchard.circuit
            .synthesize_full_fixed_base_mul_last_region region result))) =
      EccSpec.point_add
        (Field.map_mod
          (assigned_point_value Γ result.(Garden.Orchard.circuit.FullFixedResult.mul_b)))
        (Field.map_mod
          (assigned_point_value Γ result.(Garden.Orchard.circuit.FullFixedResult.acc))).
  Proof.
    unfold Garden.Orchard.circuit
      .synthesize_full_fixed_base_mul_last_region in Hfacts.
    apply interpret_layouter_facts_add_region in Hfacts.
    apply (complete_point_add_correct Γ region ""
      result.(Garden.Orchard.circuit.FullFixedResult.mul_b)
      result.(Garden.Orchard.circuit.FullFixedResult.acc)).
    - exact Hfacts.
    - exact Hgates.
  Qed.

  Lemma full_incomplete_region_acc_correct
      (Γ : Assignment.t columns RegionId.t)
      (region : RegionId.t)
      (rows : list Garden.Orchard.circuit.fixed_base_row)
      (Hfacts :
        interpret_facts Γ
          (layouter_facts
            (Garden.Orchard.circuit
              .synth_full_mul_incomplete_with_rows
              region rows)))
      (Hgates :
        satisfies_gates Γ
          (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty))
      (Hpre :
        incomplete_additions_precondition Γ region 1 83
          (incomplete_additions_window_point Γ region 0)) :
    Field.map_mod
      (assigned_point_value Γ
        (layouter_value
          (Garden.Orchard.circuit
            .synth_full_mul_incomplete_with_rows
            region rows)).(Garden.Orchard.circuit.FullFixedResult.acc)) =
      incomplete_additions_output Γ region 1 83
        (incomplete_additions_window_point Γ region 0).
  Proof.
    pose proof Hfacts as Hacc_facts.
    unfold Garden.Orchard.circuit
      .synth_full_mul_incomplete_with_rows in Hacc_facts.
    apply interpret_layouter_facts_add_region in Hacc_facts.
    do 3 apply interpret_region_facts_bind_right in Hacc_facts.
    apply interpret_region_facts_bind_left in Hacc_facts.
    unfold Garden.Orchard.circuit
      .synth_full_mul_incomplete_with_rows.
    cbn [layouter_value region_value Monad.bind
      Garden.Halo2.Synthesis.RegionIsMonad].
    change (Field.map_mod
      (assigned_point_value Γ
        (region_value
          (Garden.Orchard.circuit.assign_incomplete_additions region 1 83
            (region_value
              (Garden.Orchard.circuit.assign_mul_fixed_window region 0))))) =
      incomplete_additions_output Γ region 1 83
        (incomplete_additions_window_point Γ region 0)).
    rewrite (assign_incomplete_additions_correct Γ region 1 83
      (region_value
        (Garden.Orchard.circuit.assign_mul_fixed_window region 0))).
    - rewrite assign_mul_fixed_window_correct. reflexivity.
    - exact Hacc_facts.
    - exact Hgates.
    - rewrite assign_mul_fixed_window_correct. exact Hpre.
  Qed.

  Lemma full_incomplete_region_mul_b_correct
      (Γ : Assignment.t columns RegionId.t)
      (region : RegionId.t)
      (rows : list Garden.Orchard.circuit.fixed_base_row) :
    Field.map_mod
      (assigned_point_value Γ
        (layouter_value
          (Garden.Orchard.circuit
            .synth_full_mul_incomplete_with_rows
            region rows)).(Garden.Orchard.circuit.FullFixedResult.mul_b)) =
      incomplete_additions_window_point Γ region 84.
  Proof.
    unfold Garden.Orchard.circuit
      .synth_full_mul_incomplete_with_rows.
    cbn [layouter_value region_value Monad.bind
      Garden.Halo2.Synthesis.RegionIsMonad].
    change (Field.map_mod
      (assigned_point_value Γ
        (region_value
          (Garden.Orchard.circuit.assign_mul_fixed_window region 84))) =
      incomplete_additions_window_point Γ region 84).
    rewrite assign_mul_fixed_window_correct.
    reflexivity.
  Qed.

  Lemma synthesize_full_fixed_base_mul_with_rows_correct
      (Γ : Assignment.t columns RegionId.t)
      (incomplete_region last_region : RegionId.t)
      (rows : list Garden.Orchard.circuit.fixed_base_row)
      (Hfacts :
        interpret_facts Γ
          (layouter_facts
            (let🞵 result :=
              Garden.Orchard.circuit
                .synth_full_mul_incomplete_with_rows
                incomplete_region rows in
             Garden.Orchard.circuit
               .synthesize_full_fixed_base_mul_last_region last_region result)))
      (Hgates :
        satisfies_gates Γ
          (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty))
      (Hpre :
        incomplete_additions_precondition Γ incomplete_region 1 83
          (incomplete_additions_window_point Γ incomplete_region 0)) :
    Field.map_mod
      (assigned_point_value Γ
        (layouter_value
          (let🞵 result :=
            Garden.Orchard.circuit
              .synth_full_mul_incomplete_with_rows
              incomplete_region rows in
           Garden.Orchard.circuit
             .synthesize_full_fixed_base_mul_last_region last_region result))) =
      EccSpec.point_add
        (incomplete_additions_window_point Γ incomplete_region 84)
        (incomplete_additions_output Γ incomplete_region 1 83
          (incomplete_additions_window_point Γ incomplete_region 0)).
  Proof.
    pose (incomplete :=
      Garden.Orchard.circuit
        .synth_full_mul_incomplete_with_rows
        incomplete_region rows).
    pose (program :=
      let🞵 result := incomplete in
      Garden.Orchard.circuit
        .synthesize_full_fixed_base_mul_last_region last_region result).
    assert (Hincomplete_facts : interpret_facts Γ (layouter_facts incomplete)).
    { subst program incomplete.
      apply interpret_layouter_facts_bind_left in Hfacts.
      exact Hfacts. }
    assert (Hlast_facts :
        interpret_facts Γ
          (layouter_facts
            (Garden.Orchard.circuit
              .synthesize_full_fixed_base_mul_last_region last_region
              (layouter_value incomplete)))).
    { subst program.
      apply interpret_layouter_facts_bind_right in Hfacts.
      exact Hfacts. }
    change (Field.map_mod
      (assigned_point_value Γ (layouter_value program)) =
      EccSpec.point_add
        (incomplete_additions_window_point Γ incomplete_region 84)
        (incomplete_additions_output Γ incomplete_region 1 83
          (incomplete_additions_window_point Γ incomplete_region 0))).
    subst program.
    cbn [layouter_value Monad.bind Garden.Halo2.Synthesis.LayouterIsMonad].
    rewrite (full_last_region_correct Γ
      last_region (layouter_value incomplete) Hlast_facts Hgates).
    subst incomplete.
    rewrite (full_incomplete_region_mul_b_correct Γ
      incomplete_region rows).
    rewrite (full_incomplete_region_acc_correct Γ
      incomplete_region rows Hincomplete_facts Hgates Hpre).
    reflexivity.
  Qed.

  Lemma full_with_rows_complete_correct
      (Γ : Assignment.t columns RegionId.t)
      (incomplete_region last_region : RegionId.t)
      (rows : list Garden.Orchard.circuit.fixed_base_row)
      (Hfacts :
        interpret_facts Γ
          (layouter_facts
            (let🞵 result :=
              Garden.Orchard.circuit
                .synth_full_mul_incomplete_with_rows
                incomplete_region rows in
             Garden.Orchard.circuit
               .synthesize_full_fixed_base_mul_last_region last_region result)))
      (Hgates :
        satisfies_gates Γ
          (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty))
      (Hpre :
        incomplete_additions_complete_precondition Γ incomplete_region 1 83
          (incomplete_additions_window_point Γ incomplete_region 0)) :
    Field.map_mod
      (assigned_point_value Γ
        (layouter_value
          (let🞵 result :=
            Garden.Orchard.circuit
              .synth_full_mul_incomplete_with_rows
              incomplete_region rows in
           Garden.Orchard.circuit
             .synthesize_full_fixed_base_mul_last_region last_region result))) =
      EccSpec.point_add
        (incomplete_additions_window_point Γ incomplete_region 84)
        (complete_additions_output Γ incomplete_region 1 83
          (incomplete_additions_window_point Γ incomplete_region 0)).
  Proof.
    rewrite (synthesize_full_fixed_base_mul_with_rows_correct Γ
      incomplete_region last_region rows Hfacts Hgates).
    - rewrite (incomplete_output_eq_complete_output Γ
        incomplete_region 1 83
        (incomplete_additions_window_point Γ incomplete_region 0) Hpre).
      reflexivity.
    - exact (incomplete_complete_implies_precondition Γ
        incomplete_region 1 83
        (incomplete_additions_window_point Γ incomplete_region 0) Hpre).
  Qed.

  Lemma complete_output_fixed_scalar_mul_aux
      (Γ : Assignment.t columns RegionId.t)
      (region : RegionId.t) (offset : Z)
      (tbl : EccSpec.fixed_table) (k : Z) (us : list Z)
      (i : nat) (acc : Point.t)
      (Hwindow :
        forall (j : nat) (w : EccSpec.fixed_window),
          List.nth_error tbl j = Some w ->
          incomplete_additions_window_point Γ region (offset + Z.of_nat j) =
          EccSpec.fixed_window_point w
            (EccSpec.window_digit k (i + j)%nat)
            (List.nth (i + j)%nat us 0)) :
    complete_additions_output Γ region offset (List.length tbl) acc =
      EccSpec.fixed_scalar_mul_aux tbl k us i acc.
  Proof.
    revert acc i offset Hwindow.
    induction tbl as [| w tbl IH]; intros acc i offset Hwindow.
    - reflexivity.
    - cbn [complete_additions_output EccSpec.fixed_scalar_mul_aux List.length].
      assert (H0 :
        incomplete_additions_window_point Γ region offset =
        EccSpec.fixed_window_point w (EccSpec.window_digit k i)
          (List.nth i us 0)).
      { replace offset with (offset + Z.of_nat 0) by lia.
        replace i with (i + 0)%nat by lia.
        exact (Hwindow 0%nat w eq_refl). }
      rewrite H0.
      apply IH.
      intros j w' Hnth.
      replace (offset + 1 + Z.of_nat j) with
        (offset + Z.of_nat (S j)) by lia.
      replace (S i + j)%nat with (i + S j)%nat by lia.
      exact (Hwindow (S j) w' Hnth).
  Qed.

  Fixpoint fixed_scalar_mul_incomplete_tail
      (tbl : EccSpec.fixed_table) (k : Z) (us : list Z)
      (i : nat) (acc : Point.t) : Point.t :=
    match tbl with
    | [] => acc
    | w :: tbl =>
        fixed_scalar_mul_incomplete_tail tbl k us (S i)
          (EccSpec.point_add_incomplete
            (EccSpec.fixed_window_point w (EccSpec.window_digit k i)
              (List.nth i us 0))
            acc)
    end.

  Fixpoint fixed_scalar_mul_circuit_tail
      (tbl : EccSpec.fixed_table) (k : Z) (us : list Z)
      (i : nat) (acc : Point.t) : Point.t :=
    match tbl with
    | [] => acc
    | [w] =>
        EccSpec.point_add
          (EccSpec.fixed_window_point w (EccSpec.window_digit k i)
            (List.nth i us 0))
          acc
    | w :: tbl =>
        fixed_scalar_mul_circuit_tail tbl k us (S i)
          (EccSpec.point_add_incomplete
            (EccSpec.fixed_window_point w (EccSpec.window_digit k i)
              (List.nth i us 0))
            acc)
    end.

  Definition fixed_scalar_mul_circuit
      (tbl : EccSpec.fixed_table) (k : Z) (us : list Z) : Point.t :=
    match tbl with
    | [] => EccSpec.identity
    | w :: tbl =>
        fixed_scalar_mul_circuit_tail tbl k us 1%nat
          (EccSpec.fixed_window_point w (EccSpec.window_digit k 0%nat)
            (List.nth 0%nat us 0))
    end.

  (** Side condition for the circuit fold to equal [EccSpec.fixed_scalar_mul].
      Every window but the last is added with the incomplete chip, so it needs
      distinct nonzero x-coordinates; the *last* window is added with the
      complete chip in the opposite operand order, so its reconciliation needs
      only on-curve and reducedness (handled even when the partial sums are
      mutual inverses), not distinctness — this is what makes the ladder sound
      at scalars whose fixed-base multiple is the identity. *)
  Fixpoint fixed_scalar_mul_circuit_tail_precondition
      (tbl : EccSpec.fixed_table) (k : Z) (us : list Z)
      (i : nat) (acc : Point.t) : Prop :=
    match tbl with
    | [] => True
    | [w] =>
        let P := EccSpec.fixed_window_point w (EccSpec.window_digit k i)
          (List.nth i us 0) in
        point_on_curve P /\
        point_on_curve acc /\
        UnOp.from (Point.x P) = Point.x P /\
        UnOp.from (Point.y P) = Point.y P /\
        UnOp.from (Point.x acc) = Point.x acc /\
        UnOp.from (Point.y acc) = Point.y acc
    | w :: tbl =>
        let P := EccSpec.fixed_window_point w (EccSpec.window_digit k i)
          (List.nth i us 0) in
        UnOp.from (Point.x P) <> 0 /\
        UnOp.from (Point.x acc) <> 0 /\
        UnOp.from (Point.x P) <> UnOp.from (Point.x acc) /\
        fixed_scalar_mul_circuit_tail_precondition tbl k us (S i)
          (EccSpec.point_add acc P)
    end.

  Lemma circuit_tail_precondition_of_complete
      (Γ : Assignment.t columns RegionId.t)
      (region : RegionId.t) (offset : Z)
      (tbl : EccSpec.fixed_table) (k : Z) (us : list Z)
      (i : nat) (acc : Point.t) (n : nat)
      (Hlen : List.length tbl = S n)
      (Hpre :
        incomplete_additions_complete_precondition Γ region offset n acc)
      (Hwindow :
        forall (j : nat) (w : EccSpec.fixed_window),
          List.nth_error tbl j = Some w ->
          incomplete_additions_window_point Γ region (offset + Z.of_nat j) =
          EccSpec.fixed_window_point w
            (EccSpec.window_digit k (i + j)%nat)
            (List.nth (i + j)%nat us 0))
      (Hacc_curve : point_on_curve acc)
      (Hacc_xr : UnOp.from (Point.x acc) = Point.x acc)
      (Hacc_yr : UnOp.from (Point.y acc) = Point.y acc)
      (Hwin_curve :
        forall (j : nat),
          (j < List.length tbl)%nat ->
          point_on_curve
            (incomplete_additions_window_point Γ region (offset + Z.of_nat j)))
      (Hwin_xr :
        forall (j : nat),
          (j < List.length tbl)%nat ->
          UnOp.from
            (Point.x (incomplete_additions_window_point Γ region
              (offset + Z.of_nat j))) =
            Point.x (incomplete_additions_window_point Γ region
              (offset + Z.of_nat j)))
      (Hwin_yr :
        forall (j : nat),
          (j < List.length tbl)%nat ->
          UnOp.from
            (Point.y (incomplete_additions_window_point Γ region
              (offset + Z.of_nat j))) =
            Point.y (incomplete_additions_window_point Γ region
              (offset + Z.of_nat j))) :
    fixed_scalar_mul_circuit_tail_precondition tbl k us i acc.
  Proof.
    revert offset i acc n Hlen Hpre Hwindow Hacc_curve Hacc_xr Hacc_yr
      Hwin_curve Hwin_xr Hwin_yr.
    induction tbl as [| w tbl IH]; intros offset i acc n Hlen Hpre Hwindow
      Hacc_curve Hacc_xr Hacc_yr Hwin_curve Hwin_xr Hwin_yr.
    - cbn [List.length] in Hlen. discriminate Hlen.
    - assert (H0 :
          incomplete_additions_window_point Γ region offset =
          EccSpec.fixed_window_point w (EccSpec.window_digit k i)
            (List.nth i us 0)).
      { replace offset with (offset + Z.of_nat 0) by lia.
        replace i with (i + 0)%nat by lia.
        exact (Hwindow 0%nat w eq_refl). }
      assert (Hwin0_curve :
          point_on_curve (incomplete_additions_window_point Γ region offset)).
      { replace offset with (offset + Z.of_nat 0) by lia.
        apply Hwin_curve. cbn [List.length]. lia. }
      assert (Hwin0_xr :
          UnOp.from
            (Point.x (incomplete_additions_window_point Γ region offset)) =
            Point.x (incomplete_additions_window_point Γ region offset)).
      { replace offset with (offset + Z.of_nat 0) by lia.
        apply Hwin_xr. cbn [List.length]. lia. }
      assert (Hwin0_yr :
          UnOp.from
            (Point.y (incomplete_additions_window_point Γ region offset)) =
            Point.y (incomplete_additions_window_point Γ region offset)).
      { replace offset with (offset + Z.of_nat 0) by lia.
        apply Hwin_yr. cbn [List.length]. lia. }
      destruct tbl as [| w' tbl'].
      + (* last window: needs on-curve + reduced of window and accumulator. *)
        cbn [fixed_scalar_mul_circuit_tail_precondition].
        rewrite <- H0.
        repeat split.
        * exact Hwin0_curve.
        * exact Hacc_curve.
        * exact Hwin0_xr.
        * exact Hwin0_yr.
        * exact Hacc_xr.
        * exact Hacc_yr.
      + (* non-last window: incomplete add, needs distinct nonzero x. *)
        cbn [List.length] in Hlen.
        injection Hlen as Hlen.
        subst n.
        cbn [incomplete_additions_complete_precondition] in Hpre.
        destruct Hpre as [Hpx Hpre].
        destruct Hpre as [Haccx Hpre].
        destruct Hpre as [Hdistinct Hpre].
        cbn [fixed_scalar_mul_circuit_tail_precondition].
        rewrite <- H0.
        repeat split.
        * exact Hpx.
        * exact Haccx.
        * exact Hdistinct.
        * apply (IH (offset + 1) (S i)
            (EccSpec.point_add acc
              (incomplete_additions_window_point Γ region offset))
            (List.length tbl')).
          -- reflexivity.
          -- exact Hpre.
          -- intros j w'' Hnth.
             replace (offset + 1 + Z.of_nat j) with
               (offset + Z.of_nat (S j)) by lia.
             replace (S i + j)%nat with (i + S j)%nat by lia.
             apply Hwindow. cbn [List.nth_error]. exact Hnth.
          -- apply (EccSpec.point_add_on_curve_x_distinct acc
               (incomplete_additions_window_point Γ region offset)
               Hacc_curve Hwin0_curve Haccx Hpx).
             intro Heq. apply Hdistinct. symmetry. exact Heq.
          -- exact (proj1 (point_add_reduced acc
               (incomplete_additions_window_point Γ region offset)
               Hacc_xr Hacc_yr Hwin0_xr Hwin0_yr)).
          -- exact (proj2 (point_add_reduced acc
               (incomplete_additions_window_point Γ region offset)
               Hacc_xr Hacc_yr Hwin0_xr Hwin0_yr)).
          -- intros j Hj.
             cbn [List.length] in Hj.
             replace (offset + 1 + Z.of_nat j) with
               (offset + Z.of_nat (S j)) by lia.
             apply Hwin_curve. cbn [List.length]. lia.
          -- intros j Hj.
             cbn [List.length] in Hj.
             replace (offset + 1 + Z.of_nat j) with
               (offset + Z.of_nat (S j)) by lia.
             apply Hwin_xr. cbn [List.length]. lia.
          -- intros j Hj.
             cbn [List.length] in Hj.
             replace (offset + 1 + Z.of_nat j) with
               (offset + Z.of_nat (S j)) by lia.
             apply Hwin_yr. cbn [List.length]. lia.
  Qed.

  Lemma circuit_tail_eq_fixed_scalar_mul_aux
      (tbl : EccSpec.fixed_table) (k : Z) (us : list Z)
      (i : nat) (acc : Point.t)
      (Hpre : fixed_scalar_mul_circuit_tail_precondition tbl k us i acc) :
    fixed_scalar_mul_circuit_tail tbl k us i acc =
    EccSpec.fixed_scalar_mul_aux tbl k us i acc.
  Proof.
    revert i acc Hpre.
    induction tbl as [| w tbl IH]; intros i acc Hpre.
    - reflexivity.
    - destruct tbl as [| w' tbl'];
        cbn [fixed_scalar_mul_circuit_tail EccSpec.fixed_scalar_mul_aux
          fixed_scalar_mul_circuit_tail_precondition] in *.
      + (* last window: complete addition in swapped order, reconciled by
           on-curve commutativity (no distinctness needed). *)
        destruct Hpre as [HPoc Hpre].
        destruct Hpre as [Haccoc Hpre].
        destruct Hpre as [HPxr Hpre].
        destruct Hpre as [HPyr Hpre].
        destruct Hpre as [Haccxr Haccyr].
        apply EccSpec.point_add_comm_on_curve_nonzero_reduced.
        * exact HPoc.
        * exact Haccoc.
        * apply (EccSpec.pallas_curve_x_nonzero
            (Point.x (EccSpec.fixed_window_point w (EccSpec.window_digit k i)
              (List.nth i us 0)))
            (Point.y (EccSpec.fixed_window_point w (EccSpec.window_digit k i)
              (List.nth i us 0)))).
          exact HPoc.
        * apply (EccSpec.pallas_curve_x_nonzero (Point.x acc) (Point.y acc)).
          exact Haccoc.
        * exact HPxr.
        * exact Haccxr.
        * exact HPyr.
        * exact Haccyr.
      + destruct Hpre as [HPx Hpre].
        destruct Hpre as [Haccx Hpre].
        destruct Hpre as [Hdistinct Htail].
        rewrite (point_add_incomplete_eq_point_add_swap
          (EccSpec.fixed_window_point w (EccSpec.window_digit k i)
            (List.nth i us 0)) acc HPx Haccx Hdistinct).
        exact (IH (S i)
          (EccSpec.point_add acc
            (EccSpec.fixed_window_point w (EccSpec.window_digit k i)
              (List.nth i us 0))) Htail).
  Qed.

  Definition fixed_scalar_mul_circuit_precondition
      (tbl : EccSpec.fixed_table) (k : Z) (us : list Z) : Prop :=
    match tbl with
    | [] => True
    | w :: tbl =>
        fixed_scalar_mul_circuit_tail_precondition tbl k us 1%nat
          (EccSpec.fixed_window_point w (EccSpec.window_digit k 0%nat)
            (List.nth 0%nat us 0))
    end.

  Lemma fixed_scalar_mul_circuit_eq_fixed_scalar_mul
      (tbl : EccSpec.fixed_table) (k : Z) (us : list Z)
      (Hpre : fixed_scalar_mul_circuit_precondition tbl k us) :
    fixed_scalar_mul_circuit tbl k us = EccSpec.fixed_scalar_mul tbl k us.
  Proof.
    destruct tbl as [| w tbl].
    - reflexivity.
    - unfold fixed_scalar_mul_circuit, EccSpec.fixed_scalar_mul in *.
      cbn [EccSpec.fixed_scalar_mul_aux].
      rewrite circuit_tail_eq_fixed_scalar_mul_aux.
      + rewrite EccSpec.point_add_identity_left.
        reflexivity.
      + exact Hpre.
  Qed.

  Definition fixed_window_default : EccSpec.fixed_window := {|
    EccSpec.fw_coeffs := [];
    EccSpec.fw_z := 0;
  |}.

  Definition spend_auth_g_fixed_table : EccSpec.fixed_table :=
    OrchardCircuitSpec.spend_auth_g orchard_internal_params.

  (** The 83 incomplete-addition edges of the SpendAuthG full-width ladder
      (rows 1..83).  Row 84 is a *complete* addition, not an incomplete-add
      edge, so it is deliberately excluded — see [spend_auth_g_table_split]. *)
  Definition spend_auth_g_ladder_distinct_precondition
      (Γ : Assignment.t columns RegionId.t) : Prop :=
    incomplete_additions_distinct_precondition Γ
      (RegionId.SpendAuthority
        RegionId.SpendAuthority.FullFixedIncomplete) 1 83
      (incomplete_additions_window_point Γ
        (RegionId.SpendAuthority
          RegionId.SpendAuthority.FullFixedIncomplete) 0).

  Definition spend_auth_g_first : EccSpec.fixed_window :=
    List.hd fixed_window_default spend_auth_g_fixed_table.

  Definition spend_auth_g_middle : EccSpec.fixed_table :=
    List.firstn 83 (List.skipn 1 spend_auth_g_fixed_table).

  Definition spend_auth_g_last : EccSpec.fixed_window :=
    List.nth 84 spend_auth_g_fixed_table fixed_window_default.

  Lemma spend_auth_g_table_split :
    EccSpec.fixed_table_of_rows
      Garden.Orchard.constants.fixed_bases.spend_auth_g.full_fixed_rows =
    spend_auth_g_first :: spend_auth_g_middle ++ [spend_auth_g_last].
  Proof. reflexivity. Qed.

  Lemma spend_auth_g_middle_length :
    List.length spend_auth_g_middle = 83%nat.
  Proof. reflexivity. Qed.

  Lemma spend_auth_g_row0_row1_window_x_distinct
      (d0 d1 : Z)
      (Hd0 : 0 <= d0 < 8)
      (Hd1 : 0 <= d1 < 8) :
    UnOp.from
      (Point.x
        (EccSpec.fixed_window_point
          (EccSpec.fixed_window_of_row
            Garden.Orchard.constants.fixed_bases.spend_auth_g.full_fixed_row_1)
          d1 0)) <>
    UnOp.from
      (Point.x
        (EccSpec.fixed_window_point
          (EccSpec.fixed_window_of_row
            Garden.Orchard.constants.fixed_bases.spend_auth_g.full_fixed_row_0)
          d0 0)).
  Proof.
    assert (Hd0_cases :
        d0 = 0 \/ d0 = 1 \/ d0 = 2 \/ d0 = 3 \/
        d0 = 4 \/ d0 = 5 \/ d0 = 6 \/ d0 = 7) by lia.
    assert (Hd1_cases :
        d1 = 0 \/ d1 = 1 \/ d1 = 2 \/ d1 = 3 \/
        d1 = 4 \/ d1 = 5 \/ d1 = 6 \/ d1 = 7) by lia.
    repeat match goal with
    | H : _ \/ _ |- _ => destruct H as [H | H]
    end; subst; compute; discriminate.
  Qed.

  Lemma incomplete_output_scalar_mul_incomplete_tail
      (Γ : Assignment.t columns RegionId.t)
      (region : RegionId.t) (offset : Z)
      (tbl : EccSpec.fixed_table) (k : Z) (us : list Z)
      (i : nat) (acc : Point.t)
      (Hwindow :
        forall (j : nat) (w : EccSpec.fixed_window),
          List.nth_error tbl j = Some w ->
          incomplete_additions_window_point Γ region (offset + Z.of_nat j) =
          EccSpec.fixed_window_point w
            (EccSpec.window_digit k (i + j)%nat)
            (List.nth (i + j)%nat us 0)) :
    incomplete_additions_output Γ region offset (List.length tbl) acc =
      fixed_scalar_mul_incomplete_tail tbl k us i acc.
  Proof.
    revert acc i offset Hwindow.
    induction tbl as [| w tbl IH]; intros acc i offset Hwindow.
    - reflexivity.
    - cbn [incomplete_additions_output fixed_scalar_mul_incomplete_tail
        List.length].
      assert (H0 :
        incomplete_additions_window_point Γ region offset =
        EccSpec.fixed_window_point w (EccSpec.window_digit k i)
          (List.nth i us 0)).
      { replace offset with (offset + Z.of_nat 0) by lia.
        replace i with (i + 0)%nat by lia.
        exact (Hwindow 0%nat w eq_refl). }
      rewrite H0.
      apply IH.
      intros j w' Hnth.
      replace (offset + 1 + Z.of_nat j) with
        (offset + Z.of_nat (S j)) by lia.
      replace (S i + j)%nat with (i + S j)%nat by lia.
      exact (Hwindow (S j) w' Hnth).
  Qed.

  Lemma fixed_scalar_mul_circuit_tail_app_last
      (middle : EccSpec.fixed_table) (last : EccSpec.fixed_window)
      (k : Z) (us : list Z) (i : nat) (acc : Point.t) :
    fixed_scalar_mul_circuit_tail (middle ++ [last]) k us i acc =
    EccSpec.point_add
      (EccSpec.fixed_window_point last
        (EccSpec.window_digit k (i + List.length middle)%nat)
        (List.nth (i + List.length middle)%nat us 0))
      (fixed_scalar_mul_incomplete_tail middle k us i acc).
  Proof.
    revert i acc.
    induction middle as [| w middle IH]; intros i acc.
    - cbn [List.app List.length fixed_scalar_mul_circuit_tail
        fixed_scalar_mul_incomplete_tail].
      replace (i + 0)%nat with i by lia.
      reflexivity.
    - cbn [List.app List.length fixed_scalar_mul_circuit_tail
        fixed_scalar_mul_incomplete_tail].
      rewrite IH.
      replace (i + S (List.length middle))%nat with
        (S i + List.length middle)%nat by lia.
      destruct middle; reflexivity.
  Qed.

  Lemma full_with_rows_circuit_tail_correct
      (Γ : Assignment.t columns RegionId.t)
      (incomplete_region last_region : RegionId.t)
      (rows : list Garden.Orchard.circuit.fixed_base_row)
      (first last : EccSpec.fixed_window) (middle : EccSpec.fixed_table)
      (k : Z) (us : list Z)
      (Hfacts :
        interpret_facts Γ
          (layouter_facts
            (let🞵 result :=
              Garden.Orchard.circuit
                .synth_full_mul_incomplete_with_rows
                incomplete_region rows in
             Garden.Orchard.circuit
               .synthesize_full_fixed_base_mul_last_region last_region result)))
      (Hgates :
        satisfies_gates Γ
          (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty))
      (Hpre :
        incomplete_additions_precondition Γ incomplete_region 1 83
          (incomplete_additions_window_point Γ incomplete_region 0))
      (Htable :
        EccSpec.fixed_table_of_rows rows = first :: middle ++ [last])
      (Hmiddle_len : List.length middle = 83%nat)
      (Hwindow :
        forall (j : nat) (w : EccSpec.fixed_window),
          List.nth_error (first :: middle ++ [last]) j = Some w ->
          incomplete_additions_window_point Γ incomplete_region (Z.of_nat j) =
          EccSpec.fixed_window_point w
            (EccSpec.window_digit k j)
            (List.nth j us 0)) :
    Field.map_mod
      (assigned_point_value Γ
        (layouter_value
          (let🞵 result :=
            Garden.Orchard.circuit
              .synth_full_mul_incomplete_with_rows
              incomplete_region rows in
           Garden.Orchard.circuit
             .synthesize_full_fixed_base_mul_last_region last_region result))) =
      EccSpec.point_add
        (EccSpec.fixed_window_point last
          (EccSpec.window_digit k 84%nat)
          (List.nth 84%nat us 0))
        (fixed_scalar_mul_incomplete_tail middle k us 1%nat
          (EccSpec.fixed_window_point first
            (EccSpec.window_digit k 0%nat)
            (List.nth 0%nat us 0))).
  Proof.
    rewrite (synthesize_full_fixed_base_mul_with_rows_correct Γ
      incomplete_region last_region rows Hfacts Hgates Hpre).
    assert (Hfirst :
        incomplete_additions_window_point Γ incomplete_region 0 =
        EccSpec.fixed_window_point first
          (EccSpec.window_digit k 0%nat)
          (List.nth 0%nat us 0)).
    { exact (Hwindow 0%nat first eq_refl). }
    assert (Hlast :
        incomplete_additions_window_point Γ incomplete_region 84 =
        EccSpec.fixed_window_point last
          (EccSpec.window_digit k 84%nat)
          (List.nth 84%nat us 0)).
    { replace 84 with (Z.of_nat (S (List.length middle))) by
        (rewrite Hmiddle_len; reflexivity).
      replace 84%nat with (S (List.length middle)) by
        (rewrite Hmiddle_len; reflexivity).
      apply Hwindow.
      cbn [List.nth_error].
      rewrite nth_error_app2 by lia.
      rewrite Nat.sub_diag.
      reflexivity. }
    rewrite Hlast.
    rewrite <- Hmiddle_len.
    rewrite (incomplete_output_scalar_mul_incomplete_tail Γ
      incomplete_region 1 middle k us 1%nat
      (incomplete_additions_window_point Γ incomplete_region 0)).
    - rewrite Hfirst.
      reflexivity.
    - intros j w Hnth.
      replace (1 + Z.of_nat j) with (Z.of_nat (S j)) by lia.
      replace (1 + j)%nat with (S j) by lia.
      apply Hwindow.
      cbn [List.nth_error].
      rewrite nth_error_app1.
      + exact Hnth.
      + apply nth_error_Some.
        rewrite Hnth.
        discriminate.
  Qed.

  Lemma full_with_rows_scalar_mul_correct
      (Γ : Assignment.t columns RegionId.t)
      (incomplete_region last_region : RegionId.t)
      (rows : list Garden.Orchard.circuit.fixed_base_row)
      (first last : EccSpec.fixed_window) (middle : EccSpec.fixed_table)
      (k : Z) (us : list Z)
      (Hfacts :
        interpret_facts Γ
          (layouter_facts
            (let🞵 result :=
              Garden.Orchard.circuit
                .synth_full_mul_incomplete_with_rows
                incomplete_region rows in
             Garden.Orchard.circuit
               .synthesize_full_fixed_base_mul_last_region last_region result)))
      (Hgates :
        satisfies_gates Γ
          (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty))
      (Hpre :
        incomplete_additions_precondition Γ incomplete_region 1 83
          (incomplete_additions_window_point Γ incomplete_region 0))
      (Htable :
        EccSpec.fixed_table_of_rows rows = first :: middle ++ [last])
      (Hmiddle_len : List.length middle = 83%nat)
      (Hwindow :
        forall (j : nat) (w : EccSpec.fixed_window),
          List.nth_error (first :: middle ++ [last]) j = Some w ->
          incomplete_additions_window_point Γ incomplete_region (Z.of_nat j) =
          EccSpec.fixed_window_point w
            (EccSpec.window_digit k j)
            (List.nth j us 0))
      (Hcircuit_pre :
        fixed_scalar_mul_circuit_precondition (first :: middle ++ [last]) k us) :
    Field.map_mod
      (assigned_point_value Γ
        (layouter_value
          (let🞵 result :=
            Garden.Orchard.circuit
              .synth_full_mul_incomplete_with_rows
              incomplete_region rows in
           Garden.Orchard.circuit
             .synthesize_full_fixed_base_mul_last_region last_region result))) =
    EccSpec.fixed_scalar_mul (first :: middle ++ [last]) k us.
  Proof.
    rewrite (full_with_rows_circuit_tail_correct Γ
      incomplete_region last_region rows first last middle k us
      Hfacts Hgates Hpre Htable Hmiddle_len Hwindow).
    replace 84%nat with (1 + List.length middle)%nat by
      (rewrite Hmiddle_len; reflexivity).
    rewrite <- (fixed_scalar_mul_circuit_tail_app_last middle last k us 1%nat
      (EccSpec.fixed_window_point first
        (EccSpec.window_digit k 0%nat)
        (List.nth 0%nat us 0))).
    change (fixed_scalar_mul_circuit (first :: middle ++ [last]) k us =
      EccSpec.fixed_scalar_mul (first :: middle ++ [last]) k us).
    apply fixed_scalar_mul_circuit_eq_fixed_scalar_mul.
    exact Hcircuit_pre.
  Qed.

  Lemma spend_auth_g_window_correct
      (Γ : Assignment.t columns RegionId.t)
      (Hfacts :
        interpret_facts Γ
          (layouter_facts
            (Garden.Orchard.circuit
              .synth_full_mul_incomplete_with_rows
              (RegionId.SpendAuthority
                RegionId.SpendAuthority.FullFixedIncomplete)
              Garden.Orchard.constants.fixed_bases.spend_auth_g.full_fixed_rows)))
      (Hgates :
        satisfies_gates Γ
          (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty))
      (j : nat) (w : EccSpec.fixed_window)
      (Hnth :
        List.nth_error (spend_auth_g_first :: spend_auth_g_middle ++
          [spend_auth_g_last]) j = Some w) :
    incomplete_additions_window_point Γ
      (RegionId.SpendAuthority RegionId.SpendAuthority.FullFixedIncomplete)
      (Z.of_nat j) =
    EccSpec.fixed_window_point w
      (EccSpec.window_digit
        (read_scalar_from_windows Γ
          (RegionId.SpendAuthority
            RegionId.SpendAuthority.FullFixedIncomplete) 85)
        j)
      (List.nth j
        (read_us Γ
          (RegionId.SpendAuthority
            RegionId.SpendAuthority.FullFixedIncomplete) 85)
        0).
  Proof.
    unfold spend_auth_g_first, spend_auth_g_middle, spend_auth_g_last,
      spend_auth_g_fixed_table, OrchardCircuitSpec.spend_auth_g,
      orchard_internal_params in Hnth.
    cbn in Hnth.
    do 85
      (destruct j as [| j];
        [ cbn in Hnth;
          inversion Hnth; subst; clear Hnth;
          rewrite <- incomplete_additions_window_point_map_mod;
          unfold incomplete_additions_window_point;
          eapply
            (full_width_incomplete_window_correct Γ
              (RegionId.SpendAuthority
                RegionId.SpendAuthority.FullFixedIncomplete)
              Garden.Orchard.constants.fixed_bases.spend_auth_g
                .full_fixed_rows);
          [ reflexivity | exact Hfacts | exact Hgates | lia ]
        | cbn in Hnth ]).
    cbn in Hnth.
    destruct j; discriminate Hnth.
  Qed.

  Lemma spend_auth_g_window_x_nonzero
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (i : nat) (Hi : (i < 85)%nat) :
    UnOp.from
      (Point.x
        (incomplete_additions_window_point Γ
          (RegionId.SpendAuthority
            RegionId.SpendAuthority.FullFixedIncomplete)
          (Z.of_nat i))) <> 0.
  Proof.
    pose proof (spend_authority_fixed_base_facts Γ Hcircuit) as Hfacts.
    unfold Garden.Orchard.circuit.synthesize_full_fixed_base_mul_spend_auth_g
      in Hfacts.
    apply interpret_layouter_facts_bind_left in Hfacts.
    apply (full_width_incomplete_window_x_nonzero Γ
        (RegionId.SpendAuthority
          RegionId.SpendAuthority.FullFixedIncomplete)
      Garden.Orchard.constants.fixed_bases.spend_auth_g.full_fixed_rows
      i Hfacts (holds_gates Γ Hcircuit) Hi).
  Qed.

  Lemma full_width_incomplete_region_window_on_curve
      (Γ : Assignment.t columns RegionId.t)
      (region : RegionId.t)
      (rows : list Garden.Orchard.circuit.fixed_base_row)
      (i : nat)
      (Hfacts :
        interpret_facts Γ
          (layouter_facts
            (Garden.Orchard.circuit
              .synth_full_mul_incomplete_with_rows
              region rows)))
      (Hgates :
        satisfies_gates Γ
          (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty))
      (Hi : (i < 85)%nat) :
    point_on_curve
      (incomplete_additions_window_point Γ region (Z.of_nat i)).
  Proof.
    unfold point_on_curve, incomplete_additions_window_point.
    pose proof
      (full_width_fixed_window_on_curve_of_facts Γ
        (layouter_facts
          (Garden.Orchard.circuit
            .synth_full_mul_incomplete_with_rows
            region rows))
        region (Z.of_nat i) Hfacts) as Hcurve.
    cbn [eval_expression rotated_row Rotation.cur] in Hcurve.
    cbn [Point.x Point.y].
    change (Γ ⊢ ⟦ Garden.Halo2.halo2_gadgets.ecc.chip.witness_point
        .curve_eqn Advice.A0 Advice.A1 ⟧ (region, Z.of_nat i) = 0).
    exact (Hcurve
      (full_incomplete_selector_fact
        region rows i Hi)
      Hgates).
  Qed.

  Lemma spend_auth_g_initial_acc_x_nonzero
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    UnOp.from
      (Point.x
        (incomplete_additions_window_point Γ
          (RegionId.SpendAuthority
            RegionId.SpendAuthority.FullFixedIncomplete) 0)) <> 0.
  Proof.
    replace 0 with (Z.of_nat 0) by reflexivity.
    apply spend_auth_g_window_x_nonzero.
    - exact Hcircuit.
    - lia.
  Qed.

  Lemma spend_auth_g_complete_of_distinct
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (Hdistinct : spend_auth_g_ladder_distinct_precondition Γ) :
    incomplete_additions_complete_precondition Γ
      (RegionId.SpendAuthority
        RegionId.SpendAuthority.FullFixedIncomplete) 1 83
      (incomplete_additions_window_point Γ
        (RegionId.SpendAuthority
          RegionId.SpendAuthority.FullFixedIncomplete) 0).
  Proof.
    pose proof (spend_authority_fixed_base_facts Γ Hcircuit) as Hfacts.
    unfold Garden.Orchard.circuit.synthesize_full_fixed_base_mul_spend_auth_g
      in Hfacts.
    apply interpret_layouter_facts_bind_left in Hfacts.
    unfold spend_auth_g_ladder_distinct_precondition in Hdistinct.
    apply incomplete_complete_precondition_of_distinct.
    - replace 0 with (Z.of_nat 0) by reflexivity.
      apply (full_width_incomplete_region_window_on_curve Γ
        (RegionId.SpendAuthority
          RegionId.SpendAuthority.FullFixedIncomplete)
        Garden.Orchard.constants.fixed_bases.spend_auth_g.full_fixed_rows
        0%nat Hfacts (holds_gates Γ Hcircuit)).
      lia.
    - exact (spend_auth_g_initial_acc_x_nonzero Γ Hcircuit).
    - intros i Hi.
      replace (1 + Z.of_nat i) with (Z.of_nat (S i)) by lia.
      apply (full_width_incomplete_region_window_on_curve Γ
        (RegionId.SpendAuthority
          RegionId.SpendAuthority.FullFixedIncomplete)
        Garden.Orchard.constants.fixed_bases.spend_auth_g.full_fixed_rows
        (S i) Hfacts (holds_gates Γ Hcircuit)).
      lia.
    - intros i Hi.
      replace (1 + Z.of_nat i) with (Z.of_nat (S i)) by lia.
      apply (spend_auth_g_window_x_nonzero Γ Hcircuit (S i)).
      lia.
    - exact Hdistinct.
  Qed.

  Lemma spend_auth_g_complete_output_on_curve
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (Hpre :
        incomplete_additions_complete_precondition Γ
          (RegionId.SpendAuthority
            RegionId.SpendAuthority.FullFixedIncomplete) 1 83
          (incomplete_additions_window_point Γ
            (RegionId.SpendAuthority
              RegionId.SpendAuthority.FullFixedIncomplete) 0)) :
    point_on_curve
      (complete_additions_output Γ
        (RegionId.SpendAuthority
          RegionId.SpendAuthority.FullFixedIncomplete) 1 83
        (incomplete_additions_window_point Γ
          (RegionId.SpendAuthority
            RegionId.SpendAuthority.FullFixedIncomplete) 0)).
  Proof.
    pose proof (spend_authority_fixed_base_facts Γ Hcircuit) as Hfacts.
    unfold Garden.Orchard.circuit.synthesize_full_fixed_base_mul_spend_auth_g
      in Hfacts.
    apply interpret_layouter_facts_bind_left in Hfacts.
    eapply complete_additions_output_on_curve.
    - replace 0 with (Z.of_nat 0) by reflexivity.
      apply (full_width_incomplete_region_window_on_curve Γ
        (RegionId.SpendAuthority
          RegionId.SpendAuthority.FullFixedIncomplete)
        Garden.Orchard.constants.fixed_bases.spend_auth_g.full_fixed_rows
        0%nat Hfacts (holds_gates Γ Hcircuit)).
      lia.
    - intros i Hi.
      replace (1 + Z.of_nat i) with (Z.of_nat (S i)) by lia.
      apply (full_width_incomplete_region_window_on_curve Γ
        (RegionId.SpendAuthority
          RegionId.SpendAuthority.FullFixedIncomplete)
        Garden.Orchard.constants.fixed_bases.spend_auth_g.full_fixed_rows
        (S i) Hfacts (holds_gates Γ Hcircuit)).
      lia.
    - exact Hpre.
  Qed.

  Lemma full_spend_auth_g_mul_correct
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (Hpre :
        incomplete_additions_precondition Γ
          (RegionId.SpendAuthority
            RegionId.SpendAuthority.FullFixedIncomplete) 1 83
          (incomplete_additions_window_point Γ
            (RegionId.SpendAuthority
              RegionId.SpendAuthority.FullFixedIncomplete) 0))
      (Hcircuit_pre :
        fixed_scalar_mul_circuit_precondition
          (OrchardCircuitSpec.spend_auth_g orchard_internal_params)
          (read_scalar_from_windows Γ
            (RegionId.SpendAuthority
              RegionId.SpendAuthority.FullFixedIncomplete) 85)
          (read_us Γ
            (RegionId.SpendAuthority
              RegionId.SpendAuthority.FullFixedIncomplete) 85)) :
    Field.map_mod
      (assigned_point_value Γ
        (layouter_value
          Garden.Orchard.circuit.synthesize_full_fixed_base_mul_spend_auth_g)) =
    EccSpec.fixed_scalar_mul
      (OrchardCircuitSpec.spend_auth_g orchard_internal_params)
      (read_scalar_from_windows Γ
        (RegionId.SpendAuthority
          RegionId.SpendAuthority.FullFixedIncomplete) 85)
      (read_us Γ
        (RegionId.SpendAuthority
          RegionId.SpendAuthority.FullFixedIncomplete) 85).
  Proof.
    pose proof (spend_authority_fixed_base_facts Γ Hcircuit) as Hfacts.
    pose proof Hfacts as Hincomplete_facts.
    unfold Garden.Orchard.circuit.synthesize_full_fixed_base_mul_spend_auth_g
      in Hfacts, Hincomplete_facts |- *.
    apply interpret_layouter_facts_bind_left in Hincomplete_facts.
    eapply full_with_rows_scalar_mul_correct
      with (first := spend_auth_g_first)
           (middle := spend_auth_g_middle)
           (last := spend_auth_g_last).
    - exact Hfacts.
    - exact (holds_gates Γ Hcircuit).
    - exact Hpre.
    - exact spend_auth_g_table_split.
    - exact spend_auth_g_middle_length.
    - intros j w Hnth.
      exact (spend_auth_g_window_correct Γ Hincomplete_facts
        (holds_gates Γ Hcircuit) j w Hnth).
    - exact Hcircuit_pre.
  Qed.

  Lemma spend_auth_g_circuit_of_complete
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (Hpre :
        incomplete_additions_complete_precondition Γ
          (RegionId.SpendAuthority
            RegionId.SpendAuthority.FullFixedIncomplete) 1 83
          (incomplete_additions_window_point Γ
            (RegionId.SpendAuthority
              RegionId.SpendAuthority.FullFixedIncomplete) 0)) :
    fixed_scalar_mul_circuit_precondition
      (OrchardCircuitSpec.spend_auth_g orchard_internal_params)
      (read_scalar_from_windows Γ
        (RegionId.SpendAuthority
          RegionId.SpendAuthority.FullFixedIncomplete) 85)
      (read_us Γ
        (RegionId.SpendAuthority
          RegionId.SpendAuthority.FullFixedIncomplete) 85).
  Proof.
    pose proof (spend_authority_fixed_base_facts Γ Hcircuit) as Hfacts.
    unfold Garden.Orchard.circuit.synthesize_full_fixed_base_mul_spend_auth_g
      in Hfacts.
    apply interpret_layouter_facts_bind_left in Hfacts.
    pose proof (spend_auth_g_window_correct Γ Hfacts
      (holds_gates Γ Hcircuit) 0%nat spend_auth_g_first eq_refl) as Hfirst.
    unfold OrchardCircuitSpec.spend_auth_g, orchard_internal_params.
    rewrite spend_auth_g_table_split.
    cbn [fixed_scalar_mul_circuit_precondition].
    rewrite <- Hfirst.
    eapply circuit_tail_precondition_of_complete
      with (n := 83%nat).
    - rewrite List.length_app, spend_auth_g_middle_length. reflexivity.
    - exact Hpre.
    - intros j w Hnth.
      replace (1 + Z.of_nat j) with (Z.of_nat (S j)) by lia.
      replace (1 + j)%nat with (S j) by lia.
      apply (spend_auth_g_window_correct Γ Hfacts
        (holds_gates Γ Hcircuit)).
      cbn [List.nth_error].
      exact Hnth.
    - replace 0 with (Z.of_nat 0) by reflexivity.
      apply (full_width_incomplete_region_window_on_curve Γ
        (RegionId.SpendAuthority RegionId.SpendAuthority.FullFixedIncomplete)
        Garden.Orchard.constants.fixed_bases.spend_auth_g.full_fixed_rows
        0%nat Hfacts (holds_gates Γ Hcircuit)).
      lia.
    - exact (proj1 (incomplete_additions_window_point_reduced Γ
        (RegionId.SpendAuthority RegionId.SpendAuthority.FullFixedIncomplete)
        0)).
    - exact (proj2 (incomplete_additions_window_point_reduced Γ
        (RegionId.SpendAuthority RegionId.SpendAuthority.FullFixedIncomplete)
        0)).
    - intros j Hj.
      rewrite List.length_app, spend_auth_g_middle_length in Hj.
      cbn [List.length] in Hj.
      replace (1 + Z.of_nat j) with (Z.of_nat (S j)) by lia.
      apply (full_width_incomplete_region_window_on_curve Γ
        (RegionId.SpendAuthority RegionId.SpendAuthority.FullFixedIncomplete)
        Garden.Orchard.constants.fixed_bases.spend_auth_g.full_fixed_rows
        (S j) Hfacts (holds_gates Γ Hcircuit)).
      lia.
    - intros j Hj.
      exact (proj1 (incomplete_additions_window_point_reduced Γ
        (RegionId.SpendAuthority RegionId.SpendAuthority.FullFixedIncomplete)
        (1 + Z.of_nat j))).
    - intros j Hj.
      exact (proj2 (incomplete_additions_window_point_reduced Γ
        (RegionId.SpendAuthority RegionId.SpendAuthority.FullFixedIncomplete)
        (1 + Z.of_nat j))).
  Qed.

  Lemma full_spend_auth_g_mul_correct_of_complete
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (Hpre :
        incomplete_additions_complete_precondition Γ
          (RegionId.SpendAuthority
            RegionId.SpendAuthority.FullFixedIncomplete) 1 83
          (incomplete_additions_window_point Γ
            (RegionId.SpendAuthority
              RegionId.SpendAuthority.FullFixedIncomplete) 0)) :
    Field.map_mod
      (assigned_point_value Γ
        (layouter_value
          Garden.Orchard.circuit.synthesize_full_fixed_base_mul_spend_auth_g)) =
    EccSpec.fixed_scalar_mul
      (OrchardCircuitSpec.spend_auth_g orchard_internal_params)
      (read_scalar_from_windows Γ
        (RegionId.SpendAuthority
          RegionId.SpendAuthority.FullFixedIncomplete) 85)
      (read_us Γ
        (RegionId.SpendAuthority
          RegionId.SpendAuthority.FullFixedIncomplete) 85).
  Proof.
    apply full_spend_auth_g_mul_correct.
    - exact Hcircuit.
    - apply incomplete_complete_implies_precondition.
      exact Hpre.
    - exact
        (spend_auth_g_circuit_of_complete
          Γ Hcircuit Hpre).
  Qed.

  (* ---------------------------------------------------------------------- *)
  (* Running-sum fixed-base windows (the short [value_commit_v] and          *)
  (* base-field [nullifier_k] multiplications).                              *)
  (*                                                                          *)
  (* Their window rows are governed by [Selector.QMulFixedRunningSum] and the *)
  (* [running_sum_coordinates_check_gate], whose [coords_check] carries the   *)
  (* same "on-curve" conjunct as the full-width gate (on advice A0/A1,        *)
  (* independent of the window digit).  This mirrors the [full_width_*]       *)
  (* development for those two tables, providing the [Honcurve] feed for the  *)
  (* per-window QR forcing.                                                   *)
  (* ---------------------------------------------------------------------- *)

  (* [QMulFixedRunningSum] is enabled at every window row [i] of a short /
     base-field incomplete-addition region by [enable_mul_fixed_running_sum_rows]
     (the running-sum analogue of [assign_full_window_witnesses_selector_fact]). *)
  Lemma running_sum_rows_selector_fact
      (region : RegionId.t) (offset : Z) (count i : nat) :
    (i < count)%nat ->
    List.In
      (Fact.SelectorOn Selector.QMulFixedRunningSum region
        (offset + Z.of_nat i))
      (region_facts region
        (Garden.Orchard.circuit.enable_mul_fixed_running_sum_rows offset count)).
  Proof.
    revert offset i.
    induction count as [| count IH]; intros offset i Hi.
    - lia.
    - destruct i as [| i].
      + cbn [Garden.Orchard.circuit.enable_mul_fixed_running_sum_rows
          region_facts].
        left. f_equal. lia.
      + cbn [Garden.Orchard.circuit.enable_mul_fixed_running_sum_rows
          region_facts].
        right.
        replace (offset + Z.of_nat (S i)) with
          (offset + 1 + Z.of_nat i) by lia.
        apply IH. lia.
  Qed.

  (* On-curve extraction from the running-sum coordinates-check gate: the
     assigned window point (A0, A1) satisfies the Pallas curve equation.  The
     running-sum analogue of [full_width_fixed_window_on_curve]. *)
  Lemma running_sum_fixed_window_on_curve
      (Γ : Assignment.t columns RegionId.t)
      (region : RegionId.t) (row : Z)
      (Hselector :
        Γ ⊢ ⟦ Selector.QMulFixedRunningSum ⟧ (region, row) <> 0)
      (Hgate :
        Γ ⊢ ⟦ Garden.Halo2.halo2_gadgets.ecc.chip.mul_fixed
            .running_sum_coordinates_check_gate ⟧ (region, row)) :
    Γ ⊢ ⟦ Garden.Halo2.halo2_gadgets.ecc.chip.witness_point
        .curve_eqn Advice.A0 Advice.A1 ⟧ (region, row) = 0.
  Proof.
    cbn [eval_gate Gate.constraints Constraints.with_selector eval_constraints
      eval_named_constraint eval_constraint eval_selector eval_expression
      rotated_row Rotation.cur
      Garden.Halo2.halo2_gadgets.ecc.chip.mul_fixed
        .running_sum_coordinates_check_gate
      Garden.Halo2.halo2_gadgets.ecc.chip.mul_fixed.coords_check
      Garden.Halo2.halo2_gadgets.ecc.chip.mul_fixed.interpolated_x
      Garden.Halo2.halo2_gadgets.ecc.chip.witness_point.curve_eqn
      Garden.Halo2.halo2_gadgets.utilities.square
      List.map List.app] in Hgate |- *.
    destruct Hgate as [_ Hgate].
    destruct Hgate as [_ Hon_curve].
    exact (Hon_curve Hselector).
  Qed.

  Lemma running_sum_fixed_window_on_curve_of_facts
      (Γ : Assignment.t columns RegionId.t)
      (facts : list (Fact.t columns RegionId.t))
      (region : RegionId.t) (row : Z)
      (Hfacts : interpret_facts Γ facts)
      (Hselector :
        List.In (Fact.SelectorOn Selector.QMulFixedRunningSum region row) facts)
      (Hgates :
        satisfies_gates Γ
          (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)) :
    Γ ⊢ ⟦ Garden.Halo2.halo2_gadgets.ecc.chip.witness_point
        .curve_eqn Advice.A0 Advice.A1 ⟧ (region, row) = 0.
  Proof.
    apply (running_sum_fixed_window_on_curve Γ region row).
    - exact (selector_nonzero_of_facts Γ facts
        Selector.QMulFixedRunningSum region row Hfacts Hselector).
    - apply (satisfies_gates_at Γ
        (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)
        Garden.Halo2.halo2_gadgets.ecc.chip.mul_fixed
          .running_sum_coordinates_check_gate
        region row); [| exact Hgates].
      cbn. repeat (first [left; reflexivity | right]).
  Qed.

  (* Correctness of a running-sum window row: the assigned point (A0, A1) equals
     the spec window point, with digit read as the running-sum word
     [z_cur - z_next * h] (A4 current/next) and square-root witness [u] on A5.
     The running-sum analogue of [full_width_fixed_window_correct]. *)
  Lemma running_sum_fixed_window_correct
      (Γ : Assignment.t columns RegionId.t)
      (region : RegionId.t) (row : Z)
      (c0 c1 c2 c3 c4 c5 c6 c7 z : Z)
      (Hselector :
        Γ ⊢ ⟦ Selector.QMulFixedRunningSum ⟧ (region, row) <> 0)
      (Hgate :
        Γ ⊢ ⟦ Garden.Halo2.halo2_gadgets.ecc.chip.mul_fixed
            .running_sum_coordinates_check_gate ⟧ (region, row))
      (Hc0 :
        Γ ⊢ ⟦ Expression.Fixed Fixed.LagrangeCoeffs0 Rotation.cur ⟧
          (region, row) = UnOp.from c0)
      (Hc1 :
        Γ ⊢ ⟦ Expression.Fixed Fixed.LagrangeCoeffs1 Rotation.cur ⟧
          (region, row) = UnOp.from c1)
      (Hc2 :
        Γ ⊢ ⟦ Expression.Fixed Fixed.LagrangeCoeffs2 Rotation.cur ⟧
          (region, row) = UnOp.from c2)
      (Hc3 :
        Γ ⊢ ⟦ Expression.Fixed Fixed.LagrangeCoeffs3 Rotation.cur ⟧
          (region, row) = UnOp.from c3)
      (Hc4 :
        Γ ⊢ ⟦ Expression.Fixed Fixed.LagrangeCoeffs4 Rotation.cur ⟧
          (region, row) = UnOp.from c4)
      (Hc5 :
        Γ ⊢ ⟦ Expression.Fixed Fixed.LagrangeCoeffs5 Rotation.cur ⟧
          (region, row) = UnOp.from c5)
      (Hc6 :
        Γ ⊢ ⟦ Expression.Fixed Fixed.LagrangeCoeffs6 Rotation.cur ⟧
          (region, row) = UnOp.from c6)
      (Hc7 :
        Γ ⊢ ⟦ Expression.Fixed Fixed.LagrangeCoeffs7 Rotation.cur ⟧
          (region, row) = UnOp.from c7)
      (Hz :
        Γ ⊢ ⟦ Expression.Fixed Fixed.FixedZ Rotation.cur ⟧
          (region, row) = UnOp.from z) :
    Field.map_mod {|
      Point.x := Γ ⊢ ⟦ Expression.Advice Advice.A0 Rotation.cur ⟧ (region, row);
      Point.y := Γ ⊢ ⟦ Expression.Advice Advice.A1 Rotation.cur ⟧ (region, row);
    |} =
      EccSpec.fixed_window_point {|
        EccSpec.fw_coeffs := [c0; c1; c2; c3; c4; c5; c6; c7];
        EccSpec.fw_z := z;
      |}
        ((Γ ⊢ ⟦ Expression.Advice Advice.A4 Rotation.cur ⟧ (region, row)) -F
          (Γ ⊢ ⟦ Expression.Advice Advice.A4 Rotation.next ⟧ (region, row)) *F
          UnOp.from Garden.Halo2.halo2_gadgets.ecc.chip.constants.h)
        (Γ ⊢ ⟦ Expression.Advice Advice.A5 Rotation.cur ⟧ (region, row)).
  Proof.
    pose proof
      (RunningSumCoordinatesCheck.deterministic Γ region row
        Hselector Hgate) as Hdet.
    rewrite Hdet.
    unfold RunningSumCoordinatesCheck.output, CoordsCheck.output,
      EccSpec.fixed_window_point.
    cbn [Field.map_mod Point.IsMapMod EccSpec.fw_coeffs EccSpec.fw_z].
    rewrite Hc0, Hc1, Hc2, Hc3, Hc4, Hc5, Hc6, Hc7, Hz.
    rewrite <- EccSpec.fixed_interp_8_eq_interpolated_x_from.
    f_equal.
    - apply FieldRewrite.from_from.
    - unfold Garden.Halo2.halo2_gadgets.utilities_proof.square.
      rewrite FieldRewrite.sub_from_right.
      cbn [Point.y].
      apply FieldRewrite.from_sub.
  Qed.

  Lemma running_sum_fixed_window_correct_of_facts
      (Γ : Assignment.t columns RegionId.t)
      (facts : list (Fact.t columns RegionId.t))
      (region : RegionId.t) (row : Z)
      (c0 c1 c2 c3 c4 c5 c6 c7 z : Z)
      (Hfacts : interpret_facts Γ facts)
      (Hselector :
        List.In (Fact.SelectorOn Selector.QMulFixedRunningSum region row) facts)
      (Hc0 :
        List.In (Fact.FixedIs Fixed.LagrangeCoeffs0 region row c0) facts)
      (Hc1 :
        List.In (Fact.FixedIs Fixed.LagrangeCoeffs1 region row c1) facts)
      (Hc2 :
        List.In (Fact.FixedIs Fixed.LagrangeCoeffs2 region row c2) facts)
      (Hc3 :
        List.In (Fact.FixedIs Fixed.LagrangeCoeffs3 region row c3) facts)
      (Hc4 :
        List.In (Fact.FixedIs Fixed.LagrangeCoeffs4 region row c4) facts)
      (Hc5 :
        List.In (Fact.FixedIs Fixed.LagrangeCoeffs5 region row c5) facts)
      (Hc6 :
        List.In (Fact.FixedIs Fixed.LagrangeCoeffs6 region row c6) facts)
      (Hc7 :
        List.In (Fact.FixedIs Fixed.LagrangeCoeffs7 region row c7) facts)
      (Hz :
        List.In (Fact.FixedIs Fixed.FixedZ region row z) facts)
      (Hgates :
        satisfies_gates Γ
          (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)) :
    Field.map_mod {|
      Point.x := Γ ⊢ ⟦ Expression.Advice Advice.A0 Rotation.cur ⟧ (region, row);
      Point.y := Γ ⊢ ⟦ Expression.Advice Advice.A1 Rotation.cur ⟧ (region, row);
    |} =
      EccSpec.fixed_window_point {|
        EccSpec.fw_coeffs := [c0; c1; c2; c3; c4; c5; c6; c7];
        EccSpec.fw_z := z;
      |}
        ((Γ ⊢ ⟦ Expression.Advice Advice.A4 Rotation.cur ⟧ (region, row)) -F
          (Γ ⊢ ⟦ Expression.Advice Advice.A4 Rotation.next ⟧ (region, row)) *F
          UnOp.from Garden.Halo2.halo2_gadgets.ecc.chip.constants.h)
        (Γ ⊢ ⟦ Expression.Advice Advice.A5 Rotation.cur ⟧ (region, row)).
  Proof.
    apply (running_sum_fixed_window_correct Γ region row
      c0 c1 c2 c3 c4 c5 c6 c7 z).
    - exact (selector_nonzero_of_facts Γ facts
        Selector.QMulFixedRunningSum region row Hfacts Hselector).
    - apply (satisfies_gates_at Γ
        (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)
        Garden.Halo2.halo2_gadgets.ecc.chip.mul_fixed
          .running_sum_coordinates_check_gate
        region row); [| exact Hgates].
      cbn. repeat (first [left; reflexivity | right]).
    - exact (fixed_expression_eq_of_facts Γ facts
        Fixed.LagrangeCoeffs0 region row c0 Hfacts Hc0).
    - exact (fixed_expression_eq_of_facts Γ facts
        Fixed.LagrangeCoeffs1 region row c1 Hfacts Hc1).
    - exact (fixed_expression_eq_of_facts Γ facts
        Fixed.LagrangeCoeffs2 region row c2 Hfacts Hc2).
    - exact (fixed_expression_eq_of_facts Γ facts
        Fixed.LagrangeCoeffs3 region row c3 Hfacts Hc3).
    - exact (fixed_expression_eq_of_facts Γ facts
        Fixed.LagrangeCoeffs4 region row c4 Hfacts Hc4).
    - exact (fixed_expression_eq_of_facts Γ facts
        Fixed.LagrangeCoeffs5 region row c5 Hfacts Hc5).
    - exact (fixed_expression_eq_of_facts Γ facts
        Fixed.LagrangeCoeffs6 region row c6 Hfacts Hc6).
    - exact (fixed_expression_eq_of_facts Γ facts
        Fixed.LagrangeCoeffs7 region row c7 Hfacts Hc7).
    - exact (fixed_expression_eq_of_facts Γ facts
        Fixed.FixedZ region row z Hfacts Hz).
  Qed.

  (* Per-region window on-curve lift for the running-sum fixed-base muls: with
     the region facts peeled down to the [enable_mul_fixed_running_sum_rows]
     selector block, every window point of the incomplete-addition region is on
     the curve.  The running-sum analogue of
     [full_width_incomplete_region_window_on_curve]. *)
  Lemma running_sum_incomplete_window_on_curve
      (Γ : Assignment.t columns RegionId.t)
      (region : RegionId.t)
      (count i : nat)
      (Hfacts :
        interpret_facts Γ
          (region_facts region
            (Garden.Orchard.circuit.enable_mul_fixed_running_sum_rows
              0 count)))
      (Hgates :
        satisfies_gates Γ
          (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty))
      (Hi : (i < count)%nat) :
    point_on_curve
      (incomplete_additions_window_point Γ region (Z.of_nat i)).
  Proof.
    unfold point_on_curve, incomplete_additions_window_point.
    assert (Hsel :
      List.In
        (Fact.SelectorOn Selector.QMulFixedRunningSum region (Z.of_nat i))
        (region_facts region
          (Garden.Orchard.circuit.enable_mul_fixed_running_sum_rows
            0 count))).
    { replace (Z.of_nat i) with (0 + Z.of_nat i) by lia.
      apply running_sum_rows_selector_fact. exact Hi. }
    pose proof
      (running_sum_fixed_window_on_curve_of_facts Γ
        (region_facts region
          (Garden.Orchard.circuit.enable_mul_fixed_running_sum_rows
            0 count))
        region (Z.of_nat i) Hfacts Hsel Hgates) as Hcurve.
    cbn [Point.x Point.y].
    change (Γ ⊢ ⟦ Garden.Halo2.halo2_gadgets.ecc.chip.witness_point
        .curve_eqn Advice.A0 Advice.A1 ⟧ (region, Z.of_nat i) = 0).
    exact Hcurve.
  Qed.

  (* Per-region window on-curve lift for the short ([value_commit_v]) mul. *)
  Lemma short_incomplete_region_window_on_curve
      (Γ : Assignment.t columns RegionId.t)
      (region : RegionId.t)
      (magnitude : Garden.Halo2.Synthesis.Cell.t columns RegionId.t)
      (i : nat)
      (Hfacts :
        interpret_facts Γ
          (layouter_facts
            (Garden.Orchard.circuit
              .synth_short_mul_incomplete
              region magnitude)))
      (Hgates :
        satisfies_gates Γ
          (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty))
      (Hi : (i < 22)%nat) :
    point_on_curve
      (incomplete_additions_window_point Γ region (Z.of_nat i)).
  Proof.
    unfold Garden.Orchard.circuit
      .synth_short_mul_incomplete in Hfacts.
    apply interpret_layouter_facts_add_region in Hfacts.
    apply interpret_region_facts_bind_right in Hfacts.
    apply interpret_region_facts_bind_right in Hfacts.
    apply interpret_region_facts_bind_left in Hfacts.
    exact (running_sum_incomplete_window_on_curve Γ region 22 i
      Hfacts Hgates Hi).
  Qed.

  (* Per-region window on-curve lift for the base-field ([nullifier_k]) mul. *)
  Lemma base_field_incomplete_region_window_on_curve
      (Γ : Assignment.t columns RegionId.t)
      (region : RegionId.t)
      (scalar : Garden.Halo2.Synthesis.Cell.t columns RegionId.t)
      (i : nat)
      (Hfacts :
        interpret_facts Γ
          (layouter_facts
            (Garden.Orchard.circuit
              .synth_base_field_mul_incomplete
              region scalar)))
      (Hgates :
        satisfies_gates Γ
          (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty))
      (Hi : (i < 85)%nat) :
    point_on_curve
      (incomplete_additions_window_point Γ region (Z.of_nat i)).
  Proof.
    unfold Garden.Orchard.circuit
      .synth_base_field_mul_incomplete in Hfacts.
    apply interpret_layouter_facts_add_region in Hfacts.
    apply interpret_region_facts_bind_right in Hfacts.
    apply interpret_region_facts_bind_right in Hfacts.
    apply interpret_region_facts_bind_left in Hfacts.
    exact (running_sum_incomplete_window_on_curve Γ region 85 i
      Hfacts Hgates Hi).
  Qed.

  (* ---------------------------------------------------------------------- *)
  (* Running-sum scalar alignment for the short ([value_commit_v]) mul.      *)
  (*                                                                          *)
  (* The short fixed-base multiplication decomposes its scalar as a running   *)
  (* sum on [A4]: the initial [Copy] pins [z_0] to the magnitude cell, and    *)
  (* the [decompose_running_sum.range_check] gate (under                      *)
  (* [Selector.QMulFixedRunningSum]) bounds every word                        *)
  (* [z_i -F z_{i+1} *F 8] to [0, 8).  The word congruences                   *)
  (* [z_i ≡ w_i + 8·z_{i+1}] hold only modulo the field prime, so identifying *)
  (* [EccSpec.window_digit magnitude i] with the circuit word additionally    *)
  (* needs the final running-sum value to vanish ([z_22 = 0]): with it the    *)
  (* chain reconstructs over the integers ([8^22 < p]) and base-8 digit       *)
  (* extraction returns the words; without it a tail cell holding a multiple  *)
  (* of the modulus shifts every digit (e.g. magnitude [5] with               *)
  (* [z_1 = 4·8⁻¹ mod p] makes word 0 equal [1] while digit 0 of the          *)
  (* magnitude is [5]).  Upstream halo2 enforces the boundary by copying the  *)
  (* final running-sum entry to the fixed zero constant                       *)
  (* ([decompose_running_sum] in strict mode); the synthesized region in      *)
  (* [circuit.v] constrains rows 0..21 only and emits no such copy, so the    *)
  (* digit-facing lemmas below carry the boundary as an explicit hypothesis   *)
  (* (packaged for the concrete region as [value_commit_v_z_boundary]).      *)
  (* ---------------------------------------------------------------------- *)

  (* Word range from the [decompose_running_sum.range_check] gate: the
     running-sum word [z_cur -F z_next *F 8] lies in [0, 8).  The running-sum
     analogue of [full_width_fixed_window_range]. *)
  Lemma running_sum_word_range
      (Γ : Assignment.t columns RegionId.t)
      (region : RegionId.t) (row : Z)
      (Hselector :
        Γ ⊢ ⟦ Selector.QMulFixedRunningSum ⟧ (region, row) <> 0)
      (Hgate :
        Γ ⊢ ⟦ Garden.Halo2.halo2_gadgets.utilities.decompose_running_sum
            .range_check_gate
            Garden.Halo2.halo2_gadgets.ecc.chip.constants
              .fixed_base_window_size
            Selector.QMulFixedRunningSum
            Advice.A4 ⟧ (region, row)) :
    0 <=
      (Γ ⊢ ⟦ Expression.Advice Advice.A4 Rotation.cur ⟧ (region, row)) -F
        (Γ ⊢ ⟦ Expression.Advice Advice.A4 Rotation.next ⟧ (region, row)) *F
        UnOp.from Garden.Halo2.halo2_gadgets.ecc.chip.constants.h <
      8.
  Proof.
    cbn [eval_gate Gate.constraints Constraints.with_selector eval_constraints
      eval_named_constraint eval_constraint eval_selector eval_expression
      rotated_row Rotation.cur
      Garden.Halo2.halo2_gadgets.utilities.decompose_running_sum
        .range_check_gate
      List.map List.app] in Hgate.
    exact (Hgate Hselector).
  Qed.

  Lemma running_sum_word_range_of_facts
      (Γ : Assignment.t columns RegionId.t)
      (facts : list (Fact.t columns RegionId.t))
      (region : RegionId.t) (row : Z)
      (Hfacts : interpret_facts Γ facts)
      (Hselector :
        List.In (Fact.SelectorOn Selector.QMulFixedRunningSum region row)
          facts)
      (Hgates :
        satisfies_gates Γ
          (𝓒.run_unit Garden.Orchard.circuit.configure
            ConstraintSystem.empty)) :
    0 <=
      (Γ ⊢ ⟦ Expression.Advice Advice.A4 Rotation.cur ⟧ (region, row)) -F
        (Γ ⊢ ⟦ Expression.Advice Advice.A4 Rotation.next ⟧ (region, row)) *F
        UnOp.from Garden.Halo2.halo2_gadgets.ecc.chip.constants.h <
      8.
  Proof.
    apply (running_sum_word_range Γ region row).
    - exact (selector_nonzero_of_facts Γ facts
        Selector.QMulFixedRunningSum region row Hfacts Hselector).
    - apply (satisfies_gates_at Γ
        (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)
        (Garden.Halo2.halo2_gadgets.utilities.decompose_running_sum
          .range_check_gate
          Garden.Halo2.halo2_gadgets.ecc.chip.constants.fixed_base_window_size
          Selector.QMulFixedRunningSum
          Advice.A4)
        region row); [| exact Hgates].
      cbn. repeat (first [left; reflexivity | right]).
  Qed.

  Lemma short_incomplete_selector_fact
      (region : RegionId.t)
      (magnitude : Garden.Halo2.Synthesis.Cell.t columns RegionId.t)
      (i : nat) :
    (i < 22)%nat ->
    List.In
      (Fact.SelectorOn Selector.QMulFixedRunningSum region (Z.of_nat i))
      (layouter_facts
        (Garden.Orchard.circuit
          .synth_short_mul_incomplete
          region magnitude)).
  Proof.
    intros Hi.
    unfold Garden.Orchard.circuit
      .synth_short_mul_incomplete.
    cbn [layouter_facts region_facts].
    apply List.in_or_app.
    right.
    apply List.in_or_app.
    right.
    apply List.in_or_app.
    left.
    replace (Z.of_nat i) with (0 + Z.of_nat i) by lia.
    apply running_sum_rows_selector_fact.
    exact Hi.
  Qed.

  Lemma short_incomplete_fixed_fact
      (region : RegionId.t)
      (magnitude : Garden.Halo2.Synthesis.Cell.t columns RegionId.t)
      (i : nat) (row : Garden.Orchard.circuit.fixed_base_row)
      (column : Fixed.t) (annotation : string) (value : Z) :
    List.nth_error
      Garden.Orchard.constants.fixed_bases.value_commit_v.short_fixed_rows
      i =
      Some row ->
    List.In (column, annotation, value) row ->
    List.In
      (Fact.FixedIs column region (Z.of_nat i) value)
      (layouter_facts
        (Garden.Orchard.circuit
          .synth_short_mul_incomplete
          region magnitude)).
  Proof.
    intros Hrow Hin.
    unfold Garden.Orchard.circuit
      .synth_short_mul_incomplete.
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
      Garden.Orchard.constants.fixed_bases.value_commit_v.short_fixed_rows
      i row column annotation value Hrow Hin).
  Qed.

  (* The initial running-sum entry: the region's [Copy] constraint pins
     [A4[0]] to the magnitude cell. *)
  Lemma short_incomplete_region_initial_z
      (Γ : Assignment.t columns RegionId.t)
      (region : RegionId.t)
      (magnitude : Garden.Halo2.Synthesis.Cell.t columns RegionId.t)
      (Hfacts :
        interpret_facts Γ
          (layouter_facts
            (Garden.Orchard.circuit
              .synth_short_mul_incomplete
              region magnitude))) :
    read_advice Γ Advice.A4 region 0 = UnOp.from (eval_cell Γ magnitude).
  Proof.
    unfold Garden.Orchard.circuit
      .synth_short_mul_incomplete in Hfacts.
    apply interpret_layouter_facts_add_region in Hfacts.
    apply interpret_region_facts_bind_left in Hfacts.
    cbn [region_facts interpret_facts interpret_fact] in Hfacts.
    destruct Hfacts as [Hcopy _].
    unfold read_advice.
    rewrite eval_advice_cur_cell.
    rewrite Hcopy.
    reflexivity.
  Qed.

  (* Per-row word range over the short region: each of the 22 running-sum
     words lies in [0, 8). *)
  Lemma short_incomplete_region_word_range
      (Γ : Assignment.t columns RegionId.t)
      (region : RegionId.t)
      (magnitude : Garden.Halo2.Synthesis.Cell.t columns RegionId.t)
      (i : nat)
      (Hfacts :
        interpret_facts Γ
          (layouter_facts
            (Garden.Orchard.circuit
              .synth_short_mul_incomplete
              region magnitude)))
      (Hgates :
        satisfies_gates Γ
          (𝓒.run_unit Garden.Orchard.circuit.configure
            ConstraintSystem.empty))
      (Hi : (i < 22)%nat) :
    0 <=
      (Γ ⊢ ⟦ Expression.Advice Advice.A4 Rotation.cur ⟧
        (region, Z.of_nat i)) -F
        (Γ ⊢ ⟦ Expression.Advice Advice.A4 Rotation.next ⟧
          (region, Z.of_nat i)) *F
        UnOp.from Garden.Halo2.halo2_gadgets.ecc.chip.constants.h <
      8.
  Proof.
    apply (running_sum_word_range_of_facts Γ
      (layouter_facts
        (Garden.Orchard.circuit
          .synth_short_mul_incomplete
          region magnitude))
      region (Z.of_nat i) Hfacts).
    - apply short_incomplete_selector_fact.
      exact Hi.
    - exact Hgates.
  Qed.

  Lemma eval_advice_next_succ
      (Γ : Assignment.t columns RegionId.t)
      (column : Advice.t) (region : RegionId.t) (i : nat) :
    Γ ⊢ ⟦ Expression.Advice column Rotation.next ⟧ (region, Z.of_nat i) =
    Γ ⊢ ⟦ Expression.Advice column Rotation.cur ⟧ (region, Z.of_nat (S i)).
  Proof.
    change (eval_expression Γ (region, Z.of_nat i)
        (Expression.Advice column Rotation.next) =
      eval_expression Γ (region, Z.of_nat (S i))
        (Expression.Advice column Rotation.cur)).
    unfold eval_expression, rotated_row, Rotation.next, Rotation.cur.
    cbn [Rotation.offset].
    do 2 f_equal.
    lia.
  Qed.

  Lemma eval_advice_cur_bounds
      (Γ : Assignment.t columns RegionId.t)
      (column : Advice.t) (region : RegionId.t) (row : Z) :
    0 <= Γ ⊢ ⟦ Expression.Advice column Rotation.cur ⟧ (region, row) <
      Primes.pallas_p.
  Proof.
    change (0 <=
      eval_expression Γ (region, row) (Expression.Advice column Rotation.cur) <
      Primes.pallas_p).
    unfold eval_expression, UnOp.from.
    apply Z.mod_pos_bound.
    unfold Primes.pallas_p, Primes.t_p.
    lia.
  Qed.

  Lemma from_h_eq_8 :
    UnOp.from Garden.Halo2.halo2_gadgets.ecc.chip.constants.h = 8.
  Proof.
    unfold UnOp.from, Garden.Halo2.halo2_gadgets.ecc.chip.constants.h,
      Garden.Halo2.halo2_gadgets.ecc.chip.constants.fixed_base_window_size.
    apply Z.mod_small.
    unfold Primes.pallas_p, Primes.t_p.
    lia.
  Qed.

  (* One running-sum link over the integers: a word [w ≡ a - 8·b (mod P)]
     in [0, 8) with both sides of the congruence in [0, P) reconstructs
     [a = w + 8·b] exactly. *)
  Lemma running_sum_word_step
      (P a b w : Z)
      (HP : 8 < P)
      (Hw : w = (a - (b * 8) mod P) mod P)
      (Ha : 0 <= a < P)
      (Hb : 0 <= b)
      (Hsum : 0 <= w + 8 * b < P) :
    a = w + 8 * b.
  Proof.
    assert (Hcong : (w + 8 * b) mod P = a mod P).
    { rewrite Hw.
      rewrite Zplus_mod_idemp_l.
      replace (a - (b * 8) mod P + 8 * b) with
        (a + 8 * b - (b * 8) mod P) by ring.
      rewrite Zminus_mod_idemp_r.
      replace (a + 8 * b - b * 8) with a by ring.
      reflexivity. }
    rewrite (Z.mod_small (w + 8 * b) P Hsum) in Hcong.
    rewrite (Z.mod_small a P Ha) in Hcong.
    symmetry.
    exact Hcong.
  Qed.

  (* Integer reconstruction of a running-sum chain with a vanishing tail:
     reduced entries [zs] whose words lie in [0, 8) and whose final entry is
     [0] satisfy [zs j = Σ_m word_{j+m}·8^m] over the integers, provided the
     whole chain fits below the modulus ([8^count < p]). *)
  Lemma running_sum_zero_tail_reconstruct
      (zs : nat -> Z) (count : nat)
      (Hreduced :
        forall i : nat, (i <= count)%nat -> 0 <= zs i < Primes.pallas_p)
      (Hwords :
        forall i : nat,
          (i < count)%nat ->
          0 <=
            zs i -F
              zs (S i) *F
              UnOp.from Garden.Halo2.halo2_gadgets.ecc.chip.constants.h <
            8)
      (Hzero : zs count = 0)
      (Hfit : 8 ^ Z.of_nat count < Primes.pallas_p) :
    forall r j : nat,
      (j + r)%nat = count ->
      zs j =
        scalar_from_windows
          (List.map
            (fun m : nat =>
              zs m -F
                zs (S m) *F
                UnOp.from Garden.Halo2.halo2_gadgets.ecc.chip.constants.h)
            (List.seq j r)) /\
      0 <= zs j < 8 ^ Z.of_nat r.
  Proof.
    induction r as [| r IH]; intros j Hj.
    - assert (Hjc : j = count) by lia.
      subst j.
      rewrite Hzero.
      cbn [List.seq List.map].
      unfold scalar_from_windows.
      cbn [scalar_from_windows_aux].
      cbn.
      lia.
    - destruct (IH (S j) ltac:(lia)) as [IHeq IHbound].
      cbn [List.seq List.map].
      rewrite scalar_from_windows_cons.
      rewrite <- IHeq.
      pose proof (Hwords j ltac:(lia)) as Hwj.
      assert (Hpow_succ :
        8 ^ Z.of_nat (S r) = 8 * 8 ^ Z.of_nat r).
      { rewrite Nat2Z.inj_succ.
        rewrite Z.pow_succ_r; lia. }
      assert (Hpow_le : 8 ^ Z.of_nat (S r) <= 8 ^ Z.of_nat count).
      { apply Z.pow_le_mono_r; lia. }
      assert (Hstep :
        zs j =
          (zs j -F
            zs (S j) *F
            UnOp.from Garden.Halo2.halo2_gadgets.ecc.chip.constants.h) +
          8 * zs (S j)).
      { apply (running_sum_word_step Primes.pallas_p).
        - unfold Primes.pallas_p, Primes.t_p; lia.
        - rewrite from_h_eq_8.
          unfold BinOp.sub, BinOp.mul.
          reflexivity.
        - apply Hreduced; lia.
        - lia.
        - lia. }
      split.
      + exact Hstep.
      + lia.
  Qed.

  (* Per-window digit extraction from a zero-tailed running-sum chain: digit
     [i] of the head entry is the [i]-th word. *)
  Lemma running_sum_zero_tail_window_digit
      (zs : nat -> Z) (count : nat)
      (Hreduced :
        forall i : nat, (i <= count)%nat -> 0 <= zs i < Primes.pallas_p)
      (Hwords :
        forall i : nat,
          (i < count)%nat ->
          0 <=
            zs i -F
              zs (S i) *F
              UnOp.from Garden.Halo2.halo2_gadgets.ecc.chip.constants.h <
            8)
      (Hzero : zs count = 0)
      (Hfit : 8 ^ Z.of_nat count < Primes.pallas_p)
      (i : nat) (Hi : (i < count)%nat) :
    EccSpec.window_digit (zs 0%nat) i =
      zs i -F
        zs (S i) *F
        UnOp.from Garden.Halo2.halo2_gadgets.ecc.chip.constants.h.
  Proof.
    destruct
      (running_sum_zero_tail_reconstruct zs count Hreduced Hwords Hzero Hfit
        count 0%nat ltac:(lia)) as [Heq _].
    rewrite Heq.
    rewrite window_digit_scalar_from_windows_nth.
    - apply (nth_map_seq
        (fun m : nat =>
          zs m -F
            zs (S m) *F
            UnOp.from Garden.Halo2.halo2_gadgets.ecc.chip.constants.h)
        count i 0).
      exact Hi.
    - apply List.Forall_forall.
      intros w Hin.
      apply List.in_map_iff in Hin.
      destruct Hin as [m Hin].
      destruct Hin as [Hw Hin].
      apply List.in_seq in Hin.
      subst w.
      apply Hwords.
      lia.
    - rewrite List.length_map, List.length_seq.
      exact Hi.
  Qed.

  (* Per-window digit match over the short region: digit [i] of the initial
     running-sum entry [A4[0]] is the [i]-th circuit word, under the explicit
     final-boundary hypothesis [A4[22] = 0]. *)
  Lemma short_incomplete_region_window_digit
      (Γ : Assignment.t columns RegionId.t)
      (region : RegionId.t)
      (magnitude : Garden.Halo2.Synthesis.Cell.t columns RegionId.t)
      (i : nat)
      (Hfacts :
        interpret_facts Γ
          (layouter_facts
            (Garden.Orchard.circuit
              .synth_short_mul_incomplete
              region magnitude)))
      (Hgates :
        satisfies_gates Γ
          (𝓒.run_unit Garden.Orchard.circuit.configure
            ConstraintSystem.empty))
      (Hz_boundary :
        Γ ⊢ ⟦ Expression.Advice Advice.A4 Rotation.cur ⟧ (region, 22) = 0)
      (Hi : (i < 22)%nat) :
    EccSpec.window_digit (read_advice Γ Advice.A4 region 0) i =
      (Γ ⊢ ⟦ Expression.Advice Advice.A4 Rotation.cur ⟧
        (region, Z.of_nat i)) -F
        (Γ ⊢ ⟦ Expression.Advice Advice.A4 Rotation.next ⟧
          (region, Z.of_nat i)) *F
        UnOp.from Garden.Halo2.halo2_gadgets.ecc.chip.constants.h.
  Proof.
    rewrite (eval_advice_next_succ Γ Advice.A4 region i).
    apply (running_sum_zero_tail_window_digit
      (fun n : nat =>
        Γ ⊢ ⟦ Expression.Advice Advice.A4 Rotation.cur ⟧ (region, Z.of_nat n))
      22%nat).
    - intros m Hm.
      apply eval_advice_cur_bounds.
    - intros m Hm.
      pose proof
        (short_incomplete_region_word_range Γ region magnitude m
          Hfacts Hgates Hm) as Hword.
      rewrite (eval_advice_next_succ Γ Advice.A4 region m) in Hword.
      exact Hword.
    - exact Hz_boundary.
    - assert (Hpow : 8 ^ Z.of_nat 22 = 73786976294838206464) by reflexivity.
      rewrite Hpow.
      unfold Primes.pallas_p, Primes.t_p.
      lia.
    - exact Hi.
  Qed.

  Lemma short_incomplete_window_digit_magnitude
      (Γ : Assignment.t columns RegionId.t)
      (region : RegionId.t)
      (magnitude : Garden.Halo2.Synthesis.Cell.t columns RegionId.t)
      (i : nat)
      (Hfacts :
        interpret_facts Γ
          (layouter_facts
            (Garden.Orchard.circuit
              .synth_short_mul_incomplete
              region magnitude)))
      (Hgates :
        satisfies_gates Γ
          (𝓒.run_unit Garden.Orchard.circuit.configure
            ConstraintSystem.empty))
      (Hz_boundary :
        Γ ⊢ ⟦ Expression.Advice Advice.A4 Rotation.cur ⟧ (region, 22) = 0)
      (Hi : (i < 22)%nat) :
    EccSpec.window_digit (UnOp.from (eval_cell Γ magnitude)) i =
      (Γ ⊢ ⟦ Expression.Advice Advice.A4 Rotation.cur ⟧
        (region, Z.of_nat i)) -F
        (Γ ⊢ ⟦ Expression.Advice Advice.A4 Rotation.next ⟧
          (region, Z.of_nat i)) *F
        UnOp.from Garden.Halo2.halo2_gadgets.ecc.chip.constants.h.
  Proof.
    rewrite <- (short_incomplete_region_initial_z Γ region magnitude Hfacts).
    apply (short_incomplete_region_window_digit Γ region magnitude i
      Hfacts Hgates Hz_boundary Hi).
  Qed.

  (* Correctness of a short-region window row at the magnitude's own digit:
     the assigned point (A0, A1) equals the spec window point at
     [window_digit magnitude i].  The short analogue of
     [full_width_incomplete_window_correct]. *)
  Lemma short_incomplete_window_correct
      (Γ : Assignment.t columns RegionId.t)
      (region : RegionId.t)
      (magnitude : Garden.Halo2.Synthesis.Cell.t columns RegionId.t)
      (i : nat)
      (a0 a1 a2 a3 a4 a5 a6 a7 az : string)
      (c0 c1 c2 c3 c4 c5 c6 c7 z : Z)
      (Hrow :
        List.nth_error
          Garden.Orchard.constants.fixed_bases.value_commit_v.short_fixed_rows
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
      (Hfacts :
        interpret_facts Γ
          (layouter_facts
            (Garden.Orchard.circuit
              .synth_short_mul_incomplete
              region magnitude)))
      (Hgates :
        satisfies_gates Γ
          (𝓒.run_unit Garden.Orchard.circuit.configure
            ConstraintSystem.empty))
      (Hz_boundary :
        Γ ⊢ ⟦ Expression.Advice Advice.A4 Rotation.cur ⟧ (region, 22) = 0)
      (Hi : (i < 22)%nat) :
    Field.map_mod {|
      Point.x :=
        Γ ⊢ ⟦ Expression.Advice Advice.A0 Rotation.cur ⟧
          (region, Z.of_nat i);
      Point.y :=
        Γ ⊢ ⟦ Expression.Advice Advice.A1 Rotation.cur ⟧
          (region, Z.of_nat i);
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
        (EccSpec.window_digit (UnOp.from (eval_cell Γ magnitude)) i)
        (List.nth i (read_us Γ region 22) 0).
  Proof.
    rewrite (short_incomplete_window_digit_magnitude Γ region
      magnitude i Hfacts Hgates Hz_boundary Hi).
    rewrite (read_us_nth Γ region 22 i Hi).
    cbn [EccSpec.fixed_window_of_row EccSpec.fw_coeffs EccSpec.fw_z
      List.firstn List.map List.nth_error snd].
    apply (running_sum_fixed_window_correct_of_facts Γ
      (layouter_facts
        (Garden.Orchard.circuit
          .synth_short_mul_incomplete
          region magnitude))
      region (Z.of_nat i) c0 c1 c2 c3 c4 c5 c6 c7 z Hfacts).
    - apply short_incomplete_selector_fact.
      exact Hi.
    - apply (short_incomplete_fixed_fact region
        magnitude i _ Fixed.LagrangeCoeffs0 a0 c0 Hrow).
      cbn. left. reflexivity.
    - apply (short_incomplete_fixed_fact region
        magnitude i _ Fixed.LagrangeCoeffs1 a1 c1 Hrow).
      cbn. right. left. reflexivity.
    - apply (short_incomplete_fixed_fact region
        magnitude i _ Fixed.LagrangeCoeffs2 a2 c2 Hrow).
      cbn. do 2 right. left. reflexivity.
    - apply (short_incomplete_fixed_fact region
        magnitude i _ Fixed.LagrangeCoeffs3 a3 c3 Hrow).
      cbn. do 3 right. left. reflexivity.
    - apply (short_incomplete_fixed_fact region
        magnitude i _ Fixed.LagrangeCoeffs4 a4 c4 Hrow).
      cbn. do 4 right. left. reflexivity.
    - apply (short_incomplete_fixed_fact region
        magnitude i _ Fixed.LagrangeCoeffs5 a5 c5 Hrow).
      cbn. do 5 right. left. reflexivity.
    - apply (short_incomplete_fixed_fact region
        magnitude i _ Fixed.LagrangeCoeffs6 a6 c6 Hrow).
      cbn. do 6 right. left. reflexivity.
    - apply (short_incomplete_fixed_fact region
        magnitude i _ Fixed.LagrangeCoeffs7 a7 c7 Hrow).
      cbn. do 7 right. left. reflexivity.
    - apply (short_incomplete_fixed_fact region
        magnitude i _ Fixed.FixedZ az z Hrow).
      cbn. do 8 right. left. reflexivity.
    - exact Hgates.
  Qed.

  (* Facts of the value_commit_v incomplete region, peeled from [Holds]: the
     region is [ValueCommitVIncomplete] and the magnitude cell is the [A9]
     free-witness cell of [MagnitudeRangeCheck] ([in_magnitude]'s source). *)
  Lemma value_commit_v_incomplete_facts
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    interpret_facts Γ
      (layouter_facts
        (Garden.Orchard.circuit
          .synth_short_mul_incomplete
          (Garden.Orchard.circuit.value_commitment_region
            RegionId.ValueCommitment.ValueCommitVIncomplete)
          (Garden.Halo2.Synthesis.Cell.advice
            (Garden.Orchard.circuit.value_commitment_region
              RegionId.ValueCommitment.MagnitudeRangeCheck)
            Advice.A9 0))).
  Proof.
    pose proof (value_commitment_facts Γ Hcircuit) as Hfacts.
    unfold Garden.Orchard.circuit.synthesize_value_commitment in Hfacts.
    do 4 apply interpret_layouter_facts_bind_right in Hfacts.
    apply interpret_layouter_facts_bind_left in Hfacts.
    unfold Garden.Orchard.circuit.synthesize_value_commit_orchard in Hfacts.
    apply interpret_layouter_facts_in_namespace in Hfacts.
    apply interpret_layouter_facts_bind_left in Hfacts.
    do 2 apply interpret_layouter_facts_in_namespace in Hfacts.
    unfold Garden.Orchard.circuit.synthesize_short_fixed_base_mul in Hfacts.
    apply interpret_layouter_facts_bind_left in Hfacts.
    exact Hfacts.
  Qed.

  (* The final boundary of the value_commit_v running sum: [A4[22]] of the
     incomplete region vanishes.  Upstream halo2 enforces this with a copy of
     the final running-sum entry to the fixed zero constant
     ([decompose_running_sum] in strict mode); the synthesized region in
     [circuit.v] emits the corresponding [𝓡.ConstrainConstant], so the Prop
     is discharged from [Holds] by [value_commit_v_z_boundary_of_holds]. *)
  Definition value_commit_v_z_boundary
      (Γ : Assignment.t columns RegionId.t) : Prop :=
    Γ ⊢ ⟦ Expression.Advice Advice.A4 Rotation.cur ⟧
      (RegionId.ValueCommitment
        RegionId.ValueCommitment.ValueCommitVIncomplete, 22) = 0.

  Lemma value_commit_v_z_boundary_of_holds
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    value_commit_v_z_boundary Γ.
  Proof.
    pose proof (value_commit_v_incomplete_facts Γ Hcircuit) as Hfacts.
    unfold Garden.Orchard.circuit
      .synth_short_mul_incomplete in Hfacts.
    apply interpret_layouter_facts_add_region in Hfacts.
    apply interpret_region_facts_bind_right in Hfacts.
    apply interpret_region_facts_bind_left in Hfacts.
    cbn [region_facts interpret_facts interpret_fact] in Hfacts.
    destruct Hfacts as [Hpin _].
    unfold Garden.Orchard.circuit.value_commitment_region in Hpin.
    unfold value_commit_v_z_boundary.
    rewrite eval_advice_cur_cell.
    rewrite Hpin.
    reflexivity.
  Qed.

  (* The base-field ([nullifier_k]) analogue: [A4[85]] of the incomplete
     region vanishes, from the strict-tail [𝓡.ConstrainConstant] of the
     base-field running sum.  Consumed by the base-field canonicity digit
     match ([circuit_proof/base_field_canonicity.v]). *)
  Definition nullifier_k_z_boundary
      (Γ : Assignment.t columns RegionId.t) : Prop :=
    Γ ⊢ ⟦ Expression.Advice Advice.A4 Rotation.cur ⟧
      (RegionId.Nullifier RegionId.Nullifier.BaseFieldIncomplete, 85) = 0.

  Lemma nullifier_k_z_boundary_of_holds
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    nullifier_k_z_boundary Γ.
  Proof.
    pose proof (nullifier_facts Γ Hcircuit) as Hfacts.
    destruct (layouter_value Garden.Orchard.circuit.synthesize_witness_inputs)
      as [ [ [ [ [ [ [psi_old rho_old] cm_old] g_d_old] ak_P] nk] v_old]
        v_new].
    unfold Garden.Orchard.circuit.synthesize_nullifier in Hfacts.
    apply interpret_layouter_facts_bind_left in Hfacts.
    apply interpret_layouter_facts_in_namespace in Hfacts.
    do 2 apply interpret_layouter_facts_bind_right in Hfacts.
    apply interpret_layouter_facts_bind_left in Hfacts.
    apply interpret_layouter_facts_in_namespace in Hfacts.
    unfold Garden.Orchard.circuit
      .synth_nullifier_k_mul in Hfacts.
    apply interpret_layouter_facts_in_namespace in Hfacts.
    apply interpret_layouter_facts_bind_left in Hfacts.
    unfold Garden.Orchard.circuit
      .synth_base_field_mul_incomplete in Hfacts.
    apply interpret_layouter_facts_add_region in Hfacts.
    apply interpret_region_facts_bind_right in Hfacts.
    apply interpret_region_facts_bind_left in Hfacts.
    cbn [region_facts interpret_facts interpret_fact] in Hfacts.
    destruct Hfacts as [Hpin _].
    unfold Garden.Orchard.circuit.nullifier_region in Hpin.
    unfold nullifier_k_z_boundary.
    rewrite eval_advice_cur_cell.
    rewrite Hpin.
    reflexivity.
  Qed.

  (* [A4[0]] of the value_commit_v incomplete region is [in_magnitude]
     ([read9] of the magnitude range-check region). *)
  Lemma value_commit_v_initial_z
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    read_advice Γ Advice.A4
      (RegionId.ValueCommitment
        RegionId.ValueCommitment.ValueCommitVIncomplete) 0 =
    read9 Γ
      (RegionId.ValueCommitment
        RegionId.ValueCommitment.MagnitudeRangeCheck).
  Proof.
    rewrite (short_incomplete_region_initial_z Γ
      (RegionId.ValueCommitment
        RegionId.ValueCommitment.ValueCommitVIncomplete)
      (Garden.Halo2.Synthesis.Cell.advice
        (Garden.Orchard.circuit.value_commitment_region
          RegionId.ValueCommitment.MagnitudeRangeCheck)
        Advice.A9 0)
      (value_commit_v_incomplete_facts Γ Hcircuit)).
    unfold read9, read_advice.
    rewrite eval_advice_cur_cell.
    reflexivity.
  Qed.

  Lemma value_commit_v_table_length :
    List.length (OrchardCircuitSpec.value_commit_v orchard_internal_params) = 22%nat.
  Proof. reflexivity. Qed.

  (* Per-window digit match at the spec scalar: digit [i] of [in_magnitude]
     is the [i]-th circuit word of the value_commit_v running sum. *)
  Lemma value_commit_v_window_digit
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (i : nat) (Hi : (i < 22)%nat) :
    EccSpec.window_digit
      (read9 Γ
        (RegionId.ValueCommitment
          RegionId.ValueCommitment.MagnitudeRangeCheck)) i =
      (Γ ⊢ ⟦ Expression.Advice Advice.A4 Rotation.cur ⟧
        (RegionId.ValueCommitment
          RegionId.ValueCommitment.ValueCommitVIncomplete, Z.of_nat i)) -F
        (Γ ⊢ ⟦ Expression.Advice Advice.A4 Rotation.next ⟧
          (RegionId.ValueCommitment
            RegionId.ValueCommitment.ValueCommitVIncomplete, Z.of_nat i)) *F
        UnOp.from Garden.Halo2.halo2_gadgets.ecc.chip.constants.h.
  Proof.
    rewrite <- (value_commit_v_initial_z Γ Hcircuit).
    apply (short_incomplete_region_window_digit Γ
      (RegionId.ValueCommitment
        RegionId.ValueCommitment.ValueCommitVIncomplete)
      (Garden.Halo2.Synthesis.Cell.advice
        (Garden.Orchard.circuit.value_commitment_region
          RegionId.ValueCommitment.MagnitudeRangeCheck)
        Advice.A9 0)
      i
      (value_commit_v_incomplete_facts Γ Hcircuit)
      (holds_gates Γ Hcircuit)
      (value_commit_v_z_boundary_of_holds Γ Hcircuit)
      Hi).
  Qed.

  (* Per-window correctness against the value_commit_v spec table at the spec
     digit: window [j] of the incomplete region equals the spec window point
     at [window_digit in_magnitude j].  The short analogue of
     [spend_auth_g_window_correct]. *)
  Lemma value_commit_v_window_correct
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (j : nat) (w : EccSpec.fixed_window)
      (Hnth :
        List.nth_error
          (OrchardCircuitSpec.value_commit_v orchard_internal_params) j = Some w) :
    incomplete_additions_window_point Γ
      (RegionId.ValueCommitment
        RegionId.ValueCommitment.ValueCommitVIncomplete)
      (Z.of_nat j) =
    EccSpec.fixed_window_point w
      (EccSpec.window_digit
        (read9 Γ
          (RegionId.ValueCommitment
            RegionId.ValueCommitment.MagnitudeRangeCheck))
        j)
      (List.nth j
        (read_us Γ
          (RegionId.ValueCommitment
            RegionId.ValueCommitment.ValueCommitVIncomplete) 22)
        0).
  Proof.
    pose proof (value_commit_v_incomplete_facts Γ Hcircuit) as Hfacts.
    assert (Hmag :
      read9 Γ
        (RegionId.ValueCommitment
          RegionId.ValueCommitment.MagnitudeRangeCheck) =
      UnOp.from
        (eval_cell Γ
          (Garden.Halo2.Synthesis.Cell.advice
            (Garden.Orchard.circuit.value_commitment_region
              RegionId.ValueCommitment.MagnitudeRangeCheck)
            Advice.A9 0))).
    { unfold read9, read_advice.
      rewrite eval_advice_cur_cell.
      reflexivity. }
    rewrite Hmag.
    unfold OrchardCircuitSpec.value_commit_v, orchard_internal_params in Hnth.
    cbn in Hnth.
    do 22
      (destruct j as [| j];
        [ cbn in Hnth;
          inversion Hnth; subst; clear Hnth;
          rewrite <- incomplete_additions_window_point_map_mod;
          unfold incomplete_additions_window_point;
          eapply
            (short_incomplete_window_correct Γ
              (RegionId.ValueCommitment
                RegionId.ValueCommitment.ValueCommitVIncomplete)
              (Garden.Halo2.Synthesis.Cell.advice
                (Garden.Orchard.circuit.value_commitment_region
                  RegionId.ValueCommitment.MagnitudeRangeCheck)
                Advice.A9 0));
          [ reflexivity
          | exact Hfacts
          | exact (holds_gates Γ Hcircuit)
          | exact (value_commit_v_z_boundary_of_holds Γ Hcircuit)
          | lia ]
        | cbn in Hnth ]).
    destruct j; discriminate Hnth.
  Qed.

  (* On-curve fact at the spec digit, in the [Hfacts] shape consumed by
     [table_us_free_of_oncurve]: the spec window point of table entry [i] at
     [window_digit in_magnitude i] with the witnessed [u] satisfies the
     Pallas curve equation. *)
  Lemma value_commit_v_spec_window_on_curve
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (i : nat) (Hi : (i < 22)%nat) :
    point_on_curve
      (EccSpec.fixed_window_point
        (List.nth i
          (OrchardCircuitSpec.value_commit_v orchard_internal_params)
          fixed_window_default)
        (EccSpec.window_digit
          (read9 Γ
            (RegionId.ValueCommitment
              RegionId.ValueCommitment.MagnitudeRangeCheck))
          i)
        (List.nth i
          (read_us Γ
            (RegionId.ValueCommitment
              RegionId.ValueCommitment.ValueCommitVIncomplete) 22)
          0)).
  Proof.
    pose proof
      (short_incomplete_region_window_on_curve Γ
        (RegionId.ValueCommitment
          RegionId.ValueCommitment.ValueCommitVIncomplete)
        (Garden.Halo2.Synthesis.Cell.advice
          (Garden.Orchard.circuit.value_commitment_region
            RegionId.ValueCommitment.MagnitudeRangeCheck)
          Advice.A9 0)
        i
        (value_commit_v_incomplete_facts Γ Hcircuit)
        (holds_gates Γ Hcircuit)
        Hi) as Honc.
    assert (Hnth :
      List.nth_error (OrchardCircuitSpec.value_commit_v orchard_internal_params) i =
      Some
        (List.nth i
          (OrchardCircuitSpec.value_commit_v orchard_internal_params)
          fixed_window_default)).
    { apply List.nth_error_nth'.
      rewrite value_commit_v_table_length.
      exact Hi. }
    rewrite (value_commit_v_window_correct Γ Hcircuit i
      (List.nth i
        (OrchardCircuitSpec.value_commit_v orchard_internal_params)
        fixed_window_default)
      Hnth) in Honc.
    exact Honc.
  Qed.

End OrchardActionFixedBase.
