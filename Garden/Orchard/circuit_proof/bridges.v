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
Require Import Garden.Halo2.PallasModel.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.mul_fixed_proof.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.mul_fixed.full_width_proof.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.witness_point_proof.
Require Import Garden.Halo2.halo2_gadgets.poseidon.spec.
Require Import Garden.Orchard.circuit_spec.
Require Import Garden.Orchard.circuit_proof.fixed_base.main.
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


Module OrchardActionBridges.
  Include OrchardActionFixedBase.

  Local Notation Holds Γ :=
    (circuit_holds Γ
      Garden.Orchard.circuit.synthesize
      (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)).

  Lemma complete_point_add_instance_x_correct
      (Γ : Assignment.t columns RegionId.t)
      (region : RegionId.t) (name : string)
      (p q : Garden.Orchard.circuit.AssignedPoint.t)
      (instance : Instance_.t) (row : Z)
      (Hfacts :
        interpret_facts Γ
          (layouter_facts
            (Garden.Orchard.circuit.synthesize_complete_point_add
              region name p q)))
      (Hgates :
        satisfies_gates Γ
          (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty))
      (Hinstance :
        eval_cell Γ
          (layouter_value
            (Garden.Orchard.circuit.synthesize_complete_point_add
              region name p q)).(Garden.Orchard.circuit.AssignedPoint.x) =
        Γ.(Assignment.instance_) instance row) :
    UnOp.from (Γ.(Assignment.instance_) instance row) =
      Point.x
        (EccSpec.point_add
          (Field.map_mod (assigned_point_value Γ p))
          (Field.map_mod (assigned_point_value Γ q))).
  Proof.
    pose proof
      (f_equal Point.x
        (complete_point_add_correct Γ region name p q Hfacts Hgates)) as Hx.
    change (UnOp.from
      (eval_cell Γ
        (layouter_value
          (Garden.Orchard.circuit.synthesize_complete_point_add region name p q))
        .(Garden.Orchard.circuit.AssignedPoint.x)) =
      Point.x
        (EccSpec.point_add
          (Field.map_mod (assigned_point_value Γ p))
          (Field.map_mod (assigned_point_value Γ q)))) in Hx.
    rewrite Hinstance in Hx.
    exact Hx.
  Qed.

  Lemma complete_point_add_instance_y_correct
      (Γ : Assignment.t columns RegionId.t)
      (region : RegionId.t) (name : string)
      (p q : Garden.Orchard.circuit.AssignedPoint.t)
      (instance : Instance_.t) (row : Z)
      (Hfacts :
        interpret_facts Γ
          (layouter_facts
            (Garden.Orchard.circuit.synthesize_complete_point_add
              region name p q)))
      (Hgates :
        satisfies_gates Γ
          (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty))
      (Hinstance :
        eval_cell Γ
          (layouter_value
            (Garden.Orchard.circuit.synthesize_complete_point_add
              region name p q)).(Garden.Orchard.circuit.AssignedPoint.y) =
        Γ.(Assignment.instance_) instance row) :
    UnOp.from (Γ.(Assignment.instance_) instance row) =
      Point.y
        (EccSpec.point_add
          (Field.map_mod (assigned_point_value Γ p))
          (Field.map_mod (assigned_point_value Γ q))).
  Proof.
    pose proof
      (f_equal Point.y
        (complete_point_add_correct Γ region name p q Hfacts Hgates)) as Hy.
    change (UnOp.from
      (eval_cell Γ
        (layouter_value
          (Garden.Orchard.circuit.synthesize_complete_point_add region name p q))
        .(Garden.Orchard.circuit.AssignedPoint.y)) =
      Point.y
        (EccSpec.point_add
          (Field.map_mod (assigned_point_value Γ p))
          (Field.map_mod (assigned_point_value Γ q)))) in Hy.
    rewrite Hinstance in Hy.
    exact Hy.
  Qed.

  Lemma orchard_gate_active_root_eq_anchor_target
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (Hvold :
        read Γ (RegionId.WitnessInput RegionId.WitnessInput.VOld) <> 0) :
    Γ ⊢ ⟦ Expression.Advice Advice.A4 Rotation.cur ⟧
      (RegionId.OrchardCircuitChecks, 0) =
    Γ ⊢ ⟦ Expression.Advice Advice.A5 Rotation.cur ⟧
      (RegionId.OrchardCircuitChecks, 0).
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
    destruct Hgate as [_ Hgate].
    destruct Hgate as [Hroot_or_anchor _].
    specialize (Hroot_or_anchor Hselector).
    destruct Hroot_or_anchor as [Hvold_zero | Hroot_anchor].
    - exfalso. apply Hvold.
      unfold read, read_advice.
      change (UnOp.from
        (Γ.(Assignment.advice) Advice.A0
          (RegionId.WitnessInput RegionId.WitnessInput.VOld) 0) = 0).
      unfold Garden.Orchard.circuit.witness_input_region in Hcopy_vold.
      rewrite <- Hcopy_vold.
      exact Hvold_zero.
    - exact Hroot_anchor.
  Qed.

  Lemma anchor_instance_eq_root_target_when_active
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (Hvold :
        read Γ (RegionId.WitnessInput RegionId.WitnessInput.VOld) <> 0) :
    read_public_instance Γ Garden.Orchard.circuit.ANCHOR =
      UnOp.from
        (eval_cell Γ
          (Garden.Halo2.Synthesis.Cell.advice
            RegionId.OrchardCircuitChecks Advice.A4 0)).
  Proof.
    destruct Hcircuit as [Hfacts HSatisfies].
    pose proof Hfacts as Horchard_facts.
    unfold Garden.Orchard.circuit.synthesize in Horchard_facts.
    do 10 apply interpret_layouter_facts_bind_right in Horchard_facts.
    apply interpret_layouter_facts_bind_left in Horchard_facts.
    unfold Garden.Orchard.circuit.synthesize_orchard_gate in Horchard_facts.
    apply interpret_layouter_facts_add_region in Horchard_facts.
    do 5 apply interpret_region_facts_bind_right in Horchard_facts.
    apply interpret_region_facts_bind_left in Horchard_facts.
    cbn [region_facts interpret_facts interpret_fact eval_cell] in Horchard_facts.
    destruct Horchard_facts as [Hcopy_anchor _].
    pose proof
      (orchard_gate_active_root_eq_anchor_target
        Γ (conj Hfacts HSatisfies) Hvold) as Hroot_anchor.
    unfold read_public_instance in *.
    cbn [eval_expression eval_cell rotated_row Rotation.cur] in *.
    cbn in Hcopy_anchor.
    change (UnOp.from
      (Γ.(Assignment.instance_) Instance_.Primary Garden.Orchard.circuit.ANCHOR) =
      UnOp.from
        (Γ.(Assignment.advice) Advice.A4 RegionId.OrchardCircuitChecks 0)).
    rewrite <- Hcopy_anchor.
    symmetry.
    exact Hroot_anchor.
  Qed.

  Lemma orchard_gate_root_target_eq_merkle_root
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    UnOp.from
      (eval_cell Γ
        (Garden.Halo2.Synthesis.Cell.advice
          RegionId.OrchardCircuitChecks Advice.A4 0)) =
    UnOp.from
      (eval_cell Γ
        (layouter_value
          (Garden.Orchard.circuit.synthesize_merkle_path
            (layouter_value
              (Garden.Orchard.circuit.witness_point
                (Garden.Orchard.circuit.witness_input_region
                  RegionId.WitnessInput.CmOld)
                "cm_old"))
              .(Garden.Orchard.circuit.AssignedPoint.x)))).
  Proof.
    destruct Hcircuit as [Hfacts HSatisfies].
    pose proof Hfacts as Horchard_facts.
    unfold Garden.Orchard.circuit.synthesize in Horchard_facts.
    do 10 apply interpret_layouter_facts_bind_right in Horchard_facts.
    apply interpret_layouter_facts_bind_left in Horchard_facts.
    unfold Garden.Orchard.circuit.synthesize_orchard_gate in Horchard_facts.
    apply interpret_layouter_facts_add_region in Horchard_facts.
    do 4 apply interpret_region_facts_bind_right in Horchard_facts.
    apply interpret_region_facts_bind_left in Horchard_facts.
    cbn [region_facts interpret_facts interpret_fact eval_cell] in Horchard_facts.
    destruct Horchard_facts as [Hcopy_root _].
    rewrite Hcopy_root.
    reflexivity.
  Qed.

  Lemma anchor_instance_eq_merkle_root_when_active
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (Hvold :
        read Γ (RegionId.WitnessInput RegionId.WitnessInput.VOld) <> 0) :
    read_public_instance Γ Garden.Orchard.circuit.ANCHOR =
    UnOp.from
      (eval_cell Γ
        (layouter_value
          (Garden.Orchard.circuit.synthesize_merkle_path
            (layouter_value
              (Garden.Orchard.circuit.witness_point
                (Garden.Orchard.circuit.witness_input_region
                  RegionId.WitnessInput.CmOld)
                "cm_old"))
              .(Garden.Orchard.circuit.AssignedPoint.x)))).
  Proof.
    rewrite (anchor_instance_eq_root_target_when_active Γ Hcircuit Hvold).
    exact (orchard_gate_root_target_eq_merkle_root Γ Hcircuit).
  Qed.

  Lemma anchor_correct_of_merkle_root
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (Hmerkle :
        UnOp.from
          (eval_cell Γ
            (layouter_value
              (Garden.Orchard.circuit.synthesize_merkle_path
                (layouter_value
                  (Garden.Orchard.circuit.witness_point
                    (Garden.Orchard.circuit.witness_input_region
                      RegionId.WitnessInput.CmOld)
                    "cm_old"))
                  .(Garden.Orchard.circuit.AssignedPoint.x)))) =
        OrchardSpec.anchor orchard_circuit_params
          (read Γ (RegionId.WitnessInput RegionId.WitnessInput.CmOld))
          (merkle_path_of Γ)) :
    read_public_instance Γ Garden.Orchard.circuit.ANCHOR =
      OrchardSpec.out_anchor (action_spec_of Γ).
  Proof.
    destruct (read Γ
      (RegionId.WitnessInput RegionId.WitnessInput.VOld) =? 0) eqn:Hvold_eqb.
    - apply Z.eqb_eq in Hvold_eqb.
      unfold action_spec_of, output_with_witness, read_action_inputs,
        read_action_inputs_with_anchor.
      cbn [OrchardSpec.out_anchor OrchardSpec.orchard_action_spec
        OrchardSpec.in_v_old OrchardSpec.in_anchor_public].
      rewrite Hvold_eqb, Z.eqb_refl.
      reflexivity.
    - assert (Hvold_ne :
        read Γ (RegionId.WitnessInput RegionId.WitnessInput.VOld) <> 0).
      { apply Z.eqb_neq. exact Hvold_eqb. }
      unfold action_spec_of, output_with_witness, read_action_inputs,
        read_action_inputs_with_anchor.
      cbn [OrchardSpec.out_anchor OrchardSpec.orchard_action_spec
        OrchardSpec.in_v_old OrchardSpec.in_leaf OrchardSpec.in_path
        OrchardSpec.anchor OrchardSpec.merkle_crh_q].
      rewrite Hvold_eqb.
      rewrite (anchor_instance_eq_merkle_root_when_active
        Γ Hcircuit Hvold_ne).
      exact Hmerkle.
  Qed.

  Lemma cv_net_x_complete_add_bridge
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    let magnitude :=
      layouter_value
        (Garden.Orchard.circuit.assign_free_advice
          (Garden.Orchard.circuit.value_commitment_region
            RegionId.ValueCommitment.MagnitudeRangeCheck)
          "v_net magnitude" Advice.A9 0) in
    let sign :=
      layouter_value
        (Garden.Orchard.circuit.assign_free_advice
          (Garden.Orchard.circuit.value_commitment_region
            RegionId.ValueCommitment.SignRangeCheck)
          "v_net sign" Advice.A9 0) in
    let value_commit_v :=
      layouter_value
        (Garden.Orchard.circuit.synthesize_short_fixed_base_mul magnitude sign) in
    let blind :=
      layouter_value
        Garden.Orchard.circuit.synth_value_commit_r_mul in
    read_public_instance Γ Garden.Orchard.circuit.CV_NET_X =
      Point.x
        (EccSpec.point_add
          (Field.map_mod (assigned_point_value Γ value_commit_v))
          (Field.map_mod (assigned_point_value Γ blind))).
  Proof.
    destruct Hcircuit as [Hfacts HSatisfies].
    destruct HSatisfies as [Hgates Hlookups].
    set (magnitude :=
      layouter_value
        (Garden.Orchard.circuit.assign_free_advice
          (Garden.Orchard.circuit.value_commitment_region
            RegionId.ValueCommitment.MagnitudeRangeCheck)
          "v_net magnitude" Advice.A9 0)).
    set (sign :=
      layouter_value
        (Garden.Orchard.circuit.assign_free_advice
          (Garden.Orchard.circuit.value_commitment_region
            RegionId.ValueCommitment.SignRangeCheck)
          "v_net sign" Advice.A9 0)).
    set (value_commit_v :=
      layouter_value
        (Garden.Orchard.circuit.synthesize_short_fixed_base_mul magnitude sign)).
    set (blind :=
      layouter_value
        Garden.Orchard.circuit.synth_value_commit_r_mul).
    pose (cv_add :=
      Garden.Orchard.circuit.synthesize_complete_point_add
        (Garden.Orchard.circuit.value_commitment_region
          RegionId.ValueCommitment.CompletePointAdd)
        "cv" value_commit_v blind).
    assert (Hcomplete_facts :
        interpret_facts Γ (layouter_facts cv_add)).
    { subst cv_add blind value_commit_v sign magnitude.
      pose proof Hfacts as Hcv_facts.
      unfold Garden.Orchard.circuit.synthesize in Hcv_facts.
      do 3 apply interpret_layouter_facts_bind_right in Hcv_facts.
      apply interpret_layouter_facts_bind_left in Hcv_facts.
      unfold Garden.Orchard.circuit.synthesize_value_commitment in Hcv_facts.
      do 4 apply interpret_layouter_facts_bind_right in Hcv_facts.
      apply interpret_layouter_facts_bind_left in Hcv_facts.
      unfold Garden.Orchard.circuit.synthesize_value_commit_orchard in Hcv_facts.
      apply interpret_layouter_facts_in_namespace in Hcv_facts.
      do 2 apply interpret_layouter_facts_bind_right in Hcv_facts.
      exact Hcv_facts. }
    assert (Hinstance :
        eval_cell Γ
          (layouter_value cv_add).(Garden.Orchard.circuit.AssignedPoint.x) =
        Γ.(Assignment.instance_) Instance_.Primary Garden.Orchard.circuit.CV_NET_X).
    { subst cv_add blind value_commit_v sign magnitude.
      pose proof Hfacts as Hinstance_facts.
      unfold Garden.Orchard.circuit.synthesize in Hinstance_facts.
      do 3 apply interpret_layouter_facts_bind_right in Hinstance_facts.
      apply interpret_layouter_facts_bind_left in Hinstance_facts.
      unfold Garden.Orchard.circuit.synthesize_value_commitment in Hinstance_facts.
      do 5 apply interpret_layouter_facts_bind_right in Hinstance_facts.
      apply interpret_layouter_facts_bind_left in Hinstance_facts.
      cbn [layouter_facts interpret_facts interpret_fact eval_cell] in Hinstance_facts.
      destruct Hinstance_facts as [Hinstance _].
      exact Hinstance. }
    apply (read_public_instance_eq_of_cell Γ
      (layouter_value cv_add).(Garden.Orchard.circuit.AssignedPoint.x)
      Garden.Orchard.circuit.CV_NET_X).
    - exact Hinstance.
    - rewrite Hinstance.
      subst cv_add.
      exact (complete_point_add_instance_x_correct Γ
        (Garden.Orchard.circuit.value_commitment_region
          RegionId.ValueCommitment.CompletePointAdd)
        "cv" value_commit_v blind Instance_.Primary Garden.Orchard.circuit.CV_NET_X
        Hcomplete_facts Hgates Hinstance).
  Qed.

  Lemma cv_net_y_complete_add_bridge
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    let magnitude :=
      layouter_value
        (Garden.Orchard.circuit.assign_free_advice
          (Garden.Orchard.circuit.value_commitment_region
            RegionId.ValueCommitment.MagnitudeRangeCheck)
          "v_net magnitude" Advice.A9 0) in
    let sign :=
      layouter_value
        (Garden.Orchard.circuit.assign_free_advice
          (Garden.Orchard.circuit.value_commitment_region
            RegionId.ValueCommitment.SignRangeCheck)
          "v_net sign" Advice.A9 0) in
    let value_commit_v :=
      layouter_value
        (Garden.Orchard.circuit.synthesize_short_fixed_base_mul magnitude sign) in
    let blind :=
      layouter_value
        Garden.Orchard.circuit.synth_value_commit_r_mul in
    read_public_instance Γ Garden.Orchard.circuit.CV_NET_Y =
      Point.y
        (EccSpec.point_add
          (Field.map_mod (assigned_point_value Γ value_commit_v))
          (Field.map_mod (assigned_point_value Γ blind))).
  Proof.
    destruct Hcircuit as [Hfacts HSatisfies].
    destruct HSatisfies as [Hgates Hlookups].
    set (magnitude :=
      layouter_value
        (Garden.Orchard.circuit.assign_free_advice
          (Garden.Orchard.circuit.value_commitment_region
            RegionId.ValueCommitment.MagnitudeRangeCheck)
          "v_net magnitude" Advice.A9 0)).
    set (sign :=
      layouter_value
        (Garden.Orchard.circuit.assign_free_advice
          (Garden.Orchard.circuit.value_commitment_region
            RegionId.ValueCommitment.SignRangeCheck)
          "v_net sign" Advice.A9 0)).
    set (value_commit_v :=
      layouter_value
        (Garden.Orchard.circuit.synthesize_short_fixed_base_mul magnitude sign)).
    set (blind :=
      layouter_value
        Garden.Orchard.circuit.synth_value_commit_r_mul).
    pose (cv_add :=
      Garden.Orchard.circuit.synthesize_complete_point_add
        (Garden.Orchard.circuit.value_commitment_region
          RegionId.ValueCommitment.CompletePointAdd)
        "cv" value_commit_v blind).
    assert (Hcomplete_facts :
        interpret_facts Γ (layouter_facts cv_add)).
    { subst cv_add blind value_commit_v sign magnitude.
      pose proof Hfacts as Hcv_facts.
      unfold Garden.Orchard.circuit.synthesize in Hcv_facts.
      do 3 apply interpret_layouter_facts_bind_right in Hcv_facts.
      apply interpret_layouter_facts_bind_left in Hcv_facts.
      unfold Garden.Orchard.circuit.synthesize_value_commitment in Hcv_facts.
      do 4 apply interpret_layouter_facts_bind_right in Hcv_facts.
      apply interpret_layouter_facts_bind_left in Hcv_facts.
      unfold Garden.Orchard.circuit.synthesize_value_commit_orchard in Hcv_facts.
      apply interpret_layouter_facts_in_namespace in Hcv_facts.
      do 2 apply interpret_layouter_facts_bind_right in Hcv_facts.
      exact Hcv_facts. }
    assert (Hinstance :
        eval_cell Γ
          (layouter_value cv_add).(Garden.Orchard.circuit.AssignedPoint.y) =
        Γ.(Assignment.instance_) Instance_.Primary Garden.Orchard.circuit.CV_NET_Y).
    { subst cv_add blind value_commit_v sign magnitude.
      pose proof Hfacts as Hinstance_facts.
      unfold Garden.Orchard.circuit.synthesize in Hinstance_facts.
      do 3 apply interpret_layouter_facts_bind_right in Hinstance_facts.
      apply interpret_layouter_facts_bind_left in Hinstance_facts.
      unfold Garden.Orchard.circuit.synthesize_value_commitment in Hinstance_facts.
      do 6 apply interpret_layouter_facts_bind_right in Hinstance_facts.
      apply interpret_layouter_facts_bind_left in Hinstance_facts.
      cbn [layouter_facts interpret_facts interpret_fact eval_cell] in Hinstance_facts.
      destruct Hinstance_facts as [Hinstance _].
      exact Hinstance. }
    apply (read_public_instance_eq_of_cell Γ
      (layouter_value cv_add).(Garden.Orchard.circuit.AssignedPoint.y)
      Garden.Orchard.circuit.CV_NET_Y).
    - exact Hinstance.
    - rewrite Hinstance.
      subst cv_add.
      exact (complete_point_add_instance_y_correct Γ
        (Garden.Orchard.circuit.value_commitment_region
          RegionId.ValueCommitment.CompletePointAdd)
        "cv" value_commit_v blind Instance_.Primary Garden.Orchard.circuit.CV_NET_Y
        Hcomplete_facts Hgates Hinstance).
  Qed.

  Lemma cv_net_x_correct_of_fixed_base
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (Hvalue :
        let magnitude :=
          layouter_value
            (Garden.Orchard.circuit.assign_free_advice
              (Garden.Orchard.circuit.value_commitment_region
                RegionId.ValueCommitment.MagnitudeRangeCheck)
              "v_net magnitude" Advice.A9 0) in
        let sign :=
          layouter_value
            (Garden.Orchard.circuit.assign_free_advice
              (Garden.Orchard.circuit.value_commitment_region
                RegionId.ValueCommitment.SignRangeCheck)
              "v_net sign" Advice.A9 0) in
        let v_point :=
          EccSpec.fixed_scalar_mul
            (OrchardSpec.value_commit_v orchard_circuit_params)
            (read9 Γ
              (RegionId.ValueCommitment
                RegionId.ValueCommitment.MagnitudeRangeCheck))
            (read_us Γ
              (RegionId.ValueCommitment
                RegionId.ValueCommitment.ValueCommitVIncomplete) 22) in
        Field.map_mod
          (assigned_point_value Γ
            (layouter_value
              (Garden.Orchard.circuit
                .synthesize_short_fixed_base_mul magnitude sign))) =
        {|
          Point.x := Point.x v_point;
          Point.y :=
            read9 Γ
              (RegionId.ValueCommitment
                RegionId.ValueCommitment.SignRangeCheck) *F
            Point.y v_point;
        |})
      (Hblind :
        Field.map_mod
          (assigned_point_value Γ
            (layouter_value
              Garden.Orchard.circuit.synth_value_commit_r_mul)) =
        EccSpec.fixed_scalar_mul
          (OrchardSpec.value_commit_r orchard_circuit_params)
          (read_scalar_from_windows Γ
            (RegionId.ValueCommitment
              RegionId.ValueCommitment.ValueCommitRIncomplete) 85)
          (read_us Γ
            (RegionId.ValueCommitment
              RegionId.ValueCommitment.ValueCommitRIncomplete) 85)) :
    read_public_instance Γ Garden.Orchard.circuit.CV_NET_X =
      Point.x (OrchardSpec.out_cv_net (action_spec_of Γ)).
  Proof.
    rewrite (cv_net_x_complete_add_bridge Γ Hcircuit).
    unfold action_spec_of, output_with_witness, read_action_inputs,
      read_action_inputs_with_anchor, read_action_witness.
    cbn [OrchardSpec.out_cv_net OrchardSpec.orchard_action_spec
      OrchardSpec.value_commit OrchardSpec.in_magnitude OrchardSpec.in_sign
      OrchardSpec.in_rcv OrchardSpec.w_us_v OrchardSpec.w_us_rcv
      OrchardSpec.value_commit_v OrchardSpec.value_commit_r].
    unfold OrchardSpec.value_commit.
    rewrite Hvalue, Hblind.
    reflexivity.
  Qed.

  Lemma cv_net_y_correct_of_fixed_base
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (Hvalue :
        let magnitude :=
          layouter_value
            (Garden.Orchard.circuit.assign_free_advice
              (Garden.Orchard.circuit.value_commitment_region
                RegionId.ValueCommitment.MagnitudeRangeCheck)
              "v_net magnitude" Advice.A9 0) in
        let sign :=
          layouter_value
            (Garden.Orchard.circuit.assign_free_advice
              (Garden.Orchard.circuit.value_commitment_region
                RegionId.ValueCommitment.SignRangeCheck)
              "v_net sign" Advice.A9 0) in
        let v_point :=
          EccSpec.fixed_scalar_mul
            (OrchardSpec.value_commit_v orchard_circuit_params)
            (read9 Γ
              (RegionId.ValueCommitment
                RegionId.ValueCommitment.MagnitudeRangeCheck))
            (read_us Γ
              (RegionId.ValueCommitment
                RegionId.ValueCommitment.ValueCommitVIncomplete) 22) in
        Field.map_mod
          (assigned_point_value Γ
            (layouter_value
              (Garden.Orchard.circuit
                .synthesize_short_fixed_base_mul magnitude sign))) =
        {|
          Point.x := Point.x v_point;
          Point.y :=
            read9 Γ
              (RegionId.ValueCommitment
                RegionId.ValueCommitment.SignRangeCheck) *F
            Point.y v_point;
        |})
      (Hblind :
        Field.map_mod
          (assigned_point_value Γ
            (layouter_value
              Garden.Orchard.circuit.synth_value_commit_r_mul)) =
        EccSpec.fixed_scalar_mul
          (OrchardSpec.value_commit_r orchard_circuit_params)
          (read_scalar_from_windows Γ
            (RegionId.ValueCommitment
              RegionId.ValueCommitment.ValueCommitRIncomplete) 85)
          (read_us Γ
            (RegionId.ValueCommitment
              RegionId.ValueCommitment.ValueCommitRIncomplete) 85)) :
    read_public_instance Γ Garden.Orchard.circuit.CV_NET_Y =
      Point.y (OrchardSpec.out_cv_net (action_spec_of Γ)).
  Proof.
    rewrite (cv_net_y_complete_add_bridge Γ Hcircuit).
    unfold action_spec_of, output_with_witness, read_action_inputs,
      read_action_inputs_with_anchor, read_action_witness.
    cbn [OrchardSpec.out_cv_net OrchardSpec.orchard_action_spec
      OrchardSpec.value_commit OrchardSpec.in_magnitude OrchardSpec.in_sign
      OrchardSpec.in_rcv OrchardSpec.w_us_v OrchardSpec.w_us_rcv
      OrchardSpec.value_commit_v OrchardSpec.value_commit_r].
    unfold OrchardSpec.value_commit.
    rewrite Hvalue, Hblind.
    reflexivity.
  Qed.

  Lemma rk_x_complete_add_bridge
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    let alpha_commitment :=
      layouter_value
        Garden.Orchard.circuit.synthesize_full_fixed_base_mul_spend_auth_g in
    let ak_P :=
      layouter_value
        (Garden.Orchard.circuit.witness_non_identity_point
          (Garden.Orchard.circuit.witness_input_region RegionId.WitnessInput.AkP)
          "witness ak_P") in
    read_public_instance Γ Garden.Orchard.circuit.RK_X =
      Point.x
        (EccSpec.point_add
          (Field.map_mod (assigned_point_value Γ alpha_commitment))
          (Field.map_mod (assigned_point_value Γ ak_P))).
  Proof.
    destruct Hcircuit as [Hfacts HSatisfies].
    destruct HSatisfies as [Hgates Hlookups].
    set (alpha_commitment :=
      layouter_value
        Garden.Orchard.circuit.synthesize_full_fixed_base_mul_spend_auth_g).
    set (ak_P :=
      layouter_value
        (Garden.Orchard.circuit.witness_non_identity_point
          (Garden.Orchard.circuit.witness_input_region RegionId.WitnessInput.AkP)
          "witness ak_P")).
    pose (rk_add :=
      Garden.Orchard.circuit.synthesize_complete_point_add
        (Garden.Orchard.circuit.spend_authority_region
          RegionId.SpendAuthority.CompletePointAdd)
        "rk" alpha_commitment ak_P).
    assert (Hcomplete_facts :
        interpret_facts Γ (layouter_facts rk_add)).
    { subst rk_add ak_P alpha_commitment.
      pose proof Hfacts as Hrk_facts.
      unfold Garden.Orchard.circuit.synthesize in Hrk_facts.
      do 6 apply interpret_layouter_facts_bind_right in Hrk_facts.
      apply interpret_layouter_facts_bind_left in Hrk_facts.
      unfold Garden.Orchard.circuit.synthesize_spend_authority in Hrk_facts.
      do 2 apply interpret_layouter_facts_bind_right in Hrk_facts.
      apply interpret_layouter_facts_bind_left in Hrk_facts.
      exact Hrk_facts. }
    assert (Hinstance :
        eval_cell Γ
          (layouter_value rk_add).(Garden.Orchard.circuit.AssignedPoint.x) =
        Γ.(Assignment.instance_) Instance_.Primary Garden.Orchard.circuit.RK_X).
    { subst rk_add ak_P alpha_commitment.
      pose proof Hfacts as Hinstance_facts.
      unfold Garden.Orchard.circuit.synthesize in Hinstance_facts.
      do 6 apply interpret_layouter_facts_bind_right in Hinstance_facts.
      apply interpret_layouter_facts_bind_left in Hinstance_facts.
      unfold Garden.Orchard.circuit.synthesize_spend_authority in Hinstance_facts.
      do 3 apply interpret_layouter_facts_bind_right in Hinstance_facts.
      apply interpret_layouter_facts_bind_left in Hinstance_facts.
      cbn [layouter_facts interpret_facts interpret_fact eval_cell] in Hinstance_facts.
      destruct Hinstance_facts as [Hinstance _].
      exact Hinstance. }
    apply (read_public_instance_eq_of_cell Γ
      (layouter_value rk_add).(Garden.Orchard.circuit.AssignedPoint.x)
      Garden.Orchard.circuit.RK_X).
    - exact Hinstance.
    - rewrite Hinstance.
      subst rk_add.
      exact (complete_point_add_instance_x_correct Γ
        (Garden.Orchard.circuit.spend_authority_region
          RegionId.SpendAuthority.CompletePointAdd)
        "rk" alpha_commitment ak_P Instance_.Primary Garden.Orchard.circuit.RK_X
        Hcomplete_facts Hgates Hinstance).
  Qed.

  Lemma rk_y_complete_add_bridge
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    let alpha_commitment :=
      layouter_value
        Garden.Orchard.circuit.synthesize_full_fixed_base_mul_spend_auth_g in
    let ak_P :=
      layouter_value
        (Garden.Orchard.circuit.witness_non_identity_point
          (Garden.Orchard.circuit.witness_input_region RegionId.WitnessInput.AkP)
          "witness ak_P") in
    read_public_instance Γ Garden.Orchard.circuit.RK_Y =
      Point.y
        (EccSpec.point_add
          (Field.map_mod (assigned_point_value Γ alpha_commitment))
          (Field.map_mod (assigned_point_value Γ ak_P))).
  Proof.
    destruct Hcircuit as [Hfacts HSatisfies].
    destruct HSatisfies as [Hgates Hlookups].
    set (alpha_commitment :=
      layouter_value
        Garden.Orchard.circuit.synthesize_full_fixed_base_mul_spend_auth_g).
    set (ak_P :=
      layouter_value
        (Garden.Orchard.circuit.witness_non_identity_point
          (Garden.Orchard.circuit.witness_input_region RegionId.WitnessInput.AkP)
          "witness ak_P")).
    pose (rk_add :=
      Garden.Orchard.circuit.synthesize_complete_point_add
        (Garden.Orchard.circuit.spend_authority_region
          RegionId.SpendAuthority.CompletePointAdd)
        "rk" alpha_commitment ak_P).
    assert (Hcomplete_facts :
        interpret_facts Γ (layouter_facts rk_add)).
    { subst rk_add ak_P alpha_commitment.
      pose proof Hfacts as Hrk_facts.
      unfold Garden.Orchard.circuit.synthesize in Hrk_facts.
      do 6 apply interpret_layouter_facts_bind_right in Hrk_facts.
      apply interpret_layouter_facts_bind_left in Hrk_facts.
      unfold Garden.Orchard.circuit.synthesize_spend_authority in Hrk_facts.
      do 2 apply interpret_layouter_facts_bind_right in Hrk_facts.
      apply interpret_layouter_facts_bind_left in Hrk_facts.
      exact Hrk_facts. }
    assert (Hinstance :
        eval_cell Γ
          (layouter_value rk_add).(Garden.Orchard.circuit.AssignedPoint.y) =
        Γ.(Assignment.instance_) Instance_.Primary Garden.Orchard.circuit.RK_Y).
    { subst rk_add ak_P alpha_commitment.
      pose proof Hfacts as Hinstance_facts.
      unfold Garden.Orchard.circuit.synthesize in Hinstance_facts.
      do 6 apply interpret_layouter_facts_bind_right in Hinstance_facts.
      apply interpret_layouter_facts_bind_left in Hinstance_facts.
      unfold Garden.Orchard.circuit.synthesize_spend_authority in Hinstance_facts.
      do 4 apply interpret_layouter_facts_bind_right in Hinstance_facts.
      apply interpret_layouter_facts_bind_left in Hinstance_facts.
      cbn [layouter_facts interpret_facts interpret_fact eval_cell] in Hinstance_facts.
      destruct Hinstance_facts as [Hinstance _].
      exact Hinstance. }
    apply (read_public_instance_eq_of_cell Γ
      (layouter_value rk_add).(Garden.Orchard.circuit.AssignedPoint.y)
      Garden.Orchard.circuit.RK_Y).
    - exact Hinstance.
    - rewrite Hinstance.
      subst rk_add.
      exact (complete_point_add_instance_y_correct Γ
        (Garden.Orchard.circuit.spend_authority_region
          RegionId.SpendAuthority.CompletePointAdd)
        "rk" alpha_commitment ak_P Instance_.Primary Garden.Orchard.circuit.RK_Y
        Hcomplete_facts Hgates Hinstance).
  Qed.

  Definition spend_auth_g_fixed_scalar_mul_value
      (Γ : Assignment.t columns RegionId.t) : Point.t :=
    EccSpec.fixed_scalar_mul
      (OrchardSpec.spend_auth_g orchard_circuit_params)
      (read_scalar_from_windows Γ
        (RegionId.SpendAuthority
          RegionId.SpendAuthority.FullFixedIncomplete) 85)
      (read_us Γ
        (RegionId.SpendAuthority
          RegionId.SpendAuthority.FullFixedIncomplete) 85).

  Lemma full_spend_auth_g_value_correct_of_complete
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
    spend_auth_g_fixed_scalar_mul_value Γ.
  Proof.
    unfold spend_auth_g_fixed_scalar_mul_value.
    exact
      (full_spend_auth_g_mul_correct_of_complete
        Γ Hcircuit Hpre).
  Qed.

  (** The SpendAuthG fixed-base multiple [α]·G is on the curve, OR is the
      [(0, 0)] identity (the latter exactly when [α ≡ 0], e.g. the all-zeros
      scalar, where the windows cancel).  A plain on-curve / x-nonzero claim
      does not hold in that identity case, and determinism still holds there
      (both circuit and spec give the identity).  Proved by the closure
      [PallasModel.point_add_curve_poly_or_identity] applied to the circuit's
      last complete addition [point_add (window 84) acc83]. *)
  Lemma spend_auth_g_mul_curve_poly_or_identity
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (Hladder :
        incomplete_additions_complete_precondition Γ
          (RegionId.SpendAuthority
            RegionId.SpendAuthority.FullFixedIncomplete) 1 83
          (incomplete_additions_window_point Γ
            (RegionId.SpendAuthority
              RegionId.SpendAuthority.FullFixedIncomplete) 0)) :
    point_on_curve (spend_auth_g_fixed_scalar_mul_value Γ) \/
    spend_auth_g_fixed_scalar_mul_value Γ = EccSpec.identity.
  Proof.
    set (region :=
      RegionId.SpendAuthority RegionId.SpendAuthority.FullFixedIncomplete).
    set (last_region :=
      RegionId.SpendAuthority RegionId.SpendAuthority.FullFixedLast).
    set (rows :=
      Garden.Orchard.constants.fixed_bases.spend_auth_g.full_fixed_rows).
    set (acc0 := incomplete_additions_window_point Γ region 0).
    set (acc83 := complete_additions_output Γ region 1 83 acc0).
    pose proof
      (spend_auth_g_complete_output_on_curve Γ Hcircuit Hladder)
      as Hacc_curve.
    pose proof
      (complete_additions_output_reduced Γ region 1 83 acc0
        (proj1 (incomplete_additions_window_point_reduced Γ region 0))
        (proj2 (incomplete_additions_window_point_reduced Γ region 0)))
      as [Hacc_xr Hacc_yr].
    pose proof (spend_authority_fixed_base_facts Γ Hcircuit) as Hfacts.
    unfold Garden.Orchard.circuit.synthesize_full_fixed_base_mul_spend_auth_g
      in Hfacts.
    pose proof Hfacts as Hincomplete_facts.
    apply interpret_layouter_facts_bind_left in Hincomplete_facts.
    assert (Hlast_curve :
        point_on_curve (incomplete_additions_window_point Γ region 84)).
    { replace 84 with (Z.of_nat 84) by reflexivity.
      apply (full_width_incomplete_region_window_on_curve Γ region rows
        84%nat Hincomplete_facts (holds_gates Γ Hcircuit)).
      lia. }
    pose proof (incomplete_additions_window_point_reduced Γ region 84)
      as [Hlast_xr Hlast_yr].
    pose proof
      (full_with_rows_complete_correct Γ
        region last_region rows Hfacts (holds_gates Γ Hcircuit) Hladder)
      as Hcomplete.
    change (Field.map_mod
      (assigned_point_value Γ
        (layouter_value
          Garden.Orchard.circuit.synthesize_full_fixed_base_mul_spend_auth_g)) =
      EccSpec.point_add
        (incomplete_additions_window_point Γ region 84) acc83)
      in Hcomplete.
    pose proof
      (full_spend_auth_g_mul_correct_of_complete
        Γ Hcircuit Hladder) as Hfixed.
    unfold spend_auth_g_fixed_scalar_mul_value.
    rewrite <- Hfixed.
    rewrite Hcomplete.
    exact (PallasModel.point_add_curve_poly_or_identity
      (incomplete_additions_window_point Γ region 84) acc83
      Hlast_xr Hlast_yr Hacc_xr Hacc_yr Hlast_curve Hacc_curve).
  Qed.

  Definition rk_ak_point
      (Γ : Assignment.t columns RegionId.t) : Point.t :=
    read_point Γ (RegionId.WitnessInput RegionId.WitnessInput.AkP).

  Lemma rk_out_rk_x_eq
      (Γ : Assignment.t columns RegionId.t) :
    Point.x (OrchardSpec.out_rk (action_spec_of Γ)) =
    Point.x
      (EccSpec.point_add
        (rk_ak_point Γ)
        (spend_auth_g_fixed_scalar_mul_value Γ)).
  Proof.
    unfold action_spec_of, output_with_witness, read_action_inputs,
      read_action_inputs_with_anchor, read_action_witness, rk_ak_point,
      spend_auth_g_fixed_scalar_mul_value.
    cbn [OrchardSpec.out_rk OrchardSpec.orchard_action_spec
      OrchardSpec.in_ak OrchardSpec.in_alpha OrchardSpec.w_us_alpha
      OrchardSpec.spend_auth_g].
    unfold OrchardSpec.spend_auth_randomize.
    reflexivity.
  Qed.

  Lemma rk_out_rk_y_eq
      (Γ : Assignment.t columns RegionId.t) :
    Point.y (OrchardSpec.out_rk (action_spec_of Γ)) =
    Point.y
      (EccSpec.point_add
        (rk_ak_point Γ)
        (spend_auth_g_fixed_scalar_mul_value Γ)).
  Proof.
    unfold action_spec_of, output_with_witness, read_action_inputs,
      read_action_inputs_with_anchor, read_action_witness, rk_ak_point,
      spend_auth_g_fixed_scalar_mul_value.
    cbn [OrchardSpec.out_rk OrchardSpec.orchard_action_spec
      OrchardSpec.in_ak OrchardSpec.in_alpha OrchardSpec.w_us_alpha
      OrchardSpec.spend_auth_g].
    unfold OrchardSpec.spend_auth_randomize.
    reflexivity.
  Qed.

  Lemma read_point_map_mod
      (Γ : Assignment.t columns RegionId.t)
      (region : RegionId.t) :
    Field.map_mod (read_point Γ region) = read_point Γ region.
  Proof.
    unfold read_point, read, read1, read_advice.
    cbn [Field.map_mod Point.IsMapMod Point.x Point.y].
    rewrite !eval_advice_cur_cell.
    rewrite !FieldRewrite.from_from.
    reflexivity.
  Qed.

  Lemma read_point_x_reduced
      (Γ : Assignment.t columns RegionId.t)
      (region : RegionId.t) :
    UnOp.from (Point.x (read_point Γ region)) =
      Point.x (read_point Γ region).
  Proof.
    pose proof (f_equal Point.x (read_point_map_mod Γ region)) as Hx.
    cbn [Field.map_mod Point.IsMapMod Point.x] in Hx.
    exact Hx.
  Qed.

  Lemma read_point_y_reduced
      (Γ : Assignment.t columns RegionId.t)
      (region : RegionId.t) :
    UnOp.from (Point.y (read_point Γ region)) =
      Point.y (read_point Γ region).
  Proof.
    pose proof (f_equal Point.y (read_point_map_mod Γ region)) as Hy.
    cbn [Field.map_mod Point.IsMapMod Point.y] in Hy.
    exact Hy.
  Qed.

  Lemma point_map_mod_x_reduced_of_eq
      (P Q : Point.t)
      (Hmap : Field.map_mod P = Q) :
    UnOp.from (Point.x Q) = Point.x Q.
  Proof.
    rewrite <- Hmap.
    cbn [Field.map_mod Point.IsMapMod Point.x].
    apply FieldRewrite.from_from.
  Qed.

  Lemma point_map_mod_y_reduced_of_eq
      (P Q : Point.t)
      (Hmap : Field.map_mod P = Q) :
    UnOp.from (Point.y Q) = Point.y Q.
  Proof.
    rewrite <- Hmap.
    cbn [Field.map_mod Point.IsMapMod Point.y].
    apply FieldRewrite.from_from.
  Qed.

  Lemma rk_ak_point_on_curve
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ) :
    point_on_curve (rk_ak_point Γ).
  Proof.
    unfold point_on_curve, rk_ak_point, read_point, read, read1, read_advice.
    change (Γ ⊢ ⟦ Garden.Halo2.halo2_gadgets.ecc.chip.witness_point
        .curve_eqn Advice.A0 Advice.A1 ⟧
      (Garden.Orchard.circuit.witness_input_region
        RegionId.WitnessInput.AkP, 0) = 0).
    exact (ak_P_on_curve Γ Hcircuit).
  Qed.

  Lemma rk_ak_point_x_reduced
      (Γ : Assignment.t columns RegionId.t) :
    UnOp.from (Point.x (rk_ak_point Γ)) =
      Point.x (rk_ak_point Γ).
  Proof.
    unfold rk_ak_point.
    apply read_point_x_reduced.
  Qed.

  Lemma rk_ak_point_y_reduced
      (Γ : Assignment.t columns RegionId.t) :
    UnOp.from (Point.y (rk_ak_point Γ)) =
      Point.y (rk_ak_point Γ).
  Proof.
    unfold rk_ak_point.
    apply read_point_y_reduced.
  Qed.

  Lemma spend_auth_g_mul_x_reduced_of_complete
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (Hladder :
        incomplete_additions_complete_precondition Γ
          (RegionId.SpendAuthority
            RegionId.SpendAuthority.FullFixedIncomplete) 1 83
          (incomplete_additions_window_point Γ
          (RegionId.SpendAuthority
            RegionId.SpendAuthority.FullFixedIncomplete) 0)) :
    UnOp.from (Point.x (spend_auth_g_fixed_scalar_mul_value Γ)) =
      Point.x (spend_auth_g_fixed_scalar_mul_value Γ).
  Proof.
    eapply point_map_mod_x_reduced_of_eq.
    exact
      (full_spend_auth_g_mul_correct_of_complete
        Γ Hcircuit Hladder).
  Qed.

  Lemma spend_auth_g_mul_y_reduced_of_complete
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (Hladder :
        incomplete_additions_complete_precondition Γ
          (RegionId.SpendAuthority
            RegionId.SpendAuthority.FullFixedIncomplete) 1 83
          (incomplete_additions_window_point Γ
          (RegionId.SpendAuthority
            RegionId.SpendAuthority.FullFixedIncomplete) 0)) :
    UnOp.from (Point.y (spend_auth_g_fixed_scalar_mul_value Γ)) =
      Point.y (spend_auth_g_fixed_scalar_mul_value Γ).
  Proof.
    eapply point_map_mod_y_reduced_of_eq.
    exact
      (full_spend_auth_g_mul_correct_of_complete
        Γ Hcircuit Hladder).
  Qed.

  Lemma rk_x_correct_of_fixed_base
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (Hfixed :
        Field.map_mod
          (assigned_point_value Γ
            (layouter_value
              Garden.Orchard.circuit.synthesize_full_fixed_base_mul_spend_auth_g)) =
        spend_auth_g_fixed_scalar_mul_value Γ)
      (Hcomm_x :
        Point.x
          (EccSpec.point_add
            (spend_auth_g_fixed_scalar_mul_value Γ)
            (rk_ak_point Γ)) =
        Point.x
          (EccSpec.point_add
            (rk_ak_point Γ)
            (spend_auth_g_fixed_scalar_mul_value Γ))) :
    read_public_instance Γ Garden.Orchard.circuit.RK_X =
      Point.x (OrchardSpec.out_rk (action_spec_of Γ)).
  Proof.
    rewrite (rk_x_complete_add_bridge Γ Hcircuit).
    rewrite (rk_out_rk_x_eq Γ).
    rewrite witness_non_identity_point_value.
    rewrite Hfixed.
    exact Hcomm_x.
  Qed.

  Lemma rk_y_correct_of_fixed_base
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (Hfixed :
        Field.map_mod
          (assigned_point_value Γ
            (layouter_value
              Garden.Orchard.circuit.synthesize_full_fixed_base_mul_spend_auth_g)) =
        spend_auth_g_fixed_scalar_mul_value Γ)
      (Hcomm_y :
        Point.y
          (EccSpec.point_add
            (spend_auth_g_fixed_scalar_mul_value Γ)
            (rk_ak_point Γ)) =
        Point.y
          (EccSpec.point_add
            (rk_ak_point Γ)
            (spend_auth_g_fixed_scalar_mul_value Γ))) :
    read_public_instance Γ Garden.Orchard.circuit.RK_Y =
      Point.y (OrchardSpec.out_rk (action_spec_of Γ)).
  Proof.
    rewrite (rk_y_complete_add_bridge Γ Hcircuit).
    rewrite (rk_out_rk_y_eq Γ).
    rewrite witness_non_identity_point_value.
    rewrite Hfixed.
    exact Hcomm_y.
  Qed.

  (** [point_add P identity = P] when [P] has a reduced nonzero x (so it is not
      the sentinel). *)
  Lemma point_add_identity_right (P : Point.t)
      (HPx : UnOp.from (Point.x P) = Point.x P)
      (HPx0 : UnOp.from (Point.x P) <> 0) :
    EccSpec.point_add P EccSpec.identity = P.
  Proof.
    destruct P as [px py]. cbn [Point.x Point.y] in *.
    unfold EccSpec.point_add, EccSpec.identity,
      add_proof.CompleteAddition.output.
    cbn [Point.x Point.y].
    destruct (px =? 0) eqn:E.
    - apply Z.eqb_eq in E. exfalso. apply HPx0. rewrite <- HPx, E.
      apply FieldRewrite.from_zero.
    - rewrite Z.eqb_refl. reflexivity.
  Qed.

  (** Complete-addition commutativity that tolerates the first operand being the
      identity sentinel (the [α ≡ 0] case): if [P] is on-curve or the identity,
      [Q] on-curve, and both reduced, then [point_add P Q = point_add Q P].
      Complete addition is genuinely commutative on the closed domain
      {curve points} ∪ {identity}. *)
  Lemma point_add_comm_curve_or_identity_reduced (P Q : Point.t)
      (HP : point_on_curve P \/ P = EccSpec.identity)
      (HQ : point_on_curve Q)
      (HPxr : UnOp.from (Point.x P) = Point.x P)
      (HPyr : UnOp.from (Point.y P) = Point.y P)
      (HQxr : UnOp.from (Point.x Q) = Point.x Q)
      (HQyr : UnOp.from (Point.y Q) = Point.y Q) :
    EccSpec.point_add P Q = EccSpec.point_add Q P.
  Proof.
    destruct HP as [HPoc | HPid].
    - apply EccSpec.point_add_comm_on_curve_nonzero_reduced.
      + exact HPoc.
      + exact HQ.
      + apply (EccSpec.pallas_curve_x_nonzero (Point.x P) (Point.y P)).
        exact HPoc.
      + apply (EccSpec.pallas_curve_x_nonzero (Point.x Q) (Point.y Q)).
        exact HQ.
      + exact HPxr.
      + exact HQxr.
      + exact HPyr.
      + exact HQyr.
    - subst P.
      rewrite EccSpec.point_add_identity_left.
      symmetry.
      apply point_add_identity_right.
      + exact HQxr.
      + apply (EccSpec.pallas_curve_x_nonzero (Point.x Q) (Point.y Q)).
        exact HQ.
  Qed.

  (** x- and y-coordinate projections of the commutativity, kept at the abstract
      point level so the [f_equal] never touches the large concrete fixed-base
      term (which makes it pathologically slow to elaborate). *)
  Lemma point_add_comm_curve_or_identity_reduced_x (P Q : Point.t)
      (HP : point_on_curve P \/ P = EccSpec.identity)
      (HQ : point_on_curve Q)
      (HPxr : UnOp.from (Point.x P) = Point.x P)
      (HPyr : UnOp.from (Point.y P) = Point.y P)
      (HQxr : UnOp.from (Point.x Q) = Point.x Q)
      (HQyr : UnOp.from (Point.y Q) = Point.y Q) :
    Point.x (EccSpec.point_add P Q) = Point.x (EccSpec.point_add Q P).
  Proof.
    exact (f_equal Point.x
      (point_add_comm_curve_or_identity_reduced P Q HP HQ
        HPxr HPyr HQxr HQyr)).
  Qed.

  Lemma point_add_comm_curve_or_identity_reduced_y (P Q : Point.t)
      (HP : point_on_curve P \/ P = EccSpec.identity)
      (HQ : point_on_curve Q)
      (HPxr : UnOp.from (Point.x P) = Point.x P)
      (HPyr : UnOp.from (Point.y P) = Point.y P)
      (HQxr : UnOp.from (Point.x Q) = Point.x Q)
      (HQyr : UnOp.from (Point.y Q) = Point.y Q) :
    Point.y (EccSpec.point_add P Q) = Point.y (EccSpec.point_add Q P).
  Proof.
    exact (f_equal Point.y
      (point_add_comm_curve_or_identity_reduced P Q HP HQ
        HPxr HPyr HQxr HQyr)).
  Qed.

  Lemma rk_point_add_comm_x_of_ladder
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (Hladder :
        incomplete_additions_complete_precondition Γ
          (RegionId.SpendAuthority
            RegionId.SpendAuthority.FullFixedIncomplete) 1 83
          (incomplete_additions_window_point Γ
            (RegionId.SpendAuthority
              RegionId.SpendAuthority.FullFixedIncomplete) 0)) :
    Point.x
      (EccSpec.point_add
        (spend_auth_g_fixed_scalar_mul_value Γ)
        (rk_ak_point Γ)) =
    Point.x
      (EccSpec.point_add
        (rk_ak_point Γ)
        (spend_auth_g_fixed_scalar_mul_value Γ)).
  Proof.
    apply point_add_comm_curve_or_identity_reduced_x.
    - exact
        (spend_auth_g_mul_curve_poly_or_identity
          Γ Hcircuit Hladder).
    - exact (rk_ak_point_on_curve Γ Hcircuit).
    - exact
        (spend_auth_g_mul_x_reduced_of_complete
          Γ Hcircuit Hladder).
    - exact
        (spend_auth_g_mul_y_reduced_of_complete
          Γ Hcircuit Hladder).
    - exact (rk_ak_point_x_reduced Γ).
    - exact (rk_ak_point_y_reduced Γ).
  Qed.

  Lemma rk_point_add_comm_y_of_ladder
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (Hladder :
        incomplete_additions_complete_precondition Γ
          (RegionId.SpendAuthority
            RegionId.SpendAuthority.FullFixedIncomplete) 1 83
          (incomplete_additions_window_point Γ
            (RegionId.SpendAuthority
              RegionId.SpendAuthority.FullFixedIncomplete) 0)) :
    Point.y
      (EccSpec.point_add
        (spend_auth_g_fixed_scalar_mul_value Γ)
        (rk_ak_point Γ)) =
    Point.y
      (EccSpec.point_add
        (rk_ak_point Γ)
        (spend_auth_g_fixed_scalar_mul_value Γ)).
  Proof.
    apply point_add_comm_curve_or_identity_reduced_y.
    - exact
        (spend_auth_g_mul_curve_poly_or_identity
          Γ Hcircuit Hladder).
    - exact (rk_ak_point_on_curve Γ Hcircuit).
    - exact
        (spend_auth_g_mul_x_reduced_of_complete
          Γ Hcircuit Hladder).
    - exact
        (spend_auth_g_mul_y_reduced_of_complete
          Γ Hcircuit Hladder).
    - exact (rk_ak_point_x_reduced Γ).
    - exact (rk_ak_point_y_reduced Γ).
  Qed.

  Lemma rk_x_correct_of_spend_auth_g_complete
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (Hladder :
        incomplete_additions_complete_precondition Γ
          (RegionId.SpendAuthority
            RegionId.SpendAuthority.FullFixedIncomplete) 1 83
          (incomplete_additions_window_point Γ
            (RegionId.SpendAuthority
              RegionId.SpendAuthority.FullFixedIncomplete) 0))
      (Hcomm_x :
        Point.x
          (EccSpec.point_add
            (spend_auth_g_fixed_scalar_mul_value Γ)
            (rk_ak_point Γ)) =
        Point.x
          (EccSpec.point_add
            (rk_ak_point Γ)
            (spend_auth_g_fixed_scalar_mul_value Γ))) :
    read_public_instance Γ Garden.Orchard.circuit.RK_X =
      Point.x (OrchardSpec.out_rk (action_spec_of Γ)).
  Proof.
    eapply rk_x_correct_of_fixed_base.
    - exact Hcircuit.
    - exact
        (full_spend_auth_g_value_correct_of_complete
          Γ Hcircuit Hladder).
    - exact Hcomm_x.
  Qed.

  Lemma rk_y_correct_of_spend_auth_g_complete
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (Hladder :
        incomplete_additions_complete_precondition Γ
          (RegionId.SpendAuthority
            RegionId.SpendAuthority.FullFixedIncomplete) 1 83
          (incomplete_additions_window_point Γ
            (RegionId.SpendAuthority
              RegionId.SpendAuthority.FullFixedIncomplete) 0))
      (Hcomm_y :
        Point.y
          (EccSpec.point_add
            (spend_auth_g_fixed_scalar_mul_value Γ)
            (rk_ak_point Γ)) =
        Point.y
          (EccSpec.point_add
            (rk_ak_point Γ)
            (spend_auth_g_fixed_scalar_mul_value Γ))) :
    read_public_instance Γ Garden.Orchard.circuit.RK_Y =
      Point.y (OrchardSpec.out_rk (action_spec_of Γ)).
  Proof.
    eapply rk_y_correct_of_fixed_base.
    - exact Hcircuit.
    - exact
        (full_spend_auth_g_value_correct_of_complete
          Γ Hcircuit Hladder).
    - exact Hcomm_y.
  Qed.

  Lemma rk_x_correct_of_spend_auth_g_ladder
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (Hladder :
        incomplete_additions_complete_precondition Γ
          (RegionId.SpendAuthority
            RegionId.SpendAuthority.FullFixedIncomplete) 1 83
          (incomplete_additions_window_point Γ
            (RegionId.SpendAuthority
              RegionId.SpendAuthority.FullFixedIncomplete) 0)) :
    read_public_instance Γ Garden.Orchard.circuit.RK_X =
      Point.x (OrchardSpec.out_rk (action_spec_of Γ)).
  Proof.
    eapply rk_x_correct_of_spend_auth_g_complete.
    - exact Hcircuit.
    - exact Hladder.
    - exact (rk_point_add_comm_x_of_ladder Γ Hcircuit Hladder).
  Qed.

  Lemma rk_y_correct_of_spend_auth_g_ladder
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (Hladder :
        incomplete_additions_complete_precondition Γ
          (RegionId.SpendAuthority
            RegionId.SpendAuthority.FullFixedIncomplete) 1 83
          (incomplete_additions_window_point Γ
            (RegionId.SpendAuthority
              RegionId.SpendAuthority.FullFixedIncomplete) 0)) :
    read_public_instance Γ Garden.Orchard.circuit.RK_Y =
      Point.y (OrchardSpec.out_rk (action_spec_of Γ)).
  Proof.
    eapply rk_y_correct_of_spend_auth_g_complete.
    - exact Hcircuit.
    - exact Hladder.
    - exact (rk_point_add_comm_y_of_ladder Γ Hcircuit Hladder).
  Qed.

  Lemma rk_x_correct_of_spend_auth_g_ladder_distinct
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (Hdistinct : spend_auth_g_ladder_distinct_precondition Γ) :
    read_public_instance Γ Garden.Orchard.circuit.RK_X =
      Point.x (OrchardSpec.out_rk (action_spec_of Γ)).
  Proof.
    apply rk_x_correct_of_spend_auth_g_ladder.
    - exact Hcircuit.
    - exact
        (spend_auth_g_complete_of_distinct
          Γ Hcircuit Hdistinct).
  Qed.

  Lemma rk_y_correct_of_spend_auth_g_ladder_distinct
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (Hdistinct : spend_auth_g_ladder_distinct_precondition Γ) :
    read_public_instance Γ Garden.Orchard.circuit.RK_Y =
      Point.y (OrchardSpec.out_rk (action_spec_of Γ)).
  Proof.
    apply rk_y_correct_of_spend_auth_g_ladder.
    - exact Hcircuit.
    - exact
        (spend_auth_g_complete_of_distinct
          Γ Hcircuit Hdistinct).
  Qed.

  Lemma nf_old_complete_add_bridge
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
    let poseidon_output :=
      layouter_value
        (Garden.Halo2.halo2_gadgets.poseidon.pow5.synthesize_hash nk rho_old) in
    let scalar :=
      layouter_value
        (Garden.Orchard.circuit.synthesize_scalar_add
          (Garden.Orchard.circuit.nullifier_region RegionId.Nullifier.ScalarAdd)
          "scalar = poseidon_hash(nk, rho) + psi"
          poseidon_output
          psi_old) in
    let product :=
      layouter_value
        (Garden.Orchard.circuit.synth_nullifier_k_mul
          scalar) in
    read_public_instance Γ Garden.Orchard.circuit.NF_OLD =
      Point.x
        (EccSpec.point_add
          (Field.map_mod (assigned_point_value Γ cm_old))
          (Field.map_mod (assigned_point_value Γ product))).
  Proof.
    destruct Hcircuit as [Hfacts HSatisfies].
    destruct HSatisfies as [Hgates Hlookups].
    set (psi_old :=
      layouter_value
        (Garden.Orchard.circuit.assign_free_advice
          (Garden.Orchard.circuit.witness_input_region
            RegionId.WitnessInput.PsiOld)
          "witness psi_old" Advice.A0 0)).
    set (rho_old :=
      layouter_value
        (Garden.Orchard.circuit.assign_free_advice
          (Garden.Orchard.circuit.witness_input_region
            RegionId.WitnessInput.RhoOld)
          "witness rho_old" Advice.A0 0)).
    set (cm_old :=
      layouter_value
        (Garden.Orchard.circuit.witness_point
          (Garden.Orchard.circuit.witness_input_region
            RegionId.WitnessInput.CmOld)
          "cm_old")).
    set (nk :=
      layouter_value
        (Garden.Orchard.circuit.assign_free_advice
          (Garden.Orchard.circuit.witness_input_region
            RegionId.WitnessInput.Nk)
          "witness nk" Advice.A0 0)).
    set (poseidon_output :=
      layouter_value
        (Garden.Halo2.halo2_gadgets.poseidon.pow5.synthesize_hash nk rho_old)).
    set (scalar :=
      layouter_value
        (Garden.Orchard.circuit.synthesize_scalar_add
          (Garden.Orchard.circuit.nullifier_region RegionId.Nullifier.ScalarAdd)
          "scalar = poseidon_hash(nk, rho) + psi"
          poseidon_output
          psi_old)).
    set (product :=
      layouter_value
        (Garden.Orchard.circuit.synth_nullifier_k_mul
          scalar)).
    pose (nf_add :=
      Garden.Orchard.circuit.synthesize_complete_point_add
        (Garden.Orchard.circuit.nullifier_region
          RegionId.Nullifier.CompletePointAdd)
        "nf" cm_old product).
    assert (Hcomplete_facts :
        interpret_facts Γ (layouter_facts nf_add)).
    { subst nf_add product scalar poseidon_output nk cm_old rho_old psi_old.
      pose proof Hfacts as Hnf_facts.
      unfold Garden.Orchard.circuit.synthesize in Hnf_facts.
      do 4 apply interpret_layouter_facts_bind_right in Hnf_facts.
      apply interpret_layouter_facts_bind_left in Hnf_facts.
      unfold Garden.Orchard.circuit.synthesize_nullifier in Hnf_facts.
      apply interpret_layouter_facts_bind_left in Hnf_facts.
      apply interpret_layouter_facts_in_namespace in Hnf_facts.
      do 3 apply interpret_layouter_facts_bind_right in Hnf_facts.
      apply interpret_layouter_facts_bind_left in Hnf_facts.
      exact Hnf_facts. }
    assert (Hinstance :
        eval_cell Γ
          (layouter_value nf_add).(Garden.Orchard.circuit.AssignedPoint.x) =
        Γ.(Assignment.instance_) Instance_.Primary Garden.Orchard.circuit.NF_OLD).
    { subst nf_add product scalar poseidon_output nk cm_old rho_old psi_old.
      pose proof Hfacts as Hinstance_facts.
      unfold Garden.Orchard.circuit.synthesize in Hinstance_facts.
      do 5 apply interpret_layouter_facts_bind_right in Hinstance_facts.
      apply interpret_layouter_facts_bind_left in Hinstance_facts.
      cbn [layouter_facts interpret_facts interpret_fact eval_cell] in Hinstance_facts.
      destruct Hinstance_facts as [Hinstance _].
      exact Hinstance. }
    apply (read_public_instance_eq_of_cell Γ
      (layouter_value nf_add).(Garden.Orchard.circuit.AssignedPoint.x)
      Garden.Orchard.circuit.NF_OLD).
    - exact Hinstance.
    - rewrite Hinstance.
      subst nf_add.
      exact (complete_point_add_instance_x_correct Γ
        (Garden.Orchard.circuit.nullifier_region
          RegionId.Nullifier.CompletePointAdd)
        "nf" cm_old product Instance_.Primary Garden.Orchard.circuit.NF_OLD
        Hcomplete_facts Hgates Hinstance).
  Qed.

  Lemma nf_old_correct_of_fixed_base
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (Hfixed :
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
            (RegionId.Nullifier RegionId.Nullifier.BaseFieldIncomplete) 85))
      (Hcomm_x :
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
              (RegionId.WitnessInput RegionId.WitnessInput.CmOld)))) :
    read_public_instance Γ Garden.Orchard.circuit.NF_OLD =
      OrchardSpec.out_nf_old (action_spec_of Γ).
  Proof.
    rewrite (nf_old_complete_add_bridge Γ Hcircuit).
    unfold action_spec_of, output_with_witness, read_action_inputs,
      read_action_inputs_with_anchor, read_action_witness.
    cbn [OrchardSpec.out_nf_old OrchardSpec.orchard_action_spec
      OrchardSpec.nullifier OrchardSpec.in_nk OrchardSpec.in_rho_old
      OrchardSpec.in_psi_old OrchardSpec.in_cm_old OrchardSpec.w_us_k
      OrchardSpec.nullifier_k].
    unfold OrchardSpec.nullifier, EccSpec.extract_x.
    rewrite assigned_point_value_witness_point.
    rewrite Hfixed.
    unfold Garden.Orchard.circuit.witness_input_region.
    exact Hcomm_x.
  Qed.

  Lemma cmx_instance_eq_note_commit_new
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ) :
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
    let v_new :=
      layouter_value
        (Garden.Orchard.circuit.assign_free_advice
          (Garden.Orchard.circuit.witness_input_region
            RegionId.WitnessInput.VNew)
          "witness v_new" Advice.A0 0) in
    let rho_new :=
      layouter_value
        (Garden.Orchard.circuit.synthesize_nullifier
          rho_old psi_old nk cm_old) in
    let g_d_new_star :=
      layouter_value
        (Garden.Orchard.circuit.witness_non_identity_point
          RegionId.NoteCommitNewWitnessGD
          "witness g_d_new_star") in
    let pk_d_new :=
      layouter_value
        (Garden.Orchard.circuit.witness_non_identity_point
          RegionId.NoteCommitNewWitnessPkD
          "witness pk_d_new") in
    let psi_new :=
      layouter_value
        (Garden.Orchard.circuit.assign_free_advice
          RegionId.NoteCommitNewWitnessPsi
          "witness psi_new" Advice.A0 0) in
    read_public_instance Γ Garden.Orchard.circuit.CMX =
      UnOp.from
        (eval_cell Γ
          (layouter_value
            (Garden.Orchard.circuit.note_commit.synthesize_new
              g_d_new_star.(Garden.Orchard.circuit.AssignedPoint.x)
              g_d_new_star.(Garden.Orchard.circuit.AssignedPoint.y)
              pk_d_new.(Garden.Orchard.circuit.AssignedPoint.x)
              pk_d_new.(Garden.Orchard.circuit.AssignedPoint.y)
              v_new
              rho_new
              psi_new)).(Garden.Orchard.circuit.note_commit.AssignedPoint.x)).
  Proof.
    destruct Hcircuit as [Hfacts HSatisfies].
    pose proof Hfacts as Hinstance_facts.
    unfold Garden.Orchard.circuit.synthesize in Hinstance_facts.
    do 9 apply interpret_layouter_facts_bind_right in Hinstance_facts.
    apply interpret_layouter_facts_bind_left in Hinstance_facts.
    unfold Garden.Orchard.circuit.synthesize_note_commit_new in Hinstance_facts.
    do 5 apply interpret_layouter_facts_bind_right in Hinstance_facts.
    apply interpret_layouter_facts_bind_left in Hinstance_facts.
    cbn [layouter_facts interpret_facts interpret_fact eval_cell]
      in Hinstance_facts.
    destruct Hinstance_facts as [Hinstance _].
    apply read_public_instance_eq_cell.
    exact Hinstance.
  Qed.

  Lemma cmx_correct_of_note_commit_new
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit : Holds Γ)
      (Hnote :
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
        let v_new :=
          layouter_value
            (Garden.Orchard.circuit.assign_free_advice
              (Garden.Orchard.circuit.witness_input_region
                RegionId.WitnessInput.VNew)
              "witness v_new" Advice.A0 0) in
        let rho_new :=
          layouter_value
            (Garden.Orchard.circuit.synthesize_nullifier
              rho_old psi_old nk cm_old) in
        let g_d_new_star :=
          layouter_value
            (Garden.Orchard.circuit.witness_non_identity_point
              RegionId.NoteCommitNewWitnessGD
              "witness g_d_new_star") in
        let pk_d_new :=
          layouter_value
            (Garden.Orchard.circuit.witness_non_identity_point
              RegionId.NoteCommitNewWitnessPkD
              "witness pk_d_new") in
        let psi_new :=
          layouter_value
            (Garden.Orchard.circuit.assign_free_advice
              RegionId.NoteCommitNewWitnessPsi
              "witness psi_new" Advice.A0 0) in
        UnOp.from
          (eval_cell Γ
            (layouter_value
              (Garden.Orchard.circuit.note_commit.synthesize_new
                g_d_new_star.(Garden.Orchard.circuit.AssignedPoint.x)
                g_d_new_star.(Garden.Orchard.circuit.AssignedPoint.y)
                pk_d_new.(Garden.Orchard.circuit.AssignedPoint.x)
                pk_d_new.(Garden.Orchard.circuit.AssignedPoint.y)
                v_new
                rho_new
                psi_new)).(Garden.Orchard.circuit.note_commit.AssignedPoint.x)) =
          OrchardSpec.out_cmx (action_spec_of Γ)) :
    read_public_instance Γ Garden.Orchard.circuit.CMX =
      OrchardSpec.out_cmx (action_spec_of Γ).
  Proof.
    rewrite (cmx_instance_eq_note_commit_new Γ Hcircuit).
    exact Hnote.
  Qed.

End OrchardActionBridges.
