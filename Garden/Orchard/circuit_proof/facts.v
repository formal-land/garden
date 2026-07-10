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
Require Import Garden.Field.Field.
Require Import Garden.Field.Div.
Require Import Garden.Field.Lemmas.
Require Import Garden.Plonky3.M.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Lists.List.
Require Import Stdlib.setoid_ring.Ring.

Require Import Garden.Orchard.circuit_proof.inputs.

#[local] Existing Instance Primes.PallasPIsPrime.

Global Open Scope Z_scope.


Module OrchardActionFacts.
  Include OrchardActionInputs.

  Local Notation Holds Γ :=
    (circuit_holds Γ
      Garden.Orchard.circuit.synthesize
      (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty)).

  Lemma holds_facts (Γ : Assignment.t columns RegionId.t) :
    Holds Γ ->
    interpret_facts Γ (layouter_facts Garden.Orchard.circuit.synthesize).
  Proof.
    intros [Hfacts _].
    exact Hfacts.
  Qed.

  Lemma holds_gates (Γ : Assignment.t columns RegionId.t) :
    Holds Γ ->
    satisfies_gates Γ
      (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty).
  Proof.
    intros [_ HSatisfies].
    destruct HSatisfies as [Hgates _].
    exact Hgates.
  Qed.

  Lemma holds_lookups (Γ : Assignment.t columns RegionId.t) :
    Holds Γ ->
    satisfies_lookups Γ
      (layouter_table_rows Garden.Orchard.circuit.synthesize)
      (𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty).
  Proof.
    intros [_ HSatisfies].
    destruct HSatisfies as [_ Hlookups].
    exact Hlookups.
  Qed.

  Definition orchard_constraint_system : ConstraintSystem.t columns :=
    𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty.

  Definition orchard_gates_only_system : ConstraintSystem.t columns :=
    gates_only_system orchard_constraint_system.

  Lemma subprogram_holds_with_orchard_gates
      (Γ : Assignment.t columns RegionId.t)
      {A : Set}
      (program : Garden.Halo2.Synthesis.𝓛 columns RegionId.t A) :
    Holds Γ ->
    interpret_facts Γ (layouter_facts program) ->
    circuit_holds Γ program orchard_gates_only_system.
  Proof.
    intros Hcircuit Hprogram_facts.
    split.
    - exact Hprogram_facts.
    - split.
      + exact (satisfies_gates_only_system Γ
          orchard_constraint_system
          (holds_gates Γ Hcircuit)).
      + apply satisfies_lookups_nil.
        reflexivity.
  Qed.

  Lemma subprogram_holds_with_orchard_system
      (Γ : Assignment.t columns RegionId.t)
      {A : Set}
      (program : Garden.Halo2.Synthesis.𝓛 columns RegionId.t A)
      (system : ConstraintSystem.t columns) :
    Holds Γ ->
    interpret_facts Γ (layouter_facts program) ->
    (forall gate,
      List.In gate system.(ConstraintSystem.gates) ->
      List.In gate orchard_constraint_system.(ConstraintSystem.gates)) ->
    (forall arg,
      List.In arg system.(ConstraintSystem.lookups) ->
      List.In arg orchard_constraint_system.(ConstraintSystem.lookups)) ->
    layouter_table_rows Garden.Orchard.circuit.synthesize <=
      layouter_table_rows program ->
    circuit_holds Γ program system.
  Proof.
    intros Hcircuit Hprogram_facts Hgates_subset Hlookups_subset Hrows.
    split.
    - exact Hprogram_facts.
    - split.
      + exact (satisfies_gates_subset Γ system orchard_constraint_system
          Hgates_subset (holds_gates Γ Hcircuit)).
      + exact (satisfies_lookups_subset Γ
          (layouter_table_rows Garden.Orchard.circuit.synthesize)
          (layouter_table_rows program)
          system orchard_constraint_system
          Hlookups_subset Hrows (holds_lookups Γ Hcircuit)).
  Qed.

  Lemma witness_inputs_facts
      (Γ : Assignment.t columns RegionId.t) :
    Holds Γ ->
    interpret_facts Γ
      (layouter_facts Garden.Orchard.circuit.synthesize_witness_inputs).
  Proof.
    intros Hcircuit.
    pose proof (holds_facts Γ Hcircuit) as Hfacts.
    unfold Garden.Orchard.circuit.synthesize in Hfacts.
    apply interpret_layouter_facts_bind_right in Hfacts.
    apply interpret_layouter_facts_bind_left in Hfacts.
    exact Hfacts.
  Qed.

  Lemma witness_inputs_holds
      (Γ : Assignment.t columns RegionId.t) :
    Holds Γ ->
    circuit_holds Γ
      Garden.Orchard.circuit.synthesize_witness_inputs
      orchard_gates_only_system.
  Proof.
    intros Hcircuit.
    apply subprogram_holds_with_orchard_gates.
    - exact Hcircuit.
    - exact (witness_inputs_facts Γ Hcircuit).
  Qed.

  Lemma merkle_path_facts
      (Γ : Assignment.t columns RegionId.t) :
    Holds Γ ->
    interpret_facts Γ
      (let '(_, _, cm_old, _, _, _, _, _) :=
         layouter_value Garden.Orchard.circuit.synthesize_witness_inputs in
       layouter_facts
         (Garden.Orchard.circuit.synthesize_merkle_path
           cm_old.(Garden.Orchard.circuit.AssignedPoint.x))).
  Proof.
    intros Hcircuit.
    pose proof (holds_facts Γ Hcircuit) as Hfacts.
    unfold Garden.Orchard.circuit.synthesize in Hfacts.
    do 2 apply interpret_layouter_facts_bind_right in Hfacts.
    apply interpret_layouter_facts_bind_left in Hfacts.
    exact Hfacts.
  Qed.

  Lemma merkle_path_holds
      (Γ : Assignment.t columns RegionId.t) :
    Holds Γ ->
    circuit_holds Γ
      (let '(_, _, cm_old, _, _, _, _, _) :=
         layouter_value Garden.Orchard.circuit.synthesize_witness_inputs in
       Garden.Orchard.circuit.synthesize_merkle_path
         cm_old.(Garden.Orchard.circuit.AssignedPoint.x))
      orchard_gates_only_system.
  Proof.
    intros Hcircuit.
    apply subprogram_holds_with_orchard_gates.
    - exact Hcircuit.
    - exact (merkle_path_facts Γ Hcircuit).
  Qed.

  Lemma value_commitment_facts
      (Γ : Assignment.t columns RegionId.t) :
    Holds Γ ->
    interpret_facts Γ
      (layouter_facts Garden.Orchard.circuit.synthesize_value_commitment).
  Proof.
    intros Hcircuit.
    pose proof (holds_facts Γ Hcircuit) as Hfacts.
    unfold Garden.Orchard.circuit.synthesize in Hfacts.
    do 3 apply interpret_layouter_facts_bind_right in Hfacts.
    apply interpret_layouter_facts_bind_left in Hfacts.
    exact Hfacts.
  Qed.

  Lemma value_commitment_holds
      (Γ : Assignment.t columns RegionId.t) :
    Holds Γ ->
    circuit_holds Γ
      Garden.Orchard.circuit.synthesize_value_commitment
      orchard_gates_only_system.
  Proof.
    intros Hcircuit.
    apply subprogram_holds_with_orchard_gates.
    - exact Hcircuit.
    - exact (value_commitment_facts Γ Hcircuit).
  Qed.

  Lemma nullifier_facts
      (Γ : Assignment.t columns RegionId.t) :
    Holds Γ ->
    interpret_facts Γ
      (let '(psi_old, rho_old, cm_old, _, _, nk, _, _) :=
         layouter_value Garden.Orchard.circuit.synthesize_witness_inputs in
       layouter_facts
         (Garden.Orchard.circuit.synthesize_nullifier
           rho_old psi_old nk cm_old)).
  Proof.
    intros Hcircuit.
    pose proof (holds_facts Γ Hcircuit) as Hfacts.
    unfold Garden.Orchard.circuit.synthesize in Hfacts.
    do 4 apply interpret_layouter_facts_bind_right in Hfacts.
    apply interpret_layouter_facts_bind_left in Hfacts.
    exact Hfacts.
  Qed.

  Lemma nullifier_holds
      (Γ : Assignment.t columns RegionId.t) :
    Holds Γ ->
    circuit_holds Γ
      (let '(psi_old, rho_old, cm_old, _, _, nk, _, _) :=
         layouter_value Garden.Orchard.circuit.synthesize_witness_inputs in
       Garden.Orchard.circuit.synthesize_nullifier rho_old psi_old nk cm_old)
      orchard_gates_only_system.
  Proof.
    intros Hcircuit.
    apply subprogram_holds_with_orchard_gates.
    - exact Hcircuit.
    - exact (nullifier_facts Γ Hcircuit).
  Qed.

  Lemma note_commit_new_facts
      (Γ : Assignment.t columns RegionId.t) :
    Holds Γ ->
    interpret_facts Γ
      (let '(psi_old, rho_old, cm_old, _, _, nk, _, v_new) :=
         layouter_value Garden.Orchard.circuit.synthesize_witness_inputs in
       let rho_new :=
         layouter_value
           (Garden.Orchard.circuit.synthesize_nullifier
             rho_old psi_old nk cm_old) in
       layouter_facts
         (Garden.Orchard.circuit.synthesize_note_commit_new v_new rho_new)).
  Proof.
    intros Hcircuit.
    pose proof (holds_facts Γ Hcircuit) as Hfacts.
    unfold Garden.Orchard.circuit.synthesize in Hfacts.
    do 9 apply interpret_layouter_facts_bind_right in Hfacts.
    apply interpret_layouter_facts_bind_left in Hfacts.
    exact Hfacts.
  Qed.

  Lemma note_commit_new_holds
      (Γ : Assignment.t columns RegionId.t) :
    Holds Γ ->
    circuit_holds Γ
      (let '(psi_old, rho_old, cm_old, _, _, nk, _, v_new) :=
         layouter_value Garden.Orchard.circuit.synthesize_witness_inputs in
       let rho_new :=
         layouter_value
           (Garden.Orchard.circuit.synthesize_nullifier
             rho_old psi_old nk cm_old) in
       Garden.Orchard.circuit.synthesize_note_commit_new v_new rho_new)
      orchard_gates_only_system.
  Proof.
    intros Hcircuit.
    apply subprogram_holds_with_orchard_gates.
    - exact Hcircuit.
    - exact (note_commit_new_facts Γ Hcircuit).
  Qed.

  Lemma orchard_gate_facts
      (Γ : Assignment.t columns RegionId.t) :
    Holds Γ ->
    interpret_facts Γ
      (let '(_, _, cm_old, _, _, _, v_old, v_new) :=
         layouter_value Garden.Orchard.circuit.synthesize_witness_inputs in
       let root :=
         layouter_value
           (Garden.Orchard.circuit.synthesize_merkle_path
             cm_old.(Garden.Orchard.circuit.AssignedPoint.x)) in
       let '(magnitude, sign) :=
         layouter_value Garden.Orchard.circuit.synthesize_value_commitment in
       layouter_facts
         (Garden.Orchard.circuit.synthesize_orchard_gate
           v_old v_new magnitude sign root)).
  Proof.
    intros Hcircuit.
    pose proof (holds_facts Γ Hcircuit) as Hfacts.
    unfold Garden.Orchard.circuit.synthesize in Hfacts.
    do 10 apply interpret_layouter_facts_bind_right in Hfacts.
    apply interpret_layouter_facts_bind_left in Hfacts.
    exact Hfacts.
  Qed.

  Lemma orchard_gate_holds
      (Γ : Assignment.t columns RegionId.t) :
    Holds Γ ->
    circuit_holds Γ
      (let '(_, _, cm_old, _, _, _, v_old, v_new) :=
         layouter_value Garden.Orchard.circuit.synthesize_witness_inputs in
       let root :=
         layouter_value
           (Garden.Orchard.circuit.synthesize_merkle_path
             cm_old.(Garden.Orchard.circuit.AssignedPoint.x)) in
       let '(magnitude, sign) :=
         layouter_value Garden.Orchard.circuit.synthesize_value_commitment in
       Garden.Orchard.circuit.synthesize_orchard_gate
         v_old v_new magnitude sign root)
      orchard_gates_only_system.
  Proof.
    intros Hcircuit.
    apply subprogram_holds_with_orchard_gates.
    - exact Hcircuit.
    - exact (orchard_gate_facts Γ Hcircuit).
  Qed.

  Lemma spend_authority_facts
      (Γ : Assignment.t columns RegionId.t) :
    Holds Γ ->
    interpret_facts Γ
      (layouter_facts
        (Garden.Orchard.circuit.synthesize_spend_authority
          (layouter_value
            (Garden.Orchard.circuit.witness_non_identity_point
              (Garden.Orchard.circuit.witness_input_region
                RegionId.WitnessInput.AkP)
              "witness ak_P")))).
  Proof.
    intros Hcircuit.
    pose proof (holds_facts Γ Hcircuit) as Hfacts.
    unfold Garden.Orchard.circuit.synthesize in Hfacts.
    do 6 apply interpret_layouter_facts_bind_right in Hfacts.
    apply interpret_layouter_facts_bind_left in Hfacts.
    exact Hfacts.
  Qed.

  Lemma spend_authority_fixed_base_facts
      (Γ : Assignment.t columns RegionId.t) :
    Holds Γ ->
    interpret_facts Γ
      (layouter_facts
        Garden.Orchard.circuit.synthesize_full_fixed_base_mul_spend_auth_g).
  Proof.
    intros Hcircuit.
    pose proof (spend_authority_facts Γ Hcircuit) as Hfacts.
    unfold Garden.Orchard.circuit.synthesize_spend_authority in Hfacts.
    apply interpret_layouter_facts_bind_right in Hfacts.
    apply interpret_layouter_facts_bind_left in Hfacts.
    do 2 apply interpret_layouter_facts_in_namespace in Hfacts.
    exact Hfacts.
  Qed.

  Lemma spend_authority_holds
      (Γ : Assignment.t columns RegionId.t) :
    Holds Γ ->
    circuit_holds Γ
      (Garden.Orchard.circuit.synthesize_spend_authority
        (layouter_value
          (Garden.Orchard.circuit.witness_non_identity_point
            (Garden.Orchard.circuit.witness_input_region
              RegionId.WitnessInput.AkP)
            "witness ak_P")))
      orchard_gates_only_system.
  Proof.
    intros Hcircuit.
    apply subprogram_holds_with_orchard_gates.
    - exact Hcircuit.
    - exact (spend_authority_facts Γ Hcircuit).
  Qed.

  Lemma spend_authority_fixed_base_holds
      (Γ : Assignment.t columns RegionId.t) :
    Holds Γ ->
    circuit_holds Γ
      Garden.Orchard.circuit.synthesize_full_fixed_base_mul_spend_auth_g
      orchard_gates_only_system.
  Proof.
    intros Hcircuit.
    apply subprogram_holds_with_orchard_gates.
    - exact Hcircuit.
    - exact (spend_authority_fixed_base_facts Γ Hcircuit).
  Qed.

  Lemma holds_instance_fact
      (Γ : Assignment.t columns RegionId.t)
      (cell : Garden.Halo2.Synthesis.Cell.t columns RegionId.t)
      (instance : Instance_.t) (row : Z) :
    Holds Γ ->
    List.In (Fact.InstanceIs cell instance row)
      (layouter_facts Garden.Orchard.circuit.synthesize) ->
    eval_cell Γ cell = Γ.(Assignment.instance_) instance row.
  Proof.
    intros Hcircuit Hin.
    exact (interpret_facts_In Γ (Fact.InstanceIs cell instance row)
      (layouter_facts Garden.Orchard.circuit.synthesize)
      (holds_facts Γ Hcircuit) Hin).
  Qed.

  Lemma fixed_expression_eq
      (Γ : Assignment.t columns RegionId.t)
      (column : Fixed.t) (region : RegionId.t) (row value : Z) :
    Γ.(Assignment.fixed) column region row = value ->
    Γ ⊢ ⟦ Expression.Fixed column Rotation.cur ⟧ (region, row) =
      UnOp.from value.
  Proof.
    intros Hfixed.
    unfold eval_expression.
    cbn.
    replace (rotated_row row Rotation.cur) with row
      by (unfold rotated_row, Rotation.cur; cbn; lia).
    rewrite Hfixed.
    reflexivity.
  Qed.

  Lemma fixed_expression_eq_of_facts
      (Γ : Assignment.t columns RegionId.t)
      (facts : list (Fact.t columns RegionId.t))
      (column : Fixed.t) (region : RegionId.t) (row value : Z) :
    interpret_facts Γ facts ->
    List.In (Fact.FixedIs column region row value) facts ->
    Γ ⊢ ⟦ Expression.Fixed column Rotation.cur ⟧ (region, row) =
      UnOp.from value.
  Proof.
    intros Hfacts Hin.
    apply fixed_expression_eq.
    exact (interpret_facts_In Γ
      (Fact.FixedIs column region row value) facts Hfacts Hin).
  Qed.

  Lemma selector_nonzero_of_facts
      (Γ : Assignment.t columns RegionId.t)
      (facts : list (Fact.t columns RegionId.t))
      (selector : Selector.t) (region : RegionId.t) (row : Z) :
    interpret_facts Γ facts ->
    List.In (Fact.SelectorOn selector region row) facts ->
    Γ ⊢ ⟦ selector ⟧ (region, row) <> 0.
  Proof.
    intros Hfacts Hin.
    apply (enabled_nonzero Γ selector region row).
    exact (interpret_facts_In Γ
      (Fact.SelectorOn selector region row) facts Hfacts Hin).
  Qed.

  Lemma assign_full_window_witnesses_selector_fact
      (region : RegionId.t) (offset : Z) (count i : nat) :
    (i < count)%nat ->
    List.In
      (Fact.SelectorOn Selector.QMulFixedFull region
        (offset + Z.of_nat i))
      (region_facts region
        (Garden.Orchard.circuit.assign_full_window_witnesses offset count)).
  Proof.
    revert offset i.
    induction count as [| count IH]; intros offset i Hi.
    - lia.
    - destruct i as [| i].
      + cbn [Garden.Orchard.circuit.assign_full_window_witnesses
          region_facts].
        left. f_equal. lia.
      + cbn [Garden.Orchard.circuit.assign_full_window_witnesses
          region_facts].
        right.
        replace (offset + Z.of_nat (S i)) with
          (offset + 1 + Z.of_nat i) by lia.
        apply IH. lia.
  Qed.

  Lemma assign_fixed_row_fixed_fact
      (region : RegionId.t) (offset : Z)
      (row : Garden.Orchard.circuit.fixed_base_row)
      (column : Fixed.t) (annotation : string) (value : Z) :
    List.In (column, annotation, value) row ->
    List.In (Fact.FixedIs column region offset value)
      (region_facts region
        (Garden.Orchard.circuit.assign_fixed_row offset row)).
  Proof.
    induction row as [| entry row IH]; intros Hin.
    - contradiction.
    - destruct entry as [entry value'].
      destruct entry as [column' annotation'].
      cbn [Garden.Orchard.circuit.assign_fixed_row region_facts].
      destruct Hin as [Hin | Hin].
      + inversion Hin. subst.
        left. reflexivity.
      + right. apply IH. exact Hin.
  Qed.

  Lemma assign_fixed_rows_with_selector_fixed_fact
      (region : RegionId.t) (selector : Selector.t) (offset : Z)
      (rows : list Garden.Orchard.circuit.fixed_base_row)
      (i : nat) (row : Garden.Orchard.circuit.fixed_base_row)
      (column : Fixed.t) (annotation : string) (value : Z) :
    List.nth_error rows i = Some row ->
    List.In (column, annotation, value) row ->
    List.In (Fact.FixedIs column region (offset + Z.of_nat i) value)
      (region_facts region
        (Garden.Orchard.circuit.assign_fixed_rows_with_selector
          selector offset rows)).
  Proof.
    revert offset i row.
    induction rows as [| row0 rows IH]; intros offset i row Hnth Hin.
    - destruct i; discriminate.
    - destruct i as [| i].
      + cbn in Hnth. inversion Hnth. subst row0.
        cbn [Garden.Orchard.circuit.assign_fixed_rows_with_selector
          region_facts].
        cbn.
        right.
        apply List.in_or_app.
        left.
        assert (Hoffset : offset + 0 = offset) by lia.
        rewrite Hoffset.
        apply (assign_fixed_row_fixed_fact region offset row
          column annotation value).
        exact Hin.
      + cbn in Hnth.
        replace (offset + Z.of_nat (S i)) with
          (offset + 1 + Z.of_nat i) by lia.
        cbn [Garden.Orchard.circuit.assign_fixed_rows_with_selector
          region_facts].
        cbn.
        right.
        apply List.in_or_app.
        right.
        apply IH with (row := row).
        * exact Hnth.
        * exact Hin.
  Qed.

  Lemma read_public_instance_eq_cell
      (Γ : Assignment.t columns RegionId.t)
      (cell : Garden.Halo2.Synthesis.Cell.t columns RegionId.t)
      (row : Z) :
    eval_cell Γ cell =
      Γ.(Assignment.instance_) Instance_.Primary row ->
    read_public_instance Γ row = UnOp.from (eval_cell Γ cell).
  Proof.
    intros Hinstance.
    unfold read_public_instance.
    change (eval_expression Γ
      (RegionId.OrchardCircuitChecks, row)
      (Expression.Instance_ Instance_.Primary Rotation.cur) =
      UnOp.from (eval_cell Γ cell)).
    unfold eval_expression, rotated_row, Rotation.cur.
    cbn.
    rewrite Z.add_0_r.
    rewrite <- Hinstance.
    reflexivity.
  Qed.

  Lemma read_public_instance_eq_of_cell
      (Γ : Assignment.t columns RegionId.t)
      (cell : Garden.Halo2.Synthesis.Cell.t columns RegionId.t)
      (row value : Z) :
    eval_cell Γ cell =
      Γ.(Assignment.instance_) Instance_.Primary row ->
    UnOp.from (eval_cell Γ cell) = value ->
    read_public_instance Γ row = value.
  Proof.
    intros Hinstance Hvalue.
    rewrite (read_public_instance_eq_cell Γ cell row Hinstance).
    exact Hvalue.
  Qed.

  Lemma eval_advice_cur_cell
      (Γ : Assignment.t columns RegionId.t)
      (region : RegionId.t) (column : Advice.t) (row : Z) :
    Γ ⊢ ⟦ Expression.Advice column Rotation.cur ⟧ (region, row) =
      UnOp.from
        (eval_cell Γ (Garden.Halo2.Synthesis.Cell.advice region column row)).
  Proof.
    change (eval_expression Γ (region, row)
      (Expression.Advice column Rotation.cur) =
      UnOp.from
        (eval_cell Γ (Garden.Halo2.Synthesis.Cell.advice region column row))).
    unfold eval_expression, eval_cell, rotated_row, Rotation.cur.
    cbn.
    rewrite Z.add_0_r.
    reflexivity.
  Qed.

  Lemma nf_old_public_instance_source
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ) :
    exists cell : Garden.Halo2.Synthesis.Cell.t columns RegionId.t,
      read_public_instance Γ Garden.Orchard.circuit.NF_OLD =
        UnOp.from (eval_cell Γ cell).
  Proof.
    destruct Hcircuit as [Hfacts HSatisfies].
    destruct HSatisfies as [Hgates Hlookups].
    unfold Garden.Orchard.circuit.synthesize in Hfacts.
    do 5 apply interpret_layouter_facts_bind_right in Hfacts.
    apply interpret_layouter_facts_bind_left in Hfacts.
    cbn [layouter_facts interpret_facts interpret_fact eval_cell] in Hfacts.
    destruct Hfacts as [Hinstance _].
    eexists.
    apply read_public_instance_eq_cell.
    exact Hinstance.
  Qed.

  Lemma cv_net_x_public_instance_source
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ) :
    exists cell : Garden.Halo2.Synthesis.Cell.t columns RegionId.t,
      read_public_instance Γ Garden.Orchard.circuit.CV_NET_X =
        UnOp.from (eval_cell Γ cell).
  Proof.
    destruct Hcircuit as [Hfacts HSatisfies].
    destruct HSatisfies as [Hgates Hlookups].
    unfold Garden.Orchard.circuit.synthesize in Hfacts.
    do 3 apply interpret_layouter_facts_bind_right in Hfacts.
    apply interpret_layouter_facts_bind_left in Hfacts.
    unfold Garden.Orchard.circuit.synthesize_value_commitment in Hfacts.
    do 5 apply interpret_layouter_facts_bind_right in Hfacts.
    apply interpret_layouter_facts_bind_left in Hfacts.
    cbn [layouter_facts interpret_facts interpret_fact eval_cell] in Hfacts.
    destruct Hfacts as [Hinstance _].
    eexists.
    apply read_public_instance_eq_cell.
    exact Hinstance.
  Qed.

  Lemma cv_net_y_public_instance_source
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ) :
    exists cell : Garden.Halo2.Synthesis.Cell.t columns RegionId.t,
      read_public_instance Γ Garden.Orchard.circuit.CV_NET_Y =
        UnOp.from (eval_cell Γ cell).
  Proof.
    destruct Hcircuit as [Hfacts HSatisfies].
    destruct HSatisfies as [Hgates Hlookups].
    unfold Garden.Orchard.circuit.synthesize in Hfacts.
    do 3 apply interpret_layouter_facts_bind_right in Hfacts.
    apply interpret_layouter_facts_bind_left in Hfacts.
    unfold Garden.Orchard.circuit.synthesize_value_commitment in Hfacts.
    do 6 apply interpret_layouter_facts_bind_right in Hfacts.
    apply interpret_layouter_facts_bind_left in Hfacts.
    cbn [layouter_facts interpret_facts interpret_fact eval_cell] in Hfacts.
    destruct Hfacts as [Hinstance _].
    eexists.
    apply read_public_instance_eq_cell.
    exact Hinstance.
  Qed.

  Lemma rk_x_public_instance_source
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ) :
    exists cell : Garden.Halo2.Synthesis.Cell.t columns RegionId.t,
      read_public_instance Γ Garden.Orchard.circuit.RK_X =
        UnOp.from (eval_cell Γ cell).
  Proof.
    destruct Hcircuit as [Hfacts HSatisfies].
    destruct HSatisfies as [Hgates Hlookups].
    unfold Garden.Orchard.circuit.synthesize in Hfacts.
    do 6 apply interpret_layouter_facts_bind_right in Hfacts.
    apply interpret_layouter_facts_bind_left in Hfacts.
    unfold Garden.Orchard.circuit.synthesize_spend_authority in Hfacts.
    do 3 apply interpret_layouter_facts_bind_right in Hfacts.
    apply interpret_layouter_facts_bind_left in Hfacts.
    cbn [layouter_facts interpret_facts interpret_fact eval_cell] in Hfacts.
    destruct Hfacts as [Hinstance _].
    eexists.
    apply read_public_instance_eq_cell.
    exact Hinstance.
  Qed.

  Lemma rk_y_public_instance_source
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ) :
    exists cell : Garden.Halo2.Synthesis.Cell.t columns RegionId.t,
      read_public_instance Γ Garden.Orchard.circuit.RK_Y =
        UnOp.from (eval_cell Γ cell).
  Proof.
    destruct Hcircuit as [Hfacts HSatisfies].
    destruct HSatisfies as [Hgates Hlookups].
    unfold Garden.Orchard.circuit.synthesize in Hfacts.
    do 6 apply interpret_layouter_facts_bind_right in Hfacts.
    apply interpret_layouter_facts_bind_left in Hfacts.
    unfold Garden.Orchard.circuit.synthesize_spend_authority in Hfacts.
    do 4 apply interpret_layouter_facts_bind_right in Hfacts.
    apply interpret_layouter_facts_bind_left in Hfacts.
    cbn [layouter_facts interpret_facts interpret_fact eval_cell] in Hfacts.
    destruct Hfacts as [Hinstance _].
    eexists.
    apply read_public_instance_eq_cell.
    exact Hinstance.
  Qed.

  Lemma cmx_public_instance_source
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ) :
    exists cell : Garden.Halo2.Synthesis.Cell.t columns RegionId.t,
      read_public_instance Γ Garden.Orchard.circuit.CMX =
        UnOp.from (eval_cell Γ cell).
  Proof.
    destruct Hcircuit as [Hfacts HSatisfies].
    destruct HSatisfies as [Hgates Hlookups].
    unfold Garden.Orchard.circuit.synthesize in Hfacts.
    do 9 apply interpret_layouter_facts_bind_right in Hfacts.
    apply interpret_layouter_facts_bind_left in Hfacts.
    unfold Garden.Orchard.circuit.synthesize_note_commit_new in Hfacts.
    do 5 apply interpret_layouter_facts_bind_right in Hfacts.
    apply interpret_layouter_facts_bind_left in Hfacts.
    cbn [layouter_facts interpret_facts interpret_fact eval_cell] in Hfacts.
    destruct Hfacts as [Hinstance _].
    eexists.
    apply read_public_instance_eq_cell.
    exact Hinstance.
  Qed.

  Lemma anchor_public_instance_source
      (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ) :
    exists cell : Garden.Halo2.Synthesis.Cell.t columns RegionId.t,
      read_public_instance Γ Garden.Orchard.circuit.ANCHOR =
        UnOp.from (eval_cell Γ cell).
  Proof.
    destruct Hcircuit as [Hfacts HSatisfies].
    destruct HSatisfies as [Hgates Hlookups].
    unfold Garden.Orchard.circuit.synthesize in Hfacts.
    do 10 apply interpret_layouter_facts_bind_right in Hfacts.
    apply interpret_layouter_facts_bind_left in Hfacts.
    unfold Garden.Orchard.circuit.synthesize_orchard_gate in Hfacts.
    apply interpret_layouter_facts_add_region in Hfacts.
    do 5 apply interpret_region_facts_bind_right in Hfacts.
    apply interpret_region_facts_bind_left in Hfacts.
    cbn [region_facts interpret_facts interpret_fact eval_cell] in Hfacts.
    destruct Hfacts as [Hcopy _].
    eexists.
    apply read_public_instance_eq_cell.
    cbn [eval_cell Garden.Halo2.Synthesis.Cell.instance] in Hcopy.
    exact Hcopy.
  Qed.

End OrchardActionFacts.
