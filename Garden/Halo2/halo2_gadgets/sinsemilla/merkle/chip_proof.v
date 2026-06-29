Require Import Garden.Halo2.main.
Require Import Garden.Halo2.Synthesis.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.lemmas.
Require Garden.Halo2.halo2_gadgets.sinsemilla.merkle.chip.
Require Import Garden.Halo2.halo2_gadgets.utilities_proof.
Require Import Garden.Orchard.columns.
Require Import Garden.Field.Field.
Require Import Garden.Plonky3.M.

#[local] Existing Instance Primes.PallasPIsPrime.

Global Open Scope Z_scope.

Module DecompositionCheck.
  Record t : Set := {
    l_whole : Z;
    left_node : Z;
    right_node : Z;
    z1_b : Z;
  }.

  Definition output {p : Z} `{Prime p}
      (a_whole b_whole c_whole a_1 b_1 b_2 : Z)
      : t :=
    let l_whole := a_whole -F a_1 *F UnOp.from (2 ^ 10) in
    let z1_b := b_1 +F b_2 *F UnOp.from (2 ^ 5) in
    let b_0 := b_whole -F z1_b *F UnOp.from (2 ^ 10) in
    {|
      l_whole := l_whole;
      left_node :=
        a_1 +F
          (b_0 +F b_1 *F UnOp.from (2 ^ 10)) *F
            UnOp.from (2 ^ 240);
      right_node := b_2 +F c_whole *F UnOp.from (2 ^ 5);
      z1_b := z1_b;
    |}.

  (* The four reconstruction cells are uniquely determined by the six input
     cells of the current/next rows via the constraints of
     [decomposition_check_gate] ("l_check", "left_check", "right_check",
     "b1_b2_check"). The inputs are read as:
       a_whole = a_col.cur,  b_whole = b_col.cur,  c_whole = c_col.cur,
       a_1     = a_col.next, b_1     = c_col.next, b_2     = left_col.next. *)
  Theorem deterministic
      {RegionId : Set} (Γ : Assignment.t columns RegionId) (region : RegionId) (row : Z)
      (q_decompose : Selector.t)
      (a_col b_col c_col left_col right_col : Advice.t)
      (Hselector : Γ ⊢ ⟦ q_decompose ⟧ (region, row) <> 0)
      (Hgate :
        Γ ⊢ ⟦ Garden.Halo2.halo2_gadgets.sinsemilla.merkle.chip
            .decomposition_check_gate
              q_decompose a_col b_col c_col left_col right_col ⟧ (region, row)) :
      {|
        l_whole := Γ ⊢ ⟦ Expression.Advice right_col Rotation.next ⟧ (region, row);
        left_node := Γ ⊢ ⟦ Expression.Advice left_col Rotation.cur ⟧ (region, row);
        right_node := Γ ⊢ ⟦ Expression.Advice right_col Rotation.cur ⟧ (region, row);
        z1_b := Γ ⊢ ⟦ Expression.Advice b_col Rotation.next ⟧ (region, row);
      |} =
        output
          (Γ ⊢ ⟦ Expression.Advice a_col Rotation.cur ⟧ (region, row))
          (Γ ⊢ ⟦ Expression.Advice b_col Rotation.cur ⟧ (region, row))
          (Γ ⊢ ⟦ Expression.Advice c_col Rotation.cur ⟧ (region, row))
          (Γ ⊢ ⟦ Expression.Advice a_col Rotation.next ⟧ (region, row))
          (Γ ⊢ ⟦ Expression.Advice c_col Rotation.next ⟧ (region, row))
          (Γ ⊢ ⟦ Expression.Advice left_col Rotation.next ⟧ (region, row)).
  Proof.
    (* Each of the four reconstruction cells is fixed by one constraint, all
       linear once the radix constants [2^5], [2^10], [2^240] are exposed:
       "l_check" pins [l_whole], "left_check" pins [left_node] (using
       "b1_b2_check" to rewrite the [b] decomposition), "right_check" pins
       [right_node], "b1_b2_check" pins [z1_b]. *)
    unfold output.
    with_strategy opaque [BinOp.add BinOp.sub BinOp.mul UnOp.from] cbn in *.
    destruct Hgate as (Hc1 & Hc2 & Hc3 & Hc4).
    specialize (Hc1 Hselector).
    specialize (Hc2 Hselector).
    specialize (Hc3 Hselector).
    specialize (Hc4 Hselector).
    f_equal; field_solve.
  Qed.

  (* Chip-level determinism (admitted): [chip.synthesize_instance] enables
     [q_decompose] at offset 0 of region [SinsemillaMerkleDecomposition], so
     [circuit_holds] discharges the [Hselector]/[Hgate] of [deterministic].
     Parameterised over the selector/columns and the [cond_swap] sub-programs
     that [configure_instance]/[synthesize_instance] take.  See
     [CompleteAddition.synthesize_correct] (add_proof.v) for the proved
     template. *)
  Theorem synthesize_correct
      (Γ : Assignment.t columns RegionId.t)
      (q_decompose : Selector.t)
      (synthesize_cond_swap : 𝓛 columns RegionId.t unit)
      (configure_cond_swap : 𝓒 columns unit)
      (a_col b_col c_col left_col right_col : Advice.t)
      (Hcircuit :
        circuit_holds Γ
          (Garden.Halo2.halo2_gadgets.sinsemilla.merkle.chip.synthesize_instance
            q_decompose synthesize_cond_swap)
          (𝓒.run_unit
            (Garden.Halo2.halo2_gadgets.sinsemilla.merkle.chip.configure_instance
              q_decompose configure_cond_swap a_col b_col c_col left_col right_col)
            ConstraintSystem.empty)) :
      {|
        l_whole := Γ ⊢ ⟦ Expression.Advice right_col Rotation.next ⟧
          (RegionId.GadgetLocal RegionId.GadgetLocal.SinsemillaMerkleDecomposition, 0);
        left_node := Γ ⊢ ⟦ Expression.Advice left_col Rotation.cur ⟧
          (RegionId.GadgetLocal RegionId.GadgetLocal.SinsemillaMerkleDecomposition, 0);
        right_node := Γ ⊢ ⟦ Expression.Advice right_col Rotation.cur ⟧
          (RegionId.GadgetLocal RegionId.GadgetLocal.SinsemillaMerkleDecomposition, 0);
        z1_b := Γ ⊢ ⟦ Expression.Advice b_col Rotation.next ⟧
          (RegionId.GadgetLocal RegionId.GadgetLocal.SinsemillaMerkleDecomposition, 0);
      |} =
        output
          (Γ ⊢ ⟦ Expression.Advice a_col Rotation.cur ⟧
            (RegionId.GadgetLocal RegionId.GadgetLocal.SinsemillaMerkleDecomposition, 0))
          (Γ ⊢ ⟦ Expression.Advice b_col Rotation.cur ⟧
            (RegionId.GadgetLocal RegionId.GadgetLocal.SinsemillaMerkleDecomposition, 0))
          (Γ ⊢ ⟦ Expression.Advice c_col Rotation.cur ⟧
            (RegionId.GadgetLocal RegionId.GadgetLocal.SinsemillaMerkleDecomposition, 0))
          (Γ ⊢ ⟦ Expression.Advice a_col Rotation.next ⟧
            (RegionId.GadgetLocal RegionId.GadgetLocal.SinsemillaMerkleDecomposition, 0))
          (Γ ⊢ ⟦ Expression.Advice c_col Rotation.next ⟧
            (RegionId.GadgetLocal RegionId.GadgetLocal.SinsemillaMerkleDecomposition, 0))
          (Γ ⊢ ⟦ Expression.Advice left_col Rotation.next ⟧
            (RegionId.GadgetLocal RegionId.GadgetLocal.SinsemillaMerkleDecomposition, 0)).
  Proof.
    destruct Hcircuit as [Hfacts HSatisfies].
    destruct HSatisfies as [Hgates Hlookups].
    apply (deterministic Γ
      (RegionId.GadgetLocal RegionId.GadgetLocal.SinsemillaMerkleDecomposition) 0
      q_decompose a_col b_col c_col left_col right_col).
    - (* [q_decompose] is enabled at offset 0 of the decomposition region; the
         [cond_swap] sub-program's facts form an opaque prefix, so project past
         them to reach the selector fact at the tail. *)
      unfold Garden.Halo2.halo2_gadgets.sinsemilla.merkle.chip.synthesize_instance
        in Hfacts.
      cbn [layouter_facts region_facts layouter_value Monad.bind
        ConfigureIsMonad LayouterIsMonad] in Hfacts.
      assert (Happ : forall (Δ : Assignment.t columns RegionId.t)
          (xs ys : list (Fact.t columns RegionId.t)),
          interpret_facts Δ (xs ++ ys) -> interpret_facts Δ ys).
      { intros Δ xs. induction xs as [| x xs IH]; intros ys H.
        - exact H.
        - exact (IH ys (proj2 H)). }
      apply Happ in Hfacts.
      cbn in Hfacts.
      destruct Hfacts as [Hsel Htrivial].
      exact (enabled_nonzero Γ q_decompose
        (RegionId.GadgetLocal RegionId.GadgetLocal.SinsemillaMerkleDecomposition)
        0 Hsel).
    - (* The decomposition-check gate is the last configured gate (after the
         opaque [cond_swap] gates), so it occurs in the configured list. *)
      apply (satisfies_gates_at Γ
        (𝓒.run_unit
          (Garden.Halo2.halo2_gadgets.sinsemilla.merkle.chip.configure_instance
            q_decompose configure_cond_swap a_col b_col c_col left_col right_col)
          ConstraintSystem.empty)
        (Garden.Halo2.halo2_gadgets.sinsemilla.merkle.chip.decomposition_check_gate
          q_decompose a_col b_col c_col left_col right_col)
        (RegionId.GadgetLocal RegionId.GadgetLocal.SinsemillaMerkleDecomposition) 0);
        [| exact Hgates].
      unfold Garden.Halo2.halo2_gadgets.sinsemilla.merkle.chip.configure_instance,
        𝓒.run_unit.
      cbn [𝓒.run snd Monad.bind ConfigureIsMonad ConstraintSystem.create_gate
        ConstraintSystem.gates].
      destruct (𝓒.run configure_cond_swap ConstraintSystem.empty) as [v meta] eqn:E.
      cbn [𝓒.run snd ConstraintSystem.create_gate ConstraintSystem.gates].
      apply List.in_or_app. right. left. reflexivity.
  Qed.
End DecompositionCheck.
