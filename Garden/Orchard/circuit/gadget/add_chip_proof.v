Require Import Garden.Halo2.main.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.lemmas.
Require Garden.Orchard.circuit.gadget.add_chip.
Require Import Garden.Orchard.columns.
Require Import Garden.Field.Field.
Require Import Garden.Plonky3.M.

#[local] Existing Instance Primes.PallasPIsPrime.

Global Open Scope Z_scope.

Module Addition.
  Record t : Set := {
    c : Z;
  }.

  Definition output {p : Z} `{Prime p}
      (a b : Z)
      : t := {|
    c := a +F b;
  |}.

  Theorem deterministic
      {RegionId : Set} (Γ : Assignment.t columns RegionId)
      (region : RegionId) (row : Z)
      (Hselector : Γ ⊢ ⟦ Selector.QAdd ⟧ (region, row) <> 0)
      (Hgate :
        Γ ⊢ ⟦ Garden.Orchard.circuit.gadget.add_chip.addition_gate ⟧
          (region, row)) :
      {|
        c := Γ ⊢ ⟦ Expression.Advice Advice.A6 Rotation.cur ⟧ (region, row);
      |} =
        output
          (Γ ⊢ ⟦ Expression.Advice Advice.A7 Rotation.cur ⟧ (region, row))
          (Γ ⊢ ⟦ Expression.Advice Advice.A8 Rotation.cur ⟧ (region, row)).
  Proof.
    unfold output.
    cbn [Garden.Orchard.circuit.gadget.add_chip.addition_gate
      Gate.constraints Constraints.with_selector eval_gate eval_constraints
      eval_named_constraint eval_constraint eval_expression] in Hgate.
    cbn.
    f_equal.
    symmetry.
    exact (Hgate Hselector).
  Qed.

  Theorem synthesize_correct
      (Γ : Assignment.t columns RegionId.t)
      (a b c_value : Z)
      (Hcircuit :
        circuit_holds Γ
          (Garden.Orchard.circuit.gadget.add_chip.synthesize a b c_value)
          (𝓒.run_unit
            Garden.Orchard.circuit.gadget.add_chip.configure
            ConstraintSystem.empty)) :
      {|
        c := Γ ⊢ ⟦ Expression.Advice Advice.A6 Rotation.cur ⟧
          (RegionId.GadgetLocal RegionId.GadgetLocal.AddChip, 0);
      |} =
        output
          (Γ ⊢ ⟦ Expression.Advice Advice.A7 Rotation.cur ⟧
            (RegionId.GadgetLocal RegionId.GadgetLocal.AddChip, 0))
          (Γ ⊢ ⟦ Expression.Advice Advice.A8 Rotation.cur ⟧
            (RegionId.GadgetLocal RegionId.GadgetLocal.AddChip, 0)).
  Proof.
    destruct Hcircuit as [Hfacts HSatisfies].
    destruct HSatisfies as [Hgates Hlookups].
    apply deterministic.
    - cbn in Hfacts.
      destruct Hfacts as [Hselector _].
      exact (enabled_nonzero Γ Selector.QAdd
        (RegionId.GadgetLocal RegionId.GadgetLocal.AddChip) 0 Hselector).
    - apply (satisfies_gates_at Γ
        (𝓒.run_unit
          Garden.Orchard.circuit.gadget.add_chip.configure
          ConstraintSystem.empty)
        Garden.Orchard.circuit.gadget.add_chip.addition_gate
        (RegionId.GadgetLocal RegionId.GadgetLocal.AddChip) 0);
        [cbn; left; reflexivity | exact Hgates].
  Qed.
End Addition.
