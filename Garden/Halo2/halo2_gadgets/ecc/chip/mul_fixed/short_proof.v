Require Import Garden.Halo2.main.
Require Import Garden.Halo2.proof.
Require Garden.Halo2.halo2_gadgets.ecc.chip.mul_fixed.short.
Require Import Garden.Field.Field.
Require Import Garden.Orchard.columns.
Require Import Garden.Plonky3.M.

#[local] Existing Instance Primes.PallasPIsPrime.

Global Open Scope Z_scope.

Module ShortFixedBaseMul.
  Record t : Set := {
    y_a : Z;
  }.

  Definition output {p : Z} `{Prime p}
      (y_p sign : Z)
      : t := {|
    y_a := sign *F y_p;
  |}.

  (* The signed ordinate [y_a] on A3 is uniquely determined by the magnitude
     [y_p] on A1 and the witnessed [sign] on A4, via the "negation_check"
     constraint of [short_fixed_base_mul_gate]. *)
  Theorem deterministic
      {RegionId : Set} (Γ : Assignment.t columns RegionId) (region : RegionId) (row : Z)
      (Hselector : Γ ⊢ ⟦ Selector.QMulFixedShort ⟧ (region, row) <> 0)
      (Hgate :
        Γ ⊢ ⟦ Garden.Halo2.halo2_gadgets.ecc.chip.mul_fixed.short
            .short_fixed_base_mul_gate ⟧ (region, row)) :
      {|
        y_a := Γ ⊢ ⟦ Expression.Advice Advice.A3 Rotation.cur ⟧ (region, row);
      |} =
        output
          (Γ ⊢ ⟦ Expression.Advice Advice.A1 Rotation.cur ⟧ (region, row))
          (Γ ⊢ ⟦ Expression.Advice Advice.A4 Rotation.cur ⟧ (region, row)).
  Proof.
    unfold output.
    with_strategy opaque [BinOp.add BinOp.mul BinOp.sub UnOp.from] cbn in *.
    destruct Hgate as (_ & _ & _ & h4).
    specialize (h4 Hselector).
    now rewrite h4.
  Qed.

  (* Chip-level determinism (admitted): [short.synthesize] enables
     [QMulFixedShort] at offset 0 of region [EccMulFixedShort], so
     [circuit_holds] discharges the [Hselector]/[Hgate] of [deterministic].
     See [CompleteAddition.synthesize_correct] (add_proof.v) for the proved
     template. *)
  Theorem synthesize_correct
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit :
        circuit_holds Γ
          Garden.Halo2.halo2_gadgets.ecc.chip.mul_fixed.short.synthesize
          (𝓒.run_unit Garden.Halo2.halo2_gadgets.ecc.chip.mul_fixed.short.configure
            ConstraintSystem.empty)) :
      {|
        y_a := Γ ⊢ ⟦ Expression.Advice Advice.A3 Rotation.cur ⟧
          (RegionId.GadgetLocal RegionId.GadgetLocal.EccMulFixedShort, 0);
      |} =
        output
          (Γ ⊢ ⟦ Expression.Advice Advice.A1 Rotation.cur ⟧
            (RegionId.GadgetLocal RegionId.GadgetLocal.EccMulFixedShort, 0))
          (Γ ⊢ ⟦ Expression.Advice Advice.A4 Rotation.cur ⟧
            (RegionId.GadgetLocal RegionId.GadgetLocal.EccMulFixedShort, 0)).
  Proof.
    destruct Hcircuit as [Hfacts HSatisfies].
    destruct HSatisfies as [Hgates Hlookups].
    apply deterministic.
    - (* Selector enabled by [synthesize]. *)
      cbn in Hfacts.
      destruct Hfacts as [Hselector Htrivial].
      exact (enabled_nonzero Γ Selector.QMulFixedShort
        (RegionId.GadgetLocal RegionId.GadgetLocal.EccMulFixedShort) 0 Hselector).
    - (* The short fixed-base mul gate holds, from gate satisfaction. *)
      assert (Hsystem :
        (𝓒.run_unit Garden.Halo2.halo2_gadgets.ecc.chip.mul_fixed.short.configure
          ConstraintSystem.empty).(ConstraintSystem.gates)
        = [Garden.Halo2.halo2_gadgets.ecc.chip.mul_fixed.short.short_fixed_base_mul_gate])
        by reflexivity.
      exact (satisfies_gates_single Γ _
        Garden.Halo2.halo2_gadgets.ecc.chip.mul_fixed.short.short_fixed_base_mul_gate
        (RegionId.GadgetLocal RegionId.GadgetLocal.EccMulFixedShort) 0
        Hsystem Hgates).
  Qed.
End ShortFixedBaseMul.
