Require Import Garden.Halo2.main.
Require Import Garden.Halo2.proof.
Require Garden.Halo2.halo2_gadgets.ecc.chip.witness_point.
Require Import Garden.Orchard.columns.
Require Import Garden.Plonky3.M.

#[local] Existing Instance Primes.PallasPIsPrime.

Global Open Scope Z_scope.

Module WitnessPoint.
  (* [witness_point] is a validity check, not a state transition, so its
     property is soundness rather than determinism: the witnessed point
     [(x, y)] on A0/A1 is either the identity [(0, 0)] or lies on the curve
     [y^2 = x^3 + b] (i.e. [curve_eqn] evaluates to zero). *)
  Theorem sound
      (ρ : Evaluation.t columns)
      (Hselector : ⟦ Selector.QWitnessPoint ⟧ ρ <> 0)
      (Hgate :
        ⟦ Garden.Halo2.halo2_gadgets.ecc.chip.witness_point
            .witness_point_gate ⟧ ρ) :
      (⟦ Expression.Advice Advice.A0 Rotation.cur ⟧ ρ = 0 /\
       ⟦ Expression.Advice Advice.A1 Rotation.cur ⟧ ρ = 0) \/
      ⟦ Garden.Halo2.halo2_gadgets.ecc.chip.witness_point
          .curve_eqn Advice.A0 Advice.A1 ⟧ ρ = 0.
  Proof.
    cbn in *.
    destruct Hgate as (hc1 & hc2).
    specialize (hc1 Hselector).
    specialize (hc2 Hselector).
    destruct hc1 as [hx | hcurve].
    - destruct hc2 as [hy | hcurve].
      + left. split; assumption.
      + right. assumption.
    - right. assumption.
  Qed.

  (* The non-identity variant forbids the identity case, so the witnessed point
     must lie on the curve. *)
  Theorem sound_non_identity
      (ρ : Evaluation.t columns)
      (Hselector : ⟦ Selector.QWitnessPointNonId ⟧ ρ <> 0)
      (Hgate :
        ⟦ Garden.Halo2.halo2_gadgets.ecc.chip.witness_point
            .witness_non_identity_point_gate ⟧ ρ) :
      ⟦ Garden.Halo2.halo2_gadgets.ecc.chip.witness_point
          .curve_eqn Advice.A0 Advice.A1 ⟧ ρ = 0.
  Proof.
    cbn in *.
    exact (Hgate Hselector).
  Qed.
End WitnessPoint.
