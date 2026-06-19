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
      (Γ : Assignment.t columns) (row : Z)
      (Hselector : Γ ⊢ ⟦ Selector.QWitnessPoint ⟧ row <> 0)
      (Hgate :
        Γ ⊢ ⟦ Garden.Halo2.halo2_gadgets.ecc.chip.witness_point
            .witness_point_gate ⟧ row) :
      (Γ ⊢ ⟦ Expression.Advice Advice.A0 Rotation.cur ⟧ row = 0 /\
       Γ ⊢ ⟦ Expression.Advice Advice.A1 Rotation.cur ⟧ row = 0) \/
      Γ ⊢ ⟦ Garden.Halo2.halo2_gadgets.ecc.chip.witness_point
          .curve_eqn Advice.A0 Advice.A1 ⟧ row = 0.
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
      (Γ : Assignment.t columns) (row : Z)
      (Hselector : Γ ⊢ ⟦ Selector.QWitnessPointNonId ⟧ row <> 0)
      (Hgate :
        Γ ⊢ ⟦ Garden.Halo2.halo2_gadgets.ecc.chip.witness_point
            .witness_non_identity_point_gate ⟧ row) :
      Γ ⊢ ⟦ Garden.Halo2.halo2_gadgets.ecc.chip.witness_point
          .curve_eqn Advice.A0 Advice.A1 ⟧ row = 0.
  Proof.
    cbn in *.
    exact (Hgate Hselector).
  Qed.
End WitnessPoint.
