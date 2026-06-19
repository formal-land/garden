Require Import Garden.Halo2.main.
Require Import Garden.Halo2.proof.
Require Garden.Halo2.halo2_gadgets.ecc.chip.mul.complete.
Require Import Garden.Field.Field.
Require Import Garden.Orchard.columns.
Require Import Garden.Plonky3.M.

#[local] Existing Instance Primes.PallasPIsPrime.

Global Open Scope Z_scope.

Module DecomposeScalarComplete.
  Record t : Set := {
    k : Z;
  }.

  Definition output {p : Z} `{Prime p}
      (z_prev z_next : Z)
      : t := {|
    k := z_next -F UnOp.from 2 *F z_prev;
  |}.

  (* Soundness: the decomposed bit [k = z_next - 2*z_prev] is boolean (the
     [bool_check] constraint of [decompose_scalar_complete_gate]). [k] is an
     intermediate scalar, not a stored next-row cell, so there is no
     determinism statement. *)
  Theorem sound
      {RegionId : Set} (Γ : Assignment.t columns RegionId) (region : RegionId) (row : Z)
      (Hselector : Γ ⊢ ⟦ Selector.QMulDecomposeVar ⟧ (region, row) <> 0)
      (Hgate :
        Γ ⊢ ⟦ Garden.Halo2.halo2_gadgets.ecc.chip.mul.complete
            .decompose_scalar_complete_gate ⟧ (region, row)) :
      IsBool.t
        (output
          (Γ ⊢ ⟦ Expression.Advice Advice.A9 Rotation.prev ⟧ (region, row))
          (Γ ⊢ ⟦ Expression.Advice Advice.A9 Rotation.next ⟧ (region, row))).(k).
  Proof.
    unfold output; cbn.
    destruct Hgate as (hbool & _).
    exact (hbool Hselector).
  Qed.
End DecomposeScalarComplete.
