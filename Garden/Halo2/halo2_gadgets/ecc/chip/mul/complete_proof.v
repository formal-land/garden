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
      (ρ : Evaluation.t columns)
      (Hselector : ⟦ Selector.QMulDecomposeVar ⟧ ρ <> 0)
      (Hgate :
        ⟦ Garden.Halo2.halo2_gadgets.ecc.chip.mul.complete
            .decompose_scalar_complete_gate ⟧ ρ) :
      IsBool.t
        (k
          (output
            (⟦ Expression.Advice Advice.A9 Rotation.prev ⟧ ρ)
            (⟦ Expression.Advice Advice.A9 Rotation.next ⟧ ρ))).
  Proof.
  Admitted.
End DecomposeScalarComplete.
