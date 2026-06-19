Require Import Garden.Halo2.main.
Require Import Garden.Halo2.proof.
Require Garden.Halo2.halo2_gadgets.ecc.chip.mul.
Require Import Garden.Field.Field.
Require Import Garden.Orchard.columns.
Require Import Garden.Plonky3.M.

#[local] Existing Instance Primes.PallasPIsPrime.

Global Open Scope Z_scope.

Module LsbCheck.
  Record t : Set := {
    lsb : Z;
  }.

  Definition output {p : Z} `{Prime p}
      (z_0 z_1 : Z)
      : t := {|
    lsb := z_0 -F z_1 *F UnOp.from 2;
  |}.

  (* Soundness: the recovered least-significant bit [lsb = z_0 - 2*z_1] is
     boolean (the [bool_check] constraint of [lsb_check_gate]). This is the
     meaningful property of the gate; there is no determinism statement because
     [lsb] is an intermediate scalar, not a stored next-row trace cell. *)
  Theorem sound
      (Γ : Assignment.t columns) (row : Z)
      (Hselector : Γ ⊢ ⟦ Selector.QMulLsb ⟧ row <> 0)
      (Hgate : Γ ⊢ ⟦ Garden.Halo2.halo2_gadgets.ecc.chip.mul.lsb_check_gate ⟧ row) :
      IsBool.t
        (output
          (Γ ⊢ ⟦ Expression.Advice Advice.A9 Rotation.next ⟧ row)
          (Γ ⊢ ⟦ Expression.Advice Advice.A9 Rotation.cur ⟧ row)).(lsb).
  Proof.
    unfold output; cbn.
    destruct Hgate as (hbool & _).
    exact (hbool Hselector).
  Qed.
End LsbCheck.
