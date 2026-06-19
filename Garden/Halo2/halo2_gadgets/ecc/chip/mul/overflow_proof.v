Require Import Garden.Halo2.main.
Require Import Garden.Halo2.proof.
Require Garden.Halo2.halo2_gadgets.ecc.chip.mul.overflow.
Require Import Garden.Field.Field.
Require Garden.Halo2.halo2_gadgets.ecc.chip.constants.
Require Import Garden.Orchard.columns.
Require Import Garden.Plonky3.M.

#[local] Existing Instance Primes.PallasPIsPrime.

Global Open Scope Z_scope.

Module OverflowChecks.
  Record t : Set := {
    s : Z;
    z_0 : Z;
  }.

  Definition output {p : Z} `{Prime p}
      (alpha k_254 : Z)
      : t := {|
    s := alpha +F k_254 *F UnOp.from (2 ^ 130);
    z_0 :=
      alpha +F
        UnOp.from Garden.Halo2.halo2_gadgets.ecc.chip.constants.t_q;
  |}.

  (* The next-row values constrained by the overflow-check gate are uniquely
     determined by the witnessed [alpha] and [k_254]: [s] is recovered from the
     [s_check] constraint and [z_0] from the [recovery] constraint. *)
  Theorem deterministic
      (ρ : Evaluation.t columns)
      (Hselector : ⟦ Selector.QMulOverflow ⟧ ρ <> 0)
      (Hgate :
        ⟦ Garden.Halo2.halo2_gadgets.ecc.chip.mul.overflow.overflow_checks_gate ⟧
          ρ) :
      {|
        s := ⟦ Expression.Advice Advice.A8 Rotation.cur ⟧ ρ;
        z_0 := ⟦ Expression.Advice Advice.A6 Rotation.prev ⟧ ρ;
      |} =
        output
          (⟦ Expression.Advice Advice.A7 Rotation.cur ⟧ ρ)
          (⟦ Expression.Advice Advice.A7 Rotation.prev ⟧ ρ).
  Proof.
  Admitted.
End OverflowChecks.
