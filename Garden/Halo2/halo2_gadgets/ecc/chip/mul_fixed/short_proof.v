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
      (ρ : Evaluation.t columns)
      (Hselector : ⟦ Selector.QMulFixedShort ⟧ ρ <> 0)
      (Hgate :
        ⟦ Garden.Halo2.halo2_gadgets.ecc.chip.mul_fixed.short
            .short_fixed_base_mul_gate ⟧ ρ) :
      {|
        y_a := ⟦ Expression.Advice Advice.A3 Rotation.cur ⟧ ρ;
      |} =
        output
          (⟦ Expression.Advice Advice.A1 Rotation.cur ⟧ ρ)
          (⟦ Expression.Advice Advice.A4 Rotation.cur ⟧ ρ).
  Proof.
    unfold output.
    with_strategy opaque [BinOp.add BinOp.mul BinOp.sub UnOp.from] cbn in *.
    destruct Hgate as (_ & _ & _ & h4).
    specialize (h4 Hselector).
    now rewrite h4.
  Qed.
End ShortFixedBaseMul.
