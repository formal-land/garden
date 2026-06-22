Require Import Garden.Halo2.main.
Require Import Garden.Halo2.proof.
Require Garden.Halo2.halo2_gadgets.ecc.chip.mul_fixed.base_field_elem.
Require Import Garden.Field.Field.
Require Garden.Halo2.halo2_gadgets.ecc.chip.constants.
Require Import Garden.Orchard.columns.
Require Import Garden.Plonky3.M.

#[local] Existing Instance Primes.PallasPIsPrime.

Global Open Scope Z_scope.

Module CanonicityChecks.
  Record t : Set := {
    z_84_alpha : Z;
    alpha_0 : Z;
    alpha_0_prime : Z;
  }.

  Definition output {p : Z} `{Prime p}
      (alpha alpha_1 alpha_2 : Z)
      : t :=
    let z_84_alpha := alpha_1 +F alpha_2 *F UnOp.from (2 ^ 2) in
    let alpha_0 := alpha -F z_84_alpha *F UnOp.from (2 ^ 252) in
    {|
      z_84_alpha := z_84_alpha;
      alpha_0 := alpha_0;
      alpha_0_prime :=
        alpha_0 +F UnOp.from (2 ^ 130) -F
          UnOp.from Garden.Halo2.halo2_gadgets.ecc.chip.constants.t_p;
    |}.

  (* Soundness of [canonicity_checks_gate]: the directly-constrained facts.
     [alpha_2] (A8.cur) is boolean and [alpha_1] (A7.cur) is in [0, 4); the two
     reconstruction cells [z_84_alpha] (A8.prev) and [alpha_0_prime] (A6.cur)
     equal their [output] values. The remaining "MSB = 1 => ..." conditional
     constraints are canonicity bounds on intermediate scalars that are not
     stored in dedicated cells, so they are not part of this statement. *)
  Theorem sound
      {RegionId : Set} (Γ : Assignment.t columns RegionId) (region : RegionId) (row : Z)
      (Hselector : Γ ⊢ ⟦ Selector.QMulFixedBaseField ⟧ (region, row) <> 0)
      (Hgate :
        Γ ⊢ ⟦ Garden.Halo2.halo2_gadgets.ecc.chip.mul_fixed.base_field_elem
            .canonicity_checks_gate ⟧ (region, row)) :
      IsBool.t (Γ ⊢ ⟦ Expression.Advice Advice.A8 Rotation.cur ⟧ (region, row)) /\
      0 <= Γ ⊢ ⟦ Expression.Advice Advice.A7 Rotation.cur ⟧ (region, row) < Z.of_nat 4 /\
      Γ ⊢ ⟦ Expression.Advice Advice.A8 Rotation.prev ⟧ (region, row) =
        (output
          (Γ ⊢ ⟦ Expression.Advice Advice.A6 Rotation.prev ⟧ (region, row))
          (Γ ⊢ ⟦ Expression.Advice Advice.A7 Rotation.cur ⟧ (region, row))
          (Γ ⊢ ⟦ Expression.Advice Advice.A8 Rotation.cur ⟧ (region, row))).(z_84_alpha) /\
      Γ ⊢ ⟦ Expression.Advice Advice.A6 Rotation.cur ⟧ (region, row) =
        (output
          (Γ ⊢ ⟦ Expression.Advice Advice.A6 Rotation.prev ⟧ (region, row))
          (Γ ⊢ ⟦ Expression.Advice Advice.A7 Rotation.cur ⟧ (region, row))
          (Γ ⊢ ⟦ Expression.Advice Advice.A8 Rotation.cur ⟧ (region, row))).(alpha_0_prime).
  Proof.
    unfold output.
    with_strategy opaque [BinOp.add BinOp.mul BinOp.sub UnOp.from] cbn in *.
    destruct Hgate as (_ & _ & _ & _ & hrange & hbool & hz84 & halpha0).
    specialize (hrange Hselector).
    specialize (hbool Hselector).
    specialize (hz84 Hselector).
    specialize (halpha0 Hselector).
    split; [exact hbool |].
    split; [exact hrange |].
    split.
    - (* [z_84_alpha] reconstruction cell. *) exact hz84.
    - (* [alpha_0_prime] reconstruction cell: the gate computes [alpha_0] from
         the [z_84_alpha] cell (A8.prev), [output] from the reconstructed value;
         [hz84] bridges the two. *)
      rewrite <- hz84. exact halpha0.
  Qed.
End CanonicityChecks.
