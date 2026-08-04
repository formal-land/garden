(** * Refinement of the width-eight scalar-window extractor

    [window8_standard] reads a byte from five little-endian radix-[2^63]
    limbs.  Four of the 32 byte windows straddle a limb boundary.  This file
    proves that both the ordinary and straddling branches return exactly the
    corresponding base-256 digit of [eval5]. *)

From Stdlib Require Import ZArith Lia.
From Stdlib Require Import ZArith.Zbitwise.
Require Import Stdlib.Numbers.Cyclic.Int63.Uint63.
Require Import Garden.Prim63.Words.
Require Import Garden.Prim63.Montgomery.
Require Import Garden.Prim63.Refinement.

Local Open Scope Z_scope.

Module Prim63WindowRefinement (C : Prim63MontgomeryConfig).
  Import Prim63Words.
  Module M := Prim63Montgomery C.

  Lemma radix_pow2 : radix = 2 ^ 63.
  Proof. reflexivity. Qed.

  Lemma byte_mask_spec (x : word) :
    Uint63.to_Z (PrimInt63.land x 255%uint63) =
      Uint63.to_Z x mod 256.
  Proof.
    rewrite Uint63.land_spec'.
    change (Uint63.to_Z 255%uint63) with 255.
    change 255 with (Z.ones 8).
    rewrite Z.land_ones by lia.
    reflexivity.
  Qed.

  Lemma byte_shift_spec (x offset : word) :
    Uint63.to_Z
      (PrimInt63.land (PrimInt63.lsr x offset) 255%uint63) =
    (Uint63.to_Z x / 2 ^ Uint63.to_Z offset) mod 256.
  Proof.
    rewrite byte_mask_spec, Uint63.lsr_spec.
    reflexivity.
  Qed.

  Lemma power_divides_radix (shift : Z) :
    0 <= shift <= 63 -> (2 ^ shift | radix).
  Proof.
    intros Hshift.
    rewrite radix_pow2.
    exists (2 ^ (63 - shift)).
    rewrite <- Z.pow_add_r by lia.
    f_equal; lia.
  Qed.

  Lemma byte_divides_radix : (256 | radix).
  Proof.
    rewrite radix_pow2.
    exists (2 ^ 55).
    change 256 with (2 ^ 8).
    rewrite <- Z.pow_add_r by lia.
    reflexivity.
  Qed.

  Lemma radix_split (offset : Z) :
    0 <= offset <= 63 ->
    radix = 2 ^ offset * 2 ^ (63 - offset).
  Proof.
    intros Hoffset.
    rewrite radix_pow2, <- Z.pow_add_r by lia.
    f_equal; lia.
  Qed.

  Lemma byte_divides_upper_power (offset : Z) :
    0 <= offset <= 55 -> (256 | 2 ^ (63 - offset)).
  Proof.
    intros Hoffset.
    exists (2 ^ (55 - offset)).
    change 256 with (2 ^ 8).
    rewrite <- Z.pow_add_r by lia.
    f_equal; lia.
  Qed.

  Lemma radix2_mul_power (offset : Z) (Hoffset : 0 <= offset) :
    radix ^ 2 * 2 ^ offset = 2 ^ (126 + offset).
  Proof.
    rewrite radix_pow2.
    change ((2 ^ 63 * 2 ^ 63) * 2 ^ offset = 2 ^ (126 + offset)).
    rewrite <- (Z.pow_add_r 2 63 63) by lia.
    rewrite <- (Z.pow_add_r 2 (63 + 63) offset) by lia.
    f_equal; lia.
  Qed.

  Lemma radix3_mul_power (offset : Z) (Hoffset : 0 <= offset) :
    radix ^ 3 * 2 ^ offset = 2 ^ (189 + offset).
  Proof.
    rewrite radix_pow2.
    change
      (((2 ^ 63 * 2 ^ 63) * 2 ^ 63) * 2 ^ offset =
        2 ^ (189 + offset)).
    rewrite <- (Z.pow_add_r 2 63 63) by lia.
    rewrite <- (Z.pow_add_r 2 (63 + 63) 63) by lia.
    rewrite <- (Z.pow_add_r 2 (63 + 63 + 63) offset) by lia.
    f_equal; lia.
  Qed.

  (** A value below [2^shift] and a multiple of [2^shift] occupy disjoint
      bit ranges, so bitwise-or is ordinary addition. *)
  Lemma lor_disjoint_low_high (low high shift : Z) :
    0 <= shift ->
    0 <= low < 2 ^ shift ->
    high mod 2 ^ shift = 0 ->
    Z.lor low high = low + high.
  Proof.
    intros Hshift Hlow Hhigh.
    assert (Hlow_mask : Z.land low (Z.ones shift) = low).
    { rewrite Z.land_ones by exact Hshift.
      apply Z.mod_small; exact Hlow. }
    assert (Hhigh_mask : Z.land high (Z.ones shift) = 0).
    { rewrite Z.land_ones by exact Hshift.
      exact Hhigh. }
    assert (Hdisjoint : Z.land low high = 0).
    { rewrite <- Hlow_mask at 1.
      rewrite <- Z.land_assoc.
      rewrite (Z.land_comm (Z.ones shift) high), Hhigh_mask.
      apply Z.land_0_r. }
    pose proof (Z.add_lor_land low high) as Hsum.
    rewrite Hdisjoint, Z.add_0_r in Hsum.
    exact Hsum.
  Qed.

  (** The primitive straddling branch joins the last [shift] bits of one
      limb with the first [8-shift] bits of the next limb. *)
  Lemma byte_join_spec (x y offset shift : word)
      (Hoffset : 0 <= Uint63.to_Z offset)
      (Hshift : 0 < Uint63.to_Z shift <= 8)
      (Htotal : Uint63.to_Z offset + Uint63.to_Z shift = 63) :
    Uint63.to_Z
      (PrimInt63.land
        (PrimInt63.lor (PrimInt63.lsr x offset)
          (PrimInt63.lsl y shift))
        255%uint63) =
    (Uint63.to_Z x / 2 ^ Uint63.to_Z offset +
      Uint63.to_Z y * 2 ^ Uint63.to_Z shift) mod 256.
  Proof.
    rewrite byte_mask_spec, Uint63.lor_spec', Uint63.lsr_spec,
      Uint63.lsl_spec.
    set (low := Uint63.to_Z x / 2 ^ Uint63.to_Z offset).
    set (high :=
      (Uint63.to_Z y * 2 ^ Uint63.to_Z shift) mod radix).
    change ((Z.lor low high) mod 256 =
      (low + Uint63.to_Z y * 2 ^ Uint63.to_Z shift) mod 256).
    pose proof (word_bounds x) as Hx.
    assert (Hpo : 0 < 2 ^ Uint63.to_Z offset).
    { apply Z.pow_pos_nonneg; lia. }
    assert (Hps : 0 < 2 ^ Uint63.to_Z shift).
    { apply Z.pow_pos_nonneg; lia. }
    assert (Hlow : 0 <= low < 2 ^ Uint63.to_Z shift).
    { subst low.
      split.
      - apply Z.div_pos; lia.
      - apply Z.div_lt_upper_bound; [exact Hpo |].
        rewrite <- Z.pow_add_r by lia.
        rewrite Htotal, <- radix_pow2.
        exact (proj2 Hx). }
    assert (Hhigh_mod : high mod 2 ^ Uint63.to_Z shift = 0).
    { subst high.
      rewrite Z.mod_mod_divide by (apply power_divides_radix; lia).
      apply Z.mod_mul; lia. }
    rewrite (lor_disjoint_low_high low high (Uint63.to_Z shift)
      ltac:(lia) Hlow Hhigh_mod).
    subst low high.
    rewrite (Z.add_mod
      (Uint63.to_Z x / 2 ^ Uint63.to_Z offset)
      ((Uint63.to_Z y * 2 ^ Uint63.to_Z shift) mod radix) 256) by lia.
    rewrite (Z.add_mod
      (Uint63.to_Z x / 2 ^ Uint63.to_Z offset)
      (Uint63.to_Z y * 2 ^ Uint63.to_Z shift) 256) by lia.
    rewrite Z.mod_mod_divide by exact byte_divides_radix.
    reflexivity.
  Qed.

  (** Removing a lower-radix prefix does not affect the quotient.  The
      remainder bound is the only subtle point: the prefix is shorter than
      [scale], while [x mod d] occupies fewer than [d] such blocks. *)
  Lemma div_with_prefix (prefix scale x d : Z) :
    0 <= prefix < scale ->
    0 < scale ->
    0 <= x ->
    0 < d ->
    (prefix + scale * x) / (scale * d) = x / d.
  Proof.
    intros Hprefix Hscale Hx Hd.
    pose proof (Z.div_mod x d ltac:(lia)) as Hdivmod.
    pose proof (Z.mod_pos_bound x d Hd) as Hmod.
    set (remainder := prefix + scale * (x mod d)).
    assert (Hremainder : 0 <= remainder < scale * d).
    { subst remainder.
      split.
      - apply Z.add_nonneg_nonneg; [lia |].
        apply Z.mul_nonneg_nonneg; lia.
      - assert (Hstep :
          prefix + scale * (x mod d) < scale * ((x mod d) + 1)).
        { ring_simplify; lia. }
        assert (Hmono : scale * ((x mod d) + 1) <= scale * d).
        { apply Z.mul_le_mono_nonneg_l; lia. }
        lia. }
    replace (prefix + scale * x) with
      ((x / d) * (scale * d) + remainder).
    2: { subst remainder. rewrite Hdivmod at 3. ring. }
    assert (Hscale_d : 0 < scale * d).
    { apply Z.mul_pos_pos; assumption. }
    rewrite Z.div_add_l by lia.
    rewrite (Z.div_small remainder (scale * d) Hremainder).
    lia.
  Qed.

  Lemma quotient_slice (prefix scale limb tail d high : Z) :
    0 <= prefix < scale ->
    0 < scale ->
    0 <= limb ->
    0 <= tail ->
    0 < d ->
    radix = d * high ->
    (prefix + scale * (limb + radix * tail)) / (scale * d) =
      limb / d + high * tail.
  Proof.
    intros Hprefix Hscale Hlimb Htail Hd Hradix.
    rewrite div_with_prefix.
    2: exact Hprefix.
    2: exact Hscale.
    2: { apply Z.add_nonneg_nonneg; [exact Hlimb |].
         apply Z.mul_nonneg_nonneg;
           [apply Z.lt_le_incl, radix_pos | exact Htail]. }
    2: exact Hd.
    rewrite Hradix.
    replace (limb + d * high * tail) with
      (limb + (high * tail) * d) by ring.
    rewrite Z.div_add by lia.
    ring.
  Qed.

  Lemma quotient_slice_no_cross
      (prefix scale limb tail d high : Z) :
    0 <= prefix < scale ->
    0 < scale ->
    0 <= limb ->
    0 <= tail ->
    0 < d ->
    radix = d * high ->
    (256 | high) ->
    ((prefix + scale * (limb + radix * tail)) / (scale * d)) mod 256 =
      (limb / d) mod 256.
  Proof.
    intros Hprefix Hscale Hlimb Htail Hd Hradix [k Hhigh].
    rewrite (quotient_slice prefix scale limb tail d high) by assumption.
    rewrite Hhigh.
    replace (k * 256 * tail) with ((k * tail) * 256) by ring.
    apply Z.mod_add; lia.
  Qed.

  Lemma quotient_slice_cross
      (prefix scale limb next rest d high : Z) :
    0 <= prefix < scale ->
    0 < scale ->
    0 <= limb ->
    0 <= next ->
    0 <= rest ->
    0 < d ->
    radix = d * high ->
    ((prefix + scale *
        (limb + radix * (next + radix * rest))) / (scale * d)) mod 256 =
      (limb / d + high * next) mod 256.
  Proof.
    intros Hprefix Hscale Hlimb Hnext Hrest Hd Hradix.
    rewrite (quotient_slice prefix scale limb
      (next + radix * rest) d high).
    2: exact Hprefix.
    2: exact Hscale.
    2: exact Hlimb.
    2: { apply Z.add_nonneg_nonneg; [exact Hnext |].
         apply Z.mul_nonneg_nonneg;
           [apply Z.lt_le_incl, radix_pos | exact Hrest]. }
    2: exact Hd.
    2: exact Hradix.
    replace (high * (next + radix * rest)) with
      (high * next + (high * rest) * radix) by ring.
    destruct byte_divides_radix as [k Hradix256].
    rewrite Hradix256.
    replace (high * rest * (k * 256)) with
      ((high * rest * k) * 256) by ring.
    replace
      (limb / d + (high * next + high * rest * k * 256)) with
      ((limb / d + high * next) + (high * rest * k) * 256) by ring.
    apply Z.mod_add; lia.
  Qed.

  Lemma quotient_slice_zero_no_cross (limb tail d high : Z) :
    0 <= limb ->
    0 <= tail ->
    0 < d ->
    radix = d * high ->
    (256 | high) ->
    ((limb + radix * tail) / d) mod 256 = (limb / d) mod 256.
  Proof.
    intros Hlimb Htail Hd Hradix Hhigh.
    pose proof (quotient_slice_no_cross 0 1 limb tail d high
      ltac:(lia) ltac:(lia) Hlimb Htail Hd Hradix Hhigh) as H.
    replace (0 + 1 * (limb + radix * tail)) with
      (limb + radix * tail) in H by ring.
    replace (1 * d) with d in H by ring.
    exact H.
  Qed.

  Lemma quotient_slice_zero_cross (limb next rest d high : Z) :
    0 <= limb ->
    0 <= next ->
    0 <= rest ->
    0 < d ->
    radix = d * high ->
    ((limb + radix * (next + radix * rest)) / d) mod 256 =
      (limb / d + high * next) mod 256.
  Proof.
    intros Hlimb Hnext Hrest Hd Hradix.
    pose proof (quotient_slice_cross 0 1 limb next rest d high
      ltac:(lia) ltac:(lia) Hlimb Hnext Hrest Hd Hradix) as H.
    replace (0 + 1 * (limb + radix * (next + radix * rest))) with
      (limb + radix * (next + radix * rest)) in H by ring.
    replace (1 * d) with d in H by ring.
    exact H.
  Qed.

  Lemma append_limb_bounds (prefix scale limb : Z) :
    0 <= prefix < scale ->
    0 < scale ->
    0 <= limb < radix ->
    0 <= prefix + scale * limb < scale * radix.
  Proof.
    intros Hprefix Hscale Hlimb.
    split.
    - apply Z.add_nonneg_nonneg; [lia |].
      apply Z.mul_nonneg_nonneg; lia.
    - assert (Hlimb_le : limb <= radix - 1) by lia.
      assert (Hmul : scale * limb <= scale * (radix - 1)).
      { apply Z.mul_le_mono_nonneg_l; lia. }
      nia.
  Qed.

  Lemma two_limb_bounds (a0 a1 : word) :
    0 <= Uint63.to_Z a0 + radix * Uint63.to_Z a1 < radix ^ 2.
  Proof.
    replace (radix ^ 2) with (radix * radix) by ring.
    apply append_limb_bounds.
    - apply word_bounds.
    - apply radix_pos.
    - apply word_bounds.
  Qed.

  Lemma three_limb_bounds (a0 a1 a2 : word) :
    0 <= Uint63.to_Z a0 +
      radix * (Uint63.to_Z a1 + radix * Uint63.to_Z a2) < radix ^ 3.
  Proof.
    replace
      (Uint63.to_Z a0 +
        radix * (Uint63.to_Z a1 + radix * Uint63.to_Z a2)) with
      ((Uint63.to_Z a0 + radix * Uint63.to_Z a1) +
        radix ^ 2 * Uint63.to_Z a2) by ring.
    replace (radix ^ 3) with (radix ^ 2 * radix) by ring.
    apply append_limb_bounds.
    - apply two_limb_bounds.
    - apply Z.pow_pos_nonneg; [apply radix_pos | lia].
    - apply word_bounds.
  Qed.

  (** ** The four possible starting limbs *)

  Lemma eval5_slice0_no_cross (a : words5) (offset : Z)
      (Hoffset : 0 <= offset <= 55) :
    (eval5 a / 2 ^ offset) mod 256 =
      (Uint63.to_Z a.(w0) / 2 ^ offset) mod 256.
  Proof.
    destruct a as [a0 a1 a2 a3 a4].
    pose proof (word_bounds a0) as H0.
    pose proof (word_bounds a1) as H1.
    pose proof (word_bounds a2) as H2.
    pose proof (word_bounds a3) as H3.
    pose proof (word_bounds a4) as H4.
    unfold eval5; cbn [w0 w1 w2 w3 w4].
    eapply (quotient_slice_zero_no_cross
      (Uint63.to_Z a0)
      (Uint63.to_Z a1 + radix *
        (Uint63.to_Z a2 + radix *
          (Uint63.to_Z a3 + radix * Uint63.to_Z a4)))
      (2 ^ offset) (2 ^ (63 - offset))).
    - lia.
    - rewrite radix_value in *; lia.
    - apply Z.pow_pos_nonneg; lia.
    - apply radix_split; lia.
    - apply byte_divides_upper_power; lia.
  Qed.

  Lemma eval5_slice1_no_cross (a : words5) (offset : Z)
      (Hoffset : 0 <= offset <= 55) :
    (eval5 a / 2 ^ (63 + offset)) mod 256 =
      (Uint63.to_Z a.(w1) / 2 ^ offset) mod 256.
  Proof.
    destruct a as [a0 a1 a2 a3 a4].
    pose proof (word_bounds a0) as H0.
    pose proof (word_bounds a1) as H1.
    pose proof (word_bounds a2) as H2.
    pose proof (word_bounds a3) as H3.
    pose proof (word_bounds a4) as H4.
    unfold eval5; cbn [w0 w1 w2 w3 w4].
    rewrite Z.pow_add_r by lia.
    change (2 ^ 63) with radix.
    eapply (quotient_slice_no_cross
      (Uint63.to_Z a0) radix (Uint63.to_Z a1)
      (Uint63.to_Z a2 + radix *
        (Uint63.to_Z a3 + radix * Uint63.to_Z a4))
      (2 ^ offset) (2 ^ (63 - offset))).
    - exact H0.
    - apply radix_pos.
    - lia.
    - rewrite radix_value in *; lia.
    - apply Z.pow_pos_nonneg; lia.
    - apply radix_split; lia.
    - apply byte_divides_upper_power; lia.
  Qed.

  Lemma eval5_slice2_no_cross (a : words5) (offset : Z)
      (Hoffset : 0 <= offset <= 55) :
    (eval5 a / 2 ^ (126 + offset)) mod 256 =
      (Uint63.to_Z a.(w2) / 2 ^ offset) mod 256.
  Proof.
    destruct a as [a0 a1 a2 a3 a4].
    pose proof (word_bounds a0) as H0.
    pose proof (word_bounds a1) as H1.
    pose proof (word_bounds a2) as H2.
    pose proof (word_bounds a3) as H3.
    pose proof (word_bounds a4) as H4.
    unfold eval5; cbn [w0 w1 w2 w3 w4].
    replace (2 ^ (126 + offset)) with (radix ^ 2 * 2 ^ offset).
    2: { apply radix2_mul_power; lia. }
    replace
      (Uint63.to_Z a0 + radix *
        (Uint63.to_Z a1 + radix *
          (Uint63.to_Z a2 + radix *
            (Uint63.to_Z a3 + radix * Uint63.to_Z a4)))) with
      ((Uint63.to_Z a0 + radix * Uint63.to_Z a1) +
        radix ^ 2 *
          (Uint63.to_Z a2 + radix *
            (Uint63.to_Z a3 + radix * Uint63.to_Z a4))) by ring.
    eapply (quotient_slice_no_cross
      (Uint63.to_Z a0 + radix * Uint63.to_Z a1)
      (radix ^ 2) (Uint63.to_Z a2)
      (Uint63.to_Z a3 + radix * Uint63.to_Z a4)
      (2 ^ offset) (2 ^ (63 - offset))).
    - apply two_limb_bounds.
    - apply Z.pow_pos_nonneg; [apply radix_pos | lia].
    - lia.
    - rewrite radix_value in *; lia.
    - apply Z.pow_pos_nonneg; lia.
    - apply radix_split; lia.
    - apply byte_divides_upper_power; lia.
  Qed.

  Lemma eval5_slice3_no_cross (a : words5) (offset : Z)
      (Hoffset : 0 <= offset <= 55) :
    (eval5 a / 2 ^ (189 + offset)) mod 256 =
      (Uint63.to_Z a.(w3) / 2 ^ offset) mod 256.
  Proof.
    destruct a as [a0 a1 a2 a3 a4].
    pose proof (word_bounds a0) as H0.
    pose proof (word_bounds a1) as H1.
    pose proof (word_bounds a2) as H2.
    pose proof (word_bounds a3) as H3.
    pose proof (word_bounds a4) as H4.
    unfold eval5; cbn [w0 w1 w2 w3 w4].
    replace (2 ^ (189 + offset)) with (radix ^ 3 * 2 ^ offset).
    2: { apply radix3_mul_power; lia. }
    replace
      (Uint63.to_Z a0 + radix *
        (Uint63.to_Z a1 + radix *
          (Uint63.to_Z a2 + radix *
            (Uint63.to_Z a3 + radix * Uint63.to_Z a4)))) with
      ((Uint63.to_Z a0 + radix *
          (Uint63.to_Z a1 + radix * Uint63.to_Z a2)) +
        radix ^ 3 * (Uint63.to_Z a3 + radix * Uint63.to_Z a4)) by ring.
    eapply (quotient_slice_no_cross
      (Uint63.to_Z a0 + radix *
        (Uint63.to_Z a1 + radix * Uint63.to_Z a2))
      (radix ^ 3) (Uint63.to_Z a3) (Uint63.to_Z a4)
      (2 ^ offset) (2 ^ (63 - offset))).
    - apply three_limb_bounds.
    - apply Z.pow_pos_nonneg; [apply radix_pos | lia].
    - lia.
    - lia.
    - apply Z.pow_pos_nonneg; lia.
    - apply radix_split; lia.
    - apply byte_divides_upper_power; lia.
  Qed.

  Lemma eval5_slice0_cross (a : words5) (offset : Z)
      (Hoffset : 55 < offset < 63) :
    (eval5 a / 2 ^ offset) mod 256 =
      (Uint63.to_Z a.(w0) / 2 ^ offset +
        2 ^ (63 - offset) * Uint63.to_Z a.(w1)) mod 256.
  Proof.
    destruct a as [a0 a1 a2 a3 a4].
    pose proof (word_bounds a0) as H0.
    pose proof (word_bounds a1) as H1.
    pose proof (word_bounds a2) as H2.
    pose proof (word_bounds a3) as H3.
    pose proof (word_bounds a4) as H4.
    unfold eval5; cbn [w0 w1 w2 w3 w4].
    eapply (quotient_slice_zero_cross
      (Uint63.to_Z a0) (Uint63.to_Z a1)
      (Uint63.to_Z a2 + radix *
        (Uint63.to_Z a3 + radix * Uint63.to_Z a4))
      (2 ^ offset) (2 ^ (63 - offset))).
    - lia.
    - lia.
    - rewrite radix_value in *; lia.
    - apply Z.pow_pos_nonneg; lia.
    - apply radix_split; lia.
  Qed.

  Lemma eval5_slice1_cross (a : words5) (offset : Z)
      (Hoffset : 55 < offset < 63) :
    (eval5 a / 2 ^ (63 + offset)) mod 256 =
      (Uint63.to_Z a.(w1) / 2 ^ offset +
        2 ^ (63 - offset) * Uint63.to_Z a.(w2)) mod 256.
  Proof.
    destruct a as [a0 a1 a2 a3 a4].
    pose proof (word_bounds a0) as H0.
    pose proof (word_bounds a1) as H1.
    pose proof (word_bounds a2) as H2.
    pose proof (word_bounds a3) as H3.
    pose proof (word_bounds a4) as H4.
    unfold eval5; cbn [w0 w1 w2 w3 w4].
    rewrite Z.pow_add_r by lia.
    change (2 ^ 63) with radix.
    eapply (quotient_slice_cross
      (Uint63.to_Z a0) radix (Uint63.to_Z a1) (Uint63.to_Z a2)
      (Uint63.to_Z a3 + radix * Uint63.to_Z a4)
      (2 ^ offset) (2 ^ (63 - offset))).
    - exact H0.
    - apply radix_pos.
    - lia.
    - lia.
    - rewrite radix_value in *; lia.
    - apply Z.pow_pos_nonneg; lia.
    - apply radix_split; lia.
  Qed.

  Lemma eval5_slice2_cross (a : words5) (offset : Z)
      (Hoffset : 55 < offset < 63) :
    (eval5 a / 2 ^ (126 + offset)) mod 256 =
      (Uint63.to_Z a.(w2) / 2 ^ offset +
        2 ^ (63 - offset) * Uint63.to_Z a.(w3)) mod 256.
  Proof.
    destruct a as [a0 a1 a2 a3 a4].
    pose proof (word_bounds a0) as H0.
    pose proof (word_bounds a1) as H1.
    pose proof (word_bounds a2) as H2.
    pose proof (word_bounds a3) as H3.
    pose proof (word_bounds a4) as H4.
    unfold eval5; cbn [w0 w1 w2 w3 w4].
    replace (2 ^ (126 + offset)) with (radix ^ 2 * 2 ^ offset).
    2: { apply radix2_mul_power; lia. }
    replace
      (Uint63.to_Z a0 + radix *
        (Uint63.to_Z a1 + radix *
          (Uint63.to_Z a2 + radix *
            (Uint63.to_Z a3 + radix * Uint63.to_Z a4)))) with
      ((Uint63.to_Z a0 + radix * Uint63.to_Z a1) +
        radix ^ 2 *
          (Uint63.to_Z a2 + radix *
            (Uint63.to_Z a3 + radix * Uint63.to_Z a4))) by ring.
    eapply (quotient_slice_cross
      (Uint63.to_Z a0 + radix * Uint63.to_Z a1)
      (radix ^ 2) (Uint63.to_Z a2) (Uint63.to_Z a3)
      (Uint63.to_Z a4) (2 ^ offset) (2 ^ (63 - offset))).
    - apply two_limb_bounds.
    - apply Z.pow_pos_nonneg; [apply radix_pos | lia].
    - lia.
    - lia.
    - lia.
    - apply Z.pow_pos_nonneg; lia.
    - apply radix_split; lia.
  Qed.

  Lemma eval5_slice3_cross (a : words5) (offset : Z)
      (Hoffset : 55 < offset < 63) :
    (eval5 a / 2 ^ (189 + offset)) mod 256 =
      (Uint63.to_Z a.(w3) / 2 ^ offset +
        2 ^ (63 - offset) * Uint63.to_Z a.(w4)) mod 256.
  Proof.
    destruct a as [a0 a1 a2 a3 a4].
    pose proof (word_bounds a0) as H0.
    pose proof (word_bounds a1) as H1.
    pose proof (word_bounds a2) as H2.
    pose proof (word_bounds a3) as H3.
    pose proof (word_bounds a4) as H4.
    unfold eval5; cbn [w0 w1 w2 w3 w4].
    replace (2 ^ (189 + offset)) with (radix ^ 3 * 2 ^ offset).
    2: { apply radix3_mul_power; lia. }
    replace
      (Uint63.to_Z a0 + radix *
        (Uint63.to_Z a1 + radix *
          (Uint63.to_Z a2 + radix *
            (Uint63.to_Z a3 + radix * Uint63.to_Z a4)))) with
      ((Uint63.to_Z a0 + radix *
          (Uint63.to_Z a1 + radix * Uint63.to_Z a2)) +
        radix ^ 3 * (Uint63.to_Z a3 + radix * Uint63.to_Z a4)) by ring.
    replace (Uint63.to_Z a3 + radix * Uint63.to_Z a4) with
      (Uint63.to_Z a3 + radix * (Uint63.to_Z a4 + radix * 0)) by ring.
    eapply (quotient_slice_cross
      (Uint63.to_Z a0 + radix *
        (Uint63.to_Z a1 + radix * Uint63.to_Z a2))
      (radix ^ 3) (Uint63.to_Z a3) (Uint63.to_Z a4) 0
      (2 ^ offset) (2 ^ (63 - offset))).
    - apply three_limb_bounds.
    - apply Z.pow_pos_nonneg; [apply radix_pos | lia].
    - lia.
    - lia.
    - lia.
    - apply Z.pow_pos_nonneg; lia.
    - apply radix_split; lia.
  Qed.

  (** ** Complete window theorem

      The finite case split is on the public window number, never on scalar
      data.  It mirrors the executable control flow: 28 ordinary byte reads
      and four reads crossing a 63-bit limb boundary. *)
  Theorem window8_standard_spec (a : words5) (window : word)
      (Hwindow : Uint63.to_Z window < 32) :
    Uint63.to_Z (M.window8_standard a window) =
      (eval5 a / 2 ^ (8 * Uint63.to_Z window)) mod 256.
  Proof.
    pose proof (word_bounds window) as Hwindow_nonnegative.
    assert (Hcases :
      Uint63.to_Z window = 0 \/
      Uint63.to_Z window = 1 \/
      Uint63.to_Z window = 2 \/
      Uint63.to_Z window = 3 \/
      Uint63.to_Z window = 4 \/
      Uint63.to_Z window = 5 \/
      Uint63.to_Z window = 6 \/
      Uint63.to_Z window = 7 \/
      Uint63.to_Z window = 8 \/
      Uint63.to_Z window = 9 \/
      Uint63.to_Z window = 10 \/
      Uint63.to_Z window = 11 \/
      Uint63.to_Z window = 12 \/
      Uint63.to_Z window = 13 \/
      Uint63.to_Z window = 14 \/
      Uint63.to_Z window = 15 \/
      Uint63.to_Z window = 16 \/
      Uint63.to_Z window = 17 \/
      Uint63.to_Z window = 18 \/
      Uint63.to_Z window = 19 \/
      Uint63.to_Z window = 20 \/
      Uint63.to_Z window = 21 \/
      Uint63.to_Z window = 22 \/
      Uint63.to_Z window = 23 \/
      Uint63.to_Z window = 24 \/
      Uint63.to_Z window = 25 \/
      Uint63.to_Z window = 26 \/
      Uint63.to_Z window = 27 \/
      Uint63.to_Z window = 28 \/
      Uint63.to_Z window = 29 \/
      Uint63.to_Z window = 30 \/
      Uint63.to_Z window = 31) by lia.
    Ltac finish_window_case a window Hwindow_value :=
      let k := match type of Hwindow_value with
        | Uint63.to_Z ?w = ?value => value
        end in
      let literal := (eval vm_compute in (Uint63.of_Z k)) in
      assert (Hliteral : window = literal);
      [ apply Uint63.to_Z_inj;
        rewrite Hwindow_value;
        vm_compute;
        reflexivity
      | rewrite Hliteral;
        let normalized :=
          (eval vm_compute in (M.window8_standard a literal)) in
        lazymatch normalized with
        | PrimInt63.land (PrimInt63.lsr ?word ?offset_word) ?mask =>
            change
              (Uint63.to_Z normalized =
                (eval5 a / 2 ^ (8 * k)) mod 256);
            let offset := (eval vm_compute in
              (Uint63.to_Z offset_word)) in
            let Hoffset := fresh "Hoffset" in
            assert (Hoffset : Uint63.to_Z offset_word = offset)
              by (vm_compute; reflexivity);
            rewrite byte_shift_spec, Hoffset;
            clear Hoffset;
            symmetry;
            destruct a as [a0 a1 a2 a3 a4];
            let limb := (eval vm_compute in ((8 * k) / 63)) in
            lazymatch limb with
            | 0 =>
                replace (8 * k) with offset by (vm_compute; reflexivity);
                apply eval5_slice0_no_cross;
                vm_compute; constructor; discriminate
            | 1 =>
                replace (8 * k) with (63 + offset)
                  by (vm_compute; reflexivity);
                apply eval5_slice1_no_cross;
                vm_compute; constructor; discriminate
            | 2 =>
                replace (8 * k) with (126 + offset)
                  by (vm_compute; reflexivity);
                apply eval5_slice2_no_cross;
                vm_compute; constructor; discriminate
            | 3 =>
                replace (8 * k) with (189 + offset)
                  by (vm_compute; reflexivity);
                apply eval5_slice3_no_cross;
                vm_compute; constructor; discriminate
            end
        | PrimInt63.land
            (PrimInt63.lor (PrimInt63.lsr ?left ?offset_word)
              (PrimInt63.lsl ?right ?shift_word)) ?mask =>
            change
              (Uint63.to_Z normalized =
                (eval5 a / 2 ^ (8 * k)) mod 256);
            let offset := (eval vm_compute in
              (Uint63.to_Z offset_word)) in
            let shift := (eval vm_compute in
              (Uint63.to_Z shift_word)) in
            let Hoffset := fresh "Hoffset" in
            let Hshift := fresh "Hshift" in
            assert (Hoffset : Uint63.to_Z offset_word = offset)
              by (vm_compute; reflexivity);
            assert (Hshift : Uint63.to_Z shift_word = shift)
              by (vm_compute; reflexivity);
            rewrite byte_join_spec by (cbn; lia);
            rewrite Hoffset, Hshift;
            clear Hoffset Hshift;
            symmetry;
            destruct a as [a0 a1 a2 a3 a4];
            let limb := (eval vm_compute in ((8 * k) / 63)) in
            lazymatch limb with
            | 0 =>
                replace (8 * k) with offset by (vm_compute; reflexivity);
                rewrite eval5_slice0_cross by lia;
                replace (63 - offset) with shift
                  by (vm_compute; reflexivity);
                f_equal; cbn [w0 w1 w2 w3 w4]; ring
            | 1 =>
                replace (8 * k) with (63 + offset)
                  by (vm_compute; reflexivity);
                rewrite eval5_slice1_cross by lia;
                replace (63 - offset) with shift
                  by (vm_compute; reflexivity);
                f_equal; cbn [w0 w1 w2 w3 w4]; ring
            | 2 =>
                replace (8 * k) with (126 + offset)
                  by (vm_compute; reflexivity);
                rewrite eval5_slice2_cross by lia;
                replace (63 - offset) with shift
                  by (vm_compute; reflexivity);
                f_equal; cbn [w0 w1 w2 w3 w4]; ring
            | 3 =>
                replace (8 * k) with (189 + offset)
                  by (vm_compute; reflexivity);
                rewrite eval5_slice3_cross by lia;
                replace (63 - offset) with shift
                  by (vm_compute; reflexivity);
                f_equal; cbn [w0 w1 w2 w3 w4]; ring
            end
        end ].
    Ltac finish_window_cases a window cases :=
      lazymatch type of cases with
      | _ \/ _ =>
          destruct cases as [Hwindow_value | cases];
          [ finish_window_case a window Hwindow_value
          | finish_window_cases a window cases ]
      | _ =>
          finish_window_case a window cases
      end.
    destruct Hcases as [Hwindow_zero | Hcases].
    - assert (Hliteral : window = 0%uint63).
      { apply Uint63.to_Z_inj.
        change (Uint63.to_Z window = 0).
        exact Hwindow_zero. }
      rewrite Hliteral.
      let normalized :=
        (eval vm_compute in (M.window8_standard a 0%uint63)) in
      change
        (Uint63.to_Z normalized =
          (eval5 a / 2 ^ (8 * 0)) mod 256).
      rewrite byte_shift_spec.
      symmetry.
      assert (Hoffset_zero : 0 <= 0 <= 55) by lia.
      pose proof (eval5_slice0_no_cross a 0 Hoffset_zero) as Hslice.
      exact Hslice.
    - destruct Hcases as [Hwindow_one | Hcases].
      + assert (Hliteral : window = 1%uint63).
        { apply Uint63.to_Z_inj.
          rewrite Hwindow_one.
          vm_compute.
          reflexivity. }
        rewrite Hliteral.
        let normalized :=
          (eval vm_compute in (M.window8_standard a 1%uint63)) in
        change
          (Uint63.to_Z normalized =
            (eval5 a / 2 ^ (8 * 1)) mod 256).
        rewrite byte_shift_spec.
        symmetry.
        destruct a as [a0 a1 a2 a3 a4].
        apply eval5_slice0_no_cross.
        vm_compute.
        constructor; discriminate.
      + finish_window_cases a window Hcases.
  Qed.

  Corollary window8_standard_bound (a : words5) (window : word)
      (Hwindow : Uint63.to_Z window < 32) :
    0 <= Uint63.to_Z (M.window8_standard a window) < 256.
  Proof.
    rewrite window8_standard_spec by exact Hwindow.
    apply Z.mod_pos_bound; lia.
  Qed.

End Prim63WindowRefinement.
