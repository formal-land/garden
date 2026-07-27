(** * Base-8 running-sum reconstruction from a canonicity bound

    The number-theoretic core of the base-field (nullifier_k) scalar digit
    match.  The base-field running sum has 85 windows,
    and [8^85 > pallas_p], so the short-leg route (reconstruct over Z from
    [8^count < p]) does not apply.  Instead:

    - the mod-P telescoping [wsum_tail_congruent] holds unconditionally from a
      vanishing tail -- no size hypothesis on the windows or the modulus (this
      is what the short leg gets for free from [8^count < p]);

    - the canonicity sub-circuit supplies the single extra fact
      [wsum 0 count < P], and [reconstruct_of_canon] closes the reconstruction:
      two values below [P] that are congruent mod [P] are equal.

    Generic over the prime [P], plain-Z arithmetic ([word i] mirrors the field
    word [zs i -F zs (S i) *F 8] as [(zs i - 8 * zs (S i)) mod P]).  Depends on
    the standard library only, so it is independent of the Garden field layer
    and the circuit proofs; the circuit-facing canonicity extraction
    discharges the [wsum 0 count < P] bound and instantiates [zs] at the
    running-sum cells. *)

Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Lists.List.
Require Import Stdlib.micromega.Lia.

Import ListNotations.
Open Scope Z_scope.

Module BaseEightReconstruct.
  Section CanonicalReconstruct.
    Context (P : Z) (HP : 8 < P).
    Variable zs : nat -> Z.

    (** The [i]-th base-8 word of the running sum, reduced mod [P]. *)
    Definition word (i : nat) : Z := (zs i - 8 * zs (S i)) mod P.

    (** Weighted base-8 sum of words [j .. j+r-1], over the integers. *)
    Fixpoint wsum (j r : nat) : Z :=
      match r with
      | O => 0
      | S r' => word j + 8 * wsum (S j) r'
      end.

    (** The mod-P telescoping.  With a vanishing tail [zs count = 0], the head
        entry is congruent mod [P] to the full weighted word sum, with no size
        hypothesis on the windows or the modulus. *)
    Lemma wsum_tail_congruent (count : nat) (Hzero : zs count = 0) :
      forall r j, (j + r = count)%nat -> wsum j r mod P = zs j mod P.
    Proof.
      induction r as [| r IH]; intros j Hj; cbn [wsum].
      - assert (j = count) by lia. subst j. rewrite Hzero. reflexivity.
      - rewrite Z.add_mod by lia.
        rewrite Z.mul_mod by lia.
        rewrite (IH (S j) ltac:(lia)).
        rewrite <- Z.mul_mod by lia.
        rewrite <- Z.add_mod by lia.
        unfold word.
        rewrite Z.add_mod_idemp_l by lia.
        f_equal. ring.
    Qed.

    (** Reconstruction from canonicity: given the vanishing tail, a reduced
        head, and the canonicity bound [wsum 0 count < P], the head equals the
        weighted word sum over the integers. *)
    Lemma reconstruct_of_canon (count : nat)
        (Hzero : zs count = 0)
        (Hhead : 0 <= zs 0 < P)
        (Hcanon : 0 <= wsum 0 count < P) :
      zs 0 = wsum 0 count.
    Proof.
      pose proof (wsum_tail_congruent count Hzero count 0 ltac:(lia)) as Hcong.
      rewrite (Z.mod_small (wsum 0 count) P Hcanon) in Hcong.
      rewrite (Z.mod_small (zs 0) P Hhead) in Hcong.
      lia.
    Qed.

    (** When its words are in [0, 8), a weighted word sum is bounded by [8^r]. *)
    Lemma wsum_bound (Hwords : forall i, 0 <= word i < 8) :
      forall r j, 0 <= wsum j r < 8 ^ Z.of_nat r.
    Proof.
      induction r as [| r IH]; intros j; cbn [wsum].
      - cbn. lia.
      - specialize (IH (S j)). specialize (Hwords j).
        rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
        lia.
    Qed.

    (** Head digit at position 0: once reconstructed, [word 0 = zs 0 mod 8]. *)
    Lemma reconstruct_digit_0 (count : nat)
        (Hzero : zs count = 0)
        (Hhead : 0 <= zs 0 < P)
        (Hwords : forall i, 0 <= word i < 8)
        (Hcanon : wsum 0 count < P) :
      (count <> 0)%nat -> word 0 = zs 0 mod 8.
    Proof.
      intro Hne.
      destruct count as [| c]; [ lia | ].
      assert (Hrec : zs 0 = wsum 0 (S c)).
      { apply (reconstruct_of_canon (S c) Hzero Hhead).
        pose proof (wsum_bound Hwords (S c) 0%nat) as Hlo. lia. }
      rewrite Hrec. cbn [wsum].
      replace (word 0 + 8 * wsum 1 c) with (word 0 + wsum 1 c * 8) by ring.
      rewrite Z_mod_plus_full.
      rewrite Z.mod_small by (apply Hwords).
      reflexivity.
    Qed.
  End CanonicalReconstruct.
End BaseEightReconstruct.
