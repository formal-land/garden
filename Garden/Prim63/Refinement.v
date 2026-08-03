(** * Refinement facts for the primitive radix-[2^63] backend

    These theorems connect the primitive carry instructions to ordinary [Z]
    arithmetic.  Consequently their assumption cone contains Rocq's standard
    [Uint63Axioms]; the executable modules themselves do not postulate any
    additional arithmetic facts. *)

From Stdlib Require Import ZArith Lia Ring.
Require Import Stdlib.Numbers.Cyclic.Int63.Uint63.
Require Import Garden.Prim63.Words.
Require Import Garden.Prim63.Montgomery.

Local Open Scope Z_scope.

Module Prim63WordsRefinement.
  Import Prim63Words.

  (** Algebraic carry cancellation used by [sweep_spec].  Keeping this fact
      independent of primitive words makes the proof cheap: [ring] only sees
      a small symbolic polynomial, rather than the expanded [Uint63] terms. *)
  Lemma cancel_sweep_carries
      (r sx a0 a1 a2 a3 a4 a5 y0 y1 y2 y3 y4
       o0 o1 o2 o3 o4 o5 c0 c1 c2 c3 c4 top : Z) :
    o0 + r * c0 = sx * y0 + a0 ->
    o1 + r * c1 = sx * y1 + a1 + c0 ->
    o2 + r * c2 = sx * y2 + a2 + c1 ->
    o3 + r * c3 = sx * y3 + a3 + c2 ->
    o4 + r * c4 = sx * y4 + a4 + c3 ->
    o5 + r * top = a5 + c4 ->
    o0 + r * (o1 + r * (o2 + r * (o3 + r * (o4 + r * o5)))) +
        r ^ 6 * top =
      a0 + r * (a1 + r * (a2 + r * (a3 + r * (a4 + r * a5)))) +
        sx * (y0 + r * (y1 + r * (y2 + r * (y3 + r * y4)))).
  Proof.
    intros E0 E1 E2 E3 E4 E5.
    replace
      (o0 + r * (o1 + r * (o2 + r * (o3 + r * (o4 + r * o5)))) +
       r ^ 6 * top)
      with
      ((o0 + r * c0) +
       r * ((o1 + r * c1) - c0) +
       r ^ 2 * ((o2 + r * c2) - c1) +
       r ^ 3 * ((o3 + r * c3) - c2) +
       r ^ 4 * ((o4 + r * c4) - c3) +
       r ^ 5 * ((o5 + r * top) - c4)) by ring.
    rewrite E0, E1, E2, E3, E4, E5.
    ring.
  Qed.

  Lemma product_plus_two_words_bound (x y z c : word) :
    Uint63.to_Z x * Uint63.to_Z y + Uint63.to_Z z + Uint63.to_Z c <
      radix * radix.
  Proof.
    pose proof (word_bounds x) as Hx.
    pose proof (word_bounds y) as Hy.
    pose proof (word_bounds z) as Hz.
    pose proof (word_bounds c) as Hc.
    pose proof radix_pos as Hr.
    nia.
  Qed.

  Lemma mac_spec (z x y c : word) :
    let '(carry, low) := mac z x y c in
    Uint63.to_Z low + radix * Uint63.to_Z carry =
      Uint63.to_Z x * Uint63.to_Z y + Uint63.to_Z z + Uint63.to_Z c.
  Proof.
    unfold mac.
    destruct (PrimInt63.mulc x y) as [hi lo] eqn:Hmul.
    pose proof (Uint63.mulc_spec x y) as M.
    rewrite Hmul in M; cbn [fst snd] in M.
    change (Uint63.to_Z x * Uint63.to_Z y =
      Uint63.to_Z hi * radix + Uint63.to_Z lo) in M.
    destruct (PrimInt63.addc lo z) as [lo1 | lo1] eqn:Hadd1;
      pose proof (Uint63.addc_spec lo z) as A1;
      rewrite Hadd1 in A1; cbn [interp_carry] in A1;
      destruct (PrimInt63.addc lo1 c) as [out | out] eqn:Hadd2;
      pose proof (Uint63.addc_spec lo1 c) as A2;
      rewrite Hadd2 in A2; cbn [interp_carry] in A2;
      pose proof (product_plus_two_words_bound x y z c) as Htotal;
      pose proof (word_bounds out) as Hout;
      pose proof radix_pos as Hr.
    - lia.
    - change (radix + Uint63.to_Z out =
        Uint63.to_Z lo1 + Uint63.to_Z c) in A2.
      assert (Hinc : Uint63.to_Z hi + 1 < radix) by nia.
      rewrite add_small_1 by exact Hinc.
      nia.
    - change (radix + Uint63.to_Z lo1 =
        Uint63.to_Z lo + Uint63.to_Z z) in A1.
      assert (Hinc : Uint63.to_Z hi + 1 < radix) by nia.
      rewrite add_small_1 by exact Hinc.
      nia.
    - change (radix + Uint63.to_Z lo1 =
        Uint63.to_Z lo + Uint63.to_Z z) in A1.
      change (radix + Uint63.to_Z out =
        Uint63.to_Z lo1 + Uint63.to_Z c) in A2.
      assert (Hinc : Uint63.to_Z hi + 2 < radix) by nia.
      rewrite add_small_2 by exact Hinc.
      nia.
  Qed.

  Lemma sweep_spec (a : words6) (x : word) (y : words5) :
    let '(r, top) := sweep a x y in
    eval6 r + radix6 * Uint63.to_Z top =
      eval6 a + Uint63.to_Z x * eval5 y.
  Proof.
    unfold sweep.
    destruct (mac (x0 a) x (w0 y) 0%uint63) as [c0 r0] eqn:H0.
    destruct (mac (x1 a) x (w1 y) c0) as [c1 r1] eqn:H1.
    destruct (mac (x2 a) x (w2 y) c1) as [c2 r2] eqn:H2.
    destruct (mac (x3 a) x (w3 y) c2) as [c3 r3] eqn:H3.
    destruct (mac (x4 a) x (w4 y) c3) as [c4 r4] eqn:H4.
    pose proof (mac_spec (x0 a) x (w0 y) 0%uint63) as S0.
    pose proof (mac_spec (x1 a) x (w1 y) c0) as S1.
    pose proof (mac_spec (x2 a) x (w2 y) c1) as S2.
    pose proof (mac_spec (x3 a) x (w3 y) c2) as S3.
    pose proof (mac_spec (x4 a) x (w4 y) c3) as S4.
    rewrite H0 in S0; cbn [fst snd] in S0.
    rewrite Uint63.to_Z_0 in S0.
    rewrite Z.add_0_r in S0.
    rewrite H1 in S1; cbn [fst snd] in S1.
    rewrite H2 in S2; cbn [fst snd] in S2.
    rewrite H3 in S3; cbn [fst snd] in S3.
    rewrite H4 in S4; cbn [fst snd] in S4.
    destruct (PrimInt63.addc (x5 a) c4) as [r5 | r5] eqn:H5;
      pose proof (Uint63.addc_spec (x5 a) c4) as S5;
      rewrite H5 in S5; cbn [interp_carry] in S5;
      unfold eval6, eval5, radix6;
      cbn [x0 x1 x2 x3 x4 x5 w0 w1 w2 w3 w4 fst snd] in S0, S1,
        S2, S3, S4, S5 |- *.
    - eapply cancel_sweep_carries.
      + exact S0.
      + exact S1.
      + exact S2.
      + exact S3.
      + exact S4.
      + rewrite Uint63.to_Z_0, Z.mul_0_r, Z.add_0_r.
        exact S5.
    - eapply cancel_sweep_carries.
      + exact S0.
      + exact S1.
      + exact S2.
      + exact S3.
      + exact S4.
      + rewrite Uint63.to_Z_1, <- S5.
        unfold radix.
        rewrite Z.mul_1_r, Z.mul_1_l.
        apply Z.add_comm.
  Qed.

End Prim63WordsRefinement.

(** Refinement of the CIOS control flow.  The statements in this module are
    deliberately phrased over [eval5]/[eval6]: they expose the exact integer
    represented by every primitive-array-free Montgomery state. *)
Module Prim63MontgomeryRefinement (C : Prim63MontgomeryConfig).
  Import Prim63Words.
  Module M := Prim63Montgomery C.

  Lemma sweep_top_le_one (a : words6) (x : word) (y : words5) :
    let '(_, top) := sweep a x y in Uint63.to_Z top <= 1.
  Proof.
    unfold sweep.
    destruct (mac (x0 a) x (w0 y) 0%uint63) as [c0 r0].
    destruct (mac (x1 a) x (w1 y) c0) as [c1 r1].
    destruct (mac (x2 a) x (w2 y) c1) as [c2 r2].
    destruct (mac (x3 a) x (w3 y) c2) as [c3 r3].
    destruct (mac (x4 a) x (w4 y) c3) as [c4 r4].
    destruct (PrimInt63.addc (x5 a) c4); cbn; lia.
  Qed.

  Lemma sweep2_spec
      (a : words6) (top x : word) (y : words5)
      (Htop : Uint63.to_Z top + 1 < radix) :
    let '(r, top') := sweep2 a top x y in
    eval6 r + radix6 * Uint63.to_Z top' =
      eval6 a + radix6 * Uint63.to_Z top + Uint63.to_Z x * eval5 y.
  Proof.
    unfold sweep2.
    destruct (sweep a x y) as [r carry] eqn:Hs.
    pose proof (Prim63WordsRefinement.sweep_spec a x y) as E.
    rewrite Hs in E; cbn [fst snd] in E |- *.
    pose proof (sweep_top_le_one a x y) as Hcarry.
    rewrite Hs in Hcarry; cbn [fst snd] in Hcarry.
    rewrite Uint63.add_spec.
    rewrite Z.mod_small.
    - nia.
    - pose proof (word_bounds top) as Htop0.
      pose proof (word_bounds carry) as Hcarry0.
      change
        (0 <= Uint63.to_Z top + Uint63.to_Z carry < radix).
      lia.
  Qed.

  Lemma shift7_spec (a : words6) (top : word) :
    radix * eval6 (shift7 a top) + Uint63.to_Z a.(x0) =
      eval6 a + radix6 * Uint63.to_Z top.
  Proof.
    destruct a as [a0 a1 a2 a3 a4 a5].
    unfold shift7, eval6, radix6.
    cbn [x0 x1 x2 x3 x4 x5].
    ring.
  Qed.

  Lemma radix_divides_radix6_mul (z : Z) :
    (radix | radix6 * z).
  Proof.
    exists (radix ^ 5 * z).
    unfold radix6.
    ring.
  Qed.

  Lemma radix_divides_eval6_tail (a : words6) :
    (radix | eval6 a - Uint63.to_Z a.(x0)).
  Proof.
    destruct a as [a0 a1 a2 a3 a4 a5].
    unfold eval6; cbn [x0 x1 x2 x3 x4 x5].
    exists
      (Uint63.to_Z a1 +
       radix * (Uint63.to_Z a2 +
       radix * (Uint63.to_Z a3 +
       radix * (Uint63.to_Z a4 + radix * Uint63.to_Z a5)))).
    ring.
  Qed.

  Lemma n0_cancels (x : word) :
    (radix |
      Uint63.to_Z x +
        Uint63.to_Z (PrimInt63.mul x C.n0_prime) *
          Uint63.to_Z C.modulus.(w0)).
  Proof.
    pose proof radix_pos as Hr.
    assert (Hr0 : radix <> 0) by lia.
    assert (Hn :
      (radix |
        Uint63.to_Z C.modulus.(w0) * Uint63.to_Z C.n0_prime + 1)).
    { apply (proj1 (Z.mod_divide _ _ Hr0)).
      exact C.n0_prime_correct. }
    assert (Hu :
      (radix |
        Uint63.to_Z x * Uint63.to_Z C.n0_prime -
          Uint63.to_Z (PrimInt63.mul x C.n0_prime))).
    { apply (proj1 (Z.mod_divide _ _ Hr0)).
      rewrite Zminus_mod.
      rewrite Uint63.mul_spec, Z.mod_mod by exact Hr0.
      rewrite Z.sub_diag, Z.mod_0_l.
      reflexivity.
      all: exact Hr0. }
    destruct Hn as [kn Hn].
    destruct Hu as [ku Hu].
    exists (Uint63.to_Z x * kn - Uint63.to_Z C.modulus.(w0) * ku).
    replace
      ((Uint63.to_Z x * kn - Uint63.to_Z C.modulus.(w0) * ku) * radix)
      with
      (Uint63.to_Z x * (kn * radix) -
       Uint63.to_Z C.modulus.(w0) * (ku * radix)) by ring.
    rewrite <- Hn, <- Hu.
    ring.
  Qed.

  Lemma radix_divides_reduction_input (s : words6) :
    let u := PrimInt63.mul s.(x0) C.n0_prime in
    (radix | eval6 s + Uint63.to_Z u * eval5 C.modulus).
  Proof.
    cbn zeta.
    pose proof (radix_divides_eval6_tail s) as Htail.
    pose proof (n0_cancels s.(x0)) as Hlow.
    destruct Htail as [kt Htail].
    destruct Hlow as [kl Hlow].
    exists
      (kt + kl +
       Uint63.to_Z (PrimInt63.mul s.(x0) C.n0_prime) *
         (radix * (Uint63.to_Z C.modulus.(w2) +
          radix * (Uint63.to_Z C.modulus.(w3) +
          radix * Uint63.to_Z C.modulus.(w4))) +
          Uint63.to_Z C.modulus.(w1))).
    unfold eval5 in *.
    nia.
  Qed.

  Definition reduction_word (b : words5) (a_i : word) (acc : words6) : word :=
    let '(s, _) := sweep acc a_i b in
    PrimInt63.mul s.(x0) C.n0_prime.

  (** One CIOS round is exact division by the word radix.  In particular,
      this proves that the low word discarded by [shift7] is zero; that fact
      is derived from [n0_prime_correct], not assumed. *)
  Lemma montgomery_step_spec (b : words5) (a_i : word) (acc : words6) :
    radix * eval6 (M.montgomery_step b a_i acc) =
      eval6 acc + Uint63.to_Z a_i * eval5 b +
      Uint63.to_Z (reduction_word b a_i acc) * eval5 C.modulus.
  Proof.
    unfold M.montgomery_step, reduction_word.
    destruct (sweep acc a_i b) as [s1 top1] eqn:H1.
    set (u := PrimInt63.mul s1.(x0) C.n0_prime).
    destruct (sweep2 s1 top1 u C.modulus) as [s2 top2] eqn:H2.
    pose proof (Prim63WordsRefinement.sweep_spec acc a_i b) as E1.
    rewrite H1 in E1; cbn [fst snd] in E1.
    pose proof (sweep_top_le_one acc a_i b) as Htop1.
    rewrite H1 in Htop1; cbn [fst snd] in Htop1.
    assert (Htop1_fit : Uint63.to_Z top1 + 1 < radix).
    { rewrite radix_value. lia. }
    pose proof (sweep2_spec s1 top1 u C.modulus Htop1_fit) as E2.
    rewrite H2 in E2; cbn [fst snd] in E2.
    pose proof (radix_divides_reduction_input s1) as Hred.
    change (radix | eval6 s1 + Uint63.to_Z u * eval5 C.modulus) in Hred.
    assert (Hs2div : (radix | eval6 s2)).
    { destruct Hred as [kred Hred].
      destruct (radix_divides_radix6_mul (Uint63.to_Z top1))
        as [ktop1 Htop1div].
      destruct (radix_divides_radix6_mul (Uint63.to_Z top2))
        as [ktop2 Htop2div].
      exists (kred + ktop1 - ktop2).
      replace ((kred + ktop1 - ktop2) * radix) with
        (kred * radix + ktop1 * radix - ktop2 * radix) by ring.
      rewrite <- Hred, <- Htop1div, <- Htop2div.
      nia. }
    assert (Hlow : Uint63.to_Z s2.(x0) = 0).
    { pose proof (radix_divides_eval6_tail s2) as Htail.
      assert (Hxdiv : (radix | Uint63.to_Z s2.(x0))).
      { destruct Hs2div as [ks Hs2div].
        destruct Htail as [kt Htail].
        exists (ks - kt).
        nia. }
      assert (Hr0 : radix <> 0) by (pose proof radix_pos; lia).
      pose proof (proj2 (Z.mod_divide _ _ Hr0) Hxdiv) as Hmod.
      rewrite Z.mod_small in Hmod.
      - exact Hmod.
      - apply word_bounds. }
    pose proof (shift7_spec s2 top2) as Eshift.
    rewrite Hlow, Z.add_0_r in Eshift.
    fold u in E1, E2, Eshift |- *.
    nia.
  Qed.

  Corollary montgomery_step_congruent
      (b : words5) (a_i : word) (acc : words6) :
    (radix * eval6 (M.montgomery_step b a_i acc)) mod C.modulus_Z =
      (eval6 acc + Uint63.to_Z a_i * eval5 b) mod C.modulus_Z.
  Proof.
    assert (Hm0 : C.modulus_Z <> 0) by
      (pose proof C.modulus_positive; lia).
    rewrite montgomery_step_spec, C.modulus_words_correct.
    rewrite Z.add_mod by exact Hm0.
    rewrite Z.mul_mod by exact Hm0.
    rewrite Z.mod_same by exact Hm0.
    rewrite Z.mul_0_r, Z.mod_0_l, Z.add_0_r.
    rewrite Z.mod_mod by exact Hm0.
    reflexivity.
    all: exact Hm0.
  Qed.

  Definition montgomery_steps (a b : words5) : words6 :=
    let s1 := M.montgomery_step b a.(w0) zero6 in
    let s2 := M.montgomery_step b a.(w1) s1 in
    let s3 := M.montgomery_step b a.(w2) s2 in
    let s4 := M.montgomery_step b a.(w3) s3 in
    M.montgomery_step b a.(w4) s4.

  Lemma montgomery_reduce_unfold (a b : words5) :
    M.montgomery_reduce a b = M.reduce_once (low5 (montgomery_steps a b)).
  Proof. reflexivity. Qed.

  (** The five CIOS rounds compute the unreduced Montgomery product exactly,
      up to an explicit integer multiple of the modulus.  This theorem does
      not require canonical inputs. *)
  Lemma montgomery_steps_spec (a b : words5) :
    exists k : Z,
      radix5 * eval6 (montgomery_steps a b) =
        eval5 a * eval5 b + k * C.modulus_Z.
  Proof.
    destruct a as [a0 a1 a2 a3 a4].
    cbn [montgomery_steps w0 w1 w2 w3 w4].
    set (s1 := M.montgomery_step b a0 zero6).
    set (s2 := M.montgomery_step b a1 s1).
    set (s3 := M.montgomery_step b a2 s2).
    set (s4 := M.montgomery_step b a3 s3).
    set (s5 := M.montgomery_step b a4 s4).
    set (k1 := Uint63.to_Z (reduction_word b a0 zero6)).
    set (k2 := Uint63.to_Z (reduction_word b a1 s1)).
    set (k3 := Uint63.to_Z (reduction_word b a2 s2)).
    set (k4 := Uint63.to_Z (reduction_word b a3 s3)).
    set (k5 := Uint63.to_Z (reduction_word b a4 s4)).
    pose proof (montgomery_step_spec b a0 zero6) as E1.
    pose proof (montgomery_step_spec b a1 s1) as E2.
    pose proof (montgomery_step_spec b a2 s2) as E3.
    pose proof (montgomery_step_spec b a3 s3) as E4.
    pose proof (montgomery_step_spec b a4 s4) as E5.
    change
      (radix * eval6 s1 = eval6 zero6 + Uint63.to_Z a0 * eval5 b +
       k1 * eval5 C.modulus) in E1.
    change
      (radix * eval6 s2 = eval6 s1 + Uint63.to_Z a1 * eval5 b +
       k2 * eval5 C.modulus) in E2.
    change
      (radix * eval6 s3 = eval6 s2 + Uint63.to_Z a2 * eval5 b +
       k3 * eval5 C.modulus) in E3.
    change
      (radix * eval6 s4 = eval6 s3 + Uint63.to_Z a3 * eval5 b +
       k4 * eval5 C.modulus) in E4.
    change
      (radix * eval6 s5 = eval6 s4 + Uint63.to_Z a4 * eval5 b +
       k5 * eval5 C.modulus) in E5.
    exists (k1 + radix * k2 + radix ^ 2 * k3 +
      radix ^ 3 * k4 + radix ^ 4 * k5).
    change
      (radix5 * eval6 s5 =
       eval5
         {| w0 := a0; w1 := a1; w2 := a2; w3 := a3; w4 := a4 |} *
         eval5 b +
       (k1 + radix * k2 + radix ^ 2 * k3 +
        radix ^ 3 * k4 + radix ^ 4 * k5) * C.modulus_Z).
    rewrite <- C.modulus_words_correct.
    unfold radix5.
    cbn [eval6 zero6 x0 x1 x2 x3 x4 x5] in E1.
    ring_simplify in E1.
    replace (radix ^ 5 * eval6 s5) with
      (radix ^ 4 * (radix * eval6 s5)) by ring.
    rewrite E5.
    replace
      (radix ^ 4 *
       (eval6 s4 + Uint63.to_Z a4 * eval5 b + k5 * eval5 C.modulus))
      with
      (radix ^ 3 * (radix * eval6 s4) +
       radix ^ 4 * Uint63.to_Z a4 * eval5 b +
       radix ^ 4 * k5 * eval5 C.modulus) by ring.
    rewrite E4.
    replace
      (radix ^ 3 *
       (eval6 s3 + Uint63.to_Z a3 * eval5 b + k4 * eval5 C.modulus) +
       radix ^ 4 * Uint63.to_Z a4 * eval5 b +
       radix ^ 4 * k5 * eval5 C.modulus)
      with
      (radix ^ 2 * (radix * eval6 s3) +
       radix ^ 3 * Uint63.to_Z a3 * eval5 b +
       radix ^ 3 * k4 * eval5 C.modulus +
       radix ^ 4 * Uint63.to_Z a4 * eval5 b +
       radix ^ 4 * k5 * eval5 C.modulus) by ring.
    rewrite E3.
    replace
      (radix ^ 2 *
       (eval6 s2 + Uint63.to_Z a2 * eval5 b + k3 * eval5 C.modulus) +
       radix ^ 3 * Uint63.to_Z a3 * eval5 b +
       radix ^ 3 * k4 * eval5 C.modulus +
       radix ^ 4 * Uint63.to_Z a4 * eval5 b +
       radix ^ 4 * k5 * eval5 C.modulus)
      with
      (radix * (radix * eval6 s2) +
       radix ^ 2 * Uint63.to_Z a2 * eval5 b +
       radix ^ 2 * k3 * eval5 C.modulus +
       radix ^ 3 * Uint63.to_Z a3 * eval5 b +
       radix ^ 3 * k4 * eval5 C.modulus +
       radix ^ 4 * Uint63.to_Z a4 * eval5 b +
       radix ^ 4 * k5 * eval5 C.modulus) by ring.
    rewrite E2.
    replace
      (radix *
       (eval6 s1 + Uint63.to_Z a1 * eval5 b + k2 * eval5 C.modulus) +
       radix ^ 2 * Uint63.to_Z a2 * eval5 b +
       radix ^ 2 * k3 * eval5 C.modulus +
       radix ^ 3 * Uint63.to_Z a3 * eval5 b +
       radix ^ 3 * k4 * eval5 C.modulus +
       radix ^ 4 * Uint63.to_Z a4 * eval5 b +
       radix ^ 4 * k5 * eval5 C.modulus)
      with
      ((radix * eval6 s1) +
       radix * Uint63.to_Z a1 * eval5 b +
       radix * k2 * eval5 C.modulus +
       radix ^ 2 * Uint63.to_Z a2 * eval5 b +
       radix ^ 2 * k3 * eval5 C.modulus +
       radix ^ 3 * Uint63.to_Z a3 * eval5 b +
       radix ^ 3 * k4 * eval5 C.modulus +
       radix ^ 4 * Uint63.to_Z a4 * eval5 b +
       radix ^ 4 * k5 * eval5 C.modulus) by ring.
    rewrite E1.
    unfold eval5; cbn [w0 w1 w2 w3 w4].
    unfold eval6, zero6; cbn [x0 x1 x2 x3 x4 x5].
    rewrite Uint63.to_Z_0.
    ring.
  Qed.

  Corollary montgomery_steps_congruent (a b : words5) :
    (radix5 * eval6 (montgomery_steps a b)) mod C.modulus_Z =
      (eval5 a * eval5 b) mod C.modulus_Z.
  Proof.
    destruct (montgomery_steps_spec a b) as [k E].
    rewrite E.
    assert (Hm0 : C.modulus_Z <> 0) by
      (pose proof C.modulus_positive; lia).
    rewrite Z.add_mod by exact Hm0.
    rewrite Z.mod_mul by exact Hm0.
    rewrite Z.add_0_r, Z.mod_mod by exact Hm0.
    reflexivity.
    all: exact Hm0.
  Qed.

  Lemma montgomery_step_bound
      (b : words5) (a_i : word) (acc : words6)
      (Hacc : eval6 acc < 2 * C.modulus_Z)
      (Hb : eval5 b < C.modulus_Z) :
    eval6 (M.montgomery_step b a_i acc) < 2 * C.modulus_Z.
  Proof.
    pose proof (montgomery_step_spec b a_i acc) as E.
    pose proof (eval6_bounds acc) as Hacc0.
    pose proof (eval6_bounds (M.montgomery_step b a_i acc)) as Hout0.
    pose proof (eval5_bounds b) as Hb0.
    pose proof (word_bounds a_i) as Hai.
    pose proof (word_bounds (reduction_word b a_i acc)) as Hu.
    pose proof radix_pos as Hr.
    pose proof C.modulus_positive as Hm.
    rewrite C.modulus_words_correct in E.
    nia.
  Qed.

  Lemma montgomery_steps_bound
      (a b : words5) (Hb : eval5 b < C.modulus_Z) :
    eval6 (montgomery_steps a b) < 2 * C.modulus_Z.
  Proof.
    destruct a as [a0 a1 a2 a3 a4].
    cbn [montgomery_steps w0 w1 w2 w3 w4].
    set (s1 := M.montgomery_step b a0 zero6).
    set (s2 := M.montgomery_step b a1 s1).
    set (s3 := M.montgomery_step b a2 s2).
    set (s4 := M.montgomery_step b a3 s3).
    assert (Hzero : eval6 zero6 < 2 * C.modulus_Z).
    { unfold eval6, zero6; cbn [x0 x1 x2 x3 x4 x5].
      rewrite Uint63.to_Z_0.
      pose proof C.modulus_positive; nia. }
    pose proof (montgomery_step_bound b a0 zero6 Hzero Hb) as H1.
    change (eval6 s1 < 2 * C.modulus_Z) in H1.
    pose proof (montgomery_step_bound b a1 s1 H1 Hb) as H2.
    change (eval6 s2 < 2 * C.modulus_Z) in H2.
    pose proof (montgomery_step_bound b a2 s2 H2 Hb) as H3.
    change (eval6 s3 < 2 * C.modulus_Z) in H3.
    pose proof (montgomery_step_bound b a3 s3 H3 Hb) as H4.
    change (eval6 s4 < 2 * C.modulus_Z) in H4.
    exact (montgomery_step_bound b a4 s4 H4 Hb).
  Qed.

  Lemma montgomery_steps_high_zero
      (a b : words5) (Hb : eval5 b < C.modulus_Z) :
    Uint63.to_Z (montgomery_steps a b).(x5) = 0.
  Proof.
    pose proof (montgomery_steps_bound a b Hb) as Hbound.
    pose proof (eval_low5 (montgomery_steps a b)) as Elow.
    pose proof (eval5_bounds (low5 (montgomery_steps a b))) as Hlow.
    pose proof (word_bounds (montgomery_steps a b).(x5)) as Hhigh.
    pose proof C.twice_modulus_fits as Hfit.
    pose proof radix_pos as Hr.
    unfold radix5 in *.
    nia.
  Qed.

  Lemma montgomery_steps_low5
      (a b : words5) (Hb : eval5 b < C.modulus_Z) :
    eval5 (low5 (montgomery_steps a b)) = eval6 (montgomery_steps a b).
  Proof.
    pose proof (eval_low5 (montgomery_steps a b)) as E.
    rewrite (montgomery_steps_high_zero a b Hb) in E.
    ring_simplify in E.
    lia.
  Qed.

  Lemma equal_sound (a b : words5) :
    M.equal a b = true -> eval5 a = eval5 b.
  Proof.
    destruct a as [a0 a1 a2 a3 a4].
    destruct b as [b0 b1 b2 b3 b4].
    intro H.
    unfold M.equal in H; cbn [w0 w1 w2 w3 w4] in H.
    apply Bool.andb_true_iff in H; destruct H as [E0 H].
    apply Bool.andb_true_iff in H; destruct H as [E1 H].
    apply Bool.andb_true_iff in H; destruct H as [E2 H].
    apply Bool.andb_true_iff in H; destruct H as [E3 E4].
    apply Uint63.eqb_spec in E0.
    apply Uint63.eqb_spec in E1.
    apply Uint63.eqb_spec in E2.
    apply Uint63.eqb_spec in E3.
    apply Uint63.eqb_spec in E4.
    subst.
    reflexivity.
  Qed.

  Lemma less_than_sound (a b : words5) :
    M.less_than a b = true -> eval5 a < eval5 b.
  Proof.
    destruct a as [a0 a1 a2 a3 a4].
    destruct b as [b0 b1 b2 b3 b4].
    unfold M.less_than; cbn [w0 w1 w2 w3 w4].
    Ltac solve_lex a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 :=
      let Hlt := fresh "Hlt" in
      intro Hlt; apply Uint63.ltb_spec in Hlt;
      unfold eval5; cbn [w0 w1 w2 w3 w4];
      pose proof (word_bounds a0); pose proof (word_bounds a1);
      pose proof (word_bounds a2); pose proof (word_bounds a3);
      pose proof (word_bounds a4); pose proof (word_bounds b0);
      pose proof (word_bounds b1); pose proof (word_bounds b2);
      pose proof (word_bounds b3); pose proof (word_bounds b4);
      rewrite radix_value in *; nia.
    destruct (PrimInt63.eqb a4 b4) eqn:E4.
    - apply Uint63.eqb_spec in E4; subst b4.
      destruct (PrimInt63.eqb a3 b3) eqn:E3.
      + apply Uint63.eqb_spec in E3; subst b3.
        destruct (PrimInt63.eqb a2 b2) eqn:E2.
        * apply Uint63.eqb_spec in E2; subst b2.
          destruct (PrimInt63.eqb a1 b1) eqn:E1.
          -- apply Uint63.eqb_spec in E1; subst b1.
             solve_lex a0 a1 a2 a3 a4 b0 a1 a2 a3 a4.
          -- solve_lex a0 a1 a2 a3 a4 b0 b1 a2 a3 a4.
        * solve_lex a0 a1 a2 a3 a4 b0 b1 b2 a3 a4.
      + solve_lex a0 a1 a2 a3 a4 b0 b1 b2 b3 a4.
    - solve_lex a0 a1 a2 a3 a4 b0 b1 b2 b3 b4.
  Qed.

  Lemma less_equal_sound (a b : words5) :
    M.less_equal a b = true -> eval5 a <= eval5 b.
  Proof.
    unfold M.less_equal.
    rewrite Bool.orb_true_iff.
    intros [Hlt | Heq].
    - apply less_than_sound in Hlt; lia.
    - apply equal_sound in Heq; lia.
  Qed.

  Definition borrow_Z (b : bool) : Z := if b then 1 else 0.

  Lemma sub_step_spec (a b : word) (borrow : bool) :
    let '(r, borrow') := M.sub_step a b borrow in
    Uint63.to_Z r - radix * borrow_Z borrow' =
      Uint63.to_Z a - Uint63.to_Z b - borrow_Z borrow.
  Proof.
    unfold M.sub_step, borrow_Z.
    destruct borrow.
    - destruct (PrimInt63.subcarryc a b) as [r | r] eqn:E;
        pose proof (Uint63.subcarryc_spec a b) as S;
        rewrite E in S; cbn [interp_carry fst snd] in S |- *;
        unfold radix in *; lia.
    - destruct (PrimInt63.subc a b) as [r | r] eqn:E;
        pose proof (Uint63.subc_spec a b) as S;
        rewrite E in S; cbn [interp_carry fst snd] in S |- *;
        unfold radix in *; lia.
  Qed.

  Lemma sub_raw_spec (a b : words5) :
    let '(r, borrow) := M.sub_raw a b in
    eval5 r - radix5 * borrow_Z borrow = eval5 a - eval5 b.
  Proof.
    destruct a as [a0 a1 a2 a3 a4].
    destruct b as [b0 b1 b2 b3 b4].
    unfold M.sub_raw; cbn [w0 w1 w2 w3 w4].
    destruct (M.sub_step a0 b0 false) as [r0 c0] eqn:E0.
    destruct (M.sub_step a1 b1 c0) as [r1 c1] eqn:E1.
    destruct (M.sub_step a2 b2 c1) as [r2 c2] eqn:E2.
    destruct (M.sub_step a3 b3 c2) as [r3 c3] eqn:E3.
    destruct (M.sub_step a4 b4 c3) as [r4 c4] eqn:E4.
    pose proof (sub_step_spec a0 b0 false) as S0.
    pose proof (sub_step_spec a1 b1 c0) as S1.
    pose proof (sub_step_spec a2 b2 c1) as S2.
    pose proof (sub_step_spec a3 b3 c2) as S3.
    pose proof (sub_step_spec a4 b4 c3) as S4.
    rewrite E0 in S0; cbn [fst snd borrow_Z] in S0.
    rewrite E1 in S1; cbn [fst snd] in S1.
    rewrite E2 in S2; cbn [fst snd] in S2.
    rewrite E3 in S3; cbn [fst snd] in S3.
    rewrite E4 in S4; cbn [fst snd] in S4 |- *.
    assert (T1 : Uint63.to_Z r1 - radix * borrow_Z c1 + borrow_Z c0 =
      Uint63.to_Z a1 - Uint63.to_Z b1) by lia.
    assert (T2 : Uint63.to_Z r2 - radix * borrow_Z c2 + borrow_Z c1 =
      Uint63.to_Z a2 - Uint63.to_Z b2) by lia.
    assert (T3 : Uint63.to_Z r3 - radix * borrow_Z c3 + borrow_Z c2 =
      Uint63.to_Z a3 - Uint63.to_Z b3) by lia.
    assert (T4 : Uint63.to_Z r4 - radix * borrow_Z c4 + borrow_Z c3 =
      Uint63.to_Z a4 - Uint63.to_Z b4) by lia.
    unfold eval5, radix5; cbn [w0 w1 w2 w3 w4].
    replace
      (Uint63.to_Z r0 +
       radix * (Uint63.to_Z r1 +
       radix * (Uint63.to_Z r2 +
       radix * (Uint63.to_Z r3 + radix * Uint63.to_Z r4))) -
       radix ^ 5 * borrow_Z c4)
      with
      ((Uint63.to_Z r0 - radix * borrow_Z c0) +
       radix * (Uint63.to_Z r1 - radix * borrow_Z c1 + borrow_Z c0) +
       radix ^ 2 * (Uint63.to_Z r2 - radix * borrow_Z c2 + borrow_Z c1) +
       radix ^ 3 * (Uint63.to_Z r3 - radix * borrow_Z c3 + borrow_Z c2) +
       radix ^ 4 * (Uint63.to_Z r4 - radix * borrow_Z c4 + borrow_Z c3))
      by ring.
    rewrite S0, T1, T2, T3, T4.
    ring.
  Qed.

  Lemma sub_raw_no_borrow (a b : words5) (Hle : eval5 b <= eval5 a) :
    exists r : words5,
      M.sub_raw a b = (r, false) /\ eval5 r = eval5 a - eval5 b.
  Proof.
    destruct (M.sub_raw a b) as [r borrow] eqn:Eraw.
    pose proof (sub_raw_spec a b) as E.
    rewrite Eraw in E; cbn [fst snd] in E.
    destruct borrow.
    - cbn [borrow_Z] in E.
      pose proof (eval5_bounds r) as Hr.
      nia.
    - exists r; split; [reflexivity |].
      cbn [borrow_Z] in E.
      nia.
  Qed.

  Lemma subtract_modulus_spec (a : words5)
      (Hcmp : M.less_equal C.modulus a = true) :
    eval5 (M.subtract_modulus a) = eval5 a - C.modulus_Z.
  Proof.
    pose proof (less_equal_sound C.modulus a Hcmp) as Hle.
    destruct (sub_raw_no_borrow a C.modulus Hle) as [r [Eraw Er]].
    unfold M.subtract_modulus.
    rewrite Eraw; cbn [fst].
    rewrite Er, C.modulus_words_correct.
    reflexivity.
  Qed.

  Lemma reduce_once_spec (a : words5) :
    exists q : Z,
      eval5 (M.reduce_once a) = eval5 a - q * C.modulus_Z.
  Proof.
    unfold M.reduce_once.
    destruct (M.less_equal C.modulus a) eqn:Hcmp.
    - exists 1. rewrite (subtract_modulus_spec a Hcmp). ring.
    - exists 0. ring.
  Qed.

  Corollary reduce_once_congruent (a : words5) :
    eval5 (M.reduce_once a) mod C.modulus_Z = eval5 a mod C.modulus_Z.
  Proof.
    destruct (reduce_once_spec a) as [q E].
    rewrite E.
    assert (Hm0 : C.modulus_Z <> 0) by
      (pose proof C.modulus_positive; lia).
    rewrite Zminus_mod, Z.mod_mul by exact Hm0.
    rewrite Z.sub_0_r, Z.mod_mod by exact Hm0.
    reflexivity.
    all: exact Hm0.
  Qed.

  (** End-to-end modular correctness of the executable multiplication.  The
      sole range hypothesis is the normal field invariant on the second
      operand; multiplication is commutative at the specification level, but
      the CIOS bound uses the operand held fixed across its five sweeps. *)
  Theorem montgomery_reduce_congruent
      (a b : words5) (Hb : eval5 b < C.modulus_Z) :
    (radix5 * eval5 (M.montgomery_reduce a b)) mod C.modulus_Z =
      (eval5 a * eval5 b) mod C.modulus_Z.
  Proof.
    rewrite montgomery_reduce_unfold.
    destruct (reduce_once_spec (low5 (montgomery_steps a b))) as [q Ered].
    rewrite Ered, (montgomery_steps_low5 a b Hb).
    destruct (montgomery_steps_spec a b) as [k Esteps].
    replace
      (radix5 * (eval6 (montgomery_steps a b) - q * C.modulus_Z))
      with
      (radix5 * eval6 (montgomery_steps a b) +
       (- radix5 * q) * C.modulus_Z) by ring.
    rewrite Esteps.
    replace
      (eval5 a * eval5 b + k * C.modulus_Z +
       (- radix5 * q) * C.modulus_Z)
      with
      (eval5 a * eval5 b + (k - radix5 * q) * C.modulus_Z) by ring.
    assert (Hm0 : C.modulus_Z <> 0) by
      (pose proof C.modulus_positive; lia).
    rewrite Z.add_mod by exact Hm0.
    rewrite Z.mod_mul by exact Hm0.
    rewrite Z.add_0_r, Z.mod_mod by exact Hm0.
    reflexivity.
    all: exact Hm0.
  Qed.

  Corollary mul_congruent
      (a b : M.t) (Hb : M.canonical b) :
    (radix5 * eval5 (M.mul a b)) mod C.modulus_Z =
      (eval5 a * eval5 b) mod C.modulus_Z.
  Proof.
    exact (montgomery_reduce_congruent a b Hb).
  Qed.

  Lemma mod_mul_compat (x x' y y' : Z)
      (Hx : x mod C.modulus_Z = x' mod C.modulus_Z)
      (Hy : y mod C.modulus_Z = y' mod C.modulus_Z) :
    (x * y) mod C.modulus_Z = (x' * y') mod C.modulus_Z.
  Proof.
    assert (Hm0 : C.modulus_Z <> 0) by
      (pose proof C.modulus_positive; lia).
    rewrite (Z.mul_mod x y C.modulus_Z Hm0).
    rewrite (Z.mul_mod x' y' C.modulus_Z Hm0).
    rewrite Hx, Hy.
    reflexivity.
  Qed.

  (** Semantic multiplication for Montgomery-denoted values.  This closes the
      refinement chain from the five primitive-word sweeps through the final
      conditional subtraction. *)
  Theorem mul_denote (a b : M.t) (Hb : M.canonical b) :
    M.denote (M.mul a b) =
      (M.denote a * M.denote b) mod C.modulus_Z.
  Proof.
    unfold M.denote.
    pose proof (mul_congruent a b Hb) as Hmul.
    pose proof C.r_inverse_correct as Hinv.
    pose proof C.modulus_positive as Hm.
    assert (Hm0 : C.modulus_Z <> 0) by lia.
    assert (Hm1 : 1 < C.modulus_Z).
    { pose proof
        (Z.mod_pos_bound (radix5 * C.r_inverse_Z) C.modulus_Z Hm) as Hbound.
      rewrite Hinv in Hbound.
      lia. }
    assert (Hone :
      1 mod C.modulus_Z =
        (radix5 * C.r_inverse_Z) mod C.modulus_Z).
    { rewrite Hinv, Z.mod_small; lia. }
    assert (Hleft :
      (eval5 (M.mul a b) * C.r_inverse_Z) mod C.modulus_Z =
      ((radix5 * eval5 (M.mul a b)) *
       (C.r_inverse_Z * C.r_inverse_Z)) mod C.modulus_Z).
    { pose proof
        (mod_mul_compat
          (eval5 (M.mul a b) * C.r_inverse_Z)
          (eval5 (M.mul a b) * C.r_inverse_Z)
          1 (radix5 * C.r_inverse_Z) eq_refl Hone) as E.
      replace
        ((eval5 (M.mul a b) * C.r_inverse_Z) * 1)
        with (eval5 (M.mul a b) * C.r_inverse_Z) in E by ring.
      replace
        ((eval5 (M.mul a b) * C.r_inverse_Z) *
         (radix5 * C.r_inverse_Z))
        with
        ((radix5 * eval5 (M.mul a b)) *
         (C.r_inverse_Z * C.r_inverse_Z)) in E by ring.
      exact E. }
    assert (Hscaled :
      ((radix5 * eval5 (M.mul a b)) *
       (C.r_inverse_Z * C.r_inverse_Z)) mod C.modulus_Z =
      ((eval5 a * eval5 b) *
       (C.r_inverse_Z * C.r_inverse_Z)) mod C.modulus_Z).
    { apply mod_mul_compat; [exact Hmul | reflexivity]. }
    rewrite Hleft, Hscaled.
    replace
      ((eval5 a * eval5 b) * (C.r_inverse_Z * C.r_inverse_Z))
      with
      ((eval5 a * C.r_inverse_Z) *
       (eval5 b * C.r_inverse_Z)) by ring.
    rewrite Z.mul_mod by exact Hm0.
    reflexivity.
    all: exact Hm0.
  Qed.

End Prim63MontgomeryRefinement.
