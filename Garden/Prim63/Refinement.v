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

  Lemma eval5_inj (a b : words5) :
    eval5 a = eval5 b -> a = b.
  Proof.
    destruct a as [a0 a1 a2 a3 a4].
    destruct b as [b0 b1 b2 b3 b4].
    intro E.
    pose proof (word_bounds a0) as Ha0.
    pose proof (word_bounds a1) as Ha1.
    pose proof (word_bounds a2) as Ha2.
    pose proof (word_bounds a3) as Ha3.
    pose proof (word_bounds a4) as Ha4.
    pose proof (word_bounds b0) as Hb0.
    pose proof (word_bounds b1) as Hb1.
    pose proof (word_bounds b2) as Hb2.
    pose proof (word_bounds b3) as Hb3.
    pose proof (word_bounds b4) as Hb4.
    unfold eval5 in E; cbn [w0 w1 w2 w3 w4] in E.
    rewrite radix_value in E, Ha0, Ha1, Ha2, Ha3, Ha4,
      Hb0, Hb1, Hb2, Hb3, Hb4.
    assert (E4 : Uint63.to_Z a4 = Uint63.to_Z b4) by nia.
    assert (E3 : Uint63.to_Z a3 = Uint63.to_Z b3) by nia.
    assert (E2 : Uint63.to_Z a2 = Uint63.to_Z b2) by nia.
    assert (E1 : Uint63.to_Z a1 = Uint63.to_Z b1) by nia.
    assert (E0 : Uint63.to_Z a0 = Uint63.to_Z b0) by nia.
    apply Uint63.to_Z_inj in E0.
    apply Uint63.to_Z_inj in E1.
    apply Uint63.to_Z_inj in E2.
    apply Uint63.to_Z_inj in E3.
    apply Uint63.to_Z_inj in E4.
    subst; reflexivity.
  Qed.

  Lemma equal_spec (a b : words5) :
    M.equal a b = true <-> a = b.
  Proof.
    split.
    - intro H.
      apply eval5_inj.
      exact (equal_sound a b H).
    - intros ->.
      unfold M.equal.
      repeat rewrite Uint63.eqb_refl.
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

  Lemma word_ltb_false_ge (a b : word) :
    PrimInt63.ltb a b = false -> Uint63.to_Z b <= Uint63.to_Z a.
  Proof.
    intros Hfalse.
    destruct (Z_lt_ge_dec (Uint63.to_Z a) (Uint63.to_Z b)) as [Hlt | Hge].
    - apply Uint63.ltb_spec in Hlt.
      rewrite Hlt in Hfalse.
      discriminate.
    - lia.
  Qed.

  Lemma word_eqb_false_neq (a b : word) :
    PrimInt63.eqb a b = false -> Uint63.to_Z a <> Uint63.to_Z b.
  Proof.
    intros Hfalse Heq.
    apply Uint63.to_Z_inj in Heq.
    subst b.
    rewrite Uint63.eqb_refl in Hfalse.
    discriminate.
  Qed.

  Lemma less_than_complete (a b : words5) :
    eval5 a < eval5 b -> M.less_than a b = true.
  Proof.
    destruct a as [a0 a1 a2 a3 a4].
    destruct b as [b0 b1 b2 b3 b4].
    unfold M.less_than; cbn [w0 w1 w2 w3 w4].
    intro H.
    pose proof (word_bounds a0) as Ha0.
    pose proof (word_bounds a1) as Ha1.
    pose proof (word_bounds a2) as Ha2.
    pose proof (word_bounds a3) as Ha3.
    pose proof (word_bounds a4) as Ha4.
    pose proof (word_bounds b0) as Hb0.
    pose proof (word_bounds b1) as Hb1.
    pose proof (word_bounds b2) as Hb2.
    pose proof (word_bounds b3) as Hb3.
    pose proof (word_bounds b4) as Hb4.
    unfold eval5 in H; cbn [w0 w1 w2 w3 w4] in H.
    rewrite radix_value in H, Ha0, Ha1, Ha2, Ha3, Ha4,
      Hb0, Hb1, Hb2, Hb3, Hb4.
    destruct (PrimInt63.eqb a4 b4) eqn:E4.
    - apply Uint63.eqb_spec in E4; subst b4.
      destruct (PrimInt63.eqb a3 b3) eqn:E3.
      + apply Uint63.eqb_spec in E3; subst b3.
        destruct (PrimInt63.eqb a2 b2) eqn:E2.
        * apply Uint63.eqb_spec in E2; subst b2.
          destruct (PrimInt63.eqb a1 b1) eqn:E1.
          -- apply Uint63.eqb_spec in E1; subst b1.
             apply Uint63.ltb_spec. nia.
          -- destruct (PrimInt63.ltb a1 b1) eqn:L1; [reflexivity |].
             pose proof (word_ltb_false_ge a1 b1 L1).
             pose proof (word_eqb_false_neq a1 b1 E1).
             exfalso; nia.
        * destruct (PrimInt63.ltb a2 b2) eqn:L2; [reflexivity |].
          pose proof (word_ltb_false_ge a2 b2 L2).
          pose proof (word_eqb_false_neq a2 b2 E2).
          exfalso; nia.
      + destruct (PrimInt63.ltb a3 b3) eqn:L3; [reflexivity |].
        pose proof (word_ltb_false_ge a3 b3 L3).
        pose proof (word_eqb_false_neq a3 b3 E3).
        exfalso; nia.
    - destruct (PrimInt63.ltb a4 b4) eqn:L4; [reflexivity |].
      pose proof (word_ltb_false_ge a4 b4 L4).
      pose proof (word_eqb_false_neq a4 b4 E4).
      exfalso; nia.
  Qed.

  Lemma less_than_spec (a b : words5) :
    M.less_than a b = true <-> eval5 a < eval5 b.
  Proof.
    split; [apply less_than_sound | apply less_than_complete].
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

  Lemma less_equal_spec (a b : words5) :
    M.less_equal a b = true <-> eval5 a <= eval5 b.
  Proof.
    split; [apply less_equal_sound |].
    intro Hle.
    destruct (proj1 (Z.lt_eq_cases (eval5 a) (eval5 b)) Hle)
      as [Hlt | Heq].
    - unfold M.less_equal.
      apply Bool.orb_true_iff; left.
      exact (less_than_complete a b Hlt).
    - unfold M.less_equal.
      apply Bool.orb_true_iff; right.
      apply (proj2 (equal_spec a b)).
      apply eval5_inj.
      exact Heq.
  Qed.

  Definition borrow_Z (b : bool) : Z := if b then 1 else 0.

  Definition carry_Z (b : bool) : Z := if b then 1 else 0.

  Lemma add_step_spec (a b : word) (carry : bool) :
    let '(r, carry') := M.add_step a b carry in
    Uint63.to_Z r + radix * carry_Z carry' =
      Uint63.to_Z a + Uint63.to_Z b + carry_Z carry.
  Proof.
    unfold M.add_step, carry_Z.
    destruct carry.
    - destruct (PrimInt63.addcarryc a b) as [r | r] eqn:E;
        pose proof (Uint63.addcarryc_spec a b) as S;
        rewrite E in S; cbn [interp_carry fst snd] in S |- *;
        unfold radix in *; lia.
    - destruct (PrimInt63.addc a b) as [r | r] eqn:E;
        pose proof (Uint63.addc_spec a b) as S;
        rewrite E in S; cbn [interp_carry fst snd] in S |- *;
        unfold radix in *; lia.
  Qed.

  Lemma add_raw_spec (a b : words5) :
    let '(r, carry) := M.add_raw a b in
    eval5 r + radix5 * carry_Z carry = eval5 a + eval5 b.
  Proof.
    destruct a as [a0 a1 a2 a3 a4].
    destruct b as [b0 b1 b2 b3 b4].
    unfold M.add_raw; cbn [w0 w1 w2 w3 w4].
    destruct (M.add_step a0 b0 false) as [r0 c0] eqn:E0.
    destruct (M.add_step a1 b1 c0) as [r1 c1] eqn:E1.
    destruct (M.add_step a2 b2 c1) as [r2 c2] eqn:E2.
    destruct (M.add_step a3 b3 c2) as [r3 c3] eqn:E3.
    destruct (M.add_step a4 b4 c3) as [r4 c4] eqn:E4.
    pose proof (add_step_spec a0 b0 false) as S0.
    pose proof (add_step_spec a1 b1 c0) as S1.
    pose proof (add_step_spec a2 b2 c1) as S2.
    pose proof (add_step_spec a3 b3 c2) as S3.
    pose proof (add_step_spec a4 b4 c3) as S4.
    rewrite E0 in S0; cbn [fst snd carry_Z] in S0.
    rewrite E1 in S1; cbn [fst snd] in S1.
    rewrite E2 in S2; cbn [fst snd] in S2.
    rewrite E3 in S3; cbn [fst snd] in S3.
    rewrite E4 in S4; cbn [fst snd] in S4 |- *.
    unfold eval5, radix5; cbn [w0 w1 w2 w3 w4].
    replace
      (Uint63.to_Z r0 +
       radix * (Uint63.to_Z r1 +
       radix * (Uint63.to_Z r2 +
       radix * (Uint63.to_Z r3 + radix * Uint63.to_Z r4))) +
       radix ^ 5 * carry_Z c4)
      with
      ((Uint63.to_Z r0 + radix * carry_Z c0) +
       radix * (Uint63.to_Z r1 + radix * carry_Z c1 - carry_Z c0) +
       radix ^ 2 *
         (Uint63.to_Z r2 + radix * carry_Z c2 - carry_Z c1) +
       radix ^ 3 *
         (Uint63.to_Z r3 + radix * carry_Z c3 - carry_Z c2) +
       radix ^ 4 *
         (Uint63.to_Z r4 + radix * carry_Z c4 - carry_Z c3))
      by ring.
    rewrite S0.
    assert (T1 : Uint63.to_Z r1 + radix * carry_Z c1 - carry_Z c0 =
      Uint63.to_Z a1 + Uint63.to_Z b1) by lia.
    assert (T2 : Uint63.to_Z r2 + radix * carry_Z c2 - carry_Z c1 =
      Uint63.to_Z a2 + Uint63.to_Z b2) by lia.
    assert (T3 : Uint63.to_Z r3 + radix * carry_Z c3 - carry_Z c2 =
      Uint63.to_Z a3 + Uint63.to_Z b3) by lia.
    assert (T4 : Uint63.to_Z r4 + radix * carry_Z c4 - carry_Z c3 =
      Uint63.to_Z a4 + Uint63.to_Z b4) by lia.
    rewrite T1, T2, T3, T4.
    ring.
  Qed.

  Lemma add_raw_no_carry (a b : words5)
      (Hfit : eval5 a + eval5 b < radix5) :
    exists r : words5,
      M.add_raw a b = (r, false) /\ eval5 r = eval5 a + eval5 b.
  Proof.
    destruct (M.add_raw a b) as [r carry] eqn:Eraw.
    pose proof (add_raw_spec a b) as E.
    rewrite Eraw in E; cbn [fst snd] in E.
    destruct carry.
    - cbn [carry_Z] in E.
      pose proof (eval5_bounds r) as Hr.
      lia.
    - exists r; split; [reflexivity |].
      cbn [carry_Z] in E.
      lia.
  Qed.

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

  (** ** Stable field-operation interface *)

  Lemma modulus_nonzero : C.modulus_Z <> 0.
  Proof. pose proof C.modulus_positive; lia. Qed.

  Lemma modulus_gt_one : 1 < C.modulus_Z.
  Proof.
    pose proof C.modulus_positive as Hm.
    pose proof
      (Z.mod_pos_bound (radix5 * C.r_inverse_Z) C.modulus_Z Hm) as Hbound.
    rewrite C.r_inverse_correct in Hbound.
    lia.
  Qed.

  Lemma eval5_zero : eval5 zero5 = 0.
  Proof.
    unfold eval5, zero5; cbn [w0 w1 w2 w3 w4].
    rewrite Uint63.to_Z_0.
    ring.
  Qed.

  Lemma eval5_one : eval5 one5 = 1.
  Proof.
    unfold eval5, one5; cbn [w0 w1 w2 w3 w4].
    rewrite Uint63.to_Z_0, Uint63.to_Z_1.
    ring.
  Qed.

  Lemma reduce_once_canonical (a : words5)
      (Ha : eval5 a < 2 * C.modulus_Z) :
    M.canonical (M.reduce_once a).
  Proof.
    unfold M.canonical, M.reduce_once.
    destruct (M.less_equal C.modulus a) eqn:Hcmp.
    - rewrite (subtract_modulus_spec a Hcmp).
      pose proof (less_equal_sound C.modulus a Hcmp) as Hle.
      rewrite C.modulus_words_correct in Hle.
      lia.
    - assert (Hnot : ~ eval5 C.modulus <= eval5 a).
      { intro Hle.
        pose proof (proj2 (less_equal_spec C.modulus a) Hle) as Htrue.
        rewrite Hcmp in Htrue.
        discriminate. }
      rewrite C.modulus_words_correct in Hnot.
      lia.
  Qed.

  Lemma reduce_once_eval (a : words5)
      (Ha : eval5 a < 2 * C.modulus_Z) :
    eval5 (M.reduce_once a) = eval5 a mod C.modulus_Z.
  Proof.
    pose proof (reduce_once_canonical a Ha) as Hcanonical.
    pose proof (reduce_once_congruent a) as Hcongruent.
    unfold M.canonical in Hcanonical.
    rewrite Z.mod_small in Hcongruent.
    - exact Hcongruent.
    - pose proof (eval5_bounds (M.reduce_once a)).
      lia.
  Qed.

  Lemma zero_canonical : M.canonical M.zero.
  Proof.
    unfold M.canonical, M.zero.
    rewrite eval5_zero.
    exact C.modulus_positive.
  Qed.

  Lemma denote_zero : M.denote M.zero = 0.
  Proof.
    unfold M.denote, M.zero.
    rewrite eval5_zero, Z.mul_0_l, Z.mod_0_l by exact modulus_nonzero.
    reflexivity.
  Qed.

  Lemma one_canonical : M.canonical M.one.
  Proof.
    unfold M.canonical, M.one.
    rewrite C.montgomery_one_correct.
    apply (proj2 (Z.mod_pos_bound radix5 C.modulus_Z C.modulus_positive)).
  Qed.

  Lemma denote_one : M.denote M.one = 1.
  Proof.
    unfold M.denote, M.one.
    rewrite C.montgomery_one_correct.
    rewrite Z.mul_mod_idemp_l by exact modulus_nonzero.
    rewrite C.r_inverse_correct.
    reflexivity.
  Qed.

  Lemma add_canonical (a b : M.t)
      (Ha : M.canonical a) (Hb : M.canonical b) :
    M.canonical (M.add a b).
  Proof.
    assert (Hsum : eval5 a + eval5 b < radix5).
    { unfold M.canonical in Ha, Hb.
      pose proof C.twice_modulus_fits.
      lia. }
    destruct (add_raw_no_carry a b Hsum) as [s [Eraw Es]].
    unfold M.add.
    rewrite Eraw; cbn [fst snd].
    apply reduce_once_canonical.
    rewrite Es.
    unfold M.canonical in Ha, Hb.
    lia.
  Qed.

  Lemma add_eval (a b : M.t)
      (Ha : M.canonical a) (Hb : M.canonical b) :
    eval5 (M.add a b) = (eval5 a + eval5 b) mod C.modulus_Z.
  Proof.
    assert (Hsum : eval5 a + eval5 b < radix5).
    { unfold M.canonical in Ha, Hb.
      pose proof C.twice_modulus_fits.
      lia. }
    destruct (add_raw_no_carry a b Hsum) as [s [Eraw Es]].
    unfold M.add.
    rewrite Eraw; cbn [fst snd].
    rewrite reduce_once_eval.
    - rewrite Es; reflexivity.
    - rewrite Es.
      unfold M.canonical in Ha, Hb.
      lia.
  Qed.

  Lemma sub_canonical (a b : M.t)
      (Ha : M.canonical a) (Hb : M.canonical b) :
    M.canonical (M.sub a b).
  Proof.
    destruct (M.sub_raw a b) as [d borrow] eqn:Eraw.
    pose proof (sub_raw_spec a b) as Esub.
    rewrite Eraw in Esub; cbn [fst snd] in Esub.
    unfold M.sub.
    rewrite Eraw; cbn [fst snd].
    pose proof (eval5_bounds a) as Ha0.
    pose proof (eval5_bounds b) as Hb0.
    pose proof (eval5_bounds d) as Hd0.
    unfold M.canonical in Ha, Hb |- *.
    destruct borrow.
    - cbn [borrow_Z] in Esub.
      destruct (M.add_raw d C.modulus) as [s carry] eqn:Eadd.
      pose proof (add_raw_spec d C.modulus) as Sadd.
      rewrite Eadd in Sadd; cbn [fst snd] in Sadd |- *.
      rewrite C.modulus_words_correct in Sadd.
      pose proof (eval5_bounds s) as Hs0.
      destruct carry.
      + cbn [carry_Z] in Sadd.
        lia.
      + cbn [carry_Z] in Sadd.
        exfalso; lia.
    - cbn [borrow_Z] in Esub.
      lia.
  Qed.

  Lemma sub_eval_congruent (a b : M.t)
      (Ha : M.canonical a) (Hb : M.canonical b) :
    eval5 (M.sub a b) mod C.modulus_Z =
      (eval5 a - eval5 b) mod C.modulus_Z.
  Proof.
    destruct (M.sub_raw a b) as [d borrow] eqn:Eraw.
    pose proof (sub_raw_spec a b) as Esub.
    rewrite Eraw in Esub; cbn [fst snd] in Esub.
    unfold M.sub.
    rewrite Eraw; cbn [fst snd].
    pose proof (eval5_bounds a) as Ha0.
    pose proof (eval5_bounds b) as Hb0.
    pose proof (eval5_bounds d) as Hd0.
    unfold M.canonical in Ha, Hb.
    destruct borrow.
    - cbn [borrow_Z] in Esub.
      destruct (M.add_raw d C.modulus) as [s carry] eqn:Eadd.
      pose proof (add_raw_spec d C.modulus) as Sadd.
      rewrite Eadd in Sadd; cbn [fst snd] in Sadd |- *.
      rewrite C.modulus_words_correct in Sadd.
      pose proof (eval5_bounds s) as Hs0.
      destruct carry.
      + cbn [carry_Z] in Sadd.
        replace (eval5 s) with
          ((eval5 a - eval5 b) + C.modulus_Z) by lia.
        rewrite Z.add_mod by exact modulus_nonzero.
        rewrite Z.mod_same by exact modulus_nonzero.
        rewrite Z.add_0_r, Z.mod_mod by exact modulus_nonzero.
        reflexivity.
      + cbn [carry_Z] in Sadd.
        exfalso; lia.
    - cbn [borrow_Z] in Esub.
      assert (Ed : eval5 d = eval5 a - eval5 b) by lia.
      rewrite Ed.
      reflexivity.
  Qed.

  Lemma sub_eval (a b : M.t)
      (Ha : M.canonical a) (Hb : M.canonical b) :
    eval5 (M.sub a b) =
      (eval5 a - eval5 b) mod C.modulus_Z.
  Proof.
    pose proof (sub_canonical a b Ha Hb) as Hcanonical.
    pose proof (sub_eval_congruent a b Ha Hb) as Hcongruent.
    unfold M.canonical in Hcanonical.
    rewrite Z.mod_small in Hcongruent.
    - exact Hcongruent.
    - pose proof (eval5_bounds (M.sub a b)).
      lia.
  Qed.

  Lemma neg_canonical (a : M.t) (Ha : M.canonical a) :
    M.canonical (M.neg a).
  Proof.
    unfold M.neg.
    destruct (M.equal a M.zero) eqn:Heq.
    - exact zero_canonical.
    - assert (Hneq : a <> M.zero).
      { intro E; subst a.
        rewrite (proj2 (equal_spec M.zero M.zero) eq_refl) in Heq.
        discriminate. }
      assert (Hpositive : 0 < eval5 a).
      { pose proof (eval5_bounds a) as Ha0.
        destruct (Z.eq_dec (eval5 a) 0) as [Hz | Hz]; [|lia].
        exfalso.
        apply Hneq.
        apply eval5_inj.
        unfold M.zero.
        rewrite eval5_zero.
        exact Hz. }
      assert (Hle : eval5 a <= eval5 C.modulus).
      { rewrite C.modulus_words_correct.
        unfold M.canonical in Ha.
        lia. }
      destruct (sub_raw_no_borrow C.modulus a Hle) as [d [Eraw Ed]].
      rewrite Eraw; cbn [fst snd].
      unfold M.canonical.
      rewrite Ed, C.modulus_words_correct.
      lia.
  Qed.

  Lemma neg_eval_congruent (a : M.t) (Ha : M.canonical a) :
    eval5 (M.neg a) mod C.modulus_Z = (- eval5 a) mod C.modulus_Z.
  Proof.
    unfold M.neg.
    destruct (M.equal a M.zero) eqn:Heq.
    - apply (proj1 (equal_spec a M.zero)) in Heq.
      subst a.
      unfold M.zero.
      rewrite !eval5_zero, Z.opp_0, !Z.mod_0_l by exact modulus_nonzero.
      reflexivity.
    - assert (Hle : eval5 a <= eval5 C.modulus).
      { rewrite C.modulus_words_correct.
        unfold M.canonical in Ha.
        lia. }
      destruct (sub_raw_no_borrow C.modulus a Hle) as [d [Eraw Ed]].
      rewrite Eraw; cbn [fst snd].
      rewrite Ed, C.modulus_words_correct.
      replace (C.modulus_Z - eval5 a) with
        (- eval5 a + C.modulus_Z) by ring.
      rewrite Z.add_mod by exact modulus_nonzero.
      rewrite Z.mod_same by exact modulus_nonzero.
      rewrite Z.add_0_r, Z.mod_mod by exact modulus_nonzero.
      reflexivity.
  Qed.

  Lemma neg_eval (a : M.t) (Ha : M.canonical a) :
    eval5 (M.neg a) = (- eval5 a) mod C.modulus_Z.
  Proof.
    pose proof (neg_canonical a Ha) as Hcanonical.
    pose proof (neg_eval_congruent a Ha) as Hcongruent.
    unfold M.canonical in Hcanonical.
    rewrite Z.mod_small in Hcongruent.
    - exact Hcongruent.
    - pose proof (eval5_bounds (M.neg a)).
      lia.
  Qed.

  Lemma mul_canonical (a b : M.t) (Hb : M.canonical b) :
    M.canonical (M.mul a b).
  Proof.
    unfold M.mul.
    rewrite montgomery_reduce_unfold.
    apply reduce_once_canonical.
    rewrite (montgomery_steps_low5 a b Hb).
    exact (montgomery_steps_bound a b Hb).
  Qed.

  Lemma square_canonical (a : M.t) (Ha : M.canonical a) :
    M.canonical (M.square a).
  Proof. exact (mul_canonical a a Ha). Qed.

  Lemma square_denote (a : M.t) (Ha : M.canonical a) :
    M.denote (M.square a) =
      (M.denote a * M.denote a) mod C.modulus_Z.
  Proof. exact (mul_denote a a Ha). Qed.

  Lemma add_denote (a b : M.t)
      (Ha : M.canonical a) (Hb : M.canonical b) :
    M.denote (M.add a b) =
      (M.denote a + M.denote b) mod C.modulus_Z.
  Proof.
    unfold M.denote.
    rewrite (add_eval a b Ha Hb).
    rewrite Z.mul_mod_idemp_l by exact modulus_nonzero.
    rewrite <- Z.add_mod by exact modulus_nonzero.
    f_equal; ring.
  Qed.

  Lemma sub_denote (a b : M.t)
      (Ha : M.canonical a) (Hb : M.canonical b) :
    M.denote (M.sub a b) =
      (M.denote a - M.denote b) mod C.modulus_Z.
  Proof.
    unfold M.denote.
    rewrite (sub_eval a b Ha Hb).
    rewrite Z.mul_mod_idemp_l by exact modulus_nonzero.
    rewrite <- Zminus_mod.
    f_equal; ring.
  Qed.

  Lemma neg_denote (a : M.t) (Ha : M.canonical a) :
    M.denote (M.neg a) = (- M.denote a) mod C.modulus_Z.
  Proof.
    unfold M.denote.
    rewrite (neg_eval a Ha).
    rewrite Z.mul_mod_idemp_l by exact modulus_nonzero.
    replace (- ((eval5 a * C.r_inverse_Z) mod C.modulus_Z))
      with
      (0 - ((eval5 a * C.r_inverse_Z) mod C.modulus_Z)) by ring.
    rewrite <- (Z.mod_0_l C.modulus_Z modulus_nonzero).
    rewrite <- Zminus_mod.
    f_equal; ring.
  Qed.

  Lemma r_inverse_cancel (x : Z) :
    ((x * C.r_inverse_Z) * radix5) mod C.modulus_Z =
      x mod C.modulus_Z.
  Proof.
    replace ((x * C.r_inverse_Z) * radix5)
      with (x * (radix5 * C.r_inverse_Z)) by ring.
    assert (Hinv :
      (radix5 * C.r_inverse_Z) mod C.modulus_Z =
        1 mod C.modulus_Z).
    { rewrite C.r_inverse_correct, Z.mod_small; [reflexivity |].
      pose proof modulus_gt_one; lia. }
    pose proof
      (mod_mul_compat x x (radix5 * C.r_inverse_Z) 1
        eq_refl Hinv) as E.
    replace (x * 1) with x in E by ring.
    exact E.
  Qed.

  Lemma denote_injective (a b : M.t)
      (Ha : M.canonical a) (Hb : M.canonical b) :
    M.denote a = M.denote b -> a = b.
  Proof.
    unfold M.denote, M.canonical in *.
    intro H.
    pose proof
      (f_equal (fun z => (z * radix5) mod C.modulus_Z) H) as Hscaled.
    cbn beta in Hscaled.
    rewrite !Z.mul_mod_idemp_l in Hscaled by exact modulus_nonzero.
    rewrite !r_inverse_cancel in Hscaled.
    pose proof (eval5_bounds a) as Ha0.
    pose proof (eval5_bounds b) as Hb0.
    rewrite !Z.mod_small in Hscaled by lia.
    apply eval5_inj.
    exact Hscaled.
  Qed.

  Lemma equal_denote_iff (a b : M.t)
      (Ha : M.canonical a) (Hb : M.canonical b) :
    M.equal a b = true <-> M.denote a = M.denote b.
  Proof.
    split.
    - intro Heq.
      apply (proj1 (equal_spec a b)) in Heq.
      subst b; reflexivity.
    - intro Hdenote.
      apply (proj2 (equal_spec a b)).
      exact (denote_injective a b Ha Hb Hdenote).
  Qed.

  Lemma equal_denote_false_iff (a b : M.t)
      (Ha : M.canonical a) (Hb : M.canonical b) :
    M.equal a b = false <-> M.denote a <> M.denote b.
  Proof.
    split.
    - intros Hfalse Hdenote.
      pose proof (proj2 (equal_denote_iff a b Ha Hb) Hdenote) as Htrue.
      rewrite Hfalse in Htrue; discriminate.
    - intro Hneq.
      destruct (M.equal a b) eqn:Heq; [|reflexivity].
      exfalso.
      apply Hneq.
      exact (proj1 (equal_denote_iff a b Ha Hb) Heq).
  Qed.

  Lemma modulus_lt_radix5 : C.modulus_Z < radix5.
  Proof.
    pose proof C.modulus_positive.
    pose proof C.twice_modulus_fits.
    lia.
  Qed.

  Lemma words_of_nonnegative_eval (z : Z)
      (Hz : 0 <= z < radix5) :
    eval5 (M.words_of_nonnegative z) = z.
  Proof.
    unfold M.words_of_nonnegative, eval5.
    cbn [w0 w1 w2 w3 w4].
    rewrite !Uint63.of_Z_spec.
    pose proof radix_pos as Hr.
    assert (Hr0 : radix <> 0) by lia.
    assert (Hr2 : radix ^ 2 <> 0) by
      (apply Z.pow_nonzero; [exact Hr0 | lia]).
    assert (Hr3 : radix ^ 3 <> 0) by
      (apply Z.pow_nonzero; [exact Hr0 | lia]).
    assert (E12 : z / radix / radix = z / radix ^ 2).
    { rewrite Z.div_div by (exact Hr0 || lia).
      f_equal; ring. }
    assert (E23 : z / radix ^ 2 / radix = z / radix ^ 3).
    { rewrite Z.div_div by (exact Hr2 || lia).
      f_equal; ring. }
    assert (E34 : z / radix ^ 3 / radix = z / radix ^ 4).
    { rewrite Z.div_div by (exact Hr3 || lia).
      f_equal; ring. }
    assert (Hq4 : 0 <= z / radix ^ 4 < radix).
    { split.
      - apply Z.div_pos; [exact (proj1 Hz) |].
        apply Z.pow_pos_nonneg; lia.
      - apply Z.div_lt_upper_bound.
        + apply Z.pow_pos_nonneg; lia.
        + unfold radix5 in Hz.
          replace (radix ^ 4 * radix) with (radix ^ 5) by ring.
          exact (proj2 Hz). }
    assert (E45 : z / radix ^ 4 / radix = 0).
    { apply Z.div_small; exact Hq4. }
    rewrite !Z.mod_eq by exact Hr0.
    fold radix.
    rewrite E12, E23, E34, E45.
    ring.
  Qed.

  Lemma standard_of_Z_eval (z : Z) :
    eval5 (M.standard_of_Z z) = z mod C.modulus_Z.
  Proof.
    unfold M.standard_of_Z.
    apply words_of_nonnegative_eval.
    pose proof (Z.mod_pos_bound z C.modulus_Z C.modulus_positive).
    pose proof modulus_lt_radix5.
    lia.
  Qed.

  Lemma standard_of_Z_canonical (z : Z) :
    M.canonical (M.standard_of_Z z).
  Proof.
    unfold M.canonical.
    rewrite standard_of_Z_eval.
    apply (proj2 (Z.mod_pos_bound z C.modulus_Z C.modulus_positive)).
  Qed.

  Lemma r2_canonical : M.canonical C.r2.
  Proof.
    unfold M.canonical.
    rewrite C.r2_correct.
    apply (proj2
      (Z.mod_pos_bound (radix5 * radix5) C.modulus_Z C.modulus_positive)).
  Qed.

  Lemma denote_r2 : M.denote C.r2 = radix5 mod C.modulus_Z.
  Proof.
    unfold M.denote.
    rewrite C.r2_correct.
    rewrite Z.mul_mod_idemp_l by exact modulus_nonzero.
    replace ((radix5 * radix5) * C.r_inverse_Z)
      with (radix5 * (radix5 * C.r_inverse_Z)) by ring.
    assert (Hinv :
      (radix5 * C.r_inverse_Z) mod C.modulus_Z =
        1 mod C.modulus_Z).
    { rewrite C.r_inverse_correct, Z.mod_small; [reflexivity |].
      pose proof modulus_gt_one; lia. }
    pose proof
      (mod_mul_compat radix5 radix5
        (radix5 * C.r_inverse_Z) 1 eq_refl Hinv) as E.
    replace (radix5 * 1) with radix5 in E by ring.
    exact E.
  Qed.

  Lemma encode_canonical (standard : words5) :
    M.canonical (M.encode standard).
  Proof.
    unfold M.encode.
    exact (mul_canonical standard C.r2 r2_canonical).
  Qed.

  Lemma encode_denote (standard : words5) :
    M.denote (M.encode standard) = eval5 standard mod C.modulus_Z.
  Proof.
    unfold M.encode.
    rewrite (mul_denote standard C.r2 r2_canonical), denote_r2.
    unfold M.denote.
    rewrite <- Z.mul_mod by exact modulus_nonzero.
    exact (r_inverse_cancel (eval5 standard)).
  Qed.

  Lemma from_Z_canonical (z : Z) : M.canonical (M.from_Z z).
  Proof.
    unfold M.from_Z.
    apply encode_canonical.
  Qed.

  Lemma from_Z_denote (z : Z) :
    M.denote (M.from_Z z) = z mod C.modulus_Z.
  Proof.
    unfold M.from_Z.
    rewrite encode_denote, standard_of_Z_eval.
    rewrite Z.mod_mod by exact modulus_nonzero.
    reflexivity.
  Qed.

  Lemma standard_one_canonical : M.canonical one5.
  Proof.
    unfold M.canonical.
    rewrite eval5_one.
    exact modulus_gt_one.
  Qed.

  Lemma mul_eval (a b : M.t) (Hb : M.canonical b) :
    eval5 (M.mul a b) =
      (eval5 a * eval5 b * C.r_inverse_Z) mod C.modulus_Z.
  Proof.
    pose proof (mul_congruent a b Hb) as Hmul.
    pose proof
      (mod_mul_compat
        (radix5 * eval5 (M.mul a b)) (eval5 a * eval5 b)
        C.r_inverse_Z C.r_inverse_Z Hmul eq_refl) as Hscaled.
    replace
      ((radix5 * eval5 (M.mul a b)) * C.r_inverse_Z)
      with
      ((eval5 (M.mul a b) * C.r_inverse_Z) * radix5)
      in Hscaled by ring.
    rewrite r_inverse_cancel in Hscaled.
    pose proof (mul_canonical a b Hb) as Hcanonical.
    unfold M.canonical in Hcanonical.
    pose proof (eval5_bounds (M.mul a b)) as Hbounds.
    rewrite Z.mod_small in Hscaled by lia.
    exact Hscaled.
  Qed.

  Lemma decode_canonical (a : M.t) : M.canonical (M.decode a).
  Proof.
    unfold M.decode.
    exact (mul_canonical a one5 standard_one_canonical).
  Qed.

  Lemma decode_eval5 (a : M.t) :
    eval5 (M.decode a) = M.denote a.
  Proof.
    unfold M.decode, M.denote.
    rewrite (mul_eval a one5 standard_one_canonical), eval5_one.
    f_equal; ring.
  Qed.

  Lemma to_Z_denote (a : M.t) : M.to_Z a = M.denote a.
  Proof.
    unfold M.to_Z.
    apply decode_eval5.
  Qed.

End Prim63MontgomeryRefinement.
