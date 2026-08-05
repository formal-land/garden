(** * Five-word arithmetic over Rocq's primitive unsigned 63-bit integers

    This file contains only radix-[2^63] plumbing.  In particular, [mac]
    returns the exact low word and carry word of [x*y + z + c], and [sweep]
    adds a one-word multiple of a five-word value to a six-word accumulator.
    The carry beyond the sixth word is returned explicitly; callers must not
    discard it. *)

From Stdlib Require Import ZArith Lia.
Require Import Stdlib.Numbers.Cyclic.Int63.Uint63.

Local Open Scope Z_scope.

Module Prim63Words.

  Definition word := PrimInt63.int.
  Definition radix : Z := Uint63.wB.

  Record words5 : Set := {
    w0 : word;
    w1 : word;
    w2 : word;
    w3 : word;
    w4 : word;
  }.

  Record words6 : Set := {
    x0 : word;
    x1 : word;
    x2 : word;
    x3 : word;
    x4 : word;
    x5 : word;
  }.

  Definition zero5 : words5 :=
    {| w0 := 0%uint63; w1 := 0%uint63; w2 := 0%uint63;
       w3 := 0%uint63; w4 := 0%uint63 |}.

  Definition one5 : words5 :=
    {| w0 := 1%uint63; w1 := 0%uint63; w2 := 0%uint63;
       w3 := 0%uint63; w4 := 0%uint63 |}.

  Definition zero6 : words6 :=
    {| x0 := 0%uint63; x1 := 0%uint63; x2 := 0%uint63;
       x3 := 0%uint63; x4 := 0%uint63; x5 := 0%uint63 |}.

  Definition low5 (x : words6) : words5 :=
    {| w0 := x.(x0); w1 := x.(x1); w2 := x.(x2);
       w3 := x.(x3); w4 := x.(x4) |}.

  Definition widen (x : words5) : words6 :=
    {| x0 := x.(w0); x1 := x.(w1); x2 := x.(w2);
       x3 := x.(w3); x4 := x.(w4); x5 := 0%uint63 |}.

  Definition eval5 (x : words5) : Z :=
    Uint63.to_Z x.(w0) +
    radix * (Uint63.to_Z x.(w1) +
    radix * (Uint63.to_Z x.(w2) +
    radix * (Uint63.to_Z x.(w3) +
    radix * Uint63.to_Z x.(w4)))).

  Definition eval6 (x : words6) : Z :=
    Uint63.to_Z x.(x0) +
    radix * (Uint63.to_Z x.(x1) +
    radix * (Uint63.to_Z x.(x2) +
    radix * (Uint63.to_Z x.(x3) +
    radix * (Uint63.to_Z x.(x4) +
    radix * Uint63.to_Z x.(x5))))).

  Definition radix5 : Z := radix ^ 5.
  Definition radix6 : Z := radix ^ 6.

  Lemma radix_value : radix = 9223372036854775808%Z.
  Proof. reflexivity. Qed.

  Lemma radix_pos : 0 < radix.
  Proof. rewrite radix_value; lia. Qed.

  Lemma word_bounds (x : word) : 0 <= Uint63.to_Z x < radix.
  Proof. apply Uint63.to_Z_bounded. Qed.

  Lemma eval5_bounds (x : words5) : 0 <= eval5 x < radix5.
  Proof.
    destruct x as [a0 a1 a2 a3 a4].
    pose proof (word_bounds a0) as H0.
    pose proof (word_bounds a1) as H1.
    pose proof (word_bounds a2) as H2.
    pose proof (word_bounds a3) as H3.
    pose proof (word_bounds a4) as H4.
    pose proof radix_pos as Hr.
    assert (H34 :
      0 <= Uint63.to_Z a3 + radix * Uint63.to_Z a4 < radix ^ 2) by
      (replace (radix ^ 2) with (radix * radix) by ring; nia).
    assert (H234 :
      0 <= Uint63.to_Z a2 +
        radix * (Uint63.to_Z a3 + radix * Uint63.to_Z a4) < radix ^ 3) by
      (replace (radix ^ 3) with (radix * radix ^ 2) by ring; nia).
    assert (H1234 :
      0 <= Uint63.to_Z a1 +
        radix * (Uint63.to_Z a2 +
          radix * (Uint63.to_Z a3 + radix * Uint63.to_Z a4)) < radix ^ 4) by
      (replace (radix ^ 4) with (radix * radix ^ 3) by ring; nia).
    cbn [eval5 radix5].
    replace (radix ^ 5) with (radix * radix ^ 4) by ring.
    assert (0 <= radix ^ 4) by (apply Z.pow_nonneg; lia).
    assert (Hmul :
      radix * (Uint63.to_Z a1 +
        radix * (Uint63.to_Z a2 +
          radix * (Uint63.to_Z a3 + radix * Uint63.to_Z a4))) <=
      radix * (radix ^ 4 - 1)) by
      (apply Z.mul_le_mono_nonneg_l; lia).
    split.
    - assert (Htailprod : 0 <= radix *
          (Uint63.to_Z a1 +
            radix * (Uint63.to_Z a2 +
              radix * (Uint63.to_Z a3 + radix * Uint63.to_Z a4)))) by
          (apply Z.mul_nonneg_nonneg; lia).
      apply Z.add_nonneg_nonneg; [exact (proj1 H0) | exact Htailprod].
    - replace (radix * (radix ^ 4 - 1)) with
        (radix * radix ^ 4 - radix) in Hmul by ring.
      apply Z.lt_le_trans with
        (radix + radix *
          (Uint63.to_Z a1 +
            radix * (Uint63.to_Z a2 +
              radix * (Uint63.to_Z a3 + radix * Uint63.to_Z a4)))).
      + apply Z.add_lt_mono_r. exact (proj2 H0).
      + pose proof (proj1 (Z.add_le_mono_l _ _ radix) Hmul) as Hplus.
        replace (radix + (radix * radix ^ 4 - radix)) with
          (radix * radix ^ 4) in Hplus by ring.
        exact Hplus.
  Qed.

  Lemma eval6_bounds (x : words6) : 0 <= eval6 x < radix6.
  Proof.
    destruct x as [a0 a1 a2 a3 a4 a5].
    pose proof (word_bounds a0) as H0.
    pose proof (word_bounds a1) as H1.
    pose proof (word_bounds a2) as H2.
    pose proof (word_bounds a3) as H3.
    pose proof (word_bounds a4) as H4.
    pose proof (word_bounds a5) as H5.
    pose proof radix_pos as Hr.
    assert (H45 :
      0 <= Uint63.to_Z a4 + radix * Uint63.to_Z a5 < radix ^ 2) by
      (replace (radix ^ 2) with (radix * radix) by ring; nia).
    assert (H345 :
      0 <= Uint63.to_Z a3 +
        radix * (Uint63.to_Z a4 + radix * Uint63.to_Z a5) < radix ^ 3) by
      (replace (radix ^ 3) with (radix * radix ^ 2) by ring; nia).
    assert (H2345 :
      0 <= Uint63.to_Z a2 +
        radix * (Uint63.to_Z a3 +
          radix * (Uint63.to_Z a4 + radix * Uint63.to_Z a5)) < radix ^ 4) by
      (replace (radix ^ 4) with (radix * radix ^ 3) by ring; nia).
    assert (H12345 :
      0 <= Uint63.to_Z a1 +
        radix * (Uint63.to_Z a2 +
          radix * (Uint63.to_Z a3 +
            radix * (Uint63.to_Z a4 + radix * Uint63.to_Z a5))) < radix ^ 5) by
      (replace (radix ^ 5) with (radix * radix ^ 4) by ring; nia).
    cbn [eval6 radix6].
    replace (radix ^ 6) with (radix * radix ^ 5) by ring.
    assert (0 <= radix ^ 5) by (apply Z.pow_nonneg; lia).
    assert (Hmul :
      radix * (Uint63.to_Z a1 +
        radix * (Uint63.to_Z a2 +
          radix * (Uint63.to_Z a3 +
            radix * (Uint63.to_Z a4 + radix * Uint63.to_Z a5)))) <=
      radix * (radix ^ 5 - 1)) by
      (apply Z.mul_le_mono_nonneg_l; lia).
    split.
    - assert (Htailprod : 0 <= radix *
          (Uint63.to_Z a1 +
            radix * (Uint63.to_Z a2 +
              radix * (Uint63.to_Z a3 +
                radix * (Uint63.to_Z a4 + radix * Uint63.to_Z a5))))) by
          (apply Z.mul_nonneg_nonneg; lia).
      apply Z.add_nonneg_nonneg; [exact (proj1 H0) | exact Htailprod].
    - replace (radix * (radix ^ 5 - 1)) with
        (radix * radix ^ 5 - radix) in Hmul by ring.
      apply Z.lt_le_trans with
        (radix + radix *
          (Uint63.to_Z a1 +
            radix * (Uint63.to_Z a2 +
              radix * (Uint63.to_Z a3 +
                radix * (Uint63.to_Z a4 + radix * Uint63.to_Z a5))))).
      + apply Z.add_lt_mono_r. exact (proj2 H0).
      + pose proof (proj1 (Z.add_le_mono_l _ _ radix) Hmul) as Hplus.
        replace (radix + (radix * radix ^ 5 - radix)) with
          (radix * radix ^ 5) in Hplus by ring.
        exact Hplus.
  Qed.

  Lemma eval_widen (x : words5) : eval6 (widen x) = eval5 x.
  Proof.
    destruct x.
    unfold eval6, eval5, widen.
    change (Uint63.to_Z 0%uint63) with 0.
    rewrite Z.mul_0_r, Z.add_0_r.
    reflexivity.
  Qed.

  Lemma eval_low5 (x : words6) :
    eval6 x = eval5 (low5 x) + radix5 * Uint63.to_Z x.(x5).
  Proof.
    destruct x as [u0 u1 u2 u3 u4 u5].
    unfold eval6, eval5, low5, radix5.
    cbn [x0 x1 x2 x3 x4 x5 w0 w1 w2 w3 w4].
    remember radix as r.
    remember (Uint63.to_Z u0) as a0.
    remember (Uint63.to_Z u1) as a1.
    remember (Uint63.to_Z u2) as a2.
    remember (Uint63.to_Z u3) as a3.
    remember (Uint63.to_Z u4) as a4.
    remember (Uint63.to_Z u5) as a5.
    ring.
  Qed.

  (** Add zero, one, or two to a high word.  The exact [mac] theorem below
      proves that the selected increment cannot wrap. *)
  Definition add_small (x : word) (n : nat) : word :=
    match n with
    | O => x
    | S O => Uint63.add x 1%uint63
    | _ => Uint63.add x 2%uint63
    end.

  (** Exact multiply-accumulate.  The result is [(carry, low)]. *)
  Definition mac (z x y c : word) : word * word :=
    let '(hi, lo) := PrimInt63.mulc x y in
    match PrimInt63.addc lo z with
    | C0 lo1 =>
        match PrimInt63.addc lo1 c with
        | C0 out => (hi, out)
        | C1 out => (add_small hi 1, out)
        end
    | C1 lo1 =>
        match PrimInt63.addc lo1 c with
        | C0 out => (add_small hi 1, out)
        | C1 out => (add_small hi 2, out)
        end
    end.

  Lemma add_small_0 (x : word) :
    Uint63.to_Z (add_small x 0) = Uint63.to_Z x.
  Proof. reflexivity. Qed.

  Lemma add_small_1 (x : word) :
    Uint63.to_Z x + 1 < radix ->
    Uint63.to_Z (add_small x 1) = Uint63.to_Z x + 1.
  Proof.
    intro H.
    unfold add_small.
    rewrite Uint63.add_spec, Uint63.to_Z_1.
    rewrite Z.mod_small; [reflexivity |].
    pose proof (word_bounds x) as Hx.
    split; [apply Z.add_nonneg_nonneg; lia | exact H].
  Qed.

  Lemma add_small_2 (x : word) :
    Uint63.to_Z x + 2 < radix ->
    Uint63.to_Z (add_small x 2) = Uint63.to_Z x + 2.
  Proof.
    intro H.
    unfold add_small.
    rewrite Uint63.add_spec.
    change (Uint63.to_Z 2%uint63) with 2.
    rewrite Z.mod_small; [reflexivity |].
    pose proof (word_bounds x) as Hx.
    split; [apply Z.add_nonneg_nonneg; lia | exact H].
  Qed.

  (** One complete five-word MAC sweep into a six-word accumulator.  The
      returned word is exactly the carry beyond word 5 (therefore 0 or 1). *)
  Definition sweep (a : words6) (x : word) (y : words5) : words6 * word :=
    let '(c0, r0) := mac a.(x0) x y.(w0) 0%uint63 in
    let '(c1, r1) := mac a.(x1) x y.(w1) c0 in
    let '(c2, r2) := mac a.(x2) x y.(w2) c1 in
    let '(c3, r3) := mac a.(x3) x y.(w3) c2 in
    let '(c4, r4) := mac a.(x4) x y.(w4) c3 in
    match PrimInt63.addc a.(x5) c4 with
    | C0 r5 =>
        ({| x0 := r0; x1 := r1; x2 := r2;
            x3 := r3; x4 := r4; x5 := r5 |}, 0%uint63)
    | C1 r5 =>
        ({| x0 := r0; x1 := r1; x2 := r2;
            x3 := r3; x4 := r4; x5 := r5 |}, 1%uint63)
    end.

  (** Add a second multiple without losing the carry from the first sweep. *)
  Definition sweep2
      (a : words6) (top : word) (x : word) (y : words5)
      : words6 * word :=
    let '(r, top') := sweep a x y in
    (r, Uint63.add top top').

  Definition shift7 (a : words6) (top : word) : words6 :=
    {| x0 := a.(x1); x1 := a.(x2); x2 := a.(x3);
       x3 := a.(x4); x4 := a.(x5); x5 := top |}.

End Prim63Words.
