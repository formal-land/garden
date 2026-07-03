Require Import Garden.Field.Field.
Require Import Garden.Field.Fermat.
Require Import Garden.Field.Div.
Require Import Garden.Field.Lemmas.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.ZArith.Zpow_facts.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.Wf_nat.
Import ListNotations.

(** * Square roots in a prime field [Z/pZ]

    [is_square] is Euler's criterion; [field_sqrt] is a concrete Tonelli–Shanks
    square root.  Both are generic over any prime field [{p} `{Prime p}] — the
    algorithm is valid for every prime, so it lives here in [Field/] rather than
    tied to a specific curve.  [find_nonresidue] is a total (well-founded) search
    for a quadratic non-residue, which always exists below [p]; this makes
    [field_sqrt_sound] (correctness on quadratic residues) hold unconditionally.

    The development builds the supporting field-power algebra ([Fpow], [modpow]
    correctness), Euler's criterion facts, the Tonelli–Shanks loop invariant
    ([ts_loop_sound]), the 2-adic factorisation of [p-1] ([split_two]), a
    self-contained polynomial root bound used to prove non-residue existence
    ([root_bound], [nonresidue_exists]), and finally [field_sqrt_sound]. *)

Global Open Scope Z_scope.

Section FieldSqrt.
  Context {p : Z} `{Prime p}.

  (** Fast modular exponentiation by square-and-multiply over the binary digits
      of the exponent, reducing mod [p] (via [*F]) at each step. *)
  Fixpoint modpow_pos (base : Z) (e : positive) : Z :=
    match e with
    | xH => UnOp.from base
    | xO e' => let h := modpow_pos base e' in h *F h
    | xI e' => let h := modpow_pos base e' in h *F h *F base
    end.

  Definition modpow (base e : Z) : Z :=
    match e with
    | Zpos q => modpow_pos base q
    | _ => UnOp.from 1
    end.

  (* Every [modpow] output is already reduced mod [p]: [modpow_pos] returns a
     [UnOp.from] leaf or a [*F] product, and the non-positive branch a [UnOp.from]. *)
  Lemma modpow_pos_reduced (base : Z) (e : positive) :
    UnOp.from (modpow_pos base e) = modpow_pos base e.
  Proof.
    destruct e; cbn [modpow_pos];
      solve [apply from_mul_reduced | apply from_idem].
  Qed.

  Lemma modpow_reduced (base e : Z) : UnOp.from (modpow base e) = modpow base e.
  Proof.
    unfold modpow. destruct e;
      solve [apply from_idem | apply modpow_pos_reduced].
  Qed.

  (* [Fpow], [prime_gt1] and the basic field-power laws live in [Field.Lemmas]. *)

  Lemma modpow_pos_correct (base : Z) (e : positive) :
    modpow_pos base e = Fpow base (Z.pos e).
  Proof.
    pose proof prime_gt1 as Hp1.
    induction e as [e IH | e IH | ]; cbn [modpow_pos].
    - (* xI *)
      rewrite IH.
      rewrite <- Fpow_add by lia.
      replace (Fpow base (Z.pos e + Z.pos e) *F base)
        with (Fpow base (Z.pos e + Z.pos e) *F UnOp.from base)
        by (unfold BinOp.mul, UnOp.from; now rewrite Zmult_mod_idemp_r).
      rewrite <- Fpow_1.
      rewrite <- Fpow_add by lia.
      f_equal. lia.
    - (* xO *)
      rewrite IH.
      rewrite <- Fpow_add by lia.
      f_equal. lia.
    - (* xH *)
      rewrite Fpow_1. reflexivity.
  Qed.

  Lemma modpow_correct (base e : Z) : 0 <= e -> modpow base e = Fpow base e.
  Proof.
    intros He. unfold modpow.
    destruct e as [|q|q]; try lia.
    - now rewrite Fpow_0.
    - apply modpow_pos_correct.
  Qed.

  (* Fermat in field-power form: a^(p-1) = 1 for nonzero a. *)
  Lemma fermat_Fpow (a : Z) : UnOp.from a <> 0 -> Fpow a (p - 1) = UnOp.from 1.
  Proof.
    intros Ha.
    pose proof (@is_prime p _) as Hp. unfold IsPrime in Hp.
    pose proof prime_gt1 as Hp1.
    unfold Fpow.
    assert (Ha' : 0 < a mod p < p).
    { pose proof (Z.mod_pos_bound a p ltac:(lia)) as Hb.
      unfold UnOp.from in Ha. lia. }
    unfold UnOp.from.
    rewrite (Zpower_mod a (p - 1) p ltac:(lia)).
    rewrite (flt_pow_pred (a mod p) p Hp Ha').
    now rewrite Z.mod_1_l by lia.
  Qed.

  (* Euler: for nonzero a, a^((p-1)/2) is 1 or -1. *)
  Lemma euler_pm (a : Z) : 2 < p -> UnOp.from a <> 0 ->
    Fpow a ((p - 1) / 2) = UnOp.from 1 \/ Fpow a ((p - 1) / 2) = UnOp.from (-1).
  Proof.
    intros Hp3 Ha.
    pose proof half_nonneg as Hh.
    rewrite <- (Fpow_reduced a ((p - 1) / 2)).
    apply sqrt_one.
    rewrite Fpow_sqr by lia.
    rewrite odd_pm1 by lia.
    now apply fermat_Fpow.
  Qed.

  (* Euler's criterion as used by [is_square]. *)
  Definition is_square (a : Z) : bool :=
    Z.eqb (UnOp.from a) 0 || Z.eqb (modpow a ((p - 1) / 2)) (UnOp.from 1).

  Lemma is_square_true_nonzero (a : Z) :
    UnOp.from a <> 0 -> is_square a = true ->
    Fpow a ((p - 1) / 2) = UnOp.from 1.
  Proof.
    intros Ha Hsq. unfold is_square in Hsq.
    apply orb_true_iff in Hsq. destruct Hsq as [Hz | He].
    - apply Z.eqb_eq in Hz. contradiction.
    - apply Z.eqb_eq in He.
      rewrite modpow_correct in He by (apply half_nonneg).
      exact He.
  Qed.

  Lemma is_square_false_spec (z : Z) :
    is_square z = false ->
    UnOp.from z <> 0 /\ Fpow z ((p - 1) / 2) <> UnOp.from 1.
  Proof.
    intros Hns. unfold is_square in Hns.
    apply orb_false_iff in Hns. destruct Hns as [Hz He].
    split.
    - apply Z.eqb_neq in Hz. exact Hz.
    - apply Z.eqb_neq in He.
      rewrite modpow_correct in He by (apply half_nonneg). exact He.
  Qed.

  (* A non-residue z has z^((p-1)/2) = -1. *)
  Lemma nonresidue_pow (z : Z) :
    2 < p -> is_square z = false ->
    Fpow z ((p - 1) / 2) = UnOp.from (-1).
  Proof.
    intros Hp3 Hns.
    pose proof (is_square_false_spec z Hns) as [Hz He].
    destruct (euler_pm z Hp3 Hz) as [H1 | Hm1].
    - contradiction.
    - exact Hm1.
  Qed.

  (* --- [is_square] algebra: the zero branch, squares are residues, and QR
     multiplicativity, all from the Euler scaffolding above. These feed
     window-point sign forcing: with [is_square (z - r) = is_square (u * u) = true]
     and [is_square (window_disc) = is_square ((z - r) *F (r + z)) = false],
     [is_square_mul_cancel_l] forces [is_square (r + z) = false]. --- *)

  (* Anything reducing to 0 mod p counts as a square (the zero branch). *)
  Lemma is_square_from_zero (a : Z) : UnOp.from a = 0 -> is_square a = true.
  Proof.
    intros Ha. unfold is_square. apply orb_true_iff. left.
    apply Z.eqb_eq. exact Ha.
  Qed.

  Lemma is_square_zero : is_square 0 = true.
  Proof. apply is_square_from_zero. unfold UnOp.from. apply Zmod_0_l. Qed.

  (* Squares are quadratic residues: [u * u] is always a square (Euler's
     criterion collapses to Fermat on the nonzero branch; the zero branch is
     handled by [is_square_from_zero]). *)
  Lemma is_square_sq (u : Z) : is_square (u *F u) = true.
  Proof.
    destruct (Z.eq_dec (UnOp.from u) 0) as [Hz | Hnz].
    - apply is_square_from_zero.
      assert (Hmul : u *F u = 0)
        by (rewrite mul_zero_implies_zero; left; exact Hz).
      rewrite Hmul. unfold UnOp.from. apply Zmod_0_l.
    - unfold is_square. apply orb_true_iff. right. apply Z.eqb_eq.
      rewrite modpow_correct by (apply half_nonneg).
      rewrite Fpow_mul_base by (apply half_nonneg).
      rewrite Fpow_sqr by (apply half_nonneg).
      destruct (Z.eq_dec p 2) as [Hp2 | Hpne].
      + assert (He0 : 2 * ((p - 1) / 2) = 0) by (rewrite Hp2; reflexivity).
        rewrite He0. apply Fpow_0.
      + assert (Hp3 : 2 < p) by (pose proof prime_gt1; lia).
        rewrite odd_pm1 by exact Hp3.
        exact (fermat_Fpow u Hnz).
  Qed.

  (* QR multiplicativity: a product of two residues is a residue. *)
  Lemma is_square_mul (a b : Z) :
    is_square a = true -> is_square b = true -> is_square (a *F b) = true.
  Proof.
    intros Ha Hb.
    destruct (Z.eq_dec (UnOp.from a) 0) as [Haz | Hanz].
    - apply is_square_from_zero.
      assert (Hmul : a *F b = 0)
        by (rewrite mul_zero_implies_zero; left; exact Haz).
      rewrite Hmul. unfold UnOp.from. apply Zmod_0_l.
    - destruct (Z.eq_dec (UnOp.from b) 0) as [Hbz | Hbnz].
      + apply is_square_from_zero.
        assert (Hmul : a *F b = 0)
          by (rewrite mul_zero_implies_zero; right; exact Hbz).
        rewrite Hmul. unfold UnOp.from. apply Zmod_0_l.
      + unfold is_square. apply orb_true_iff. right. apply Z.eqb_eq.
        rewrite modpow_correct by (apply half_nonneg).
        rewrite Fpow_mul_base by (apply half_nonneg).
        rewrite (is_square_true_nonzero a Hanz Ha).
        rewrite (is_square_true_nonzero b Hbnz Hb).
        rewrite from_one. unfold BinOp.mul. rewrite Z.mul_1_l.
        pose proof prime_gt1. now rewrite Z.mod_1_l by lia.
  Qed.

  (* Cancelling a square factor on the left: [a] a residue and [a *F b] a
     non-residue force [b] a non-residue (square * non-square = non-square).
     This is the exact form the discriminant step of the sign forcing consumes:
     [a := z - r] (a square, [= u * u]), [a *F b := window_disc] (the
     certified non-residue), yielding [is_square (r + z) = false]. *)
  Lemma is_square_mul_cancel_l (a b : Z) :
    is_square a = true -> is_square (a *F b) = false -> is_square b = false.
  Proof.
    intros Ha Hns.
    pose proof (is_square_false_spec (a *F b) Hns) as [HABnz HABne].
    assert (HBnz : UnOp.from b <> 0).
    { intro Hb. apply HABnz.
      assert (Hmul : a *F b = 0)
        by (rewrite mul_zero_implies_zero; right; exact Hb).
      rewrite Hmul. unfold UnOp.from. apply Zmod_0_l. }
    assert (HAnz : UnOp.from a <> 0).
    { intro Haz. apply HABnz.
      assert (Hmul : a *F b = 0)
        by (rewrite mul_zero_implies_zero; left; exact Haz).
      rewrite Hmul. unfold UnOp.from. apply Zmod_0_l. }
    pose proof (is_square_true_nonzero a HAnz Ha) as HApow.
    unfold is_square. apply orb_false_iff. split.
    - apply Z.eqb_neq. exact HBnz.
    - apply Z.eqb_neq. rewrite modpow_correct by (apply half_nonneg).
      intro HBpow. apply HABne.
      rewrite Fpow_mul_base by (apply half_nonneg).
      rewrite HApow, HBpow, from_one.
      unfold BinOp.mul. rewrite Z.mul_1_l.
      pose proof prime_gt1. now rewrite Z.mod_1_l by lia.
  Qed.

  (* Cancelling a square factor on the right (the commuted form). *)
  Lemma is_square_mul_cancel_r (a b : Z) :
    is_square b = true -> is_square (a *F b) = false -> is_square a = false.
  Proof.
    intros Hb Hns. apply (is_square_mul_cancel_l b a Hb).
    rewrite field_mul_comm. exact Hns.
  Qed.

  (* --- Iterated-squaring helpers specific to Tonelli–Shanks (the general
     field-power and [UnOp.from] facts are in [Field.Lemmas]). --- *)

  Lemma Fpow_two_double (t : Z) (k : nat) :
    Fpow t (2 ^ Z.of_nat k) *F Fpow t (2 ^ Z.of_nat k) = Fpow t (2 ^ Z.of_nat (S k)).
  Proof.
    rewrite Fpow_sqr by (apply Z.pow_nonneg; lia).
    f_equal. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. ring.
  Qed.

  Lemma self_mul_Fpow (t : Z) : t *F t = Fpow t (2 ^ Z.of_nat 1).
  Proof.
    replace (2 ^ Z.of_nat 1) with 2 by reflexivity.
    unfold Fpow, BinOp.mul, UnOp.from. now rewrite Z.pow_2_r.
  Qed.

  Lemma sqrt_one_val (x : Z) :
    x *F x = 1 -> UnOp.from x = 1 \/ UnOp.from x = UnOp.from (-1).
  Proof.
    intros Hx. rewrite <- from_one in Hx.
    destruct (sqrt_one x Hx) as [H1 | H2].
    - left. rewrite H1. apply from_one.
    - right. exact H2.
  Qed.

  (* Iterated squaring composes the exponents of 2. *)
  Lemma Fpow_pow2_mul (c : Z) (x y : nat) :
    Fpow (Fpow c (2 ^ Z.of_nat x)) (2 ^ Z.of_nat y) = Fpow c (2 ^ Z.of_nat (x + y)).
  Proof.
    rewrite Fpow_mul by (apply Z.pow_nonneg; lia).
    f_equal. rewrite Nat2Z.inj_add, Z.pow_add_r by lia. reflexivity.
  Qed.

  (* --- Algorithm pieces (mirroring Sqrt.v) --- *)

  Fixpoint least_i (fuel : nat) (cur : Z) (i : nat) : nat :=
    match fuel with
    | O => i
    | S fuel' =>
        if Z.eqb (UnOp.from cur) 1 then i else least_i fuel' (cur *F cur) (S i)
    end.

  Fixpoint ts_loop (fuel m : nat) (c t r : Z) : Z :=
    match fuel with
    | O => r
    | S fuel' =>
        if Z.eqb (UnOp.from t) 1 then r
        else
          let i := least_i m (t *F t) 1%nat in
          let b := modpow c (2 ^ Z.of_nat (m - i - 1)%nat) in
          let b2 := b *F b in
          ts_loop fuel' i b2 (t *F b2) (r *F b)
    end.

  (* The Tonelli-Shanks loop returns its running accumulator, updated only via
     [*F]; so a reduced initial accumulator stays reduced through to the result. *)
  Lemma ts_loop_reduced :
    forall (fuel m : nat) (c t r : Z),
      UnOp.from r = r -> UnOp.from (ts_loop fuel m c t r) = ts_loop fuel m c t r.
  Proof.
    induction fuel as [| fuel' IH]; intros m c t r Hr; cbn [ts_loop].
    - exact Hr.
    - destruct (UnOp.from t =? 1); [exact Hr |].
      apply IH. apply from_mul_reduced.
  Qed.

  (* [least_i fuel (t^(2^i0)) i0] is the least index >= i0 (within fuel) at which
     [t^(2^.)] becomes 1; everything strictly below it is not 1. *)
  Lemma least_i_spec (t : Z) :
    forall (fuel i0 : nat),
      (i0 <= least_i fuel (Fpow t (2 ^ Z.of_nat i0)) i0 <= i0 + fuel)%nat
      /\ (forall j, (i0 <= j < least_i fuel (Fpow t (2 ^ Z.of_nat i0)) i0)%nat ->
             Fpow t (2 ^ Z.of_nat j) <> 1)
      /\ (forall k, (i0 <= k < i0 + fuel)%nat -> Fpow t (2 ^ Z.of_nat k) = 1 ->
             (least_i fuel (Fpow t (2 ^ Z.of_nat i0)) i0 <= k)%nat
             /\ Fpow t (2 ^ Z.of_nat (least_i fuel (Fpow t (2 ^ Z.of_nat i0)) i0)) = 1).
  Proof.
    intro fuel. induction fuel as [|fuel' IH]; intros i0.
    - cbn [least_i]. split; [lia | split].
      + intros j Hj. exfalso. lia.
      + intros k Hk Hk1. exfalso. lia.
    - cbn [least_i]. rewrite Fpow_reduced. rewrite (Fpow_two_double t i0).
      pose proof (IH (S i0)) as IHs.
      destruct (Fpow t (2 ^ Z.of_nat i0) =? 1) eqn:E.
      + apply Z.eqb_eq in E. split; [lia | split].
        * intros j Hj. exfalso. lia.
        * intros k Hk Hk1. split; [lia | exact E].
      + apply Z.eqb_neq in E. destruct IHs as [Hb [Hmid Hthird]].
        split; [lia | split].
        * intros j Hj. destruct (Nat.eq_dec j i0) as [->|Hjne].
          -- exact E.
          -- apply Hmid. lia.
        * intros k Hk Hk1. destruct (Nat.eq_dec k i0) as [->|Hkne].
          -- exfalso. apply E. exact Hk1.
          -- apply Hthird; [lia | exact Hk1].
  Qed.

  (* The Tonelli-Shanks loop invariant: r^2 = a*t, ord(c) = 2^m (c^(2^(m-1)) = -1),
     t in the 2-Sylow subgroup (t^(2^(m-1)) = 1). On exit (t = 1) we get r^2 = a. *)
  Lemma ts_loop_sound (a : Z) :
    2 < p ->
    forall (fuel m : nat) (c t r : Z),
      (1 <= m)%nat ->
      (m <= fuel)%nat ->
      UnOp.from t <> 0 ->
      UnOp.from c <> 0 ->
      Fpow c (2 ^ Z.of_nat (m - 1)) = UnOp.from (-1) ->
      Fpow t (2 ^ Z.of_nat (m - 1)) = 1 ->
      r *F r = a *F t ->
      ts_loop fuel m c t r *F ts_loop fuel m c t r = UnOp.from a.
  Proof.
    intros Hp3 fuel. induction fuel as [|fuel' IH];
      intros m c t r Hm1 Hmfuel Ht0 Hc0 Hcinv Htinv Hr2.
    - exfalso. lia.
    - cbn [ts_loop]. destruct (UnOp.from t =? 1) eqn:Eg.
      + apply Z.eqb_eq in Eg. rewrite Hr2. apply mul_one_r. exact Eg.
      + apply Z.eqb_neq in Eg.
        assert (Hm2 : (2 <= m)%nat).
        { destruct (le_lt_dec 2 m) as [Hle|Hlt]; [exact Hle|].
          assert (Hm_eq : m = 1%nat) by lia. subst m.
          exfalso. apply Eg.
          replace (2 ^ Z.of_nat (1 - 1)) with 1 in Htinv by reflexivity.
          rewrite Fpow_1 in Htinv. exact Htinv. }
        pose proof (least_i_spec t m 1) as Lspec.
        rewrite <- self_mul_Fpow in Lspec.
        set (i := least_i m (t *F t) 1) in *.
        destruct Lspec as [Hib [Hiless Hihit]].
        assert (Hile : (i <= m - 1)%nat /\ Fpow t (2 ^ Z.of_nat i) = 1).
        { apply Hihit; [lia | exact Htinv]. }
        destruct Hile as [Hile1 Hihit_i].
        assert (Htim1 : Fpow t (2 ^ Z.of_nat (i - 1)) = UnOp.from (-1)).
        { assert (Hsq : Fpow t (2 ^ Z.of_nat (i - 1)) *F Fpow t (2 ^ Z.of_nat (i - 1)) = 1).
          { rewrite Fpow_two_double. replace (S (i - 1)) with i by lia. exact Hihit_i. }
          destruct (sqrt_one_val _ Hsq) as [H1 | H2].
          - exfalso. rewrite Fpow_reduced in H1.
            destruct (Nat.eq_dec i 1) as [Hi1|Hine].
            + rewrite Hi1 in H1.
              replace (2 ^ Z.of_nat (1 - 1)) with 1 in H1 by reflexivity.
              rewrite Fpow_1 in H1. apply Eg. exact H1.
            + apply (Hiless (i - 1)%nat); [lia | exact H1].
          - rewrite Fpow_reduced in H2. exact H2. }
        remember (modpow c (2 ^ Z.of_nat (m - i - 1))) as b eqn:Hb.
        assert (Hbf : b = Fpow c (2 ^ Z.of_nat (m - i - 1))).
        { rewrite Hb. apply modpow_correct. apply Z.pow_nonneg; lia. }
        assert (Hbnz : UnOp.from b <> 0).
        { rewrite Hbf, Fpow_reduced.
          apply Fpow_nonzero; [apply Z.pow_nonneg; lia | exact Hc0]. }
        assert (Hb2nz : UnOp.from (b *F b) <> 0).
        { apply field_from_mul_nonzero; exact Hbnz. }
        assert (Hb2 : b *F b = Fpow c (2 ^ Z.of_nat (m - i))).
        { rewrite Hbf, Fpow_two_double.
          replace (S (m - i - 1)) with (m - i)%nat by lia. reflexivity. }
        apply IH.
        * lia.
        * lia.
        * apply field_from_mul_nonzero; [exact Ht0 | exact Hb2nz].
        * exact Hb2nz.
        * rewrite Hb2, Fpow_pow2_mul.
          replace ((m - i) + (i - 1))%nat with (m - 1)%nat by lia. exact Hcinv.
        * rewrite Fpow_mul_base by (apply Z.pow_nonneg; lia). rewrite Htim1.
          rewrite Hb2, Fpow_pow2_mul.
          replace ((m - i) + (i - 1))%nat with (m - 1)%nat by lia.
          rewrite Hcinv. apply neg1_sq.
        * rewrite (field_mul_swap_inner r b r b). rewrite Hr2.
          rewrite field_mul_assoc. reflexivity.
  Qed.

  (* --- 2-adic factorisation [split_two] --- *)

  Fixpoint split_two (fuel : nat) (n : Z) : nat * Z :=
    match fuel with
    | O => (O, n)
    | S fuel' =>
        if Z.even n then let '(s, q) := split_two fuel' (n / 2) in (S s, q)
        else (O, n)
    end.

  Lemma split_two_factor : forall fuel n s q,
    split_two fuel n = (s, q) -> n = q * 2 ^ Z.of_nat s.
  Proof.
    induction fuel as [|fuel' IH]; intros n s q Hsplit.
    - cbn [split_two] in Hsplit. injection Hsplit as Hs Hq. subst.
      replace (2 ^ Z.of_nat 0) with 1 by reflexivity. lia.
    - cbn [split_two] in Hsplit. destruct (Z.even n) eqn:E.
      + destruct (split_two fuel' (n / 2)) as [s' q'] eqn:Hsq'.
        injection Hsplit as Hs Hq. subst.
        pose proof (IH (n / 2) s' q Hsq') as IHeq.
        apply Zeven_bool_iff in E.
        pose proof (Zeven_div2 n E) as Hn2. rewrite Z.div2_div in Hn2.
        rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
        rewrite Hn2, IHeq. ring.
      + injection Hsplit as Hs Hq. subst.
        replace (2 ^ Z.of_nat 0) with 1 by reflexivity. lia.
  Qed.

  Lemma split_two_odd : forall fuel n,
    1 <= n -> n < 2 ^ Z.of_nat fuel -> Z.odd (snd (split_two fuel n)) = true.
  Proof.
    induction fuel as [|fuel' IH]; intros n Hn Hlt.
    - replace (2 ^ Z.of_nat 0) with 1 in Hlt by reflexivity. lia.
    - cbn [split_two]. destruct (Z.even n) eqn:E.
      + destruct (split_two fuel' (n / 2)) as [s' q'] eqn:Hsq'. cbn [snd].
        pose proof (IH (n / 2)) as IHn. rewrite Hsq' in IHn. cbn [snd] in IHn.
        apply IHn.
        * apply Zeven_bool_iff in E. pose proof (Zeven_div2 n E) as Hn2.
          rewrite Z.div2_div in Hn2. lia.
        * rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hlt by lia.
          apply Zeven_bool_iff in E. pose proof (Zeven_div2 n E) as Hn2.
          rewrite Z.div2_div in Hn2. lia.
      + cbn [snd]. rewrite <- Z.negb_even, E. reflexivity.
  Qed.

  Lemma split_two_succ_even : forall fuel n,
    Z.even n = true -> (1 <= fst (split_two (S fuel) n))%nat.
  Proof.
    intros fuel n He. cbn [split_two]. rewrite He.
    destruct (split_two fuel (n / 2)). cbn [fst]. lia.
  Qed.

  Lemma split_two_pm1 : forall s q,
    2 < p ->
    split_two (S (Z.to_nat (Z.log2 p))) (p - 1) = (s, q) ->
    p - 1 = q * 2 ^ Z.of_nat s /\ Z.odd q = true /\ (1 <= s)%nat /\ 1 <= q.
  Proof.
    intros s q Hp3 Hsplit.
    pose proof (@is_prime p _) as Hp. unfold IsPrime in Hp.
    assert (Hpodd : p mod 2 = 1).
    { assert (H2 : ~ (2 | p)).
      { intro Hd. pose proof (Znumtheory.prime_divisors p Hp 2 Hd). lia. }
      destruct (Z.eq_dec (p mod 2) 0) as [Hc|Hc].
      - exfalso. apply H2. apply Z.mod_divide; [lia | exact Hc].
      - pose proof (Z.mod_pos_bound p 2 ltac:(lia)). lia. }
    pose proof (split_two_factor _ _ _ _ Hsplit) as Hfac.
    assert (Hbound : p - 1 < 2 ^ Z.of_nat (S (Z.to_nat (Z.log2 p)))).
    { rewrite Nat2Z.inj_succ. rewrite Z2Nat.id by (apply Z.log2_nonneg).
      pose proof (Z.log2_spec p ltac:(lia)). lia. }
    pose proof (split_two_odd (S (Z.to_nat (Z.log2 p))) (p - 1) ltac:(lia) Hbound) as Hoddq.
    rewrite Hsplit in Hoddq. cbn [snd] in Hoddq.
    assert (Hev : Z.even (p - 1) = true).
    { apply Zeven_bool_iff. apply Zeven_equiv. exists ((p - 1) / 2).
      pose proof (Z.div_mod (p - 1) 2 ltac:(lia)). lia. }
    pose proof (split_two_succ_even (Z.to_nat (Z.log2 p)) (p - 1) Hev) as Hs1.
    rewrite Hsplit in Hs1. cbn [fst] in Hs1.
    assert (Hpow1 : 0 < 2 ^ Z.of_nat s) by (apply Z.pow_pos_nonneg; lia).
    split; [exact Hfac | split; [exact Hoddq | split; [exact Hs1 | nia]]].
  Qed.

  (* --- Entry gluing: the loop started from the algorithm's initial state is
     sound, given a genuine non-residue z and the 2-adic data of p-1. --- *)
  Lemma ts_entry_sound (a z : Z) (s : nat) (q : Z) :
    2 < p ->
    UnOp.from a <> 0 ->
    is_square a = true ->
    is_square z = false ->
    p - 1 = q * 2 ^ Z.of_nat s ->
    Z.odd q = true ->
    (1 <= s)%nat ->
    1 <= q ->
    ts_loop s s (modpow z q) (modpow a q) (modpow a ((q + 1) / 2)) *F
    ts_loop s s (modpow z q) (modpow a q) (modpow a ((q + 1) / 2)) = UnOp.from a.
  Proof.
    intros Hp3 Ha Hsqa Hnsz Hfac Hqodd Hs1 Hq1.
    assert (Hq0 : 0 <= q) by lia.
    assert (Hqh0 : 0 <= (q + 1) / 2) by (apply Z.div_pos; lia).
    pose proof (is_square_false_spec z Hnsz) as [Hznz _].
    assert (Hs2 : 2 ^ Z.of_nat s = 2 * 2 ^ Z.of_nat (s - 1)).
    { replace (Z.of_nat s) with (Z.of_nat (s - 1) + 1) by lia.
      rewrite Z.pow_add_r by lia. rewrite Z.pow_1_r. ring. }
    assert (Hhalf : (p - 1) / 2 = q * 2 ^ Z.of_nat (s - 1)).
    { rewrite Hfac, Hs2.
      replace (q * (2 * 2 ^ Z.of_nat (s - 1)))
        with ((q * 2 ^ Z.of_nat (s - 1)) * 2) by ring.
      rewrite Z.div_mul by lia. reflexivity. }
    rewrite (modpow_correct z q Hq0).
    rewrite (modpow_correct a q Hq0).
    rewrite (modpow_correct a ((q + 1) / 2) Hqh0).
    apply (ts_loop_sound a Hp3).
    - exact Hs1.
    - lia.
    - rewrite Fpow_reduced. apply Fpow_nonzero; [exact Hq0 | exact Ha].
    - rewrite Fpow_reduced. apply Fpow_nonzero; [exact Hq0 | exact Hznz].
    - rewrite Fpow_mul by (first [assumption | (apply Z.pow_nonneg; lia)]).
      rewrite <- Hhalf. apply (nonresidue_pow z Hp3 Hnsz).
    - rewrite Fpow_mul by (first [assumption | (apply Z.pow_nonneg; lia)]).
      rewrite <- Hhalf. rewrite (is_square_true_nonzero a Ha Hsqa). apply from_one.
    - rewrite Fpow_sqr by exact Hqh0. rewrite Fpow_succ_l by exact Hq0.
      f_equal. apply Z.odd_spec in Hqodd. destruct Hqodd as [m Hm]. lia.
  Qed.

  (* --- Polynomial root bound (for non-residue existence) --- *)

  (* Horner evaluation of a coefficient list (low to high degree). *)
  Fixpoint peval (cs : list Z) (x : Z) : Z :=
    match cs with
    | [] => 0
    | c :: cs' => c + x * peval cs' x
    end.

  (* Quotient of [cs] by [X - a] (drops the remainder), one degree shorter. *)
  Fixpoint quo (cs : list Z) (a : Z) : list Z :=
    match cs with
    | [] => []
    | c :: cs' =>
        match cs' with
        | [] => []
        | _ => peval cs' a :: quo cs' a
        end
    end.

  Lemma quo_cons : forall c cs' a,
    cs' <> [] -> quo (c :: cs') a = peval cs' a :: quo cs' a.
  Proof. intros c cs' a Hne. destruct cs'; [contradiction | reflexivity]. Qed.

  Lemma quo_length : forall cs a,
    Datatypes.length (quo cs a) = (Datatypes.length cs - 1)%nat.
  Proof.
    induction cs as [|c cs' IH]; intros a; [reflexivity|].
    destruct cs' as [|c' cs'']; [reflexivity|].
    rewrite quo_cons by discriminate. cbn [Datatypes.length].
    rewrite IH. cbn [Datatypes.length]. lia.
  Qed.

  (* Factor theorem: cs(x) = cs(a) + (x - a) * quo(x). *)
  Lemma peval_factor : forall cs a x,
    peval cs x = peval cs a + (x - a) * peval (quo cs a) x.
  Proof.
    induction cs as [|c cs' IH]; intros a x; [cbn; ring|].
    destruct cs' as [|c' cs''] eqn:E.
    - cbn. ring.
    - rewrite <- E. rewrite <- E in IH.
      assert (Hne : cs' <> []) by (rewrite E; discriminate).
      rewrite (quo_cons c cs' a Hne).
      cbn [peval]. rewrite (IH a x). ring.
  Qed.

  (* A polynomial of degree < (length cs) with [length cs] or more distinct
     residue roots is identically zero mod p. *)
  Lemma root_bound : forall (n : nat) (cs xs : list Z),
    (Datatypes.length cs <= n)%nat ->
    NoDup (map (fun x => x mod p) xs) ->
    (forall x, In x xs -> peval cs x mod p = 0) ->
    (Datatypes.length xs <= Datatypes.length cs - 1)%nat
    \/ (forall y, peval cs y mod p = 0).
  Proof.
    induction n as [|n' IH]; intros cs xs Hlen Hnodup Hroots.
    - destruct cs as [|c cs'].
      + right. intros y. apply Zmod_0_l.
      + exfalso. cbn [Datatypes.length] in Hlen. lia.
    - destruct cs as [|c0 cs'].
      + right. intros y. apply Zmod_0_l.
      + destruct cs' as [|c1 cs1].
        * destruct xs as [|a xs'].
          -- left. cbn [Datatypes.length]. lia.
          -- right. intros y.
             assert (Hc0 : c0 mod p = 0).
             { specialize (Hroots a (or_introl eq_refl)). cbn [peval] in Hroots.
               replace (c0 + a * 0) with c0 in Hroots by ring. exact Hroots. }
             cbn [peval]. replace (c0 + y * 0) with c0 by ring. exact Hc0.
        * destruct xs as [|a xs'].
          -- left. cbn [Datatypes.length]. lia.
          -- cbn [map] in Hnodup. rewrite NoDup_cons_iff in Hnodup.
             destruct Hnodup as [Hnotin Hnd].
             assert (Haroot : peval (c0 :: c1 :: cs1) a mod p = 0)
               by (apply Hroots; left; reflexivity).
             assert (Hquoroots : forall b, In b xs' ->
                       peval (quo (c0 :: c1 :: cs1) a) b mod p = 0).
             { intros b Hb.
               assert (Hbroot : peval (c0 :: c1 :: cs1) b mod p = 0)
                 by (apply Hroots; right; exact Hb).
               pose proof (peval_factor (c0 :: c1 :: cs1) a b) as Hf.
               rewrite Hf in Hbroot.
               rewrite Zplus_mod, Haroot, Z.add_0_l, Zmod_mod in Hbroot.
               assert (Hbane : (b - a) mod p <> 0).
               { intro Hc.
                 assert (Hba : b mod p = a mod p).
                 { apply sub_zero_equiv in Hc. unfold UnOp.from in Hc. exact Hc. }
                 apply Hnotin. rewrite <- Hba.
                 apply (in_map (fun x : Z => x mod p)). exact Hb. }
               assert (Hmul0 : BinOp.mul (b - a)
                                 (peval (quo (c0 :: c1 :: cs1) a) b) = 0)
                 by exact Hbroot.
               rewrite mul_zero_implies_zero in Hmul0.
               destruct Hmul0 as [Hz | Hz]; unfold UnOp.from in Hz.
               - contradiction.
               - exact Hz. }
             assert (Hlenquo :
                       (Datatypes.length (quo (c0 :: c1 :: cs1) a) <= n')%nat).
             { rewrite quo_length. cbn [Datatypes.length] in Hlen |- *. lia. }
             destruct (IH (quo (c0 :: c1 :: cs1) a) xs' Hlenquo Hnd Hquoroots)
               as [Hle | Hzero].
             ++ left. rewrite quo_length in Hle.
                cbn [Datatypes.length] in Hle |- *. lia.
             ++ right. intros y.
                pose proof (peval_factor (c0 :: c1 :: cs1) a y) as Hf.
                rewrite Hf. rewrite Zplus_mod, Haroot, Z.add_0_l, Zmod_mod.
                rewrite Zmult_mod, (Hzero y), Z.mul_0_r, Zmod_0_l. reflexivity.
  Qed.

  (* The polynomial X^d - 1 and its evaluation. *)
  Lemma peval_zeros_one : forall (k : nat) (x : Z),
    peval (repeat 0 k ++ [1]) x = x ^ Z.of_nat k.
  Proof.
    induction k as [|k' IH]; intros x.
    - cbn [repeat app peval]. rewrite Z.pow_0_r. ring.
    - cbn [repeat app peval]. rewrite IH.
      rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. ring.
  Qed.

  Definition poly_d (d : nat) : list Z := (-1) :: (repeat 0 (d - 1) ++ [1]).

  Lemma poly_d_length : forall d,
    (1 <= d)%nat -> Datatypes.length (poly_d d) = (d + 1)%nat.
  Proof.
    intros d Hd. unfold poly_d. cbn [Datatypes.length].
    rewrite length_app, repeat_length. cbn [Datatypes.length]. lia.
  Qed.

  Lemma peval_poly_d : forall d x,
    (1 <= d)%nat -> peval (poly_d d) x = x ^ Z.of_nat d - 1.
  Proof.
    intros d x Hd. unfold poly_d. cbn [peval].
    rewrite peval_zeros_one.
    replace (Z.of_nat (d - 1)) with (Z.of_nat d - 1) by lia.
    rewrite <- (Z.pow_succ_r x (Z.of_nat d - 1)) by lia.
    replace (Z.succ (Z.of_nat d - 1)) with (Z.of_nat d) by lia.
    ring.
  Qed.

  Lemma is_square_one : is_square 1 = true.
  Proof.
    unfold is_square. apply orb_true_iff. right.
    apply Z.eqb_eq. rewrite modpow_correct by (apply half_nonneg).
    unfold Fpow. now rewrite Z.pow_1_l by (apply half_nonneg).
  Qed.

  (* The list [k; k-1; ...; 1] of nonzero residues. *)
  Fixpoint range1 (k : nat) : list Z :=
    match k with O => [] | S k' => Z.of_nat (S k') :: range1 k' end.

  Lemma range1_length : forall k, Datatypes.length (range1 k) = k.
  Proof. induction k as [|k' IH]; cbn; [reflexivity | now rewrite IH]. Qed.

  Lemma range1_In : forall k e, In e (range1 k) -> 1 <= e <= Z.of_nat k.
  Proof.
    induction k as [|k' IH]; intros e Hin; cbn [range1] in Hin.
    - contradiction.
    - destruct Hin as [<- | Hin].
      + rewrite Nat2Z.inj_succ; lia.
      + apply IH in Hin. rewrite Nat2Z.inj_succ; lia.
  Qed.

  Lemma range1_NoDup_mod : forall k,
    Z.of_nat k < p -> NoDup (map (fun x => x mod p) (range1 k)).
  Proof.
    induction k as [|k' IH]; intros Hk.
    - cbn. constructor.
    - cbn [range1 map]. apply NoDup_cons.
      + intro Hin. apply in_map_iff in Hin. destruct Hin as [e [Heq He]].
        apply range1_In in He. rewrite Nat2Z.inj_succ in Hk.
        rewrite (Z.mod_small e p) in Heq by lia.
        rewrite (Z.mod_small (Z.of_nat (S k')) p) in Heq by (rewrite Nat2Z.inj_succ; lia).
        rewrite Nat2Z.inj_succ in Heq. lia.
      + apply IH. rewrite Nat2Z.inj_succ in Hk. lia.
  Qed.

  (* Constructive finite search for a non-residue. *)
  Lemma find_false_in_range : forall (lo : Z) (k : nat),
    (forall z, lo <= z < lo + Z.of_nat k -> is_square z = true)
    \/ (exists z, lo <= z < lo + Z.of_nat k /\ is_square z = false).
  Proof.
    intros lo k. induction k as [|k' IH].
    - left. intros z Hz. cbn in Hz. lia.
    - destruct IH as [Hall | Hex].
      + destruct (is_square (lo + Z.of_nat k')) eqn:E.
        * left. intros z Hz. rewrite Nat2Z.inj_succ in Hz.
          destruct (Z.eq_dec z (lo + Z.of_nat k')) as [-> | Hne].
          -- exact E.
          -- apply Hall. lia.
        * right. exists (lo + Z.of_nat k').
          rewrite Nat2Z.inj_succ. split; [lia | exact E].
      + destruct Hex as [z [Hz Hsq]]. right. exists z.
        rewrite Nat2Z.inj_succ. split; [lia | exact Hsq].
  Qed.

  (* A quadratic non-residue exists in [2, p). *)
  Lemma nonresidue_exists : 2 < p -> exists z, 2 <= z < p /\ is_square z = false.
  Proof.
    intros Hp3. pose proof prime_gt1 as Hp1.
    destruct (find_false_in_range 2 (Z.to_nat (p - 2))) as [Hall | Hex].
    2:{ destruct Hex as [z [Hz Hsq]]. exists z. rewrite Z2Nat.id in Hz by lia.
        split; [lia | exact Hsq]. }
    exfalso.
    set (d := Z.to_nat ((p - 1) / 2)).
    set (units := range1 (Z.to_nat (p - 1))).
    assert (Hd1 : (1 <= d)%nat).
    { unfold d. assert (1 <= (p - 1) / 2) by lia. lia. }
    assert (Hroots : forall e, In e units -> peval (poly_d d) e mod p = 0).
    { intros e He. unfold units in He. apply range1_In in He.
      rewrite Z2Nat.id in He by lia.
      assert (Hsqe : is_square e = true).
      { destruct (Z.eq_dec e 1) as [-> | Hne].
        - apply is_square_one.
        - apply Hall. rewrite Z2Nat.id by lia. lia. }
      assert (Hez : UnOp.from e <> 0).
      { unfold UnOp.from. rewrite Z.mod_small by lia. lia. }
      pose proof (is_square_true_nonzero e Hez Hsqe) as Hfe.
      rewrite peval_poly_d by exact Hd1.
      unfold d. rewrite Z2Nat.id by (apply half_nonneg).
      rewrite Zminus_mod. unfold Fpow, UnOp.from in Hfe. rewrite Hfe.
      rewrite Z.sub_diag. apply Zmod_0_l. }
    assert (Hnodup : NoDup (map (fun x => x mod p) units)).
    { unfold units. apply range1_NoDup_mod. rewrite Z2Nat.id by lia. lia. }
    assert (Hlu : Datatypes.length units = Z.to_nat (p - 1))
      by (unfold units; apply range1_length).
    destruct (root_bound (Datatypes.length (poly_d d)) (poly_d d) units
                (le_n _) Hnodup Hroots) as [Hle | Hzero].
    - rewrite poly_d_length in Hle by exact Hd1. rewrite Hlu in Hle. unfold d in Hle.
      assert (Hlt : (Z.to_nat ((p - 1) / 2) < Z.to_nat (p - 1))%nat) by lia.
      lia.
    - specialize (Hzero 0). rewrite peval_poly_d in Hzero by exact Hd1.
      rewrite Z.pow_0_l in Hzero by lia.
      replace (0 - 1) with (-1) in Hzero by ring.
      apply Z.mod_divide in Hzero; [| lia].
      apply Z.divide_opp_r in Hzero. apply Z.divide_1_r in Hzero. lia.
  Qed.

  (* Total search for the least quadratic non-residue at or above [z]. It is
     defined by well-founded recursion on the measure [p - z]: a non-residue
     always exists below [p], so the search terminates. The accessibility proof
     is wrapped in [Acc_intro_generator] so that [vm_compute] reduces the few
     real steps without forcing the (huge) [nat] measure — the search stays
     computable even for cryptographic-size primes. *)
  Definition fnr_meas (z : Z) : nat := Z.to_nat (p - z).
  Definition fnr_R (a b : Z) : Prop := (fnr_meas a < fnr_meas b)%nat.
  Definition fnr_wf : well_founded fnr_R := well_founded_ltof Z fnr_meas.

  Lemma fnr_dec : forall z, z < p -> fnr_R (z + 1) z.
  Proof. intros z Hlt. unfold fnr_R, fnr_meas. apply Z2Nat.inj_lt; lia. Qed.

  Definition fnr_body (z : Z) (rec : forall y, fnr_R y z -> Z) : Z :=
    match Z_lt_le_dec z p with
    | left Hlt => if is_square z then rec (z + 1) (fnr_dec z Hlt) else z
    | right _ => z
    end.

  Lemma fnr_body_ext : forall x f g,
    (forall y q, f y q = g y q) -> fnr_body x f = fnr_body x g.
  Proof.
    intros x f g Hfg. unfold fnr_body.
    destruct (Z_lt_le_dec x p); [|reflexivity].
    destruct (is_square x); [apply Hfg | reflexivity].
  Qed.

  Definition find_nonresidue (z : Z) : Z :=
    Fix (Acc_intro_generator 256 fnr_wf) (fun _ => Z) fnr_body z.

  Lemma find_nonresidue_eq : forall z,
    find_nonresidue z = fnr_body z (fun y _ => find_nonresidue y).
  Proof.
    intro z. unfold find_nonresidue.
    exact (@Fix_eq Z fnr_R (Acc_intro_generator 256 fnr_wf)
             (fun _ => Z) fnr_body fnr_body_ext z).
  Qed.

  Lemma find_nonresidue_sound : forall (n : nat) (z0 : Z),
    2 < p ->
    (Z.to_nat (p - z0) <= n)%nat ->
    (exists w, z0 <= w < p /\ is_square w = false) ->
    is_square (find_nonresidue z0) = false.
  Proof.
    induction n as [|n' IH]; intros z0 Hp3 Hmeas Hex.
    - exfalso. destruct Hex as [w [Hw _]]. lia.
    - rewrite find_nonresidue_eq. unfold fnr_body.
      destruct (Z_lt_le_dec z0 p) as [Hlt | Hge].
      + destruct (is_square z0) eqn:Esq.
        * apply (IH (z0 + 1) Hp3).
          -- lia.
          -- destruct Hex as [w [Hw Hwf]]. exists w. split; [|exact Hwf].
             assert (w <> z0) by (intro Heq; subst; rewrite Esq in Hwf; discriminate).
             lia.
        * exact Esq.
      + exfalso. destruct Hex as [w [Hw _]]. lia.
  Qed.

  Lemma find_nonresidue_correct : 2 < p -> is_square (find_nonresidue 2) = false.
  Proof.
    intros Hp3.
    apply (find_nonresidue_sound (Z.to_nat (p - 2)) 2 Hp3 (le_n _)).
    apply nonresidue_exists. exact Hp3.
  Qed.

  Definition field_sqrt (n : Z) : Z :=
    if Z.eqb (UnOp.from n) 0 then 0
    else
      let fuel := S (Z.to_nat (Z.log2 p)) in
      let '(s, q) := split_two fuel (p - 1) in
      let z := find_nonresidue 2 in
      ts_loop s s (modpow z q) (modpow n q) (modpow n ((q + 1) / 2)).

  Lemma field_sqrt_sound (a : Z) :
    is_square a = true -> field_sqrt a *F field_sqrt a = UnOp.from a.
  Proof.
    intros Hsq. unfold field_sqrt.
    destruct (UnOp.from a =? 0) eqn:E0.
    - apply Z.eqb_eq in E0.
      unfold BinOp.mul. rewrite Z.mul_0_l, Zmod_0_l. symmetry. exact E0.
    - apply Z.eqb_neq in E0.
      destruct (Z.eq_dec p 2) as [Hp2 | Hpne2].
      + (* p = 2 *)
        assert (Hsplit2 : split_two (S (Z.to_nat (Z.log2 p))) (p - 1) = (0%nat, 1))
          by (rewrite Hp2; reflexivity).
        rewrite Hsplit2. cbn [ts_loop].
        replace ((1 + 1) / 2) with 1 by reflexivity.
        cbn [modpow modpow_pos].
        assert (Ha1 : UnOp.from a = 1).
        { unfold UnOp.from in E0 |- *.
          pose proof (Z.mod_pos_bound a p ltac:(pose proof prime_gt1; lia)) as Hb. lia. }
        rewrite Ha1. unfold BinOp.mul.
        rewrite Z.mul_1_r, Z.mod_1_l by (pose proof prime_gt1; lia). reflexivity.
      + (* p > 2 *)
        assert (Hp3 : 2 < p).
        { pose proof (@is_prime p _) as Hpp. apply Znumtheory.prime_ge_2 in Hpp. lia. }
        destruct (split_two (S (Z.to_nat (Z.log2 p))) (p - 1)) as [s q] eqn:Hsplit.
        pose proof (split_two_pm1 s q Hp3 Hsplit) as [Hfac [Hqodd [Hs1 Hq1]]].
        apply (ts_entry_sound a (find_nonresidue 2) s q Hp3 E0 Hsq).
        * apply find_nonresidue_correct. exact Hp3.
        * exact Hfac.
        * exact Hqodd.
        * exact Hs1.
        * exact Hq1.
  Qed.

  (* [field_sqrt] always returns a value reduced mod [p] (either [0] or the
     Tonelli-Shanks accumulator, whose initial value [modpow ..] is reduced). *)
  Lemma field_sqrt_reduced (n : Z) : UnOp.from (field_sqrt n) = field_sqrt n.
  Proof.
    unfold field_sqrt. destruct (UnOp.from n =? 0).
    - unfold UnOp.from. apply Zmod_0_l.
    - destruct (split_two (S (Z.to_nat (Z.log2 p))) (p - 1)) as [s q].
      apply ts_loop_reduced. apply modpow_reduced.
  Qed.

End FieldSqrt.
