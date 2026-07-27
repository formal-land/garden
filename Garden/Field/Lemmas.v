Require Import Garden.Field.Field.
Require Import Stdlib.ZArith.Zpow_facts.

Global Open Scope Z_scope.

(* Ring and integral-domain facts for the field operations [UnOp.from] and
   [BinOp.add/sub/mul] (reduced modulo a prime [p]), parametric in any
   [{p : Z} `{Prime p}]. The point-addition determinism proofs use them at the
   Pallas base field to clear the field-division gradient and the nonzero
   [x_p - x_q] / [x_p - x_q]^2 / [2 y_p] factors. *)

(* The result of [BinOp.sub] / [BinOp.mul] is reduced modulo [p]. *)
Lemma from_sub_reduced {p : Z} `{Prime p} (a b : Z) :
    UnOp.from (BinOp.sub a b) = BinOp.sub a b.
Proof.
  unfold UnOp.from, BinOp.sub. apply Zmod_mod.
Qed.

Lemma from_mul_reduced {p : Z} `{Prime p} (a b : Z) :
    UnOp.from (BinOp.mul a b) = BinOp.mul a b.
Proof.
  unfold UnOp.from, BinOp.mul. apply Zmod_mod.
Qed.

Lemma field_mul_comm {p : Z} `{Prime p} (a b : Z) :
    BinOp.mul a b = BinOp.mul b a.
Proof.
  unfold BinOp.mul. now rewrite Z.mul_comm.
Qed.

Lemma field_mul_assoc {p : Z} `{Prime p} (a b c : Z) :
    BinOp.mul (BinOp.mul a b) c = BinOp.mul a (BinOp.mul b c).
Proof.
  unfold BinOp.mul.
  rewrite Zmult_mod_idemp_l, Zmult_mod_idemp_r.
  f_equal. ring.
Qed.

Lemma field_mul_swap_inner {p : Z} `{Prime p} (a b c d : Z) :
    BinOp.mul (BinOp.mul a b) (BinOp.mul c d) =
    BinOp.mul (BinOp.mul a c) (BinOp.mul b d).
Proof.
  unfold BinOp.mul.
  rewrite !Zmult_mod_idemp_l, !Zmult_mod_idemp_r.
  f_equal. ring.
Qed.

Lemma field_mul_cancel_r {p : Z} `{Prime p} (a b c : Z) :
    UnOp.from c <> 0 ->
    BinOp.mul a c = BinOp.mul b c ->
    UnOp.from a = UnOp.from b.
Proof.
  intros Hc Heq.
  assert (Hzero : BinOp.mul (BinOp.sub a b) c = 0).
  { unfold BinOp.mul, BinOp.sub in *.
    rewrite Zmult_mod_idemp_l.
    replace ((a - b) * c) with (a * c - b * c) by ring.
    rewrite Zminus_mod, Heq, Z.sub_diag.
    apply Zmod_0_l. }
  rewrite mul_zero_implies_zero in Hzero.
  destruct Hzero as [Hz | Hz].
  - rewrite from_sub_reduced in Hz.
    now rewrite sub_zero_equiv in Hz.
  - contradiction.
Qed.

(* Solve a nonexceptional coordinate constraint for the reduced next-row cell:
   from [m - a - b - c = 0] (field) with [c] reduced, [c = m - a - b]. *)
Lemma field_solve_xr {p : Z} `{Prime p} (m a b c : Z) :
    UnOp.from c = c ->
    UnOp.from (m -F a -F b -F c) = 0 ->
    c = m -F a -F b.
Proof.
  intros Hc Hh.
  rewrite from_sub_reduced in Hh.
  apply sub_zero_equiv in Hh.
  rewrite from_sub_reduced, Hc in Hh.
  symmetry. exact Hh.
Qed.

Lemma field_solve_yr {p : Z} `{Prime p} (m a c : Z) :
    UnOp.from c = c ->
    UnOp.from (m -F a -F c) = 0 ->
    c = m -F a.
Proof.
  intros Hc Hh.
  rewrite from_sub_reduced in Hh.
  apply sub_zero_equiv in Hh.
  rewrite from_sub_reduced, Hc in Hh.
  symmetry. exact Hh.
Qed.

Lemma field_add_comm {p : Z} `{Prime p} (a b : Z) :
    BinOp.add a b = BinOp.add b a.
Proof.
  unfold BinOp.add. now rewrite Z.add_comm.
Qed.

Lemma field_mul_cong {p : Z} `{Prime p} (a b c d : Z) :
    UnOp.from a = UnOp.from c ->
    UnOp.from b = UnOp.from d ->
    BinOp.mul a b = BinOp.mul c d.
Proof.
  intros Hac Hbd.
  unfold BinOp.mul, UnOp.from in *.
  rewrite Zmult_mod, Hac, Hbd, <- Zmult_mod.
  reflexivity.
Qed.

Lemma field_mul_eq_zero_cancel {p : Z} `{Prime p} (a b : Z) :
    UnOp.from a <> 0 ->
    BinOp.mul a b = 0 ->
    UnOp.from b = 0.
Proof.
  intros Ha Hab.
  rewrite mul_zero_implies_zero in Hab.
  destruct Hab as [Hz | Hz]; [contradiction | exact Hz].
Qed.

Lemma field_mul_sub_distr {p : Z} `{Prime p} (a b c : Z) :
    BinOp.mul a (BinOp.sub b c) =
    BinOp.sub (BinOp.mul a b) (BinOp.mul a c).
Proof.
  unfold BinOp.mul, BinOp.sub.
  rewrite Zmult_mod_idemp_r, <- Zminus_mod.
  f_equal. ring.
Qed.

Lemma field_from_mul_nonzero {p : Z} `{Prime p} (a b : Z) :
    UnOp.from a <> 0 ->
    UnOp.from b <> 0 ->
    UnOp.from (BinOp.mul a b) <> 0.
Proof.
  intros Ha Hb Hcontra.
  rewrite from_mul_reduced in Hcontra.
  rewrite mul_zero_implies_zero in Hcontra.
  destruct Hcontra; [apply Ha | apply Hb]; assumption.
Qed.

(* Field exponentiation [Fpow a n = a^n mod p] and general field-algebra facts,
   reusable beyond the square-root development (Fermat / Euler's criterion live
   in [Field.Sqrt], which needs [Field.Fermat]). *)
Section FieldPow.
  Context {p : Z} `{Prime p}.

  Lemma prime_gt1 : 1 < p.
  Proof. exact (prime_range (p := p)). Qed.

  Lemma half_nonneg : 0 <= (p - 1) / 2.
  Proof. pose proof prime_gt1. apply Z.div_pos; lia. Qed.

  Lemma from_idem (x : Z) : UnOp.from (UnOp.from x) = UnOp.from x.
  Proof. unfold UnOp.from. pose proof prime_gt1. now rewrite Z.mod_mod by lia. Qed.

  Lemma from_one : UnOp.from 1 = 1.
  Proof. unfold UnOp.from. pose proof prime_gt1. now rewrite Z.mod_1_l by lia. Qed.

  Lemma mul_left_reduce (a x : Z) : a *F x = UnOp.from a *F x.
  Proof. unfold BinOp.mul, UnOp.from. now rewrite Zmult_mod_idemp_l. Qed.

  Lemma mul_one_r (a t : Z) : UnOp.from t = 1 -> a *F t = UnOp.from a.
  Proof.
    intros Ht. unfold BinOp.mul, UnOp.from in *.
    rewrite Zmult_mod, Ht, Z.mul_1_r, Zmod_mod. reflexivity.
  Qed.

  Lemma neg1_sq : UnOp.from (-1) *F UnOp.from (-1) = 1.
  Proof.
    pose proof prime_gt1 as Hp1.
    unfold BinOp.mul, UnOp.from.
    rewrite Zmult_mod_idemp_l, Zmult_mod_idemp_r.
    replace (-1 * -1) with 1 by ring.
    now rewrite Z.mod_1_l by lia.
  Qed.

  (* The only square roots of 1 are 1 and -1 (integral domain). *)
  Lemma sqrt_one (x : Z) :
    BinOp.mul x x = UnOp.from 1 ->
    UnOp.from x = UnOp.from 1 \/ UnOp.from x = UnOp.from (-1).
  Proof.
    intros Hx.
    pose proof prime_gt1 as Hp1.
    assert (Hz : BinOp.mul (BinOp.sub x 1) (BinOp.add x 1) = 0).
    { unfold BinOp.mul, BinOp.sub, BinOp.add in *.
      rewrite Zmult_mod_idemp_l, Zmult_mod_idemp_r.
      replace ((x - 1) * (x + 1)) with (x * x - 1) by ring.
      rewrite Zminus_mod. unfold UnOp.from in Hx. rewrite Hx.
      rewrite Z.sub_diag. apply Zmod_0_l. }
    rewrite mul_zero_implies_zero in Hz.
    destruct Hz as [Hz | Hz].
    - left. rewrite from_sub_reduced in Hz. now apply sub_zero_equiv in Hz.
    - right.
      replace (BinOp.add x 1) with (BinOp.sub x (-1)) in Hz
        by (unfold BinOp.add, BinOp.sub; f_equal; ring).
      rewrite from_sub_reduced in Hz. now apply sub_zero_equiv in Hz.
  Qed.

  (* p is odd (p > 2 prime): 2 * ((p-1)/2) = p - 1. *)
  Lemma odd_pm1 : 2 < p -> 2 * ((p - 1) / 2) = p - 1.
  Proof.
    intros Hp3.
    pose proof (@is_prime p _) as Hp. unfold IsPrime in Hp.
    assert (H2 : ~ (2 | p)).
    { intro Hd. pose proof (Znumtheory.prime_divisors p Hp 2 Hd). lia. }
    assert (Hmod : p mod 2 <> 0).
    { intro Hc. apply H2. apply Z.mod_divide; [lia | exact Hc]. }
    lia.
  Qed.

  (* Field power with a Z exponent: a^n reduced mod p. *)
  Definition Fpow (a n : Z) : Z := UnOp.from (a ^ n).

  Lemma Fpow_0 (a : Z) : Fpow a 0 = UnOp.from 1.
  Proof. unfold Fpow. now rewrite Z.pow_0_r. Qed.

  Lemma Fpow_1 (a : Z) : Fpow a 1 = UnOp.from a.
  Proof. unfold Fpow. now rewrite Z.pow_1_r. Qed.

  Lemma Fpow_add (a m n : Z) : 0 <= m -> 0 <= n ->
    Fpow a (m + n) = Fpow a m *F Fpow a n.
  Proof.
    intros Hm Hn. unfold Fpow, BinOp.mul, UnOp.from.
    rewrite Z.pow_add_r by lia.
    rewrite Zmult_mod. reflexivity.
  Qed.

  Lemma Fpow_mul (a m n : Z) : 0 <= m -> 0 <= n ->
    Fpow (Fpow a m) n = Fpow a (m * n).
  Proof.
    intros Hm Hn. pose proof prime_gt1 as Hp1.
    unfold Fpow, UnOp.from.
    rewrite Z.pow_mul_r by lia.
    rewrite <- (Zpower_mod (a ^ m) n p) by lia.
    reflexivity.
  Qed.

  Lemma Fpow_sqr (a n : Z) : 0 <= n ->
    Fpow a n *F Fpow a n = Fpow a (2 * n).
  Proof.
    intros Hn.
    replace (2 * n) with (n + n) by ring.
    rewrite Fpow_add by lia. reflexivity.
  Qed.

  Lemma Fpow_reduced (a n : Z) : UnOp.from (Fpow a n) = Fpow a n.
  Proof. unfold Fpow. apply from_idem. Qed.

  (* a^n is nonzero in the field whenever a is. *)
  Lemma Fpow_nonzero (a n : Z) : 0 <= n -> UnOp.from a <> 0 -> Fpow a n <> 0.
  Proof.
    intros Hn Ha.
    pose proof (@is_prime p _) as Hp. unfold IsPrime in Hp.
    pose proof prime_gt1 as Hp1.
    unfold Fpow, UnOp.from in *.
    intro Hc.
    apply Z.mod_divide in Hc; [|lia].
    assert (Hrp : Znumtheory.rel_prime p a).
    { apply Znumtheory.prime_rel_prime; [exact Hp|].
      intro Hd. apply Ha. apply Z.mod_divide; [lia|exact Hd]. }
    pose proof (rel_prime_Zpower_r n p a Hn Hrp) as Hrpn.
    destruct (Znumtheory.rel_prime_bezout p (a ^ n) Hrpn) as [u v Hb].
    assert (Hpd : (p | 1)).
    { rewrite <- Hb. apply Z.divide_add_r.
      - rewrite Z.mul_comm. apply Z.divide_factor_l.
      - apply Z.divide_mul_r. exact Hc. }
    apply Z.divide_1_r in Hpd. lia.
  Qed.

  (* Fpow of a field product distributes. *)
  Lemma Fpow_mul_base (x y k : Z) : 0 <= k ->
    Fpow (x *F y) k = Fpow x k *F Fpow y k.
  Proof.
    intros Hk. pose proof prime_gt1 as Hp1.
    unfold Fpow, BinOp.mul, UnOp.from.
    rewrite <- (Zpower_mod (x * y) k p) by lia.
    rewrite Z.pow_mul_l.
    rewrite Zmult_mod. reflexivity.
  Qed.

  (* a^(q+1) = a * a^q (field), for q >= 0. *)
  Lemma Fpow_succ_l (a q : Z) : 0 <= q -> a *F Fpow a q = Fpow a (q + 1).
  Proof.
    intros Hq.
    rewrite mul_left_reduce, <- Fpow_1, <- Fpow_add by lia.
    f_equal. lia.
  Qed.

End FieldPow.
