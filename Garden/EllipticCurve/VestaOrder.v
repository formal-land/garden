(** * The Vesta group order annihilates every point

    Instantiation of the tight generic order theorem
    [GroupOrderTight.mul_q_annihilates_tight] at the Vesta curve
    [y^2 = x^3 + 5] over [F_{pallas_q}]: every reduced on-curve Vesta point
    is annihilated by the group order [pallas_p].  Vesta sits on the
    positive-trace side of the pasta cycle ([pallas_p < pallas_q]), so the
    two-coset bound of [GroupOrder.mul_q_annihilates] fails and the
    three-coset argument is required, together with the absence of
    two-torsion: [x^3 + 5] has no root in [F_{pallas_q}] because [-5] is
    not a cube — certified by the Euler-criterion power
    [(-5)^((q-1)/3) <> 1] and Fermat's little theorem.

    The generator is the placeholder point [affine (-1) 2] (the same
    coordinates as the Pallas placeholder: both curves have [b = 5]), with
    a [vm_cast_no_check]'d [pallas_p]-fold double-and-add ladder as its
    order certificate. *)

Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.ZArith.Zpow_facts.
Require Import Stdlib.micromega.Lia.
Require Import Garden.Field.Field.
Require Import Garden.Field.Lemmas.
Require Import Garden.Field.Fermat.
Require Import Garden.Field.Sqrt.
Require Import Garden.EllipticCurve.Weierstrass.
Require Import Garden.EllipticCurve.Vesta.
Require Import Garden.EllipticCurve.GroupOrderTight.

Global Open Scope Z_scope.

#[local] Existing Instance Primes.PallasQIsPrime.

Module VestaOrder.

  Local Notation qq := Primes.pallas_q.

  (** Characteristic bound for the fiat-crypto transported group law. *)
  Lemma eleven_lt_q : 11 < qq.
  Proof. vm_compute. reflexivity. Qed.

  (** The Vesta group order is prime. *)
  Lemma vesta_r_prime : IsPrime Vesta.vesta_r.
  Proof. exact Primes.pallas_p_prime. Qed.

  (** ** The placeholder generator [(-1, 2)] *)

  Lemma gen_on_curve : Vesta.on_curve (Vesta.affine (-1) 2).
  Proof. vm_compute. reflexivity. Qed.

  Lemma gen_reduced : Vesta.reduced (Vesta.affine (-1) 2).
  Proof. vm_compute. split; reflexivity. Qed.

  Lemma gen_ne_identity : Vesta.affine (-1) 2 <> Vesta.identity.
  Proof. discriminate. Qed.

  (** Prime-order certificate: a finite [vm_cast_no_check]'d
      [pallas_p]-fold double-and-add ladder. *)
  Lemma placeholder_order :
    Vesta.mul Vesta.vesta_r (Vesta.affine (-1) 2) = Vesta.identity.
  Proof. vm_cast_no_check (@eq_refl Vesta.point Vesta.identity). Qed.

  (** ** No two-torsion: [-5] is not a cube in [F_{pallas_q}]

      Euler-criterion certificate: [(q-5)^((q-1)/3) <> 1 mod q]. *)
  Lemma q_mod_3 : qq mod 3 = 1.
  Proof. vm_compute. reflexivity. Qed.

  Lemma five_lt_q : (5 <? qq) = true.
  Proof. vm_compute. reflexivity. Qed.

  Lemma cube_char_cert :
    (modpow (p := Primes.pallas_q) (qq - 5) ((qq - 1) / 3) =? 1) = false.
  Proof. vm_cast_no_check (@eq_refl bool false). Qed.

  (** [x^3 + 5] has no root modulo [q]: a root would give
      [x^3 = -5 mod q], hence
      [1 = x^(q-1) = (x^3)^((q-1)/3) = (-5)^((q-1)/3) mod q] by Fermat,
      contradicting the certificate. *)
  Lemma no_cube_root (x : Z) :
    UnOp.from (p := Primes.pallas_q)
      (x *F x *F x +F Vesta.a *F x +F Vesta.b) <> 0.
  Proof.
    intros Hx0.
    assert (Hq1 : 1 < qq).
    { pose proof (prime_range (p := qq)). lia. }
    assert (Hq5 : 5 < qq).
    { apply Z.ltb_lt. exact five_lt_q. }
    (* Normalize the field expression to a bare mod equation. *)
    unfold Vesta.a, Vesta.b, BinOp.add, BinOp.mul, UnOp.from in Hx0.
    rewrite (Z.mul_0_l x), Zmod_0_l, Z.add_0_r in Hx0.
    rewrite Zmod_mod in Hx0.
    rewrite Zplus_mod_idemp_l in Hx0.
    rewrite Zplus_mod in Hx0.
    rewrite Zmult_mod_idemp_l in Hx0.
    rewrite <- Zplus_mod in Hx0.
    rewrite Zplus_mod_idemp_l in Hx0.
    (* Hx0 : (x * x * x + 5) mod qq = 0 *)
    assert (Hshift : (x * x * x) mod qq = qq - 5).
    { pose proof (Z.div_mod (x * x * x + 5) qq ltac:(lia)) as Hdm.
      rewrite Hx0, Z.add_0_r in Hdm.
      replace (x * x * x)
        with ((qq - 5) + ((x * x * x + 5) / qq - 1) * qq) by lia.
      rewrite Z_mod_plus_full.
      apply Z.mod_small. lia. }
    assert (Hyb : 0 <= x mod qq < qq) by (apply Z.mod_pos_bound; lia).
    assert (Hyne : x mod qq <> 0).
    { intros H0.
      assert (H3 : (x * x * x) mod qq = 0).
      { rewrite Zmult_mod, H0, Z.mul_0_r, Zmod_0_l. reflexivity. }
      lia. }
    (* Fermat. *)
    assert (Hf : (x ^ (qq - 1)) mod qq = 1).
    { rewrite Zpower_mod by lia.
      apply flt_pow_pred; [exact Primes.pallas_q_prime | lia]. }
    assert (Hepos : 0 <= (qq - 1) / 3) by (apply Z.div_pos; lia).
    assert (He : qq - 1 = 3 * ((qq - 1) / 3)).
    { pose proof (Z.div_mod qq 3 ltac:(lia)) as Hdm3.
      pose proof (Z.div_mod (qq - 1) 3 ltac:(lia)) as Hdm31.
      pose proof (Z.mod_pos_bound (qq - 1) 3 ltac:(lia)) as Hb31.
      pose proof q_mod_3 as Hq3.
      clear - Hdm3 Hdm31 Hb31 Hq3. lia. }
    rewrite He in Hf.
    rewrite (Z.pow_mul_r x 3 ((qq - 1) / 3) ltac:(lia) Hepos) in Hf.
    rewrite Zpower_mod in Hf by lia.
    replace (x ^ 3) with (x * x * x) in Hf by ring.
    rewrite Hshift in Hf.
    (* Contradiction with the Euler-criterion certificate. *)
    pose proof cube_char_cert as Hcert.
    apply Z.eqb_neq in Hcert.
    apply Hcert.
    rewrite (modpow_correct (p := Primes.pallas_q) (qq - 5) ((qq - 1) / 3)
               Hepos).
    unfold Fpow, UnOp.from.
    exact Hf.
  Qed.

  (** Tight-counting bound: [2*pallas_q + 1 < 3*pallas_p]. *)
  Lemma curve_size_bound3 :
    2 * qq + 1 < 3 * Vesta.vesta_r.
  Proof. vm_compute. reflexivity. Qed.

  (** Keep conversion from re-running the [pallas_p]-fold ladder when the
      [Vesta.mul] and [Weierstrass.mul] spellings are aligned. *)
  Strategy opaque [Weierstrass.mul].

  (** ** Every reduced on-curve Vesta point is annihilated by [pallas_p]. *)
  Theorem vesta_mul_r_on_curve (P : Vesta.point) :
    Vesta.reduced P ->
    Vesta.on_curve P ->
    Vesta.mul Vesta.vesta_r P = Vesta.identity.
  Proof.
    intros HrP HoP.
    exact (GroupOrderTight.mul_q_annihilates_tight Vesta.a Vesta.b
             eleven_lt_q Vesta.nonsingular no_cube_root
             (Vesta.affine (-1) 2) Vesta.vesta_r
             gen_reduced gen_on_curve gen_ne_identity
             vesta_r_prime placeholder_order
             curve_size_bound3 P HrP HoP).
  Qed.

  (** Scalar reduction modulo the Vesta group order. *)
  Lemma vesta_mul_mod (P : Vesta.point) (n : Z) :
    Vesta.reduced P ->
    Vesta.on_curve P ->
    Vesta.mul (n mod Vesta.vesta_r) P = Vesta.mul n P.
  Proof.
    intros HrP HoP.
    apply (GroupOrderTight.mul_mod_order Vesta.a Vesta.b eleven_lt_q
             Vesta.nonsingular P Vesta.vesta_r n).
    - pose proof (Znumtheory.prime_ge_2 _ vesta_r_prime). lia.
    - exact HrP.
    - exact HoP.
    - exact (vesta_mul_r_on_curve P HrP HoP).
  Qed.

  Strategy transparent [Weierstrass.mul].

End VestaOrder.
