(** * Pallas instantiation of the generic short-Weierstrass curve

    Instantiates [Weierstrass] at [a = 0], [b = 5], [p = pallas_p] (the
    Pallas base field), provides Pallas-specific [add]/[neg]/[mul] wrappers,
    and establishes curve nonsingularity.
    This file is self-contained: it depends only on [Garden.Field] and
    [EllipticCurve/Weierstrass.v], not on [Halo2/] or [Orchard/]. The
    representation map to the Halo2 chip-level [EccSpec.Point.t] model and
    the [mul]-vs-[EccSpec.scalar_mul] bridge live in
    [Garden.Halo2.PallasModel] instead, since that is the only place this
    development touches the Halo2 ECC chip spec. The six Orchard fixed-base
    generator points and their per-generator facts are instantiated
    separately in [Garden.Orchard.Pallas.Generators].

    Proof structure. Nonsingularity is a finite Pallas-field computation
    (closed by [vm_compute]). The shared placeholder generator
    [affine (-1) 2] — reused by [Generators] for the five fixed bases that
    have not yet been given their real coordinates — has its reducedness
    ([gen_reduced]) and prime-order certificate ([placeholder_order], a
    [pallas_q]-fold double-and-add ladder closed by [vm_cast_no_check])
    established here, since it is curve data rather than Orchard-specific
    data: because [#E_Pallas(F_p) = pallas_q] is prime, the whole group is
    cyclic of prime order [pallas_q] and every non-identity point is a
    generator, so [(-1, 2)] (which lies on [y^2 = x^3 + 5] since
    [(-1)^3 + 5 = 4 = 2^2]) needs no per-base justification. *)

Require Import Garden.Field.Field.
Require Import Garden.EllipticCurve.Weierstrass.

Global Open Scope Z_scope.

#[local] Existing Instance Primes.PallasPIsPrime.

Module Pallas.
  (** ** The Pallas curve instance [y^2 = x^3 + 5] over [F_{pallas_p}] *)

  (** Short-Weierstrass coefficients. *)
  Definition a : Z := 0.
  Definition b : Z := 5.

  (** Convenient aliases for the base prime and the (prime) group order. *)
  Definition pallas_q : Z := Primes.pallas_q.

  (** Pallas points are the generic Weierstrass points; the group identity is
      the proper point at infinity. *)
  Definition point : Set := Weierstrass.point.
  Definition identity : point := Weierstrass.Infinity.

  (** Pallas-specialised curve operations (the generic ones at [a], [b],
      [p := pallas_p]). *)
  Definition on_curve (P : point) : Prop :=
    Weierstrass.on_curve (p := Primes.pallas_p) a b P.
  Definition reduced (P : point) : Prop :=
    Weierstrass.reduced (p := Primes.pallas_p) P.
  Definition neg (P : point) : point :=
    Weierstrass.neg (p := Primes.pallas_p) P.
  Definition add (P Q : point) : point :=
    Weierstrass.add (p := Primes.pallas_p) a P Q.

  (** ** Binary scalar multiplication for Pallas (definition) *)
  Definition mul (k : Z) (P : point) : point :=
    Weierstrass.mul (p := Primes.pallas_p) a k P.

  (** A reduced affine point: coordinates are taken [mod pallas_p], so the
      result is always [reduced]. *)
  Definition affine (x y : Z) : point :=
    Weierstrass.Affine
      (UnOp.from (p := Primes.pallas_p) x)
      (UnOp.from (p := Primes.pallas_p) y).

  (** ** Nonsingularity [4 a^3 + 27 b^2 = 27 * 25 <> 0 mod p] (statement) *)
  Lemma nonsingular : Weierstrass.nonsingular (p := Primes.pallas_p) a b.
  Proof.
    unfold Weierstrass.nonsingular. intro Hc. vm_compute in Hc. discriminate.
  Qed.

  (** ** Side conditions shared by the per-generator order lemmas

      [three_lt_p] / [pallas_q_is_prime] are the characteristic and prime-order
      facts the [Weierstrass] order theory consumes; [gen_reduced] witnesses
      that the (shared) placeholder generator [affine (-1) 2] has reduced
      coordinates. *)
  Lemma three_lt_p : 3 < Primes.pallas_p.
  Proof. vm_compute. reflexivity. Qed.

  (** Sharper characteristic bound, required by the [Weierstrass] order theory
      after its fiat-crypto transport ([W.commutative_group] needs
      [char_ge 12]). *)
  Lemma eleven_lt_p : 11 < Primes.pallas_p.
  Proof. vm_compute. reflexivity. Qed.

  Lemma pallas_q_is_prime : IsPrime pallas_q.
  Proof. exact Primes.pallas_q_prime. Qed.

  Lemma gen_reduced : reduced (affine (-1) 2).
  Proof. vm_compute. split; reflexivity. Qed.

  (** Prime-order certificate for the shared placeholder generator
      [affine (-1) 2]: a finite [vm_cast_no_check]'d [pallas_q]-fold
      double-and-add ladder, reused by conversion in [Generators] for the
      fixed bases that still carry the placeholder. *)
  Lemma placeholder_order : mul pallas_q (affine (-1) 2) = identity.
  Proof. vm_cast_no_check (@eq_refl point identity). Qed.
End Pallas.
