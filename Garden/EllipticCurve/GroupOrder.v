(** * Annihilation by a prime generator order on small short-Weierstrass curves

    The generic order theorem: on a curve carrying a generator [G] of prime
    order [q] with [2*p + 1 < 2*q], every reduced on-curve point [P]
    satisfies [mul q P = Infinity].  Point equality on [Weierstrass.point]
    is decidable (a point is [Infinity] or a pair of integers), so the proof
    is a constructive case split with no classical axioms: either
    [mul q P = Infinity] outright, or [P] lies outside the cyclic subgroup
    [<G>] — a multiple [P = [n]G] would give
    [mul q P = mul (q*n) G = Infinity] by the composition law
    ([Weierstrass.mul_mul]) and the order certificate
    ([Weierstrass.mul_eq_Infinity_iff]) — and then the two-coset family of
    [GroupOrderCosets] provides [2*q] pairwise-distinct reduced on-curve
    points, contradicting the [2*p + 1] counting bound of
    [GroupOrderCounting.family_bound].

    Everything is symbolic in [p] and [q]: nothing of scalar size is ever
    computed. *)

Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.micromega.Lia.
Require Import Garden.Field.Field.
Require Import Garden.EllipticCurve.Weierstrass.
Require Import Garden.EllipticCurve.GroupOrderCounting.
Require Import Garden.EllipticCurve.GroupOrderCosets.

Global Open Scope Z_scope.

Module GroupOrder.

(** Point equality is decidable: coordinates are integers. *)
Definition point_eq_dec (P Q : Weierstrass.point) : {P = Q} + {P <> Q}.
Proof. decide equality; apply Z.eq_dec. Defined.

Section Order.
  (** The abstract base field [Z/pZ], as in [Weierstrass.Curve]. *)
  Context {p : Z} `{Prime p}.

  (** The short-Weierstrass coefficients [y^2 = x^3 + a*x + b]. *)
  Variables (a b : Z).

  (** The characteristic bound and nonsingularity required by the
      fiat-crypto transported group law. *)
  Hypothesis H11 : 11 < p.
  Hypothesis Hns : Weierstrass.nonsingular (p := p) a b.

  Local Notation point := Weierstrass.point.
  Local Notation Infinity := Weierstrass.Infinity.
  Local Notation on_curve := (Weierstrass.on_curve (p := p) a b).
  Local Notation reduced := (Weierstrass.reduced (p := p)).
  Local Notation mul := (Weierstrass.mul (p := p) a).

  (** The prime-order generator: reduced, on the curve, not the identity,
      with order certificate [mul q G = Infinity] for a prime [q]. *)
  Variables (G : point) (q : Z).
  Hypothesis HrG : reduced G.
  Hypothesis HoG : on_curve G.
  Hypothesis HGne : G <> Infinity.
  Hypothesis Hq : IsPrime q.
  Hypothesis Hord : mul q G = Infinity.

  (** The smallness bound: the [2*p + 1] cap on reduced on-curve points
      ([GroupOrderCounting.family_bound]) is below the [2*q] members of a
      two-coset family. *)
  Hypothesis Hcard : 2 * p + 1 < 2 * q.

  Theorem mul_q_annihilates (P : point) :
    reduced P -> on_curve P -> mul q P = Infinity.
  Proof.
    intros HrP HoP.
    assert (H3 : 3 < p) by lia.
    destruct (point_eq_dec (mul q P) Infinity) as [He | Hne]; [exact He |].
    exfalso.
    (** [P] is outside [<G>]: a multiple would be annihilated by [q]. *)
    assert (Hnm : forall n : Z, P <> mul n G).
    { intros n HP. apply Hne. rewrite HP.
      rewrite <- (Weierstrass.mul_mul a b q n G H11 Hns HrG HoG).
      apply (proj2 (Weierstrass.mul_eq_Infinity_iff a b G q H11 Hns HrG HoG
                      HGne Hq Hord (q * n))).
      apply Z.divide_factor_l. }
    (** The two-coset family: [2*q] pairwise-distinct reduced on-curve
        points, against the [2*p + 1] cap. *)
    pose proof (GroupOrderCounting.family_bound a b (2 * q)
                  (GroupOrderCosets.family a G q P)
                  H3
                  (fun k Hk =>
                     proj1 (GroupOrderCosets.family_reduced_on_curve
                              a b H11 G q HrG HoG P HrP HoP k Hk))
                  (fun k Hk =>
                     proj2 (GroupOrderCosets.family_reduced_on_curve
                              a b H11 G q HrG HoG P HrP HoP k Hk))
                  (GroupOrderCosets.family_inj a b H11 Hns G q HrG HoG HGne
                     Hq Hord P HrP HoP Hnm)) as Hbound.
    lia.
  Qed.

End Order.

End GroupOrder.
