(** * The Pallas group order annihilates every point

    Instantiation of the generic order theorem [GroupOrder.mul_q_annihilates]
    at the Pallas curve: every reduced on-curve Pallas point is annihilated
    by [pallas_q].  The generator is the placeholder point [affine (-1) 2],
    whose reducedness ([Pallas.gen_reduced]) and prime-order certificate
    ([Pallas.placeholder_order]) live in [EllipticCurve/Pallas.v]; the
    remaining side facts are literal computations on the Pallas constants —
    the curve membership [(-1)^3 + 5 = 4 = 2^2] and the smallness bound
    [2*pallas_p + 1 < 2*pallas_q] (Pallas sits on the negative-trace side of
    the Pallas/Vesta pair, so [pallas_q > pallas_p] and no Hasse bound is
    needed). *)

Require Import Garden.Field.Field.
Require Import Garden.EllipticCurve.Weierstrass.
Require Import Garden.EllipticCurve.Pallas.
Require Import Garden.EllipticCurve.GroupOrder.

Global Open Scope Z_scope.

#[local] Existing Instance Primes.PallasPIsPrime.

Module PallasOrder.

  (** The placeholder generator lies on [y^2 = x^3 + 5]. *)
  Lemma gen_on_curve : Pallas.on_curve (Pallas.affine (-1) 2).
  Proof. vm_compute. reflexivity. Qed.

  (** The placeholder generator is a proper affine point. *)
  Lemma gen_ne_identity : Pallas.affine (-1) 2 <> Pallas.identity.
  Proof. discriminate. Qed.

  (** The smallness bound of the generic order theorem, on the literal
      Pallas constants. *)
  Lemma curve_size_bound : 2 * Primes.pallas_p + 1 < 2 * Pallas.pallas_q.
  Proof. vm_compute. reflexivity. Qed.

  (** Aligning the [Pallas.mul] form of [placeholder_order] and of the goal
      with the [Weierstrass.mul] shape the generic theorem expects must not
      recompute the [pallas_q]-fold ladder: when the two heads ([Pallas.mul]
      / [Weierstrass.mul]) differ, the conversion oracle would otherwise
      evaluate the (concrete, ~255-bit-scalar) ladder. Making
      [Weierstrass.mul] opaque to conversion forces the cheap [delta]
      unfolding of [Pallas.mul] instead. Transparency is restored below. *)
  Strategy opaque [Weierstrass.mul].

  (** Every reduced on-curve Pallas point is annihilated by [pallas_q]. *)
  Theorem pallas_mul_q_on_curve (P : Pallas.point) :
    Pallas.reduced P ->
    Pallas.on_curve P ->
    Pallas.mul Pallas.pallas_q P = Pallas.identity.
  Proof.
    intros HrP HoP.
    exact (GroupOrder.mul_q_annihilates Pallas.a Pallas.b
             Pallas.eleven_lt_p Pallas.nonsingular
             (Pallas.affine (-1) 2) Pallas.pallas_q
             Pallas.gen_reduced gen_on_curve gen_ne_identity
             Pallas.pallas_q_is_prime Pallas.placeholder_order
             curve_size_bound P HrP HoP).
  Qed.

  Strategy transparent [Weierstrass.mul].

End PallasOrder.
