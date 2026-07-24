(** * Vesta instantiation of the generic short-Weierstrass curve

    Instantiates [Weierstrass] at [a = 0], [b = 5], [p = pallas_q] (the Vesta
    base field, which is the Pallas scalar field of the pasta cycle), provides
    Vesta-specific [add]/[neg]/[mul] wrappers, and establishes curve
    nonsingularity.  Vesta is the commitment curve of the Halo2 IPA over
    Pallas circuits: the pinned Orchard verifying-key commitments
    ([Orchard/vk_pinned_data.v]) are Vesta points, with coordinates mod
    [pallas_q] ([VkPinnedData.base_modulus]) and scalars mod [pallas_p]
    ([VkPinnedData.scalar_modulus] — the Vesta group order).

    This file is self-contained: it depends only on [Garden.Field] and
    [EllipticCurve/Weierstrass.v], mirroring [EllipticCurve/Pallas.v]. *)

Require Import Garden.Field.Field.
Require Import Garden.EllipticCurve.Weierstrass.

Global Open Scope Z_scope.

#[local] Existing Instance Primes.PallasQIsPrime.

Module Vesta.
  (** ** The Vesta curve instance [y^2 = x^3 + 5] over [F_{pallas_q}] *)

  (** Short-Weierstrass coefficients. *)
  Definition a : Z := 0.
  Definition b : Z := 5.

  (** Convenient aliases for the base prime and the (prime) group order. *)
  Definition vesta_q : Z := Primes.pallas_q.
  Definition vesta_r : Z := Primes.pallas_p.

  (** Vesta points are the generic Weierstrass points; the group identity is
      the proper point at infinity. *)
  Definition point : Set := Weierstrass.point.
  Definition identity : point := Weierstrass.Infinity.

  (** Vesta-specialised curve operations (the generic ones at [a], [b],
      [p := pallas_q]). *)
  Definition on_curve (P : point) : Prop :=
    Weierstrass.on_curve (p := Primes.pallas_q) a b P.
  Definition reduced (P : point) : Prop :=
    Weierstrass.reduced (p := Primes.pallas_q) P.
  Definition neg (P : point) : point :=
    Weierstrass.neg (p := Primes.pallas_q) P.
  Definition add (P Q : point) : point :=
    Weierstrass.add (p := Primes.pallas_q) a P Q.

  (** ** Binary scalar multiplication for Vesta (definition) *)
  Definition mul (k : Z) (P : point) : point :=
    Weierstrass.mul (p := Primes.pallas_q) a k P.

  (** A reduced affine point: coordinates are taken [mod pallas_q], so the
      result is always [reduced]. *)
  Definition affine (x y : Z) : point :=
    Weierstrass.Affine
      (UnOp.from (p := Primes.pallas_q) x)
      (UnOp.from (p := Primes.pallas_q) y).

  (** ** Nonsingularity [4 a^3 + 27 b^2 = 27 * 25 <> 0 mod q] *)
  Lemma nonsingular : Weierstrass.nonsingular (p := Primes.pallas_q) a b.
  Proof.
    unfold Weierstrass.nonsingular. intro Hc. vm_compute in Hc. discriminate.
  Qed.
End Vesta.
