(** * Prime-order certificate for the Pallas SpendAuthG fixed base

    Discharges the certificate consumed by
    [PallasGeneratorsOrder.spend_auth_g_order]: the scalar multiple
    [[pallas_q] G] of the SpendAuthG generator equals the group identity
    (the point at infinity).

    The fact is an instance of [PallasOrder.pallas_mul_q_on_curve]
    ([Garden/EllipticCurve/PallasOrder.v]): every reduced on-curve Pallas
    point is annihilated by [pallas_q], so the certificate follows from the
    generator's [reduced] / [on_curve] facts ([Generators.v]) with no
    per-generator ladder computation.

    Layering: the order theorem depends only on [Garden.EllipticCurve]; the
    SpendAuthG generator point itself comes from
    [Garden.Orchard.Pallas.Generators], which is why this file lives under
    [Garden/Orchard/] rather than [Garden/EllipticCurve/]. *)

Require Import Garden.EllipticCurve.Weierstrass.
Require Import Garden.EllipticCurve.Pallas.
Require Import Garden.EllipticCurve.PallasOrder.
Require Import Garden.Orchard.Pallas.Generators.

Module PallasOrder_spend_auth_g.
  (** [Weierstrass.mul] stays opaque to conversion here so that checking the
      instantiated theorem never attempts to evaluate the concrete
      [pallas_q]-scalar ladder. *)
  Strategy opaque [Weierstrass.mul].

  (** [[pallas_q] G = O] for the SpendAuthG generator [G], matching the exact
      form of [PallasGeneratorsOrder.spend_auth_g_order]. *)
  Lemma spend_auth_g_order :
    Pallas.mul Pallas.pallas_q PallasGenerators.spend_auth_g_G =
      Pallas.identity.
  Proof.
    exact (PallasOrder.pallas_mul_q_on_curve
             PallasGenerators.spend_auth_g_G
             PallasGenerators.spend_auth_g_reduced
             PallasGenerators.spend_auth_g_on_curve).
  Qed.

  Strategy transparent [Weierstrass.mul].
End PallasOrder_spend_auth_g.
