(** * Prime-order certificate for the Pallas SpendAuthG fixed base

    Discharges the certificate consumed by [PallasGeneratorsOrder.spend_auth_g_order]:
    the scalar multiple [[pallas_q] G] of the
    SpendAuthG generator equals the group identity (the point at infinity).

    The proof is a finite computation: [Pallas.mul] is the binary
    double-and-add ladder over the textbook complete addition, every field
    operation ([UnOp.from], [BinOp.*], the extended-Euclid [mod_inverse])
    is a closed [Z]-computation modulo [pallas_p], and the [Prime pallas_p]
    instance never enters the computational content. Reducing the ladder with
    the bytecode VM lands on [Weierstrass.Infinity], so the goal is closed by a
    single VM-checked conversion ([vm_cast_no_check]).

    Layering: this file's curve arithmetic depends only on
    [Garden.EllipticCurve.Pallas] (and transitively on [Garden.Field],
    [Garden.EllipticCurve.Weierstrass]); the SpendAuthG generator point itself
    comes from [Garden.Orchard.Pallas.Generators], which is why this file lives
    under [Garden/Orchard/] rather than [Garden/EllipticCurve/]. *)

Require Import Garden.EllipticCurve.Pallas.
Require Import Garden.Orchard.Pallas.Generators.

Module PallasOrder_spend_auth_g.
  (** [[pallas_q] G = O] for the SpendAuthG generator [G], matching the exact
      form of [PallasGeneratorsOrder.spend_auth_g_order]. *)
  Lemma spend_auth_g_order :
    Pallas.mul Pallas.pallas_q PallasGenerators.spend_auth_g_G =
      Pallas.identity.
  Proof.
    vm_cast_no_check (@eq_refl Pallas.point Pallas.identity).
  Qed.
End PallasOrder_spend_auth_g.
