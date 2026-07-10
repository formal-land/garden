(** * NullifierK prime-order certificate ([pallas_q] K = O)

    The prime-order certificate for the NullifierK
    fixed base: the finite computational certificate that the NullifierK
    generator has order dividing [pallas_q],

      [Pallas.mul Pallas.pallas_q PallasGenerators.nullifier_k_G =
         Pallas.identity].

    This is exactly the certificate consumed by
    [PallasGeneratorsOrder.nullifier_k_order]; here it is discharged by a single
    [vm_compute] of the [pallas_q]-fold double-and-add, which reduces the
    left-hand side to [Weierstrass.Infinity = Pallas.identity].

    Layering: this file's curve arithmetic is over the Pallas base field
    ([Garden.EllipticCurve.Pallas]); the NullifierK generator point comes
    from [Garden.Orchard.Pallas.Generators], which is why this file lives
    under [Garden/Orchard/] rather than [Garden/EllipticCurve/]. The heavy
    [vm_compute] is isolated in its own file so it recompiles
    independently under [make -j].

    Cost: the certificate is a [pallas_q]-scalar double-and-add (~254 doublings
    + ~60 additions), each affine point operation performing one extended-Euclid
    modular inverse over the 254-bit prime [pallas_p]; total ≈ 5 min of kernel
    VM time, ≈ 0.42 GB resident. The [vm_cast_no_check] idiom defers a *single*
    VM conversion to [Qed] (rather than running the VM once for the [vm_compute]
    tactic and again for the [Qed] cast).

    The generator carries the real Zcash NullifierK coordinates. Because
    [#E_Pallas(F_p) = pallas_q] is prime, every non-identity on-curve point has
    order [pallas_q], so [[pallas_q] G = O] is a finite computation whose
    inverse-dominated cost is independent of the specific coordinates. *)

Require Import Garden.Field.Field.
Require Import Garden.EllipticCurve.Weierstrass.
Require Import Garden.EllipticCurve.Pallas.
Require Import Garden.Orchard.Pallas.Generators.

Global Open Scope Z_scope.

Module PallasOrder_nullifier_k.
  (** Proves [PallasGeneratorsOrder.nullifier_k_order]'s
      statement by the finite [pallas_q]-fold scalar multiplication, reducing
      to the identity. *)
  Lemma nullifier_k_order :
    Pallas.mul Pallas.pallas_q PallasGenerators.nullifier_k_G = Pallas.identity.
  Proof.
    vm_cast_no_check (eq_refl Pallas.identity).
  Qed.
End PallasOrder_nullifier_k.
