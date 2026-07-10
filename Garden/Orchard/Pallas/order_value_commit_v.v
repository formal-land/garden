(** * Prime-order certificate for the Pallas ValueCommitV fixed base

    The prime-order certificate for the
    ValueCommitV generator: the finite computation [[pallas_q] G = identity].
    This is Pallas-curve arithmetic ([Garden.EllipticCurve.Pallas]) applied to
    the ValueCommitV generator point from
    [Garden.Orchard.Pallas.Generators], isolated in its own file so the heavy
    [vm_compute] recompiles independently.

    The statement matches [PallasGeneratorsOrder.value_commit_v_order] verbatim.
    The proof is the [q]G = O finite computation: [Pallas.mul] is binary
    double-and-add over the textbook complete addition, every field operation
    (including the extended-Euclid [mod_inverse]) is closed-form computable, and
    [pallas_q], [pallas_p], [value_commit_v_G] are concrete,
    so [vm_compute] reduces the scalar multiple to
    [Weierstrass.Infinity = Pallas.identity]. *)

Require Import Garden.Field.Field.
Require Import Garden.EllipticCurve.Weierstrass.
Require Import Garden.EllipticCurve.Pallas.
Require Import Garden.Orchard.Pallas.Generators.

Global Open Scope Z_scope.

#[local] Existing Instance Primes.PallasPIsPrime.

Module PallasOrder_value_commit_v.
  (** ** [[pallas_q] ValueCommitV_G = identity]

      Proved by the finite [vm_compute] of the ~255-bit double-and-add ladder
      (about one extended-Euclid modular inverse per point operation over
      [pallas_p]). *)
  Lemma value_commit_v_order :
    Pallas.mul Pallas.pallas_q PallasGenerators.value_commit_v_G =
      Pallas.identity.
  Proof.
    vm_compute.
    reflexivity.
  Qed.
End PallasOrder_value_commit_v.
