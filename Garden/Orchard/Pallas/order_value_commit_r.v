(** * Prime-order certificate for the Pallas ValueCommitR fixed base

    The prime-order certificate for the
    [ValueCommitR] generator: the finite computation

      [[pallas_q] * value_commit_r_G = identity]

    proved by reducing the binary double-and-add ladder
    [Weierstrass.mul (p := pallas_p) 0 pallas_q value_commit_r_G] to the proper
    point at infinity [Weierstrass.Infinity], at the real Zcash ValueCommitR
    affine coordinates. Because [#E_Pallas(F_p) = pallas_q] is prime, every
    non-identity on-curve point has order exactly [pallas_q]; the
    inverse-dominated ladder cost is independent of the coordinates.

    Layering: this file's curve arithmetic depends only on
    [Garden.EllipticCurve.Pallas]; the ValueCommitR generator point comes from
    [Garden.Orchard.Pallas.Generators], which is why this file lives under
    [Garden/Orchard/] rather than [Garden/EllipticCurve/]. The heavy
    [vm_compute] is isolated here so it recompiles independently.

    Proof method. The reduction is a closed kernel computation. We close the
    goal with [vm_cast_no_check (eq_refl identity)], which leaves a single VM
    cast: the kernel runs the bytecode virtual machine exactly once, at [Qed]
    time, to check that [mul pallas_q value_commit_r_G] is convertible to
    [identity]. (Using [vm_compute; reflexivity] instead would run the VM twice
    — once for the tactic-level goal rewrite, once for the [Qed] re-check — so we
    avoid it here for the ~5-minute ladder.) *)

Require Import Garden.EllipticCurve.Pallas.
Require Import Garden.Orchard.Pallas.Generators.

Module PallasOrder_value_commit_r.

  (** The prime-order certificate stated exactly as
      [PallasGeneratorsOrder.value_commit_r_order]
      ([mul pallas_q value_commit_r_G = identity]). *)
  Lemma value_commit_r_order :
    Pallas.mul Pallas.pallas_q PallasGenerators.value_commit_r_G =
      Pallas.identity.
  Proof.
    vm_cast_no_check (eq_refl Pallas.identity).
  Qed.

End PallasOrder_value_commit_r.
