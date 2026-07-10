(** * Prime-order certificate for the Pallas CommitIvkR fixed base

    The prime-order certificate for the CommitIvkR
    generator: the finite computation [[pallas_q] commit_ivk_r_G = identity].
    This is the order certificate that [PallasGeneratorsOrder.commit_ivk_r_order]
    consumes;
    here it is proved outright, ending in [Qed].

    The proof is a closed kernel computation. [Pallas.mul] is the binary
    double-and-add [Weierstrass.mul] at [a = 0]; over [pallas_q] (a 255-bit
    scalar) it runs ~254 doublings and ~127 additions, each performing one
    extended-Euclid modular inverse over [pallas_p]
    ([BinOp.div] via [mod_inverse]). The whole evaluation reduces
    [Pallas.mul Pallas.pallas_q PallasGenerators.commit_ivk_r_G] to
    [Weierstrass.Infinity = Pallas.identity].

    Performance. The reduction is heavy (single-core CPU on the order of a few
    minutes). To avoid evaluating the VM twice — once when [vm_compute] runs as
    a tactic and again when [Qed] re-checks the resulting [VMcast] — the proof
    is given as a single [vm_cast_no_check] of [eq_refl Pallas.identity]: the VM
    conversion then runs exactly once, at [Qed] time.

    Layering. This file's curve arithmetic depends only on
    [Garden.EllipticCurve.Pallas]; the CommitIvkR generator point comes from
    [Garden.Orchard.Pallas.Generators], which is why this file lives under
    [Garden/Orchard/] rather than [Garden/EllipticCurve/]. The generator
    carries the real Zcash CommitIvkR coordinates; because
    [#E_Pallas(F_p) = pallas_q] is prime, every non-identity on-curve point
    has order [pallas_q], so the certificate is a finite computation. *)

Require Import Garden.EllipticCurve.Pallas.
Require Import Garden.Orchard.Pallas.Generators.

Global Open Scope Z_scope.

(** [[pallas_q] commit_ivk_r_G = identity], proved by a
    single VM conversion. The statement matches
    [PallasGeneratorsOrder.commit_ivk_r_order] verbatim. *)
Lemma commit_ivk_r_order :
  Pallas.mul Pallas.pallas_q PallasGenerators.commit_ivk_r_G = Pallas.identity.
Proof.
  vm_cast_no_check (@eq_refl Pallas.point Pallas.identity).
Qed.
