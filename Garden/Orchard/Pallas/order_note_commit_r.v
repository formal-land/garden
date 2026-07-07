(** * Pallas prime-order certificate for the NoteCommitR fixed base

    The
    prime-order certificate [[pallas_q] G = identity] for the NoteCommitR
    generator [G = PallasGenerators.note_commit_r_G], by the finite
    [vm_compute] of the double-and-add ladder over the Pallas base field.

    This is a curve-arithmetic computation over [Garden.EllipticCurve.Pallas];
    the NoteCommitR generator point comes from
    [Garden.Orchard.Pallas.Generators], which is why this file lives under
    [Garden/Orchard/] rather than [Garden/EllipticCurve/]. It proves exactly
    the certificate consumed by
    [PallasGeneratorsOrder.note_commit_r_order].

    The generator carries the real Zcash NoteCommitR coordinates; because
    [#E_Pallas(F_p) = pallas_q] is prime, the group is cyclic of prime order
    [pallas_q], so every non-identity point has order [pallas_q] and is
    annihilated by the scalar [pallas_q].

    Proof discipline. The heavy computation ([pallas_q] is a 255-bit scalar,
    ~300 point operations, each dominated by one extended-Euclid modular inverse over
    the 254-bit prime [pallas_p]) is run exactly once, inside the kernel, via
    [vm_cast_no_check (eq_refl Pallas.identity)]: the tactic provides the
    reflexivity witness without a tactic-time reduction and asks the kernel to
    discharge the conversion [[pallas_q] G == identity] with the bytecode VM. *)

Require Import Garden.EllipticCurve.Pallas.
Require Import Garden.Orchard.Pallas.Generators.

Module PallasOrder_note_commit_r.
  Lemma note_commit_r_order :
    Pallas.mul Pallas.pallas_q PallasGenerators.note_commit_r_G =
      Pallas.identity.
  Proof.
    vm_cast_no_check (eq_refl Pallas.identity).
  Qed.
End PallasOrder_note_commit_r.
