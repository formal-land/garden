(** * Prime-order facts for the Orchard fixed-base generators

    The order-theory layer over [Garden.Orchard.Pallas.Generators]: for each
    fixed-base generator, the prime-order certificate
    [[pallas_q] G = identity] together with the derived order
    characterisation [ord = pallas_q] (as the divisibility iff) and the
    injectivity of [mul] modulo [pallas_q], from the generic
    [Weierstrass] order theory ([mul_eq_Infinity_iff] /
    [mul_injective_mod]) and [Pallas.pallas_q_is_prime].

    The per-generator certificates live in the [order_<base>.v] leaf files,
    each an instance of [PallasOrder.pallas_mul_q_on_curve]
    ([Garden/EllipticCurve/PallasOrder.v] — every reduced on-curve Pallas
    point is annihilated by [pallas_q]) at that generator's
    [reduced] / [on_curve] facts; this file only re-exports them under the
    [PallasGeneratorsOrder] names and derives the order characterisation and
    injectivity.  Keeping the certificates out of [Generators.v] keeps the
    generator points file cheap: the fixed-base table leaves depend on the
    points but not on the order facts. *)

Require Import Garden.Field.Field.
Require Import Garden.EllipticCurve.Weierstrass.
Require Import Garden.EllipticCurve.Pallas.
Require Import Garden.Orchard.Pallas.Generators.
Require Import Garden.Orchard.Pallas.order_spend_auth_g.
Require Import Garden.Orchard.Pallas.order_value_commit_v.
Require Import Garden.Orchard.Pallas.order_value_commit_r.
Require Import Garden.Orchard.Pallas.order_nullifier_k.
Require Import Garden.Orchard.Pallas.order_note_commit_r.
Require Import Garden.Orchard.Pallas.order_commit_ivk_r.

Global Open Scope Z_scope.

#[local] Existing Instance Primes.PallasPIsPrime.

Module PallasGeneratorsOrder.
  Import Pallas.
  Import PallasGenerators.

  (** Feed the [Weierstrass] order theory the order certificates ([_order], which are in
      [Pallas.mul] form) without recomputing the [pallas_q]-fold ladder: when the
      kernel checks an [_order] proof against the [Weierstrass.mul] shape the
      lemma expects, the two heads ([Pallas.mul] / [Weierstrass.mul]) differ and
      the conversion oracle would otherwise re-evaluate the (concrete,
      ~255-bit-scalar) ladder. Making [Weierstrass.mul] opaque to conversion
      forces the cheap [delta] unfolding of [Pallas.mul] instead. Transparency
      is restored before [End PallasGeneratorsOrder]. *)
  Strategy opaque [Weierstrass.mul].

  (** *** SpendAuthG (the RK base) *)
  Lemma spend_auth_g_order : mul pallas_q spend_auth_g_G = identity.
  Proof. exact PallasOrder_spend_auth_g.spend_auth_g_order. Qed.

  Lemma spend_auth_g_order_eq (n : Z) :
    mul n spend_auth_g_G = identity <-> Z.divide pallas_q n.
  Proof.
    exact (Weierstrass.mul_eq_Infinity_iff (p := Primes.pallas_p) a b
             spend_auth_g_G pallas_q eleven_lt_p nonsingular spend_auth_g_reduced
             spend_auth_g_on_curve spend_auth_g_ne_identity pallas_q_is_prime
             spend_auth_g_order n).
  Qed.

  Lemma spend_auth_g_mul_injective (i j : Z) :
    mul i spend_auth_g_G = mul j spend_auth_g_G <-> i mod pallas_q = j mod pallas_q.
  Proof.
    exact (Weierstrass.mul_injective_mod (p := Primes.pallas_p) a b
             spend_auth_g_G pallas_q eleven_lt_p nonsingular spend_auth_g_reduced
             spend_auth_g_on_curve spend_auth_g_ne_identity pallas_q_is_prime
             spend_auth_g_order i j).
  Qed.

  (** *** ValueCommitV *)
  Lemma value_commit_v_order : mul pallas_q value_commit_v_G = identity.
  Proof. exact PallasOrder_value_commit_v.value_commit_v_order. Qed.

  Lemma value_commit_v_order_eq (n : Z) :
    mul n value_commit_v_G = identity <-> Z.divide pallas_q n.
  Proof.
    exact (Weierstrass.mul_eq_Infinity_iff (p := Primes.pallas_p) a b
             value_commit_v_G pallas_q eleven_lt_p nonsingular value_commit_v_reduced
             value_commit_v_on_curve value_commit_v_ne_identity pallas_q_is_prime
             value_commit_v_order n).
  Qed.

  Lemma value_commit_v_mul_injective (i j : Z) :
    mul i value_commit_v_G = mul j value_commit_v_G <->
    i mod pallas_q = j mod pallas_q.
  Proof.
    exact (Weierstrass.mul_injective_mod (p := Primes.pallas_p) a b
             value_commit_v_G pallas_q eleven_lt_p nonsingular value_commit_v_reduced
             value_commit_v_on_curve value_commit_v_ne_identity pallas_q_is_prime
             value_commit_v_order i j).
  Qed.

  (** *** ValueCommitR *)
  Lemma value_commit_r_order : mul pallas_q value_commit_r_G = identity.
  Proof. exact PallasOrder_value_commit_r.value_commit_r_order. Qed.

  Lemma value_commit_r_order_eq (n : Z) :
    mul n value_commit_r_G = identity <-> Z.divide pallas_q n.
  Proof.
    exact (Weierstrass.mul_eq_Infinity_iff (p := Primes.pallas_p) a b
             value_commit_r_G pallas_q eleven_lt_p nonsingular value_commit_r_reduced
             value_commit_r_on_curve value_commit_r_ne_identity pallas_q_is_prime
             value_commit_r_order n).
  Qed.

  Lemma value_commit_r_mul_injective (i j : Z) :
    mul i value_commit_r_G = mul j value_commit_r_G <->
    i mod pallas_q = j mod pallas_q.
  Proof.
    exact (Weierstrass.mul_injective_mod (p := Primes.pallas_p) a b
             value_commit_r_G pallas_q eleven_lt_p nonsingular value_commit_r_reduced
             value_commit_r_on_curve value_commit_r_ne_identity pallas_q_is_prime
             value_commit_r_order i j).
  Qed.

  (** *** NullifierK *)
  Lemma nullifier_k_order : mul pallas_q nullifier_k_G = identity.
  Proof. exact PallasOrder_nullifier_k.nullifier_k_order. Qed.

  Lemma nullifier_k_order_eq (n : Z) :
    mul n nullifier_k_G = identity <-> Z.divide pallas_q n.
  Proof.
    exact (Weierstrass.mul_eq_Infinity_iff (p := Primes.pallas_p) a b
             nullifier_k_G pallas_q eleven_lt_p nonsingular nullifier_k_reduced
             nullifier_k_on_curve nullifier_k_ne_identity pallas_q_is_prime
             nullifier_k_order n).
  Qed.

  Lemma nullifier_k_mul_injective (i j : Z) :
    mul i nullifier_k_G = mul j nullifier_k_G <-> i mod pallas_q = j mod pallas_q.
  Proof.
    exact (Weierstrass.mul_injective_mod (p := Primes.pallas_p) a b
             nullifier_k_G pallas_q eleven_lt_p nonsingular nullifier_k_reduced
             nullifier_k_on_curve nullifier_k_ne_identity pallas_q_is_prime
             nullifier_k_order i j).
  Qed.

  (** *** NoteCommitR *)
  Lemma note_commit_r_order : mul pallas_q note_commit_r_G = identity.
  Proof. exact PallasOrder_note_commit_r.note_commit_r_order. Qed.

  Lemma note_commit_r_order_eq (n : Z) :
    mul n note_commit_r_G = identity <-> Z.divide pallas_q n.
  Proof.
    exact (Weierstrass.mul_eq_Infinity_iff (p := Primes.pallas_p) a b
             note_commit_r_G pallas_q eleven_lt_p nonsingular note_commit_r_reduced
             note_commit_r_on_curve note_commit_r_ne_identity pallas_q_is_prime
             note_commit_r_order n).
  Qed.

  Lemma note_commit_r_mul_injective (i j : Z) :
    mul i note_commit_r_G = mul j note_commit_r_G <-> i mod pallas_q = j mod pallas_q.
  Proof.
    exact (Weierstrass.mul_injective_mod (p := Primes.pallas_p) a b
             note_commit_r_G pallas_q eleven_lt_p nonsingular note_commit_r_reduced
             note_commit_r_on_curve note_commit_r_ne_identity pallas_q_is_prime
             note_commit_r_order i j).
  Qed.

  (** *** CommitIvkR *)
  Lemma commit_ivk_r_order : mul pallas_q commit_ivk_r_G = identity.
  Proof.
    exact Garden.Orchard.Pallas.order_commit_ivk_r.commit_ivk_r_order.
  Qed.

  Lemma commit_ivk_r_order_eq (n : Z) :
    mul n commit_ivk_r_G = identity <-> Z.divide pallas_q n.
  Proof.
    exact (Weierstrass.mul_eq_Infinity_iff (p := Primes.pallas_p) a b
             commit_ivk_r_G pallas_q eleven_lt_p nonsingular commit_ivk_r_reduced
             commit_ivk_r_on_curve commit_ivk_r_ne_identity pallas_q_is_prime
             commit_ivk_r_order n).
  Qed.

  Lemma commit_ivk_r_mul_injective (i j : Z) :
    mul i commit_ivk_r_G = mul j commit_ivk_r_G <-> i mod pallas_q = j mod pallas_q.
  Proof.
    exact (Weierstrass.mul_injective_mod (p := Primes.pallas_p) a b
             commit_ivk_r_G pallas_q eleven_lt_p nonsingular commit_ivk_r_reduced
             commit_ivk_r_on_curve commit_ivk_r_ne_identity pallas_q_is_prime
             commit_ivk_r_order i j).
  Qed.

  (** Restore the default transparency of [Weierstrass.mul] (made opaque above
      only to keep the order-theory conversions cheap). *)
  Strategy transparent [Weierstrass.mul].
End PallasGeneratorsOrder.
