(** * Signed-value / representation algebra for the CV_NET leg

    The base-independent algebra behind the [out_cv_net] clause of
    [OrchardProtocolEquiv.output_protocol_eq]
    ([Garden/Orchard/circuit_proof/protocol_equiv.v]).  The circuit-structured
    [OrchardCircuitSpec.value_commit] applies the sign field element ([1] or
    [pallas_p − 1] for [−1]) as a y-coordinate multiplier on the magnitude
    leg; the protocol-aligned [OrchardProtocolSpec.value_commit] instead
    multiplies the base point by the *signed* scalar
    [signed_net_value magnitude sign].  This file relates the two through the
    [PallasModel.repr] bridge:

    - [repr_neg] / [repr_neg_sign]: [repr] of the Weierstrass negation is the
      record with the y-coordinate negated — as [-F y] ([UnOp.opp], the form
      [Weierstrass.neg] produces) and as [(pallas_p − 1) *F y] (the form the
      spec's sign multiplier produces); the [Infinity] / [(0, 0)]-sentinel
      case holds because both negation forms fix [0].
    - [repr_sign_one]: at [sign = 1] the y-multiplier is the identity on the
      [repr] of a reduced point (including the sentinel).
    - [pallas_mul_neg_nonneg]: [[−m] G = −([m] G)] for [m >= 0] — the
      definitional negative-scalar step of [Weierstrass.mul], named.
    - [value_commit_signed_eq]: the composition — for
      [sign ∈ {1, pallas_p − 1}], the [OrchardCircuitSpec.value_commit] shape with
      the two [EccSpec.fixed_scalar_mul] legs already rewritten to
      [OrchardProtocolSpec.mul_value_commit_v] / [mul_value_commit_r] equals
      [OrchardProtocolSpec.value_commit (signed_net_value m sign) rcv].  The
      [repr ∘ Pallas.add = EccSpec.point_add ∘ repr] step is
      [FixedBaseLadder.pallas_repr_add], with the [reduced]/[on_curve] side
      conditions closed by [pallas_mul_reduced]/[pallas_mul_on_curve] over
      the [PallasGenerators] facts; the [m = 0] corner is covered because
      every negation/sign lemma handles the identity sentinel. *)

Require Import Garden.Field.Field.
Require Import Garden.Field.Lemmas.
Require Import Garden.Field.Sqrt.
Require Import Garden.EllipticCurve.Weierstrass.
Require Import Garden.EllipticCurve.Pallas.
Require Import Garden.Halo2.lemmas.
Require Import Garden.Halo2.PallasModel.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.spec.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.fixed_window_canonical.
Require Import Garden.Orchard.Pallas.Generators.
Require Import Garden.Orchard.protocol_spec.
Require Import Garden.Orchard.circuit_proof.internal_spec.
Require Import Garden.Orchard.circuit_proof.ladder.main.
Require Import Stdlib.ZArith.ZArith.

(* The Orchard circuit lives over the Pallas base field; fix the ambient prime
   instance so the field operators below are at [pallas_p] (every other EC and
   Orchard file sets this). *)
#[local] Existing Instance Primes.PallasPIsPrime.

Global Open Scope Z_scope.

(* Keep the square-root / QR chain opaque to the kernel's conversion oracle so
   no up-to-conversion matching ever evaluates [modpow] over the concrete
   Pallas [(p-1)/2] exponent (see [docs/compile-performance.md]). *)
Strategy opaque
  [is_square modpow modpow_pos field_sqrt fixed_window_point_canonical].

Module SignedValueAlgebra.
  Import FixedBaseLadder.

  (** ** Field-level sign algebra

      The two values of the circuit's sign field element act on a
      y-coordinate as the identity ([1 *F y = y] on reduced [y]) and as the
      field negation ([(pallas_p − 1) *F y = -F y], unconditionally). *)

  Lemma sign_one_mul_y (y : Z) (Hy : UnOp.from y = y) :
    1 *F y = y.
  Proof.
    unfold BinOp.mul, UnOp.from in *.
    rewrite Z.mul_1_l.
    exact Hy.
  Qed.

  Lemma sign_neg_mul_y (y : Z) :
    (Primes.pallas_p - 1) *F y = -F y.
  Proof.
    unfold BinOp.mul, UnOp.opp.
    replace ((Primes.pallas_p - 1) * y) with (- y + y * Primes.pallas_p)
      by ring.
    apply Z_mod_plus_full.
  Qed.

  (** Field negation fixes [0] — the [(0, 0)]-sentinel coordinate. *)
  Lemma opp_zero : -F 0 = 0.
  Proof.
    unfold UnOp.opp.
    change (- 0) with 0.
    apply Zmod_0_l.
  Qed.

  (** ** [repr] of a negation

      [PallasModel.repr (Pallas.neg P)] is the record of [repr P] with the
      y-coordinate negated.  No side condition: [Weierstrass.neg] negates the
      affine [y] as [-F y] verbatim, and the [Infinity] case is the [(0, 0)]
      sentinel, whose [y = 0] is fixed by [-F]. *)
  Lemma repr_neg (P : Pallas.point) :
    PallasModel.repr (Pallas.neg P) =
    {| Point.x := Point.x (PallasModel.repr P);
       Point.y := -F Point.y (PallasModel.repr P) |}.
  Proof.
    destruct P as [| x y].
    - unfold Pallas.neg.
      cbn [Weierstrass.neg PallasModel.repr].
      unfold EccSpec.identity.
      cbn [Point.x Point.y].
      rewrite opp_zero.
      reflexivity.
    - reflexivity.
  Qed.

  (** The same fact with the negation in the spec's sign-multiplier form
      [(pallas_p − 1) *F y] — the shape [OrchardCircuitSpec.value_commit] produces
      at [sign = pallas_p − 1]. *)
  Lemma repr_neg_sign (P : Pallas.point) :
    PallasModel.repr (Pallas.neg P) =
    {| Point.x := Point.x (PallasModel.repr P);
       Point.y := (Primes.pallas_p - 1) *F Point.y (PallasModel.repr P) |}.
  Proof.
    rewrite repr_neg.
    rewrite sign_neg_mul_y.
    reflexivity.
  Qed.

  (** At [sign = 1] the y-multiplier is the identity on the [repr] of a
      reduced point (the sentinel's [y = 0] included, via
      [repr_y_reduced]). *)
  Lemma repr_sign_one (P : Pallas.point) (HP : Pallas.reduced P) :
    {| Point.x := Point.x (PallasModel.repr P);
       Point.y := 1 *F Point.y (PallasModel.repr P) |} =
    PallasModel.repr P.
  Proof.
    pose proof (repr_y_reduced P HP) as Hy.
    set (Q := PallasModel.repr P) in *.
    clearbody Q.
    destruct Q as [qx qy].
    cbn [Point.x Point.y] in *.
    rewrite (sign_one_mul_y qy Hy).
    reflexivity.
  Qed.

  (** ** Negative scalar = negated multiple

      [[−m] G = −([m] G)] for [m >= 0]: definitional from [Weierstrass.mul]
      ([mul (Zneg n) = neg (mul_pos n)] by construction, and [mul 0] is the
      infinity fixed by [neg]); stated and proved as the named step of the
      CV_NET composition. *)
  Lemma pallas_mul_neg_nonneg (m : Z) (G : Pallas.point) (Hm : 0 <= m) :
    Pallas.mul (- m) G = Pallas.neg (Pallas.mul m G).
  Proof.
    destruct m as [| n | n].
    - reflexivity.
    - reflexivity.
    - lia.
  Qed.

  (** ** [signed_net_value] at the two circuit sign values *)

  Lemma signed_net_value_one (m : Z) :
    OrchardProtocolSpec.signed_net_value m 1 = m.
  Proof. reflexivity. Qed.

  Lemma signed_net_value_neg_one (m : Z) :
    OrchardProtocolSpec.signed_net_value m (Primes.pallas_p - 1) = - m.
  Proof.
    unfold OrchardProtocolSpec.signed_net_value.
    assert (Hne : (Primes.pallas_p - 1 =? 1) = false).
    { apply Z.eqb_neq. unfold Primes.pallas_p, Primes.t_p. lia. }
    rewrite Hne.
    reflexivity.
  Qed.

  (** ** The CV_NET composition shape

      For [sign ∈ {1, pallas_p − 1}]: the [OrchardCircuitSpec.value_commit] record
      with the two [EccSpec.fixed_scalar_mul] legs already rewritten to the
      protocol group multiples (the exact right-hand sides of
      [value_commit_v_mul_protocol] / [value_commit_r_mul_protocol]) equals
      the protocol value commitment of the signed net value.  [Hm] feeds the
      named step [pallas_mul_neg_nonneg] on the [sign = pallas_p − 1] branch;
      [m = 0] needs no special case because [repr_sign_one]/[repr_neg_sign]
      cover the identity sentinel. *)
  Lemma value_commit_signed_eq (m sign rcv : Z)
      (Hm : 0 <= m)
      (Hsign : sign = 1 \/ sign = Primes.pallas_p - 1) :
    EccSpec.point_add
      {| Point.x := Point.x (OrchardProtocolSpec.mul_value_commit_v m);
         Point.y :=
           sign *F Point.y (OrchardProtocolSpec.mul_value_commit_v m) |}
      (OrchardProtocolSpec.mul_value_commit_r rcv) =
    OrchardProtocolSpec.value_commit
      (OrchardProtocolSpec.signed_net_value m sign) rcv.
  Proof.
    pose proof PallasGenerators.value_commit_v_reduced as HrV.
    pose proof PallasGenerators.value_commit_v_on_curve as HoV.
    pose proof PallasGenerators.value_commit_r_reduced as HrR.
    pose proof PallasGenerators.value_commit_r_on_curve as HoR.
    destruct Hsign as [-> | ->].
    - (* sign = 1: the y-multiplier is the identity, the scalar is [m]. *)
      rewrite signed_net_value_one.
      unfold OrchardProtocolSpec.mul_value_commit_v,
        OrchardProtocolSpec.mul_value_commit_r,
        OrchardProtocolSpec.value_commit.
      rewrite (repr_sign_one
        (Pallas.mul m PallasGenerators.value_commit_v_G)
        (pallas_mul_reduced m PallasGenerators.value_commit_v_G HrV)).
      rewrite (pallas_repr_add
        (Pallas.mul m PallasGenerators.value_commit_v_G)
        (Pallas.mul rcv PallasGenerators.value_commit_r_G)
        (pallas_mul_reduced m PallasGenerators.value_commit_v_G HrV)
        (pallas_mul_reduced rcv PallasGenerators.value_commit_r_G HrR)
        (pallas_mul_on_curve m PallasGenerators.value_commit_v_G HoV)
        (pallas_mul_on_curve rcv PallasGenerators.value_commit_r_G HoR)).
      reflexivity.
    - (* sign = pallas_p − 1: the y-multiplier is the point negation, the
         scalar is [− m]. *)
      rewrite signed_net_value_neg_one.
      unfold OrchardProtocolSpec.mul_value_commit_v,
        OrchardProtocolSpec.mul_value_commit_r,
        OrchardProtocolSpec.value_commit.
      rewrite <- (repr_neg_sign
        (Pallas.mul m PallasGenerators.value_commit_v_G)).
      rewrite <- (pallas_mul_neg_nonneg m
        PallasGenerators.value_commit_v_G Hm).
      rewrite (pallas_repr_add
        (Pallas.mul (- m) PallasGenerators.value_commit_v_G)
        (Pallas.mul rcv PallasGenerators.value_commit_r_G)
        (pallas_mul_reduced (- m) PallasGenerators.value_commit_v_G HrV)
        (pallas_mul_reduced rcv PallasGenerators.value_commit_r_G HrR)
        (pallas_mul_on_curve (- m) PallasGenerators.value_commit_v_G HoV)
        (pallas_mul_on_curve rcv PallasGenerators.value_commit_r_G HoR)).
      reflexivity.
  Qed.
End SignedValueAlgebra.
