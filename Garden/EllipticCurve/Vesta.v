(** * Vesta instantiation of the generic short-Weierstrass curve

    Vesta is [y^2 = x^3 + 5] over the Pasta scalar field
    [F_{pallas_q}].  Its prime group order is [pallas_p]. *)

Require Import Garden.Field.Field.
Require Import Garden.EllipticCurve.Weierstrass.

Global Open Scope Z_scope.

#[local] Existing Instance Primes.PallasQIsPrime.

Module Vesta.
  Definition a : Z := 0.
  Definition b : Z := 5.

  (** Vesta's base modulus and prime group order. *)
  Definition vesta_p : Z := Primes.pallas_q.
  Definition vesta_q : Z := Primes.pallas_p.

  Definition point : Set := Weierstrass.point.
  Definition identity : point := Weierstrass.Infinity.

  Definition on_curve (P : point) : Prop :=
    Weierstrass.on_curve (p := vesta_p) a b P.
  Definition reduced (P : point) : Prop :=
    Weierstrass.reduced (p := vesta_p) P.
  Definition neg (P : point) : point :=
    Weierstrass.neg (p := vesta_p) P.
  Definition add (P Q : point) : point :=
    Weierstrass.add (p := vesta_p) a P Q.
  Definition mul (k : Z) (P : point) : point :=
    Weierstrass.mul (p := vesta_p) a k P.

  Definition affine (x y : Z) : point :=
    Weierstrass.Affine
      (UnOp.from (p := vesta_p) x)
      (UnOp.from (p := vesta_p) y).

  Lemma nonsingular : Weierstrass.nonsingular (p := vesta_p) a b.
  Proof.
    unfold Weierstrass.nonsingular. intro Hc. vm_compute in Hc. discriminate.
  Qed.

  Lemma three_lt_p : 3 < vesta_p.
  Proof. vm_compute. reflexivity. Qed.

  Lemma eleven_lt_p : 11 < vesta_p.
  Proof. vm_compute. reflexivity. Qed.

  Lemma vesta_q_is_prime : IsPrime vesta_q.
  Proof. exact Primes.pallas_p_prime. Qed.

  Lemma gen_reduced : reduced (affine (-1) 2).
  Proof. vm_compute. split; reflexivity. Qed.
End Vesta.
