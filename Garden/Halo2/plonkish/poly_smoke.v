(** * Smoke tests for the polynomial library on a [k = 2] toy domain.

    Concrete checks of division, the root bound, interpolation, and the
    primitive-root enumeration over [F_5] with [w = 2] (a primitive
    [2^2]-th root of unity: [2^4 = 16 = 1] and [2^2 = 4 = -1 mod 5]),
    plus restatements of the pinned Pallas [omega] order certificates. *)

Require Import Garden.Field.Field.
Require Import Garden.Field.Lemmas.
Require Import Garden.Halo2.plonkish.poly.
Require Import Garden.Halo2.plonkish.poly_domain.

Import List.ListNotations.
Global Open Scope Z_scope.

Module PolySmoke.

  (** ** The toy field [F_5] *)

  Lemma prime_5 : IsPrime 5.
  Proof.
    unfold IsPrime.
    apply (proj1 (Znumtheory.prime_alt 5)).
    split; [lia |].
    intros x Hx Hd.
    destruct Hd as [q Hq].
    assert (x = 2 \/ x = 3 \/ x = 4) as [-> | [-> | ->]] by lia; lia.
  Qed.

  #[local] Instance Prime5 : Prime 5 := {| is_prime := prime_5 |}.

  (** ** Division: [X^3 + 2X + 1 = (X^2 + X + 3)(X - 1) + 4] over [F_5] *)

  Goal Poly.pdivmod (p := 5) [1; 2; 0; 1] (Poly.lin (p := 5) 1) =
       ([3; 1; 1], [4; 0; 0; 0]).
  Proof. vm_compute. reflexivity. Qed.

  Goal Poly.peq (p := 5) [1; 2; 0; 1]
         (Poly.padd (p := 5)
            (Poly.pmul (p := 5)
               (Poly.pdiv (p := 5) [1; 2; 0; 1] (Poly.lin (p := 5) 1))
               (Poly.lin (p := 5) 1))
            (Poly.pmod (p := 5) [1; 2; 0; 1] (Poly.lin (p := 5) 1))).
  Proof. vm_compute. reflexivity. Qed.

  Goal (Poly.pdeg (p := 5)
          (Poly.pmod (p := 5) [1%Z; 2%Z; 0%Z; 1%Z] (Poly.lin (p := 5) 1))
        < Poly.pdeg (p := 5) (Poly.lin (p := 5) 1))%nat.
  Proof. vm_compute. lia. Qed.

  (** ** The root bound: [(X - 1)(X - 2)] has the two roots [1, 2] and
      degree 2, so [length [1; 2] < pdeg = 3] via [roots_le_pdeg] *)

  Goal Poly.norm (p := 5) (Poly.prod_lin (p := 5) [1; 2]) = [2; 2; 1].
  Proof. vm_compute. reflexivity. Qed.

  Goal (List.length [1%Z; 2%Z]
        < Poly.pdeg (p := 5) (Poly.prod_lin (p := 5) [1%Z; 2%Z]))%nat.
  Proof.
    apply (Poly.roots_le_pdeg (p := 5) [1; 2]).
    - vm_compute. discriminate.
    - unfold Poly.NoDupP. simpl.
      constructor.
      + intros [H | []]. lia.
      + constructor; [intros [] | constructor].
    - apply List.Forall_forall. intros r Hr.
      destruct Hr as [<- | [<- | []]]; vm_compute; reflexivity.
  Qed.

  (** ** Interpolation on the toy domain [H = [1; 2; 4; 3]] *)

  Goal Poly.eval (p := 5) (Poly.lagrange (p := 5) [1; 2; 4; 3] (fun x => x * x)) 4 = 1.
  Proof. vm_compute. reflexivity. Qed.

  Goal Poly.eval (p := 5) (Poly.lagrange (p := 5) [1; 2; 4; 3] (fun x => x * x)) 3 = 4.
  Proof. vm_compute. reflexivity. Qed.

  Goal Poly.eval (p := 5) (Poly.lagrange_delta (p := 5) [1; 2; 4; 3] 4) 4 = 1.
  Proof. vm_compute. reflexivity. Qed.

  Goal Poly.eval (p := 5) (Poly.lagrange_delta (p := 5) [1; 2; 4; 3] 4) 2 = 0.
  Proof. vm_compute. reflexivity. Qed.

  (** ** The toy primitive root: enumeration and factorization *)

  Goal Poly.w_pows (p := 5) 2 2%nat = [1; 2; 4; 3].
  Proof. vm_compute. reflexivity. Qed.

  Goal Poly.NoDupP (p := 5) (Poly.w_pows (p := 5) 2 2%nat).
  Proof.
    apply (Poly.w_pows_NoDupP (p := 5) 2 2%nat);
      [lia | lia | vm_compute; reflexivity | vm_compute; reflexivity].
  Qed.

  (** [X^4 - 1 = (X - 1)(X - 2)(X - 4)(X - 3)] over [F_5], both via the
      generic factorization theorem and by direct computation. *)
  Goal Poly.peq (p := 5) (Poly.xn1 (p := 5) (2 ^ 2)%nat)
         (Poly.prod_lin (p := 5) (Poly.w_pows (p := 5) 2 2%nat)).
  Proof.
    apply (Poly.xn1_factorization (p := 5) 2 2%nat);
      [lia | lia | vm_compute; reflexivity | vm_compute; reflexivity].
  Qed.

  Goal Poly.norm (p := 5) (Poly.xn1 (p := 5) 4%nat) =
       Poly.norm (p := 5) (Poly.prod_lin (p := 5) (Poly.w_pows (p := 5) 2 2%nat)).
  Proof. vm_compute. reflexivity. Qed.

  (** ** The pinned Pallas [omega]: order certificate restatements *)

  Goal fast_pow_modulo_positive 1 PolyDomain.omega Primes.pallas_p 2048 = 1.
  Proof. exact PolyDomain.omega_pow_2048_check. Qed.

  Goal Fpow (p := Primes.pallas_p) PolyDomain.omega 2048 = 1.
  Proof. exact PolyDomain.omega_order_full. Qed.

  Goal Fpow (p := Primes.pallas_p) PolyDomain.omega 1024 =
       Primes.pallas_p - 1.
  Proof.
    pose proof PolyDomain.omega_order_half as Hh.
    change (2 ^ (Z.of_nat PolyDomain.k - 1)) with 1024 in Hh.
    rewrite Hh.
    vm_compute. reflexivity.
  Qed.

End PolySmoke.
