(** * The multiplicative evaluation domain of the pinned Orchard circuit.

    The deployed verifying key evaluates polynomials over the cyclic group
    [H = <omega>] of order [n = 2^k] in the Pallas base field, with [k = 11]
    ([n = 2048]) per the pinned dump
    [orchard/src/circuit_data/circuit_description_fixed]
    ([PinnedEvaluationDomain { k: 11, extended_k: 14, omega: 0x181b...7813 }]).

    This file pins that [omega] as a Rocq literal and certifies, by two
    [vm_compute] square-and-multiply checks bridged through
    [fast_pow_correct], that its order is exactly [2^11]:
    [omega^2048 = 1] and [omega^1024 = -1].  The generic primitive-root
    theory of [Poly] then yields the repetition-free enumeration
    [omega_pows] of [H], the product decomposition
    [X^2048 - 1 = prod_{j<2048} (X - omega^j)], and the Lagrange row
    selectors [l_0] / [l_last] as delta interpolants on [H]. *)

Require Import Garden.Field.Field.
Require Import Garden.Field.Div.
Require Import Garden.Field.Lemmas.
Require Import Garden.Halo2.plonkish.poly.

Import List.ListNotations.
Global Open Scope Z_scope.

Module PolyDomain.

  (** The pinned [omega] of [circuit_description_fixed], as a canonical
      residue mod [Primes.pallas_p] (decimal
      [10903770050551191186451481744535548418731134600017891582826719412432433936403]). *)
  Definition omega : Z :=
    0x181b50ad5f32119e31cbd395426d600b7a9b88bcaaa1c24eef28545aada17813.

  Definition k : nat := 11%nat.
  Definition n : nat := 2048%nat.

  Lemma n_eq : n = (2 ^ k)%nat.
  Proof. reflexivity. Qed.

  Lemma pallas_p_big : 1 < Primes.pallas_p.
  Proof. exact (prime_range (p := Primes.pallas_p)). Qed.

  Lemma pallas_p_gt2 : 2 < Primes.pallas_p.
  Proof. apply Z.ltb_lt. vm_compute. reflexivity. Qed.

  Lemma omega_canonical : omega mod Primes.pallas_p = omega.
  Proof. vm_compute. reflexivity. Qed.

  (** ** The order certificates *)

  Lemma omega_pow_2048_check :
    fast_pow_modulo_positive 1 omega Primes.pallas_p 2048 = 1.
  Proof. vm_compute. reflexivity. Qed.

  Lemma omega_pow_1024_check :
    fast_pow_modulo_positive 1 omega Primes.pallas_p 1024 =
    Primes.pallas_p - 1.
  Proof. vm_compute. reflexivity. Qed.

  Lemma omega_order_full :
    Fpow (p := Primes.pallas_p) omega (2 ^ Z.of_nat k) = 1.
  Proof.
    unfold Fpow, UnOp.from.
    change (2 ^ Z.of_nat k) with 2048.
    assert (Hp : 0 < Primes.pallas_p) by (pose proof pallas_p_big; lia).
    pose proof (fast_pow_correct Primes.pallas_p Hp 2048%positive 1 omega) as Hf.
    rewrite Z.mul_1_l in Hf.
    rewrite <- Hf.
    exact omega_pow_2048_check.
  Qed.

  Lemma omega_order_half :
    Fpow (p := Primes.pallas_p) omega (2 ^ (Z.of_nat k - 1)) =
    UnOp.from (p := Primes.pallas_p) (-1).
  Proof.
    unfold Fpow, UnOp.from.
    change (2 ^ (Z.of_nat k - 1)) with 1024.
    assert (Hp : 0 < Primes.pallas_p) by (pose proof pallas_p_big; lia).
    pose proof (fast_pow_correct Primes.pallas_p Hp 1024%positive 1 omega) as Hf.
    rewrite Z.mul_1_l in Hf.
    rewrite <- Hf.
    rewrite omega_pow_1024_check.
    vm_compute. reflexivity.
  Qed.

  (** [omega] has order exactly [2^11]: no smaller positive power is 1. *)
  Lemma omega_primitive (m : Z) :
    0 < m < 2 ^ Z.of_nat k -> Fpow (p := Primes.pallas_p) omega m <> 1.
  Proof.
    apply (Poly.w_pow_order (p := Primes.pallas_p) omega k);
      [unfold k; lia | exact pallas_p_gt2
       | exact omega_order_full | exact omega_order_half].
  Qed.

  (** ** The enumeration of [H = { omega^j : 0 <= j < 2048 }] *)

  Definition omega_pows : list Z := Poly.w_pows (p := Primes.pallas_p) omega k.

  Lemma omega_pows_length : List.length omega_pows = n.
  Proof. exact (Poly.w_pows_length (p := Primes.pallas_p) omega k). Qed.

  Lemma omega_pows_nth (j : nat) :
    (j < n)%nat ->
    List.nth j omega_pows 0 = Fpow (p := Primes.pallas_p) omega (Z.of_nat j).
  Proof.
    intros Hj.
    apply (Poly.w_pows_nth (p := Primes.pallas_p) omega k);
      [unfold k; lia | exact Hj].
  Qed.

  (** The [2048] powers are pairwise distinct: [H] enumerates without
      repetition. *)
  Lemma omega_pows_NoDupP : Poly.NoDupP (p := Primes.pallas_p) omega_pows.
  Proof.
    apply (Poly.w_pows_NoDupP (p := Primes.pallas_p) omega k);
      [unfold k; lia | exact pallas_p_gt2
       | exact omega_order_full | exact omega_order_half].
  Qed.

  (** ** The vanishing polynomial splits over [H]:
      [X^2048 - 1 = prod_{j<2048} (X - omega^j)] *)

  Theorem xn1_factorization :
    Poly.peq (p := Primes.pallas_p)
      (Poly.xn1 (p := Primes.pallas_p) n)
      (Poly.prod_lin (p := Primes.pallas_p) omega_pows).
  Proof.
    apply (Poly.xn1_factorization (p := Primes.pallas_p) omega k);
      [unfold k; lia | exact pallas_p_gt2
       | exact omega_order_full | exact omega_order_half].
  Qed.

  (** ** The Lagrange row selectors on [H]

      [row_delta j] is the degree-[< n] interpolant that is [1] at
      [omega^j] and [0] at every other row of [H] — the [l_0] / [l_last]
      Lagrange basis polynomials built by [plonk/keygen.rs].  The Orchard
      domain has [blinding_factors = 5], so [usable_rows = 2042] and
      [l_last] sits at row [2042]. *)

  Definition row_delta (j : nat) : Poly.t :=
    Poly.lagrange_delta (p := Primes.pallas_p)
      omega_pows (List.nth j omega_pows 0).

  Definition l0_poly : Poly.t := row_delta 0.
  Definition l_last_poly : Poly.t := row_delta 2042.

  Lemma row_delta_eval (i j : nat) :
    (i < n)%nat -> (j < n)%nat ->
    Poly.eval (p := Primes.pallas_p) (row_delta j) (List.nth i omega_pows 0) =
    (if (i =? j)%nat then 1 else 0).
  Proof.
    intros Hi Hj.
    unfold row_delta.
    rewrite (Poly.lagrange_delta_eval (p := Primes.pallas_p)
               omega_pows (List.nth j omega_pows 0) (List.nth i omega_pows 0)
               omega_pows_NoDupP).
    - destruct (Nat.eqb_spec i j) as [-> | Hne].
      + now rewrite Z.eqb_refl.
      + destruct (Z.eqb_spec (List.nth i omega_pows 0) (List.nth j omega_pows 0))
          as [He | He]; [| reflexivity].
        exfalso. apply Hne.
        rewrite !omega_pows_nth in He by assumption.
        apply Nat2Z.inj.
        apply (Poly.w_pow_inj (p := Primes.pallas_p) omega k);
          [unfold k; lia | exact pallas_p_gt2
           | exact omega_order_full | exact omega_order_half
           | | | exact He].
        * change (2 ^ Z.of_nat k) with 2048. unfold n in Hi. lia.
        * change (2 ^ Z.of_nat k) with 2048. unfold n in Hj. lia.
    - apply List.nth_In. rewrite omega_pows_length. exact Hi.
  Qed.

  Lemma row_delta_pdeg (j : nat) :
    (Poly.pdeg (p := Primes.pallas_p) (row_delta j) <= n)%nat.
  Proof.
    unfold row_delta.
    rewrite <- omega_pows_length.
    apply Poly.lagrange_delta_pdeg.
  Qed.

End PolyDomain.
