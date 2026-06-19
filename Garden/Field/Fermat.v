(** * Fermat's little theorem and field-inverse correctness over [Z]

    The Garden field layer represents field elements as integers reduced
    [mod p]. The field facts that need primality content — Fermat's little
    theorem and correctness of the modular inverse — are obtained here by a
    small bridge to mathcomp's [fermat_little] (which lives over [nat]).

    From the assumed [Znumtheory.prime] facts this derives a usable inverse
    law. *)

Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.ZArith.Znumtheory.
Require Import Stdlib.ZArith.Zpow_facts.
Require Import Stdlib.micromega.Lia.

(* mathcomp is imported last so that the unqualified [prime] is mathcomp's
   [nat]-predicate and the [%N] delimiter denotes mathcomp's [nat_scope]; the
   [Z]-level number-theoretic predicate is always written [Znumtheory.prime]. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div prime binomial.

Open Scope Z_scope.

(** ** Bridge lemmas: mathcomp [nat] arithmetic to [Z] *)

(** [expn] (mathcomp nat power) transported to [Z.pow]. *)
Lemma expn_to_Z (n m : nat) :
  Z.of_nat (expn n m) = (Z.of_nat n) ^ (Z.of_nat m).
Proof.
  induction m as [|m IH].
  - rewrite expn0. reflexivity.
  - rewrite expnS -multE Nat2Z.inj_mul IH.
    rewrite Nat2Z.inj_succ Z.pow_succ_r; [ reflexivity | apply Nat2Z.is_nonneg ].
Qed.

(** [modn] (mathcomp nat modulo) transported to [Z.modulo]. *)
Lemma modn_to_Z (x d : nat) :
  (0 < d)%N -> Z.of_nat (modn x d) = (Z.of_nat x) mod (Z.of_nat d).
Proof.
  intros Hd.
  pose proof (ltn_pmod x Hd) as Hlt.
  pose proof (divn_eq x d) as Heq.
  apply (f_equal Z.of_nat) in Heq.
  rewrite -plusE -multE Nat2Z.inj_add Nat2Z.inj_mul in Heq.
  assert (HdZ : 0 < Z.of_nat d).
  { assert (Hd' : (0 < d)%coq_nat) by (apply/ltP; exact Hd). lia. }
  assert (HrltZ : Z.of_nat (modn x d) < Z.of_nat d).
  { assert (Hlt' : (modn x d < d)%coq_nat) by (apply/ltP; exact Hlt). lia. }
  pose proof (Nat2Z.is_nonneg (modn x d)) as Hrnn.
  rewrite Heq Z.add_comm Z_mod_plus_full.
  symmetry. apply Z.mod_small. lia.
Qed.

(** [Znumtheory] primality of [p] gives mathcomp primality of its [nat] image. *)
Lemma prime_Z_to_nat (p : Z) :
  Znumtheory.prime p -> prime (Z.to_nat p).
Proof.
  intros Hp.
  pose proof (Znumtheory.prime_ge_2 _ Hp) as Hp2.
  assert (HP : Z.of_nat (Z.to_nat p) = p) by (apply Z2Nat.id; lia).
  apply/primeP. split.
  - assert (Hle : (2 <= Z.to_nat p)%coq_nat).
    { rewrite Nat2Z.inj_le. rewrite HP. simpl; lia. }
    apply/ltP. lia.
  - intros d Hdvd.
    move/dvdnP: Hdvd => [k Hk].
    assert (Hdivide : (Z.of_nat d | p)).
    { exists (Z.of_nat k).
      rewrite <- HP. rewrite Hk. rewrite <- multE. rewrite Nat2Z.inj_mul. ring. }
    pose proof (Znumtheory.prime_divisors p Hp (Z.of_nat d) Hdivide) as Hcases.
    pose proof (Nat2Z.is_nonneg d) as Hdnn.
    apply/orP.
    destruct Hcases as [H1 | [H1 | [H1 | H1]]].
    + exfalso; lia.
    + left. apply/eqP. apply Nat2Z.inj. rewrite H1. reflexivity.
    + right. apply/eqP. apply Nat2Z.inj. rewrite H1. symmetry; exact HP.
    + exfalso; lia.
Qed.

(** ** Fermat's little theorem over [Z] *)

Lemma fermat_little_Z (a p : Z) :
  Znumtheory.prime p -> 0 <= a -> (a ^ p) mod p = a mod p.
Proof.
  intros Hp Ha.
  pose proof (Znumtheory.prime_ge_2 _ Hp) as Hp2.
  pose proof (prime_Z_to_nat p Hp) as Hpr.
  pose proof (@fermat_little (Z.to_nat a) (Z.to_nat p) Hpr) as HF.
  apply (f_equal Z.of_nat) in HF.
  assert (HP0 : (0 < Z.to_nat p)%N).
  { apply/ltP.
    assert (Hle : (1 <= Z.to_nat p)%coq_nat).
    { rewrite Nat2Z.inj_le. rewrite (Z2Nat.id p ltac:(lia)). lia. }
    lia. }
  rewrite !(modn_to_Z _ _ HP0) in HF.
  rewrite expn_to_Z in HF.
  rewrite !(Z2Nat.id a Ha) !(Z2Nat.id p ltac:(lia)) in HF.
  exact HF.
Qed.

(** ** Field-inverse correctness *)

(** [a^(p-1) = 1] in the field, for a reduced nonzero [a]. *)
Lemma flt_pow_pred (a p : Z) :
  Znumtheory.prime p -> 0 < a < p -> (a ^ (p - 1)) mod p = 1.
Proof.
  intros Hp Ha.
  pose proof (Znumtheory.prime_ge_2 _ Hp) as Hp2.
  pose proof (fermat_little_Z a p Hp ltac:(lia)) as HF.
  assert (Hamod : a mod p = a) by (apply Z.mod_small; lia).
  rewrite Hamod in HF.
  assert (Hpow : a ^ p = a ^ (p - 1) * a).
  { replace p with ((p - 1) + 1) at 1 by lia.
    rewrite Z.pow_add_r; [ | lia | lia]. rewrite Z.pow_1_r. reflexivity. }
  rewrite Hpow in HF.
  assert (Hd1 : (a ^ (p - 1) * a - a) mod p = 0).
  { rewrite Zminus_mod. rewrite HF. rewrite Hamod.
    replace (a - a) with 0 by ring. apply Zmod_0_l. }
  apply Z.mod_divide in Hd1; [ | lia].
  assert (Hd2 : (p | a * (a ^ (p - 1) - 1))).
  { replace (a * (a ^ (p - 1) - 1)) with (a ^ (p - 1) * a - a) by ring. exact Hd1. }
  assert (Hrp : Znumtheory.rel_prime p a).
  { apply Znumtheory.prime_rel_prime; [exact Hp |].
    intro Hc. apply Z.divide_pos_le in Hc; lia. }
  pose proof (Znumtheory.Gauss p a (a ^ (p - 1) - 1) Hd2 Hrp) as Hd3.
  apply Z.mod_divide in Hd3; [ | lia].
  replace (a ^ (p - 1)) with ((a ^ (p - 1) - 1) + 1) by ring.
  rewrite Zplus_mod Hd3 Z.add_0_l (Z.mod_mod 1 p ltac:(lia)).
  apply Z.mod_small; lia.
Qed.

(** The modular inverse [a^(p-2) mod p] inverts [a], for any integer [a] not
    divisible by [p]. This is the field-inverse law (the [a^(p-2)] form matches
    both [Field.mod_inverse] and the Rust [Field] inverse). *)
Lemma inv_correct_gen (a p : Z) :
  Znumtheory.prime p -> a mod p <> 0 ->
  (a * (a ^ (p - 2) mod p)) mod p = 1.
Proof.
  intros Hp Hnz.
  pose proof (Znumtheory.prime_ge_2 _ Hp) as Hp2.
  rewrite Zmult_mod_idemp_r.
  replace (a * a ^ (p - 2)) with (a ^ (p - 1)).
  2:{ replace (p - 1) with ((p - 2) + 1) by lia.
      rewrite Z.pow_add_r; [ | lia | lia]. rewrite Z.pow_1_r. ring. }
  assert (Hr : 0 <= a mod p < p) by (apply Z.mod_pos_bound; lia).
  rewrite (Zpower_mod a (p - 1) p ltac:(lia)).
  apply flt_pow_pred; [exact Hp | lia].
Qed.
