Require Import Coq.ZArith.ZArith.
Require Import Plonky3.M.
Require Import Coq.ZArith.Znumtheory.
Open Scope Z_scope.


Module Type PrimeField.
  Parameter p : Z. (* The prime characteristic *)
  Parameter mod_p : Z -> Z.
  
  (* field operations *)
  Parameter zero : Z.
  Parameter one : Z.
  Parameter add : Z -> Z -> Z.
  Parameter mul : Z -> Z -> Z.
  Parameter neg : Z -> Z.
  Parameter sub : Z -> Z -> Z.

  (* inv and div only works for non-zeroes. *)
  Parameter inv : Z -> Prop -> Z.
  Parameter div : Z -> Z -> Prop -> Z.
  
  (* integer & bool conversions *)
  Parameter of_nat : nat -> Z.
  Parameter to_nat : Z -> nat.
  Parameter of_bool : bool -> Z.
  
  (* Field properties *)
  Parameter p_prime : IsPrime p.
  
  (* Additional operations in field.rs *)
  Parameter double : Z -> Z.
  Parameter square : Z -> Z.
  Parameter cube : Z -> Z.
  Parameter xor : Z -> Z -> Z.
  Parameter xor3 : Z -> Z -> Z -> Z.
  Parameter andn : Z -> Z -> Z.
  
  (* Basic algebraic properties *)
  Axiom add_comm : forall a b, add a b = add b a.
  Axiom add_assoc : forall a b c, add (add a b) c = add a (add b c).
  Axiom mul_comm : forall a b, mul a b = mul b a.
  Axiom mul_assoc : forall a b c, mul (mul a b) c = mul a (mul b c).
  Axiom add_zero : forall a, add a zero = a.
  Axiom mul_one : forall a, mul a one = a.
  Axiom mul_zero : forall a, mul a zero = zero.
  Axiom add_neg : forall a, add a (neg a) = zero.
  Axiom sub_def : forall a b, sub a b = add a (neg b).
  Axiom div_def : forall a b, div a b (b <> 0) = mul a (inv b (b <> 0)).
  Axiom mul_inv : forall a c, a <> zero -> mul a (inv a c) = one.
  Axiom distrib : forall a b c, mul a (add b c) = add (mul a b) (mul a c).
  Axiom of_bool_true : of_bool true = one.
  Axiom of_bool_false : of_bool false = zero.
End PrimeField.

(* Core module type with just the prime *)
Module Type PrimeParameter.
  Parameter p : Z.
  Parameter p_prime : IsPrime p.
End PrimeParameter.

(* Functor that implements all field operations given a prime *)
Module MakePrimeField (P : PrimeParameter) <: PrimeField.
  Definition p := P.p.
  Definition mod_p (x : Z) : Z := Z.modulo x p.
  
  (* Field operations *)
  Definition zero : Z := 0.
  Definition one : Z := 1.
  Definition add (a b : Z) : Z := mod_p (a + b).
  Definition mul (a b : Z) : Z := mod_p (a * b).
  Definition neg (a : Z) : Z := mod_p (p - a).
  Definition sub (a b : Z) : Z := mod_p (a + p - b).
  Definition inv (a : Z) (c : Prop) : Z := mod_p (a ^ (p - 2)).
  Definition div (a b : Z) (c : Prop) : Z := mul a (inv b c).
  
  (* Integer conversions *)
  Definition of_nat (n : nat) : Z := Z.of_nat n.
  Definition to_nat (a : Z) : nat := Z.to_nat a.
  Definition of_bool (b : bool) : Z := if b then one else zero.
  
  (* Use the provided prime proof *)
  Definition p_prime := P.p_prime.
  
  (* Additional operations *)
  Definition double (a : Z) : Z := add a a.
  Definition square (a : Z) : Z := mul a a.
  Definition cube (a : Z) : Z := mul (square a) a.
  Definition xor (a b : Z) : Z := sub (add a b) (mul a (double b)).
  Definition xor3 (a b c : Z) : Z := xor (xor a b) c.
  Definition andn (a b : Z) : Z := mul (sub one a) b.
  
  (* Proofs of field properties *)
  Lemma add_comm : forall a b, add a b = add b a.
  Proof.
    intros a b. unfold add, mod_p.
    rewrite Z.add_comm. reflexivity.
  Qed.
  
  Lemma add_assoc : forall a b c, add (add a b) c = add a (add b c).
  Proof. Admitted.
  
  Lemma mul_comm : forall a b, mul a b = mul b a.
  Proof. Admitted.
  
  Lemma mul_assoc : forall a b c, mul (mul a b) c = mul a (mul b c).
  Proof. Admitted.
  
  Lemma add_zero : forall a, add a zero = a.
  Proof. Admitted.
  
  Lemma mul_one : forall a, mul a one = a.
  Proof. Admitted.
  
  Lemma mul_zero : forall a, mul a zero = zero.
  Proof. Admitted.
  
  Lemma add_neg : forall a, add a (neg a) = zero.
  Proof. Admitted.
  
  Lemma sub_def : forall a b, sub a b = add a (neg b).
  Proof. Admitted.
  
  Lemma div_def : forall a b, div a b (b <> 0) = mul a (inv b (b <> 0)).
  Proof. Admitted.
  
  Lemma mul_inv : forall a c, a <> zero -> mul a (inv a c) = one.
  Proof. Admitted.
  
  Lemma distrib : forall a b c, mul a (add b c) = add (mul a b) (mul a c).
  Proof. Admitted.
  
  Lemma of_bool_true : of_bool true = one.
  Proof. unfold of_bool, one. reflexivity. Qed.
  
  Lemma of_bool_false : of_bool false = zero.
  Proof. unfold of_bool, zero. reflexivity. Qed.
End MakePrimeField.

(* Define Mersenne31 prime as the prime parameter module *)
Module Mersenne31Parameter <: PrimeParameter.
  Definition p : Z := 2147483647.  (* 2^31 - 1 *)
  
  Lemma p_prime : IsPrime p.
  Proof. Admitted.
End Mersenne31Parameter.

Module Mersenne31 := MakePrimeField(Mersenne31Parameter).

(* Define BabyBear prime, 2^31 - 2^27 + 1, as the prime parameter module *)
Module BabyBearParameter <: PrimeParameter.
  Definition p : Z := 2^31 - 2^27 + 1.
  
  Lemma p_prime : IsPrime p.
  Proof. Admitted.
End BabyBearParameter.

Module BabyBear := MakePrimeField(BabyBearParameter).


(* Define KoalaBear prime field, 2^31 - 2^24 + 1 *)
Module KoalaBearParameter <: PrimeParameter.
  Definition p : Z := 2^31 - 2^27 + 1.
  
  Lemma p_prime : IsPrime p.
  Proof. Admitted.
End KoalaBearParameter.

Module KoalaBear := MakePrimeField(KoalaBearParameter).

(* Define Goldilocks prime field, which is 2^64 - 2^32 + 1 *)
Module GoldilocksParameter <: PrimeParameter.
  Definition p : Z := 2^64 - 2^32 + 1.
  
  Lemma p_prime : IsPrime p.
  Proof. Admitted.
End GoldilocksParameter.
Module Goldilocks := MakePrimeField(GoldilocksParameter).
