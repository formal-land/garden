Require Import Coq.ZArith.ZArith.
Require Import Plonky3.M.
Require Import Coq.ZArith.Znumtheory.
Open Scope Z_scope.



Module Type PrimeField.
  (* unused abstraction: Parameter F : Type. *)
  Parameter p : Z.  (* The prime characteristic *)

  Definition mod_p (x : Z) : Z := Z.modulo x p.

  (* 
    later we need an assertion here that all operations are
    within the prime field with characteristic p,
    so all elements are in the range [0, p-1].
  *)

  (* field operations *)
  Definition zero : Z := 0.
  Definition one : Z := 1.
  Definition add (a b : Z) : Z := 
    mod_p (a + b).
  
  Definition mul (a b : Z) : Z :=
    mod_p (a * b).
    
  Definition neg (a : Z) : Z :=
    mod_p (p - a).
    
  Definition sub (a b : Z) : Z :=
    mod_p (a + p - b).
    
  Definition inv (a : Z) : Z := mod_p (a ^ (p - 2)).

  Definition div (a b : Z) : Z := mul a (inv b).

  (* integer conversions *)
  (*
  These two are used as placeholders now 
  because we temporarily use Z as the field type instead of F as abstraction.
  =======
  Parameter of_Z : Z -> F.
  Parameter to_Z : F -> Z.
  *)

  Definition of_nat (n : nat) : Z := Z.of_nat n.
  Definition to_nat (a : Z) : nat := Z.to_nat a.
  Definition of_bool (b : bool) : Z := if b then one else zero.

  (* Field properties *)
  Parameter p_prime : IsPrime p.

  (* Additional operations in field.rs *)
  Definition double (a : Z) : Z := add a a.
  Definition square (a : Z) : Z := mul a a.
  Definition cube (a : Z) : Z := mul (square a) a.

  (* for boolean inputs only. *)
  Definition xor (a b : Z) : Z := sub (add a b) (mul a (double b)).
  Definition xor3 (a b c : Z) : Z := xor (xor a b) c.
  Definition andn (a b : Z) : Z := mul (sub one a) b.



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
  Axiom div_def : forall a b, div a b = mul a (inv b).
  Axiom mul_inv : forall a, a <> zero -> mul a (inv a) = one.

  (* Distributivity *)
  Axiom distrib : forall a b c, mul a (add b c) = add (mul a b) (mul a c).
  
  (* Boolean to field conversion *)
  Axiom of_bool_true : of_bool true = one.
  Axiom of_bool_false : of_bool false = zero.    
End PrimeField.

(* (* An implementation: Mersenne prime p = 2^31 - 1.
  The computations here are done primitively, especially the implementation of inverse.
  Later we could replace the implementations with mathcomp.
 *)
Module Mersenne31 <: PrimeField.
  Definition p : Z := 2147483647.  (* 2^31 - 1 *)

  (* Modulo utility for all prime fields. *)
  Definition mod_p (x : Z) : Z := Z.modulo x p.

  (* Proof that the field is in the range [0, p-1] *)
  (* This is a placeholder, we will need to prove this later. *)
  (* We can use Z.modulo to ensure the result is in the range. *)
  (* The proof obligation is that all operations are within the prime field. *)
  
  (* Proof obligation: for all x, 0 <= x < p *)
  Lemma mod_p_in_range : forall x, 0 <= Z.modulo x p < p.
  Proof.
  Admitted.
  
  (* Field operations, for now use pure integer zero and one,
  as we are dealing with prime fields. *)
  Definition zero : Z := 0.
  Definition one : Z := 1.
  
  Definition add (a b : Z) : Z := 
    mod_p (a + b).
  
  Definition mul (a b : Z) : Z :=
    mod_p (a * b).
    
  Definition neg (a : Z) : Z :=
    mod_p (p - a).
    
  Definition sub (a b : Z) : Z :=
    mod_p (a + p - b).
    
  Definition inv (a : Z) : Z := mod_p (a ^ (p - 2)).
  
  (* Division is defined as multiplication by the inverse *)
  (* This is a placeholder, we will need to prove this later. *)
  (* The proof obligation is that all operations are within the prime field. *)
    
    
  Definition div (a b : Z) : Z := mul a (inv b).
  
  (* Conversion functions *)
  (* Definition of_Z (z : Z) : F := exist _ (mod_p z) (mod_p_in_range z).  (* Proof obligation *)
  Definition to_Z (a : F) : Z := 
    match a with
    | exist _ va _ => va
    end. *)
  
  Definition of_nat (n : nat) : Z := Z.of_nat n.
  Definition to_nat (a : Z) : nat := Z.to_nat a.
  Definition of_bool (b : bool) : Z := if b then one else zero.

  Axiom p_prime : IsPrime p.
  Axiom add_comm : forall a b, add a b = add b a.
  Axiom add_assoc : forall a b c, add (add a b) c = add a (add b c).
  Axiom mul_comm : forall a b, mul a b = mul b a.
  Axiom mul_assoc : forall a b c, mul (mul a b) c = mul a (mul b c).
  Axiom add_zero : forall a, add a zero = a.
  Axiom mul_one : forall a, mul a one = a.
  Axiom mul_zero : forall a, mul a zero = zero.
  Axiom add_neg : forall a, add a (neg a) = zero.
  Axiom sub_def : forall a b, sub a b = add a (neg b).
  Axiom div_def : forall a b, div a b = mul a (inv b).
  Axiom mul_inv : forall a, a <> zero -> mul a (inv a) = one.
  Axiom distrib : forall a b c, mul a (add b c) = add (mul a b) (mul a c).

  
  (* Boolean to field conversion *)
  Axiom of_bool_true : of_bool true = one.
  Axiom of_bool_false : of_bool false = zero.    
End Mersenne31.
 *)
