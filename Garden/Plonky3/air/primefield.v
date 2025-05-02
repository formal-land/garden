Require Import Coq.ZArith.ZArith.
Require Import Plonky3.M.
Require Import Coq.ZArith.Znumtheory.
Open Scope Z_scope.



Module Type PrimeField.
  Parameter F : Type.
  Parameter p : Z.  (* The prime characteristic *)

  (* field operations *)
  Parameter zero : F.
  Parameter one : F.
  Parameter add : F -> F -> F.
  Parameter sub : F -> F -> F.
  Parameter neg : F -> F.
  Parameter mul : F -> F -> F.
  Parameter inv : F -> F.
  Parameter div : F -> F -> F.

  (* integer conversions *)
  Parameter of_Z : Z -> F.
  Parameter to_Z : F -> Z.
  Parameter of_nat : nat -> F.
  Parameter to_nat : F -> nat.
  Parameter of_bool : bool -> F.

  (* Field properties *)
  Parameter p_prime : IsPrime p.

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
  
  (* Field element equality *)
  Axiom to_Z_range : forall a, 0 <= to_Z a < p.
  Axiom of_Z_to_Z : forall a, of_Z (to_Z a) = a.
  Axiom to_Z_of_Z : forall n, 0 <= n < p -> to_Z (of_Z n) = n.
  
  (* Boolean to field conversion *)
  Axiom of_bool_true : of_bool true = one.
  Axiom of_bool_false : of_bool false = zero.    
End PrimeField.

(* An implementation: Mersenne prime p = 2^31 - 1 *)
Module Mersenne31 <: PrimeField.
  Definition p := 2^31 - 1.
  
  (* We'll represent field elements as Z values in the range [0, p-1] *)
  Definition F := {x : Z | 0 <= x < p}.


  Lemma mod_p_in_range : forall x, 0 <= Z.modulo x p < p.
  Proof.
  Admitted.
  
  (* Field operations *)
  Definition zero : F := exist _ 0 (mod_p_in_range 0). 
  Definition one : F := exist _ 1 (mod_p_in_range 1). 

  Definition mod_p (x : Z) : Z := Z.modulo x p.
  
  Definition add (a b : F) : F := 
    match a, b with
    | exist _ va _, exist _ vb _ => 
      exist _ (mod_p (va + vb)) (mod_p_in_range (va + vb))
    end.
  
  Definition mul (a b : F) : F :=
    match a, b with
    | exist _ va _, exist _ vb _ => 
      exist _ (mod_p (va * vb)) (mod_p_in_range (va * vb))
    end.
    
  Definition neg (a : F) : F :=
    match a with
    | exist _ va _ =>
      if Z.eqb va 0 then zero
      else exist _ (mod_p (-va)) (mod_p_in_range (-va))
    end.
    
  Definition sub (a b : F) : F :=
    match a, b with
    | exist _ va _, exist _ vb _ => 
      exist _ (mod_p (va - vb)) (mod_p_in_range (va - vb))
    end.
    
  Definition inv (a : F) : F :=
    match a with
    | exist _ va _ =>
      if Z.eqb va 0 then zero
      (* Just a placeholder, we can compute later with either mathcomp or a ^ (p-2). *)
      else exist _ 1 (mod_p_in_range 1) 
    end.
    
  Definition div (a b : F) : F := mul a (inv b).
  
  (* Conversion functions *)
  Definition of_Z (z : Z) : F := exist _ (mod_p z) (mod_p_in_range z).  (* Proof obligation *)
  Definition to_Z (a : F) : Z := 
    match a with
    | exist _ va _ => va
    end.
  
  Definition of_nat (n : nat) : F := of_Z (Z.of_nat n).
  Definition to_nat (a : F) : nat := Z.to_nat (to_Z a).
  Definition of_bool (b : bool) : F := if b then one else zero.

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


  (* Field element equality *)
  Axiom to_Z_range : forall a, 0 <= to_Z a < p.
  Axiom of_Z_to_Z : forall a, of_Z (to_Z a) = a.
  Axiom to_Z_of_Z : forall n, 0 <= n < p -> to_Z (of_Z n) = n.
  
  (* Boolean to field conversion *)
  Axiom of_bool_true : of_bool true = one.
  Axiom of_bool_false : of_bool false = zero.    
End Mersenne31.

