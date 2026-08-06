(** * Evaluation-domain setup used by Halo 2 key generation

    This module is the executable, field-independent part of
    [EvaluationDomain::new] from [halo2_proofs/src/poly/domain.rs].  Given the
    constraint-system degree [j] and the commitment parameter [k], Halo 2
    chooses the least exponent at least [k] whose power-of-two domain holds
    [2^k * (j - 1)] coefficients.  The bounded search returns [None] when the
    required exponent exceeds the field's two-adicity.

    The root construction follows the two Rust loops separately: first square
    [ROOT_OF_UNITY] from the field two-adicity down to [extended_k], then from
    [extended_k] down to [k]. *)

From Stdlib Require Import Arith.PeanoNat ZArith.

Module EvaluationDomainSetup.

Definition quotient_poly_degree (degree : nat) : nat :=
  Nat.pred degree.

Definition domain_size (k : nat) : nat :=
  Nat.pow 2 k.

Definition required_extended_size (degree k : nat) : nat :=
  domain_size k * quotient_poly_degree degree.

Fixpoint first_power_at_least
    (fuel current target : nat) : option nat :=
  if Nat.leb target (domain_size current) then Some current
  else
    match fuel with
    | O => None
    | S fuel => first_power_at_least fuel (S current) target
    end.

(** [two_adicity] is [F::S].  The fuel exactly covers the exponents from [k]
    through [F::S], including the initial fit test at [k]. *)
Definition extended_k
    (two_adicity degree k : nat) : option nat :=
  if Nat.leb k two_adicity then
    first_power_at_least
      (two_adicity - k) k (required_extended_size degree k)
  else None.

Fixpoint square_n (modulus : Z) (count : nat) (value : Z) : Z :=
  match count with
  | O => value
  | S count => square_n modulus count ((value * value) mod modulus)
  end.

Definition extended_root
    (modulus root_of_unity : Z) (two_adicity extended_k : nat) : Z :=
  square_n modulus (two_adicity - extended_k) root_of_unity.

Definition root_for_domain
    (modulus root_of_unity : Z)
    (two_adicity extended_k k : nat) : Z :=
  square_n modulus (extended_k - k)
    (extended_root modulus root_of_unity two_adicity extended_k).

End EvaluationDomainSetup.
