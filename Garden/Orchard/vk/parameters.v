(** * Deployment parameters for the Post-NU6.3 Orchard verifying key *)

From Stdlib Require Import Arith.PeanoNat ZArith.ZArith.
Require Import Garden.Field.Field.

Local Open Scope Z_scope.

Module OrchardVkParameters.

(** The exponent supplied to [Params::new].  This is a deployment input: the
    circuit determines whether the chosen domain is large enough, but does not
    uniquely select this exponent. *)
Definition k : nat := 11%nat.

(** The two-adicity [F::S] of the Vesta scalar field [Fp]. *)
Definition scalar_two_adicity : nat := 32%nat.

(** [32] is derived from the scalar modulus: [2^32] divides [p - 1],
    while the remaining cofactor is odd.  Hence no larger power of two
    divides the multiplicative-group order. *)
Lemma scalar_two_adicity_exact :
  (Primes.pallas_p - 1) mod (2 ^ Z.of_nat scalar_two_adicity) = 0 /\
  ((Primes.pallas_p - 1) /
    (2 ^ Z.of_nat scalar_two_adicity)) mod 2 = 1.
Proof. vm_compute. split; reflexivity. Qed.

Definition n : nat := Nat.pow 2 k.

End OrchardVkParameters.
