(** * Generic integer facts about powers and division

    Pure [Z] arithmetic shared by the bit-slice and digit-decomposition
    proofs: a packed message is read as [x / base ^ a mod base ^ b], so the
    same positivity, exponent-splitting and iterated-division facts recur in
    every file that identifies a witnessed cell with a slice.  Nothing here
    mentions a modulus or a field; these are thin wrappers over the standard
    library kept in one place so the callers share a statement. *)

Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.micromega.Lia.

Global Open Scope Z_scope.

Lemma pow2_pos (a : Z) : 0 <= a -> 0 < 2 ^ a.
Proof. intros Ha. apply Z.pow_pos_nonneg; lia. Qed.

Lemma pow2_split (a b : Z) : 0 <= a -> 0 <= b ->
  2 ^ (a + b) = 2 ^ a * 2 ^ b.
Proof. intros. apply Z.pow_add_r; lia. Qed.

Lemma div_div_pow (x a b : Z) : 0 <= a -> 0 <= b ->
  x / 2 ^ a / 2 ^ b = x / 2 ^ (a + b).
Proof.
  intros Ha Hb.
  pose proof (pow2_pos a Ha).
  pose proof (pow2_pos b Hb).
  rewrite Z.div_div by lia.
  rewrite <- pow2_split by lia.
  reflexivity.
Qed.

Lemma pow8_pos (m : nat) : 0 < 8 ^ Z.of_nat m.
Proof. apply Z.pow_pos_nonneg; [lia | apply Nat2Z.is_nonneg]. Qed.
