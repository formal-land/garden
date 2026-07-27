(** * Integer helpers shared by the forward lemmas

    The per-family forward lemmas identify a generator cell with a slice of a
    packed message, so they repeatedly need the same facts about powers of
    two and the Pallas prime.  Collecting them here keeps one statement per
    fact: in particular the two Pallas bounds are named apart, since the
    ladder needs the strict [2 <] form while the slice arguments need only
    positivity. *)

Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.micromega.Lia.
Require Import Garden.Field.Field.

Module OrchardForwardArith.
  Local Open Scope Z_scope.

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

  Lemma pallas_p_pos : 0 < Primes.pallas_p.
  Proof. unfold Primes.pallas_p, Primes.t_p; lia. Qed.

  Lemma pallas_p_gt_2 : 2 < Primes.pallas_p.
  Proof. unfold Primes.pallas_p, Primes.t_p; lia. Qed.
End OrchardForwardArith.
