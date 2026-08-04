(** * Opaque equality between the two Vesta-base-field modulus names *)

From Stdlib Require Import ZArith.
Require Import Garden.Field.Field.
Require Import Garden.Prim63.Pasta.

Lemma PallasQ_modulus_eq :
  PallasQConfig.modulus_Z = Primes.pallas_q.
Proof. vm_compute. reflexivity. Qed.
