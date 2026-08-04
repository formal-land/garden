(** * Opaque conversion-denotation facts for the Vesta base field *)

From Stdlib Require Import ZArith.
Require Import Garden.Field.Field.
Require Import Garden.Prim63.Pasta.
Require Import Garden.Prim63.PastaInstances.
Require Import Garden.Prim63.PastaModulusFacts.

Local Open Scope Z_scope.

Module PallasQConversionDenoteFacts.
  Lemma to_Z_denote (a : PallasQ.t) :
    PallasQ.to_Z a = PallasQ.denote a.
  Proof. exact (PallasQRefinement.to_Z_denote a). Qed.

  Lemma from_Z_denote (z : Z) :
    PallasQ.denote (PallasQ.from_Z z) = z mod Primes.pallas_q.
  Proof.
    rewrite <- PallasQ_modulus_eq.
    exact (PallasQRefinement.from_Z_denote z).
  Qed.
End PallasQConversionDenoteFacts.
