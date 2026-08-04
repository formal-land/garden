(** * Opaque multiplication-denotation fact for the Vesta base field *)

Require Import Garden.Field.Field.
Require Import Garden.Prim63.Pasta.
Require Import Garden.Prim63.PastaInstances.
Require Import Garden.Prim63.PastaModulusFacts.

Local Open Scope Z_scope.

Module PallasQMulOnlyDenoteFacts.
  Lemma mul_denote (a b : PallasQ.t) :
    PallasQ.canonical b ->
    PallasQ.denote (PallasQ.mul a b) =
      (PallasQ.denote a * PallasQ.denote b) mod Primes.pallas_q.
  Proof.
    intro Hb. rewrite <- PallasQ_modulus_eq.
    exact (PallasQRefinement.mul_denote a b Hb).
  Qed.
End PallasQMulOnlyDenoteFacts.
