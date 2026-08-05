(** * Opaque square-denotation fact for the Vesta base field *)

Require Import Garden.Field.Field.
Require Import Garden.Prim63.Pasta.
Require Import Garden.Prim63.PastaInstances.
Require Import Garden.Prim63.PastaModulusFacts.

Local Open Scope Z_scope.

Module PallasQSquareDenoteFacts.
  Lemma square_denote (a : PallasQ.t) :
    PallasQ.canonical a ->
    PallasQ.denote (PallasQ.square a) =
      (PallasQ.denote a * PallasQ.denote a) mod Primes.pallas_q.
  Proof.
    intro Ha. rewrite <- PallasQ_modulus_eq.
    exact (PallasQRefinement.square_denote a Ha).
  Qed.
End PallasQSquareDenoteFacts.
