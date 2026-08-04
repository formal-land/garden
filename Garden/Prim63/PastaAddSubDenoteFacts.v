(** * Opaque additive denotation facts for the Vesta base field *)

Require Import Garden.Field.Field.
Require Import Garden.Prim63.Pasta.
Require Import Garden.Prim63.PastaInstances.
Require Import Garden.Prim63.PastaModulusFacts.

Local Open Scope Z_scope.

Module PallasQAddSubDenoteFacts.
  Lemma add_denote (a b : PallasQ.t) :
    PallasQ.canonical a -> PallasQ.canonical b ->
    PallasQ.denote (PallasQ.add a b) =
      (PallasQ.denote a + PallasQ.denote b) mod Primes.pallas_q.
  Proof.
    intros Ha Hb. rewrite <- PallasQ_modulus_eq.
    exact (PallasQRefinement.add_denote a b Ha Hb).
  Qed.

  Lemma sub_denote (a b : PallasQ.t) :
    PallasQ.canonical a -> PallasQ.canonical b ->
    PallasQ.denote (PallasQ.sub a b) =
      (PallasQ.denote a - PallasQ.denote b) mod Primes.pallas_q.
  Proof.
    intros Ha Hb. rewrite <- PallasQ_modulus_eq.
    exact (PallasQRefinement.sub_denote a b Ha Hb).
  Qed.
End PallasQAddSubDenoteFacts.
