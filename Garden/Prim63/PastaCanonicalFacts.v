(** * Opaque canonical-form facts for the Vesta base field *)

From Stdlib Require Import ZArith.
Require Import Garden.Prim63.Pasta.
Require Import Garden.Prim63.PastaInstances.

Module PallasQCanonicalFacts.
  Lemma from_Z_canonical (z : Z) :
    PallasQ.canonical (PallasQ.from_Z z).
  Proof. exact (PallasQRefinement.from_Z_canonical z). Qed.

  Lemma zero_canonical : PallasQ.canonical PallasQ.zero.
  Proof. exact PallasQRefinement.zero_canonical. Qed.

  Lemma one_canonical : PallasQ.canonical PallasQ.one.
  Proof. exact PallasQRefinement.one_canonical. Qed.

  Lemma add_canonical (a b : PallasQ.t) :
    PallasQ.canonical a -> PallasQ.canonical b ->
    PallasQ.canonical (PallasQ.add a b).
  Proof. exact (PallasQRefinement.add_canonical a b). Qed.

  Lemma sub_canonical (a b : PallasQ.t) :
    PallasQ.canonical a -> PallasQ.canonical b ->
    PallasQ.canonical (PallasQ.sub a b).
  Proof. exact (PallasQRefinement.sub_canonical a b). Qed.

  Lemma mul_canonical (a b : PallasQ.t) :
    PallasQ.canonical b -> PallasQ.canonical (PallasQ.mul a b).
  Proof. exact (PallasQRefinement.mul_canonical a b). Qed.

  Lemma square_canonical (a : PallasQ.t) :
    PallasQ.canonical a -> PallasQ.canonical (PallasQ.square a).
  Proof.
    unfold PallasQ.square. apply mul_canonical.
  Qed.
End PallasQCanonicalFacts.
