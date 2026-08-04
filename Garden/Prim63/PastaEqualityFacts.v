(** * Opaque equality facts for the Vesta base field *)

Require Import Garden.Prim63.Pasta.
Require Import Garden.Prim63.PastaInstances.

Module PallasQEqualityFacts.
  Lemma equal_denote_iff (a b : PallasQ.t) :
    PallasQ.canonical a -> PallasQ.canonical b ->
    (PallasQ.equal a b = true <-> PallasQ.denote a = PallasQ.denote b).
  Proof. exact (PallasQRefinement.equal_denote_iff a b). Qed.

  Lemma equal_denote_false_iff (a b : PallasQ.t) :
    PallasQ.canonical a -> PallasQ.canonical b ->
    (PallasQ.equal a b = false <-> PallasQ.denote a <> PallasQ.denote b).
  Proof.
    intros Ha Hb. pose proof (equal_denote_iff a b Ha Hb) as Heq.
    split.
    - intros Hab Hden. apply (proj2 Heq) in Hden.
      rewrite Hab in Hden. discriminate.
    - intro Hneq. destruct (PallasQ.equal a b) eqn:Hab; [|reflexivity].
      exfalso. apply Hneq. apply (proj1 Heq). reflexivity.
  Qed.
End PallasQEqualityFacts.
