(** * Ready-to-use refinement modules for the two Pasta fields *)

Require Export Garden.Prim63.PastaInstances.
Require Import Garden.Prim63.PastaCanonicalFacts.
Require Import Garden.Prim63.PastaDenoteFacts.
Require Import Garden.Prim63.PastaEqualityFacts.

(** Opaque, fully-specialized entry points for the Vesta base field.

    Applying a theorem through the refinement functor asks elaboration to
    normalize the complete five-word configuration.  These small wrappers pay
    that conversion once in this cached module; projective-curve consumers can
    then use an opaque constant with the exact [PallasQ] type. *)
Module PallasQFacts.
  Include PallasQCanonicalFacts.
  Include PallasQDenoteFacts.
  Include PallasQEqualityFacts.
End PallasQFacts.
