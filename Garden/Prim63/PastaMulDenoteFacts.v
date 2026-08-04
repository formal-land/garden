(** * Public multiplicative-denotation façade for the Vesta base field *)

Require Import Garden.Prim63.PastaMulOnlyDenoteFacts.
Require Import Garden.Prim63.PastaSquareDenoteFacts.

Module PallasQMulDenoteFacts.
  Include PallasQMulOnlyDenoteFacts.
  Include PallasQSquareDenoteFacts.
End PallasQMulDenoteFacts.
