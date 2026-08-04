(** * Public arithmetic-denotation façade for the Vesta base field *)

Require Import Garden.Prim63.PastaAddSubDenoteFacts.
Require Import Garden.Prim63.PastaMulDenoteFacts.

Module PallasQArithmeticDenoteFacts.
  Include PallasQAddSubDenoteFacts.
  Include PallasQMulDenoteFacts.
End PallasQArithmeticDenoteFacts.
