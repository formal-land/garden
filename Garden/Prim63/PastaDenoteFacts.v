(** * Public denotation-fact façade for the Vesta base field *)

Require Import Garden.Prim63.PastaArithmeticDenoteFacts.
Require Import Garden.Prim63.PastaConversionDenoteFacts.

Module PallasQDenoteFacts.
  Include PallasQArithmeticDenoteFacts.
  Include PallasQConversionDenoteFacts.
End PallasQDenoteFacts.
