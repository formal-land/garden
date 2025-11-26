Require Import Garden.Plonky3.M.
Require Import Garden.Brevis.primitives.consts.

Module Word.
  (** We use a type synonym rather than a container, as this is simpler *)
  Definition t := Array.t Z WORD_SIZE.

  Global Instance IsMapMod {p} `{Prime p} : MapMod t := {
    map_mod x := M.map_mod x;
  }.

  Global Instance IsGenerate : MGenerate.C t :=
    _.
End Word.
