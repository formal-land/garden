Require Garden.Orchard.circuit.gadget.add_chip.
Require Import Garden.Field.Field.
Require Import Garden.Plonky3.M.

Global Open Scope Z_scope.

Module Addition.
  Record t : Set := {
    c : Z;
  }.

  Definition output {p : Z} `{Prime p}
      (a b : Z)
      : t := {|
    c := a +F b;
  |}.
End Addition.
