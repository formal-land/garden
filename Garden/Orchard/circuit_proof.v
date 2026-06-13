Require Garden.Orchard.circuit.
Require Import Garden.Plonky3.M.

Global Open Scope Z_scope.

Module OrchardCircuitChecks.
  Record t : Set := {
    v_old : Z;
  }.

  Definition output {p : Z} `{Prime p}
      (v_new magnitude sign : Z)
      : t := {|
    v_old := v_new +F magnitude *F sign;
  |}.
End OrchardCircuitChecks.
