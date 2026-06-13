Require Import Garden.Halo2.Gadgets.Utilities_proof.
Require Garden.Halo2.Gadgets.Utilities.CondSwap.
Require Import Garden.Plonky3.M.

Global Open Scope Z_scope.

Module CondSwap.
  Record t : Set := {
    a_swapped : Z;
    b_swapped : Z;
  }.

  Definition output {p : Z} `{Prime p}
      (a b swap : Z)
      : t := {|
    a_swapped := Garden.Halo2.Gadgets.Utilities_proof.ternary swap b a;
    b_swapped := Garden.Halo2.Gadgets.Utilities_proof.ternary swap a b;
  |}.
End CondSwap.
