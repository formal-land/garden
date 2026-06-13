Require Import Garden.Halo2.main.
Require Import Garden.Plonky3.M.

Global Open Scope Z_scope.

Definition square {p : Z} `{Prime p}
    (value : Z)
    : Z :=
  value *F value.

Definition ternary {p : Z} `{Prime p}
    (selector when_true when_false : Z)
    : Z :=
  selector *F when_true +F
    (UnOp.from 1 -F selector) *F when_false.

Fixpoint pow_nat {p : Z} `{Prime p}
    (value : Z)
    (power : nat)
    : Z :=
  match power with
  | O => UnOp.from 1
  | S power => pow_nat value power *F value
  end.

Module Point.
  Record t : Set := {
    x : Z;
    y : Z;
  }.

  Global Instance IsMapMod {p : Z} `{Prime p} : MapMod t := {
    map_mod point := {|
      x := UnOp.from point.(x);
      y := UnOp.from point.(y);
    |};
  }.
End Point.

Module Pair.
  Record t : Set := {
    left : Z;
    right : Z;
  }.

  Global Instance IsMapMod {p : Z} `{Prime p} : MapMod t := {
    map_mod pair := {|
      left := UnOp.from pair.(left);
      right := UnOp.from pair.(right);
    |};
  }.
End Pair.
