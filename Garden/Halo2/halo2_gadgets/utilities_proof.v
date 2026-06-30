Require Import Garden.Halo2.main.
Require Import Garden.Field.Field.
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
