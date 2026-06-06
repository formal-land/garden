Require Import Garden.Halo2.main.

Import ListNotations.
Global Open Scope Z_scope.

Definition square {columns : Columns.t}
    (value : Expression.t columns)
    : Expression.t columns :=
  value *E value.

Definition range_check {columns : Columns.t}
    (word : Expression.t columns)
    (range : nat)
    : Expression.t columns :=
  List.fold_left
    (fun acc i => acc *E (Expression.Constant (Z.of_nat i) -E word))
    (List.seq 1 (Nat.pred range))
    word.

Definition bool_check {columns : Columns.t}
    (value : Expression.t columns)
    : Expression.t columns :=
  range_check value 2.

Definition ternary {columns : Columns.t}
    (a b c : Expression.t columns)
    : Expression.t columns :=
  (a *E b) +E ((Expression.Constant 1 -E a) *E c).

Fixpoint pow_expr {columns : Columns.t}
    (value : Expression.t columns)
    (power : nat)
    : Expression.t columns :=
  match power with
  | O => Expression.Constant 1
  | S power => pow_expr value power *E value
  end.
