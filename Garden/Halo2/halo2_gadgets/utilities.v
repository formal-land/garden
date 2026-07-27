Require Import Garden.Halo2.main.

Import ListNotations.
Global Open Scope Z_scope.

Definition square {columns : Columns.t}
    (value : Expression.t columns)
    : Expression.t columns :=
  value ✖️ value.

Definition range_check {columns : Columns.t}
    (word : Expression.t columns)
    (range : nat)
    : Expression.t columns :=
  List.fold_left
    (fun acc i => acc ✖️ (Expression.Constant (Z.of_nat i) ➖ word))
    (List.seq 1 (Nat.pred range))
    word.

Definition bool_check {columns : Columns.t}
    (value : Expression.t columns)
    : Expression.t columns :=
  range_check value 2.

Definition ternary {columns : Columns.t}
    (a b c : Expression.t columns)
    : Expression.t columns :=
  (a ✖️ b) ➕ ((Expression.Constant 1 ➖ a) ✖️ c).

Fixpoint pow_expr {columns : Columns.t}
    (value : Expression.t columns)
    (power : nat)
    : Expression.t columns :=
  match power with
  | O => Expression.Constant 1
  | S power => pow_expr value power ✖️ value
  end.
