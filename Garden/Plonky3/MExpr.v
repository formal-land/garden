Require Import Garden.Plonky3.M.

Module Field.
  Record t : Set := {
    value : Z;
  }.
End Field.

Module Var.
  Record t : Set := {
    index : Z;
  }.
End Var.

Module Expr.
  Inductive t : Set :=
  | Var (var : Var.t)
  | IsFirstRow
  | IsLastRow
  | IsTransition
  | Constant (value : Field.t)
  | Add (x y : t)
  | Sub (x y : t)
  | Neg (x : t)
  | Mul (x y : t).

  Definition constant (value : Z) : t :=
    Constant {| Field.value := value |}.

  Definition ZERO : t := constant 0.

  Definition ONE : t := constant 1.

  Definition not (e : t) : t :=
    Sub e ONE.

  Definition assert_zero (e : t) : t :=
    e.

  Definition assert_one (e : t) : t :=
    Sub e ONE.

  Definition assert_bool (e : t) : t :=
    Mul e (Sub e ONE).
End Expr.

Module Builder.
  Record t : Set := {
    constraints : list Expr.t;
  }.

  Definition assert_zero (builder : t) (e : Expr.t) : t :=
    {| constraints := Expr.assert_zero e :: builder.(constraints) |}.

  Definition assert_one (builder : t) (e : Expr.t) : t :=
    assert_zero builder (Expr.assert_one e).

  Definition assert_bool (builder : t) (e : Expr.t) : t :=
    assert_zero builder (Expr.assert_bool e).
End Builder.
