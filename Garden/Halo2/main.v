Require Export Stdlib.Lists.List.
Require Export Stdlib.Strings.PrimString.
Require Export Stdlib.ZArith.ZArith.

Import ListNotations.
Export PStringNotations.
Global Open Scope pstring_scope.
Global Open Scope Z_scope.

Module Columns.
  Record t : Type := {
    Selector : Set;
    Fixed : Set;
    Advice : Set;
    Instance_ : Set;
  }.
End Columns.

Module Rotation.
  Record t : Set := {
    offset : Z;
  }.

  Definition cur : t := {|
    offset := 0;
  |}.
End Rotation.

Module Expression.
  Inductive t (columns : Columns.t) : Set :=
  | Constant (value : Z)
  | Selector (selector : columns.(Columns.Selector))
  | Fixed
      (fixed : columns.(Columns.Fixed))
      (rotation : Rotation.t)
  | Advice
      (advice : columns.(Columns.Advice))
      (rotation : Rotation.t)
  | Instance_
      (instance : columns.(Columns.Instance_))
      (rotation : Rotation.t)
  | Negated (expr : t columns)
  | Sum
      (left : t columns)
      (right : t columns)
  | Product
      (left : t columns)
      (right : t columns)
  | Scaled
      (expr : t columns)
      (scale : Z).
  Arguments Constant {_}.
  Arguments Selector {_}.
  Arguments Fixed {_}.
  Arguments Advice {_}.
  Arguments Instance_ {_}.
  Arguments Negated {_}.
  Arguments Sum {_}.
  Arguments Product {_}.
  Arguments Scaled {_}.

  Notation "-E x" := (Negated x)
    (at level 35, right associativity).
  Notation "x +E y" := (Sum x y)
    (at level 50, left associativity).
  Notation "x -E y" := (Sum x (Negated y))
    (at level 50, left associativity).
  Notation "x *E y" := (Product x y)
    (at level 40, left associativity).
  Notation "x *Z y" := (Scaled x y)
    (at level 40, left associativity).
End Expression.
Export (notations) Expression.

Module Constraints.
  Definition t (columns : Columns.t) : Set :=
    list (option string * Expression.t columns).

  Definition with_selector {columns : Columns.t}
      (selector : columns.(Columns.Selector))
      (constraints : t columns) : t columns :=
    List.map
      (fun constraint =>
        let '(name, expression) := constraint in
        (name, Expression.Selector selector *E expression))
      constraints.
End Constraints.

Module Gate.
  Record t (columns : Columns.t) : Set := {
    name : string;
    constraints : Constraints.t columns;
  }.
End Gate.

Module ConstraintSystem.
  Record t (columns : Columns.t) : Set := {
    gates : list (Gate.t columns);
  }.

  Definition empty {columns : Columns.t} : t columns := {|
    gates := [];
  |}.

  Definition concat {columns : Columns.t}
      (left right : t columns) : t columns := {|
    gates := left.(gates columns) ++ right.(gates columns);
  |}.

  Definition create_gate {columns : Columns.t}
      (self : t columns)
      (gate : Gate.t columns) : t columns := {|
    gates := self.(gates columns) ++ [gate];
  |}.
End ConstraintSystem.
