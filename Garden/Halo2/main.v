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

  Definition prev : t := {|
    offset := -1;
  |}.

  Definition next : t := {|
    offset := 1;
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

Module Constraint.
  Inductive t (columns : Columns.t) : Set :=
  | Select
      (selector : columns.(Columns.Selector))
      (constraint : t columns)
  | Equal
      (left : Expression.t columns)
      (right : Expression.t columns)
  | EqualZeroToPrecise
      (expression : Expression.t columns).
  Arguments Select {_}.
  Arguments Equal {_}.
  Arguments EqualZeroToPrecise {_}.
End Constraint.

Module Constraints.
  Definition t (columns : Columns.t) : Set :=
    list (option string * Constraint.t columns).

  Definition with_selector {columns : Columns.t}
      (selector : columns.(Columns.Selector))
      (constraints : t columns) : t columns :=
    List.map
      (fun constraint =>
        let '(name, constraint) := constraint in
        (name, Constraint.Select selector constraint))
      constraints.
End Constraints.

Module Gate.
  Record t {columns : Columns.t} : Set := {
    name : string;
    constraints : Constraints.t columns;
  }.
  Arguments t : clear implicits.
End Gate.

Module LookupArgument.
  Record t {columns : Columns.t} : Set := {
    pairs : list (Expression.t columns * columns.(Columns.Fixed));
  }.
  Arguments t : clear implicits.
End LookupArgument.

Module ConstraintSystem.
  Record t {columns : Columns.t} : Set := {
    gates : list (Gate.t columns);
    lookups : list (LookupArgument.t columns);
  }.
  Arguments t : clear implicits.

  Definition empty {columns : Columns.t} : t columns := {|
    gates := [];
    lookups := [];
  |}.

  Definition concat {columns : Columns.t}
      (left right : t columns) : t columns := {|
    gates := left.(gates) ++ right.(gates);
    lookups := left.(lookups) ++ right.(lookups);
  |}.

  Definition create_gate {columns : Columns.t}
      (self : t columns)
      (gate : Gate.t columns) : t columns := {|
    gates := self.(gates) ++ [gate];
    lookups := self.(lookups);
  |}.

  Definition create_lookup {columns : Columns.t}
      (self : t columns)
      (lookup : LookupArgument.t columns) : t columns := {|
    gates := self.(gates);
    lookups := self.(lookups) ++ [lookup];
  |}.
End ConstraintSystem.
