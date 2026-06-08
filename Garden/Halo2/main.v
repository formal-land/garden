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

  Record map (source target : t) : Set := {
    selector : source.(Selector) -> target.(Selector);
    fixed : source.(Fixed) -> target.(Fixed);
    advice : source.(Advice) -> target.(Advice);
    instance_ : source.(Instance_) -> target.(Instance_);
  }.
  Arguments map : clear implicits.
  Arguments selector {_ _} _ _.
  Arguments fixed {_ _} _ _.
  Arguments advice {_ _} _ _.
  Arguments instance_ {_ _} _ _.
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

  Notation "➖ x" := (Negated x)
    (at level 35, right associativity).
  Notation "x ➕ y" := (Sum x y)
    (at level 50, left associativity).
  Notation "x ➖ y" := (Sum x (Negated y))
    (at level 50, left associativity).
  Notation "x ✖️ y" := (Product x y)
    (at level 40, left associativity).
  Notation "x ● y" := (Scaled x y)
    (at level 40, left associativity).

  Fixpoint map {source target : Columns.t}
      (column_map : Columns.map source target)
      (expression : t source) : t target :=
    match expression with
    | Constant value =>
        Constant value
    | Selector selector =>
        Selector (column_map.(Columns.selector) selector)
    | Fixed fixed rotation =>
        Fixed (column_map.(Columns.fixed) fixed) rotation
    | Advice advice rotation =>
        Advice (column_map.(Columns.advice) advice) rotation
    | Instance_ instance rotation =>
        Instance_ (column_map.(Columns.instance_) instance) rotation
    | Negated expression =>
        Negated (map column_map expression)
    | Sum lhs rhs =>
        Sum (map column_map lhs) (map column_map rhs)
    | Product lhs rhs =>
        Product (map column_map lhs) (map column_map rhs)
    | Scaled expression scale =>
        Scaled (map column_map expression) scale
    end.
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

  Fixpoint to_expression {columns : Columns.t}
      (constraint : t columns) : Expression.t columns :=
    match constraint with
    | Select selector constraint =>
        Expression.Product
          (Expression.Selector selector)
          (to_expression constraint)
    | Equal lhs rhs =>
        Expression.Sum lhs (Expression.Negated rhs)
    | EqualZeroToPrecise expression =>
        expression
    end.

  Definition map_to_equal_zero_to_precise {source target : Columns.t}
      (column_map : Columns.map source target)
      (constraint : t source) : t target :=
    EqualZeroToPrecise
      (Expression.map column_map (to_expression constraint)).
  Arguments to_expression {_} _ /.
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
  Arguments with_selector {_} _ _ /.

  Definition map {source target : Columns.t}
      (column_map : Columns.map source target)
      (constraints : t source) : t target :=
    List.map
      (fun constraint =>
        let '(name, constraint) := constraint in
        (name, Constraint.map_to_equal_zero_to_precise column_map constraint))
      constraints.
End Constraints.

Module Gate.
  Record t {columns : Columns.t} : Set := {
    name : string;
    constraints : Constraints.t columns;
  }.
  Arguments t : clear implicits.

  Definition map {source target : Columns.t}
      (column_map : Columns.map source target)
      (gate : t source) : t target := {|
    name := gate.(name);
    constraints := Constraints.map column_map gate.(constraints);
  |}.
End Gate.

Module LookupArgument.
  Record t {columns : Columns.t} : Set := {
    pairs : list (Expression.t columns * columns.(Columns.Fixed));
  }.
  Arguments t : clear implicits.

  Definition map {source target : Columns.t}
      (column_map : Columns.map source target)
      (lookup : t source) : t target := {|
    pairs :=
      List.map
        (fun '(expression, fixed) =>
          (Expression.map column_map expression,
            column_map.(Columns.fixed) fixed))
        lookup.(pairs);
  |}.
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

  Definition map {source target : Columns.t}
      (column_map : Columns.map source target)
      (system : t source) : t target := {|
    gates := List.map (Gate.map column_map) system.(gates);
    lookups := List.map (LookupArgument.map column_map) system.(lookups);
  |}.
End ConstraintSystem.
