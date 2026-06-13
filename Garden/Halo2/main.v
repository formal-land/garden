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
    Lookup : Set;
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
  | Boolean
      (expression : Expression.t columns)
  | Range
      (expression : Expression.t columns)
      (range : nat)
  | Either
      (left : t columns)
      (right : t columns)
  | EqualZeroToPrecise
      (expression : Expression.t columns).
  Arguments Select {_}.
  Arguments Equal {_}.
  Arguments Boolean {_}.
  Arguments Range {_}.
  Arguments Either {_}.
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
  Arguments with_selector {_} _ _ /.
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
    pairs : list (Expression.t columns * columns.(Columns.Lookup));
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

Module Monad.
  Class C (M : Set -> Set) : Set := {
    ret : forall {A : Set}, A -> M A;
    bind : forall {A B : Set}, M A -> (A -> M B) -> M B;
  }.
End Monad.

Arguments Monad.ret {M} {_} {A} _.
Arguments Monad.bind {M} {_} {A B} _ _.

Notation "'return🞵' x" :=
  (Monad.ret x)
  (at level 100).

Notation "'let🞵' x ':=' a 'in' b" :=
  (Monad.bind a (fun x => b))
  (at level 200, x name, a at level 100, b at level 200).

Notation "'let🞵' ' x ':=' a 'in' b" :=
  (Monad.bind a (fun x => b))
  (at level 200, x pattern, a at level 100, b at level 200).

Notation "'do🞵' a 'in' b" :=
  (Monad.bind a (fun _ : unit => b))
  (at level 200, a at level 100, b at level 200).

Module 𝓒.
  (** Free syntax tree for Halo2 configure-time operations.  The
      interpreter threads the immutable [ConstraintSystem.t], while proofs can
      later give these operations relational semantics. *)
  Inductive t (columns : Columns.t) : Set -> Set :=
  | Ret {A : Set} (value : A) : t columns A
  | Bind {A B : Set}
      (first : t columns A)
      (second : A -> t columns B) : t columns B
  | CreateGate
      (gate : Gate.t columns) : t columns unit
  | CreateLookup
      (lookup : LookupArgument.t columns) : t columns unit.
  Arguments Ret {_ _}.
  Arguments Bind {_ _ _}.
  Arguments CreateGate {_}.
  Arguments CreateLookup {_}.

  Fixpoint run {columns : Columns.t} {A : Set}
      (program : t columns A)
      (meta : ConstraintSystem.t columns)
      : A * ConstraintSystem.t columns :=
    match program with
    | Ret value => (value, meta)
    | Bind first second =>
        let '(value, meta) := run first meta in
        run (second value) meta
    | CreateGate gate =>
        (tt, ConstraintSystem.create_gate meta gate)
    | CreateLookup lookup =>
        (tt, ConstraintSystem.create_lookup meta lookup)
    end.

  Definition run_unit {columns : Columns.t}
      (program : t columns unit)
      (meta : ConstraintSystem.t columns)
      : ConstraintSystem.t columns :=
    snd (run program meta).
End 𝓒.

Definition 𝓒 := 𝓒.t.

Global Instance ConfigureIsMonad {columns : Columns.t}
    : Monad.C (𝓒.t columns) := {|
  Monad.ret := @𝓒.Ret columns;
  Monad.bind := @𝓒.Bind columns;
|}.
