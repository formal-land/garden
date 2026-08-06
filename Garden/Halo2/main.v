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
  (** A zero-product disjunction whose enclosing [Select] retains the exact
      left-associated polynomial tree [(selector * left) * right]. *)
  | EitherZeroToPrecise
      (left : Expression.t columns)
      (right : Expression.t columns)
  | EqualZeroToPrecise
      (expression : Expression.t columns).
  Arguments Select {_}.
  Arguments Equal {_}.
  Arguments Boolean {_}.
  Arguments Range {_}.
  Arguments Either {_}.
  Arguments EitherZeroToPrecise {_}.
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

(** Configure-time metadata that affects Halo2 key generation without changing
    the gate and lookup relation.  Operations retain typed circuit columns;
    [IndexMap.t] gives them the numeric identities used by Halo2's pinned
    constraint system. *)
Module Metadata.
  Module SelectorKind.
    Inductive t : Set :=
    | Simple
    | Complex.

    Definition is_simple (kind : t) : bool :=
      match kind with
      | Simple => true
      | Complex => false
      end.
  End SelectorKind.

  Module IndexedColumn.
    Inductive Kind : Set :=
    | Advice
    | Fixed
    | Instance_.

    Record t : Set := {
      kind : Kind;
      index : Z;
    }.

    Definition eqb (lhs rhs : t) : bool :=
      andb
        (match lhs.(kind), rhs.(kind) with
         | Advice, Advice | Fixed, Fixed | Instance_, Instance_ => true
         | _, _ => false
         end)
        (lhs.(index) =? rhs.(index)).
  End IndexedColumn.

  Module IndexMap.
    Record t (columns : Columns.t) : Set := {
      selector : columns.(Columns.Selector) -> Z;
      fixed : columns.(Columns.Fixed) -> Z;
      lookup : columns.(Columns.Lookup) -> Z;
      advice : columns.(Columns.Advice) -> Z;
      instance_ : columns.(Columns.Instance_) -> Z;
    }.
    Arguments selector {_} _ _.
    Arguments fixed {_} _ _.
    Arguments lookup {_} _ _.
    Arguments advice {_} _ _.
    Arguments instance_ {_} _ _.
  End IndexMap.

  Module Operation.
    Inductive t (columns : Columns.t) : Set :=
    | AllocateAdvice (column : columns.(Columns.Advice))
    | AllocateFixed (column : columns.(Columns.Fixed))
    | AllocateLookupTable (column : columns.(Columns.Lookup))
    | AllocateInstance (column : columns.(Columns.Instance_))
    | AllocateSelector
        (selector : columns.(Columns.Selector))
        (kind : SelectorKind.t)
    | QueryAdvice
        (column : columns.(Columns.Advice))
        (rotation : Rotation.t)
    | QueryFixed (column : columns.(Columns.Fixed))
    | QueryLookup (column : columns.(Columns.Lookup))
    | QueryInstance
        (column : columns.(Columns.Instance_))
        (rotation : Rotation.t)
    | EnableEqualityAdvice (column : columns.(Columns.Advice))
    | EnableEqualityFixed (column : columns.(Columns.Fixed))
    | EnableEqualityInstance (column : columns.(Columns.Instance_))
    | EnableConstant (column : columns.(Columns.Fixed))
    | SetMinimumDegree (degree : nat).
    Arguments AllocateAdvice {_}.
    Arguments AllocateFixed {_}.
    Arguments AllocateLookupTable {_}.
    Arguments AllocateInstance {_}.
    Arguments AllocateSelector {_}.
    Arguments QueryAdvice {_}.
    Arguments QueryFixed {_}.
    Arguments QueryLookup {_}.
    Arguments QueryInstance {_}.
    Arguments EnableEqualityAdvice {_}.
    Arguments EnableEqualityFixed {_}.
    Arguments EnableEqualityInstance {_}.
    Arguments EnableConstant {_}.
    Arguments SetMinimumDegree {_}.

    Definition allocate_simple_selector {columns : Columns.t}
        (selector : columns.(Columns.Selector)) : t columns :=
      AllocateSelector selector SelectorKind.Simple.

    Definition allocate_complex_selector {columns : Columns.t}
        (selector : columns.(Columns.Selector)) : t columns :=
      AllocateSelector selector SelectorKind.Complex.
  End Operation.

  Module Counts.
    Record t : Set := {
      fixed : Z;
      advice : Z;
      instance_ : Z;
      selectors : Z;
    }.

    Definition empty : t := {|
      fixed := 0;
      advice := 0;
      instance_ := 0;
      selectors := 0;
    |}.
  End Counts.

  Module Queries.
    Definition query := (Z * Z)%type.

    Record t : Set := {
      advice : list query;
      fixed : list query;
      instance_ : list query;
    }.

    Definition empty : t := {|
      advice := [];
      fixed := [];
      instance_ := [];
    |}.

    Definition eqb (lhs rhs : query) : bool :=
      andb (fst lhs =? fst rhs) (snd lhs =? snd rhs).

    Definition add (entry : query) (queries : list query) : list query :=
      if List.existsb (eqb entry) queries
      then queries
      else queries ++ [entry].

    Definition add_advice (self : t) (entry : query) : t := {|
      advice := add entry self.(advice);
      fixed := self.(fixed);
      instance_ := self.(instance_);
    |}.

    Definition add_fixed (self : t) (entry : query) : t := {|
      advice := self.(advice);
      fixed := add entry self.(fixed);
      instance_ := self.(instance_);
    |}.

    Definition add_instance (self : t) (entry : query) : t := {|
      advice := self.(advice);
      fixed := self.(fixed);
      instance_ := add entry self.(instance_);
    |}.
  End Queries.

  Module State.
    Record t : Set := {
      counts : Counts.t;
      selector_types : list bool;
      lookup_columns : list Z;
      queries : Queries.t;
      permutation_columns : list IndexedColumn.t;
      constants : list Z;
      minimum_degree : option nat;
      valid : bool;
    }.

    Definition empty : t := {|
      counts := Counts.empty;
      selector_types := [];
      lookup_columns := [];
      queries := Queries.empty;
      permutation_columns := [];
      constants := [];
      minimum_degree := None;
      valid := true;
    |}.

    Definition next
        (self : t)
        (counts : Counts.t)
        (selector_types : list bool)
        (lookup_columns : list Z)
        (queries : Queries.t)
        (permutation_columns : list IndexedColumn.t)
        (constants : list Z)
        (minimum_degree : option nat)
        (operation_valid : bool) : t := {|
      counts := counts;
      selector_types := selector_types;
      lookup_columns := lookup_columns;
      queries := queries;
      permutation_columns := permutation_columns;
      constants := constants;
      minimum_degree := minimum_degree;
      valid := andb self.(valid) operation_valid;
    |}.

    Definition allocated (count index : Z) : bool :=
      andb (0 <=? index) (index <? count).

    Definition contains_Z (value : Z) (values : list Z) : bool :=
      List.existsb (Z.eqb value) values.

    Definition contains_column
        (column : IndexedColumn.t)
        (columns : list IndexedColumn.t) : bool :=
      List.existsb (IndexedColumn.eqb column) columns.

    Definition column_allocated (self : t)
        (column : IndexedColumn.t) : bool :=
      match column.(IndexedColumn.kind) with
      | IndexedColumn.Advice =>
          allocated self.(counts).(Counts.advice) column.(IndexedColumn.index)
      | IndexedColumn.Fixed =>
          allocated self.(counts).(Counts.fixed) column.(IndexedColumn.index)
      | IndexedColumn.Instance_ =>
          allocated self.(counts).(Counts.instance_) column.(IndexedColumn.index)
      end.

    Definition enable_equality (self : t)
        (column : IndexedColumn.t) : t :=
      let query := (column.(IndexedColumn.index), 0) in
      let queries :=
        match column.(IndexedColumn.kind) with
        | IndexedColumn.Advice => Queries.add_advice self.(queries) query
        | IndexedColumn.Fixed => Queries.add_fixed self.(queries) query
        | IndexedColumn.Instance_ => Queries.add_instance self.(queries) query
        end in
      let permutation_columns :=
        if contains_column column self.(permutation_columns)
        then self.(permutation_columns)
        else self.(permutation_columns) ++ [column] in
      next self
        self.(counts)
        self.(selector_types)
        self.(lookup_columns)
        queries
        permutation_columns
        self.(constants)
        self.(minimum_degree)
        (column_allocated self column).

    Definition enable_constant (self : t) (column : Z) : t :=
      if contains_Z column self.(constants)
      then
        next self
          self.(counts)
          self.(selector_types)
          self.(lookup_columns)
          self.(queries)
          self.(permutation_columns)
          self.(constants)
          self.(minimum_degree)
          (allocated self.(counts).(Counts.fixed) column)
      else
        enable_equality
          (next self
            self.(counts)
            self.(selector_types)
            self.(lookup_columns)
            self.(queries)
            self.(permutation_columns)
            (self.(constants) ++ [column])
            self.(minimum_degree)
            (allocated self.(counts).(Counts.fixed) column))
          {| IndexedColumn.kind := IndexedColumn.Fixed;
             IndexedColumn.index := column |}.
  End State.

  Definition step {columns : Columns.t}
      (indices : IndexMap.t columns)
      (self : State.t)
      (operation : Operation.t columns) : State.t :=
    match operation with
    | Operation.AllocateAdvice column =>
        let index := indices.(IndexMap.advice) column in
        State.next self
          {| Counts.fixed := self.(State.counts).(Counts.fixed);
             Counts.advice := self.(State.counts).(Counts.advice) + 1;
             Counts.instance_ := self.(State.counts).(Counts.instance_);
             Counts.selectors := self.(State.counts).(Counts.selectors) |}
          self.(State.selector_types)
          self.(State.lookup_columns)
          self.(State.queries)
          self.(State.permutation_columns)
          self.(State.constants)
          self.(State.minimum_degree)
          (index =? self.(State.counts).(Counts.advice))
    | Operation.AllocateFixed column =>
        let index := indices.(IndexMap.fixed) column in
        State.next self
          {| Counts.fixed := self.(State.counts).(Counts.fixed) + 1;
             Counts.advice := self.(State.counts).(Counts.advice);
             Counts.instance_ := self.(State.counts).(Counts.instance_);
             Counts.selectors := self.(State.counts).(Counts.selectors) |}
          self.(State.selector_types)
          self.(State.lookup_columns)
          self.(State.queries)
          self.(State.permutation_columns)
          self.(State.constants)
          self.(State.minimum_degree)
          (index =? self.(State.counts).(Counts.fixed))
    | Operation.AllocateLookupTable column =>
        let index := indices.(IndexMap.lookup) column in
        State.next self
          {| Counts.fixed := self.(State.counts).(Counts.fixed) + 1;
             Counts.advice := self.(State.counts).(Counts.advice);
             Counts.instance_ := self.(State.counts).(Counts.instance_);
             Counts.selectors := self.(State.counts).(Counts.selectors) |}
          self.(State.selector_types)
          (self.(State.lookup_columns) ++ [index])
          self.(State.queries)
          self.(State.permutation_columns)
          self.(State.constants)
          self.(State.minimum_degree)
          (index =? self.(State.counts).(Counts.fixed))
    | Operation.AllocateInstance column =>
        let index := indices.(IndexMap.instance_) column in
        State.next self
          {| Counts.fixed := self.(State.counts).(Counts.fixed);
             Counts.advice := self.(State.counts).(Counts.advice);
             Counts.instance_ := self.(State.counts).(Counts.instance_) + 1;
             Counts.selectors := self.(State.counts).(Counts.selectors) |}
          self.(State.selector_types)
          self.(State.lookup_columns)
          self.(State.queries)
          self.(State.permutation_columns)
          self.(State.constants)
          self.(State.minimum_degree)
          (index =? self.(State.counts).(Counts.instance_))
    | Operation.AllocateSelector selector kind =>
        let index := indices.(IndexMap.selector) selector in
        State.next self
          {| Counts.fixed := self.(State.counts).(Counts.fixed);
             Counts.advice := self.(State.counts).(Counts.advice);
             Counts.instance_ := self.(State.counts).(Counts.instance_);
             Counts.selectors := self.(State.counts).(Counts.selectors) + 1 |}
          (self.(State.selector_types) ++ [SelectorKind.is_simple kind])
          self.(State.lookup_columns)
          self.(State.queries)
          self.(State.permutation_columns)
          self.(State.constants)
          self.(State.minimum_degree)
          (index =? self.(State.counts).(Counts.selectors))
    | Operation.QueryAdvice column rotation =>
        let index := indices.(IndexMap.advice) column in
        State.next self
          self.(State.counts)
          self.(State.selector_types)
          self.(State.lookup_columns)
          (Queries.add_advice self.(State.queries)
            (index, rotation.(Rotation.offset)))
          self.(State.permutation_columns)
          self.(State.constants)
          self.(State.minimum_degree)
          (State.allocated self.(State.counts).(Counts.advice) index)
    | Operation.QueryFixed column =>
        let index := indices.(IndexMap.fixed) column in
        State.next self
          self.(State.counts)
          self.(State.selector_types)
          self.(State.lookup_columns)
          (Queries.add_fixed self.(State.queries) (index, 0))
          self.(State.permutation_columns)
          self.(State.constants)
          self.(State.minimum_degree)
          (State.allocated self.(State.counts).(Counts.fixed) index)
    | Operation.QueryLookup column =>
        let index := indices.(IndexMap.lookup) column in
        State.next self
          self.(State.counts)
          self.(State.selector_types)
          self.(State.lookup_columns)
          (Queries.add_fixed self.(State.queries) (index, 0))
          self.(State.permutation_columns)
          self.(State.constants)
          self.(State.minimum_degree)
          (State.contains_Z index self.(State.lookup_columns))
    | Operation.QueryInstance column rotation =>
        let index := indices.(IndexMap.instance_) column in
        State.next self
          self.(State.counts)
          self.(State.selector_types)
          self.(State.lookup_columns)
          (Queries.add_instance self.(State.queries)
            (index, rotation.(Rotation.offset)))
          self.(State.permutation_columns)
          self.(State.constants)
          self.(State.minimum_degree)
          (State.allocated self.(State.counts).(Counts.instance_) index)
    | Operation.EnableEqualityAdvice column =>
        State.enable_equality self
          {| IndexedColumn.kind := IndexedColumn.Advice;
             IndexedColumn.index := indices.(IndexMap.advice) column |}
    | Operation.EnableEqualityFixed column =>
        State.enable_equality self
          {| IndexedColumn.kind := IndexedColumn.Fixed;
             IndexedColumn.index := indices.(IndexMap.fixed) column |}
    | Operation.EnableEqualityInstance column =>
        State.enable_equality self
          {| IndexedColumn.kind := IndexedColumn.Instance_;
             IndexedColumn.index := indices.(IndexMap.instance_) column |}
    | Operation.EnableConstant column =>
        State.enable_constant self (indices.(IndexMap.fixed) column)
    | Operation.SetMinimumDegree degree =>
        State.next self
          self.(State.counts)
          self.(State.selector_types)
          self.(State.lookup_columns)
          self.(State.queries)
          self.(State.permutation_columns)
          self.(State.constants)
          (Some degree)
          true
    end.

  Definition run {columns : Columns.t}
      (indices : IndexMap.t columns)
      (operations : list (Operation.t columns))
      (initial : State.t) : State.t :=
    List.fold_left (step indices) operations initial.
End Metadata.

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
      (lookup : LookupArgument.t columns) : t columns unit
  | Metadata
      (operations : list (Metadata.Operation.t columns)) : t columns unit.
  Arguments Ret {_ _}.
  Arguments Bind {_ _ _}.
  Arguments CreateGate {_}.
  Arguments CreateLookup {_}.
  Arguments Metadata {_}.

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
    | Metadata _ => (tt, meta)
    end.

  Fixpoint run_metadata {columns : Columns.t} {A : Set}
      (indices : Metadata.IndexMap.t columns)
      (program : t columns A)
      (state : Metadata.State.t)
      : A * Metadata.State.t :=
    match program with
    | Ret value => (value, state)
    | Bind first second =>
        let '(value, state) := run_metadata indices first state in
        run_metadata indices (second value) state
    | CreateGate _ => (tt, state)
    | CreateLookup _ => (tt, state)
    | Metadata operations =>
        (tt, Garden.Halo2.main.Metadata.run indices operations state)
    end.

  Definition run_unit {columns : Columns.t}
      (program : t columns unit)
      (meta : ConstraintSystem.t columns)
      : ConstraintSystem.t columns :=
    snd (run program meta).

  Definition run_metadata_unit {columns : Columns.t}
      (indices : Metadata.IndexMap.t columns)
      (program : t columns unit)
      (state : Metadata.State.t) : Metadata.State.t :=
    snd (run_metadata indices program state).
End 𝓒.

Definition 𝓒 := 𝓒.t.

Global Instance ConfigureIsMonad {columns : Columns.t}
    : Monad.C (𝓒.t columns) := {|
  Monad.ret := @𝓒.Ret columns;
  Monad.bind := @𝓒.Bind columns;
|}.
