(** * The compiled plonkish layer: cyclic domain, selector compression, σ.

    Halo2's keygen compiles the configured circuit into the plonkish system
    the verifier actually checks: rows live on a cyclic domain of size
    [2^k] with a reserved blinding tail, the boolean selector columns are
    packed into combination fixed columns and substituted out of the gates
    by indicator polynomials, and the [Copy] obligations are closed into an
    explicit permutation σ of the equality-enabled cell set.

    This file models that compilation step over the indexed constraint
    system of [serialize.v]:

    - [Domain]: rows in [[0, 2^k)], rotation as addition mod [n], the
      usable-row prefix and the [l_0]/[l_last]/[l_blind] row predicates;
    - [CompiledSystem]: gates as bare indexed expressions over
      {Fixed, Advice, Instance} queries (no [Expression.Selector] leaves),
      lookup arguments, the query tables, the permutation column list and
      the constants columns;
    - [Compile.compile]: the port of
      [halo2_proofs/src/plonk/circuit/compress_selectors.rs] ([process])
      and its caller [ConstraintSystem::compress_selectors]
      ([plonk/circuit.rs]) — degree-driven greedy packing, indicator
      polynomial substitution, non-simple selectors as plain 0/1 fixed
      columns;
    - [Sigma.sigma_of_copies]: the port of the permutation keygen
      ([plonk/permutation/keygen.rs], [Assembly::copy]) — cycle closure of
      the copy list by weighted union with an explicit cycle relabeling
      walk.

    No polynomials appear here: the domain is plain [Z] arithmetic and the
    compiled gates are the same deep-embedded expressions, so this layer
    sits strictly between the raw event grid ([realize/]) and the
    polynomial identities of the vanishing/permutation/lookup arguments. *)

Require Import Garden.Halo2.main.
Require Import Garden.Halo2.serialize.

Import ListNotations.
Global Open Scope Z_scope.

Module Plonkish.

(** ** List helpers *)

Definition enumerate {A : Set} (l : list A) : list (nat * A) :=
  List.combine (List.seq 0 (List.length l)) l.

Fixpoint list_set {A : Set} (l : list A) (i : nat) (v : A) : list A :=
  match l, i with
  | [], _ => []
  | _ :: l, O => v :: l
  | x :: l, S i => x :: list_set l i v
  end.

Definition list_sum (l : list nat) : nat :=
  List.fold_left Nat.add l O.

(** ** The cyclic domain

    [n = 2^k] rows.  The prover reserves the top [blinding_factors] rows
    for blinding plus one spare row between the usable prefix and the
    blinding tail; [l_last] marks that spare row (the first inactive row)
    and [l_blind] the blinding tail, mirroring the [l_0]/[l_last]/[l_blind]
    Lagrange selectors built by [plonk/keygen.rs].  Rotations wrap around
    the domain: a query at rotation [o] from row [r] reads row
    [(r + o) mod n]. *)

Module Domain.
  Record t : Set := {
    k : Z;
    blinding_factors : Z;
  }.

  Definition n (self : t) : Z := 2 ^ self.(k).

  (** Rows [0 .. usable_rows - 1] carry the circuit; row [usable_rows] is
      the spare ([l_last]) row; rows above it are blinding rows. *)
  Definition usable_rows (self : t) : Z :=
    n self - (self.(blinding_factors) + 1).

  Definition in_domain (self : t) (row : Z) : bool :=
    andb (0 <=? row) (row <? n self).

  Definition usable (self : t) (row : Z) : bool :=
    andb (0 <=? row) (row <? usable_rows self).

  (** Rotation as addition mod [n]. *)
  Definition rot (self : t) (row offset : Z) : Z :=
    (row + offset) mod n self.

  Definition l_0 (self : t) (row : Z) : bool :=
    row =? 0.

  Definition l_last (self : t) (row : Z) : bool :=
    row =? usable_rows self.

  Definition l_blind (self : t) (row : Z) : bool :=
    andb (usable_rows self <? row) (row <? n self).
End Domain.

(** ** Expression measures

    Ports of [Expression::degree] and [Expression::extract_simple_selector]
    ([plonk/circuit.rs]).  The extraction is total where Rust panics on two
    simple selectors in one expression: the merge keeps the left selector,
    which agrees with Rust on every input Rust accepts. *)

Fixpoint expression_degree {columns : Columns.t}
    (expression : Expression.t columns) : nat :=
  match expression with
  | Expression.Constant _ => O
  | Expression.Selector _ => 1%nat
  | Expression.Fixed _ _ => 1%nat
  | Expression.Advice _ _ => 1%nat
  | Expression.Instance_ _ _ => 1%nat
  | Expression.Negated expression => expression_degree expression
  | Expression.Sum lhs rhs =>
      Nat.max (expression_degree lhs) (expression_degree rhs)
  | Expression.Product lhs rhs =>
      (expression_degree lhs + expression_degree rhs)%nat
  | Expression.Scaled expression _ => expression_degree expression
  end.

Definition merge_selector {A : Set} (lhs rhs : option A) : option A :=
  match lhs with
  | Some a => Some a
  | None => rhs
  end.

Fixpoint extract_simple_selector {columns : Columns.t}
    (is_simple : columns.(Columns.Selector) -> bool)
    (expression : Expression.t columns)
    : option columns.(Columns.Selector) :=
  match expression with
  | Expression.Constant _ => None
  | Expression.Selector selector =>
      if is_simple selector then Some selector else None
  | Expression.Fixed _ _ => None
  | Expression.Advice _ _ => None
  | Expression.Instance_ _ _ => None
  | Expression.Negated expression => extract_simple_selector is_simple expression
  | Expression.Sum lhs rhs =>
      merge_selector
        (extract_simple_selector is_simple lhs)
        (extract_simple_selector is_simple rhs)
  | Expression.Product lhs rhs =>
      merge_selector
        (extract_simple_selector is_simple lhs)
        (extract_simple_selector is_simple rhs)
  | Expression.Scaled expression _ => extract_simple_selector is_simple expression
  end.

(** The flattened gate polynomials of a constraint system, in gate then
    constraint order — the expressions [ConstraintSystem::compress_selectors]
    iterates over. *)
Definition gate_polys {columns : Columns.t}
    (system : ConstraintSystem.t columns) : list (Expression.t columns) :=
  List.flat_map
    (fun gate =>
      List.map
        (fun named_constraint =>
          Configure.constraint_to_expression (snd named_constraint))
        gate.(Gate.constraints))
    system.(ConstraintSystem.gates).

(** ** System degree

    Port of [ConstraintSystem::degree] ([plonk/circuit.rs]): the maximum of
    the permutation argument's required degree (the constant 3, per
    [plonk/permutation.rs]), each lookup argument's required degree
    ([plonk/lookup.rs] — the model's table side is a bare column, whose
    query has degree 1), the gate polynomial degrees, and the configured
    minimum degree (default 1). *)

Definition lookup_required_degree {columns : Columns.t}
    (lookup : LookupArgument.t columns) : nat :=
  let input_degree :=
    List.fold_left
      (fun acc pair => Nat.max acc (expression_degree (fst pair)))
      lookup.(LookupArgument.pairs)
      1%nat in
  let table_degree := 1%nat in
  Nat.max 4 (2 + input_degree + table_degree).

Definition system_degree_with_minimum {columns : Columns.t}
    (system : ConstraintSystem.t columns)
    (minimum_degree : option nat) : nat :=
  let degree := 3%nat in
  let degree :=
    Nat.max degree
      (List.fold_left
        (fun acc lookup => Nat.max acc (lookup_required_degree lookup))
        system.(ConstraintSystem.lookups)
        1%nat) in
  let degree :=
    Nat.max degree
      (List.fold_left
        (fun acc poly => Nat.max acc (expression_degree poly))
        (gate_polys system)
        O) in
  Nat.max degree
    (match minimum_degree with
     | Some degree => degree
     | None => 1
     end).

(** Compatibility entry point for configure programs that do not carry the
    metadata trace. *)
Definition system_degree {columns : Columns.t}
    (system : ConstraintSystem.t columns) : nat :=
  system_degree_with_minimum system None.

(** ** Selector compression

    Port of [compress_selectors::process].  A selector is described by its
    column index, its per-row boolean activations, and the maximum degree
    of a gate polynomial from which it is extracted as a simple selector
    (0 for complex selectors and selectors outside every gate).  Fixed
    columns for the combinations are allocated sequentially from
    [first_new_column]: the combination at index [c] lands in fixed column
    [first_new_column + c], matching the [allocate_fixed_column] closure of
    [ConstraintSystem::compress_selectors]. *)

Module SelectorDescription.
  Record t : Set := {
    selector : Z;
    activations : list bool;
    max_degree : nat;
  }.
End SelectorDescription.

Module SelectorAssignment.
  Record t : Set := {
    selector : Z;
    combination_index : nat;
    expression : Expression.t Configure.indexed_columns;
  }.
End SelectorAssignment.

Module Compress.
  (** Two activation vectors are both on at some common row: the exclusion
      matrix entry of [process]. *)
  Definition rows_conflict (lhs rhs : list bool) : bool :=
    List.existsb (fun pair => andb (fst pair) (snd pair)) (List.combine lhs rhs).

  (** The indicator polynomial substituted for the selector assigned root
      [assigned_root] in the combination column queried by [query]:
      [query · ∏_{root ∈ [1, combination_len], root ≠ assigned_root}
      (root − query)], built by the same left-associated fold in increasing
      root order as [process].  The product bound is the number of selectors
      packed into the combination. *)
  Definition indicator_expression
      (query : Expression.t Configure.indexed_columns)
      (combination_len : nat)
      (assigned_root : Z)
      : Expression.t Configure.indexed_columns :=
    List.fold_left
      (fun expression root =>
        if root =? assigned_root then expression
        else
          Expression.Product
            expression
            (Expression.Sum (Expression.Constant root) (Expression.Negated query)))
      (List.map Z.of_nat (List.seq 1 combination_len))
      query.

  (** The values of a combination column: 0 on rows where every member
      selector is off, the member's assigned root (its 1-based position in
      the combination) where it is on.  Built by the same
      write-per-selector fold as [process]; members are row-disjoint, so
      the write order is immaterial. *)
  Definition apply_activation (root : Z) (activations : list bool)
      (values : list Z) : list Z :=
    List.map
      (fun (pair : bool * Z) => if fst pair then root else snd pair)
      (List.combine activations values).

  Definition combination_values (n_rows : nat)
      (combination : list SelectorDescription.t) : list Z :=
    snd
      (List.fold_left
        (fun state description =>
          let '(root, values) := state in
          (root + 1,
            apply_activation
              root
              description.(SelectorDescription.activations)
              values))
        combination
        (1, List.repeat 0 n_rows)).

  (** The inner candidate scan of the greedy packing: try to add each later
      selector [j] to the combination, skipping already-added and
      row-conflicting selectors, capping the combination by the degree
      budget, and stopping outright when the budget is exhausted.  Returns
      the final degree bound, the combination in join order, and the
      updated added flags. *)
  Fixpoint scan_candidates
      (candidates : list (nat * SelectorDescription.t))
      (max_degree : nat)
      (d : nat)
      (combination : list (nat * SelectorDescription.t))
      (added : list bool)
      : nat * list (nat * SelectorDescription.t) * list bool :=
    match candidates with
    | [] => (d, combination, added)
    | (j, description) :: candidates =>
        if (d + List.length combination =? max_degree)%nat then
          (d, combination, added)
        else if List.nth j added false then
          scan_candidates candidates max_degree d combination added
        else if
          List.existsb
            (fun member =>
              rows_conflict
                description.(SelectorDescription.activations)
                (snd member).(SelectorDescription.activations))
            combination
        then
          scan_candidates candidates max_degree d combination added
        else
          let new_d :=
            Nat.max d (description.(SelectorDescription.max_degree) - 1) in
          if (max_degree <? new_d + List.length combination + 1)%nat then
            scan_candidates candidates max_degree d combination added
          else
            scan_candidates
              candidates
              max_degree
              new_d
              (combination ++ [(j, description)])
              (list_set added j true)
    end.

  (** One packed combination: the fixed column at
      [first_new_column + combination_index], the member selectors
      substituted by their indicator polynomials with roots assigned in
      join order. *)
  Definition combination_assignments
      (first_new_column : Z)
      (combination_index : nat)
      (combination : list SelectorDescription.t)
      : list SelectorAssignment.t :=
    let query : Expression.t Configure.indexed_columns :=
      @Expression.Fixed
        Configure.indexed_columns
        (first_new_column + Z.of_nat combination_index)
        Rotation.cur in
    let combination_len := List.length combination in
    List.map
      (fun member =>
        let '(position, description) := member in
        {|
          SelectorAssignment.selector :=
            description.(SelectorDescription.selector);
          SelectorAssignment.combination_index := combination_index;
          SelectorAssignment.expression :=
            indicator_expression query combination_len (Z.of_nat (S position));
        |})
      (enumerate combination).

  (** The outer greedy loop over the simple selectors, in order, threading
      the added flags and the accumulated combinations and assignments. *)
  Fixpoint pack_simple
      (todo : list (nat * SelectorDescription.t))
      (max_degree : nat)
      (n_rows : nat)
      (first_new_column : Z)
      (added : list bool)
      (combinations : list (list Z))
      (assignments : list SelectorAssignment.t)
      : list (list Z) * list SelectorAssignment.t :=
    match todo with
    | [] => (combinations, assignments)
    | (i, description) :: todo =>
        if List.nth i added false then
          pack_simple
            todo max_degree n_rows first_new_column
            added combinations assignments
        else
          let added := list_set added i true in
          let d := (description.(SelectorDescription.max_degree) - 1)%nat in
          let '(_, combination, added) :=
            scan_candidates todo max_degree d [(i, description)] added in
          let combination_index := List.length combinations in
          let members := List.map snd combination in
          pack_simple
            todo max_degree n_rows first_new_column
            added
            (combinations ++ [combination_values n_rows members])
            (assignments
              ++ combination_assignments
                   first_new_column combination_index members)
    end.

  (** The full [process]: selectors of degree 0 (complex, or outside every
      gate) each get their own plain 0/1 fixed column, in selector order;
      the remaining simple selectors are packed greedily under the degree
      budget.  Returns the combination column values (in allocation order)
      and the per-selector assignments. *)
  Definition process
      (selectors : list SelectorDescription.t)
      (max_degree : nat)
      (first_new_column : Z)
      : list (list Z) * list SelectorAssignment.t :=
    match selectors with
    | [] => ([], [])
    | first :: _ =>
        let n_rows :=
          List.length first.(SelectorDescription.activations) in
        let retained :=
          List.filter
            (fun description =>
              (description.(SelectorDescription.max_degree) =? 0)%nat)
            selectors in
        let simple :=
          List.filter
            (fun description =>
              negb (description.(SelectorDescription.max_degree) =? 0)%nat)
            selectors in
        let retained_combinations :=
          List.map
            (fun description =>
              List.map
                (fun active : bool => if active then 1 else 0)
                description.(SelectorDescription.activations))
            retained in
        let retained_assignments :=
          List.map
            (fun indexed =>
              let '(combination_index, description) := indexed in
              {|
                SelectorAssignment.selector :=
                  description.(SelectorDescription.selector);
                SelectorAssignment.combination_index := combination_index;
                SelectorAssignment.expression :=
                  @Expression.Fixed
                    Configure.indexed_columns
                    (first_new_column + Z.of_nat combination_index)
                    Rotation.cur;
              |})
            (enumerate retained) in
        pack_simple
          (enumerate simple)
          max_degree
          n_rows
          first_new_column
          (List.repeat false (List.length simple))
          retained_combinations
          retained_assignments
    end.
End Compress.

(** ** The compiled system *)

(** Substitution of the per-selector assignment expressions into an
    expression: the [replace_selectors] rebuild of
    [ConstraintSystem::compress_selectors].  Selectors without an
    assignment are left in place, where they stay visible to
    [expression_selector_free]. *)
Fixpoint substitute_selectors
    (replacement : Z -> option (Expression.t Configure.indexed_columns))
    (expression : Expression.t Configure.indexed_columns)
    : Expression.t Configure.indexed_columns :=
  match expression with
  | Expression.Constant value => Expression.Constant value
  | Expression.Selector selector =>
      match replacement selector with
      | Some expression => expression
      | None => Expression.Selector selector
      end
  | Expression.Fixed column rotation => Expression.Fixed column rotation
  | Expression.Advice column rotation => Expression.Advice column rotation
  | Expression.Instance_ column rotation => Expression.Instance_ column rotation
  | Expression.Negated expression =>
      Expression.Negated (substitute_selectors replacement expression)
  | Expression.Sum lhs rhs =>
      Expression.Sum
        (substitute_selectors replacement lhs)
        (substitute_selectors replacement rhs)
  | Expression.Product lhs rhs =>
      Expression.Product
        (substitute_selectors replacement lhs)
        (substitute_selectors replacement rhs)
  | Expression.Scaled expression scale =>
      Expression.Scaled (substitute_selectors replacement expression) scale
  end.

(** No [Expression.Selector] leaf remains. *)
Fixpoint expression_selector_free {columns : Columns.t}
    (expression : Expression.t columns) : bool :=
  match expression with
  | Expression.Constant _ => true
  | Expression.Selector _ => false
  | Expression.Fixed _ _ => true
  | Expression.Advice _ _ => true
  | Expression.Instance_ _ _ => true
  | Expression.Negated expression => expression_selector_free expression
  | Expression.Sum lhs rhs =>
      andb (expression_selector_free lhs) (expression_selector_free rhs)
  | Expression.Product lhs rhs =>
      andb (expression_selector_free lhs) (expression_selector_free rhs)
  | Expression.Scaled expression _ => expression_selector_free expression
  end.

(** The query tables: the distinct (column, rotation offset) pairs read by
    the compiled system, one table per column kind. *)
Module Queries.
  Record t : Set := {
    advice : list (Z * Z);
    fixed : list (Z * Z);
    instance_ : list (Z * Z);
  }.

  Definition empty : t := {|
    advice := [];
    fixed := [];
    instance_ := [];
  |}.

  Definition query_eqb (lhs rhs : Z * Z) : bool :=
    andb (fst lhs =? fst rhs) (snd lhs =? snd rhs).

  Definition add (queries : list (Z * Z)) (query : Z * Z) : list (Z * Z) :=
    if List.existsb (query_eqb query) queries then queries
    else queries ++ [query].

  Definition add_advice (self : t) (query : Z * Z) : t := {|
    advice := add self.(advice) query;
    fixed := self.(fixed);
    instance_ := self.(instance_);
  |}.

  Definition add_fixed (self : t) (query : Z * Z) : t := {|
    advice := self.(advice);
    fixed := add self.(fixed) query;
    instance_ := self.(instance_);
  |}.

  Definition add_instance (self : t) (query : Z * Z) : t := {|
    advice := self.(advice);
    fixed := self.(fixed);
    instance_ := add self.(instance_) query;
  |}.

  Fixpoint collect_expression
      (expression : Expression.t Configure.indexed_columns)
      (self : t) : t :=
    match expression with
    | Expression.Constant _ => self
    | Expression.Selector _ => self
    | Expression.Fixed column rotation =>
        add_fixed self (column, rotation.(Rotation.offset))
    | Expression.Advice column rotation =>
        add_advice self (column, rotation.(Rotation.offset))
    | Expression.Instance_ column rotation =>
        add_instance self (column, rotation.(Rotation.offset))
    | Expression.Negated expression => collect_expression expression self
    | Expression.Sum lhs rhs =>
        collect_expression rhs (collect_expression lhs self)
    | Expression.Product lhs rhs =>
        collect_expression rhs (collect_expression lhs self)
    | Expression.Scaled expression _ => collect_expression expression self
    end.

  (** Every equality-enabled column is also queried at the current
      rotation ([enable_equality] registers the query in Rust). *)
  Definition add_permutation_column (self : t) (column : Raw.ColumnRef.t)
      : t :=
    match column.(Raw.ColumnRef.kind) with
    | Raw.ColumnKind.Advice =>
        add_advice self (column.(Raw.ColumnRef.index), 0)
    | Raw.ColumnKind.Fixed =>
        add_fixed self (column.(Raw.ColumnRef.index), 0)
    | Raw.ColumnKind.Instance_ =>
        add_instance self (column.(Raw.ColumnRef.index), 0)
    end.

  (** The number of distinct rotations at which [column] is queried. *)
  Definition column_query_count (queries : list (Z * Z)) (column : Z) : nat :=
    List.length (List.filter (fun query => fst query =? column) queries).

  Definition max_column_queries (queries : list (Z * Z)) : nat :=
    List.fold_left
      (fun acc query => Nat.max acc (column_query_count queries (fst query)))
      queries
      O.
End Queries.

Module CompiledSystem.
  (** The compiled plonkish system: bare indexed gate polynomials with the
      selectors substituted out, the lookup arguments with substituted
      input expressions, the query tables, and the permutation and
      constants data of the verifying key. *)
  Record t : Set := {
    gates : list (Expression.t Configure.indexed_columns);
    lookups : list (LookupArgument.t Configure.indexed_columns);
    advice_queries : list (Z * Z);
    fixed_queries : list (Z * Z);
    instance_queries : list (Z * Z);
    permutation_columns : list Raw.ColumnRef.t;
    constants : list Z;
    combination_columns : list Z;
    combination_assignments : list (list Z);
    selector_assignments : list SelectorAssignment.t;
  }.

  (** No gate polynomial or lookup input mentions a selector. *)
  Definition selector_free_b (self : t) : bool :=
    andb
      (List.forallb expression_selector_free self.(gates))
      (List.forallb
        (fun lookup =>
          List.forallb
            (fun pair => expression_selector_free (fst pair))
            lookup.(LookupArgument.pairs))
        self.(lookups)).

  (** Port of [ConstraintSystem::blinding_factors]: the maximum number of
      distinct rotations at which one advice column is queried (at least
      3), plus one multiopen evaluation, plus one spare. *)
  Definition blinding_factors (self : t) : Z :=
    Z.of_nat
      (Nat.max 3 (Queries.max_column_queries self.(advice_queries)) + 1 + 1).
End CompiledSystem.

(** ** The compiler *)

Module Compile.
  (** Per-selector compilation input: the boolean activation vector over
      the domain rows (recoverable from the [EnableSelector] events) and
      whether the selector is simple.  Complex selectors may appear in
      lookup arguments and are never packed; the flag mirrors
      [Selector::is_simple], which the constraint system itself does not
      record.  List position [i] describes selector index [i]. *)
  Module SelectorInfo.
    Record t : Set := {
      activations : list bool;
      simple : bool;
    }.
  End SelectorInfo.

  (** The activation vector of selector [s] over rows [[0, n_rows)], read
      off the serialized events. *)
  Definition selector_activations_of_events
      (events : list Raw.Event.t)
      (s : Z)
      (n_rows : nat)
      : list bool :=
    List.map
      (fun row =>
        List.existsb
          (fun event =>
            match event with
            | Raw.Event.EnableSelector selector row' _ =>
                andb (selector =? s) (row' =? Z.of_nat row)
            | _ => false
            end)
          events)
      (List.seq 0 n_rows).

  (** The maximum degree of a gate polynomial from which selector [s] is
      extracted as a simple selector — the [degrees] pass of
      [ConstraintSystem::compress_selectors]. *)
  Definition selector_max_degree
      (polys : list (Expression.t Configure.indexed_columns))
      (is_simple : Z -> bool)
      (s : Z)
      : nat :=
    List.fold_left
      (fun (acc : nat) (poly : Expression.t Configure.indexed_columns) =>
        match
          extract_simple_selector
            (columns := Configure.indexed_columns) is_simple poly
        with
        | Some s' =>
            if s' =? s then Nat.max acc (expression_degree poly) else acc
        | None => acc
        end)
      polys
      O.

  Definition selector_descriptions
      (system : ConstraintSystem.t Configure.indexed_columns)
      (infos : list SelectorInfo.t)
      : list SelectorDescription.t :=
    let is_simple := fun s =>
      List.nth
        (Z.to_nat s)
        (List.map SelectorInfo.simple infos)
        false in
    let polys := gate_polys system in
    List.map
      (fun indexed =>
        let '(i, info) := indexed in
        {|
          SelectorDescription.selector := Z.of_nat i;
          SelectorDescription.activations := info.(SelectorInfo.activations);
          SelectorDescription.max_degree :=
            selector_max_degree polys is_simple (Z.of_nat i);
        |})
      (enumerate infos).

  (** The selector-to-expression substitution read off a compiled
      output's per-selector assignments. *)
  Definition assignment_replacement
      (assignments : list SelectorAssignment.t)
      (s : Z)
      : option (Expression.t Configure.indexed_columns) :=
    match
      List.find
        (fun assignment =>
          assignment.(SelectorAssignment.selector) =? s)
        assignments
    with
    | Some assignment => Some assignment.(SelectorAssignment.expression)
    | None => None
    end.

  (** The compilation proper: compute the per-selector degrees, run the
      packing at the system degree, and substitute the assignment
      expressions into every gate polynomial and lookup input.  The
      combination columns extend the fixed columns starting at
      [num_fixed_columns]; the permutation column list and the constants
      columns are configure-time data the modeled [ConstraintSystem.t]
      does not carry, so they are passed through. *)
  Definition compile_with_minimum
      (system : ConstraintSystem.t Configure.indexed_columns)
      (infos : list SelectorInfo.t)
      (num_fixed_columns : Z)
      (permutation_columns : list Raw.ColumnRef.t)
      (constants : list Z)
      (minimum_degree : option nat)
      : CompiledSystem.t :=
    let descriptions := selector_descriptions system infos in
    let max_degree := system_degree_with_minimum system minimum_degree in
    let '(combinations, assignments) :=
      Compress.process descriptions max_degree num_fixed_columns in
    let replacement := assignment_replacement assignments in
    let gates :=
      List.map (substitute_selectors replacement) (gate_polys system) in
    let lookups :=
      List.map
        (fun lookup =>
          {|
            LookupArgument.pairs :=
              List.map
                (fun pair =>
                  (substitute_selectors replacement (fst pair), snd pair))
                lookup.(LookupArgument.pairs);
          |})
        system.(ConstraintSystem.lookups) in
    let queries :=
      List.fold_left
        (fun acc column => Queries.add_permutation_column acc column)
        permutation_columns
        (List.fold_left
          (fun acc lookup =>
            List.fold_left
              (fun acc pair => Queries.collect_expression (fst pair) acc)
              lookup.(LookupArgument.pairs)
              acc)
          lookups
          (List.fold_left
            (fun acc poly => Queries.collect_expression poly acc)
            gates
            Queries.empty)) in
    {|
      CompiledSystem.gates := gates;
      CompiledSystem.lookups := lookups;
      CompiledSystem.advice_queries := queries.(Queries.advice);
      CompiledSystem.fixed_queries := queries.(Queries.fixed);
      CompiledSystem.instance_queries := queries.(Queries.instance_);
      CompiledSystem.permutation_columns := permutation_columns;
      CompiledSystem.constants := constants;
      CompiledSystem.combination_columns :=
        List.map
          (fun c => num_fixed_columns + Z.of_nat c)
          (List.seq 0 (List.length combinations));
      CompiledSystem.combination_assignments := combinations;
      CompiledSystem.selector_assignments := assignments;
    |}.

  Definition compile
      (system : ConstraintSystem.t Configure.indexed_columns)
      (infos : list SelectorInfo.t)
      (num_fixed_columns : Z)
      (permutation_columns : list Raw.ColumnRef.t)
      (constants : list Z)
      : CompiledSystem.t :=
    compile_with_minimum system infos num_fixed_columns permutation_columns
      constants None.

  Module KeygenMetadata.
    (** Indexed configure metadata consumed by selector compression and by
        [PinnedConstraintSystem].  Query tables are in first-registration
        order, before compression allocates its combination columns. *)
    Record t : Set := {
      base_fixed_columns : Z;
      advice_queries : list (Z * Z);
      fixed_queries : list (Z * Z);
      instance_queries : list (Z * Z);
      permutation_columns : list Raw.ColumnRef.t;
      constants : list Z;
      minimum_degree : option nat;
    }.
  End KeygenMetadata.

  Definition add_combination_queries
      (queries : list (Z * Z)) (columns : list Z) : list (Z * Z) :=
    List.fold_left
      (fun queries column => Queries.add queries (column, 0))
      columns queries.

  (** Compile from the configure interpreter rather than reconstructing
      query sets from expression traversal.  This preserves Halo 2's
      keygen-order query indices; selector compression appends one current-
      rotation fixed query for each newly allocated combination column. *)
  Definition compile_from_metadata
      (system : ConstraintSystem.t Configure.indexed_columns)
      (infos : list SelectorInfo.t)
      (metadata : KeygenMetadata.t)
      : CompiledSystem.t :=
    let compiled :=
      compile_with_minimum system infos
        metadata.(KeygenMetadata.base_fixed_columns)
        metadata.(KeygenMetadata.permutation_columns)
        metadata.(KeygenMetadata.constants)
        metadata.(KeygenMetadata.minimum_degree) in
    {|
      CompiledSystem.gates := compiled.(CompiledSystem.gates);
      CompiledSystem.lookups := compiled.(CompiledSystem.lookups);
      CompiledSystem.advice_queries := metadata.(KeygenMetadata.advice_queries);
      CompiledSystem.fixed_queries :=
        add_combination_queries metadata.(KeygenMetadata.fixed_queries)
          compiled.(CompiledSystem.combination_columns);
      CompiledSystem.instance_queries :=
        metadata.(KeygenMetadata.instance_queries);
      CompiledSystem.permutation_columns :=
        metadata.(KeygenMetadata.permutation_columns);
      CompiledSystem.constants := metadata.(KeygenMetadata.constants);
      CompiledSystem.combination_columns :=
        compiled.(CompiledSystem.combination_columns);
      CompiledSystem.combination_assignments :=
        compiled.(CompiledSystem.combination_assignments);
      CompiledSystem.selector_assignments :=
        compiled.(CompiledSystem.selector_assignments);
    |}.
End Compile.

(** ** The permutation σ

    Port of [plonk/permutation/keygen.rs] ([Assembly]): cells are
    (column position, row) pairs over the permutation column list;
    [mapping] is the permutation whose orbits are the cycles built so far,
    [aux] names each cell's cycle representative, and [sizes] carries the
    cycle sizes at the representatives for the weighted union.  The cycle
    relabeling walk of [Assembly::copy] is fuel-bounded by the cell count,
    which every cycle length is at most. *)

Module Sigma.
  Definition cell : Set := (nat * nat)%type.

  Definition cell_eqb (lhs rhs : cell) : bool :=
    andb (fst lhs =? fst rhs)%nat (snd lhs =? snd rhs)%nat.

  Definition column_kind_eqb (lhs rhs : Raw.ColumnKind.t) : bool :=
    match lhs, rhs with
    | Raw.ColumnKind.Advice, Raw.ColumnKind.Advice => true
    | Raw.ColumnKind.Fixed, Raw.ColumnKind.Fixed => true
    | Raw.ColumnKind.Instance_, Raw.ColumnKind.Instance_ => true
    | _, _ => false
    end.

  Definition column_eqb (lhs rhs : Raw.ColumnRef.t) : bool :=
    andb
      (column_kind_eqb lhs.(Raw.ColumnRef.kind) rhs.(Raw.ColumnRef.kind))
      (lhs.(Raw.ColumnRef.index) =? rhs.(Raw.ColumnRef.index)).

  Fixpoint column_position
      (columns : list Raw.ColumnRef.t)
      (column : Raw.ColumnRef.t)
      : option nat :=
    match columns with
    | [] => None
    | head :: columns =>
        if column_eqb head column then Some O
        else option_map S (column_position columns column)
    end.

  Definition get2 {A : Set} (default : A) (matrix : list (list A))
      (c : cell) : A :=
    List.nth (snd c) (List.nth (fst c) matrix []) default.

  Definition set2 {A : Set} (matrix : list (list A)) (c : cell) (value : A)
      : list (list A) :=
    list_set matrix (fst c) (list_set (List.nth (fst c) matrix []) (snd c) value).

  Record t : Set := {
    columns : list Raw.ColumnRef.t;
    mapping : list (list cell);
    aux : list (list cell);
    sizes : list (list nat);
  }.

  (** Every cell in a 1-cycle: [mapping] and [aux] are the identity and
      every size is 1. *)
  Definition init (permutation_columns : list Raw.ColumnRef.t) (n_rows : nat)
      : t :=
    let identity :=
      List.map
        (fun i => List.map (fun j => (i, j)) (List.seq 0 n_rows))
        (List.seq 0 (List.length permutation_columns)) in
    {|
      columns := permutation_columns;
      mapping := identity;
      aux := identity;
      sizes :=
        List.repeat
          (List.repeat 1%nat n_rows)
          (List.length permutation_columns);
    |}.

  (** The do-while relabeling walk: set [aux] to [label] along the
      [mapping] orbit starting at [i], stopping on return to [start]. *)
  Fixpoint relabel_cycle
      (fuel : nat)
      (mapping : list (list cell))
      (aux : list (list cell))
      (i start label : cell)
      : list (list cell) :=
    match fuel with
    | O => aux
    | S fuel =>
        let aux := set2 aux i label in
        let next := get2 i mapping i in
        if cell_eqb next start then aux
        else relabel_cycle fuel mapping aux next start label
    end.

  Definition total_cells (self : t) : nat :=
    list_sum (List.map (@List.length cell) self.(mapping)).

  (** One [Assembly::copy]: resolve the columns in the permutation list,
      check row bounds, and if the two cells are in distinct cycles, merge
      the smaller cycle into the larger (relabel its representatives, add
      the sizes) and splice the orbits by swapping the two mapping
      entries. *)
  Definition copy (self : t) (left right : Raw.Cell.t) : option t :=
    match
      column_position self.(columns) left.(Raw.Cell.column),
      column_position self.(columns) right.(Raw.Cell.column)
    with
    | Some left_column, Some right_column =>
        let left_length :=
          List.length (List.nth left_column self.(mapping) []) in
        let right_length :=
          List.length (List.nth right_column self.(mapping) []) in
        if
          negb
            (andb
              (andb
                (0 <=? left.(Raw.Cell.row))
                (left.(Raw.Cell.row) <? Z.of_nat left_length))
              (andb
                (0 <=? right.(Raw.Cell.row))
                (right.(Raw.Cell.row) <? Z.of_nat right_length)))
        then None
        else
          let left_cell := (left_column, Z.to_nat left.(Raw.Cell.row)) in
          let right_cell := (right_column, Z.to_nat right.(Raw.Cell.row)) in
          let left_cycle := get2 left_cell self.(aux) left_cell in
          let right_cycle := get2 right_cell self.(aux) right_cell in
          if cell_eqb left_cycle right_cycle then Some self
          else
            let '(left_cycle, right_cycle) :=
              if
                (get2 O self.(sizes) left_cycle
                  <? get2 O self.(sizes) right_cycle)%nat
              then (right_cycle, left_cycle)
              else (left_cycle, right_cycle) in
            let sizes :=
              set2 self.(sizes) left_cycle
                (get2 O self.(sizes) left_cycle
                  + get2 O self.(sizes) right_cycle)%nat in
            let aux :=
              relabel_cycle
                (S (total_cells self))
                self.(mapping)
                self.(aux)
                right_cycle right_cycle left_cycle in
            let left_image := get2 left_cell self.(mapping) left_cell in
            let right_image := get2 right_cell self.(mapping) right_cell in
            let mapping := set2 self.(mapping) left_cell right_image in
            let mapping := set2 mapping right_cell left_image in
            Some {|
              columns := self.(columns);
              mapping := mapping;
              aux := aux;
              sizes := sizes;
            |}
    | _, _ => None
    end.

  (** The copy obligations of an event stream, in order. *)
  Definition copies_of_events (events : list Raw.Event.t)
      : list (Raw.Cell.t * Raw.Cell.t) :=
    List.flat_map
      (fun event =>
        match event with
        | Raw.Event.Copy left_cell right_cell => [(left_cell, right_cell)]
        | _ => []
        end)
      events.

  (** The cycle closure of a copy list: fold [copy] from the identity
      assembly.  [None] exactly when some copy names a column outside the
      permutation list or a row outside [[0, n_rows)]. *)
  Definition sigma_of_copies
      (permutation_columns : list Raw.ColumnRef.t)
      (n_rows : nat)
      (copies : list (Raw.Cell.t * Raw.Cell.t))
      : option t :=
    List.fold_left
      (fun state pair =>
        match state with
        | None => None
        | Some self => copy self (fst pair) (snd pair)
        end)
      copies
      (Some (init permutation_columns n_rows)).

  (** The permutation read off the closed assembly; cells outside the
      matrix are fixed points. *)
  Definition perm (self : t) (c : cell) : cell :=
    get2 c self.(mapping) c.
End Sigma.

End Plonkish.
