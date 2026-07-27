(** * Pinned-vk parity certificate for the compiled Orchard action circuit.

    Machine-checked comparison of [Plonkish.Compile.compile] applied to the
    model's own [orchard_indexed_system] against the pinned compiled
    description of [compiled/pinned.v] (transcribed from the deployed
    verifying key).  Each certificate is a single [vm_compute] conversion,
    closed with [vm_cast_no_check].

    Certified components:

    - the compiled gate polynomials: all 193 match the pinned dump exactly —
      including the selector-indicator factors, so the full 56-selector ->
      combination-column assignment of the deployed keygen is pinned
      wherever a selector occurs (packed selectors through their gate
      indicators; the retained [QLookup]/[QRunning] columns through the
      lookup inputs below);
    - the gate count (193), the combination-column count (15, so 29 fixed
      columns post-compression), coverage of all 56 selectors by the
      assignment, and gate selector-freeness;
    - the query tables (25 advice / 29 fixed / 1 instance), as set equality
      plus length — the model collects queries in gate order, the deployed
      keygen in configure order;
    - the three lookup arguments, input and table expressions pairwise;
    - the constants column ([Fixed 3]), derived from the floor planner's
      constants tail;
    - the equality-enabled columns actually copied are all among the pinned
      permutation column list.

    Comparison is by expression fingerprint (below): the top-level product
    chain flattened into factors, each factor serialized preorder.  The
    flattening absorbs the product re-association between the model's
    [constraint_to_expression] and the deployed gate builder (two gates
    differ this way); every other node is compared exactly, including
    rotations and canonical field constants. *)

Require Import Stdlib.ZArith.ZArith.
Require Import Garden.Field.Field.
Require Import Garden.Halo2.main.
Require Import Garden.Halo2.serialize.
Require Import Garden.Halo2.plonkish.main.
Require Import Garden.Orchard.circuit_operational.
Require Import Garden.Orchard.compiled.pinned.

Import ListNotations.
Import Plonkish.
Local Open Scope Z_scope.

Module OrchardCompiledCheck.

(** ** The model's compiled Orchard system

    Per-selector activation vectors are read off the [EnableSelector] events
    of the serialized stream, over the [2048] domain rows.  The complex
    selectors — [Selector::is_simple] is configure-time data the modeled
    [ConstraintSystem.t] does not carry — are [QLookup] (2) and [QRunning]
    (3) ([halo2_gadgets/src/utilities/lookup_range_check.rs], the
    [complex_selector] allocations) and the two Sinsemilla instances'
    [q_sinsemilla1] (25, 29) ([halo2_gadgets/src/sinsemilla/chip.rs]); all
    other selectors are simple.  The combination columns extend the [14]
    pre-compression fixed columns. *)

Definition enable_pairs : list (Z * Z) :=
  List.flat_map
    (fun e =>
      match e with
      | Raw.Event.EnableSelector s r _ => [(s, r)]
      | _ => []
      end)
    orchard_events.

Definition rows_of (s : Z) : list Z :=
  List.map snd (List.filter (fun p => fst p =? s) enable_pairs).

Definition activation_of (s : Z) : list bool :=
  let rs := rows_of s in
  List.map
    (fun row => List.existsb (Z.eqb row) rs)
    (List.map Z.of_nat (List.seq 0 2048)).

Definition complex_selectors : list Z := [2; 3; 25; 29].

Definition orchard_infos : list Compile.SelectorInfo.t :=
  List.map
    (fun s =>
      {|
        Compile.SelectorInfo.activations := activation_of (Z.of_nat s);
        Compile.SelectorInfo.simple :=
          negb (List.existsb (Z.eqb (Z.of_nat s)) complex_selectors);
      |})
    (List.seq 0 56).

(** The permutation column list and the constants column are configure-time
    data the modeled [ConstraintSystem.t] does not carry; they are passed
    through from the pinned description (which makes the pass-through fields
    of [compiled] unusable as parity evidence — the stream-derived
    cross-checks below cover them) and consulted only for the query
    tables. *)
Definition compiled : CompiledSystem.t :=
  Compile.compile orchard_indexed_system orchard_infos 14
    OrchardCompiledPinned.permutation_columns
    OrchardCompiledPinned.constants.

(** ** Expression fingerprints

    Preorder serialization with tags [Sum 1], [Product 2], [Negated 3],
    [Scaled 4] (scalar inlined after the tag), and arity-fixed leaves
    [Advice 10], [Fixed 20], [Instance 50] (column index and rotation offset
    inlined), [Constant 30] (canonical residue inlined); every tag has a
    fixed arity, so the token stream determines the tree.  [gate_fp]
    flattens the top-level product chain and concatenates the factor
    fingerprints. *)

Definition fp_p : Z := Primes.pallas_p.

Fixpoint fpc (e : Expression.t Configure.indexed_columns) : list Z :=
  match e with
  | Expression.Constant z => [30; z mod fp_p]
  | Expression.Selector s => [99; s]
  | Expression.Fixed c r => [20; c; r.(Rotation.offset)]
  | Expression.Advice c r => [10; c; r.(Rotation.offset)]
  | Expression.Instance_ c r => [50; c; r.(Rotation.offset)]
  | Expression.Negated x => 3 :: fpc x
  | Expression.Scaled x z => 4 :: (z mod fp_p) :: fpc x
  | Expression.Sum a b => 1 :: fpc a ++ fpc b
  | Expression.Product a b => 2 :: fpc a ++ fpc b
  end.

Fixpoint factors (e : Expression.t Configure.indexed_columns)
    : list (Expression.t Configure.indexed_columns) :=
  match e with
  | Expression.Product a b => factors a ++ factors b
  | _ => [e]
  end.

Definition gate_fp (e : Expression.t Configure.indexed_columns) : list Z :=
  List.concat (List.map fpc (factors e)).

(** ** Boolean list equality *)

Fixpoint zlist_eqb (a b : list Z) : bool :=
  match a, b with
  | [], [] => true
  | x :: a, y :: b => andb (x =? y) (zlist_eqb a b)
  | _, _ => false
  end.

Fixpoint zll_eqb (a b : list (list Z)) : bool :=
  match a, b with
  | [], [] => true
  | x :: a, y :: b => andb (zlist_eqb x y) (zll_eqb a b)
  | _, _ => false
  end.

Fixpoint zlll_eqb (a b : list (list (list Z))) : bool :=
  match a, b with
  | [], [] => true
  | x :: a, y :: b => andb (zll_eqb x y) (zlll_eqb a b)
  | _, _ => false
  end.

(** ** Query-table comparison

    Both sides are duplicate-free ([Queries.add] deduplicates; the deployed
    query tables index distinct queries), so mutual inclusion plus equal
    length is equality up to order. *)

Definition query_subset (a b : list (Z * Z)) : bool :=
  List.forallb (fun q => List.existsb (Queries.query_eqb q) b) a.

Definition query_set_eqb (a b : list (Z * Z)) : bool :=
  andb
    (andb (query_subset a b) (query_subset b a))
    (Nat.eqb (List.length a) (List.length b)).

(** ** The lookup table columns

    The model's lookup-table namespace ([TableIdx], [TableX], [TableY] as
    indexed columns 0, 1, 2) corresponds to the fixed columns the deployed
    keygen allocates for the table columns; the correspondence is the
    identity on indices, verified below against the pinned table
    expressions.  Each table column is queried at the current rotation
    inside its lookup argument. *)

Definition table_fixed_column (c : Z) : Z := c.

Definition model_lookup_table_fps : list (list (list Z)) :=
  List.map
    (fun lk : LookupArgument.t Configure.indexed_columns =>
      List.map
        (fun pair =>
          fpc
            (@Expression.Fixed
              Configure.indexed_columns
              (table_fixed_column (snd pair))
              Rotation.cur))
        lk.(LookupArgument.pairs))
    compiled.(CompiledSystem.lookups).

(** The model's fixed queries extended with the lookup table columns, which
    the deployed keygen also queries (the table expressions above) while the
    model keeps them out of [Queries.collect_expression]'s reach on the
    table side of each pair. *)
Definition model_fixed_queries : list (Z * Z) :=
  List.fold_left
    (fun acc (lk : LookupArgument.t Configure.indexed_columns) =>
      List.fold_left
        (fun acc pair =>
          Queries.add acc (table_fixed_column (snd pair), 0))
        lk.(LookupArgument.pairs)
        acc)
    compiled.(CompiledSystem.lookups)
    compiled.(CompiledSystem.fixed_queries).

(** ** Derived permutation / constants data of the serialized stream *)

Definition kind_code (k : Raw.ColumnKind.t) : Z :=
  match k with
  | Raw.ColumnKind.Advice => 0
  | Raw.ColumnKind.Fixed => 1
  | Raw.ColumnKind.Instance_ => 2
  end.

Definition colref_code (c : Raw.ColumnRef.t) : Z * Z :=
  (kind_code c.(Raw.ColumnRef.kind), c.(Raw.ColumnRef.index)).

Definition pair_eqb (a b : Z * Z) : bool :=
  andb (fst a =? fst b) (snd a =? snd b).

Definition add_uniq (acc : list (Z * Z)) (a : Z * Z) : list (Z * Z) :=
  if List.existsb (pair_eqb a) acc then acc else acc ++ [a].

(** The distinct columns referenced by the [Copy] obligations of the stream:
    every column carrying an equality copy is permutation-enabled. *)
Definition copy_columns : list (Z * Z) :=
  List.fold_left
    (fun acc e =>
      match e with
      | Raw.Event.Copy l r =>
          add_uniq
            (add_uniq acc (colref_code l.(Raw.Cell.column)))
            (colref_code r.(Raw.Cell.column))
      | _ => acc
      end)
    orchard_events [].

(** The distinct fixed columns written by the floor planner's constants tail:
    the constants columns. *)
Definition add_uniq1 (acc : list Z) (a : Z) : list Z :=
  if List.existsb (Z.eqb a) acc then acc else acc ++ [a].

Definition constants_columns : list Z :=
  List.fold_left
    (fun acc e =>
      match e with
      | Raw.Event.AssignFixed col _ _ _ => add_uniq1 acc col
      | _ => acc
      end)
    orchard_constants_events [].

Definition pinned_permutation_codes : list (Z * Z) :=
  List.map colref_code OrchardCompiledPinned.permutation_columns.

(** ** The certificates *)

(** The 193 compiled gate polynomials match the pinned dump exactly, up to
    top-level product re-association: indicator factors, rotations and
    constants included.  This pins the selector compression — grouping,
    combination-column numbering and assigned indicator values — to the
    deployed keygen for every selector that guards a gate. *)
Lemma gate_polynomials_match :
  zll_eqb
    (List.map gate_fp compiled.(CompiledSystem.gates))
    OrchardCompiledPinned.gate_fps
  = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(** 193 compiled gates. *)
Lemma gate_count_match :
  Nat.eqb
    (List.length compiled.(CompiledSystem.gates))
    OrchardCompiledPinned.num_gates
  = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(** 15 combination columns, i.e. [14 + 15 = 29] fixed columns
    post-compression. *)
Lemma combination_count_match :
  andb
    (Nat.eqb
      (List.length compiled.(CompiledSystem.combination_columns))
      OrchardCompiledPinned.num_combinations)
    (OrchardCompiledPinned.base_fixed_columns
      + Z.of_nat (List.length compiled.(CompiledSystem.combination_columns))
      =? OrchardCompiledPinned.num_fixed_columns)
  = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(** Every one of the 56 selectors receives a compression assignment. *)
Lemma selector_assignments_cover :
  List.forallb
    (fun s =>
      List.existsb
        (fun a => a.(SelectorAssignment.selector) =? Z.of_nat s)
        compiled.(CompiledSystem.selector_assignments))
    (List.seq 0 56)
  = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(** No compiled gate polynomial or lookup input mentions a selector. *)
Lemma compiled_selector_free :
  CompiledSystem.selector_free_b compiled = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(** The query tables match: 25 advice, 29 fixed (with the three lookup table
    columns), 1 instance. *)
Lemma advice_queries_match :
  query_set_eqb
    compiled.(CompiledSystem.advice_queries)
    OrchardCompiledPinned.advice_queries
  = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma fixed_queries_match :
  query_set_eqb model_fixed_queries OrchardCompiledPinned.fixed_queries
  = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma instance_queries_match :
  query_set_eqb
    compiled.(CompiledSystem.instance_queries)
    OrchardCompiledPinned.instance_queries
  = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(** The three lookup arguments match pairwise: the compiled input
    expressions (with the retained [QLookup]/[QRunning] fixed columns 14 and
    15 substituted in) and the table columns. *)
Lemma lookup_inputs_match :
  zlll_eqb
    (List.map
      (fun lk : LookupArgument.t Configure.indexed_columns =>
        List.map
          (fun pair => gate_fp (fst pair))
          lk.(LookupArgument.pairs))
      compiled.(CompiledSystem.lookups))
    OrchardCompiledPinned.lookup_input_fps
  = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma lookup_tables_match :
  zlll_eqb model_lookup_table_fps OrchardCompiledPinned.lookup_table_fps
  = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(** The constants column derived from the constants tail is [Fixed 3]. *)
Lemma constants_column_match :
  zlist_eqb constants_columns OrchardCompiledPinned.constants = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(** Every column carrying an equality copy is in the pinned permutation
    list.  Inclusion, not equality: fixed columns 8, 9, 10 are
    equality-enabled but never copied by the synthesis stream, so the full
    15-column list is configure-time pinned data. *)
Lemma copy_columns_in_permutation :
  List.forallb
    (fun c => List.existsb (pair_eqb c) pinned_permutation_codes)
    copy_columns
  = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

End OrchardCompiledCheck.
