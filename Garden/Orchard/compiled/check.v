(** * Deployed-vk parity certificate for the compiled Orchard action circuit.

    Machine-checked comparison of
    [Plonkish.Compile.compile_from_metadata] applied to the model's own
    [orchard_indexed_system] and formal configure metadata against the
    deployed comparison targets in [compiled/pinned.v].  Each closed
    computational certificate uses VM conversion through
    [vm_cast_no_check].

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
    - the query tables (25 advice / 29 fixed / 1 instance), in exact keygen
      order derived from the formal configure metadata;
    - the three lookup arguments, input and table expressions pairwise;
    - the constants column ([Fixed 3]), derived from the floor planner's
      constants tail;
    - the complete ordered equality-enabled column list, plus the independent
      check that every column actually copied by synthesis belongs to it.

    The compact polynomial comparison uses an association-insensitive
    top-level product fingerprint.  The exact expression tree is checked
    separately: [vk/print.v] prints the derived compiled AST directly and T1
    compares its complete Debug representation byte-for-byte with the
    deployed dump. *)

Require Import Stdlib.ZArith.ZArith.
Require Import Garden.Field.Field.
Require Import Garden.Halo2.main.
Require Import Garden.Halo2.serialize.
Require Import Garden.Halo2.plonkish.main.
Require Import Garden.Orchard.circuit_operational.
Require Import Garden.Orchard.compiled.configuration.
Require Import Garden.Orchard.compiled.pinned.

Import ListNotations.
Import Plonkish.
Local Open Scope Z_scope.

Module OrchardCompiledCheck.

(** ** The model's compiled Orchard system

    Per-selector activation vectors are read off the [EnableSelector] events
    of the serialized stream over the [2048] domain rows.  Allocation counts,
    selector kinds, query order, equality columns, constants, and minimum
    degree are interpreted from the metadata events in the same formal
    configure program. *)

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

Definition orchard_infos : list Compile.SelectorInfo.t :=
  List.map
    (fun indexed =>
      let '(s, simple) := indexed in
      {|
        Compile.SelectorInfo.activations := activation_of (Z.of_nat s);
        Compile.SelectorInfo.simple := simple;
      |})
    (enumerate OrchardConfigure.selector_types).

Definition keygen_metadata : Compile.KeygenMetadata.t := {|
  Compile.KeygenMetadata.base_fixed_columns :=
    OrchardConfigure.base_fixed_columns;
  Compile.KeygenMetadata.advice_queries := OrchardConfigure.advice_queries;
  Compile.KeygenMetadata.fixed_queries := OrchardConfigure.fixed_queries;
  Compile.KeygenMetadata.instance_queries := OrchardConfigure.instance_queries;
  Compile.KeygenMetadata.permutation_columns :=
    OrchardConfigure.permutation_columns;
  Compile.KeygenMetadata.constants := OrchardConfigure.constants;
  Compile.KeygenMetadata.minimum_degree := OrchardConfigure.minimum_degree;
|}.

Definition compiled : CompiledSystem.t :=
  Compile.compile_from_metadata orchard_indexed_system orchard_infos
    keygen_metadata.

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

(** ** The lookup table columns

    The fixed column backing each typed lookup table is read from the shared
    lookup/fixed allocator in the configure metadata. *)

Definition table_fixed_column : Z -> Z := OrchardConfigure.lookup_fixed_column.

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

Definition derived_permutation_codes : list (Z * Z) :=
  List.map colref_code OrchardConfigure.permutation_columns.

(** Small certified cache of selector-combination column indices.  Keeping
    these indices materialized lets the VK printer resolve every fixed query
    without replaying the 2,048-row compression computation per expression
    leaf. *)
Definition combination_columns_cache : list Z :=
  [14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28].

(** ** The certificates *)

(** The 193 compiled gate polynomials match the deployed flattened-factor
    fingerprints: indicator factors, rotations and constants included.  This
    pins the selector compression — grouping, combination-column numbering
    and assigned indicator values — to the deployed keygen for every selector
    that guards a gate.  Exact tree association is checked by T1. *)
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

(** The configure interpreter derives the four pre-compression counts. *)
Lemma configure_counts_match :
  OrchardConfigure.base_fixed_columns =
      OrchardCompiledPinned.base_fixed_columns /\
  OrchardConfigure.num_advice_columns =
      OrchardCompiledPinned.num_advice_columns /\
  OrchardConfigure.num_instance_columns =
      OrchardCompiledPinned.num_instance_columns /\
  OrchardConfigure.num_selectors = OrchardCompiledPinned.num_selectors.
Proof. vm_compute. repeat split; reflexivity. Qed.

(** 15 combination columns, so the derived pre-compression fixed count plus
    the compression output is the deployed post-compression count 29. *)
Lemma combination_count_match :
  andb
    (Nat.eqb
      (List.length compiled.(CompiledSystem.combination_columns))
      OrchardCompiledPinned.num_combinations)
    (OrchardConfigure.base_fixed_columns
      + Z.of_nat (List.length compiled.(CompiledSystem.combination_columns))
      =? OrchardCompiledPinned.num_fixed_columns)
  = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(** Exact compression-column indices and the corresponding assignment count.
    These strengthen the count check and justify the printer cache above. *)
Lemma combination_columns_match :
  compiled.(CompiledSystem.combination_columns) = combination_columns_cache.
Proof.
  vm_cast_no_check (@eq_refl (list Z) combination_columns_cache).
Qed.

Lemma combination_assignments_count_match :
  List.length compiled.(CompiledSystem.combination_assignments) = 15%nat.
Proof. vm_cast_no_check (@eq_refl nat 15%nat). Qed.

(** Every allocated selector receives a compression assignment. *)
Lemma selector_assignments_cover :
  List.forallb
    (fun s =>
      List.existsb
        (fun a => a.(SelectorAssignment.selector) =? Z.of_nat s)
        compiled.(CompiledSystem.selector_assignments))
    (List.seq 0 (Z.to_nat OrchardConfigure.num_selectors))
  = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(** No compiled gate polynomial or lookup input mentions a selector. *)
Lemma compiled_selector_free :
  CompiledSystem.selector_free_b compiled = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(** The query tables match in exact keygen order: 25 advice, 29 fixed, and
    one instance query.  This is stronger than set equality and determines
    every [query_index] rendered in the pinned constraint system. *)
Lemma advice_queries_match :
  compiled.(CompiledSystem.advice_queries) =
    OrchardCompiledPinned.advice_queries.
Proof.
  vm_cast_no_check
    (@eq_refl (list (Z * Z)) compiled.(CompiledSystem.advice_queries)).
Qed.

Lemma fixed_queries_match :
  compiled.(CompiledSystem.fixed_queries) =
    OrchardCompiledPinned.fixed_queries.
Proof.
  vm_cast_no_check
    (@eq_refl (list (Z * Z)) compiled.(CompiledSystem.fixed_queries)).
Qed.

Lemma instance_queries_match :
  compiled.(CompiledSystem.instance_queries) =
    OrchardCompiledPinned.instance_queries.
Proof.
  vm_cast_no_check
    (@eq_refl (list (Z * Z)) compiled.(CompiledSystem.instance_queries)).
Qed.

(** Equality-enabled columns and constants are complete configure outputs,
    not values passed through from the deployed description. *)
Lemma permutation_columns_match :
  compiled.(CompiledSystem.permutation_columns) =
    OrchardCompiledPinned.permutation_columns.
Proof.
  vm_cast_no_check
    (@eq_refl (list Raw.ColumnRef.t)
      compiled.(CompiledSystem.permutation_columns)).
Qed.

Lemma configure_constants_match :
  compiled.(CompiledSystem.constants) = OrchardCompiledPinned.constants.
Proof.
  vm_cast_no_check
    (@eq_refl (list Z) compiled.(CompiledSystem.constants)).
Qed.

Lemma minimum_degree_match :
  OrchardConfigure.minimum_degree = None.
Proof. exact OrchardConfigure.minimum_degree_eq. Qed.

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

(** Every synthesis copy lies in the complete permutation list derived by the
    configure interpreter, independently of the synthesis copy subset and
    deployed comparison list. *)
Lemma copy_columns_in_permutation :
  List.forallb
    (fun c => List.existsb (pair_eqb c) derived_permutation_codes)
    copy_columns
  = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

End OrchardCompiledCheck.
