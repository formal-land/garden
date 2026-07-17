(** * Compilation smoke tests: domain arithmetic, selector packing, σ orbits.

    Three concrete instances of the compiled plonkish layer, each closed by
    [vm_compute]:

    - the cyclic domain at [k = 2]: [n]/[usable_rows] values, the
      [l_0]/[l_last]/[l_blind] row predicates, and rotation wrap-around;
    - [Compile.compile] on the add chip under the concrete Orchard
      placement, with the selector activations read off the serialized
      events, and on a synthetic three-selector system whose packing
      produces a two-member combination with non-trivial indicator
      polynomials;
    - [Sigma.sigma_of_copies] on a three-copy list: the resulting mapping
      is the cycle closure of the copies, checked both as the full matrix
      and orbit by orbit, with an out-of-range copy rejected. *)

Require Import Garden.Halo2.main.
Require Import Garden.Halo2.serialize.
Require Import Garden.Halo2.plonkish.main.
Require Import Garden.Halo2.realize.smoke.
Require Import Garden.Orchard.columns.

Import ListNotations.
Import Plonkish.
Global Open Scope Z_scope.

(** ** The cyclic domain at [k = 2]

    Four rows, one blinding factor: rows 0 and 1 are usable, row 2 is the
    spare ([l_last]) row, row 3 is the blinding row. *)

Definition domain_k2 : Domain.t := {|
  Domain.k := 2;
  Domain.blinding_factors := 1;
|}.

Lemma domain_k2_n : Domain.n domain_k2 = 4.
Proof. vm_compute. reflexivity. Qed.

Lemma domain_k2_usable_rows : Domain.usable_rows domain_k2 = 2.
Proof. vm_compute. reflexivity. Qed.

Lemma domain_k2_l_0 :
  List.map (Domain.l_0 domain_k2) [0; 1; 2; 3] =
    [true; false; false; false].
Proof. vm_compute. reflexivity. Qed.

Lemma domain_k2_l_last :
  List.map (Domain.l_last domain_k2) [0; 1; 2; 3] =
    [false; false; true; false].
Proof. vm_compute. reflexivity. Qed.

Lemma domain_k2_l_blind :
  List.map (Domain.l_blind domain_k2) [0; 1; 2; 3] =
    [false; false; false; true].
Proof. vm_compute. reflexivity. Qed.

Lemma domain_k2_usable :
  List.map (Domain.usable domain_k2) [0; 1; 2; 3] =
    [true; true; false; false].
Proof. vm_compute. reflexivity. Qed.

(** Every row is exactly one of usable, [l_last], blinding. *)
Lemma domain_k2_partition :
  List.forallb
    (fun row =>
      Z.eqb 1
        ((if Domain.usable domain_k2 row then 1 else 0) +
          (if Domain.l_last domain_k2 row then 1 else 0) +
          (if Domain.l_blind domain_k2 row then 1 else 0)))
    [0; 1; 2; 3] = true.
Proof. vm_compute. reflexivity. Qed.

(** Rotation wraps around the domain in both directions. *)
Lemma domain_k2_rot_next :
  List.map (fun row => Domain.rot domain_k2 row 1) [0; 1; 2; 3] =
    [1; 2; 3; 0].
Proof. vm_compute. reflexivity. Qed.

Lemma domain_k2_rot_prev :
  List.map (fun row => Domain.rot domain_k2 row (-1)) [0; 1; 2; 3] =
    [3; 0; 1; 2].
Proof. vm_compute. reflexivity. Qed.

(** ** Compilation of the add chip

    The add chip under the concrete Orchard placement: selector 1 ([QAdd])
    is enabled at absolute row 1764 by the serialized events and appears in
    the single addition gate; selector 0 appears in no gate, so it is
    retained as a plain 0/1 fixed column.  The activations are read off the
    event stream over the full [2^11]-row domain.  With combination fixed
    columns allocated from index 2: selector 0 lands alone in column 2 as a
    plain query, selector 1 is packed as the sole member of the combination
    in column 3, whose indicator polynomial (an empty product over the
    other roots) is the bare query. *)

Definition add_chip_indexed_system
    : ConstraintSystem.t Configure.indexed_columns :=
  Configure.to_indexed Index.indices add_chip_system.

Definition add_chip_n_rows : nat := 2048%nat.

Definition add_chip_infos : list Compile.SelectorInfo.t := [
  {|
    Compile.SelectorInfo.activations :=
      Compile.selector_activations_of_events
        add_chip_events 0 add_chip_n_rows;
    Compile.SelectorInfo.simple := true;
  |};
  {|
    Compile.SelectorInfo.activations :=
      Compile.selector_activations_of_events
        add_chip_events 1 add_chip_n_rows;
    Compile.SelectorInfo.simple := true;
  |}
].

Definition add_chip_compiled : CompiledSystem.t :=
  Compile.compile add_chip_indexed_system add_chip_infos 2 [] [].

Lemma add_chip_system_degree : system_degree add_chip_indexed_system = 3%nat.
Proof. vm_compute. reflexivity. Qed.

(** The compiled gate: the combination column query substituted for the
    selector in the flattened addition polynomial. *)
Lemma add_chip_compiled_gates :
  add_chip_compiled.(CompiledSystem.gates) =
    [Expression.Product
      (@Expression.Fixed Configure.indexed_columns 3 Rotation.cur)
      (Expression.Sum
        (Expression.Sum
          (@Expression.Advice Configure.indexed_columns 7 Rotation.cur)
          (@Expression.Advice Configure.indexed_columns 8 Rotation.cur))
        (Expression.Negated
          (@Expression.Advice Configure.indexed_columns 6 Rotation.cur)))].
Proof. vm_compute. reflexivity. Qed.

Lemma add_chip_selector_free :
  CompiledSystem.selector_free_b add_chip_compiled = true.
Proof. vm_compute. reflexivity. Qed.

Lemma add_chip_compiled_queries :
  (add_chip_compiled.(CompiledSystem.advice_queries),
    add_chip_compiled.(CompiledSystem.fixed_queries),
    add_chip_compiled.(CompiledSystem.instance_queries)) =
    ([(7, 0); (8, 0); (6, 0)], [(3, 0)], []).
Proof. vm_compute. reflexivity. Qed.

Lemma add_chip_combination_columns :
  add_chip_compiled.(CompiledSystem.combination_columns) = [2; 3].
Proof. vm_compute. reflexivity. Qed.

Lemma add_chip_selector_assignments :
  add_chip_compiled.(CompiledSystem.selector_assignments) = [
    {|
      SelectorAssignment.selector := 0;
      SelectorAssignment.combination_index := 0%nat;
      SelectorAssignment.expression :=
        @Expression.Fixed Configure.indexed_columns 2 Rotation.cur;
    |};
    {|
      SelectorAssignment.selector := 1;
      SelectorAssignment.combination_index := 1%nat;
      SelectorAssignment.expression :=
        @Expression.Fixed Configure.indexed_columns 3 Rotation.cur;
    |}
  ].
Proof. vm_compute. reflexivity. Qed.

Lemma add_chip_combination_lengths :
  List.map (@List.length Z)
    add_chip_compiled.(CompiledSystem.combination_assignments) =
    [2048; 2048]%nat.
Proof. vm_compute. reflexivity. Qed.

(** Selector 0 is enabled nowhere: its column is identically 0. *)
Lemma add_chip_combination_0_all_off :
  List.forallb (Z.eqb 0)
    (List.nth 0
      add_chip_compiled.(CompiledSystem.combination_assignments) []) = true.
Proof. vm_compute. reflexivity. Qed.

(** Selector 1 is enabled exactly at row 1764: its column carries the
    assigned root 1 there and 0 everywhere else. *)
Lemma add_chip_combination_1_on_row :
  List.nth 1764%nat
    (List.nth 1
      add_chip_compiled.(CompiledSystem.combination_assignments) [])
    0 = 1.
Proof. vm_compute. reflexivity. Qed.

Lemma add_chip_combination_1_off_rows :
  let column :=
    List.nth 1
      add_chip_compiled.(CompiledSystem.combination_assignments) [] in
  andb
    (List.forallb (Z.eqb 0) (List.firstn 1764 column))
    (List.forallb (Z.eqb 0) (List.skipn 1765 column)) = true.
Proof. vm_compute. reflexivity. Qed.

(** The add chip queries each advice column at one rotation, so the
    blinding count is the [max (3, 1) + 1 + 1] default. *)
Lemma add_chip_blinding_factors :
  CompiledSystem.blinding_factors add_chip_compiled = 5.
Proof. vm_compute. reflexivity. Qed.

(** ** Greedy packing on a synthetic three-selector system

    Three degree-2 gates, one selector each; selectors 0 and 2 are active
    on row 0, selector 1 on row 1.  Under the degree budget 3 (the
    permutation argument's required degree), the packing joins selectors 0
    and 1 — row-disjoint — into the combination in column 4 with roots 1
    and 2 and the indicator polynomials [F·(2 − F)] and [F·(1 − F)];
    selector 2 conflicts with selector 0 on row 0, so it lands alone in
    column 5 as a bare query. *)

Definition packing_gate (selector : Z) (name : PrimString.string)
    : Gate.t Configure.indexed_columns := {|
  Gate.name := name;
  Gate.constraints := [
    (None,
      @Constraint.Select Configure.indexed_columns selector
        (@Constraint.Equal Configure.indexed_columns
          (@Expression.Advice Configure.indexed_columns 0 Rotation.cur)
          (@Expression.Advice Configure.indexed_columns 1 Rotation.cur)))
  ];
|}.

Definition packing_system : ConstraintSystem.t Configure.indexed_columns := {|
  ConstraintSystem.gates :=
    [packing_gate 0 "g0"; packing_gate 1 "g1"; packing_gate 2 "g2"];
  ConstraintSystem.lookups := [];
|}.

Definition packing_infos : list Compile.SelectorInfo.t := [
  {| Compile.SelectorInfo.activations := [true; false];
     Compile.SelectorInfo.simple := true |};
  {| Compile.SelectorInfo.activations := [false; true];
     Compile.SelectorInfo.simple := true |};
  {| Compile.SelectorInfo.activations := [true; false];
     Compile.SelectorInfo.simple := true |}
].

Definition packing_compiled : CompiledSystem.t :=
  Compile.compile packing_system packing_infos 4 [] [].

Definition packing_query (column : Z)
    : Expression.t Configure.indexed_columns :=
  @Expression.Fixed Configure.indexed_columns column Rotation.cur.

Definition packing_body : Expression.t Configure.indexed_columns :=
  Expression.Sum
    (@Expression.Advice Configure.indexed_columns 0 Rotation.cur)
    (Expression.Negated
      (@Expression.Advice Configure.indexed_columns 1 Rotation.cur)).

Definition packing_indicator (root : Z)
    : Expression.t Configure.indexed_columns :=
  Expression.Product
    (packing_query 4)
    (Expression.Sum
      (Expression.Constant root)
      (Expression.Negated (packing_query 4))).

Lemma packing_system_degree : system_degree packing_system = 3%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma packing_compiled_eq :
  packing_compiled = {|
    CompiledSystem.gates := [
      Expression.Product (packing_indicator 2) packing_body;
      Expression.Product (packing_indicator 1) packing_body;
      Expression.Product (packing_query 5) packing_body
    ];
    CompiledSystem.lookups := [];
    CompiledSystem.advice_queries := [(0, 0); (1, 0)];
    CompiledSystem.fixed_queries := [(4, 0); (5, 0)];
    CompiledSystem.instance_queries := [];
    CompiledSystem.permutation_columns := [];
    CompiledSystem.constants := [];
    CompiledSystem.combination_columns := [4; 5];
    CompiledSystem.combination_assignments := [[1; 2]; [1; 0]];
    CompiledSystem.selector_assignments := [
      {|
        SelectorAssignment.selector := 0;
        SelectorAssignment.combination_index := 0%nat;
        SelectorAssignment.expression := packing_indicator 2;
      |};
      {|
        SelectorAssignment.selector := 1;
        SelectorAssignment.combination_index := 0%nat;
        SelectorAssignment.expression := packing_indicator 1;
      |};
      {|
        SelectorAssignment.selector := 2;
        SelectorAssignment.combination_index := 1%nat;
        SelectorAssignment.expression := packing_query 5;
      |}
    ];
  |}.
Proof. vm_compute. reflexivity. Qed.

(** ** σ on a three-copy list

    Two advice columns, four rows.  The first two copies chain
    [(0,0) ~ (1,1) ~ (0,2)] into one 3-cycle, the third joins [(0,3)] and
    [(1,3)] into a 2-cycle; every other cell stays a fixed point. *)

Definition sigma_advice_column (index : Z) : Raw.ColumnRef.t := {|
  Raw.ColumnRef.kind := Raw.ColumnKind.Advice;
  Raw.ColumnRef.index := index;
|}.

Definition sigma_cell_at (column : Raw.ColumnRef.t) (row : Z) : Raw.Cell.t := {|
  Raw.Cell.column := column;
  Raw.Cell.row := row;
|}.

Definition sigma_columns : list Raw.ColumnRef.t :=
  [sigma_advice_column 0; sigma_advice_column 1].

Definition sigma_copies : list (Raw.Cell.t * Raw.Cell.t) := [
  (sigma_cell_at (sigma_advice_column 0) 0,
    sigma_cell_at (sigma_advice_column 1) 1);
  (sigma_cell_at (sigma_advice_column 1) 1,
    sigma_cell_at (sigma_advice_column 0) 2);
  (sigma_cell_at (sigma_advice_column 0) 3,
    sigma_cell_at (sigma_advice_column 1) 3)
].

Definition sigma_result : option Sigma.t :=
  Sigma.sigma_of_copies sigma_columns 4 sigma_copies.

Definition sigma_perm (c : Sigma.cell) : Sigma.cell :=
  match sigma_result with
  | Some assembly => Sigma.perm assembly c
  | None => c
  end.

(** The full mapping matrix: the cycle closure of the three copies. *)
Lemma sigma_result_mapping :
  option_map Sigma.mapping sigma_result =
    Some [
      [(1, 1); (0, 1); (0, 0); (1, 3)];
      [(1, 0); (0, 2); (1, 2); (0, 3)]
    ]%nat.
Proof. vm_compute. reflexivity. Qed.

(** The 3-cycle through the two chained copies. *)
Lemma sigma_orbit_three :
  List.map sigma_perm [(0, 0); (1, 1); (0, 2)]%nat =
    [(1, 1); (0, 2); (0, 0)]%nat.
Proof. vm_compute. reflexivity. Qed.

(** The 2-cycle of the third copy. *)
Lemma sigma_orbit_two :
  List.map sigma_perm [(0, 3); (1, 3)]%nat = [(1, 3); (0, 3)]%nat.
Proof. vm_compute. reflexivity. Qed.

(** Cells outside every copy are fixed points. *)
Lemma sigma_fixed_points :
  List.map sigma_perm [(0, 1); (1, 0); (1, 2)]%nat =
    [(0, 1); (1, 0); (1, 2)]%nat.
Proof. vm_compute. reflexivity. Qed.

(** The union-find bookkeeping: one representative per orbit, sizes at the
    representatives. *)
Lemma sigma_result_aux :
  option_map Sigma.aux sigma_result =
    Some [
      [(0, 0); (0, 1); (0, 0); (0, 3)];
      [(1, 0); (0, 0); (1, 2); (0, 3)]
    ]%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma sigma_result_sizes :
  option_map Sigma.sizes sigma_result =
    Some [[3; 1; 1; 2]; [1; 1; 1; 1]]%nat.
Proof. vm_compute. reflexivity. Qed.

(** A copy whose row is outside the domain is rejected. *)
Lemma sigma_out_of_range :
  Sigma.sigma_of_copies sigma_columns 4
    [(sigma_cell_at (sigma_advice_column 0) 0,
      sigma_cell_at (sigma_advice_column 1) 4)] = None.
Proof. vm_compute. reflexivity. Qed.

(** A copy naming a column outside the permutation list is rejected. *)
Lemma sigma_column_not_in_permutation :
  Sigma.sigma_of_copies sigma_columns 4
    [(sigma_cell_at (sigma_advice_column 0) 0,
      sigma_cell_at (sigma_advice_column 2) 0)] = None.
Proof. vm_compute. reflexivity. Qed.
