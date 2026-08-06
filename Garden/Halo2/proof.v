Require Import Garden.Halo2.main.
Require Import Garden.Halo2.Synthesis.
Require Import Garden.Field.Field.
Require Import Garden.Plonky3.M.
Require Import Stdlib.micromega.Lia.

Import ListNotations.
Global Open Scope Z_scope.

Module Assignment.
  Record t {columns : Columns.t} {RegionId : Set} : Set := {
    selector : columns.(Columns.Selector) -> RegionId -> Z -> Z;
    fixed : columns.(Columns.Fixed) -> RegionId -> Z -> Z;
    advice : columns.(Columns.Advice) -> RegionId -> Z -> Z;
    instance_ : columns.(Columns.Instance_) -> Z -> Z;
    lookup : columns.(Columns.Lookup) -> Z -> Z;
  }.
  Arguments t : clear implicits.
End Assignment.

Module Evaluation.
  Class C {columns : Columns.t} {RegionId : Set} {p : Z} `{Prime p}
      (Index A B : Type) : Type := {
    eval : Assignment.t columns RegionId -> Index -> A -> B;
  }.
End Evaluation.

Module Fact.
  (** A reified atomic fact established by running synthesis.  Keeping facts as
      data (a [Set]) rather than as a [Prop] side-steps the large-elimination
      restriction: the synthesis syntax [𝓡]/[𝓛] is non-small, so a
      [Prop]-valued recursion over it is rejected, but a [Set]-valued one (as in
      [region_facts]) is fine. *)
  Inductive t (columns : Columns.t) (RegionId : Set) : Set :=
  | SelectorOn
      (selector : columns.(Columns.Selector))
      (region : RegionId) (offset : Z)
  | FixedIs
      (column : columns.(Columns.Fixed))
      (region : RegionId) (offset : Z) (value : Z)
  | CellsEqual
      (left right : Garden.Halo2.Synthesis.Cell.t columns RegionId)
  | InstanceIs
      (cell : Garden.Halo2.Synthesis.Cell.t columns RegionId)
      (instance : columns.(Columns.Instance_)) (row : Z)
  | LookupTableLoaded
      (column : columns.(Columns.Lookup))
      (values : list Z) (default_value : Z)
  | CellIsConstant
      (cell : Garden.Halo2.Synthesis.Cell.t columns RegionId)
      (value : Z).
  Arguments SelectorOn {_ _}.
  Arguments FixedIs {_ _}.
  Arguments CellsEqual {_ _}.
  Arguments InstanceIs {_ _}.
  Arguments LookupTableLoaded {_ _}.
  Arguments CellIsConstant {_ _}.
End Fact.

Notation "Γ ⊢ ⟦ x ⟧ ρ" := (Evaluation.eval Γ ρ x)
  (at level 10, x at level 200, ρ at level 9).

Definition rotated_row
    (row : Z)
    (rotation : Rotation.t)
    : Z :=
  row + rotation.(Rotation.offset).

(** The value held by a loaded lookup-table column at [row]: the [row]-th entry
    of [values], or [default_value] past the end.  Mirrors the operational
    [serialize.v] fill, which assigns [values] and pads the remaining rows with
    [default_value]. *)
Definition value_at_row
    (row : Z)
    (values : list Z)
    (default_value : Z)
    : Z :=
  List.nth (Z.to_nat row) values default_value.

Section Semantics.
  Context {columns : Columns.t}.
  Context {RegionId : Set}.
  Context {p : Z}.
  Context `{Prime p}.

  Definition eval_selector
      (assignment : Assignment.t columns RegionId)
      (index : RegionId * Z)
      (selector : columns.(Columns.Selector))
      : Z :=
    let '(region, row) := index in
    UnOp.from
      (assignment.(Assignment.selector) selector region row).

  Fixpoint eval_expression
      (assignment : Assignment.t columns RegionId)
      (index : RegionId * Z)
      (expression : Expression.t columns)
      : Z :=
    let '(region, row) := index in
    match expression with
    | Expression.Constant value =>
        UnOp.from value
    | Expression.Selector selector =>
        eval_selector assignment index selector
    | Expression.Fixed fixed rotation =>
        UnOp.from
          (assignment.(Assignment.fixed)
            fixed
            region
            (rotated_row row rotation))
    | Expression.Advice advice rotation =>
        UnOp.from
          (assignment.(Assignment.advice)
            advice
            region
            (rotated_row row rotation))
    | Expression.Instance_ instance rotation =>
        UnOp.from
          (assignment.(Assignment.instance_)
            instance
            (rotated_row row rotation))
    | Expression.Sum lhs (Expression.Negated rhs) =>
        BinOp.sub
          (eval_expression assignment index lhs)
          (eval_expression assignment index rhs)
    | Expression.Negated expression =>
        UnOp.opp (eval_expression assignment index expression)
    | Expression.Sum lhs rhs =>
        BinOp.add
          (eval_expression assignment index lhs)
          (eval_expression assignment index rhs)
    | Expression.Product lhs rhs =>
        BinOp.mul
          (eval_expression assignment index lhs)
          (eval_expression assignment index rhs)
    | Expression.Scaled expression scale =>
        BinOp.mul
          (eval_expression assignment index expression)
          (UnOp.from scale)
    end.

  Fixpoint eval_constraint
      (assignment : Assignment.t columns RegionId)
      (index : RegionId * Z)
      (constraint : Constraint.t columns)
      : Prop :=
    match constraint with
    | Constraint.Select selector constraint =>
        eval_selector assignment index selector <> 0 ->
          eval_constraint assignment index constraint
    | Constraint.Equal lhs rhs =>
        eval_expression assignment index lhs =
          eval_expression assignment index rhs
    | Constraint.Boolean expression =>
        IsBool.t (eval_expression assignment index expression)
    | Constraint.Range expression range =>
        0 <= eval_expression assignment index expression < Z.of_nat range
    | Constraint.Either lhs rhs =>
        eval_constraint assignment index lhs \/
          eval_constraint assignment index rhs
    | Constraint.EitherZeroToPrecise lhs rhs =>
        eval_expression assignment index lhs = 0 \/
          eval_expression assignment index rhs = 0
    | Constraint.EqualZeroToPrecise expression =>
        eval_expression assignment index expression = 0
    end.
  Arguments eval_constraint _ _ _ /.

  Definition eval_named_constraint
      (assignment : Assignment.t columns RegionId)
      (index : RegionId * Z)
      (constraint : option string * Constraint.t columns)
      : Prop :=
    let '(_, constraint) := constraint in
    eval_constraint assignment index constraint.
  Arguments eval_named_constraint _ _ _ /.

  Fixpoint eval_constraints
      (assignment : Assignment.t columns RegionId)
      (index : RegionId * Z)
      (constraints : Constraints.t columns)
      : Prop :=
    match constraints with
    | [] => True
    | [constraint] =>
        eval_named_constraint assignment index constraint
    | constraint :: constraints =>
        eval_named_constraint assignment index constraint /\
        eval_constraints assignment index constraints
    end.
  Arguments eval_constraints _ _ _ /.

  Definition eval_gate
      (assignment : Assignment.t columns RegionId)
      (index : RegionId * Z)
      (gate : Gate.t columns)
      : Prop :=
    eval_constraints
      assignment
      index
      gate.(Gate.constraints).
  Arguments eval_gate _ _ _ /.

  Fixpoint eval_gates
      (assignment : Assignment.t columns RegionId)
      (index : RegionId * Z)
      (gates : list (Gate.t columns))
      : Prop :=
    match gates with
    | [] => True
    | [gate] =>
        eval_gate assignment index gate
    | gate :: gates =>
        eval_gate assignment index gate /\
        eval_gates assignment index gates
    end.
  Arguments eval_gates _ _ _ /.

  Definition eval_cell
      (assignment : Assignment.t columns RegionId)
      (cell : Garden.Halo2.Synthesis.Cell.t columns RegionId)
      : Z :=
    match Garden.Halo2.Synthesis.Cell.column cell with
    | Garden.Halo2.Synthesis.ColumnRef.Advice column =>
        assignment.(Assignment.advice)
          column
          (Garden.Halo2.Synthesis.Cell.region cell)
          (Garden.Halo2.Synthesis.Cell.row_offset cell)
    | Garden.Halo2.Synthesis.ColumnRef.Fixed column =>
        assignment.(Assignment.fixed)
          column
          (Garden.Halo2.Synthesis.Cell.region cell)
          (Garden.Halo2.Synthesis.Cell.row_offset cell)
    | Garden.Halo2.Synthesis.ColumnRef.Instance_ column =>
        assignment.(Assignment.instance_)
          column
          (Garden.Halo2.Synthesis.Cell.row_offset cell)
    end.

  (** The value computed by a region program.  It depends only on the program
      structure ([Ret]/[Bind]); the effectful nodes return [tt], so it is
      independent of the assignment. *)
  Fixpoint region_value {A : Set}
      (program : Garden.Halo2.Synthesis.𝓡 columns RegionId A)
      {struct program}
      : A :=
    match program with
    | Garden.Halo2.Synthesis.𝓡.Ret value => value
    | Garden.Halo2.Synthesis.𝓡.Bind first second =>
        region_value (second (region_value first))
    | Garden.Halo2.Synthesis.𝓡.EnableSelector _ _ _ => tt
    | Garden.Halo2.Synthesis.𝓡.AssignFixed _ _ _ _ => tt
    | Garden.Halo2.Synthesis.𝓡.Copy _ _ => tt
    | Garden.Halo2.Synthesis.𝓡.ConstrainConstant _ _ => tt
    end.

  (** The facts established by a region program, reified as data.  Keeping facts
      as a [list] (a [Set]) side-steps the large-elimination restriction: the
      non-small synthesis syntax [𝓡]/[𝓛] admits no [Prop]-valued recursion.
      Values threaded through [Bind] come from [region_value]. *)
  Fixpoint region_facts {A : Set}
      (region : RegionId)
      (program : Garden.Halo2.Synthesis.𝓡 columns RegionId A)
      {struct program}
      : list (Fact.t columns RegionId) :=
    match program with
    | Garden.Halo2.Synthesis.𝓡.Ret _ => []
    | Garden.Halo2.Synthesis.𝓡.Bind first second =>
        region_facts region first ++
        region_facts region (second (region_value first))
    | Garden.Halo2.Synthesis.𝓡.EnableSelector selector offset _ =>
        [Fact.SelectorOn selector region offset]
    | Garden.Halo2.Synthesis.𝓡.AssignFixed _ column offset value =>
        [Fact.FixedIs column region offset value]
    | Garden.Halo2.Synthesis.𝓡.Copy left_cell right_cell =>
        [Fact.CellsEqual left_cell right_cell]
    | Garden.Halo2.Synthesis.𝓡.ConstrainConstant cell value =>
        [Fact.CellIsConstant cell value]
    end.

  Fixpoint layouter_value {A : Set}
      (program : Garden.Halo2.Synthesis.𝓛 columns RegionId A)
      {struct program}
      : A :=
    match program with
    | Garden.Halo2.Synthesis.𝓛.Ret value => value
    | Garden.Halo2.Synthesis.𝓛.Bind first second =>
        layouter_value (second (layouter_value first))
    | Garden.Halo2.Synthesis.𝓛.AddRegion region _ region_program =>
        region_value (region_program region)
    | Garden.Halo2.Synthesis.𝓛.ConstrainInstance _ _ _ => tt
    | Garden.Halo2.Synthesis.𝓛.InitLookupTables _ _ => tt
    | Garden.Halo2.Synthesis.𝓛.InNamespace _ nested =>
        layouter_value nested
    end.

  (** The facts established by a layouter program, reified as data: the copies,
      fixed/selector assignments and instance constraints from running
      synthesis. *)
  Fixpoint layouter_facts {A : Set}
      (program : Garden.Halo2.Synthesis.𝓛 columns RegionId A)
      {struct program}
      : list (Fact.t columns RegionId) :=
    match program with
    | Garden.Halo2.Synthesis.𝓛.Ret _ => []
    | Garden.Halo2.Synthesis.𝓛.Bind first second =>
        layouter_facts first ++
        layouter_facts (second (layouter_value first))
    | Garden.Halo2.Synthesis.𝓛.AddRegion region _ region_program =>
        region_facts region (region_program region)
    | Garden.Halo2.Synthesis.𝓛.ConstrainInstance cell instance row =>
        [Fact.InstanceIs cell instance row]
    | Garden.Halo2.Synthesis.𝓛.InitLookupTables _ entries =>
        List.map
          (fun entry =>
            Fact.LookupTableLoaded
              entry.(Garden.Halo2.Synthesis.LookupTableColumn.lookup)
              entry.(Garden.Halo2.Synthesis.LookupTableColumn.values)
              entry.(Garden.Halo2.Synthesis.LookupTableColumn.default_value))
          entries
    | Garden.Halo2.Synthesis.𝓛.InNamespace _ nested =>
        layouter_facts nested
    end.

  (** The number of rows of the lookup table loaded by a layouter program, read
      off the [InitLookupTables] entries — the largest column length.  Supplies
      the [nb_table_rows] used by [circuit_holds] from the program itself; a
      program that loads no table gets [0]. *)
  Fixpoint layouter_table_rows {A : Set}
      (program : Garden.Halo2.Synthesis.𝓛 columns RegionId A)
      {struct program}
      : Z :=
    match program with
    | Garden.Halo2.Synthesis.𝓛.Ret _ => 0
    | Garden.Halo2.Synthesis.𝓛.Bind first second =>
        Z.max
          (layouter_table_rows first)
          (layouter_table_rows (second (layouter_value first)))
    | Garden.Halo2.Synthesis.𝓛.AddRegion _ _ _ => 0
    | Garden.Halo2.Synthesis.𝓛.ConstrainInstance _ _ _ => 0
    | Garden.Halo2.Synthesis.𝓛.InitLookupTables _ entries =>
        Z.of_nat
          (List.list_max
            (List.map
              (fun entry =>
                List.length
                  entry.(Garden.Halo2.Synthesis.LookupTableColumn.values))
              entries))
    | Garden.Halo2.Synthesis.𝓛.InNamespace _ nested =>
        layouter_table_rows nested
    end.

  (** Interpret a reified fact into a [Prop]. *)
  Definition interpret_fact
      (assignment : Assignment.t columns RegionId)
      (fact : Fact.t columns RegionId)
      : Prop :=
    match fact with
    | Fact.SelectorOn selector region offset =>
        assignment.(Assignment.selector) selector region offset = 1
    | Fact.FixedIs column region offset value =>
        assignment.(Assignment.fixed) column region offset = value
    | Fact.CellsEqual left_cell right_cell =>
        eval_cell assignment left_cell = eval_cell assignment right_cell
    | Fact.InstanceIs cell instance row =>
        eval_cell assignment cell =
          assignment.(Assignment.instance_) instance row
    | Fact.LookupTableLoaded column values default_value =>
        (* Only the assigned rows [0 .. length values) are pinned: the
           serializer assigns those rows and, keygen-faithfully, fills the
           default value only up to the usable rows, leaving the [l_last] and
           blinding tail at [0].  Past [length values] the table column is no
           longer program-determined (the default band and the zero tail are
           captured operationally by the fill-replay lemmas, not by this
           relational fact). *)
        forall row,
          0 <= row < Z.of_nat (List.length values) ->
          assignment.(Assignment.lookup) column row =
            value_at_row row values default_value
    | Fact.CellIsConstant cell value =>
        eval_cell assignment cell = value
    end.

  Fixpoint interpret_facts
      (assignment : Assignment.t columns RegionId)
      (facts : list (Fact.t columns RegionId))
      : Prop :=
    match facts with
    | [] => True
    | fact :: facts =>
        interpret_fact assignment fact /\
        interpret_facts assignment facts
    end.

  Lemma interpret_facts_app
      (assignment : Assignment.t columns RegionId)
      (facts1 facts2 : list (Fact.t columns RegionId)) :
    interpret_facts assignment (facts1 ++ facts2) <->
      interpret_facts assignment facts1 /\
      interpret_facts assignment facts2.
  Proof.
    induction facts1 as [| fact facts1 IH]; cbn.
    - tauto.
    - rewrite IH. tauto.
  Qed.

  Lemma interpret_facts_app_left
      (assignment : Assignment.t columns RegionId)
      (facts1 facts2 : list (Fact.t columns RegionId)) :
    interpret_facts assignment (facts1 ++ facts2) ->
    interpret_facts assignment facts1.
  Proof.
    rewrite interpret_facts_app.
    tauto.
  Qed.

  Lemma interpret_facts_app_right
      (assignment : Assignment.t columns RegionId)
      (facts1 facts2 : list (Fact.t columns RegionId)) :
    interpret_facts assignment (facts1 ++ facts2) ->
    interpret_facts assignment facts2.
  Proof.
    rewrite interpret_facts_app.
    tauto.
  Qed.

  Lemma interpret_facts_In
      (assignment : Assignment.t columns RegionId)
      (fact : Fact.t columns RegionId)
      (facts : list (Fact.t columns RegionId)) :
    interpret_facts assignment facts ->
    List.In fact facts ->
    interpret_fact assignment fact.
  Proof.
    induction facts as [| fact' facts IH]; cbn; intros Hfacts Hin.
    - contradiction.
    - destruct Hfacts as [Hfact' Hfacts].
      destruct Hin as [Heq | Hin].
      + subst fact'. exact Hfact'.
      + exact (IH Hfacts Hin).
  Qed.

  Lemma interpret_facts_subset
      (assignment : Assignment.t columns RegionId)
      (facts_sub facts : list (Fact.t columns RegionId)) :
    (forall fact, List.In fact facts_sub -> List.In fact facts) ->
    interpret_facts assignment facts ->
    interpret_facts assignment facts_sub.
  Proof.
    intros Hsubset Hfacts.
    induction facts_sub as [| fact facts_sub IH]; cbn.
    - exact I.
    - split.
      + exact (interpret_facts_In assignment fact facts Hfacts
          (Hsubset fact (or_introl eq_refl))).
      + apply IH.
        intros fact' Hin.
        exact (Hsubset fact' (or_intror Hin)).
  Qed.

  Lemma interpret_region_facts_bind_left
      (assignment : Assignment.t columns RegionId)
      {A B : Set}
      (first : Garden.Halo2.Synthesis.𝓡 columns RegionId A)
      (second : A -> Garden.Halo2.Synthesis.𝓡 columns RegionId B)
      (region : RegionId) :
    interpret_facts assignment (region_facts region (𝓡.Bind first second)) ->
    interpret_facts assignment (region_facts region first).
  Proof.
    cbn [region_facts].
    rewrite interpret_facts_app.
    tauto.
  Qed.

  Lemma interpret_region_facts_bind_right
      (assignment : Assignment.t columns RegionId)
      {A B : Set}
      (first : Garden.Halo2.Synthesis.𝓡 columns RegionId A)
      (second : A -> Garden.Halo2.Synthesis.𝓡 columns RegionId B)
      (region : RegionId) :
    interpret_facts assignment (region_facts region (𝓡.Bind first second)) ->
    interpret_facts assignment
      (region_facts region (second (region_value first))).
  Proof.
    cbn [region_facts].
    rewrite interpret_facts_app.
    tauto.
  Qed.

  Lemma interpret_layouter_facts_bind_left
      (assignment : Assignment.t columns RegionId)
      {A B : Set}
      (first : Garden.Halo2.Synthesis.𝓛 columns RegionId A)
      (second : A -> Garden.Halo2.Synthesis.𝓛 columns RegionId B) :
    interpret_facts assignment (layouter_facts (𝓛.Bind first second)) ->
    interpret_facts assignment (layouter_facts first).
  Proof.
    cbn [layouter_facts].
    rewrite interpret_facts_app.
    tauto.
  Qed.

  Lemma interpret_layouter_facts_bind_right
      (assignment : Assignment.t columns RegionId)
      {A B : Set}
      (first : Garden.Halo2.Synthesis.𝓛 columns RegionId A)
      (second : A -> Garden.Halo2.Synthesis.𝓛 columns RegionId B) :
    interpret_facts assignment (layouter_facts (𝓛.Bind first second)) ->
    interpret_facts assignment
      (layouter_facts (second (layouter_value first))).
  Proof.
    cbn [layouter_facts].
    rewrite interpret_facts_app.
    tauto.
  Qed.

  Lemma interpret_layouter_facts_in_namespace
      (assignment : Assignment.t columns RegionId)
      {A : Set} (name : string)
      (nested : Garden.Halo2.Synthesis.𝓛 columns RegionId A) :
    interpret_facts assignment (layouter_facts (𝓛.InNamespace name nested)) ->
    interpret_facts assignment (layouter_facts nested).
  Proof.
    cbn [layouter_facts].
    tauto.
  Qed.

  Lemma interpret_layouter_facts_add_region
      (assignment : Assignment.t columns RegionId)
      {A : Set} (region : RegionId) (name : string)
      (program : RegionId -> Garden.Halo2.Synthesis.𝓡 columns RegionId A) :
    interpret_facts assignment (layouter_facts (𝓛.AddRegion region name program)) ->
    interpret_facts assignment (region_facts region (program region)).
  Proof.
    cbn [layouter_facts].
    tauto.
  Qed.

  Global Instance SelectorIsEvaluable :
      Evaluation.C (RegionId * Z) columns.(Columns.Selector) Z := {
    Evaluation.eval Γ index selector :=
      eval_selector Γ index selector;
  }.

  Global Instance ExpressionIsEvaluable :
      Evaluation.C (RegionId * Z) (Expression.t columns) Z := {
    Evaluation.eval Γ index expression :=
      eval_expression Γ index expression;
  }.

  Global Instance ConstraintIsEvaluable :
      Evaluation.C (RegionId * Z) (Constraint.t columns) Prop := {
    Evaluation.eval Γ index constraint :=
      eval_constraint Γ index constraint;
  }.

  Global Instance NamedConstraintIsEvaluable :
      Evaluation.C
        (RegionId * Z) (option string * Constraint.t columns) Prop := {
    Evaluation.eval Γ index constraint :=
      eval_named_constraint Γ index constraint;
  }.

  Global Instance ConstraintsIsEvaluable :
      Evaluation.C (RegionId * Z) (Constraints.t columns) Prop := {
    Evaluation.eval Γ index constraints :=
      eval_constraints Γ index constraints;
  }.

  Global Instance GateIsEvaluable :
      Evaluation.C (RegionId * Z) (Gate.t columns) Prop := {
    Evaluation.eval Γ index gate :=
      eval_gate Γ index gate;
  }.

  Global Instance GatesIsEvaluable :
      Evaluation.C (RegionId * Z) (list (Gate.t columns)) Prop := {
    Evaluation.eval Γ index gates :=
      eval_gates Γ index gates;
  }.

  (** The gate part of the prover's guarantee: every gate of the constraint
      system holds at every [(region, row)].  Because each gate constraint is
      guarded by its selector ([Constraint.Select]), this is vacuous wherever
      the selector is 0 — so it states exactly "gates bind on enabled rows".

      The quantification ranges over all of [RegionId * Z], the simplest
      faithful reading of "the prover checks every row": it is not narrowed to
      each region's actual extent, and rows are unbounded integers with no
      cyclic domain or blinding-row distinction. *)
  Definition satisfies_gates
      (assignment : Assignment.t columns RegionId)
      (system : ConstraintSystem.t columns)
      : Prop :=
    forall (region : RegionId) (row : Z),
      eval_gates assignment (region, row)
        system.(ConstraintSystem.gates).

  (** A single lookup argument holds at [index] when the tuple of queried
      expressions equals some row of the loaded table.  The witnessed row is
      bounded by [nb_table_rows], the size of the loaded table — this is what
      gives the lookup its range-check role (only valid table rows satisfy it).
      [Assignment.lookup] is global (not region-scoped): tables are loaded once
      and addressed by an absolute [table_row]. *)
  Definition eval_lookup_argument
      (assignment : Assignment.t columns RegionId)
      (index : RegionId * Z)
      (nb_table_rows : Z)
      (arg : LookupArgument.t columns)
      : Prop :=
    exists table_row,
      0 <= table_row < nb_table_rows /\
      List.Forall
        (fun '(expression, column) =>
          eval_expression assignment index expression =
            assignment.(Assignment.lookup) column table_row)
        arg.(LookupArgument.pairs).
  Arguments eval_lookup_argument _ _ _ _ /.

  (** The lookup part of the prover's guarantee: every lookup argument of the
      constraint system holds at every [(region, row)].  The table-row bound
      [nb_table_rows] is an explicit parameter: the [Γ ⊢ ⟦ x ⟧ index] notation
      has no slot for it, so [LookupArgument.t] carries no [Evaluation.C]
      instance. *)
  Definition satisfies_lookups
      (assignment : Assignment.t columns RegionId)
      (nb_table_rows : Z)
      (system : ConstraintSystem.t columns)
      : Prop :=
    forall (region : RegionId) (row : Z),
      List.Forall
        (eval_lookup_argument assignment (region, row) nb_table_rows)
        system.(ConstraintSystem.lookups).

  Definition Satisfies
      (assignment : Assignment.t columns RegionId)
      (nb_table_rows : Z)
      (system : ConstraintSystem.t columns)
      : Prop :=
    satisfies_gates assignment system /\
    satisfies_lookups assignment nb_table_rows system.

  (** What a successful Halo2 proof of a chip gives: the synthesis-time facts
      (copies, fixed/selector assignments, instance constraints collected by
      running the layouter program) together with gate/lookup satisfaction of
      the configured constraint system. *)
  Definition circuit_holds {A : Set}
      (assignment : Assignment.t columns RegionId)
      (program : Garden.Halo2.Synthesis.𝓛 columns RegionId A)
      (system : ConstraintSystem.t columns)
      : Prop :=
    interpret_facts assignment (layouter_facts program) /\
    Satisfies assignment (layouter_table_rows program) system.

  Definition gates_only_system
      (system : ConstraintSystem.t columns)
      : ConstraintSystem.t columns := {|
    ConstraintSystem.gates := system.(ConstraintSystem.gates);
    ConstraintSystem.lookups := [];
  |}.

  (** Bridge 1: a selector enabled by the synthesis program ([= 1]) evaluates
      to a non-zero value, discharging the selector hypothesis of a gate
      lemma. *)
  Lemma enabled_nonzero
      (assignment : Assignment.t columns RegionId)
      (selector : columns.(Columns.Selector))
      (region : RegionId) (offset : Z)
      (Henabled :
        assignment.(Assignment.selector) selector region offset = 1) :
    eval_selector assignment (region, offset) selector <> 0.
  Proof.
    cbn [eval_selector].
    rewrite Henabled.
    autorewrite with field_rewrite.
    discriminate.
  Qed.

  (** Bridge 2: from gate satisfaction, extract the single gate of a one-gate
      system at any [(region, row)]. *)
  Lemma satisfies_gates_single
      (assignment : Assignment.t columns RegionId)
      (system : ConstraintSystem.t columns)
      (gate : Gate.t columns)
      (region : RegionId) (row : Z)
      (Hsystem : system.(ConstraintSystem.gates) = [gate])
      (Hsatisfies : satisfies_gates assignment system) :
    eval_gate assignment (region, row) gate.
  Proof.
    specialize (Hsatisfies region row).
    rewrite Hsystem in Hsatisfies.
    exact Hsatisfies.
  Qed.

  (** Any gate that occurs in an evaluated list of gates holds individually.
      This is the multi-gate generalization of the singleton reasoning in
      [satisfies_gates_single]. *)
  Lemma eval_gates_In
      (assignment : Assignment.t columns RegionId)
      (index : RegionId * Z)
      (gate : Gate.t columns)
      (gates : list (Gate.t columns))
      (Hin : List.In gate gates)
      (Hgates : eval_gates assignment index gates) :
    eval_gate assignment index gate.
  Proof.
    revert Hin Hgates.
    induction gates as [| g gates IH]; intros Hin Hgates.
    - destruct Hin.
    - cbn [List.In] in Hin.
      destruct Hin as [Heq | Hin].
      + subst gate.
        destruct gates as [| g' gates'].
        * exact Hgates.
        * exact (proj1 Hgates).
      + destruct gates as [| g' gates'].
        * destruct Hin.
        * exact (IH Hin (proj2 Hgates)).
  Qed.

  Lemma eval_gates_subset
      (assignment : Assignment.t columns RegionId)
      (index : RegionId * Z)
      (gates_sub gates : list (Gate.t columns)) :
    (forall gate, List.In gate gates_sub -> List.In gate gates) ->
    eval_gates assignment index gates ->
    eval_gates assignment index gates_sub.
  Proof.
    intros Hsubset Hgates.
    induction gates_sub as [| gate gates_sub IH]; cbn.
    - exact I.
    - destruct gates_sub as [| gate' gates_sub'].
      + exact (eval_gates_In assignment index gate gates
          (Hsubset gate (or_introl eq_refl)) Hgates).
      + split.
        * exact (eval_gates_In assignment index gate gates
            (Hsubset gate (or_introl eq_refl)) Hgates).
        * apply IH.
          intros gate'' Hin.
          exact (Hsubset gate'' (or_intror Hin)).
  Qed.

  (** Bridge 3: from gate satisfaction, extract any gate of the constraint
      system at any [(region, row)] — the multi-gate form of
      [satisfies_gates_single]. *)
  Lemma satisfies_gates_at
      (assignment : Assignment.t columns RegionId)
      (system : ConstraintSystem.t columns)
      (gate : Gate.t columns)
      (region : RegionId) (row : Z)
      (Hin : List.In gate system.(ConstraintSystem.gates))
      (Hsatisfies : satisfies_gates assignment system) :
    eval_gate assignment (region, row) gate.
  Proof.
    exact (eval_gates_In assignment (region, row) gate _ Hin
      (Hsatisfies region row)).
  Qed.

  Lemma satisfies_gates_subset
      (assignment : Assignment.t columns RegionId)
      (system_sub system : ConstraintSystem.t columns) :
    (forall gate,
      List.In gate system_sub.(ConstraintSystem.gates) ->
      List.In gate system.(ConstraintSystem.gates)) ->
    satisfies_gates assignment system ->
    satisfies_gates assignment system_sub.
  Proof.
    intros Hsubset Hsatisfies region row.
    exact (eval_gates_subset assignment (region, row)
      system_sub.(ConstraintSystem.gates)
      system.(ConstraintSystem.gates)
      Hsubset
      (Hsatisfies region row)).
  Qed.

  Lemma satisfies_lookups_nil
      (assignment : Assignment.t columns RegionId)
      (nb_table_rows : Z)
      (system : ConstraintSystem.t columns) :
    system.(ConstraintSystem.lookups) = [] ->
    satisfies_lookups assignment nb_table_rows system.
  Proof.
    intros Hlookups region row.
    unfold satisfies_lookups.
    rewrite Hlookups.
    constructor.
  Qed.

  Lemma eval_lookup_argument_expand_rows
      (assignment : Assignment.t columns RegionId)
      (index : RegionId * Z)
      (nb_table_rows nb_table_rows' : Z)
      (arg : LookupArgument.t columns) :
    nb_table_rows <= nb_table_rows' ->
    eval_lookup_argument assignment index nb_table_rows arg ->
    eval_lookup_argument assignment index nb_table_rows' arg.
  Proof.
    intros Hrows Hlookup.
    destruct Hlookup as (table_row & Hbound & Hpairs).
    exists table_row.
    split.
    - lia.
    - exact Hpairs.
  Qed.

  Lemma eval_lookup_arguments_In
      (assignment : Assignment.t columns RegionId)
      (index : RegionId * Z)
      (nb_table_rows : Z)
      (arg : LookupArgument.t columns)
      (args : list (LookupArgument.t columns)) :
    List.In arg args ->
    List.Forall
      (eval_lookup_argument assignment index nb_table_rows) args ->
    eval_lookup_argument assignment index nb_table_rows arg.
  Proof.
    intros Hin Hargs.
    induction Hargs as [| arg' args Harg _ IH].
    - destruct Hin.
    - cbn [List.In] in Hin.
      destruct Hin as [Heq | Hin].
      + subst arg'. exact Harg.
      + exact (IH Hin).
  Qed.

  Lemma eval_lookup_arguments_subset
      (assignment : Assignment.t columns RegionId)
      (index : RegionId * Z)
      (nb_table_rows nb_table_rows' : Z)
      (args_sub args : list (LookupArgument.t columns)) :
    (forall arg, List.In arg args_sub -> List.In arg args) ->
    nb_table_rows <= nb_table_rows' ->
    List.Forall
      (eval_lookup_argument assignment index nb_table_rows) args ->
    List.Forall
      (eval_lookup_argument assignment index nb_table_rows') args_sub.
  Proof.
    intros Hsubset Hrows Hargs.
    induction args_sub as [| arg args_sub IH].
    - constructor.
    - constructor.
      + apply (eval_lookup_argument_expand_rows
          assignment index nb_table_rows nb_table_rows').
        * exact Hrows.
        * apply (eval_lookup_arguments_In assignment index
            nb_table_rows arg args).
          -- apply Hsubset. left. reflexivity.
          -- exact Hargs.
      + apply IH.
        intros arg' Hin.
        apply Hsubset. right. exact Hin.
  Qed.

  Lemma satisfies_lookups_subset
      (assignment : Assignment.t columns RegionId)
      (nb_table_rows nb_table_rows' : Z)
      (system_sub system : ConstraintSystem.t columns) :
    (forall arg,
      List.In arg system_sub.(ConstraintSystem.lookups) ->
      List.In arg system.(ConstraintSystem.lookups)) ->
    nb_table_rows <= nb_table_rows' ->
    satisfies_lookups assignment nb_table_rows system ->
    satisfies_lookups assignment nb_table_rows' system_sub.
  Proof.
    intros Hsubset Hrows Hlookups region row.
    exact (eval_lookup_arguments_subset assignment (region, row)
      nb_table_rows nb_table_rows'
      system_sub.(ConstraintSystem.lookups)
      system.(ConstraintSystem.lookups)
      Hsubset Hrows
      (Hlookups region row)).
  Qed.

  Lemma satisfies_gates_only_system
      (assignment : Assignment.t columns RegionId)
      (system : ConstraintSystem.t columns) :
    satisfies_gates assignment system ->
    satisfies_gates assignment (gates_only_system system).
  Proof.
    exact (fun Hsatisfies => Hsatisfies).
  Qed.

  Lemma circuit_holds_gates_no_lookups_subset
      (assignment : Assignment.t columns RegionId)
      {A B : Set}
      (program_sub : Garden.Halo2.Synthesis.𝓛 columns RegionId A)
      (program : Garden.Halo2.Synthesis.𝓛 columns RegionId B)
      (system_sub system : ConstraintSystem.t columns) :
    (forall fact,
      List.In fact (layouter_facts program_sub) ->
      List.In fact (layouter_facts program)) ->
    (forall gate,
      List.In gate system_sub.(ConstraintSystem.gates) ->
      List.In gate system.(ConstraintSystem.gates)) ->
    system_sub.(ConstraintSystem.lookups) = [] ->
    circuit_holds assignment program system ->
    circuit_holds assignment program_sub system_sub.
  Proof.
    intros Hfacts_subset Hgates_subset Hlookups_nil Hholds.
    destruct Hholds as [Hfacts HSatisfies].
    destruct HSatisfies as [Hgates Hlookups].
    split.
    - exact (interpret_facts_subset assignment
        (layouter_facts program_sub)
        (layouter_facts program)
        Hfacts_subset
        Hfacts).
    - split.
      + exact (satisfies_gates_subset assignment system_sub system
          Hgates_subset Hgates).
      + exact (satisfies_lookups_nil assignment
          (layouter_table_rows program_sub)
          system_sub
          Hlookups_nil).
  Qed.

  Lemma circuit_holds_subset
      (assignment : Assignment.t columns RegionId)
      {A B : Set}
      (program_sub : Garden.Halo2.Synthesis.𝓛 columns RegionId A)
      (program : Garden.Halo2.Synthesis.𝓛 columns RegionId B)
      (system_sub system : ConstraintSystem.t columns) :
    (forall fact,
      List.In fact (layouter_facts program_sub) ->
      List.In fact (layouter_facts program)) ->
    (forall gate,
      List.In gate system_sub.(ConstraintSystem.gates) ->
      List.In gate system.(ConstraintSystem.gates)) ->
    (forall arg,
      List.In arg system_sub.(ConstraintSystem.lookups) ->
      List.In arg system.(ConstraintSystem.lookups)) ->
    layouter_table_rows program <= layouter_table_rows program_sub ->
    circuit_holds assignment program system ->
    circuit_holds assignment program_sub system_sub.
  Proof.
    intros Hfacts_subset Hgates_subset Hlookups_subset Hrows Hholds.
    destruct Hholds as [Hfacts HSatisfies].
    destruct HSatisfies as [Hgates Hlookups].
    split.
    - exact (interpret_facts_subset assignment
        (layouter_facts program_sub)
        (layouter_facts program)
        Hfacts_subset
        Hfacts).
    - split.
      + exact (satisfies_gates_subset assignment system_sub system
          Hgates_subset Hgates).
      + exact (satisfies_lookups_subset assignment
          (layouter_table_rows program)
          (layouter_table_rows program_sub)
          system_sub system
          Hlookups_subset Hrows Hlookups).
  Qed.
End Semantics.
