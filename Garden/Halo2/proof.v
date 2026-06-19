Require Import Garden.Halo2.main.
Require Import Garden.Halo2.Synthesis.
Require Import Garden.Field.Field.
Require Import Garden.Plonky3.M.

Import ListNotations.
Global Open Scope Z_scope.

Module Assignment.
  Record t {columns : Columns.t} {RegionId : Set} : Set := {
    selector : columns.(Columns.Selector) -> RegionId -> Z -> Z;
    fixed : columns.(Columns.Fixed) -> RegionId -> Z -> Z;
    advice : columns.(Columns.Advice) -> RegionId -> Z -> Z;
    instance_ : columns.(Columns.Instance_) -> RegionId -> Z -> Z;
  }.
  Arguments t : clear implicits.
End Assignment.

Module Evaluation.
  Class C {columns : Columns.t} {RegionId : Set} {p : Z} `{Prime p}
      (Index A B : Type) : Type := {
    eval : Assignment.t columns RegionId -> Index -> A -> B;
  }.
End Evaluation.

Module EvaluationResult.
  Inductive t (A : Set) : Set :=
  | Mk (value : A) (facts : Prop).
  Arguments Mk {_}.
End EvaluationResult.

Notation "Γ ⊢ ⟦ x ⟧ ρ" := (Evaluation.eval Γ ρ x)
  (at level 10, x at level 200, ρ at level 9).

Definition rotated_row
    (row : Z)
    (rotation : Rotation.t)
    : Z :=
  row + rotation.(Rotation.offset).

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
            region
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
          (Garden.Halo2.Synthesis.Cell.region cell)
          (Garden.Halo2.Synthesis.Cell.row_offset cell)
    end.

  Fixpoint eval_region {A : Set}
      (assignment : Assignment.t columns RegionId)
      (region : RegionId)
      (program : Garden.Halo2.Synthesis.𝓡 columns RegionId A)
      {struct program}
      : EvaluationResult.t A :=
    match program with
    | Garden.Halo2.Synthesis.𝓡.Ret value =>
        EvaluationResult.Mk value True
    | Garden.Halo2.Synthesis.𝓡.Bind first second =>
        match eval_region assignment region first with
        | EvaluationResult.Mk value facts_first =>
            match eval_region assignment region (second value) with
            | EvaluationResult.Mk value facts_second =>
                EvaluationResult.Mk value (facts_first /\ facts_second)
            end
        end
    | Garden.Halo2.Synthesis.𝓡.EnableSelector selector offset _ =>
        EvaluationResult.Mk
          tt
          (assignment.(Assignment.selector) selector region offset = 1)
    | Garden.Halo2.Synthesis.𝓡.AssignFixed _ column offset value =>
        EvaluationResult.Mk
          tt
          (assignment.(Assignment.fixed) column region offset = value)
    | Garden.Halo2.Synthesis.𝓡.Copy left_cell right_cell =>
        EvaluationResult.Mk
          tt
          (eval_cell assignment left_cell = eval_cell assignment right_cell)
    end.

  Fixpoint eval_layouter {A : Set}
      (assignment : Assignment.t columns RegionId)
      (program : Garden.Halo2.Synthesis.𝓛 columns RegionId A)
      {struct program}
      : EvaluationResult.t A :=
    match program with
    | Garden.Halo2.Synthesis.𝓛.Ret value =>
        EvaluationResult.Mk value True
    | Garden.Halo2.Synthesis.𝓛.Bind first second =>
        match eval_layouter assignment first with
        | EvaluationResult.Mk value facts_first =>
            match eval_layouter assignment (second value) with
            | EvaluationResult.Mk value facts_second =>
                EvaluationResult.Mk value (facts_first /\ facts_second)
            end
        end
    | Garden.Halo2.Synthesis.𝓛.AddRegion region _ region_program =>
        eval_region assignment region (region_program region)
    | Garden.Halo2.Synthesis.𝓛.ConstrainInstance cell instance row =>
        EvaluationResult.Mk
          tt
          (eval_cell assignment cell =
            assignment.(Assignment.instance_)
              instance
              (Garden.Halo2.Synthesis.Cell.region cell)
              row)
    | Garden.Halo2.Synthesis.𝓛.InitLookupTables _ _ =>
        EvaluationResult.Mk tt True
    | Garden.Halo2.Synthesis.𝓛.InNamespace _ nested =>
        eval_layouter assignment nested
    end.

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

  Global Instance RegionProgramIsEvaluable {A : Set} :
      Evaluation.C
        RegionId
        (Garden.Halo2.Synthesis.𝓡 columns RegionId A)
        (EvaluationResult.t A) := {
    Evaluation.eval Γ region program :=
      eval_region Γ region program;
  }.

  Global Instance LayouterProgramIsEvaluable {A : Set} :
      Evaluation.C
        unit
        (Garden.Halo2.Synthesis.𝓛 columns RegionId A)
        (EvaluationResult.t A) := {
    Evaluation.eval Γ _ program :=
      eval_layouter Γ program;
  }.
End Semantics.
