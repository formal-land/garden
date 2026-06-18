Require Import Garden.Halo2.main.
Require Import Garden.Field.Field.
Require Import Garden.Plonky3.M.

Import ListNotations.
Global Open Scope Z_scope.

Module Assignment.
  Record t {columns : Columns.t} : Set := {
    selector : columns.(Columns.Selector) -> Z -> Z;
    fixed : columns.(Columns.Fixed) -> Z -> Z;
    advice : columns.(Columns.Advice) -> Z -> Z;
    instance_ : columns.(Columns.Instance_) -> Z -> Z;
  }.
  Arguments t : clear implicits.
End Assignment.

Module Evaluation.
  Record t {columns : Columns.t} : Set := {
    assignment : Assignment.t columns;
    row : Z;
    nb_rows : Z;
  }.
  Arguments t : clear implicits.

  Class C {columns : Columns.t} {p : Z} `{Prime p}
      (A B : Type) : Type := {
    eval : t columns -> A -> B;
  }.
End Evaluation.

Notation "⟦ x ⟧ ρ" := (Evaluation.eval ρ x)
  (at level 10, x at level 200, ρ at level 9).

Definition rotated_row
    (row nb_rows : Z)
    (rotation : Rotation.t)
    : Z :=
  row + rotation.(Rotation.offset).

Section Semantics.
  Context {columns : Columns.t}.
  Context {p : Z}.
  Context `{Prime p}.

  Definition eval_selector
      (assignment : Assignment.t columns)
      (row nb_rows : Z)
      (selector : columns.(Columns.Selector))
      : Z :=
    UnOp.from
      (assignment.(Assignment.selector) selector (row mod nb_rows)).

  Fixpoint eval_expression
      (assignment : Assignment.t columns)
      (row nb_rows : Z)
      (expression : Expression.t columns)
      : Z :=
    match expression with
    | Expression.Constant value =>
        UnOp.from value
    | Expression.Selector selector =>
        eval_selector assignment row nb_rows selector
    | Expression.Fixed fixed rotation =>
        UnOp.from
          (assignment.(Assignment.fixed)
            fixed
            (rotated_row row nb_rows rotation))
    | Expression.Advice advice rotation =>
        UnOp.from
          (assignment.(Assignment.advice)
            advice
            (rotated_row row nb_rows rotation))
    | Expression.Instance_ instance rotation =>
        UnOp.from
          (assignment.(Assignment.instance_)
            instance
            (rotated_row row nb_rows rotation))
    | Expression.Sum lhs (Expression.Negated rhs) =>
        BinOp.sub
          (eval_expression assignment row nb_rows lhs)
          (eval_expression assignment row nb_rows rhs)
    | Expression.Negated expression =>
        UnOp.opp (eval_expression assignment row nb_rows expression)
    | Expression.Sum lhs rhs =>
        BinOp.add
          (eval_expression assignment row nb_rows lhs)
          (eval_expression assignment row nb_rows rhs)
    | Expression.Product lhs rhs =>
        BinOp.mul
          (eval_expression assignment row nb_rows lhs)
          (eval_expression assignment row nb_rows rhs)
    | Expression.Scaled expression scale =>
        BinOp.mul
          (eval_expression assignment row nb_rows expression)
          (UnOp.from scale)
    end.

  Fixpoint eval_constraint
      (assignment : Assignment.t columns)
      (row nb_rows : Z)
      (constraint : Constraint.t columns)
      : Prop :=
    match constraint with
    | Constraint.Select selector constraint =>
        eval_selector assignment row nb_rows selector <> 0 ->
          eval_constraint assignment row nb_rows constraint
    | Constraint.Equal lhs rhs =>
        eval_expression assignment row nb_rows lhs =
          eval_expression assignment row nb_rows rhs
    | Constraint.Boolean expression =>
        IsBool.t (eval_expression assignment row nb_rows expression)
    | Constraint.Range expression range =>
        0 <= eval_expression assignment row nb_rows expression < Z.of_nat range
    | Constraint.Either lhs rhs =>
        eval_constraint assignment row nb_rows lhs \/
          eval_constraint assignment row nb_rows rhs
    | Constraint.EqualZeroToPrecise expression =>
        eval_expression assignment row nb_rows expression = 0
    end.
  Arguments eval_constraint _ _ _ _ /.

  Definition eval_named_constraint
      (assignment : Assignment.t columns)
      (row nb_rows : Z)
      (constraint : option string * Constraint.t columns)
      : Prop :=
    let '(_, constraint) := constraint in
    eval_constraint assignment row nb_rows constraint.
  Arguments eval_named_constraint _ _ _ _ /.

  Fixpoint eval_constraints
      (assignment : Assignment.t columns)
      (row nb_rows : Z)
      (constraints : Constraints.t columns)
      : Prop :=
    match constraints with
    | [] => True
    | [constraint] =>
        eval_named_constraint assignment row nb_rows constraint
    | constraint :: constraints =>
        eval_named_constraint assignment row nb_rows constraint /\
        eval_constraints assignment row nb_rows constraints
    end.
  Arguments eval_constraints _ _ _ _ /.

  Definition eval_gate
      (assignment : Assignment.t columns)
      (row nb_rows : Z)
      (gate : Gate.t columns)
      : Prop :=
    eval_constraints
      assignment
      row
      nb_rows
      gate.(Gate.constraints).
  Arguments eval_gate _ _ _ _ /.

  Fixpoint eval_gates
      (assignment : Assignment.t columns)
      (row nb_rows : Z)
      (gates : list (Gate.t columns))
      : Prop :=
    match gates with
    | [] => True
    | [gate] =>
        eval_gate assignment row nb_rows gate
    | gate :: gates =>
        eval_gate assignment row nb_rows gate /\
        eval_gates assignment row nb_rows gates
    end.
  Arguments eval_gates _ _ _ _ /.

  Definition eval_constraint_system_gates
      (assignment : Assignment.t columns)
      (nb_rows : Z)
      (system : ConstraintSystem.t columns)
      : Prop :=
    forall row,
      0 <= row < nb_rows ->
      eval_gates
        assignment
        row
        nb_rows
        system.(ConstraintSystem.gates).

  Global Instance SelectorIsEvaluable :
      Evaluation.C columns.(Columns.Selector) Z := {
    Evaluation.eval ρ selector :=
      eval_selector
        ρ.(Evaluation.assignment)
        ρ.(Evaluation.row)
        ρ.(Evaluation.nb_rows)
        selector;
  }.

  Global Instance ExpressionIsEvaluable :
      Evaluation.C (Expression.t columns) Z := {
    Evaluation.eval ρ expression :=
      eval_expression
        ρ.(Evaluation.assignment)
        ρ.(Evaluation.row)
        ρ.(Evaluation.nb_rows)
        expression;
  }.

  Global Instance ConstraintIsEvaluable :
      Evaluation.C (Constraint.t columns) Prop := {
    Evaluation.eval ρ constraint :=
      eval_constraint
        ρ.(Evaluation.assignment)
        ρ.(Evaluation.row)
        ρ.(Evaluation.nb_rows)
        constraint;
  }.

  Global Instance NamedConstraintIsEvaluable :
      Evaluation.C (option string * Constraint.t columns) Prop := {
    Evaluation.eval ρ constraint :=
      eval_named_constraint
        ρ.(Evaluation.assignment)
        ρ.(Evaluation.row)
        ρ.(Evaluation.nb_rows)
        constraint;
  }.

  Global Instance ConstraintsIsEvaluable :
      Evaluation.C (Constraints.t columns) Prop := {
    Evaluation.eval ρ constraints :=
      eval_constraints
        ρ.(Evaluation.assignment)
        ρ.(Evaluation.row)
        ρ.(Evaluation.nb_rows)
        constraints;
  }.

  Global Instance GateIsEvaluable :
      Evaluation.C (Gate.t columns) Prop := {
    Evaluation.eval ρ gate :=
      eval_gate
        ρ.(Evaluation.assignment)
        ρ.(Evaluation.row)
        ρ.(Evaluation.nb_rows)
        gate;
  }.

  Global Instance GatesIsEvaluable :
      Evaluation.C (list (Gate.t columns)) Prop := {
    Evaluation.eval ρ gates :=
      eval_gates
        ρ.(Evaluation.assignment)
        ρ.(Evaluation.row)
        ρ.(Evaluation.nb_rows)
        gates;
  }.
End Semantics.
