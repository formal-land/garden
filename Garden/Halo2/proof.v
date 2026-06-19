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
  Class C {columns : Columns.t} {p : Z} `{Prime p}
      (Index A B : Type) : Type := {
    eval : Assignment.t columns -> Index -> A -> B;
  }.
End Evaluation.

Notation "Γ ⊢ ⟦ x ⟧ ρ" := (Evaluation.eval Γ ρ x)
  (at level 10, x at level 200, ρ at level 9).

Definition rotated_row
    (row : Z)
    (rotation : Rotation.t)
    : Z :=
  row + rotation.(Rotation.offset).

Section Semantics.
  Context {columns : Columns.t}.
  Context {p : Z}.
  Context `{Prime p}.

  Definition eval_selector
      (assignment : Assignment.t columns)
      (row : Z)
      (selector : columns.(Columns.Selector))
      : Z :=
    UnOp.from
      (assignment.(Assignment.selector) selector row).

  Fixpoint eval_expression
      (assignment : Assignment.t columns)
      (row : Z)
      (expression : Expression.t columns)
      : Z :=
    match expression with
    | Expression.Constant value =>
        UnOp.from value
    | Expression.Selector selector =>
        eval_selector assignment row selector
    | Expression.Fixed fixed rotation =>
        UnOp.from
          (assignment.(Assignment.fixed)
            fixed
            (rotated_row row rotation))
    | Expression.Advice advice rotation =>
        UnOp.from
          (assignment.(Assignment.advice)
            advice
            (rotated_row row rotation))
    | Expression.Instance_ instance rotation =>
        UnOp.from
          (assignment.(Assignment.instance_)
            instance
            (rotated_row row rotation))
    | Expression.Sum lhs (Expression.Negated rhs) =>
        BinOp.sub
          (eval_expression assignment row lhs)
          (eval_expression assignment row rhs)
    | Expression.Negated expression =>
        UnOp.opp (eval_expression assignment row expression)
    | Expression.Sum lhs rhs =>
        BinOp.add
          (eval_expression assignment row lhs)
          (eval_expression assignment row rhs)
    | Expression.Product lhs rhs =>
        BinOp.mul
          (eval_expression assignment row lhs)
          (eval_expression assignment row rhs)
    | Expression.Scaled expression scale =>
        BinOp.mul
          (eval_expression assignment row expression)
          (UnOp.from scale)
    end.

  Fixpoint eval_constraint
      (assignment : Assignment.t columns)
      (row : Z)
      (constraint : Constraint.t columns)
      : Prop :=
    match constraint with
    | Constraint.Select selector constraint =>
        eval_selector assignment row selector <> 0 ->
          eval_constraint assignment row constraint
    | Constraint.Equal lhs rhs =>
        eval_expression assignment row lhs =
          eval_expression assignment row rhs
    | Constraint.Boolean expression =>
        IsBool.t (eval_expression assignment row expression)
    | Constraint.Range expression range =>
        0 <= eval_expression assignment row expression < Z.of_nat range
    | Constraint.Either lhs rhs =>
        eval_constraint assignment row lhs \/
          eval_constraint assignment row rhs
    | Constraint.EqualZeroToPrecise expression =>
        eval_expression assignment row expression = 0
    end.
  Arguments eval_constraint _ _ _ /.

  Definition eval_named_constraint
      (assignment : Assignment.t columns)
      (row : Z)
      (constraint : option string * Constraint.t columns)
      : Prop :=
    let '(_, constraint) := constraint in
    eval_constraint assignment row constraint.
  Arguments eval_named_constraint _ _ _ /.

  Fixpoint eval_constraints
      (assignment : Assignment.t columns)
      (row : Z)
      (constraints : Constraints.t columns)
      : Prop :=
    match constraints with
    | [] => True
    | [constraint] =>
        eval_named_constraint assignment row constraint
    | constraint :: constraints =>
        eval_named_constraint assignment row constraint /\
        eval_constraints assignment row constraints
    end.
  Arguments eval_constraints _ _ _ /.

  Definition eval_gate
      (assignment : Assignment.t columns)
      (row : Z)
      (gate : Gate.t columns)
      : Prop :=
    eval_constraints
      assignment
      row
      gate.(Gate.constraints).
  Arguments eval_gate _ _ _ /.

  Fixpoint eval_gates
      (assignment : Assignment.t columns)
      (row : Z)
      (gates : list (Gate.t columns))
      : Prop :=
    match gates with
    | [] => True
    | [gate] =>
        eval_gate assignment row gate
    | gate :: gates =>
        eval_gate assignment row gate /\
        eval_gates assignment row gates
    end.
  Arguments eval_gates _ _ _ /.

  Global Instance SelectorIsEvaluable :
      Evaluation.C Z columns.(Columns.Selector) Z := {
    Evaluation.eval Γ row selector :=
      eval_selector Γ row selector;
  }.

  Global Instance ExpressionIsEvaluable :
      Evaluation.C Z (Expression.t columns) Z := {
    Evaluation.eval Γ row expression :=
      eval_expression Γ row expression;
  }.

  Global Instance ConstraintIsEvaluable :
      Evaluation.C Z (Constraint.t columns) Prop := {
    Evaluation.eval Γ row constraint :=
      eval_constraint Γ row constraint;
  }.

  Global Instance NamedConstraintIsEvaluable :
      Evaluation.C Z (option string * Constraint.t columns) Prop := {
    Evaluation.eval Γ row constraint :=
      eval_named_constraint Γ row constraint;
  }.

  Global Instance ConstraintsIsEvaluable :
      Evaluation.C Z (Constraints.t columns) Prop := {
    Evaluation.eval Γ row constraints :=
      eval_constraints Γ row constraints;
  }.

  Global Instance GateIsEvaluable :
      Evaluation.C Z (Gate.t columns) Prop := {
    Evaluation.eval Γ row gate :=
      eval_gate Γ row gate;
  }.

  Global Instance GatesIsEvaluable :
      Evaluation.C Z (list (Gate.t columns)) Prop := {
    Evaluation.eval Γ row gates :=
      eval_gates Γ row gates;
  }.
End Semantics.
