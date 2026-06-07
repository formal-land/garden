Require Import Garden.Halo2.main.
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

Definition rotated_row
    (row nb_rows : Z)
    (rotation : Rotation.t)
    : Z :=
  (row + rotation.(Rotation.offset)) mod nb_rows.

Section Semantics.
  Context {columns : Columns.t}.
  Context {p : Z}.
  Context `{Prime p}.

  Definition eval_selector
      (assignment : Assignment.t columns)
      (row : Z)
      (selector : columns.(Columns.Selector))
      : Z :=
    UnOp.from (assignment.(Assignment.selector) selector row).

  Fixpoint eval_expression
      (assignment : Assignment.t columns)
      (row nb_rows : Z)
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
        if Z.odd (eval_selector assignment row selector) then
          eval_constraint assignment row nb_rows constraint
        else
          True
    | Constraint.Equal lhs rhs =>
        eval_expression assignment row nb_rows lhs =
          eval_expression assignment row nb_rows rhs
    | Constraint.EqualZeroToPrecise expression =>
        eval_expression assignment row nb_rows expression = 0
    end.

  Definition eval_named_constraint
      (assignment : Assignment.t columns)
      (row nb_rows : Z)
      (constraint : option string * Constraint.t columns)
      : Prop :=
    let '(_, constraint) := constraint in
    eval_constraint assignment row nb_rows constraint.

  Definition eval_constraints
      (assignment : Assignment.t columns)
      (row nb_rows : Z)
      (constraints : Constraints.t columns)
      : Prop :=
    List.Forall (eval_named_constraint assignment row nb_rows) constraints.

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

  Definition eval_gates
      (assignment : Assignment.t columns)
      (row nb_rows : Z)
      (gates : list (Gate.t columns))
      : Prop :=
    List.Forall (eval_gate assignment row nb_rows) gates.

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

End Semantics.
