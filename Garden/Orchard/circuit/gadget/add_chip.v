Require Import Garden.Halo2.main.

Import ListNotations.
Global Open Scope pstring_scope.

Definition configure {columns : Columns.t}
    (meta : ConstraintSystem.t columns)
    (q_add : columns.(Columns.Selector))
    (a b c : columns.(Columns.Advice))
    : ConstraintSystem.t columns :=
  let meta := ConstraintSystem.create_gate meta {|
    Gate.name := "Field element addition: c = a + b";
    Gate.constraints :=
      let a := Expression.Advice a Rotation.cur in
      let b := Expression.Advice b Rotation.cur in
      let c := Expression.Advice c Rotation.cur in
      Constraints.with_selector q_add [
        (None, a +E b -E c)
      ];
  |} in
  meta.
