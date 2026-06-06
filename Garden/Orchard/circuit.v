Require Import Garden.Halo2.main.
Require Garden.Orchard.circuit.gadget.add_chip.

Import ListNotations.
Global Open Scope pstring_scope.
Global Open Scope Z_scope.

Module Advice.
  Inductive t : Set :=
  | A0
  | A1
  | A2
  | A3
  | A4
  | A5
  | A6
  | A7
  | A8
  | A9.

  Definition to_index (self : t) : Z :=
    match self with
    | A0 => 0
    | A1 => 1
    | A2 => 2
    | A3 => 3
    | A4 => 4
    | A5 => 5
    | A6 => 6
    | A7 => 7
    | A8 => 8
    | A9 => 9
    end.
End Advice.

Module Lookup.
  Inductive t : Set :=
  | TableIdx
  | TableX
  | TableY.

  Definition to_index (self : t) : Z :=
    match self with
    | TableIdx => 0
    | TableX => 1
    | TableY => 2
    end.
End Lookup.

Module Fixed.
  Inductive t : Set :=
  | LagrangeCoeffs0
  | LagrangeCoeffs1
  | LagrangeCoeffs2
  | LagrangeCoeffs3
  | LagrangeCoeffs4
  | LagrangeCoeffs5
  | LagrangeCoeffs6
  | LagrangeCoeffs7.

  Definition to_index (self : t) : Z :=
    match self with
    | LagrangeCoeffs0 => 0
    | LagrangeCoeffs1 => 1
    | LagrangeCoeffs2 => 2
    | LagrangeCoeffs3 => 3
    | LagrangeCoeffs4 => 4
    | LagrangeCoeffs5 => 5
    | LagrangeCoeffs6 => 6
    | LagrangeCoeffs7 => 7
    end.
End Fixed.

Module Instance_.
  Inductive t : Set :=
  | Primary.

  Definition to_index (self : t) : Z :=
    match self with
    | Primary => 0
    end.
End Instance_.

Module Selector.
  Inductive t : Set :=
  | QOrchard
  | QAdd.

  Definition to_index (self : t) : Z :=
    match self with
    | QOrchard => 0
    | QAdd => 1
    end.
End Selector.

Definition columns : Columns.t := {|
  Columns.Selector := Selector.t;
  Columns.Fixed := Fixed.t;
  Columns.Advice := Advice.t;
  Columns.Instance_ := Instance_.t;
|}.
Canonical columns.

Definition configure
    (meta : ConstraintSystem.t columns)
    : ConstraintSystem.t columns :=
  let meta := ConstraintSystem.create_gate meta {|
    Gate.name := "Orchard circuit checks";
    Gate.constraints :=
      let v_old := Expression.Advice Advice.A0 Rotation.cur in
      let v_new := Expression.Advice Advice.A1 Rotation.cur in
      let magnitude := Expression.Advice Advice.A2 Rotation.cur in
      let sign := Expression.Advice Advice.A3 Rotation.cur in
      let root := Expression.Advice Advice.A4 Rotation.cur in
      let anchor := Expression.Advice Advice.A5 Rotation.cur in
      let enable_spends := Expression.Advice Advice.A6 Rotation.cur in
      let enable_outputs := Expression.Advice Advice.A7 Rotation.cur in
      Constraints.with_selector Selector.QOrchard [
        (Some "v_old - v_new = magnitude * sign",
          v_old -E v_new -E (magnitude *E sign));
        (Some "Either v_old = 0, or root = anchor",
          v_old *E (root -E anchor));
        (Some "v_old = 0 or enable_spends = 1",
          v_old *E (Expression.Constant 1 -E enable_spends));
        (Some "v_new = 0 or enable_outputs = 1",
          v_new *E (Expression.Constant 1 -E enable_outputs))
      ];
  |} in
  let meta :=
    Garden.Orchard.circuit.gadget.add_chip.configure
      meta
      Selector.QAdd
      Advice.A7
      Advice.A8
      Advice.A6 in
  meta.
