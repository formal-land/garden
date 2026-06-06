Require Import Garden.Halo2.main.
Require Garden.Halo2.Gadgets.LookupRangeCheck.
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
End Advice.

Module Lookup.
  Inductive t : Set :=
  | TableIdx
  | TableX
  | TableY.
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
  | LagrangeCoeffs7
  | Lookup (lookup : Lookup.t).
End Fixed.

Module Instance_.
  Inductive t : Set :=
  | Primary.
End Instance_.

Module Selector.
  Inductive t : Set :=
  | QOrchard
  | QAdd
  | QLookup
  | QRunning
  | QBitshift.
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
  let meta :=
    Garden.Halo2.Gadgets.LookupRangeCheck.configure
      10
      meta
      Selector.QLookup
      Selector.QRunning
      Selector.QBitshift
      Advice.A9
      (Fixed.Lookup Lookup.TableIdx) in
  meta.
