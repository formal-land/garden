Require Import Garden.Halo2.main.
Require Garden.Halo2.Gadgets.LookupRangeCheck.
Require Garden.Halo2.Gadgets.Ecc.chip.
Require Garden.Halo2.Gadgets.Poseidon.Pow5.
Require Garden.Halo2.Gadgets.Sinsemilla.chip.
Require Garden.Halo2.Gadgets.Sinsemilla.merkle.chip.
Require Import Garden.Orchard.columns.
Require Garden.Orchard.circuit.commit_ivk.
Require Garden.Orchard.circuit.gadget.add_chip.
Require Garden.Orchard.circuit.note_commit.

Import ListNotations.
Global Open Scope pstring_scope.
Global Open Scope Z_scope.

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
          Constraint.EqualZeroToPrecise
            (v_old ➖ v_new ➖ (magnitude ✖️ sign)));
        (Some "Either v_old = 0, or root = anchor",
          Constraint.EqualZeroToPrecise (v_old ✖️ (root ➖ anchor)));
        (Some "v_old = 0 or enable_spends = 1",
          Constraint.EqualZeroToPrecise
            (v_old ✖️ (Expression.Constant 1 ➖ enable_spends)));
        (Some "v_new = 0 or enable_outputs = 1",
          Constraint.EqualZeroToPrecise
            (v_new ✖️ (Expression.Constant 1 ➖ enable_outputs)))
      ];
  |} in
  let meta :=
    Garden.Orchard.circuit.gadget.add_chip.configure
      meta in
  let meta :=
    Garden.Halo2.Gadgets.LookupRangeCheck.configure
      10
      meta
      Selector.QLookup
      Selector.QRunning
      Selector.QBitshift
      Advice.A9
      (Fixed.Lookup Lookup.TableIdx) in
  let meta :=
    Garden.Halo2.Gadgets.Ecc.chip.configure
      meta in
  let meta :=
    Garden.Halo2.Gadgets.Poseidon.Pow5.configure
      meta in
  let meta :=
    Garden.Halo2.Gadgets.Sinsemilla.chip.configure_1
      meta in
  let meta :=
    Garden.Halo2.Gadgets.Sinsemilla.merkle.chip.configure_1
      meta in
  let meta :=
    Garden.Halo2.Gadgets.Sinsemilla.chip.configure_2
      meta in
  let meta :=
    Garden.Halo2.Gadgets.Sinsemilla.merkle.chip.configure_2
      meta in
  let meta :=
    Garden.Orchard.circuit.commit_ivk.configure
      meta in
  let meta :=
    Garden.Orchard.circuit.note_commit.configure_old
      meta in
  let meta :=
    Garden.Orchard.circuit.note_commit.configure_new
      meta in
  meta.
