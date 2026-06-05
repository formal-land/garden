Require Import Stdlib.Lists.List.
Require Import Stdlib.Strings.PrimString.
Require Import Stdlib.ZArith.ZArith.
Require Import Garden.Halo2.DSL.

Import ListNotations.
Export PStringNotations.
Global Open Scope pstring_scope.
Global Open Scope Z_scope.

Module LookupRangeCheckConfig.
  Record t : Set := {
    q_lookup : Selector.t;
    advice : Column.t;
    table_idx : Column.t;
    bits : Z;
  }.
End LookupRangeCheckConfig.

Definition configure
    (bits : Z)
    (advice : Column.t)
    (table_idx : Column.t)
    (selector_index : Z)
    : LookupRangeCheckConfig.t * Config.Trace :=
  let q_lookup := Selector.complex_selector selector_index "q_lookup" in
  let current := Expr.advice advice Rotation.Cur in
  let next := Expr.advice advice Rotation.Next in
  let lookup_input :=
    Expr.Named "running_sum_lookup + short_lookup"
      (current +H next) in
  let shift_check :=
    Expr.Named "short lookup bitshift"
      (next -H (Expr.Constant (2 ^ bits) *H current)) in
  ({|
    LookupRangeCheckConfig.q_lookup := q_lookup;
    LookupRangeCheckConfig.advice := advice;
    LookupRangeCheckConfig.table_idx := table_idx;
    LookupRangeCheckConfig.bits := bits;
  |},
  [
    Config.Event.Selector q_lookup;
    Config.Event.ConfigureChip
      "LookupRangeCheckConfig"
      "K-bit lookup range check with combined running-sum and short lookups"
      ["halo2_gadgets::utilities::lookup_range_check"];
    Config.Event.CreateLookup (Lookup.make
      "decompose-combined-lookup"
      (Some q_lookup)
      [Lookup.pair_make lookup_input table_idx]);
    Config.Event.CreateGate (Gate.make
      "Short lookup bitshift"
      (Some q_lookup)
      [GateConstraint.make "word shifted by K bits" shift_check])
  ]).

Definition load_range_check_table (cfg : LookupRangeCheckConfig.t) : Synth.Trace :=
  [
    Synth.Event.Table "range check lookup table" [
      TableEvent.Note "load entries 0..2^K into the fixed lookup table";
      TableEvent.AssignCell "table_idx" cfg.(LookupRangeCheckConfig.table_idx) 0
    ]
  ].

Definition copy_check (cfg : LookupRangeCheckConfig.t) (name : string) : Synth.Event.t :=
  Synth.Event.Namespace name [
    Synth.Event.Call
      "LookupRangeCheck.copy_check"
      [cfg.(LookupRangeCheckConfig.advice).(Column.label); "copied element"];
    Synth.Event.Return "running sum decomposition cells"
  ].

Definition witness_check (cfg : LookupRangeCheckConfig.t) (name : string) : Synth.Event.t :=
  Synth.Event.Namespace name [
    Synth.Event.Call
      "LookupRangeCheck.witness_check"
      [cfg.(LookupRangeCheckConfig.advice).(Column.label); "witnessed element"];
    Synth.Event.Return "running sum decomposition cells"
  ].
