Require Import Stdlib.Lists.List.
Require Import Stdlib.Strings.PrimString.
Require Import Stdlib.ZArith.ZArith.
Require Import Garden.Halo2.DSL.

Import ListNotations.
Export PStringNotations.
Global Open Scope pstring_scope.
Global Open Scope Z_scope.

Module Pow5Config.
  Record t : Set := {
    state : list Column.t;
    partial_sbox : Column.t;
    rc_a : list Column.t;
    rc_b : list Column.t;
    width : Z;
    rate : Z;
  }.
End Pow5Config.

Definition configure
    (state : list Column.t)
    (partial_sbox : Column.t)
    (rc_a rc_b : list Column.t)
    (width rate : Z)
    : Pow5Config.t * Config.Trace :=
  let round_expr := Expr.Named "Poseidon round transition" (Expr.named_cell "state_after_round") in
  let partial_expr := Expr.Named "partial S-box transition" (Expr.named_cell "partial_sbox") in
  let pad_expr := Expr.Named "pad-and-add message into sponge state" (Expr.named_cell "message_word") in
  ({|
    Pow5Config.state := state;
    Pow5Config.partial_sbox := partial_sbox;
    Pow5Config.rc_a := rc_a;
    Pow5Config.rc_b := rc_b;
    Pow5Config.width := width;
    Pow5Config.rate := rate;
  |},
  [
    Config.Event.ConfigureChip
      "Poseidon Pow5Chip"
      "Poseidon P128Pow5T3 sponge constraints"
      ["halo2_gadgets::poseidon::pow5"; "pasta_curves::pallas::Base"];
    Config.Event.CreateGate (Gate.make
      "full round"
      None
      [GateConstraint.make "apply full S-box and MDS layer" round_expr]);
    Config.Event.CreateGate (Gate.make
      "partial rounds"
      None
      [GateConstraint.make "apply one partial S-box and MDS layer" partial_expr]);
    Config.Event.CreateGate (Gate.make
      "pad-and-add"
      None
      [GateConstraint.make "absorb message into sponge state" pad_expr])
  ]).

Definition init (cfg : Pow5Config.t) : Synth.Event.t :=
  Synth.Event.Namespace "Poseidon init" [
    Synth.Event.ConstructChip "Poseidon Pow5Chip";
    Synth.Event.Call
      "PoseidonHash::init"
      [cfg.(Pow5Config.partial_sbox).(Column.label)];
    Synth.Event.Return "poseidon_hasher"
  ].

Definition hash (cfg : Pow5Config.t) (name : string) (message : list string) : Synth.Event.t :=
  Synth.Event.Namespace name [
    Synth.Event.Call
      "PoseidonHash::hash"
      (["width=3"; "rate=2"] ++ message);
    Synth.Event.Region "Poseidon pad-and-add" [
      RegionEvent.Note "absorb message words into the rate columns"
    ];
    Synth.Event.Region "Poseidon rounds" [
      RegionEvent.Note "apply full and partial round gates"
    ];
    Synth.Event.Return "poseidon output cell"
  ].
