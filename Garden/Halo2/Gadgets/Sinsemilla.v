Require Import Stdlib.Lists.List.
Require Import Stdlib.Strings.PrimString.
Require Import Stdlib.ZArith.ZArith.
Require Import Garden.Halo2.DSL.
Require Import Garden.Halo2.Gadgets.LookupRangeCheck.

Import ListNotations.
Export PStringNotations.
Global Open Scope pstring_scope.
Global Open Scope Z_scope.

Module SinsemillaConfig.
  Record t : Set := {
    advices : list Column.t;
    q_sinsemilla1 : Selector.t;
    q_sinsemilla2 : Selector.t;
    lookup_idx : Column.t;
    lookup_x : Column.t;
    lookup_y : Column.t;
    lookup_config : LookupRangeCheckConfig.t;
    fixed_y_q : Column.t;
    enable_generators : bool;
  }.
End SinsemillaConfig.

Definition configure
    (advices : list Column.t)
    (lookup_idx lookup_x lookup_y : Column.t)
    (lookup_config : LookupRangeCheckConfig.t)
    (fixed_y_q : Column.t)
    (selector_base : Z)
    (enable_generators : bool)
    : SinsemillaConfig.t * Config.Trace :=
  let q1 := Selector.make selector_base "q_sinsemilla1" in
  let q2 := Selector.complex_selector (selector_base + 1) "q_sinsemilla2" in
  let lookup_input :=
    Expr.Named "Sinsemilla generator lookup index"
      (Expr.named_cell "generator_table_idx") in
  let initial_y_q :=
    Expr.Named "Initial y_Q"
      (Expr.named_cell "initial_y_q") in
  let transition :=
    Expr.Named "Sinsemilla gate transition"
      (Expr.named_cell "sinsemilla_message_piece") in
  ({|
    SinsemillaConfig.advices := advices;
    SinsemillaConfig.q_sinsemilla1 := q1;
    SinsemillaConfig.q_sinsemilla2 := q2;
    SinsemillaConfig.lookup_idx := lookup_idx;
    SinsemillaConfig.lookup_x := lookup_x;
    SinsemillaConfig.lookup_y := lookup_y;
    SinsemillaConfig.lookup_config := lookup_config;
    SinsemillaConfig.fixed_y_q := fixed_y_q;
    SinsemillaConfig.enable_generators := enable_generators;
  |},
  [
    Config.Event.Selector q1;
    Config.Event.Selector q2;
    Config.Event.ConfigureChip
      "SinsemillaChip"
      "10-bit Sinsemilla hash using generator table lookups"
      [
        "halo2_gadgets::sinsemilla::chip";
        "halo2_gadgets::sinsemilla::chip::generator_table";
        "halo2_gadgets::sinsemilla::chip::hash_to_point"
      ];
    Config.Event.CreateLookup (Lookup.make
      "Sinsemilla generator table"
      (Some q2)
      [
        Lookup.pair_make lookup_input lookup_idx;
        Lookup.pair_make (Expr.named_cell "generator_x") lookup_x;
        Lookup.pair_make (Expr.named_cell "generator_y") lookup_y
      ]);
    Config.Event.CreateGate (Gate.make
      "Initial y_Q"
      (Some q1)
      [GateConstraint.make "load the domain-specific initial y-coordinate" initial_y_q]);
    Config.Event.CreateGate (Gate.make
      "Sinsemilla gate"
      (Some q2)
      [GateConstraint.make "accumulate one Sinsemilla message piece" transition])
  ]).

Definition load (cfg : SinsemillaConfig.t) : Synth.Trace :=
  [
    Synth.Event.LoadTable "Sinsemilla generator lookup table";
    Synth.Event.Table "Sinsemilla generator lookup table" [
      TableEvent.Note "load (idx, x_p, y_p) generator rows";
      TableEvent.AssignCell "idx" cfg.(SinsemillaConfig.lookup_idx) 0;
      TableEvent.AssignCell "x_p" cfg.(SinsemillaConfig.lookup_x) 0;
      TableEvent.AssignCell "y_p" cfg.(SinsemillaConfig.lookup_y) 0
    ]
  ].

Definition hash_to_point (name domain message : string) : Synth.Event.t :=
  Synth.Event.Namespace name [
    Synth.Event.Call "SinsemillaChip::hash_to_point" [domain; message];
    Synth.Event.Region "Initial y_Q" [
      RegionEvent.Note "assign domain initial point"
    ];
    Synth.Event.Region "Sinsemilla gate" [
      RegionEvent.Note "process message in 10-bit pieces with generator table lookups"
    ];
    Synth.Event.Return name
  ].

Definition commit (name domain message randomness : string) : Synth.Event.t :=
  Synth.Event.Namespace name [
    hash_to_point "Sinsemilla hash" domain message;
    Synth.Event.Call "Sinsemilla commitment" [randomness];
    Synth.Event.Return name
  ].
