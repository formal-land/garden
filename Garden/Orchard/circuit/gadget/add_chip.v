Require Import Stdlib.Lists.List.
Require Import Stdlib.Strings.PrimString.
Require Import Stdlib.ZArith.ZArith.
Require Import Garden.Halo2.DSL.

Import ListNotations.
Export PStringNotations.
Global Open Scope pstring_scope.
Global Open Scope Z_scope.

Module AddConfig.
  Record t : Set := {
    a : Column.t;
    b : Column.t;
    c : Column.t;
    q_add : Selector.t;
  }.
End AddConfig.

Module AddChip.
  Record t : Set := {
    config : AddConfig.t;
  }.

  Definition gate (cfg : AddConfig.t) : Gate.t :=
    let a := Expr.advice cfg.(AddConfig.a) Rotation.Cur in
    let b := Expr.advice cfg.(AddConfig.b) Rotation.Cur in
    let c := Expr.advice cfg.(AddConfig.c) Rotation.Cur in
    Gate.make
      "Field element addition: c = a + b"
      (Some cfg.(AddConfig.q_add))
      [GateConstraint.make "a + b - c = 0" (a +H b -H c)].

  Definition configure
      (selector_index : Z)
      (a b c : Column.t)
      : AddConfig.t * Config.Trace :=
    let q_add := Selector.make selector_index "q_add" in
    let cfg := {|
      AddConfig.a := a;
      AddConfig.b := b;
      AddConfig.c := c;
      AddConfig.q_add := q_add;
    |} in
    (cfg, [
      Config.Event.Selector q_add;
      Config.Event.ConfigureChip
        "AddChip"
        "single-row field addition constraint c = a + b"
        ["orchard::circuit::gadget::add_chip"];
      Config.Event.CreateGate (gate cfg)
    ]).

  Definition construct (cfg : AddConfig.t) : t := {|
    config := cfg;
  |}.

  Definition add (cfg : AddConfig.t) (a b : CellRef.t) : Synth.Event.t :=
    Synth.Event.Region "c = a + b" [
      RegionEvent.EnableSelector cfg.(AddConfig.q_add) 0;
      RegionEvent.CopyAdvice "copy a" a cfg.(AddConfig.a) 0;
      RegionEvent.CopyAdvice "copy b" b cfg.(AddConfig.b) 0;
      RegionEvent.AssignAdvice "c" cfg.(AddConfig.c) 0
    ].

  Definition as_chip (cfg : AddConfig.t) : Chip.t := {|
    Chip.name := "AddChip";
    Chip.config_name := "AddConfig";
    Chip.dependencies := ["orchard::circuit::gadget::AddInstruction"];
    Chip.configure := [Config.Event.CreateGate (gate cfg)];
    Chip.synthesize := [add cfg (CellRef.named "a") (CellRef.named "b")];
  |}.
End AddChip.
