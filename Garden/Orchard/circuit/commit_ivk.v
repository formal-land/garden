Require Import Stdlib.Lists.List.
Require Import Stdlib.Strings.PrimString.
Require Import Stdlib.ZArith.ZArith.
Require Import Garden.Halo2.DSL.
Require Import Garden.Halo2.Gadgets.Ecc.
Require Import Garden.Halo2.Gadgets.Sinsemilla.
Require Import Garden.Orchard.constants.

Import ListNotations.
Export PStringNotations.
Global Open Scope pstring_scope.
Global Open Scope Z_scope.

Module CommitIvkConfig.
  Record t : Set := {
    advices : list Column.t;
    q_canonicity : Selector.t;
  }.
End CommitIvkConfig.

Module CommitIvkChip.
  Record t : Set := {
    config : CommitIvkConfig.t;
  }.

  Definition canonicity_gate (cfg : CommitIvkConfig.t) : Gate.t :=
    Gate.make
      "CommitIvk canonicity check"
      (Some cfg.(CommitIvkConfig.q_canonicity))
      [
        GateConstraint.make
          "ivk is canonical in the Pallas base field"
          (Expr.Named "ivk < pallas::Base::MODULUS" (Expr.named_cell "ivk"));
        GateConstraint.make
          "Sinsemilla output is decomposed into canonicity limbs"
          (Expr.Named "CommitIvk canonicity limbs" (Expr.named_cell "z_0"))
      ].

  Definition configure
      (selector_index : Z)
      (advices : list Column.t)
      : CommitIvkConfig.t * Config.Trace :=
    let q_canonicity := Selector.make selector_index "q_commit_ivk_canonicity" in
    let cfg := {|
      CommitIvkConfig.advices := advices;
      CommitIvkConfig.q_canonicity := q_canonicity;
    |} in
    (cfg, [
      Config.Event.Selector q_canonicity;
      Config.Event.ConfigureChip
        "CommitIvkChip"
        "decomposition and canonicity checking for CommitIvk"
        [
          "orchard::circuit::commit_ivk";
          "halo2_gadgets::sinsemilla";
          "halo2_gadgets::ecc"
        ];
      Config.Event.CreateGate (canonicity_gate cfg)
    ]).

  Definition construct (cfg : CommitIvkConfig.t) : t := {|
    config := cfg;
  |}.

  Definition assign_gate (cfg : CommitIvkConfig.t) : Synth.Event.t :=
    Synth.Event.Region "CommitIvk canonicity check" [
      RegionEvent.EnableSelector cfg.(CommitIvkConfig.q_canonicity) 0;
      RegionEvent.AssignAdvice "ivk" (Column.advice 0 "ivk") 0;
      RegionEvent.Note "assign decomposition limbs used to prove canonicity"
    ].
End CommitIvkChip.

Module Gadgets.
  Definition commit_ivk (cfg : CommitIvkConfig.t) : Synth.Event.t :=
    Synth.Event.Namespace "CommitIvk" [
      Synth.Event.Call
        "gadgets::commit_ivk"
        ["ak"; "nk"; "rivk"];
      Synth.Event.Call
        "extract x-coordinate from ak"
        ["ak"];
      Sinsemilla.commit
        "Sinsemilla CommitIvk"
        Domain.CommitIvk
        "ak_x || nk"
        FixedBase.CommitIvkR;
      Ecc.fixed_mul
        "[rivk] CommitIvkR"
        FixedBase.CommitIvkR
        "rivk";
      Synth.Event.Call
        "derive ivk from commitment x-coordinate"
        ["commitment"];
      CommitIvkChip.assign_gate cfg;
      Synth.Event.Return "ivk"
    ].
End Gadgets.

Definition as_chip (cfg : CommitIvkConfig.t) : Chip.t := {|
  Chip.name := "CommitIvkChip";
  Chip.config_name := "CommitIvkConfig";
  Chip.dependencies := ["SinsemillaChip"; "EccChip"];
  Chip.configure := [Config.Event.CreateGate (CommitIvkChip.canonicity_gate cfg)];
  Chip.synthesize := [Gadgets.commit_ivk cfg];
|}.
