Require Import Stdlib.Lists.List.
Require Import Stdlib.Strings.PrimString.
Require Import Stdlib.ZArith.ZArith.
Require Import Garden.Halo2.DSL.
Require Import Garden.Halo2.Gadgets.Sinsemilla.

Import ListNotations.
Export PStringNotations.
Global Open Scope pstring_scope.
Global Open Scope Z_scope.

Module MerkleConfig.
  Record t : Set := {
    sinsemilla_config : SinsemillaConfig.t;
    q_decomposition : Selector.t;
    depth : Z;
  }.
End MerkleConfig.

Definition configure
    (sinsemilla_config : SinsemillaConfig.t)
    (selector_index : Z)
    (depth : Z)
    : MerkleConfig.t * Config.Trace :=
  let q_decomposition := Selector.make selector_index "q_merkle_decomposition" in
  ({|
    MerkleConfig.sinsemilla_config := sinsemilla_config;
    MerkleConfig.q_decomposition := q_decomposition;
    MerkleConfig.depth := depth;
  |},
  [
    Config.Event.Selector q_decomposition;
    Config.Event.ConfigureChip
      "MerkleChip"
      "Merkle path root calculation backed by Sinsemilla"
      [
        "halo2_gadgets::sinsemilla::merkle";
        "halo2_gadgets::sinsemilla::merkle::chip"
      ];
    Config.Event.CreateGate (Gate.make
      "Decomposition check"
      (Some q_decomposition)
      [GateConstraint.make
        "decompose position bits and select left/right child"
        (Expr.Named "Merkle path decomposition" (Expr.named_cell "position_bit"))])
  ]).

Definition calculate_root (cfg : MerkleConfig.t) (name leaf : string) : Synth.Event.t :=
  Synth.Event.Namespace name [
    Synth.Event.Call "MerklePath::construct" ["two MerkleChip instances"; "OrchardHashDomains::MerkleCrh"];
    Synth.Event.Call "MerklePath::calculate_root" [leaf];
    Synth.Event.Region "Merkle path row" [
      RegionEvent.Note "decompose position bit and choose sibling ordering";
      RegionEvent.Note "hash each level with Sinsemilla"
    ];
    Synth.Event.Return "calculated root"
  ].
