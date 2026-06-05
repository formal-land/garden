Require Import Stdlib.Lists.List.
Require Import Stdlib.Strings.PrimString.
Require Import Stdlib.ZArith.ZArith.
Require Import Garden.Halo2.DSL.
Require Import Garden.Halo2.Gadgets.Ecc.
Require Import Garden.Orchard.constants.
Require Import Garden.Orchard.circuit.commit_ivk.
Require Import Garden.Orchard.circuit.note_commit.
Require Import Garden.Orchard.circuit.gadget.add_chip.

Import ListNotations.
Export PStringNotations.
Global Open Scope pstring_scope.
Global Open Scope Z_scope.

Definition assign_free_advice (name : string) (column : Column.t) : Synth.Event.t :=
  Synth.Event.Namespace name [
    Synth.Event.Region "load private" [
      RegionEvent.AssignAdvice "load private" column 0
    ];
    Synth.Event.Return name
  ].

Definition value_commit_orchard : Synth.Event.t :=
  Synth.Event.Namespace "cv_net = ValueCommit^Orchard_rcv(v_net)" [
    Ecc.fixed_mul "[v] ValueCommitV" FixedBase.ValueCommitV "v_net";
    Ecc.fixed_mul "[rcv] ValueCommitR" FixedBase.ValueCommitR "rcv";
    Ecc.add "cv" "[v] ValueCommitV" "[rcv] ValueCommitR";
    Synth.Event.Return "cv_net"
  ].

Definition derive_nullifier (add_config : AddConfig.t) : Synth.Event.t :=
  Synth.Event.Namespace "nf_old = DeriveNullifier_nk(rho_old, psi_old, cm_old)" [
    Synth.Event.Namespace "Poseidon init" [
      Synth.Event.Call "PoseidonHash::init" ["Poseidon Pow5Chip"];
      Synth.Event.Return "poseidon_hasher"
    ];
    Synth.Event.Namespace "Poseidon hash (nk, rho)" [
      Synth.Event.Call "PoseidonHash::hash" ["nk"; "rho_old"];
      Synth.Event.Return "poseidon output"
    ];
    AddChip.add
      add_config
      (CellRef.named "poseidon_hash(nk, rho)")
      (CellRef.named "psi_old");
    Ecc.fixed_mul
      "[poseidon_output + psi] NullifierK"
      FixedBase.NullifierK
      "poseidon_hash(nk, rho) + psi";
    Ecc.add
      "nf"
      "cm_old"
      "[poseidon_output + psi] NullifierK";
    Synth.Event.Return "nf_old"
  ].

Definition commit_ivk (cfg : CommitIvkConfig.t) : Synth.Event.t :=
  Gadgets.commit_ivk cfg.

Definition note_commit (cfg : NoteCommitConfig.t) : Synth.Event.t :=
  note_commit.Gadgets.note_commit cfg.
