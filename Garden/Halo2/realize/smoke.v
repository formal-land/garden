(** * Replay smoke test: the add chip under the concrete Orchard placement.

    The add chip is the minimal subject for the event replay: a single
    region, one gate ([a + b = c] under [Selector.QAdd]), three advice
    cells, no lookup tables and no constants.  Its serialized events are
    replayed onto [initial_grid] by [vm_compute], and the [instance_free] /
    [flattening_ok] decision procedures are computed on its constraint
    system. *)

Require Import Garden.Halo2.main.
Require Import Garden.Halo2.Synthesis.
Require Import Garden.Halo2.serialize.
Require Import Garden.Halo2.realize.main.
Require Import Garden.Orchard.columns.
Require Import Garden.Orchard.circuit_synthesis_layout.
Require Garden.Orchard.circuit.gadget.add_chip.

Import ListNotations.
Global Open Scope Z_scope.

(** The serialized synthesis events of the add chip, under the concrete
    Orchard column indexes and region placement.  The witness values passed
    to [synthesize] do not occur in the events — advice is free witness, not
    an event. *)
Definition add_chip_events : list Raw.Event.t :=
  snd
    (V1.eval_layouter Index.indices region_start_of
      (Garden.Orchard.circuit.gadget.add_chip.synthesize 0 0 0)).

(** The add chip's constraint system: the single addition gate. *)
Definition add_chip_system : ConstraintSystem.t columns :=
  𝓒.run_unit
    Garden.Orchard.circuit.gadget.add_chip.configure
    ConstraintSystem.empty.

(** Replay of the add chip's events succeeds on any witness: no write
    collides.  The conflict check never reads the witness planes, so the
    verdict computes with [advice] and [instance_] symbolic. *)
Lemma add_chip_replay_ok (advice instance_ : Z -> Z -> Z) :
  replay_is_ok add_chip_events (initial_grid advice instance_) = true.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma add_chip_replay_some (advice instance_ : Z -> Z -> Z) :
  exists grid,
    apply_events add_chip_events (initial_grid advice instance_) = Some grid.
Proof.
  apply replay_is_ok_some, add_chip_replay_ok.
Qed.

(** The add chip's gate mentions no instance column. *)
Lemma add_chip_instance_free : instance_free add_chip_system.
Proof.
  vm_compute.
  reflexivity.
Qed.

(** The add chip's gate contains no [Constraint.Range _ 0]. *)
Lemma add_chip_flattening_ok : flattening_ok add_chip_system.
Proof.
  vm_compute.
  reflexivity.
Qed.
