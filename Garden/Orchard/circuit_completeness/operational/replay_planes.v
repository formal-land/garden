(** * Replay planes and the checker's stream algebra.

    The completeness direction of the operational bridge ("E1") starts from a
    grid produced by replaying a synthesis event stream onto witness planes
    chosen by an honest generator, and must read the generator's values back
    out of that grid.  [Halo2/realize/facts.v] carries one half of what that
    needs — every cell an event *writes* is pinned to the written value
    ([replay_selector_pinned] / [replay_fixed_pinned] / [replay_fill_pinned]).
    This file carries the complementary half, all of it generic in the
    columns, the placement and the program:

    - the free planes are invariant under replay: [apply_event] only ever
      calls [RawGrid.set_selector] / [RawGrid.set_fixed] / [RawGrid.fill_fixed]
      ([realize/main.v]), so the advice and instance planes of the final grid
      are literally the planes the replay started from ([replay_advice_plane]
      / [replay_instance_plane], and their [realize] readings);
    - the frame property for the two program-determined planes: a cell no
      event of the stream writes keeps its initial value
      ([replay_selector_unwritten] / [replay_fixed_unwritten]), with the
      written-ness test a Boolean scan of the stream ([enables_at] /
      [writes_fixed_at]) so a concrete instance discharges it by
      [vm_compute].  At the witness-initialized grid this reads as "unwritten
      selector and fixed cells are 0" ([replay_selector_zero] /
      [replay_fixed_zero]) — the replay-side content of the placed
      selector-off condition.  The [FillFromRow] arm of [writes_fixed_at] uses
      the half-open extent [[from_row, to_row)] of the keygen-faithful fill,
      so a table column past the fill's [usable_rows] bound is *unwritten*,
      not defaulted;
    - the stream algebra of the ideal checker: only the third conjunct of
      [mock_prover_accepts] ([realize/sound.v]) mentions the event list, so
      acceptance extends along [++] once the appended tail's copy obligations
      hold ([mock_prover_accepts_app]);
    - [operational_complete_events]: the projected, replay-premise-free form
      of [operational_complete] — the pair binder of [V1.eval_layouter] is
      resolved to the [snd] projection (the shape a concrete instantiation
      names its stream in, cf. [operational_sound_events] in
      [Orchard/circuit_operational.v]) and the replay premise, which
      [operational_complete] introduces and discards, is dropped.  Its
      [++]-form [operational_complete_events_app] is the statement a circuit
      whose checked stream carries a trailing constants block consumes.

    Nothing here is Orchard-specific: every lemma is quantified over the
    event stream, the initial planes and the placement, so it applies verbatim
    at any honest generator's planes.  The file is written to live at
    [Halo2/realize/planes.v]; it sits under
    [Orchard/circuit_completeness/operational/] only because of the file
    ownership discipline of the run that produced it. *)

Require Import Garden.Field.Field.
Require Import Garden.Halo2.main.
Require Import Garden.Halo2.Synthesis.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.serialize.
Require Import Garden.Halo2.realize.main.
Require Import Garden.Halo2.realize.facts.
Require Import Garden.Halo2.realize.sound.
Require Import Stdlib.micromega.Lia.

Import ListNotations.
Global Open Scope Z_scope.

(** ** The free planes are invariant under replay

    [apply_event] writes only through [RawGrid.set_selector] (the selector
    plane), [RawGrid.set_fixed] and [RawGrid.fill_fixed] (the [Fixed] plane).
    Every other plane of the grid — [Advice] and [Instance_], the free
    witness — is therefore carried through the replay unchanged. *)

Lemma apply_event_free_plane (state state' : ReplayState.t)
    (event : Raw.Event.t) (kind : Raw.ColumnKind.t) (column row : Z) :
  apply_event state event = Some state' ->
  kind <> Raw.ColumnKind.Fixed ->
  state'.(ReplayState.grid).(RawGrid.cell) kind column row =
    state.(ReplayState.grid).(RawGrid.cell) kind column row.
Proof.
  destruct event as
    [name | name | name | name | column0 row0 annotation
    | column0 row0 annotation value | left_cell right_cell
    | column0 from_row to_row value];
    cbn;
    try (intros Happly _; injection Happly as <-; reflexivity).
  - (* EnableSelector: the [cell] field is copied verbatim *)
    destruct (List.existsb (write_conflicts_write column0 row0 1)
        state.(ReplayState.log).(Log.selectors));
      intros Happly; [discriminate |].
    injection Happly as <-.
    intros _.
    reflexivity.
  - (* AssignFixed *)
    destruct (List.existsb (write_conflicts_write column0 row0 value)
        state.(ReplayState.log).(Log.fixeds));
      intros Happly; [discriminate |].
    revert Happly.
    destruct (List.existsb (write_conflicts_fill column0 row0 value)
        state.(ReplayState.log).(Log.fills));
      intros Happly; [discriminate |].
    injection Happly as <-.
    intros Hkind.
    destruct kind; [reflexivity | contradiction | reflexivity].
  - (* FillFromRow *)
    destruct (List.existsb
        (fill_conflicts_write column0 from_row to_row value)
        state.(ReplayState.log).(Log.fixeds));
      intros Happly; [discriminate |].
    revert Happly.
    destruct (List.existsb
        (fill_conflicts_fill column0 from_row to_row value)
        state.(ReplayState.log).(Log.fills));
      intros Happly; [discriminate |].
    injection Happly as <-.
    intros Hkind.
    destruct kind; [reflexivity | contradiction | reflexivity].
Qed.

Lemma apply_events_log_free_plane (events : list Raw.Event.t)
    (state state' : ReplayState.t) (kind : Raw.ColumnKind.t)
    (column row : Z) :
  apply_events_log events state = Some state' ->
  kind <> Raw.ColumnKind.Fixed ->
  state'.(ReplayState.grid).(RawGrid.cell) kind column row =
    state.(ReplayState.grid).(RawGrid.cell) kind column row.
Proof.
  revert state.
  induction events as [| event events IH]; intros state Happly Hkind;
    cbn in Happly.
  - injection Happly as <-.
    reflexivity.
  - destruct (apply_event state event) as [state1 |] eqn:Hevent;
      [| discriminate].
    rewrite (IH state1 Happly Hkind).
    exact (apply_event_free_plane state state1 event kind column row
      Hevent Hkind).
Qed.

(** The plane frame at the grid level: replay changes no non-[Fixed] plane. *)
Lemma replay_free_plane (events : list Raw.Event.t)
    (initial final : RawGrid.t) (kind : Raw.ColumnKind.t) (column row : Z) :
  apply_events events initial = Some final ->
  kind <> Raw.ColumnKind.Fixed ->
  final.(RawGrid.cell) kind column row =
    initial.(RawGrid.cell) kind column row.
Proof.
  unfold apply_events.
  destruct (apply_events_log events (ReplayState.init initial))
    as [state |] eqn:Hreplay; [| discriminate].
  intros Hfinal Hkind.
  injection Hfinal as <-.
  exact (apply_events_log_free_plane events (ReplayState.init initial) state
    kind column row Hreplay Hkind).
Qed.

(** The advice plane of a replayed grid is the advice plane the replay
    started from: advice is free witness, never an event. *)
Lemma replay_advice_plane (events : list Raw.Event.t)
    (advice instance_ : Z -> Z -> Z) (final : RawGrid.t) (column row : Z) :
  apply_events events (initial_grid advice instance_) = Some final ->
  final.(RawGrid.cell) Raw.ColumnKind.Advice column row = advice column row.
Proof.
  intros Hreplay.
  exact (replay_free_plane events (initial_grid advice instance_) final
    Raw.ColumnKind.Advice column row Hreplay ltac:(discriminate)).
Qed.

Lemma replay_instance_plane (events : list Raw.Event.t)
    (advice instance_ : Z -> Z -> Z) (final : RawGrid.t) (column row : Z) :
  apply_events events (initial_grid advice instance_) = Some final ->
  final.(RawGrid.cell) Raw.ColumnKind.Instance_ column row =
    instance_ column row.
Proof.
  intros Hreplay.
  exact (replay_free_plane events (initial_grid advice instance_) final
    Raw.ColumnKind.Instance_ column row Hreplay ltac:(discriminate)).
Qed.

(** The same two facts as readings of the realized assignment: the advice
    cell of [realize idx rs final] at [(column, region, offset)] is the chosen
    advice plane at the placed absolute row, and the instance cell is the
    chosen instance plane at the absolute row (no [region_start] on either
    side).  These are the equations the grid-identification obligation
    consumes to replace an advice/instance read of the realized assignment by
    a read of the generator's plane. *)
Lemma realize_advice_of_replay {columns : Columns.t} {RegionId : Set}
    (idx : Indices.t columns) (rs : RegionId -> Z)
    (events : list Raw.Event.t) (advice instance_ : Z -> Z -> Z)
    (final : RawGrid.t)
    (column : columns.(Columns.Advice)) (region : RegionId) (offset : Z) :
  apply_events events (initial_grid advice instance_) = Some final ->
  (realize idx rs final).(Assignment.advice) column region offset =
    advice (idx.(Indices.advice) column) (rs region + offset).
Proof.
  intros Hreplay.
  exact (replay_advice_plane events advice instance_ final
    (idx.(Indices.advice) column) (rs region + offset) Hreplay).
Qed.

Lemma realize_instance_of_replay {columns : Columns.t} {RegionId : Set}
    (idx : Indices.t columns) (rs : RegionId -> Z)
    (events : list Raw.Event.t) (advice instance_ : Z -> Z -> Z)
    (final : RawGrid.t)
    (column : columns.(Columns.Instance_)) (row : Z) :
  apply_events events (initial_grid advice instance_) = Some final ->
  (realize idx rs final).(Assignment.instance_) column row =
    instance_ (idx.(Indices.instance_) column) row.
Proof.
  intros Hreplay.
  exact (replay_instance_plane events advice instance_ final
    (idx.(Indices.instance_) column) row Hreplay).
Qed.

(** ** Which events write a given cell

    The Boolean tests below decide, per event, whether it writes the selector
    cell [(column, row)] resp. the [Fixed] cell [(column, row)].  The
    [FillFromRow] arm uses the half-open extent [[from_row, to_row)] of
    [RawGrid.fill_fixed] — the keygen-faithful fill — so rows at or past a
    fill's [to_row] bound count as unwritten. *)

Definition enables_at (column row : Z) (event : Raw.Event.t) : bool :=
  match event with
  | Raw.Event.EnableSelector c r _ => andb (column =? c) (row =? r)
  | _ => false
  end.

Definition writes_fixed_at (column row : Z) (event : Raw.Event.t) : bool :=
  match event with
  | Raw.Event.AssignFixed c r _ _ => andb (column =? c) (row =? r)
  | Raw.Event.FillFromRow c from_row to_row _ =>
      andb (column =? c) (andb (from_row <=? row) (row <? to_row))
  | _ => false
  end.

(** ** The frame property for the program-determined planes *)

Lemma apply_event_selector_frame (state state' : ReplayState.t)
    (event : Raw.Event.t) (column row : Z) :
  apply_event state event = Some state' ->
  enables_at column row event = false ->
  state'.(ReplayState.grid).(RawGrid.sel) column row =
    state.(ReplayState.grid).(RawGrid.sel) column row.
Proof.
  destruct event as
    [name | name | name | name | column0 row0 annotation
    | column0 row0 annotation value | left_cell right_cell
    | column0 from_row to_row value];
    cbn [apply_event enables_at];
    try (intros Happly _; injection Happly as <-; reflexivity).
  - (* EnableSelector *)
    destruct (List.existsb (write_conflicts_write column0 row0 1)
        state.(ReplayState.log).(Log.selectors));
      intros Happly; [discriminate |].
    injection Happly as <-.
    intros Hfree.
    cbn [ReplayState.grid RawGrid.set_selector RawGrid.sel].
    rewrite Hfree.
    reflexivity.
  - (* AssignFixed: the selector plane is copied verbatim *)
    destruct (List.existsb (write_conflicts_write column0 row0 value)
        state.(ReplayState.log).(Log.fixeds));
      intros Happly; [discriminate |].
    revert Happly.
    destruct (List.existsb (write_conflicts_fill column0 row0 value)
        state.(ReplayState.log).(Log.fills));
      intros Happly; [discriminate |].
    injection Happly as <-.
    intros _.
    reflexivity.
  - (* FillFromRow: the selector plane is copied verbatim *)
    destruct (List.existsb
        (fill_conflicts_write column0 from_row to_row value)
        state.(ReplayState.log).(Log.fixeds));
      intros Happly; [discriminate |].
    revert Happly.
    destruct (List.existsb
        (fill_conflicts_fill column0 from_row to_row value)
        state.(ReplayState.log).(Log.fills));
      intros Happly; [discriminate |].
    injection Happly as <-.
    intros _.
    reflexivity.
Qed.

Lemma apply_event_fixed_frame (state state' : ReplayState.t)
    (event : Raw.Event.t) (column row : Z) :
  apply_event state event = Some state' ->
  writes_fixed_at column row event = false ->
  state'.(ReplayState.grid).(RawGrid.cell) Raw.ColumnKind.Fixed column row =
    state.(ReplayState.grid).(RawGrid.cell) Raw.ColumnKind.Fixed column row.
Proof.
  destruct event as
    [name | name | name | name | column0 row0 annotation
    | column0 row0 annotation value | left_cell right_cell
    | column0 from_row to_row value];
    cbn [apply_event writes_fixed_at];
    try (intros Happly _; injection Happly as <-; reflexivity).
  - (* EnableSelector: the [cell] field is copied verbatim *)
    destruct (List.existsb (write_conflicts_write column0 row0 1)
        state.(ReplayState.log).(Log.selectors));
      intros Happly; [discriminate |].
    injection Happly as <-.
    intros _.
    reflexivity.
  - (* AssignFixed *)
    destruct (List.existsb (write_conflicts_write column0 row0 value)
        state.(ReplayState.log).(Log.fixeds));
      intros Happly; [discriminate |].
    revert Happly.
    destruct (List.existsb (write_conflicts_fill column0 row0 value)
        state.(ReplayState.log).(Log.fills));
      intros Happly; [discriminate |].
    injection Happly as <-.
    intros Hfree.
    cbn [ReplayState.grid RawGrid.set_fixed RawGrid.cell].
    rewrite Hfree.
    reflexivity.
  - (* FillFromRow *)
    destruct (List.existsb
        (fill_conflicts_write column0 from_row to_row value)
        state.(ReplayState.log).(Log.fixeds));
      intros Happly; [discriminate |].
    revert Happly.
    destruct (List.existsb
        (fill_conflicts_fill column0 from_row to_row value)
        state.(ReplayState.log).(Log.fills));
      intros Happly; [discriminate |].
    injection Happly as <-.
    intros Hfree.
    cbn [ReplayState.grid RawGrid.fill_fixed RawGrid.cell].
    rewrite Hfree.
    reflexivity.
Qed.

Lemma apply_events_log_selector_frame (events : list Raw.Event.t)
    (state state' : ReplayState.t) (column row : Z) :
  apply_events_log events state = Some state' ->
  List.existsb (enables_at column row) events = false ->
  state'.(ReplayState.grid).(RawGrid.sel) column row =
    state.(ReplayState.grid).(RawGrid.sel) column row.
Proof.
  revert state.
  induction events as [| event events IH]; intros state Happly Hfree;
    cbn in Happly.
  - injection Happly as <-.
    reflexivity.
  - destruct (apply_event state event) as [state1 |] eqn:Hevent;
      [| discriminate].
    cbn [List.existsb] in Hfree.
    destruct (enables_at column row event) eqn:Hhead;
      cbn in Hfree; [discriminate |].
    rewrite (IH state1 Happly Hfree).
    exact (apply_event_selector_frame state state1 event column row
      Hevent Hhead).
Qed.

Lemma apply_events_log_fixed_frame (events : list Raw.Event.t)
    (state state' : ReplayState.t) (column row : Z) :
  apply_events_log events state = Some state' ->
  List.existsb (writes_fixed_at column row) events = false ->
  state'.(ReplayState.grid).(RawGrid.cell) Raw.ColumnKind.Fixed column row =
    state.(ReplayState.grid).(RawGrid.cell) Raw.ColumnKind.Fixed column row.
Proof.
  revert state.
  induction events as [| event events IH]; intros state Happly Hfree;
    cbn in Happly.
  - injection Happly as <-.
    reflexivity.
  - destruct (apply_event state event) as [state1 |] eqn:Hevent;
      [| discriminate].
    cbn [List.existsb] in Hfree.
    destruct (writes_fixed_at column row event) eqn:Hhead;
      cbn in Hfree; [discriminate |].
    rewrite (IH state1 Happly Hfree).
    exact (apply_event_fixed_frame state state1 event column row
      Hevent Hhead).
Qed.

(** A selector cell no [EnableSelector] event of the stream targets keeps the
    value it had in the initial grid — the converse of
    [replay_selector_pinned]. *)
Lemma replay_selector_unwritten (events : list Raw.Event.t)
    (initial final : RawGrid.t) (column row : Z) :
  apply_events events initial = Some final ->
  List.existsb (enables_at column row) events = false ->
  final.(RawGrid.sel) column row = initial.(RawGrid.sel) column row.
Proof.
  unfold apply_events.
  destruct (apply_events_log events (ReplayState.init initial))
    as [state |] eqn:Hreplay; [| discriminate].
  intros Hfinal Hfree.
  injection Hfinal as <-.
  exact (apply_events_log_selector_frame events (ReplayState.init initial)
    state column row Hreplay Hfree).
Qed.

(** A [Fixed] cell no [AssignFixed] event targets and no [FillFromRow]
    event's half-open extent covers keeps the value it had in the initial
    grid — the converse of [replay_fixed_pinned] / [replay_fill_pinned]. *)
Lemma replay_fixed_unwritten (events : list Raw.Event.t)
    (initial final : RawGrid.t) (column row : Z) :
  apply_events events initial = Some final ->
  List.existsb (writes_fixed_at column row) events = false ->
  final.(RawGrid.cell) Raw.ColumnKind.Fixed column row =
    initial.(RawGrid.cell) Raw.ColumnKind.Fixed column row.
Proof.
  unfold apply_events.
  destruct (apply_events_log events (ReplayState.init initial))
    as [state |] eqn:Hreplay; [| discriminate].
  intros Hfinal Hfree.
  injection Hfinal as <-.
  exact (apply_events_log_fixed_frame events (ReplayState.init initial)
    state column row Hreplay Hfree).
Qed.

(** At the witness-initialized grid both program-determined planes start at
    zero, so an unwritten cell reads zero.  [replay_selector_zero] is the
    replay-side content of the placed selector-off condition: off the absolute
    rows the stream enables, the realized selector plane is 0. *)
Lemma replay_selector_zero (events : list Raw.Event.t)
    (advice instance_ : Z -> Z -> Z) (final : RawGrid.t) (column row : Z) :
  apply_events events (initial_grid advice instance_) = Some final ->
  List.existsb (enables_at column row) events = false ->
  final.(RawGrid.sel) column row = 0.
Proof.
  intros Hreplay Hfree.
  exact (replay_selector_unwritten events (initial_grid advice instance_)
    final column row Hreplay Hfree).
Qed.

Lemma replay_fixed_zero (events : list Raw.Event.t)
    (advice instance_ : Z -> Z -> Z) (final : RawGrid.t) (column row : Z) :
  apply_events events (initial_grid advice instance_) = Some final ->
  List.existsb (writes_fixed_at column row) events = false ->
  final.(RawGrid.cell) Raw.ColumnKind.Fixed column row = 0.
Proof.
  intros Hreplay Hfree.
  exact (replay_fixed_unwritten events (initial_grid advice instance_)
    final column row Hreplay Hfree).
Qed.

(** The same two statements as readings of the realized assignment, at the
    placed absolute row. *)
Lemma realize_selector_zero {columns : Columns.t} {RegionId : Set}
    (idx : Indices.t columns) (rs : RegionId -> Z)
    (events : list Raw.Event.t) (advice instance_ : Z -> Z -> Z)
    (final : RawGrid.t)
    (selector : columns.(Columns.Selector)) (region : RegionId) (row : Z) :
  apply_events events (initial_grid advice instance_) = Some final ->
  List.existsb
    (enables_at (idx.(Indices.selector) selector) (rs region + row))
    events = false ->
  (realize idx rs final).(Assignment.selector) selector region row = 0.
Proof.
  intros Hreplay Hfree.
  exact (replay_selector_zero events advice instance_ final
    (idx.(Indices.selector) selector) (rs region + row) Hreplay Hfree).
Qed.

Lemma realize_lookup_zero {columns : Columns.t} {RegionId : Set}
    (idx : Indices.t columns) (rs : RegionId -> Z)
    (events : list Raw.Event.t) (advice instance_ : Z -> Z -> Z)
    (final : RawGrid.t)
    (column : columns.(Columns.Lookup)) (row : Z) :
  apply_events events (initial_grid advice instance_) = Some final ->
  List.existsb (writes_fixed_at (idx.(Indices.lookup) column) row)
    events = false ->
  (realize idx rs final).(Assignment.lookup) column row = 0.
Proof.
  intros Hreplay Hfree.
  exact (replay_fixed_zero events advice instance_ final
    (idx.(Indices.lookup) column) row Hreplay Hfree).
Qed.

(** ** The existence form: a changed cell was written

    The literal converses of the pinning lemmas.  Both are constructive: the
    written-ness test is a Boolean scan, so the case split needs no classical
    reasoning, and the witnessing event is extracted from
    [List.existsb_exists]. *)

Lemma replay_selector_written (events : list Raw.Event.t)
    (initial final : RawGrid.t) (column row : Z) :
  apply_events events initial = Some final ->
  final.(RawGrid.sel) column row <> initial.(RawGrid.sel) column row ->
  List.existsb (enables_at column row) events = true.
Proof.
  intros Hreplay Hdiffers.
  destruct (List.existsb (enables_at column row) events) eqn:Hscan;
    [reflexivity |].
  exfalso.
  exact (Hdiffers (replay_selector_unwritten events initial final column row
    Hreplay Hscan)).
Qed.

Lemma replay_fixed_written (events : list Raw.Event.t)
    (initial final : RawGrid.t) (column row : Z) :
  apply_events events initial = Some final ->
  final.(RawGrid.cell) Raw.ColumnKind.Fixed column row <>
    initial.(RawGrid.cell) Raw.ColumnKind.Fixed column row ->
  List.existsb (writes_fixed_at column row) events = true.
Proof.
  intros Hreplay Hdiffers.
  destruct (List.existsb (writes_fixed_at column row) events) eqn:Hscan;
    [reflexivity |].
  exfalso.
  exact (Hdiffers (replay_fixed_unwritten events initial final column row
    Hreplay Hscan)).
Qed.

(** The scans name their events: a positive [enables_at] scan exhibits an
    [EnableSelector] event at exactly [(column, row)], and a positive
    [writes_fixed_at] scan exhibits either an [AssignFixed] at that cell or a
    [FillFromRow] whose half-open extent covers the row. *)
Lemma enables_at_In (column row : Z) (events : list Raw.Event.t) :
  List.existsb (enables_at column row) events = true ->
  exists annotation : string,
    List.In (Raw.Event.EnableSelector column row annotation) events.
Proof.
  intros Hscan.
  apply List.existsb_exists in Hscan.
  destruct Hscan as (event & Hin & Hcheck).
  destruct event as
    [name | name | name | name | column0 row0 annotation
    | column0 row0 annotation value | left_cell right_cell
    | column0 from_row to_row value];
    cbn [enables_at] in Hcheck; try discriminate Hcheck.
  apply andb_prop in Hcheck.
  destruct Hcheck as [Hcolumn Hrow].
  apply Z.eqb_eq in Hcolumn, Hrow.
  subst column0 row0.
  exists annotation.
  exact Hin.
Qed.

Lemma writes_fixed_at_In (column row : Z) (events : list Raw.Event.t) :
  List.existsb (writes_fixed_at column row) events = true ->
  (exists (annotation : string) (value : Z),
    List.In (Raw.Event.AssignFixed column row annotation value) events) \/
  (exists from_row to_row value : Z,
    List.In (Raw.Event.FillFromRow column from_row to_row value) events /\
    from_row <= row < to_row).
Proof.
  intros Hscan.
  apply List.existsb_exists in Hscan.
  destruct Hscan as (event & Hin & Hcheck).
  destruct event as
    [name | name | name | name | column0 row0 annotation
    | column0 row0 annotation value | left_cell right_cell
    | column0 from_row to_row value];
    cbn [writes_fixed_at] in Hcheck; try discriminate Hcheck.
  - (* AssignFixed *)
    apply andb_prop in Hcheck.
    destruct Hcheck as [Hcolumn Hrow].
    apply Z.eqb_eq in Hcolumn, Hrow.
    subst column0 row0.
    left.
    exists annotation, value.
    exact Hin.
  - (* FillFromRow *)
    apply andb_prop in Hcheck.
    destruct Hcheck as [Hcolumn Hextent].
    apply Z.eqb_eq in Hcolumn.
    apply andb_prop in Hextent.
    destruct Hextent as [Hfrom Hto].
    apply Z.leb_le in Hfrom.
    apply Z.ltb_lt in Hto.
    subst column0.
    right.
    exists from_row, to_row, value.
    split; [exact Hin | lia].
Qed.

(** ** The checker's stream algebra

    Only the third conjunct of [mock_prover_accepts] mentions the event
    list, so acceptance is monotone along list concatenation once the
    appended tail's copy obligations are discharged.  This is what lets a
    circuit whose checked stream is "synthesis events ++ constants tail" be
    accepted from the synthesis-only completeness statement plus the tail's
    copy facts. *)

Section StreamAlgebra.
  Context {p : Z}.
  Context `{Prime p}.

  Lemma mock_prover_accepts_app
      (system : ConstraintSystem.t Configure.indexed_columns)
      (events tail : list Raw.Event.t)
      (grid : RawGrid.t)
      (table_rows : Z) :
    mock_prover_accepts (p := p) system events grid table_rows ->
    (forall left right : Raw.Cell.t,
      List.In (Raw.Event.Copy left right) tail ->
      raw_cell_read grid left = raw_cell_read grid right) ->
    mock_prover_accepts (p := p) system (events ++ tail) grid table_rows.
  Proof.
    intros Haccept Htail.
    destruct Haccept as (Hgates & Hlookups & Hcopies).
    split; [exact Hgates |].
    split; [exact Hlookups |].
    intros left right Hin.
    apply List.in_app_or in Hin.
    destruct Hin as [Hin | Hin].
    - exact (Hcopies left right Hin).
    - exact (Htail left right Hin).
  Qed.
End StreamAlgebra.

(** ** Operational completeness, in the projected form

    [operational_complete] ([realize/sound.v]) binds the serialized stream
    through a pair destructuring of [V1.eval_layouter] and states a replay
    premise it introduces and discards.  This restatement names the stream as
    the [snd] projection — the shape a concrete instantiation uses — and drops
    the unused premise, so a caller never has to supply a replay at the
    synthesis-only grid.  The proof is the one of [operational_complete],
    through [relational_gates_to_mock], [relational_lookups_to_mock] and
    [layouter_copy_event_fact]. *)

Section OperationalCompleteEvents.
  Context {columns : Columns.t}.
  Context {RegionId : Set}.
  Context {p : Z}.
  Context `{Prime p}.

  Theorem operational_complete_events
      {A : Set} (program : 𝓛 columns RegionId A)
      (idx : Indices.t columns) (rs : RegionId -> Z) (usable_rows : Z)
      (system : ConstraintSystem.t columns)
      (grid : RawGrid.t)
      (region0 : RegionId) :
    instance_free system ->
    flattening_ok system ->
    circuit_holds (realize idx rs grid) program system ->
    mock_prover_accepts (p := p) (Configure.to_indexed idx system)
      (snd (V1.eval_layouter idx rs usable_rows program)) grid
      (layouter_table_rows program).
  Proof.
    intros Hinstance_free Hflattening_ok Hholds.
    destruct Hholds as (Hfacts & Hgates & Hlookups).
    split; [| split].
    - exact (relational_gates_to_mock idx rs grid system region0
        Hinstance_free Hflattening_ok Hgates).
    - exact (relational_lookups_to_mock idx rs grid system
        (layouter_table_rows program) region0 Hinstance_free Hlookups).
    - intros left right Hin.
      destruct (layouter_copy_event_fact idx rs usable_rows program left right
        Hin) as
        [ (left_cell & right_cell & Hleft & Hright & Hfact)
        | (cell & instance & row & Hleft & Hright & Hfact) ].
      + subst left right.
        rewrite <- !realize_eval_cell.
        exact (interpret_facts_In _ _ _ Hfacts Hfact).
      + subst left right.
        rewrite <- realize_eval_cell.
        exact (interpret_facts_In _ _ _ Hfacts Hfact).
  Qed.

  (** The form a circuit with a trailing constants block consumes: the
      checked stream is the synthesis events followed by a tail, and the
      tail's [Raw.Event.Copy] obligations are supplied separately (for the
      Orchard circuit they are the 166 constants copies, each pinned by the
      tail's own [AssignFixed] through [replay_fixed_pinned]). *)
  Theorem operational_complete_events_app
      {A : Set} (program : 𝓛 columns RegionId A)
      (idx : Indices.t columns) (rs : RegionId -> Z) (usable_rows : Z)
      (system : ConstraintSystem.t columns)
      (grid : RawGrid.t)
      (tail : list Raw.Event.t)
      (region0 : RegionId) :
    instance_free system ->
    flattening_ok system ->
    circuit_holds (realize idx rs grid) program system ->
    (forall left right : Raw.Cell.t,
      List.In (Raw.Event.Copy left right) tail ->
      raw_cell_read grid left = raw_cell_read grid right) ->
    mock_prover_accepts (p := p) (Configure.to_indexed idx system)
      (snd (V1.eval_layouter idx rs usable_rows program) ++ tail) grid
      (layouter_table_rows program).
  Proof.
    intros Hinstance_free Hflattening_ok Hholds Htail.
    apply mock_prover_accepts_app; [| exact Htail].
    exact (operational_complete_events program idx rs usable_rows system grid
      region0 Hinstance_free Hflattening_ok Hholds).
  Qed.
End OperationalCompleteEvents.
