(** * Placement-generic sufficient conditions for replay success.

    [realize/main.v]'s [apply_events] fails exactly when a write event would
    change an already-written cell to a different value, so replay success
    of a concrete event stream is a [vm_compute] — quadratic in the stream
    length.  This file factors that computation into placement-generic
    reasoning, in two layers:

    - a conflict-freedom core: [conflict_free], a decidable predicate on a
      raw event stream ("no write event conflicts with any earlier write
      event", through the same [write_conflicts_write] /
      [write_conflicts_fill] / [fill_conflicts_write] /
      [fill_conflicts_fill] checks the replay log performs), equal to
      [replay_is_ok] at every initial grid ([replay_is_ok_conflict_free]);
    - a block layer over the [V1.eval_layouter] lowering: per-region
      single-assignment at region-local offsets, per-block row extents, and
      pairwise block compatibility (disjoint absolute row intervals under
      [region_start], or disjoint written column slots) imply
      conflict-freedom of the whole lowered stream, hence replay success at
      every placement satisfying the interval conditions
      ([layouter_replay_succeeds]).

    Every condition is a boolean, so concrete instances discharge them by
    [vm_compute]: the per-block checks are placement-independent and
    quadratic only within one block, and the cross-block checks are
    quadratic in the number of blocks, not in the number of events. *)

Require Import Garden.Halo2.main.
Require Import Garden.Halo2.Synthesis.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.serialize.
Require Import Garden.Halo2.realize.main.
Require Import Garden.Halo2.realize.facts.
Require Import Stdlib.btauto.Btauto.
Require Import Stdlib.micromega.Lia.

Import ListNotations.
Global Open Scope Z_scope.

(** ** The writes of an event stream

    The replay log records exactly the point writes and fills of the
    replayed events; [EventWrite.t] is one such record, tagged with the
    plane it targets.  Region and namespace markers and [Copy] events write
    nothing. *)
Module EventWrite.
  Inductive t : Set :=
  | Selector (write : Write.t)
  | Fixed (write : Write.t)
  | Fill (fill : Fill.t).
End EventWrite.

Definition event_write (event : Raw.Event.t) : option EventWrite.t :=
  match event with
  | Raw.Event.EnterRegion _
  | Raw.Event.ExitRegion _
  | Raw.Event.PushNamespace _
  | Raw.Event.PopNamespace _
  | Raw.Event.Copy _ _ =>
      None
  | Raw.Event.EnableSelector column row _ =>
      Some (EventWrite.Selector
        {| Write.column := column; Write.row := row; Write.value := 1 |})
  | Raw.Event.AssignFixed column row _ value =>
      Some (EventWrite.Fixed
        {| Write.column := column; Write.row := row; Write.value := value |})
  | Raw.Event.FillFromRow column from_row value =>
      Some (EventWrite.Fill
        {|
          Fill.column := column;
          Fill.from_row := from_row;
          Fill.value := value;
        |})
  end.

Fixpoint event_writes (events : list Raw.Event.t) : list EventWrite.t :=
  match events with
  | [] => []
  | event :: events =>
      match event_write event with
      | Some write => write :: event_writes events
      | None => event_writes events
      end
  end.

Lemma event_writes_app (events1 events2 : list Raw.Event.t) :
  event_writes (events1 ++ events2) =
    event_writes events1 ++ event_writes events2.
Proof.
  induction events1 as [| event events1 IH]; cbn; [reflexivity |].
  destruct (event_write event); cbn; rewrite IH; reflexivity.
Qed.

(** A later write conflicts with an earlier one exactly when the replay's
    conflict check for the later write fires on the earlier write's log
    entry.  Selector writes live in a plane of their own, so they never
    conflict with fixed-plane writes or fills. *)
Definition writes_conflict (later earlier : EventWrite.t) : bool :=
  match later, earlier with
  | EventWrite.Selector later, EventWrite.Selector earlier =>
      write_conflicts_write
        later.(Write.column) later.(Write.row) later.(Write.value) earlier
  | EventWrite.Selector _, EventWrite.Fixed _ => false
  | EventWrite.Selector _, EventWrite.Fill _ => false
  | EventWrite.Fixed _, EventWrite.Selector _ => false
  | EventWrite.Fixed later, EventWrite.Fixed earlier =>
      write_conflicts_write
        later.(Write.column) later.(Write.row) later.(Write.value) earlier
  | EventWrite.Fixed later, EventWrite.Fill earlier =>
      write_conflicts_fill
        later.(Write.column) later.(Write.row) later.(Write.value) earlier
  | EventWrite.Fill _, EventWrite.Selector _ => false
  | EventWrite.Fill later, EventWrite.Fixed earlier =>
      fill_conflicts_write
        later.(Fill.column) later.(Fill.from_row) later.(Fill.value) earlier
  | EventWrite.Fill later, EventWrite.Fill earlier =>
      fill_conflicts_fill later.(Fill.column) later.(Fill.value) earlier
  end.

(** ** Conflict freedom

    No write conflicts with any earlier write: for each write of the list,
    every later write passes the conflict check against it. *)
Fixpoint conflict_free_writes (writes : list EventWrite.t) : bool :=
  match writes with
  | [] => true
  | write :: writes =>
      andb
        (List.forallb
          (fun later => negb (writes_conflict later write)) writes)
        (conflict_free_writes writes)
  end.

Definition conflict_free (events : list Raw.Event.t) : bool :=
  conflict_free_writes (event_writes events).

(** ** Boolean list helpers *)

Lemma forallb_ext_in {A : Type} (f g : A -> bool) (l : list A) :
  (forall x, List.In x l -> f x = g x) ->
  List.forallb f l = List.forallb g l.
Proof.
  induction l as [| x l IH]; intros Hext; cbn; [reflexivity |].
  rewrite (Hext x (List.in_eq _ _)).
  rewrite IH; [reflexivity |].
  intros y Hy.
  apply Hext, List.in_cons, Hy.
Qed.

Lemma forallb_andb {A : Type} (f g : A -> bool) (l : list A) :
  List.forallb (fun x => andb (f x) (g x)) l =
    andb (List.forallb f l) (List.forallb g l).
Proof.
  induction l as [| x l IH]; cbn; [reflexivity |].
  rewrite IH.
  btauto.
Qed.

Lemma forallb_map_compose {A B : Type} (f : B -> bool) (g : A -> B)
    (l : list A) :
  List.forallb f (List.map g l) = List.forallb (fun x => f (g x)) l.
Proof.
  induction l as [| x l IH]; cbn; [reflexivity |].
  rewrite IH; reflexivity.
Qed.

Lemma forallb_true {A : Type} (l : list A) :
  List.forallb (fun _ => true) l = true.
Proof.
  induction l as [| x l IH]; cbn; [reflexivity | exact IH].
Qed.

(** ** Independence of two streams

    No write of the later stream conflicts with any write of the earlier
    one; with per-stream conflict freedom this decomposes conflict freedom
    of a concatenation. *)
Definition writes_independent (earlier later : list EventWrite.t) : bool :=
  List.forallb
    (fun write_later =>
      List.forallb
        (fun write_earlier => negb (writes_conflict write_later write_earlier))
        earlier)
    later.

Lemma writes_independent_nil (later : list EventWrite.t) :
  writes_independent [] later = true.
Proof.
  induction later as [| write later IH]; cbn; [reflexivity | exact IH].
Qed.

Lemma writes_independent_cons (write : EventWrite.t)
    (earlier later : list EventWrite.t) :
  writes_independent (write :: earlier) later =
    andb
      (List.forallb
        (fun write_later => negb (writes_conflict write_later write)) later)
      (writes_independent earlier later).
Proof.
  unfold writes_independent.
  rewrite <- forallb_andb.
  apply forallb_ext_in.
  intros write_later _.
  reflexivity.
Qed.

Lemma writes_independent_app_later (earlier later1 later2 : list EventWrite.t) :
  writes_independent earlier (later1 ++ later2) =
    andb
      (writes_independent earlier later1)
      (writes_independent earlier later2).
Proof.
  apply List.forallb_app.
Qed.

Lemma conflict_free_writes_app (writes1 writes2 : list EventWrite.t) :
  conflict_free_writes (writes1 ++ writes2) =
    andb (conflict_free_writes writes1)
      (andb
        (writes_independent writes1 writes2)
        (conflict_free_writes writes2)).
Proof.
  induction writes1 as [| write writes1 IH]; cbn.
  - rewrite writes_independent_nil.
    reflexivity.
  - rewrite List.forallb_app, IH, writes_independent_cons.
    btauto.
Qed.

Definition streams_independent (earlier later : list Raw.Event.t) : bool :=
  writes_independent (event_writes earlier) (event_writes later).

Lemma conflict_free_app (events1 events2 : list Raw.Event.t) :
  conflict_free (events1 ++ events2) =
    andb (conflict_free events1)
      (andb
        (streams_independent events1 events2)
        (conflict_free events2)).
Proof.
  unfold conflict_free, streams_independent.
  rewrite event_writes_app.
  apply conflict_free_writes_app.
Qed.

(** ** Replay as a computation on writes

    The replay's conflict verdict reads only the log, and the log after a
    prefix holds exactly the prefix's writes; both facts are packaged by a
    log-only replay over [event_writes]. *)

(** The conflict check [apply_event] performs for one pending write. *)
Definition write_ok_against_log (write : EventWrite.t) (log : Log.t) : bool :=
  match write with
  | EventWrite.Selector write =>
      negb
        (List.existsb
          (write_conflicts_write
            write.(Write.column) write.(Write.row) write.(Write.value))
          log.(Log.selectors))
  | EventWrite.Fixed write =>
      negb
        (orb
          (List.existsb
            (write_conflicts_write
              write.(Write.column) write.(Write.row) write.(Write.value))
            log.(Log.fixeds))
          (List.existsb
            (write_conflicts_fill
              write.(Write.column) write.(Write.row) write.(Write.value))
            log.(Log.fills)))
  | EventWrite.Fill fill =>
      negb
        (orb
          (List.existsb
            (fill_conflicts_write
              fill.(Fill.column) fill.(Fill.from_row) fill.(Fill.value))
            log.(Log.fixeds))
          (List.existsb
            (fill_conflicts_fill fill.(Fill.column) fill.(Fill.value))
            log.(Log.fills)))
  end.

Definition log_add (write : EventWrite.t) (log : Log.t) : Log.t :=
  match write with
  | EventWrite.Selector write => Log.add_selector log write
  | EventWrite.Fixed write => Log.add_fixed log write
  | EventWrite.Fill fill => Log.add_fill log fill
  end.

Fixpoint writes_replay (writes : list EventWrite.t) (log : Log.t)
    : option Log.t :=
  match writes with
  | [] => Some log
  | write :: writes =>
      if write_ok_against_log write log
      then writes_replay writes (log_add write log)
      else None
  end.

Definition writes_replay_ok (writes : list EventWrite.t) (log : Log.t)
    : bool :=
  match writes_replay writes log with
  | Some _ => true
  | None => false
  end.

Lemma writes_replay_ok_cons (write : EventWrite.t)
    (writes : list EventWrite.t) (log : Log.t) :
  writes_replay_ok (write :: writes) log =
    andb
      (write_ok_against_log write log)
      (writes_replay_ok writes (log_add write log)).
Proof.
  unfold writes_replay_ok; cbn [writes_replay].
  destruct (write_ok_against_log write log); reflexivity.
Qed.

(** Replay success of the full event stream is the log-only replay of its
    writes: the grid planes never enter the verdict. *)
Lemma apply_events_log_is_ok (events : list Raw.Event.t) :
  forall state : ReplayState.t,
  match apply_events_log events state with
  | Some _ => true
  | None => false
  end = writes_replay_ok (event_writes events) state.(ReplayState.log).
Proof.
  induction events as [| event events IH]; intros state; [reflexivity |].
  destruct event as
    [name | name | name | name | column row annotation
    | column row annotation value | left_cell right_cell
    | column from_row value]; cbn; try apply IH;
    rewrite writes_replay_ok_cons.
  - (* EnableSelector *)
    cbn [write_ok_against_log log_add Write.column Write.row Write.value].
    destruct (List.existsb (write_conflicts_write column row 1)
      state.(ReplayState.log).(Log.selectors)); [reflexivity |].
    apply IH.
  - (* AssignFixed *)
    cbn [write_ok_against_log log_add Write.column Write.row Write.value].
    destruct (List.existsb (write_conflicts_write column row value)
        state.(ReplayState.log).(Log.fixeds)),
      (List.existsb (write_conflicts_fill column row value)
        state.(ReplayState.log).(Log.fills)); try reflexivity.
    apply IH.
  - (* FillFromRow *)
    cbn [write_ok_against_log log_add Fill.column Fill.from_row Fill.value].
    destruct (List.existsb (fill_conflicts_write column from_row value)
        state.(ReplayState.log).(Log.fixeds)),
      (List.existsb (fill_conflicts_fill column value)
        state.(ReplayState.log).(Log.fills)); try reflexivity.
    apply IH.
Qed.

(** Adding a logged write splits the conflict check into "no conflict with
    the added write" and the check against the previous log. *)
Lemma write_ok_against_log_add (write earlier : EventWrite.t) (log : Log.t) :
  write_ok_against_log write (log_add earlier log) =
    andb
      (negb (writes_conflict write earlier))
      (write_ok_against_log write log).
Proof.
  destruct write as [w | w | f], earlier as [w0 | w0 | f0]; cbn; btauto.
Qed.

Lemma write_ok_against_log_empty (write : EventWrite.t) :
  write_ok_against_log write Log.empty = true.
Proof.
  destruct write; reflexivity.
Qed.

(** The log-only replay succeeds exactly when the writes are conflict-free
    among themselves and against the starting log. *)
Lemma writes_replay_ok_char (writes : list EventWrite.t) :
  forall log : Log.t,
  writes_replay_ok writes log =
    andb (conflict_free_writes writes)
      (List.forallb (fun write => write_ok_against_log write log) writes).
Proof.
  induction writes as [| write writes IH]; intros log; [reflexivity |].
  rewrite writes_replay_ok_cons, IH.
  rewrite (forallb_ext_in
    (fun write' => write_ok_against_log write' (log_add write log))
    (fun write' =>
      andb
        (negb (writes_conflict write' write))
        (write_ok_against_log write' log))
    writes
    (fun write' _ => write_ok_against_log_add write' write log)).
  rewrite forallb_andb.
  cbn [conflict_free_writes List.forallb].
  btauto.
Qed.

Lemma writes_replay_ok_empty (writes : list EventWrite.t) :
  writes_replay_ok writes Log.empty = conflict_free_writes writes.
Proof.
  rewrite writes_replay_ok_char.
  rewrite (forallb_ext_in
    (fun write => write_ok_against_log write Log.empty)
    (fun _ => true)
    writes
    (fun write _ => write_ok_against_log_empty write)).
  rewrite forallb_true.
  apply Bool.andb_true_r.
Qed.

(** ** The core theorem: replay succeeds iff the stream is conflict-free

    The verdict is one boolean equality, at every initial grid: the replay
    log after a prefix is exactly the set of earlier writes, so a [None]
    from [apply_events] is a genuine conflict and conversely. *)
Theorem replay_is_ok_conflict_free (events : list Raw.Event.t)
    (grid : RawGrid.t) :
  replay_is_ok events grid = conflict_free events.
Proof.
  unfold replay_is_ok, apply_events, conflict_free.
  pose proof (apply_events_log_is_ok events (ReplayState.init grid)) as His.
  cbn [ReplayState.init ReplayState.log] in His.
  rewrite writes_replay_ok_empty in His.
  destruct (apply_events_log events (ReplayState.init grid)) as [state |];
    exact His.
Qed.

Theorem conflict_free_apply_events (events : list Raw.Event.t) :
  conflict_free events = true ->
  forall grid : RawGrid.t,
  exists grid', apply_events events grid = Some grid'.
Proof.
  intros Hfree grid.
  apply replay_is_ok_some.
  rewrite (replay_is_ok_conflict_free events grid).
  exact Hfree.
Qed.

Theorem conflict_free_iff (events : list Raw.Event.t) (grid : RawGrid.t) :
  conflict_free events = true <->
  exists grid', apply_events events grid = Some grid'.
Proof.
  split.
  - intros Hfree.
    exact (conflict_free_apply_events events Hfree grid).
  - intros [grid' Happly].
    rewrite <- (replay_is_ok_conflict_free events grid).
    unfold replay_is_ok.
    rewrite Happly.
    reflexivity.
Qed.

(** ** Slots: the plane and column a write targets

    Every conflict check compares columns within one plane (the selector
    plane or the shared fixed plane), so writes whose slots differ never
    conflict — the column-disjointness argument for cross-block
    independence. *)
Module Slot.
  Record t : Set := {
    selector_plane : bool;
    column : Z;
  }.

  Definition eqb (slot1 slot2 : t) : bool :=
    andb
      (Bool.eqb slot1.(selector_plane) slot2.(selector_plane))
      (slot1.(column) =? slot2.(column)).
End Slot.

Definition write_slot (write : EventWrite.t) : Slot.t :=
  match write with
  | EventWrite.Selector write =>
      {| Slot.selector_plane := true; Slot.column := write.(Write.column) |}
  | EventWrite.Fixed write =>
      {| Slot.selector_plane := false; Slot.column := write.(Write.column) |}
  | EventWrite.Fill fill =>
      {| Slot.selector_plane := false; Slot.column := fill.(Fill.column) |}
  end.

Lemma writes_conflict_slots_apart (later earlier : EventWrite.t) :
  Slot.eqb (write_slot later) (write_slot earlier) = false ->
  writes_conflict later earlier = false.
Proof.
  destruct later as [w | w | f], earlier as [w0 | w0 | f0];
    unfold Slot.eqb; cbn; intros Hslot; try reflexivity;
    rewrite Z.eqb_sym in Hslot;
    unfold write_conflicts_write, write_conflicts_fill,
      fill_conflicts_write, fill_conflicts_fill;
    rewrite Hslot; reflexivity.
Qed.

(** ** Rows: point writes at distinct rows never conflict *)

Definition write_row (write : EventWrite.t) : Z :=
  match write with
  | EventWrite.Selector write => write.(Write.row)
  | EventWrite.Fixed write => write.(Write.row)
  | EventWrite.Fill fill => fill.(Fill.from_row)
  end.

Definition is_point_write (write : EventWrite.t) : bool :=
  match write with
  | EventWrite.Selector _ => true
  | EventWrite.Fixed _ => true
  | EventWrite.Fill _ => false
  end.

Lemma writes_conflict_rows_apart (later earlier : EventWrite.t) :
  is_point_write later = true ->
  is_point_write earlier = true ->
  write_row later <> write_row earlier ->
  writes_conflict later earlier = false.
Proof.
  destruct later as [w | w | f], earlier as [w0 | w0 | f0]; cbn;
    intros Hlater Hearlier Hrows; try reflexivity; try discriminate;
    unfold write_conflicts_write;
    destruct (w0.(Write.row) =? w.(Write.row)) eqn:Hrow.
  - apply Z.eqb_eq in Hrow; congruence.
  - destruct (w0.(Write.column) =? w.(Write.column)); reflexivity.
  - apply Z.eqb_eq in Hrow; congruence.
  - destruct (w0.(Write.column) =? w.(Write.column)); reflexivity.
Qed.

(** ** Shifting writes by a region start *)

Definition shift_write (delta : Z) (write : EventWrite.t) : EventWrite.t :=
  match write with
  | EventWrite.Selector write =>
      EventWrite.Selector {|
        Write.column := write.(Write.column);
        Write.row := delta + write.(Write.row);
        Write.value := write.(Write.value);
      |}
  | EventWrite.Fixed write =>
      EventWrite.Fixed {|
        Write.column := write.(Write.column);
        Write.row := delta + write.(Write.row);
        Write.value := write.(Write.value);
      |}
  | EventWrite.Fill fill =>
      EventWrite.Fill {|
        Fill.column := fill.(Fill.column);
        Fill.from_row := delta + fill.(Fill.from_row);
        Fill.value := fill.(Fill.value);
      |}
  end.

Lemma Z_eqb_shift (delta a b : Z) : (delta + a =? delta + b) = (a =? b).
Proof.
  destruct (a =? b) eqn:Hab.
  - apply Z.eqb_eq in Hab; subst; apply Z.eqb_refl.
  - apply Z.eqb_neq; apply Z.eqb_neq in Hab; lia.
Qed.

Lemma Z_leb_shift (delta a b : Z) : (delta + a <=? delta + b) = (a <=? b).
Proof.
  destruct (a <=? b) eqn:Hab.
  - apply Z.leb_le; apply Z.leb_le in Hab; lia.
  - apply Z.leb_gt; apply Z.leb_gt in Hab; lia.
Qed.

(** Conflicts are invariant under a common shift: every row comparison the
    checks make is between two shifted rows. *)
Lemma writes_conflict_shift (delta : Z) (later earlier : EventWrite.t) :
  writes_conflict (shift_write delta later) (shift_write delta earlier) =
    writes_conflict later earlier.
Proof.
  destruct later as [w | w | f], earlier as [w0 | w0 | f0]; cbn;
    try reflexivity;
    unfold write_conflicts_write, write_conflicts_fill,
      fill_conflicts_write, fill_conflicts_fill; cbn;
    rewrite ?Z_eqb_shift, ?Z_leb_shift; reflexivity.
Qed.

Lemma write_slot_shift (delta : Z) (write : EventWrite.t) :
  write_slot (shift_write delta write) = write_slot write.
Proof.
  destruct write; reflexivity.
Qed.

Lemma write_row_shift (delta : Z) (write : EventWrite.t) :
  write_row (shift_write delta write) = delta + write_row write.
Proof.
  destruct write; reflexivity.
Qed.

Lemma is_point_write_shift (delta : Z) (write : EventWrite.t) :
  is_point_write (shift_write delta write) = is_point_write write.
Proof.
  destruct write; reflexivity.
Qed.

Lemma conflict_free_writes_map_shift (delta : Z)
    (writes : list EventWrite.t) :
  conflict_free_writes (List.map (shift_write delta) writes) =
    conflict_free_writes writes.
Proof.
  induction writes as [| write writes IH]; cbn; [reflexivity |].
  rewrite IH.
  f_equal.
  rewrite forallb_map_compose.
  apply forallb_ext_in.
  intros write' _.
  rewrite writes_conflict_shift.
  reflexivity.
Qed.

(** ** Row extents

    The extent of a write list is one past its largest row; together with
    row non-negativity it confines a region's placed writes to the interval
    [[region_start, region_start + extent)]. *)
Fixpoint writes_extent (writes : list EventWrite.t) : Z :=
  match writes with
  | [] => 0
  | write :: writes => Z.max (write_row write + 1) (writes_extent writes)
  end.

Definition writes_rows_ok (writes : list EventWrite.t) : bool :=
  List.forallb
    (fun write => andb (is_point_write write) (0 <=? write_row write))
    writes.

Lemma writes_extent_bound (writes : list EventWrite.t)
    (write : EventWrite.t) :
  List.In write writes ->
  write_row write < writes_extent writes.
Proof.
  induction writes as [| write0 writes IH]; intros Hin; [contradiction |].
  destruct Hin as [-> | Hin]; cbn.
  - lia.
  - pose proof (IH Hin); lia.
Qed.

Lemma writes_rows_ok_in (writes : list EventWrite.t)
    (write : EventWrite.t) :
  writes_rows_ok writes = true ->
  List.In write writes ->
  andb (is_point_write write) (0 <=? write_row write) = true.
Proof.
  unfold writes_rows_ok.
  intros Hok Hin.
  exact (proj1 (List.forallb_forall _ _) Hok write Hin).
Qed.

(** ** Blocks

    The lowered stream of a synthesis program is a concatenation of blocks:
    one per region (writes recorded at region-local offsets, placed at the
    region's start row) and one per lookup-table load (writes at absolute
    rows).  The floor planner's trailing constants block is a further
    global block. *)
Module Block.
  Inductive t (RegionId : Set) : Set :=
  | Region (region : RegionId) (writes : list EventWrite.t)
  | Global (writes : list EventWrite.t).
  Arguments Region {_}.
  Arguments Global {_}.

  Definition writes {RegionId : Set} (block : t RegionId)
      : list EventWrite.t :=
    match block with
    | Region _ writes => writes
    | Global writes => writes
    end.
End Block.

Definition block_writes {RegionId : Set} (region_start : RegionId -> Z)
    (block : Block.t RegionId) : list EventWrite.t :=
  match block with
  | Block.Region region writes =>
      List.map (shift_write (region_start region)) writes
  | Block.Global writes => writes
  end.

(** Internal consistency of one block, placement-independent: the writes
    are conflict-free among themselves (single assignment), and a region
    block's writes are point writes at non-negative offsets — the shape
    [V1.eval_region] produces, and what confines the placed rows to the
    block's interval. *)
Definition block_ok {RegionId : Set} (block : Block.t RegionId) : bool :=
  match block with
  | Block.Region _ writes =>
      andb (conflict_free_writes writes) (writes_rows_ok writes)
  | Block.Global writes => conflict_free_writes writes
  end.

Definition block_slots {RegionId : Set} (block : Block.t RegionId)
    : list Slot.t :=
  List.map write_slot (Block.writes block).

Definition slots_disjoint (earlier later : list Slot.t) : bool :=
  List.forallb
    (fun slot => negb (List.existsb (Slot.eqb slot) earlier))
    later.

Definition intervals_disjoint (start1 extent1 start2 extent2 : Z) : bool :=
  orb (extent1 <=? 0)
    (orb (extent2 <=? 0)
      (orb (start1 + extent1 <=? start2) (start2 + extent2 <=? start1))).

(** Two blocks are compatible when their placed writes cannot touch a
    common cell: two region blocks with disjoint absolute row intervals
    under the placement, or any two blocks writing disjoint column slots.
    The slot check is placement-independent, so table loads and the
    constants block are kept apart from region writes by columns alone. *)
Definition blocks_compatible {RegionId : Set} (region_start : RegionId -> Z)
    (earlier later : Block.t RegionId) : bool :=
  orb
    (match earlier, later with
     | Block.Region region1 writes1, Block.Region region2 writes2 =>
         intervals_disjoint
           (region_start region1) (writes_extent writes1)
           (region_start region2) (writes_extent writes2)
     | _, _ => false
     end)
    (slots_disjoint (block_slots earlier) (block_slots later)).

Lemma block_writes_slot_in {RegionId : Set} (region_start : RegionId -> Z)
    (block : Block.t RegionId) (write : EventWrite.t) :
  List.In write (block_writes region_start block) ->
  List.In (write_slot write) (block_slots block).
Proof.
  destruct block as [region writes | writes]; cbn; intros Hin.
  - apply List.in_map_iff in Hin.
    destruct Hin as (write0 & <- & Hin0).
    rewrite write_slot_shift.
    apply List.in_map, Hin0.
  - apply List.in_map, Hin.
Qed.

(** Compatibility of two internally consistent blocks makes their placed
    write lists independent: a cross-block conflict would need a shared
    cell, excluded by rows (both blocks are regions with disjoint
    intervals) or by columns (disjoint slots). *)
Lemma blocks_compatible_independent {RegionId : Set}
    (region_start : RegionId -> Z) (earlier later : Block.t RegionId) :
  block_ok earlier = true ->
  block_ok later = true ->
  blocks_compatible region_start earlier later = true ->
  writes_independent
    (block_writes region_start earlier)
    (block_writes region_start later) = true.
Proof.
  intros Hok_earlier Hok_later Hcompat.
  unfold writes_independent.
  apply List.forallb_forall.
  intros write_later Hin_later.
  apply List.forallb_forall.
  intros write_earlier Hin_earlier.
  apply Bool.negb_true_iff.
  destruct (Bool.orb_prop _ _ Hcompat) as [Hrows | Hslots].
  - (* disjoint row intervals: both blocks are region blocks *)
    destruct earlier as [region1 writes1 | writes1]; [| discriminate Hrows].
    destruct later as [region2 writes2 | writes2]; [| discriminate Hrows].
    cbn in Hok_earlier, Hok_later, Hin_earlier, Hin_later.
    destruct (andb_prop _ _ Hok_earlier) as [_ Hrows1].
    destruct (andb_prop _ _ Hok_later) as [_ Hrows2].
    apply List.in_map_iff in Hin_earlier.
    destruct Hin_earlier as (write1 & <- & Hwrite1).
    apply List.in_map_iff in Hin_later.
    destruct Hin_later as (write2 & <- & Hwrite2).
    destruct (andb_prop _ _ (writes_rows_ok_in writes1 write1 Hrows1 Hwrite1))
      as [Hpoint1 Hnonneg1].
    destruct (andb_prop _ _ (writes_rows_ok_in writes2 write2 Hrows2 Hwrite2))
      as [Hpoint2 Hnonneg2].
    apply Z.leb_le in Hnonneg1, Hnonneg2.
    pose proof (writes_extent_bound writes1 write1 Hwrite1) as Hbound1.
    pose proof (writes_extent_bound writes2 write2 Hwrite2) as Hbound2.
    apply writes_conflict_rows_apart.
    + rewrite is_point_write_shift; exact Hpoint2.
    + rewrite is_point_write_shift; exact Hpoint1.
    + rewrite !write_row_shift.
      unfold intervals_disjoint in Hrows.
      destruct (Bool.orb_prop _ _ Hrows) as [Hextent1 | Hrest];
        [apply Z.leb_le in Hextent1; lia |].
      destruct (Bool.orb_prop _ _ Hrest) as [Hextent2 | Hrest'];
        [apply Z.leb_le in Hextent2; lia |].
      destruct (Bool.orb_prop _ _ Hrest') as [Hle | Hle];
        apply Z.leb_le in Hle; lia.
  - (* disjoint slots *)
    apply writes_conflict_slots_apart.
    pose proof (proj1 (List.forallb_forall _ _) Hslots
      (write_slot write_later)
      (block_writes_slot_in region_start later write_later Hin_later))
      as Hno.
    apply Bool.negb_true_iff in Hno.
    exact (existsb_false_forall _ _ Hno (write_slot write_earlier)
      (block_writes_slot_in region_start earlier write_earlier Hin_earlier)).
Qed.

(** ** Conflict freedom of a block list *)

Fixpoint blocks_compatible_all {RegionId : Set}
    (region_start : RegionId -> Z) (blocks : list (Block.t RegionId))
    : bool :=
  match blocks with
  | [] => true
  | block :: blocks =>
      andb
        (List.forallb (blocks_compatible region_start block) blocks)
        (blocks_compatible_all region_start blocks)
  end.

Lemma writes_independent_flat_map {RegionId : Set}
    (region_start : RegionId -> Z) (block : Block.t RegionId)
    (blocks : list (Block.t RegionId)) :
  block_ok block = true ->
  List.forallb block_ok blocks = true ->
  List.forallb (blocks_compatible region_start block) blocks = true ->
  writes_independent
    (block_writes region_start block)
    (List.flat_map (block_writes region_start) blocks) = true.
Proof.
  induction blocks as [| block' blocks IH]; intros Hok Hoks Hcompats.
  - reflexivity.
  - cbn [List.flat_map].
    rewrite writes_independent_app_later.
    cbn in Hoks, Hcompats.
    destruct (andb_prop _ _ Hoks) as [Hok' Hoks'].
    destruct (andb_prop _ _ Hcompats) as [Hcompat Hcompats'].
    apply andb_true_intro; split.
    + exact (blocks_compatible_independent region_start block block'
        Hok Hok' Hcompat).
    + apply IH; assumption.
Qed.

(** The block-level theorem: internally consistent, pairwise compatible
    blocks lower to a conflict-free write list.  The hypotheses are
    booleans — the per-block checks are placement-independent, and only the
    pairwise compatibility mentions [region_start]. *)
Theorem blocks_conflict_free {RegionId : Set}
    (region_start : RegionId -> Z) (blocks : list (Block.t RegionId)) :
  List.forallb block_ok blocks = true ->
  blocks_compatible_all region_start blocks = true ->
  conflict_free_writes
    (List.flat_map (block_writes region_start) blocks) = true.
Proof.
  induction blocks as [| block blocks IH]; intros Hoks Hcompats;
    [reflexivity |].
  cbn in Hoks, Hcompats.
  destruct (andb_prop _ _ Hoks) as [Hok Hoks'].
  destruct (andb_prop _ _ Hcompats) as [Hcompat Hcompats'].
  cbn [List.flat_map].
  rewrite conflict_free_writes_app.
  apply andb_true_intro; split; [| apply andb_true_intro; split].
  - destruct block as [region writes | writes]; cbn.
    + rewrite conflict_free_writes_map_shift.
      exact (proj1 (andb_prop _ _ Hok)).
    + exact Hok.
  - apply writes_independent_flat_map; assumption.
  - apply IH; assumption.
Qed.

(** ** The blocks of a synthesis program

    [region_writes] reads a region program's writes off the syntax at
    region-local offsets — the placement enters only through the final
    shift — and [layouter_blocks] collects one region block per [AddRegion]
    and one global block per [InitLookupTables].  [Copy],
    [ConstrainInstance] and [ConstrainConstant] emit no write ([Copy]
    events constrain rather than assign; [ConstrainConstant] emits no
    event), and the markers write nothing. *)
Fixpoint region_writes {columns : Columns.t} {RegionId : Set} {A : Set}
    (indices : Indices.t columns)
    (program : 𝓡 columns RegionId A) {struct program}
    : list EventWrite.t :=
  match program with
  | 𝓡.Ret _ => []
  | 𝓡.Bind first second =>
      region_writes indices first ++
      region_writes indices (second (region_value first))
  | 𝓡.EnableSelector selector offset _ =>
      [EventWrite.Selector {|
        Write.column := indices.(Indices.selector) selector;
        Write.row := offset;
        Write.value := 1;
      |}]
  | 𝓡.AssignFixed _ column offset value =>
      [EventWrite.Fixed {|
        Write.column := indices.(Indices.fixed) column;
        Write.row := offset;
        Write.value := value;
      |}]
  | 𝓡.Copy _ _ => []
  | 𝓡.ConstrainConstant _ _ => []
  end.

Lemma eval_region_event_writes {columns : Columns.t} {RegionId : Set}
    {A : Set} (indices : Indices.t columns) (region_start : RegionId -> Z)
    (region : RegionId) (program : 𝓡 columns RegionId A) :
  event_writes (snd (V1.eval_region indices region_start region program)) =
    List.map (shift_write (region_start region)) (region_writes indices program).
Proof.
  induction program as
    [A value | A B first IHfirst second IHsecond
    | selector offset annotation | annotation column offset value
    | left_cell right_cell | cell value];
    cbn [V1.eval_region region_writes]; try reflexivity.
  (* Bind *)
  rewrite (region_value_agrees indices region_start region first).
  destruct (V1.eval_region indices region_start region first)
    as [value_first events_first] eqn:Hfirst.
  cbn [fst].
  destruct (V1.eval_region indices region_start region (second value_first))
    as [value_second events_second] eqn:Hsecond.
  cbn [snd].
  rewrite event_writes_app, List.map_app.
  f_equal.
  - exact IHfirst.
  - specialize (IHsecond value_first).
    rewrite Hsecond in IHsecond.
    exact IHsecond.
Qed.

Fixpoint layouter_blocks {columns : Columns.t} {RegionId : Set} {A : Set}
    (indices : Indices.t columns)
    (program : 𝓛 columns RegionId A) {struct program}
    : list (Block.t RegionId) :=
  match program with
  | 𝓛.Ret _ => []
  | 𝓛.Bind first second =>
      layouter_blocks indices first ++
      layouter_blocks indices (second (layouter_value first))
  | 𝓛.AddRegion region _ region_program =>
      [Block.Region region (region_writes indices (region_program region))]
  | 𝓛.ConstrainInstance _ _ _ => []
  | 𝓛.InitLookupTables name entries =>
      [Block.Global
        (event_writes (V1.init_lookup_table_events indices name entries))]
  | 𝓛.InNamespace _ nested => layouter_blocks indices nested
  end.

Lemma eval_layouter_event_writes {columns : Columns.t} {RegionId : Set}
    {A : Set} (indices : Indices.t columns) (region_start : RegionId -> Z)
    (program : 𝓛 columns RegionId A) :
  event_writes (snd (V1.eval_layouter indices region_start program)) =
    List.flat_map (block_writes region_start)
      (layouter_blocks indices program).
Proof.
  induction program as
    [A value | A B first IHfirst second IHsecond
    | A region name region_program | cell instance row
    | name entries | A name nested IHnested];
    cbn [V1.eval_layouter layouter_blocks]; try reflexivity.
  - (* Bind *)
    rewrite (layouter_value_agrees indices region_start first).
    destruct (V1.eval_layouter indices region_start first)
      as [value_first events_first] eqn:Hfirst.
    cbn [fst].
    destruct (V1.eval_layouter indices region_start (second value_first))
      as [value_second events_second] eqn:Hsecond.
    cbn [snd].
    rewrite event_writes_app, List.flat_map_app.
    f_equal.
    + exact IHfirst.
    + specialize (IHsecond value_first).
      rewrite Hsecond in IHsecond.
      exact IHsecond.
  - (* AddRegion *)
    destruct (V1.eval_region indices region_start region
        (region_program region)) as [value events] eqn:Hregion.
    cbn [snd].
    rewrite !event_writes_app.
    cbn [event_writes event_write List.app List.flat_map block_writes].
    rewrite !List.app_nil_r.
    pose proof (eval_region_event_writes indices region_start region
      (region_program region)) as Hwrites.
    rewrite Hregion in Hwrites.
    cbn [snd] in Hwrites.
    exact Hwrites.
  - (* InitLookupTables *)
    cbn [snd List.flat_map block_writes].
    rewrite List.app_nil_r.
    reflexivity.
  - (* InNamespace *)
    destruct (V1.eval_layouter indices region_start nested)
      as [value events] eqn:Hnested.
    cbn [snd].
    rewrite !event_writes_app.
    cbn [event_writes event_write List.app].
    rewrite List.app_nil_r.
    exact IHnested.
Qed.

(** ** The placement-generic theorems

    The hypotheses are the two computable conditions: per-block internal
    consistency (placement-independent) and pairwise block compatibility
    under the placement (disjoint region row intervals; column-disjoint
    global blocks).  They imply conflict-freedom of the lowered stream,
    hence replay success from every initial grid. *)
Theorem layouter_conflict_free {columns : Columns.t} {RegionId : Set}
    {A : Set} (indices : Indices.t columns) (region_start : RegionId -> Z)
    (program : 𝓛 columns RegionId A) :
  List.forallb block_ok (layouter_blocks indices program) = true ->
  blocks_compatible_all region_start (layouter_blocks indices program) =
    true ->
  conflict_free (snd (V1.eval_layouter indices region_start program)) = true.
Proof.
  intros Hok Hcompat.
  unfold conflict_free.
  rewrite eval_layouter_event_writes.
  exact (blocks_conflict_free region_start _ Hok Hcompat).
Qed.

Theorem layouter_replay_succeeds {columns : Columns.t} {RegionId : Set}
    {A : Set} (indices : Indices.t columns) (region_start : RegionId -> Z)
    (program : 𝓛 columns RegionId A) :
  List.forallb block_ok (layouter_blocks indices program) = true ->
  blocks_compatible_all region_start (layouter_blocks indices program) =
    true ->
  forall grid : RawGrid.t,
  exists grid',
    apply_events (snd (V1.eval_layouter indices region_start program)) grid =
      Some grid'.
Proof.
  intros Hok Hcompat.
  apply conflict_free_apply_events.
  apply layouter_conflict_free; assumption.
Qed.

(** The same statement with an appended global tail — the shape of the
    Orchard stream, whose floor-planner constants block follows the
    layouter events.  The tail enters as one more global block, so its
    consistency and its column-disjointness from the region writes are
    checked by the same block conditions. *)
Theorem layouter_with_tail_replay_succeeds {columns : Columns.t}
    {RegionId : Set} {A : Set} (indices : Indices.t columns)
    (region_start : RegionId -> Z) (program : 𝓛 columns RegionId A)
    (tail : list Raw.Event.t) :
  List.forallb block_ok
    (layouter_blocks indices program ++
      [Block.Global (event_writes tail)]) = true ->
  blocks_compatible_all region_start
    (layouter_blocks indices program ++
      [Block.Global (event_writes tail)]) = true ->
  forall grid : RawGrid.t,
  exists grid',
    apply_events
      (snd (V1.eval_layouter indices region_start program) ++ tail) grid =
      Some grid'.
Proof.
  intros Hok Hcompat grid.
  apply conflict_free_apply_events.
  unfold conflict_free.
  rewrite event_writes_app, eval_layouter_event_writes.
  pose proof (blocks_conflict_free region_start _ Hok Hcompat) as Hfree.
  rewrite List.flat_map_app in Hfree.
  cbn [List.flat_map block_writes] in Hfree.
  rewrite List.app_nil_r in Hfree.
  exact Hfree.
Qed.
