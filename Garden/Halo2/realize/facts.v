(** * Operational soundness, conjunct 2: program-determined facts.

    Replay success pins every cell a synthesis event writes: a later event
    that would change an already-written cell to a different value makes
    [apply_events] return [None], so in a successfully replayed grid each
    write still holds its value — the frame property "later events agree
    with earlier writes on any shared footprint cell", derived here from
    the replay log ([log_pins_grid]) rather than assumed as a layout
    hypothesis.  On top of it, the program-determined facts of a synthesis
    program — [Fact.SelectorOn], [Fact.FixedIs], [Fact.LookupTableLoaded],
    selected by [determined_facts] — hold in the realized assignment, the
    second conjunct of the operational-soundness statement.  The remaining
    facts ([Fact.CellsEqual], [Fact.InstanceIs], [Fact.CellIsConstant]) are
    witness-dependent permutation obligations: their events change no grid
    value, so no replay can establish them. *)

Require Import Garden.Halo2.main.
Require Import Garden.Halo2.Synthesis.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.serialize.
Require Import Garden.Halo2.realize.main.
Require Import Stdlib.micromega.Lia.

Import ListNotations.
Global Open Scope Z_scope.

(** ** Program-determined facts

    The footprint of a synthesis program is the set of raw cells its events
    write: selector enables, fixed assignments and lookup-table loads.  The
    facts below are exactly the ones whose content is such a write; the
    other constructors reify permutation obligations over the events and
    depend on the witness planes. *)
Definition fact_is_determined {columns : Columns.t} {RegionId : Set}
    (fact : Fact.t columns RegionId) : bool :=
  match fact with
  | Fact.SelectorOn _ _ _ => true
  | Fact.FixedIs _ _ _ _ => true
  | Fact.LookupTableLoaded _ _ _ => true
  | Fact.CellsEqual _ _ => false
  | Fact.InstanceIs _ _ _ => false
  | Fact.CellIsConstant _ _ => false
  end.

Definition determined_facts {columns : Columns.t} {RegionId : Set}
    (facts : list (Fact.t columns RegionId))
    : list (Fact.t columns RegionId) :=
  List.filter fact_is_determined facts.

Lemma determined_facts_app {columns : Columns.t} {RegionId : Set}
    (facts1 facts2 : list (Fact.t columns RegionId)) :
  determined_facts (facts1 ++ facts2) =
    determined_facts facts1 ++ determined_facts facts2.
Proof.
  apply List.filter_app.
Qed.

Lemma interpret_facts_of_in {columns : Columns.t} {RegionId : Set}
    (assignment : Assignment.t columns RegionId)
    (facts : list (Fact.t columns RegionId)) :
  (forall fact, List.In fact facts -> interpret_fact assignment fact) ->
  interpret_facts assignment facts.
Proof.
  induction facts as [| fact facts IH]; intros Hfacts; cbn.
  - exact I.
  - split.
    + apply Hfacts, List.in_eq.
    + apply IH.
      intros fact' Hin.
      apply Hfacts, List.in_cons, Hin.
Qed.

(** ** Conflict checks read as value agreement

    [List.existsb check log = false] says no logged write conflicts with
    the pending one; at a shared footprint cell this forces the values to
    agree. *)

Lemma existsb_false_forall {A : Type} (check : A -> bool) (l : list A) :
  List.existsb check l = false ->
  forall x, List.In x l -> check x = false.
Proof.
  intros Hno x Hin.
  destruct (check x) eqn:Hx; [| reflexivity].
  enough (List.existsb check l = true) by congruence.
  apply List.existsb_exists.
  eauto.
Qed.

Lemma write_conflicts_write_false (column row value : Z) (write : Write.t) :
  write_conflicts_write column row value write = false ->
  write.(Write.column) = column ->
  write.(Write.row) = row ->
  write.(Write.value) = value.
Proof.
  unfold write_conflicts_write.
  intros Hcheck Hcolumn Hrow.
  rewrite Hcolumn, Hrow, !Z.eqb_refl in Hcheck.
  cbn in Hcheck.
  destruct (write.(Write.value) =? value) eqn:Hvalue.
  - apply Z.eqb_eq in Hvalue.
    exact Hvalue.
  - discriminate Hcheck.
Qed.

Lemma write_conflicts_fill_false (column row value : Z) (fill : Fill.t) :
  write_conflicts_fill column row value fill = false ->
  fill.(Fill.column) = column ->
  fill.(Fill.from_row) <= row ->
  row < fill.(Fill.to_row) ->
  fill.(Fill.value) = value.
Proof.
  unfold write_conflicts_fill.
  intros Hcheck Hcolumn Hle Hlt.
  rewrite Hcolumn, Z.eqb_refl in Hcheck.
  rewrite (proj2 (Z.leb_le fill.(Fill.from_row) row) Hle) in Hcheck.
  rewrite (proj2 (Z.ltb_lt row fill.(Fill.to_row)) Hlt) in Hcheck.
  cbn in Hcheck.
  destruct (fill.(Fill.value) =? value) eqn:Hvalue.
  - apply Z.eqb_eq in Hvalue.
    exact Hvalue.
  - discriminate Hcheck.
Qed.

Lemma fill_conflicts_write_false (column from_row to_row value : Z)
    (write : Write.t) :
  fill_conflicts_write column from_row to_row value write = false ->
  write.(Write.column) = column ->
  from_row <= write.(Write.row) ->
  write.(Write.row) < to_row ->
  write.(Write.value) = value.
Proof.
  unfold fill_conflicts_write.
  intros Hcheck Hcolumn Hle Hlt.
  rewrite Hcolumn, Z.eqb_refl in Hcheck.
  rewrite (proj2 (Z.leb_le from_row write.(Write.row)) Hle) in Hcheck.
  rewrite (proj2 (Z.ltb_lt write.(Write.row) to_row) Hlt) in Hcheck.
  cbn in Hcheck.
  destruct (write.(Write.value) =? value) eqn:Hvalue.
  - apply Z.eqb_eq in Hvalue.
    exact Hvalue.
  - discriminate Hcheck.
Qed.

Lemma fill_conflicts_fill_false (column from_row to_row value : Z)
    (fill : Fill.t) :
  fill_conflicts_fill column from_row to_row value fill = false ->
  fill.(Fill.column) = column ->
  Z.max from_row fill.(Fill.from_row) < Z.min to_row fill.(Fill.to_row) ->
  fill.(Fill.value) = value.
Proof.
  unfold fill_conflicts_fill.
  intros Hcheck Hcolumn Hinter.
  rewrite Hcolumn, Z.eqb_refl in Hcheck.
  rewrite (proj2 (Z.ltb_lt _ _) Hinter) in Hcheck.
  cbn in Hcheck.
  destruct (fill.(Fill.value) =? value) eqn:Hvalue.
  - apply Z.eqb_eq in Hvalue.
    exact Hvalue.
  - discriminate Hcheck.
Qed.

(** ** The replay log pins the grid

    Invariant of the replay: every logged write still holds its value in
    the current grid.  A later event either misses the logged footprint
    (the grid keeps the old value there) or hits it, in which case the
    conflict check forces the rewritten value to be equal — a differing
    rewrite would have returned [None]. *)
Definition log_pins_grid (log : Log.t) (grid : RawGrid.t) : Prop :=
  (forall write,
    List.In write log.(Log.selectors) ->
    grid.(RawGrid.sel) write.(Write.column) write.(Write.row) =
      write.(Write.value)) /\
  (forall write,
    List.In write log.(Log.fixeds) ->
    grid.(RawGrid.cell) Raw.ColumnKind.Fixed
      write.(Write.column) write.(Write.row) =
      write.(Write.value)) /\
  (forall fill row,
    List.In fill log.(Log.fills) ->
    fill.(Fill.from_row) <= row ->
    row < fill.(Fill.to_row) ->
    grid.(RawGrid.cell) Raw.ColumnKind.Fixed fill.(Fill.column) row =
      fill.(Fill.value)).

Lemma log_pins_grid_empty (grid : RawGrid.t) :
  log_pins_grid Log.empty grid.
Proof.
  split; [| split]; cbn; intros; contradiction.
Qed.

Lemma apply_event_pins (state state' : ReplayState.t) (event : Raw.Event.t) :
  apply_event state event = Some state' ->
  log_pins_grid state.(ReplayState.log) state.(ReplayState.grid) ->
  log_pins_grid state'.(ReplayState.log) state'.(ReplayState.grid).
Proof.
  intros Happly Hpins.
  revert Happly.
  destruct event as
    [name | name | name | name | column row annotation
    | column row annotation value | left_cell right_cell
    | column from_row to_row value];
    cbn;
    try (intros Happly; injection Happly as <-; exact Hpins).
  - (* EnableSelector *)
    destruct (List.existsb (write_conflicts_write column row 1)
        state.(ReplayState.log).(Log.selectors)) eqn:Hconflict;
      intros Happly; [discriminate |].
    injection Happly as <-.
    destruct Hpins as (Hsel & Hfixed & Hfill).
    split; [| split]; cbn.
    + intros write [<- | Hin]; cbn.
      * rewrite !Z.eqb_refl.
        reflexivity.
      * destruct (andb (write.(Write.column) =? column)
            (write.(Write.row) =? row)) eqn:Hpoint.
        -- apply andb_prop in Hpoint.
           destruct Hpoint as [Hcolumn_eq Hrow_eq].
           apply Z.eqb_eq in Hcolumn_eq, Hrow_eq.
           rewrite (write_conflicts_write_false column row 1 write
             (existsb_false_forall _ _ Hconflict write Hin)
             Hcolumn_eq Hrow_eq).
           reflexivity.
        -- apply Hsel, Hin.
    + exact Hfixed.
    + exact Hfill.
  - (* AssignFixed *)
    destruct (List.existsb (write_conflicts_write column row value)
        state.(ReplayState.log).(Log.fixeds)) eqn:Hconflict_write;
      intros Happly; [discriminate |].
    revert Happly.
    destruct (List.existsb (write_conflicts_fill column row value)
        state.(ReplayState.log).(Log.fills)) eqn:Hconflict_fill;
      intros Happly; [discriminate |].
    injection Happly as <-.
    destruct Hpins as (Hsel & Hfixed & Hfill).
    split; [| split]; cbn.
    + exact Hsel.
    + intros write [<- | Hin]; cbn.
      * rewrite !Z.eqb_refl.
        reflexivity.
      * destruct (andb (write.(Write.column) =? column)
            (write.(Write.row) =? row)) eqn:Hpoint.
        -- apply andb_prop in Hpoint.
           destruct Hpoint as [Hcolumn_eq Hrow_eq].
           apply Z.eqb_eq in Hcolumn_eq, Hrow_eq.
           rewrite (write_conflicts_write_false column row value write
             (existsb_false_forall _ _ Hconflict_write write Hin)
             Hcolumn_eq Hrow_eq).
           reflexivity.
        -- apply Hfixed, Hin.
    + intros fill fill_row Hin Hle Hlt; cbn.
      destruct (andb (fill.(Fill.column) =? column)
          (fill_row =? row)) eqn:Hpoint.
      * apply andb_prop in Hpoint.
        destruct Hpoint as [Hcolumn_eq Hrow_eq].
        apply Z.eqb_eq in Hcolumn_eq, Hrow_eq.
        subst fill_row.
        rewrite (write_conflicts_fill_false column row value fill
          (existsb_false_forall _ _ Hconflict_fill fill Hin)
          Hcolumn_eq Hle Hlt).
        reflexivity.
      * apply Hfill; assumption.
  - (* FillFromRow *)
    destruct (List.existsb (fill_conflicts_write column from_row to_row value)
        state.(ReplayState.log).(Log.fixeds)) eqn:Hconflict_write;
      intros Happly; [discriminate |].
    revert Happly.
    destruct (List.existsb (fill_conflicts_fill column from_row to_row value)
        state.(ReplayState.log).(Log.fills)) eqn:Hconflict_fill;
      intros Happly; [discriminate |].
    injection Happly as <-.
    destruct Hpins as (Hsel & Hfixed & Hfill).
    split; [| split]; cbn.
    + exact Hsel.
    + intros write Hin; cbn.
      destruct (andb (write.(Write.column) =? column)
          (andb (from_row <=? write.(Write.row))
            (write.(Write.row) <? to_row))) eqn:Hcover.
      * apply andb_prop in Hcover.
        destruct Hcover as [Hcolumn_eq Hextent].
        apply andb_prop in Hextent.
        destruct Hextent as [Hrow_le Hrow_lt].
        apply Z.eqb_eq in Hcolumn_eq.
        apply Z.leb_le in Hrow_le.
        apply Z.ltb_lt in Hrow_lt.
        rewrite (fill_conflicts_write_false column from_row to_row value write
          (existsb_false_forall _ _ Hconflict_write write Hin)
          Hcolumn_eq Hrow_le Hrow_lt).
        reflexivity.
      * apply Hfixed, Hin.
    + intros fill fill_row [<- | Hin] Hle Hlt.
      * (* the fill just performed *)
        cbn in Hle, Hlt |- *.
        rewrite Z.eqb_refl.
        rewrite (proj2 (Z.leb_le from_row fill_row) Hle).
        rewrite (proj2 (Z.ltb_lt fill_row to_row) Hlt).
        reflexivity.
      * cbn.
        destruct (andb (fill.(Fill.column) =? column)
            (andb (from_row <=? fill_row) (fill_row <? to_row))) eqn:Hcover.
        -- apply andb_prop in Hcover.
           destruct Hcover as [Hcolumn_eq Hextent].
           apply andb_prop in Hextent.
           destruct Hextent as [Hfrom_le Hto_lt].
           apply Z.eqb_eq in Hcolumn_eq.
           apply Z.leb_le in Hfrom_le.
           apply Z.ltb_lt in Hto_lt.
           assert (Hinter : Z.max from_row fill.(Fill.from_row) <
                            Z.min to_row fill.(Fill.to_row)) by lia.
           rewrite (fill_conflicts_fill_false column from_row to_row value fill
             (existsb_false_forall _ _ Hconflict_fill fill Hin)
             Hcolumn_eq Hinter).
           reflexivity.
        -- apply Hfill; assumption.
Qed.

Lemma apply_events_log_pins (events : list Raw.Event.t)
    (state state' : ReplayState.t) :
  apply_events_log events state = Some state' ->
  log_pins_grid state.(ReplayState.log) state.(ReplayState.grid) ->
  log_pins_grid state'.(ReplayState.log) state'.(ReplayState.grid).
Proof.
  revert state.
  induction events as [| event events IH]; intros state Happly Hpins;
    cbn in Happly.
  - injection Happly as <-.
    exact Hpins.
  - destruct (apply_event state event) as [state1 |] eqn:Hevent;
      [| discriminate].
    exact (IH state1 Happly (apply_event_pins _ _ _ Hevent Hpins)).
Qed.

(** ** The log grows monotonically along the replay *)

Definition log_extends (log log' : Log.t) : Prop :=
  (forall write,
    List.In write log.(Log.selectors) ->
    List.In write log'.(Log.selectors)) /\
  (forall write,
    List.In write log.(Log.fixeds) ->
    List.In write log'.(Log.fixeds)) /\
  (forall fill,
    List.In fill log.(Log.fills) ->
    List.In fill log'.(Log.fills)).

Lemma log_extends_refl (log : Log.t) : log_extends log log.
Proof.
  split; [| split]; intros; assumption.
Qed.

Lemma log_extends_trans (log1 log2 log3 : Log.t) :
  log_extends log1 log2 ->
  log_extends log2 log3 ->
  log_extends log1 log3.
Proof.
  intros (H1sel & H1fixed & H1fill) (H2sel & H2fixed & H2fill).
  split; [| split]; auto.
Qed.

Lemma apply_event_log_extends (state state' : ReplayState.t)
    (event : Raw.Event.t) :
  apply_event state event = Some state' ->
  log_extends state.(ReplayState.log) state'.(ReplayState.log).
Proof.
  destruct event as
    [name | name | name | name | column row annotation
    | column row annotation value | left_cell right_cell
    | column from_row to_row value];
    cbn;
    try (intros Happly; injection Happly as <-; apply log_extends_refl).
  - (* EnableSelector *)
    destruct (List.existsb (write_conflicts_write column row 1)
        state.(ReplayState.log).(Log.selectors));
      intros Happly; [discriminate |].
    injection Happly as <-.
    split; [| split]; cbn; intros; [right |..]; assumption.
  - (* AssignFixed *)
    destruct (List.existsb (write_conflicts_write column row value)
        state.(ReplayState.log).(Log.fixeds));
      intros Happly; [discriminate |].
    revert Happly.
    destruct (List.existsb (write_conflicts_fill column row value)
        state.(ReplayState.log).(Log.fills));
      intros Happly; [discriminate |].
    injection Happly as <-.
    split; [| split]; cbn; intros; [| right |]; assumption.
  - (* FillFromRow *)
    destruct (List.existsb (fill_conflicts_write column from_row to_row value)
        state.(ReplayState.log).(Log.fixeds));
      intros Happly; [discriminate |].
    revert Happly.
    destruct (List.existsb (fill_conflicts_fill column from_row to_row value)
        state.(ReplayState.log).(Log.fills));
      intros Happly; [discriminate |].
    injection Happly as <-.
    split; [| split]; cbn; intros; [.. | right]; assumption.
Qed.

Lemma apply_events_log_extends (events : list Raw.Event.t)
    (state state' : ReplayState.t) :
  apply_events_log events state = Some state' ->
  log_extends state.(ReplayState.log) state'.(ReplayState.log).
Proof.
  revert state.
  induction events as [| event events IH]; intros state Happly;
    cbn in Happly.
  - injection Happly as <-.
    apply log_extends_refl.
  - destruct (apply_event state event) as [state1 |] eqn:Hevent;
      [| discriminate].
    exact (log_extends_trans _ _ _
      (apply_event_log_extends _ _ _ Hevent) (IH _ Happly)).
Qed.

(** ** A replayed write event is logged *)

Lemma apply_event_selector_logged (state state' : ReplayState.t)
    (column row : Z) (annotation : string) :
  apply_event state (Raw.Event.EnableSelector column row annotation) =
    Some state' ->
  List.In
    {| Write.column := column; Write.row := row; Write.value := 1 |}
    state'.(ReplayState.log).(Log.selectors).
Proof.
  cbn.
  destruct (List.existsb (write_conflicts_write column row 1)
      state.(ReplayState.log).(Log.selectors));
    intros Happly; [discriminate |].
  injection Happly as <-.
  apply List.in_eq.
Qed.

Lemma apply_event_fixed_logged (state state' : ReplayState.t)
    (column row : Z) (annotation : string) (value : Z) :
  apply_event state (Raw.Event.AssignFixed column row annotation value) =
    Some state' ->
  List.In
    {| Write.column := column; Write.row := row; Write.value := value |}
    state'.(ReplayState.log).(Log.fixeds).
Proof.
  cbn.
  destruct (List.existsb (write_conflicts_write column row value)
      state.(ReplayState.log).(Log.fixeds));
    intros Happly; [discriminate |].
  revert Happly.
  destruct (List.existsb (write_conflicts_fill column row value)
      state.(ReplayState.log).(Log.fills));
    intros Happly; [discriminate |].
  injection Happly as <-.
  apply List.in_eq.
Qed.

Lemma apply_event_fill_logged (state state' : ReplayState.t)
    (column from_row to_row value : Z) :
  apply_event state (Raw.Event.FillFromRow column from_row to_row value) =
    Some state' ->
  List.In
    {|
      Fill.column := column;
      Fill.from_row := from_row;
      Fill.to_row := to_row;
      Fill.value := value;
    |}
    state'.(ReplayState.log).(Log.fills).
Proof.
  cbn.
  destruct (List.existsb (fill_conflicts_write column from_row to_row value)
      state.(ReplayState.log).(Log.fixeds));
    intros Happly; [discriminate |].
  revert Happly.
  destruct (List.existsb (fill_conflicts_fill column from_row to_row value)
      state.(ReplayState.log).(Log.fills));
    intros Happly; [discriminate |].
  injection Happly as <-.
  apply List.in_eq.
Qed.

Lemma apply_events_log_selector_in (events : list Raw.Event.t)
    (state state' : ReplayState.t)
    (column row : Z) (annotation : string) :
  apply_events_log events state = Some state' ->
  List.In (Raw.Event.EnableSelector column row annotation) events ->
  List.In
    {| Write.column := column; Write.row := row; Write.value := 1 |}
    state'.(ReplayState.log).(Log.selectors).
Proof.
  revert state.
  induction events as [| event events IH]; intros state Happly Hin;
    [contradiction |].
  cbn in Happly.
  destruct (apply_event state event) as [state1 |] eqn:Hevent;
    [| discriminate].
  destruct Hin as [-> | Hin].
  - destruct (apply_events_log_extends _ _ _ Happly) as (Hmono & _ & _).
    apply Hmono.
    exact (apply_event_selector_logged _ _ _ _ _ Hevent).
  - exact (IH _ Happly Hin).
Qed.

Lemma apply_events_log_fixed_in (events : list Raw.Event.t)
    (state state' : ReplayState.t)
    (column row : Z) (annotation : string) (value : Z) :
  apply_events_log events state = Some state' ->
  List.In (Raw.Event.AssignFixed column row annotation value) events ->
  List.In
    {| Write.column := column; Write.row := row; Write.value := value |}
    state'.(ReplayState.log).(Log.fixeds).
Proof.
  revert state.
  induction events as [| event events IH]; intros state Happly Hin;
    [contradiction |].
  cbn in Happly.
  destruct (apply_event state event) as [state1 |] eqn:Hevent;
    [| discriminate].
  destruct Hin as [-> | Hin].
  - destruct (apply_events_log_extends _ _ _ Happly) as (_ & Hmono & _).
    apply Hmono.
    exact (apply_event_fixed_logged _ _ _ _ _ _ Hevent).
  - exact (IH _ Happly Hin).
Qed.

Lemma apply_events_log_fill_in (events : list Raw.Event.t)
    (state state' : ReplayState.t)
    (column from_row to_row value : Z) :
  apply_events_log events state = Some state' ->
  List.In (Raw.Event.FillFromRow column from_row to_row value) events ->
  List.In
    {|
      Fill.column := column;
      Fill.from_row := from_row;
      Fill.to_row := to_row;
      Fill.value := value;
    |}
    state'.(ReplayState.log).(Log.fills).
Proof.
  revert state.
  induction events as [| event events IH]; intros state Happly Hin;
    [contradiction |].
  cbn in Happly.
  destruct (apply_event state event) as [state1 |] eqn:Hevent;
    [| discriminate].
  destruct Hin as [-> | Hin].
  - destruct (apply_events_log_extends _ _ _ Happly) as (_ & _ & Hmono).
    apply Hmono.
    exact (apply_event_fill_logged _ _ _ _ _ _ Hevent).
  - exact (IH _ Happly Hin).
Qed.

(** ** Replay success pins every written cell of the final grid *)

Lemma replay_selector_pinned (events : list Raw.Event.t)
    (initial final : RawGrid.t) (column row : Z) (annotation : string) :
  apply_events events initial = Some final ->
  List.In (Raw.Event.EnableSelector column row annotation) events ->
  final.(RawGrid.sel) column row = 1.
Proof.
  unfold apply_events.
  destruct (apply_events_log events (ReplayState.init initial))
    as [state |] eqn:Hreplay; [| discriminate].
  intros Hfinal Hin.
  injection Hfinal as <-.
  destruct (apply_events_log_pins _ _ _ Hreplay (log_pins_grid_empty initial))
    as (Hsel & _ & _).
  exact (Hsel _ (apply_events_log_selector_in _ _ _ _ _ _ Hreplay Hin)).
Qed.

Lemma replay_fixed_pinned (events : list Raw.Event.t)
    (initial final : RawGrid.t)
    (column row : Z) (annotation : string) (value : Z) :
  apply_events events initial = Some final ->
  List.In (Raw.Event.AssignFixed column row annotation value) events ->
  final.(RawGrid.cell) Raw.ColumnKind.Fixed column row = value.
Proof.
  unfold apply_events.
  destruct (apply_events_log events (ReplayState.init initial))
    as [state |] eqn:Hreplay; [| discriminate].
  intros Hfinal Hin.
  injection Hfinal as <-.
  destruct (apply_events_log_pins _ _ _ Hreplay (log_pins_grid_empty initial))
    as (_ & Hfixed & _).
  exact (Hfixed _ (apply_events_log_fixed_in _ _ _ _ _ _ _ Hreplay Hin)).
Qed.

Lemma replay_fill_pinned (events : list Raw.Event.t)
    (initial final : RawGrid.t) (column from_row to_row value row : Z) :
  apply_events events initial = Some final ->
  List.In (Raw.Event.FillFromRow column from_row to_row value) events ->
  from_row <= row ->
  row < to_row ->
  final.(RawGrid.cell) Raw.ColumnKind.Fixed column row = value.
Proof.
  unfold apply_events.
  destruct (apply_events_log events (ReplayState.init initial))
    as [state |] eqn:Hreplay; [| discriminate].
  intros Hfinal Hin Hle Hlt.
  injection Hfinal as <-.
  destruct (apply_events_log_pins _ _ _ Hreplay (log_pins_grid_empty initial))
    as (_ & _ & Hfill).
  exact (Hfill _ _ (apply_events_log_fill_in _ _ _ _ _ _ _ Hreplay Hin) Hle Hlt).
Qed.

(** ** Where the table-load events land

    [V1.init_lookup_table_events] assigns each entry's rows [0 ..
    length values) and fills the rows [length values .. usable_rows) with the
    default value; the lemmas below exhibit the corresponding events as
    members of the emitted stream. *)

Lemma value_at_row_some (row : nat) (values : list Z) (default_value : Z) :
  (row < List.length values)%nat ->
  V1.value_at_row row values = Some (List.nth row values default_value).
Proof.
  revert values.
  induction row as [| row IH]; intros [| value values] Hlt; cbn in *.
  - lia.
  - reflexivity.
  - lia.
  - apply IH.
    lia.
Qed.

Lemma assign_lookup_row_in {columns : Columns.t}
    (idx : Indices.t columns) (row : nat)
    (entries : list (LookupTableColumn.t columns))
    (entry : LookupTableColumn.t columns) (event : Raw.Event.t) :
  List.In entry entries ->
  List.In event (V1.assign_lookup_entry_at_row idx row entry) ->
  List.In event (V1.assign_lookup_row idx row entries).
Proof.
  induction entries as [| entry' entries IH]; intros Hentry Hevent;
    [contradiction |].
  cbn.
  apply List.in_or_app.
  destruct Hentry as [-> | Hentry].
  - left.
    exact Hevent.
  - right.
    apply IH; assumption.
Qed.

Lemma assign_lookup_rows_in {columns : Columns.t}
    (idx : Indices.t columns) (rows_remaining start row : nat)
    (entries : list (LookupTableColumn.t columns)) (event : Raw.Event.t) :
  (start <= row < start + rows_remaining)%nat ->
  List.In event (V1.assign_lookup_row idx row entries) ->
  List.In event (V1.assign_lookup_rows idx rows_remaining start entries).
Proof.
  revert start.
  induction rows_remaining as [| rows_remaining IH]; intros start Hrange Hevent;
    cbn; [lia |].
  apply List.in_or_app.
  destruct (Nat.eq_dec start row) as [-> | Hneq].
  - left.
    exact Hevent.
  - right.
    apply IH; [lia | exact Hevent].
Qed.

Lemma max_entry_length_bound {columns : Columns.t}
    (entries : list (LookupTableColumn.t columns))
    (entry : LookupTableColumn.t columns) :
  List.In entry entries ->
  (List.length (LookupTableColumn.values entry) <=
    V1.max_entry_length entries)%nat.
Proof.
  induction entries as [| entry' entries IH]; intros Hentry;
    [contradiction |].
  destruct Hentry as [-> | Hentry]; cbn.
  - lia.
  - pose proof (IH Hentry).
    lia.
Qed.

Section DeterminedFacts.
  Context {columns : Columns.t}.
  Context {RegionId : Set}.

  (** Value agreement between the two interpreters, needed to line up the
      [Bind] recursions: the relational side threads [region_value] /
      [layouter_value] where the operational side threads the value
      component of [V1.eval_region] / [V1.eval_layouter]. *)
  Lemma region_value_agrees {A : Set}
      (idx : Indices.t columns) (rs : RegionId -> Z) (region : RegionId)
      (program : 𝓡 columns RegionId A) :
    region_value program = fst (V1.eval_region idx rs region program).
  Proof.
    induction program as
      [A value | A B first IHfirst second IHsecond
      | selector offset annotation | annotation column offset value
      | left_cell right_cell | cell value];
      cbn [region_value V1.eval_region]; try reflexivity.
    rewrite IHfirst.
    destruct (V1.eval_region idx rs region first)
      as [value_first events_first].
    cbn [fst].
    rewrite (IHsecond value_first).
    destruct (V1.eval_region idx rs region (second value_first))
      as [value_second events_second].
    reflexivity.
  Qed.

  Lemma layouter_value_agrees {A : Set}
      (idx : Indices.t columns) (rs : RegionId -> Z) (usable_rows : Z)
      (program : 𝓛 columns RegionId A) :
    layouter_value program = fst (V1.eval_layouter idx rs usable_rows program).
  Proof.
    induction program as
      [A value | A B first IHfirst second IHsecond
      | A region name region_program | cell instance row
      | name entries | A name nested IHnested];
      cbn [layouter_value V1.eval_layouter]; try reflexivity.
    - (* Bind *)
      rewrite IHfirst.
      destruct (V1.eval_layouter idx rs usable_rows first)
        as [value_first events_first].
      cbn [fst].
      rewrite (IHsecond value_first).
      destruct (V1.eval_layouter idx rs usable_rows (second value_first))
        as [value_second events_second].
      reflexivity.
    - (* AddRegion *)
      rewrite (region_value_agrees idx rs region (region_program region)).
      destruct (V1.eval_region idx rs region (region_program region))
        as [value events].
      reflexivity.
    - (* InNamespace *)
      rewrite IHnested.
      destruct (V1.eval_layouter idx rs usable_rows nested) as [value events].
      reflexivity.
  Qed.

  Section PinnedGrid.
    Variable grid : RawGrid.t.
    Variable events_all : list Raw.Event.t.

    (** The pinning facts a successful replay provides for the two
        program-determined planes ([replay_selector_pinned] /
        [replay_fixed_pinned]), abstracted over the event list so that the
        induction below can pass to sub-lists of the replayed stream by
        [List.incl].  Rows of a table column past its value-list length are no
        longer program-determined (the keygen-faithful fill leaves the
        [l_last] and blinding tail unwritten), so the fill-pinning
        [replay_fill_pinned] is consumed operationally rather than as a
        pinning hypothesis here. *)
    Hypothesis H_selector_pinned :
      forall (column row : Z) (annotation : string),
        List.In (Raw.Event.EnableSelector column row annotation) events_all ->
        grid.(RawGrid.sel) column row = 1.
    Hypothesis H_fixed_pinned :
      forall (column row : Z) (annotation : string) (value : Z),
        List.In (Raw.Event.AssignFixed column row annotation value)
          events_all ->
        grid.(RawGrid.cell) Raw.ColumnKind.Fixed column row = value.

    (** The [Fact.LookupTableLoaded] interpretation for one table entry over
        its assigned rows [0 .. length values): each such row is pinned by the
        corresponding [AssignFixed] row-assignment event. *)
    Lemma lookup_entry_pinned (idx : Indices.t columns) (usable_rows : Z)
        (name : string)
        (entries : list (LookupTableColumn.t columns))
        (entry : LookupTableColumn.t columns)
        (Hentry : List.In entry entries)
        (Hincl :
          List.incl (V1.init_lookup_table_events idx usable_rows name entries)
            events_all)
        (row : Z)
        (Hrow :
          0 <= row < Z.of_nat (List.length (LookupTableColumn.values entry))) :
      grid.(RawGrid.cell) Raw.ColumnKind.Fixed
        (idx.(Indices.lookup) (LookupTableColumn.lookup entry)) row =
      value_at_row row (LookupTableColumn.values entry)
        (LookupTableColumn.default_value entry).
    Proof.
      unfold value_at_row.
      assert (Hrow_eq : row = Z.of_nat (Z.to_nat row)) by lia.
      assert (Hlt : (Z.to_nat row <
          List.length (LookupTableColumn.values entry))%nat) by lia.
      rewrite Hrow_eq, Nat2Z.id.
      apply (H_fixed_pinned _ _ (LookupTableColumn.annotation entry)).
      apply Hincl.
      unfold V1.init_lookup_table_events.
      apply List.in_or_app; right.
      apply List.in_or_app; left.
      apply (assign_lookup_rows_in idx (V1.max_entry_length entries)
        0%nat (Z.to_nat row) entries).
      + pose proof (max_entry_length_bound entries entry Hentry).
        lia.
      + apply (assign_lookup_row_in idx (Z.to_nat row) entries entry _
          Hentry).
        unfold V1.assign_lookup_entry_at_row.
        rewrite (value_at_row_some (Z.to_nat row)
          (LookupTableColumn.values entry)
          (LookupTableColumn.default_value entry) Hlt).
        apply List.in_eq.
    Qed.

    Lemma region_determined_facts
        (idx : Indices.t columns) (rs : RegionId -> Z) (region : RegionId)
        {A : Set} (program : 𝓡 columns RegionId A) :
      List.incl (snd (V1.eval_region idx rs region program)) events_all ->
      interpret_facts (realize idx rs grid)
        (determined_facts (region_facts region program)).
    Proof.
      induction program as
        [A value | A B first IHfirst second IHsecond
        | selector offset annotation | annotation column offset value
        | left_cell right_cell | cell value].
      - (* Ret *)
        intros _.
        exact I.
      - (* Bind *)
        cbn [V1.eval_region region_facts].
        rewrite (region_value_agrees idx rs region first).
        destruct (V1.eval_region idx rs region first)
          as [value_first events_first] eqn:Hfirst.
        cbn [fst snd].
        destruct (V1.eval_region idx rs region (second value_first))
          as [value_second events_second] eqn:Hsecond.
        cbn [snd].
        intros Hincl.
        apply List.incl_app_inv in Hincl.
        destruct Hincl as [Hincl_first Hincl_second].
        rewrite determined_facts_app, interpret_facts_app.
        split.
        + apply IHfirst.
          exact Hincl_first.
        + apply (IHsecond value_first).
          rewrite Hsecond.
          exact Hincl_second.
      - (* EnableSelector *)
        cbn.
        intros Hincl.
        split; [| exact I].
        apply (H_selector_pinned _ _ annotation).
        apply Hincl.
        apply List.in_eq.
      - (* AssignFixed *)
        cbn.
        intros Hincl.
        split; [| exact I].
        apply (H_fixed_pinned _ _ annotation).
        apply Hincl.
        apply List.in_eq.
      - (* Copy: a permutation obligation, filtered out *)
        intros _.
        exact I.
      - (* ConstrainConstant: a permutation obligation, filtered out *)
        intros _.
        exact I.
    Qed.

    Lemma layouter_determined_facts
        (idx : Indices.t columns) (rs : RegionId -> Z) (usable_rows : Z)
        {A : Set} (program : 𝓛 columns RegionId A) :
      List.incl (snd (V1.eval_layouter idx rs usable_rows program)) events_all ->
      interpret_facts (realize idx rs grid)
        (determined_facts (layouter_facts program)).
    Proof.
      induction program as
        [A value | A B first IHfirst second IHsecond
        | A region name region_program | cell instance row
        | name entries | A name nested IHnested].
      - (* Ret *)
        intros _.
        exact I.
      - (* Bind *)
        cbn [V1.eval_layouter layouter_facts].
        rewrite (layouter_value_agrees idx rs usable_rows first).
        destruct (V1.eval_layouter idx rs usable_rows first)
          as [value_first events_first] eqn:Hfirst.
        cbn [fst snd].
        destruct (V1.eval_layouter idx rs usable_rows (second value_first))
          as [value_second events_second] eqn:Hsecond.
        cbn [snd].
        intros Hincl.
        apply List.incl_app_inv in Hincl.
        destruct Hincl as [Hincl_first Hincl_second].
        rewrite determined_facts_app, interpret_facts_app.
        split.
        + apply IHfirst.
          exact Hincl_first.
        + apply (IHsecond value_first).
          rewrite Hsecond.
          exact Hincl_second.
      - (* AddRegion *)
        cbn [V1.eval_layouter layouter_facts].
        destruct (V1.eval_region idx rs region (region_program region))
          as [value events] eqn:Hregion.
        cbn [snd].
        intros Hincl.
        apply (region_determined_facts idx rs region).
        rewrite Hregion.
        cbn [snd].
        intros event Hevent.
        apply Hincl.
        apply List.in_or_app; right.
        apply List.in_or_app; left.
        exact Hevent.
      - (* ConstrainInstance: a permutation obligation, filtered out *)
        intros _.
        exact I.
      - (* InitLookupTables *)
        cbn [V1.eval_layouter layouter_facts snd].
        intros Hincl.
        apply interpret_facts_of_in.
        intros fact Hfact.
        apply List.filter_In in Hfact.
        destruct Hfact as [Hfact _].
        apply List.in_map_iff in Hfact.
        destruct Hfact as (entry & Hfact_eq & Hentry).
        subst fact.
        cbn [interpret_fact].
        intros row Hrow.
        exact (lookup_entry_pinned idx usable_rows name entries entry Hentry
          Hincl row Hrow).
      - (* InNamespace *)
        cbn [V1.eval_layouter layouter_facts].
        destruct (V1.eval_layouter idx rs usable_rows nested)
          as [value events] eqn:Hnested.
        cbn [snd].
        intros Hincl.
        apply IHnested.
        cbn [snd].
        intros event Hevent.
        apply Hincl.
        apply List.in_or_app; right.
        apply List.in_or_app; left.
        exact Hevent.
    Qed.
  End PinnedGrid.

  (** Conjunct 2 of the operational-soundness statement, over any starting
      grid: replay success alone makes the program-determined facts of the
      synthesis program hold in the realized assignment. *)
  Theorem determined_facts_hold
      (idx : Indices.t columns) (rs : RegionId -> Z) (usable_rows : Z)
      {A : Set} (program : 𝓛 columns RegionId A)
      (initial final : RawGrid.t) :
    apply_events (snd (V1.eval_layouter idx rs usable_rows program)) initial =
      Some final ->
    interpret_facts (realize idx rs final)
      (determined_facts (layouter_facts program)).
  Proof.
    intros Hreplay.
    eapply (layouter_determined_facts final
      (snd (V1.eval_layouter idx rs usable_rows program))).
    - intros column row annotation Hin.
      exact (replay_selector_pinned _ _ _ _ _ _ Hreplay Hin).
    - intros column row annotation value Hin.
      exact (replay_fixed_pinned _ _ _ _ _ _ _ Hreplay Hin).
    - apply List.incl_refl.
  Qed.

  (** The same statement at the witness-initialized grid: the form
      consumed by the operational-soundness theorem, whose replay premise
      starts from [initial_grid advice instance_]. *)
  Theorem operational_sound_determined_facts
      (idx : Indices.t columns) (rs : RegionId -> Z) (usable_rows : Z)
      {A : Set} (program : 𝓛 columns RegionId A)
      (advice instance_ : Z -> Z -> Z) (final : RawGrid.t) :
    apply_events (snd (V1.eval_layouter idx rs usable_rows program))
      (initial_grid advice instance_) = Some final ->
    interpret_facts (realize idx rs final)
      (determined_facts (layouter_facts program)).
  Proof.
    apply determined_facts_hold.
  Qed.
End DeterminedFacts.
