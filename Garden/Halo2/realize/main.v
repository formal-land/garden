(** * Realization: replaying serialized events into an operational grid.

    [serialize.v] lowers a synthesis program to a stream of [Raw.Event.t]s
    over [Z]-indexed columns and absolute rows.  This file gives those events
    an operational semantics: a flat grid ([RawGrid.t]), a partial replay
    ([apply_events]) that fails on a conflicting rewrite, and the simulation
    map [realize] reading a relational [Assignment.t] back out of the grid.
    The decision procedures [instance_free] / [flattening_ok] carve out the
    class of constraint systems for which the relational and operational gate
    readings agree. *)

Require Import Garden.Halo2.main.
Require Import Garden.Halo2.Synthesis.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.serialize.

Import ListNotations.
Global Open Scope Z_scope.

(** ** The operational grid *)

Module RawGrid.
  (** A flat, absolute, [Z]-indexed grid: the operational counterpart of the
      relational [Assignment.t].  Lookup columns get no plane of their own —
      the serializer addresses them as fixed columns ([Raw.Event.AssignFixed]
      and [Raw.Event.FillFromRow] both carry a bare [Z] index), so table
      writes land in the [Fixed] plane at the lookup column indexes.  In real
      Halo2 a table column is a fixed column, so the single plane is also the
      faithful reading. *)
  Record t : Set := {
    cell : Raw.ColumnKind.t -> Z (* column index *) -> Z (* absolute row *) -> Z;
    sel : Z (* selector index *) -> Z (* absolute row *) -> Z;
  }.

  Definition set_selector (grid : t) (column row : Z) : t := {|
    cell := grid.(cell);
    sel := fun c r =>
      if andb (c =? column) (r =? row) then 1 else grid.(sel) c r;
  |}.

  Definition set_fixed (grid : t) (column row value : Z) : t := {|
    cell := fun kind c r =>
      match kind with
      | Raw.ColumnKind.Fixed =>
          if andb (c =? column) (r =? row) then value else grid.(cell) kind c r
      | _ => grid.(cell) kind c r
      end;
    sel := grid.(sel);
  |}.

  Definition fill_fixed (grid : t) (column from_row to_row value : Z) : t := {|
    cell := fun kind c r =>
      match kind with
      | Raw.ColumnKind.Fixed =>
          if andb (c =? column) (andb (from_row <=? r) (r <? to_row))
          then value
          else grid.(cell) kind c r
      | _ => grid.(cell) kind c r
      end;
    sel := grid.(sel);
  |}.
End RawGrid.

(** The witness supplies only the free planes; the program-determined planes
    start at zero, mirroring real Halo2, where fixed, selector and table
    cells hold nothing until synthesis writes them. *)
Definition initial_grid (advice instance_ : Z -> Z -> Z) : RawGrid.t := {|
  RawGrid.cell := fun kind column row =>
    match kind with
    | Raw.ColumnKind.Advice => advice column row
    | Raw.ColumnKind.Instance_ => instance_ column row
    | Raw.ColumnKind.Fixed => 0
    end;
  RawGrid.sel := fun _ _ => 0;
|}.

(** ** The write log

    The grid is a function, so "this cell was already written" is not
    decidable from the grid alone.  Replay therefore threads a finite log of
    the performed writes — point writes per plane, plus one record per
    [FillFromRow] for its half-open extent — and the conflict check computes
    over the log. *)

Module Write.
  (** A recorded point write. *)
  Record t : Set := {
    column : Z;
    row : Z;
    value : Z;
  }.
End Write.

Module Fill.
  (** A recorded [FillFromRow]: [value] written to every row of [column] in
      the half-open extent [[from_row, to_row)]. *)
  Record t : Set := {
    column : Z;
    from_row : Z;
    to_row : Z;
    value : Z;
  }.
End Fill.

Module Log.
  Record t : Set := {
    selectors : list Write.t;
    fixeds : list Write.t;
    fills : list Fill.t;
  }.

  Definition empty : t := {|
    selectors := [];
    fixeds := [];
    fills := [];
  |}.

  Definition add_selector (log : t) (write : Write.t) : t := {|
    selectors := write :: log.(selectors);
    fixeds := log.(fixeds);
    fills := log.(fills);
  |}.

  Definition add_fixed (log : t) (write : Write.t) : t := {|
    selectors := log.(selectors);
    fixeds := write :: log.(fixeds);
    fills := log.(fills);
  |}.

  Definition add_fill (log : t) (fill : Fill.t) : t := {|
    selectors := log.(selectors);
    fixeds := log.(fixeds);
    fills := fill :: log.(fills);
  |}.
End Log.

(** A pending point write [(column, row, value)] changes an earlier point
    write to a different value. *)
Definition write_conflicts_write (column row value : Z) (write : Write.t)
    : bool :=
  andb
    (andb (write.(Write.column) =? column) (write.(Write.row) =? row))
    (negb (write.(Write.value) =? value)).

(** A pending point write lands inside an earlier fill's half-open extent
    with a different value. *)
Definition write_conflicts_fill (column row value : Z) (fill : Fill.t)
    : bool :=
  andb
    (andb (fill.(Fill.column) =? column)
      (andb (fill.(Fill.from_row) <=? row) (row <? fill.(Fill.to_row))))
    (negb (fill.(Fill.value) =? value)).

(** A pending fill [(column, from_row, to_row, value)] covers an earlier point
    write inside its half-open extent holding a different value. *)
Definition fill_conflicts_write (column from_row to_row value : Z)
    (write : Write.t) : bool :=
  andb
    (andb (write.(Write.column) =? column)
      (andb (from_row <=? write.(Write.row)) (write.(Write.row) <? to_row)))
    (negb (write.(Write.value) =? value)).

(** Two fills of one column conflict exactly when their half-open extents
    [[from_row, to_row)] and [[fill.from_row, fill.to_row)] intersect and their
    values differ. *)
Definition fill_conflicts_fill (column from_row to_row value : Z)
    (fill : Fill.t) : bool :=
  andb (fill.(Fill.column) =? column)
    (andb
      (Z.max from_row fill.(Fill.from_row) <? Z.min to_row fill.(Fill.to_row))
      (negb (fill.(Fill.value) =? value))).

(** ** Partial event replay *)

Module ReplayState.
  Record t : Set := {
    grid : RawGrid.t;
    log : Log.t;
  }.

  Definition init (grid : RawGrid.t) : t := {|
    grid := grid;
    log := Log.empty;
  |}.
End ReplayState.

(** Replay one event.  Region and namespace markers are ignored; [Copy]
    constrains rather than assigns, so it leaves the grid unchanged (the
    permutation obligation stays in the event list).  A write that would
    change an already-written cell to a different value returns [None];
    rewriting the same value is accepted. *)
Definition apply_event (state : ReplayState.t) (event : Raw.Event.t)
    : option ReplayState.t :=
  let grid := state.(ReplayState.grid) in
  let log := state.(ReplayState.log) in
  match event with
  | Raw.Event.EnterRegion _
  | Raw.Event.ExitRegion _
  | Raw.Event.PushNamespace _
  | Raw.Event.PopNamespace _
  | Raw.Event.Copy _ _ =>
      Some state
  | Raw.Event.EnableSelector column row _ =>
      if List.existsb (write_conflicts_write column row 1)
           log.(Log.selectors)
      then None
      else
        Some {|
          ReplayState.grid := RawGrid.set_selector grid column row;
          ReplayState.log :=
            Log.add_selector log
              {| Write.column := column; Write.row := row; Write.value := 1 |};
        |}
  | Raw.Event.AssignFixed column row _ value =>
      if orb
           (List.existsb (write_conflicts_write column row value)
             log.(Log.fixeds))
           (List.existsb (write_conflicts_fill column row value)
             log.(Log.fills))
      then None
      else
        Some {|
          ReplayState.grid := RawGrid.set_fixed grid column row value;
          ReplayState.log :=
            Log.add_fixed log
              {| Write.column := column; Write.row := row; Write.value := value |};
        |}
  | Raw.Event.FillFromRow column from_row to_row value =>
      if orb
           (List.existsb (fill_conflicts_write column from_row to_row value)
             log.(Log.fixeds))
           (List.existsb (fill_conflicts_fill column from_row to_row value)
             log.(Log.fills))
      then None
      else
        Some {|
          ReplayState.grid := RawGrid.fill_fixed grid column from_row to_row value;
          ReplayState.log :=
            Log.add_fill log
              {|
                Fill.column := column;
                Fill.from_row := from_row;
                Fill.to_row := to_row;
                Fill.value := value;
              |};
        |}
  end.

Fixpoint apply_events_log (events : list Raw.Event.t) (state : ReplayState.t)
    : option ReplayState.t :=
  match events with
  | [] => Some state
  | event :: events =>
      match apply_event state event with
      | None => None
      | Some state => apply_events_log events state
      end
  end.

Definition apply_events (events : list Raw.Event.t) (grid : RawGrid.t)
    : option RawGrid.t :=
  match apply_events_log events (ReplayState.init grid) with
  | None => None
  | Some state => Some state.(ReplayState.grid)
  end.

(** Success of the replay as a boolean, decided by [vm_compute] on concrete
    events: the conflict checks read only the log, never the grid planes, so
    the verdict is independent of the (possibly symbolic) witness planes. *)
Definition replay_is_ok (events : list Raw.Event.t) (grid : RawGrid.t)
    : bool :=
  match apply_events events grid with
  | Some _ => true
  | None => false
  end.

Lemma replay_is_ok_some (events : list Raw.Event.t) (grid : RawGrid.t) :
  replay_is_ok events grid = true ->
  exists grid', apply_events events grid = Some grid'.
Proof.
  unfold replay_is_ok.
  destruct (apply_events events grid) as [grid' |]; [eauto | discriminate].
Qed.

(** The first event whose replay fails, if any — the write the conflict check
    rejected.  Diagnostic companion of a [None] from [apply_events]. *)
Fixpoint first_failing_event (events : list Raw.Event.t)
    (state : ReplayState.t) : option Raw.Event.t :=
  match events with
  | [] => None
  | event :: events =>
      match apply_event state event with
      | None => Some event
      | Some state => first_failing_event events state
      end
  end.

(** ** The realization relation

    [realize idx rs] re-imposes the relational world's typed + region
    addressing on the flat grid: selector/fixed/advice reads go through
    [region_start] resolution, while instance and lookup reads use absolute
    rows, mirroring [Cell.to_raw]'s instance special case and the absolute
    rows of the table-load events.  Lookup reads target the [Fixed] plane at
    the lookup column indexes — the single-plane addressing above. *)
Definition realize {columns : Columns.t} {RegionId : Set}
    (idx : Indices.t columns) (rs : RegionId -> Z) (grid : RawGrid.t)
    : Assignment.t columns RegionId := {|
  Assignment.selector := fun sel region offset =>
    grid.(RawGrid.sel) (idx.(Indices.selector) sel) (rs region + offset);
  Assignment.fixed := fun column region offset =>
    grid.(RawGrid.cell) Raw.ColumnKind.Fixed
      (idx.(Indices.fixed) column) (rs region + offset);
  Assignment.advice := fun column region offset =>
    grid.(RawGrid.cell) Raw.ColumnKind.Advice
      (idx.(Indices.advice) column) (rs region + offset);
  Assignment.instance_ := fun column row =>
    grid.(RawGrid.cell) Raw.ColumnKind.Instance_
      (idx.(Indices.instance_) column) row;
  Assignment.lookup := fun column row =>
    grid.(RawGrid.cell) Raw.ColumnKind.Fixed
      (idx.(Indices.lookup) column) row;
|}.

(** ** Decision procedures on constraint systems *)

(** No [Expression.Instance_] occurs in the expression.  Relational gate
    evaluation reads instance columns at the region-local rotated row while
    the operational check reads the absolute row, so the gate bridge is
    stated only for systems whose gate and lookup expressions never mention
    instance columns. *)
Fixpoint expression_instance_free {columns : Columns.t}
    (expression : Expression.t columns) : bool :=
  match expression with
  | Expression.Constant _ => true
  | Expression.Selector _ => true
  | Expression.Fixed _ _ => true
  | Expression.Advice _ _ => true
  | Expression.Instance_ _ _ => false
  | Expression.Negated expression => expression_instance_free expression
  | Expression.Sum lhs rhs =>
      andb (expression_instance_free lhs) (expression_instance_free rhs)
  | Expression.Product lhs rhs =>
      andb (expression_instance_free lhs) (expression_instance_free rhs)
  | Expression.Scaled expression _ => expression_instance_free expression
  end.

Fixpoint constraint_instance_free {columns : Columns.t}
    (constraint : Constraint.t columns) : bool :=
  match constraint with
  | Constraint.Select _ constraint => constraint_instance_free constraint
  | Constraint.Equal lhs rhs =>
      andb (expression_instance_free lhs) (expression_instance_free rhs)
  | Constraint.Boolean expression => expression_instance_free expression
  | Constraint.Range expression _ => expression_instance_free expression
  | Constraint.Either lhs rhs =>
      andb (constraint_instance_free lhs) (constraint_instance_free rhs)
  | Constraint.EqualZeroToPrecise expression =>
      expression_instance_free expression
  end.

Definition gate_instance_free {columns : Columns.t}
    (gate : Gate.t columns) : bool :=
  List.forallb
    (fun named_constraint => constraint_instance_free (snd named_constraint))
    gate.(Gate.constraints).

Definition lookup_argument_instance_free {columns : Columns.t}
    (lookup : LookupArgument.t columns) : bool :=
  List.forallb
    (fun pair => expression_instance_free (fst pair))
    lookup.(LookupArgument.pairs).

Definition instance_free_b {columns : Columns.t}
    (system : ConstraintSystem.t columns) : bool :=
  andb
    (List.forallb gate_instance_free system.(ConstraintSystem.gates))
    (List.forallb
      lookup_argument_instance_free
      system.(ConstraintSystem.lookups)).

Definition instance_free {columns : Columns.t}
    (system : ConstraintSystem.t columns) : Prop :=
  instance_free_b system = true.

(** No [Constraint.Range _ 0] occurs in the system.  Relationally
    [Range e 0] is [False] ([0 <= e < 0]), but its flattening
    ([range_check_expression e 0], the empty fold) is the satisfiable
    [e = 0]; every other constructor is equivalent to its flattening over a
    prime field. *)
Fixpoint constraint_flattening_ok {columns : Columns.t}
    (constraint : Constraint.t columns) : bool :=
  match constraint with
  | Constraint.Select _ constraint => constraint_flattening_ok constraint
  | Constraint.Equal _ _ => true
  | Constraint.Boolean _ => true
  | Constraint.Range _ range => negb (range =? 0)%nat
  | Constraint.Either lhs rhs =>
      andb (constraint_flattening_ok lhs) (constraint_flattening_ok rhs)
  | Constraint.EqualZeroToPrecise _ => true
  end.

Definition gate_flattening_ok {columns : Columns.t}
    (gate : Gate.t columns) : bool :=
  List.forallb
    (fun named_constraint => constraint_flattening_ok (snd named_constraint))
    gate.(Gate.constraints).

Definition flattening_ok_b {columns : Columns.t}
    (system : ConstraintSystem.t columns) : bool :=
  List.forallb gate_flattening_ok system.(ConstraintSystem.gates).

Definition flattening_ok {columns : Columns.t}
    (system : ConstraintSystem.t columns) : Prop :=
  flattening_ok_b system = true.
