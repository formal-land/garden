(** * Operational soundness and completeness of the realization bridge.

    [realize/main.v] replays the serialized events of a synthesis program into an
    operational grid; this file connects satisfaction of the indexed,
    flattened constraint system over that grid to the relational
    [circuit_holds] of [proof.v].  The pieces are:

    - [realize_eval_cell]: relational cell reads through [realize] equal raw
      grid reads at [Cell.to_raw] — the addressing agreement, including the
      instance special case (no [region_start] on either side).
    - [realize_eval_expression]: relational expression evaluation at
      [(region, row)] equals indexed evaluation (through
      [Configure.map_expression]) at absolute row [region_start region + row],
      for instance-free expressions.
    - [mock_prover_accepts]: the ideal operational checker over the
      serialized circuit — every gate polynomial vanishes and every lookup
      argument is satisfied at every absolute row of the grid, and every
      [Raw.Event.Copy] obligation of the event stream holds.  The permutation
      obligations are read off the events: [Copy] changes no grid value, so
      the grid alone does not determine them.
    - [operational_sound]: replay success turns ideal operational acceptance
      into the relational package — the computed value agrees, the
      program-determined facts hold outright, and acceptance gives
      [circuit_holds].  The constants-column events materialized by the real
      floor planner after synthesis enter as an explicit trailing input
      ([constants_events]), with [constants_materialized] naming the
      correspondence they must provide for the program's
      [Fact.CellIsConstant] obligations; a program with no
      [ConstrainConstant] discharges it vacuously on the empty tail
      ([operational_sound_no_tail]).
    - [operational_complete]: the converse — [circuit_holds] over the
      realized assignment implies the ideal checker accepts the serialized
      stream — under the same system hypotheses plus an inhabitant of
      [RegionId] (the relational quantification reaches an absolute row only
      through some region). *)

Require Import Garden.Field.Field.
Require Import Garden.Halo2.main.
Require Import Garden.Halo2.Synthesis.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.serialize.
Require Import Garden.Halo2.realize.main.
Require Import Garden.Halo2.realize.value.
Require Import Garden.Halo2.realize.constraints.
Require Import Garden.Halo2.realize.facts.
Require Import Stdlib.micromega.Lia.

Import ListNotations.
Global Open Scope Z_scope.

(** Reading one raw cell out of the grid: the plane named by the column
    kind, at the raw column index and absolute row. *)
Definition raw_cell_read (grid : RawGrid.t) (cell : Raw.Cell.t) : Z :=
  grid.(RawGrid.cell)
    cell.(Raw.Cell.column).(Raw.ColumnRef.kind)
    cell.(Raw.Cell.column).(Raw.ColumnRef.index)
    cell.(Raw.Cell.row).

(** The grid read as an assignment over the indexed columns, with absolute
    rows: the single region is [tt] and [region_start] resolution has already
    happened.  Lookup reads target the [Fixed] plane at the lookup column
    indexes — the single-plane addressing of [RawGrid.t]. *)
Definition grid_assignment (grid : RawGrid.t)
    : Assignment.t Configure.indexed_columns unit :=
  Assignment.Build_t Configure.indexed_columns unit
    (fun (selector : Z) (_ : unit) (row : Z) =>
      grid.(RawGrid.sel) selector row)
    (fun (column : Z) (_ : unit) (row : Z) =>
      grid.(RawGrid.cell) Raw.ColumnKind.Fixed column row)
    (fun (column : Z) (_ : unit) (row : Z) =>
      grid.(RawGrid.cell) Raw.ColumnKind.Advice column row)
    (fun (column row : Z) =>
      grid.(RawGrid.cell) Raw.ColumnKind.Instance_ column row)
    (fun (column row : Z) =>
      grid.(RawGrid.cell) Raw.ColumnKind.Fixed column row).

Section OperationalBridge.
  Context {columns : Columns.t}.
  Context {RegionId : Set}.
  Context {p : Z}.
  Context `{Prime p}.

  (** ** The realization equations *)

  (** Relational cell reads through [realize] are raw grid reads at
      [Cell.to_raw].  The [Instance_] branch drops [region_start] on both
      sides. *)
  Lemma realize_eval_cell
      (idx : Indices.t columns) (rs : RegionId -> Z) (grid : RawGrid.t)
      (cell : Garden.Halo2.Synthesis.Cell.t columns RegionId) :
    eval_cell (realize idx rs grid) cell =
    raw_cell_read grid (Cell.to_raw idx rs cell).
  Proof.
    destruct cell as [[column | column | column] region offset]; reflexivity.
  Qed.

  (** [BinOp.sub] is addition of the normalized opposite: the bridge between
      the [Sum _ (Negated _)] evaluation shortcut and the compositional
      reading. *)
  Lemma sub_as_add_opp (x y : Z) :
    BinOp.sub x y = BinOp.add x (UnOp.opp y).
  Proof.
    unfold BinOp.sub, BinOp.add, UnOp.opp.
    rewrite Z.add_mod_idemp_r by (pose proof (prime_range (p := p)); lia).
    f_equal.
  Qed.

  (** [eval_expression] on a sum is the field sum of the summands, whatever
      the shape of the right summand — the [Sum _ (Negated _)] arm computes
      the same value through [BinOp.sub]. *)
  Lemma eval_expression_sum {columns0 : Columns.t} {RegionId0 : Set}
      (assignment : Assignment.t columns0 RegionId0)
      (index : RegionId0 * Z)
      (lhs rhs : Expression.t columns0) :
    eval_expression assignment index (Expression.Sum lhs rhs) =
    BinOp.add
      (eval_expression assignment index lhs)
      (eval_expression assignment index rhs).
  Proof.
    destruct index as [region row].
    destruct rhs; try reflexivity.
    apply sub_as_add_opp.
  Qed.

  (** Relational expression evaluation at [(region, row)] equals indexed
      evaluation at the absolute row [region_start region + row], for
      expressions free of [Expression.Instance_].  Relational instance reads
      are region-local while operational ones are absolute, so the instance
      case is excluded by [expression_instance_free]. *)
  Lemma realize_eval_expression
      (idx : Indices.t columns) (rs : RegionId -> Z) (grid : RawGrid.t)
      (region : RegionId) (row : Z)
      (e : Expression.t columns) :
    expression_instance_free e = true ->
    eval_expression (realize idx rs grid) (region, row) e =
    eval_expression (grid_assignment grid) (tt, rs region + row)
      (Configure.map_expression (Configure.indices_to_column_map idx) e).
  Proof.
    induction e as
      [ value | selector | column rotation | column rotation
      | column rotation | e IH | lhs IHlhs rhs IHrhs
      | lhs IHlhs rhs IHrhs | e IH scale ];
      intros Hfree; cbn [Configure.map_expression].
    - (* Constant *)
      reflexivity.
    - (* Selector *)
      reflexivity.
    - (* Fixed *)
      cbn.
      unfold rotated_row.
      rewrite Z.add_assoc.
      reflexivity.
    - (* Advice *)
      cbn.
      unfold rotated_row.
      rewrite Z.add_assoc.
      reflexivity.
    - (* Instance_ *)
      discriminate Hfree.
    - (* Negated *)
      cbn [expression_instance_free] in Hfree.
      cbn [eval_expression].
      rewrite (IH Hfree).
      reflexivity.
    - (* Sum *)
      cbn [expression_instance_free] in Hfree.
      apply andb_prop in Hfree.
      destruct Hfree as [Hfree_lhs Hfree_rhs].
      rewrite !eval_expression_sum.
      rewrite (IHlhs Hfree_lhs), (IHrhs Hfree_rhs).
      reflexivity.
    - (* Product *)
      cbn [expression_instance_free] in Hfree.
      apply andb_prop in Hfree.
      destruct Hfree as [Hfree_lhs Hfree_rhs].
      cbn [eval_expression].
      rewrite (IHlhs Hfree_lhs), (IHrhs Hfree_rhs).
      reflexivity.
    - (* Scaled *)
      cbn [expression_instance_free] in Hfree.
      cbn [eval_expression].
      rewrite (IH Hfree).
      reflexivity.
  Qed.

  (** ** The ideal operational checker *)

  (** Acceptance of the serialized circuit: every gate of the indexed,
      flattened system holds at every absolute row of the grid, every lookup
      argument is satisfied at every absolute row against table rows below
      [table_rows], and every [Raw.Event.Copy] of the event stream relates
      cells holding equal values.  The events are an input because [Copy]
      leaves the grid unchanged — the permutation obligations live only in
      the event list. *)
  Definition mock_prover_accepts
      (system : ConstraintSystem.t Configure.indexed_columns)
      (events : list Raw.Event.t)
      (grid : RawGrid.t)
      (table_rows : Z)
      : Prop :=
    (forall row : Z,
      eval_gates (grid_assignment grid) (tt, row)
        system.(ConstraintSystem.gates)) /\
    (forall row : Z,
      List.Forall
        (eval_lookup_argument (grid_assignment grid) (tt, row) table_rows)
        system.(ConstraintSystem.lookups)) /\
    (forall left right : Raw.Cell.t,
      List.In (Raw.Event.Copy left right) events ->
      raw_cell_read grid left = raw_cell_read grid right).

  (** ** List readings of the gate conjunctions *)

  Lemma eval_constraints_forall {columns0 : Columns.t} {RegionId0 : Set}
      (assignment : Assignment.t columns0 RegionId0)
      (index : RegionId0 * Z)
      (constraints : Constraints.t columns0) :
    eval_constraints assignment index constraints <->
    (forall constraint,
      List.In constraint constraints ->
      eval_named_constraint assignment index constraint).
  Proof.
    induction constraints as [| constraint constraints IH].
    - split; [intros _ c [] | intros _; exact I].
    - destruct constraints as [| constraint' constraints'].
      + split.
        * intros Hc c [Heq | []].
          subst c.
          exact Hc.
        * intros Hall.
          apply (Hall constraint (or_introl eq_refl)).
      + change (eval_constraints assignment index
            (constraint :: constraint' :: constraints'))
          with (eval_named_constraint assignment index constraint /\
            eval_constraints assignment index (constraint' :: constraints')).
        rewrite IH.
        split.
        * intros [Hc Hrest] c [Heq | Hin]; [subst c; exact Hc |].
          exact (Hrest c Hin).
        * intros Hall.
          split; [apply (Hall constraint (or_introl eq_refl)) |].
          intros c Hin.
          apply Hall.
          right.
          exact Hin.
  Qed.

  Lemma eval_gates_forall {columns0 : Columns.t} {RegionId0 : Set}
      (assignment : Assignment.t columns0 RegionId0)
      (index : RegionId0 * Z)
      (gates : list (Gate.t columns0)) :
    eval_gates assignment index gates <->
    (forall gate, List.In gate gates -> eval_gate assignment index gate).
  Proof.
    induction gates as [| gate gates IH].
    - split; [intros _ g [] | intros _; exact I].
    - destruct gates as [| gate' gates'].
      + split.
        * intros Hg g [Heq | []].
          subst g.
          exact Hg.
        * intros Hall.
          apply (Hall gate (or_introl eq_refl)).
      + change (eval_gates assignment index (gate :: gate' :: gates'))
          with (eval_gate assignment index gate /\
            eval_gates assignment index (gate' :: gates')).
        rewrite IH.
        split.
        * intros [Hg Hrest] g [Heq | Hin]; [subst g; exact Hg |].
          exact (Hrest g Hin).
        * intros Hall.
          split; [apply (Hall gate (or_introl eq_refl)) |].
          intros g Hin.
          apply Hall.
          right.
          exact Hin.
  Qed.

  (** ** Instance-freeness of the flattened gate polynomial *)

  Lemma range_check_expression_instance_free {columns0 : Columns.t}
      (word : Expression.t columns0) (range : nat) :
    expression_instance_free word = true ->
    expression_instance_free
      (Configure.range_check_expression word range) = true.
  Proof.
    intros Hword.
    unfold Configure.range_check_expression.
    generalize (List.seq 1 (Nat.pred range)) as l.
    intros l.
    enough (Hgen : forall seed : Expression.t columns0,
      expression_instance_free seed = true ->
      expression_instance_free
        (List.fold_left
          (fun acc i =>
            Expression.Product
              acc
              (Expression.Sum
                (Expression.Constant (Z.of_nat i))
                (Expression.Negated word)))
          l seed) = true).
    { exact (Hgen word Hword). }
    induction l as [| i l IH]; intros seed Hseed; cbn [List.fold_left].
    - exact Hseed.
    - apply IH.
      cbn [expression_instance_free].
      rewrite Hseed, Hword.
      reflexivity.
  Qed.

  Lemma constraint_to_expression_instance_free {columns0 : Columns.t}
      (c : Constraint.t columns0) :
    constraint_instance_free c = true ->
    expression_instance_free (Configure.constraint_to_expression c) = true.
  Proof.
    induction c as [selector c' IH | lhs rhs | e | e range | cl IHl cr IHr | e];
      intros Hc;
      cbn [constraint_instance_free] in Hc;
      cbn [Configure.constraint_to_expression].
    - (* Select *)
      cbn [expression_instance_free].
      exact (IH Hc).
    - (* Equal *)
      exact Hc.
    - (* Boolean *)
      apply range_check_expression_instance_free.
      exact Hc.
    - (* Range *)
      apply range_check_expression_instance_free.
      exact Hc.
    - (* Either *)
      apply andb_prop in Hc.
      destruct Hc as [Hcl Hcr].
      cbn [expression_instance_free].
      rewrite (IHl Hcl), (IHr Hcr).
      reflexivity.
    - (* EqualZeroToPrecise *)
      exact Hc.
  Qed.

  (** ** Membership readings of the system-level decision procedures *)

  Lemma system_gate_constraint_instance_free
      (system : ConstraintSystem.t columns)
      (gate : Gate.t columns)
      (name : option string) (c : Constraint.t columns) :
    instance_free system ->
    List.In gate system.(ConstraintSystem.gates) ->
    List.In (name, c) gate.(Gate.constraints) ->
    constraint_instance_free c = true.
  Proof.
    intros Hfree Hgate Hc.
    unfold instance_free, instance_free_b in Hfree.
    apply andb_prop in Hfree.
    destruct Hfree as [Hgates _].
    rewrite List.forallb_forall in Hgates.
    specialize (Hgates gate Hgate).
    unfold gate_instance_free in Hgates.
    rewrite List.forallb_forall in Hgates.
    exact (Hgates (name, c) Hc).
  Qed.

  Lemma system_gate_constraint_flattening_ok
      (system : ConstraintSystem.t columns)
      (gate : Gate.t columns)
      (name : option string) (c : Constraint.t columns) :
    flattening_ok system ->
    List.In gate system.(ConstraintSystem.gates) ->
    List.In (name, c) gate.(Gate.constraints) ->
    constraint_flattening_ok c = true.
  Proof.
    intros Hok Hgate Hc.
    unfold flattening_ok, flattening_ok_b in Hok.
    rewrite List.forallb_forall in Hok.
    specialize (Hok gate Hgate).
    unfold gate_flattening_ok in Hok.
    rewrite List.forallb_forall in Hok.
    exact (Hok (name, c) Hc).
  Qed.

  Lemma system_lookup_expression_instance_free
      (system : ConstraintSystem.t columns)
      (arg : LookupArgument.t columns)
      (e : Expression.t columns) (column : columns.(Columns.Lookup)) :
    instance_free system ->
    List.In arg system.(ConstraintSystem.lookups) ->
    List.In (e, column) arg.(LookupArgument.pairs) ->
    expression_instance_free e = true.
  Proof.
    intros Hfree Harg Hpair.
    unfold instance_free, instance_free_b in Hfree.
    apply andb_prop in Hfree.
    destruct Hfree as [_ Hlookups].
    rewrite List.forallb_forall in Hlookups.
    specialize (Hlookups arg Harg).
    unfold lookup_argument_instance_free in Hlookups.
    rewrite List.forallb_forall in Hlookups.
    exact (Hlookups (e, column) Hpair).
  Qed.

  (** ** Gate and lookup transfer, in both directions *)

  (** Ideal gate acceptance of the indexed, flattened system gives relational
      gate satisfaction: at [(region, row)], the flattened polynomial
      vanishing at absolute row [region_start region + row] transfers through
      [realize_eval_expression] and [constraint_to_expression_correct]. *)
  Lemma mock_gates_to_relational
      (idx : Indices.t columns) (rs : RegionId -> Z) (grid : RawGrid.t)
      (system : ConstraintSystem.t columns) :
    instance_free system ->
    flattening_ok system ->
    (forall row : Z,
      eval_gates (grid_assignment grid) (tt, row)
        (Configure.to_indexed idx system).(ConstraintSystem.gates)) ->
    satisfies_gates (realize idx rs grid) system.
  Proof.
    intros Hinstance_free Hflattening_ok Hmock region row.
    rewrite eval_gates_forall.
    intros gate Hgate.
    unfold eval_gate.
    rewrite eval_constraints_forall.
    intros [name c] Hc.
    cbn [eval_named_constraint].
    apply (proj2 (constraint_to_expression_correct _ (region, row) c
      (system_gate_constraint_flattening_ok system gate name c
        Hflattening_ok Hgate Hc))).
    rewrite (realize_eval_expression idx rs grid region row _
      (constraint_to_expression_instance_free c
        (system_gate_constraint_instance_free system gate name c
          Hinstance_free Hgate Hc))).
    specialize (Hmock (rs region + row)).
    rewrite eval_gates_forall in Hmock.
    specialize (Hmock
      (Configure.map_gate (Configure.indices_to_column_map idx) gate)).
    cbn [Configure.to_indexed Configure.map_constraint_system
      ConstraintSystem.gates] in Hmock.
    specialize (Hmock (List.in_map _ _ _ Hgate)).
    unfold eval_gate in Hmock.
    rewrite eval_constraints_forall in Hmock.
    cbn [Configure.map_gate Gate.constraints] in Hmock.
    unfold Configure.map_constraints in Hmock.
    specialize (Hmock _ (List.in_map _ _ _ Hc)).
    cbn [eval_named_constraint] in Hmock.
    unfold Configure.map_constraint_to_equal_zero_to_precise in Hmock.
    exact Hmock.
  Qed.

  (** The converse: relational gate satisfaction makes every flattened gate
      polynomial vanish at every absolute row.  The absolute row [row] is
      reached relationally as [(region0, row - region_start region0)], which
      is why the statement needs an inhabitant of [RegionId]. *)
  Lemma relational_gates_to_mock
      (idx : Indices.t columns) (rs : RegionId -> Z) (grid : RawGrid.t)
      (system : ConstraintSystem.t columns)
      (region0 : RegionId) :
    instance_free system ->
    flattening_ok system ->
    satisfies_gates (realize idx rs grid) system ->
    forall row : Z,
      eval_gates (grid_assignment grid) (tt, row)
        (Configure.to_indexed idx system).(ConstraintSystem.gates).
  Proof.
    intros Hinstance_free Hflattening_ok Hsat row.
    rewrite eval_gates_forall.
    intros gate' Hgate'.
    cbn [Configure.to_indexed Configure.map_constraint_system
      ConstraintSystem.gates] in Hgate'.
    apply List.in_map_iff in Hgate'.
    destruct Hgate' as (gate & Hgate_eq & Hgate).
    subst gate'.
    unfold eval_gate.
    cbn [Configure.map_gate Gate.constraints].
    rewrite eval_constraints_forall.
    unfold Configure.map_constraints.
    intros constraint' Hconstraint'.
    apply List.in_map_iff in Hconstraint'.
    destruct Hconstraint' as ([name c] & Hconstraint_eq & Hc).
    subst constraint'.
    cbn [eval_named_constraint].
    unfold Configure.map_constraint_to_equal_zero_to_precise.
    cbn [eval_constraint].
    replace row with (rs region0 + (row - rs region0)) by lia.
    rewrite <- (realize_eval_expression idx rs grid region0 (row - rs region0) _
      (constraint_to_expression_instance_free c
        (system_gate_constraint_instance_free system gate name c
          Hinstance_free Hgate Hc))).
    apply (proj1 (constraint_to_expression_correct _ (region0, row - rs region0) c
      (system_gate_constraint_flattening_ok system gate name c
        Hflattening_ok Hgate Hc))).
    specialize (Hsat region0 (row - rs region0)).
    rewrite eval_gates_forall in Hsat.
    specialize (Hsat gate Hgate).
    unfold eval_gate in Hsat.
    rewrite eval_constraints_forall in Hsat.
    exact (Hsat (name, c) Hc).
  Qed.

  (** Ideal lookup acceptance gives relational lookup satisfaction; the
      table-row bound is the same [table_rows] on both sides, and the table
      reads coincide because [realize]'s lookup plane is the grid's [Fixed]
      plane at the lookup column indexes. *)
  Lemma mock_lookups_to_relational
      (idx : Indices.t columns) (rs : RegionId -> Z) (grid : RawGrid.t)
      (system : ConstraintSystem.t columns)
      (table_rows : Z) :
    instance_free system ->
    (forall row : Z,
      List.Forall
        (eval_lookup_argument (grid_assignment grid) (tt, row) table_rows)
        (Configure.to_indexed idx system).(ConstraintSystem.lookups)) ->
    satisfies_lookups (realize idx rs grid) table_rows system.
  Proof.
    intros Hinstance_free Hmock region row.
    apply List.Forall_forall.
    intros arg Harg.
    specialize (Hmock (rs region + row)).
    cbn [Configure.to_indexed Configure.map_constraint_system
      ConstraintSystem.lookups] in Hmock.
    rewrite List.Forall_forall in Hmock.
    specialize (Hmock _ (List.in_map
      (Configure.map_lookup_argument (Configure.indices_to_column_map idx))
      _ _ Harg)).
    unfold eval_lookup_argument in Hmock |- *.
    destruct Hmock as (table_row & Hbound & Hpairs).
    exists table_row.
    split; [exact Hbound |].
    apply List.Forall_forall.
    intros [e column] Hpair.
    cbn [Configure.map_lookup_argument LookupArgument.pairs] in Hpairs.
    rewrite List.Forall_forall in Hpairs.
    specialize (Hpairs _ (List.in_map _ _ _ Hpair)).
    cbv beta iota in Hpairs.
    rewrite (realize_eval_expression idx rs grid region row e
      (system_lookup_expression_instance_free system arg e column
        Hinstance_free Harg Hpair)).
    exact Hpairs.
  Qed.

  (** The converse lookup transfer, again through an inhabitant of
      [RegionId]. *)
  Lemma relational_lookups_to_mock
      (idx : Indices.t columns) (rs : RegionId -> Z) (grid : RawGrid.t)
      (system : ConstraintSystem.t columns)
      (table_rows : Z)
      (region0 : RegionId) :
    instance_free system ->
    satisfies_lookups (realize idx rs grid) table_rows system ->
    forall row : Z,
      List.Forall
        (eval_lookup_argument (grid_assignment grid) (tt, row) table_rows)
        (Configure.to_indexed idx system).(ConstraintSystem.lookups).
  Proof.
    intros Hinstance_free Hsat row.
    cbn [Configure.to_indexed Configure.map_constraint_system
      ConstraintSystem.lookups].
    apply List.Forall_forall.
    intros arg' Harg'.
    apply List.in_map_iff in Harg'.
    destruct Harg' as (arg & Harg_eq & Harg).
    subst arg'.
    specialize (Hsat region0 (row - rs region0)).
    rewrite List.Forall_forall in Hsat.
    specialize (Hsat arg Harg).
    unfold eval_lookup_argument in Hsat |- *.
    destruct Hsat as (table_row & Hbound & Hpairs).
    exists table_row.
    split; [exact Hbound |].
    cbn [Configure.map_lookup_argument LookupArgument.pairs].
    apply List.Forall_forall.
    intros pair' Hpair'.
    apply List.in_map_iff in Hpair'.
    destruct Hpair' as ([e column] & Hpair_eq & Hpair).
    subst pair'.
    cbv beta iota.
    rewrite List.Forall_forall in Hpairs.
    specialize (Hpairs (e, column) Hpair).
    cbv beta iota in Hpairs.
    replace row with (rs region0 + (row - rs region0)) by lia.
    rewrite <- (realize_eval_expression idx rs grid region0 (row - rs region0) e
      (system_lookup_expression_instance_free system arg e column
        Hinstance_free Harg Hpair)).
    exact Hpairs.
  Qed.

  (** ** Facts and events: the permutation correspondence *)

  (** A [Fact.CellsEqual] of a region program appears in its event stream as
      the [Raw.Event.Copy] of the two lowered cells. *)
  Lemma region_cells_equal_event
      (idx : Indices.t columns) (rs : RegionId -> Z) (region : RegionId)
      {A : Set} (program : 𝓡 columns RegionId A)
      (left_cell right_cell : Garden.Halo2.Synthesis.Cell.t columns RegionId) :
    List.In (Fact.CellsEqual left_cell right_cell)
      (region_facts region program) ->
    List.In
      (Raw.Event.Copy
        (Cell.to_raw idx rs left_cell)
        (Cell.to_raw idx rs right_cell))
      (snd (V1.eval_region idx rs region program)).
  Proof.
    induction program as
      [A value | A B first IHfirst second IHsecond
      | selector offset annotation | annotation column offset value
      | lhs rhs | cell value];
      cbn [region_facts V1.eval_region].
    - intros [].
    - rewrite (region_value_agrees idx rs region first).
      destruct (V1.eval_region idx rs region first)
        as [value_first events_first] eqn:Hfirst.
      cbn [fst].
      destruct (V1.eval_region idx rs region (second value_first))
        as [value_second events_second] eqn:Hsecond.
      cbn [snd].
      intros Hin.
      apply List.in_app_or in Hin.
      apply List.in_or_app.
      destruct Hin as [Hin | Hin].
      + left.
        exact (IHfirst Hin).
      + right.
        specialize (IHsecond value_first Hin).
        rewrite Hsecond in IHsecond.
        exact IHsecond.
    - intros [Heq | []].
      discriminate Heq.
    - intros [Heq | []].
      discriminate Heq.
    - intros [Heq | []].
      injection Heq as -> ->.
      left.
      reflexivity.
    - intros [Heq | []].
      discriminate Heq.
  Qed.

  (** Region programs establish no [Fact.InstanceIs]: instance constraints
      are layouter-level operations. *)
  Lemma region_facts_no_instance_is
      (region : RegionId)
      {A : Set} (program : 𝓡 columns RegionId A)
      (cell : Garden.Halo2.Synthesis.Cell.t columns RegionId)
      (instance : columns.(Columns.Instance_)) (row : Z) :
    ~ List.In (Fact.InstanceIs cell instance row)
        (region_facts region program).
  Proof.
    induction program as
      [A value | A B first IHfirst second IHsecond
      | selector offset annotation | annotation column offset value
      | lhs rhs | cell' value];
      cbn [region_facts].
    - intros [].
    - intros Hin.
      apply List.in_app_or in Hin.
      destruct Hin as [Hin | Hin].
      + exact (IHfirst Hin).
      + exact (IHsecond (region_value first) Hin).
    - intros [Heq | []].
      discriminate Heq.
    - intros [Heq | []].
      discriminate Heq.
    - intros [Heq | []].
      discriminate Heq.
    - intros [Heq | []].
      discriminate Heq.
  Qed.

  (** A [Fact.CellsEqual] of a layouter program appears in its event stream
      as a [Raw.Event.Copy]. *)
  Lemma layouter_cells_equal_event
      (idx : Indices.t columns) (rs : RegionId -> Z) (usable_rows : Z)
      {A : Set} (program : 𝓛 columns RegionId A)
      (left_cell right_cell : Garden.Halo2.Synthesis.Cell.t columns RegionId) :
    List.In (Fact.CellsEqual left_cell right_cell) (layouter_facts program) ->
    List.In
      (Raw.Event.Copy
        (Cell.to_raw idx rs left_cell)
        (Cell.to_raw idx rs right_cell))
      (snd (V1.eval_layouter idx rs usable_rows program)).
  Proof.
    induction program as
      [A value | A B first IHfirst second IHsecond
      | A region name region_program | cell instance row
      | name entries | A name nested IHnested];
      cbn [layouter_facts V1.eval_layouter].
    - intros [].
    - rewrite (layouter_value_agrees idx rs usable_rows first).
      destruct (V1.eval_layouter idx rs usable_rows first)
        as [value_first events_first] eqn:Hfirst.
      cbn [fst].
      destruct (V1.eval_layouter idx rs usable_rows (second value_first))
        as [value_second events_second] eqn:Hsecond.
      cbn [snd].
      intros Hin.
      apply List.in_app_or in Hin.
      apply List.in_or_app.
      destruct Hin as [Hin | Hin].
      + left.
        exact (IHfirst Hin).
      + right.
        specialize (IHsecond value_first Hin).
        rewrite Hsecond in IHsecond.
        exact IHsecond.
    - intros Hin.
      destruct (V1.eval_region idx rs region (region_program region))
        as [value events] eqn:Hregion.
      cbn [snd].
      apply List.in_cons.
      apply List.in_or_app.
      left.
      pose proof (region_cells_equal_event idx rs region
        (region_program region) left_cell right_cell Hin) as Hevent.
      rewrite Hregion in Hevent.
      exact Hevent.
    - intros [Heq | []].
      discriminate Heq.
    - intros Hin.
      apply List.in_map_iff in Hin.
      destruct Hin as (entry & Heq & _).
      discriminate Heq.
    - destruct (V1.eval_layouter idx rs usable_rows nested)
        as [value events] eqn:Hnested.
      cbn [snd].
      intros Hin.
      apply List.in_cons.
      apply List.in_or_app.
      left.
      exact (IHnested Hin).
  Qed.

  (** A [Fact.InstanceIs] of a layouter program appears in its event stream
      as the [Raw.Event.Copy] against the raw instance cell. *)
  Lemma layouter_instance_is_event
      (idx : Indices.t columns) (rs : RegionId -> Z) (usable_rows : Z)
      {A : Set} (program : 𝓛 columns RegionId A)
      (cell : Garden.Halo2.Synthesis.Cell.t columns RegionId)
      (instance : columns.(Columns.Instance_)) (row : Z) :
    List.In (Fact.InstanceIs cell instance row) (layouter_facts program) ->
    List.In
      (Raw.Event.Copy
        (Cell.to_raw idx rs cell)
        (Cell.instance_raw idx instance row))
      (snd (V1.eval_layouter idx rs usable_rows program)).
  Proof.
    induction program as
      [A value | A B first IHfirst second IHsecond
      | A region name region_program | cell' instance' row'
      | name entries | A name nested IHnested];
      cbn [layouter_facts V1.eval_layouter].
    - intros [].
    - rewrite (layouter_value_agrees idx rs usable_rows first).
      destruct (V1.eval_layouter idx rs usable_rows first)
        as [value_first events_first] eqn:Hfirst.
      cbn [fst].
      destruct (V1.eval_layouter idx rs usable_rows (second value_first))
        as [value_second events_second] eqn:Hsecond.
      cbn [snd].
      intros Hin.
      apply List.in_app_or in Hin.
      apply List.in_or_app.
      destruct Hin as [Hin | Hin].
      + left.
        exact (IHfirst Hin).
      + right.
        specialize (IHsecond value_first Hin).
        rewrite Hsecond in IHsecond.
        exact IHsecond.
    - intros Hin.
      exfalso.
      exact (region_facts_no_instance_is region (region_program region)
        cell instance row Hin).
    - intros [Heq | []].
      injection Heq as -> -> ->.
      left.
      reflexivity.
    - intros Hin.
      apply List.in_map_iff in Hin.
      destruct Hin as (entry & Heq & _).
      discriminate Heq.
    - destruct (V1.eval_layouter idx rs usable_rows nested)
        as [value events] eqn:Hnested.
      cbn [snd].
      intros Hin.
      apply List.in_cons.
      apply List.in_or_app.
      left.
      exact (IHnested Hin).
  Qed.

  (** The table-load stream contains no [Raw.Event.Copy]: it consists of
      region markers, fixed assignments and fills. *)
  Lemma assign_lookup_entry_at_row_no_copy
      (idx : Indices.t columns) (row : nat)
      (entry : LookupTableColumn.t columns)
      (left right : Raw.Cell.t) :
    ~ List.In (Raw.Event.Copy left right)
        (V1.assign_lookup_entry_at_row idx row entry).
  Proof.
    unfold V1.assign_lookup_entry_at_row.
    destruct (V1.value_at_row row (LookupTableColumn.values entry))
      as [value |].
    - intros [Heq | []].
      discriminate Heq.
    - intros [].
  Qed.

  Lemma assign_lookup_row_no_copy
      (idx : Indices.t columns) (row : nat)
      (entries : list (LookupTableColumn.t columns))
      (left right : Raw.Cell.t) :
    ~ List.In (Raw.Event.Copy left right)
        (V1.assign_lookup_row idx row entries).
  Proof.
    induction entries as [| entry entries IH]; cbn [V1.assign_lookup_row].
    - intros [].
    - intros Hin.
      apply List.in_app_or in Hin.
      destruct Hin as [Hin | Hin].
      + exact (assign_lookup_entry_at_row_no_copy idx row entry
          left right Hin).
      + exact (IH Hin).
  Qed.

  Lemma assign_lookup_rows_no_copy
      (idx : Indices.t columns) (rows_remaining row : nat)
      (entries : list (LookupTableColumn.t columns))
      (left right : Raw.Cell.t) :
    ~ List.In (Raw.Event.Copy left right)
        (V1.assign_lookup_rows idx rows_remaining row entries).
  Proof.
    revert row.
    induction rows_remaining as [| rows_remaining IH]; intros row;
      cbn [V1.assign_lookup_rows].
    - intros [].
    - intros Hin.
      apply List.in_app_or in Hin.
      destruct Hin as [Hin | Hin].
      + exact (assign_lookup_row_no_copy idx row entries left right Hin).
      + exact (IH (S row) Hin).
  Qed.

  Lemma fill_lookup_entries_no_copy
      (idx : Indices.t columns) (usable_rows : Z)
      (entries : list (LookupTableColumn.t columns))
      (left right : Raw.Cell.t) :
    ~ List.In (Raw.Event.Copy left right)
        (V1.fill_lookup_entries idx usable_rows entries).
  Proof.
    induction entries as [| entry entries IH]; cbn [V1.fill_lookup_entries].
    - intros [].
    - intros [Heq | Hin].
      + discriminate Heq.
      + exact (IH Hin).
  Qed.

  Lemma init_lookup_table_events_no_copy
      (idx : Indices.t columns) (usable_rows : Z) (name : string)
      (entries : list (LookupTableColumn.t columns))
      (left right : Raw.Cell.t) :
    ~ List.In (Raw.Event.Copy left right)
        (V1.init_lookup_table_events idx usable_rows name entries).
  Proof.
    unfold V1.init_lookup_table_events.
    intros Hin.
    cbn [List.app] in Hin.
    destruct Hin as [Heq | Hin]; [discriminate Heq |].
    apply List.in_app_or in Hin.
    destruct Hin as [Hin | Hin].
    - exact (assign_lookup_rows_no_copy idx _ _ entries left right Hin).
    - destruct Hin as [Heq | Hin]; [discriminate Heq |].
      exact (fill_lookup_entries_no_copy idx usable_rows entries left right Hin).
  Qed.

  (** Every [Raw.Event.Copy] of a region stream is the lowering of a
      [Fact.CellsEqual] of the program. *)
  Lemma region_copy_event_fact
      (idx : Indices.t columns) (rs : RegionId -> Z) (region : RegionId)
      {A : Set} (program : 𝓡 columns RegionId A)
      (left right : Raw.Cell.t) :
    List.In (Raw.Event.Copy left right)
      (snd (V1.eval_region idx rs region program)) ->
    exists left_cell right_cell,
      left = Cell.to_raw idx rs left_cell /\
      right = Cell.to_raw idx rs right_cell /\
      List.In (Fact.CellsEqual left_cell right_cell)
        (region_facts region program).
  Proof.
    induction program as
      [A value | A B first IHfirst second IHsecond
      | selector offset annotation | annotation column offset value
      | lhs rhs | cell value];
      cbn [region_facts V1.eval_region].
    - intros [].
    - rewrite (region_value_agrees idx rs region first).
      destruct (V1.eval_region idx rs region first)
        as [value_first events_first] eqn:Hfirst.
      cbn [fst].
      destruct (V1.eval_region idx rs region (second value_first))
        as [value_second events_second] eqn:Hsecond.
      cbn [snd].
      intros Hin.
      apply List.in_app_or in Hin.
      destruct Hin as [Hin | Hin].
      + destruct (IHfirst Hin) as
          (left_cell & right_cell & Hleft & Hright & Hfact).
        exists left_cell, right_cell.
        split; [exact Hleft |].
        split; [exact Hright |].
        apply List.in_or_app.
        left.
        exact Hfact.
      + specialize (IHsecond value_first).
        rewrite Hsecond in IHsecond.
        destruct (IHsecond Hin) as
          (left_cell & right_cell & Hleft & Hright & Hfact).
        exists left_cell, right_cell.
        split; [exact Hleft |].
        split; [exact Hright |].
        apply List.in_or_app.
        right.
        exact Hfact.
    - intros [Heq | []].
      discriminate Heq.
    - intros [Heq | []].
      discriminate Heq.
    - intros [Heq | []].
      injection Heq as <- <-.
      exists lhs, rhs.
      split; [reflexivity |].
      split; [reflexivity |].
      left.
      reflexivity.
    - intros [].
  Qed.

  (** Every [Raw.Event.Copy] of a layouter stream is the lowering of a
      [Fact.CellsEqual] or of a [Fact.InstanceIs]. *)
  Lemma layouter_copy_event_fact
      (idx : Indices.t columns) (rs : RegionId -> Z) (usable_rows : Z)
      {A : Set} (program : 𝓛 columns RegionId A)
      (left right : Raw.Cell.t) :
    List.In (Raw.Event.Copy left right)
      (snd (V1.eval_layouter idx rs usable_rows program)) ->
    (exists left_cell right_cell,
      left = Cell.to_raw idx rs left_cell /\
      right = Cell.to_raw idx rs right_cell /\
      List.In (Fact.CellsEqual left_cell right_cell)
        (layouter_facts program)) \/
    (exists cell instance row,
      left = Cell.to_raw idx rs cell /\
      right = Cell.instance_raw idx instance row /\
      List.In (Fact.InstanceIs cell instance row) (layouter_facts program)).
  Proof.
    induction program as
      [A value | A B first IHfirst second IHsecond
      | A region name region_program | cell instance row
      | name entries | A name nested IHnested];
      cbn [layouter_facts V1.eval_layouter].
    - intros [].
    - rewrite (layouter_value_agrees idx rs usable_rows first).
      destruct (V1.eval_layouter idx rs usable_rows first)
        as [value_first events_first] eqn:Hfirst.
      cbn [fst].
      destruct (V1.eval_layouter idx rs usable_rows (second value_first))
        as [value_second events_second] eqn:Hsecond.
      cbn [snd].
      intros Hin.
      apply List.in_app_or in Hin.
      destruct Hin as [Hin | Hin].
      + destruct (IHfirst Hin) as
          [ (left_cell & right_cell & Hleft & Hright & Hfact)
          | (cell & instance & row & Hleft & Hright & Hfact) ].
        * left.
          exists left_cell, right_cell.
          split; [exact Hleft |].
          split; [exact Hright |].
          apply List.in_or_app.
          left.
          exact Hfact.
        * right.
          exists cell, instance, row.
          split; [exact Hleft |].
          split; [exact Hright |].
          apply List.in_or_app.
          left.
          exact Hfact.
      + specialize (IHsecond value_first).
        rewrite Hsecond in IHsecond.
        destruct (IHsecond Hin) as
          [ (left_cell & right_cell & Hleft & Hright & Hfact)
          | (cell & instance & row & Hleft & Hright & Hfact) ].
        * left.
          exists left_cell, right_cell.
          split; [exact Hleft |].
          split; [exact Hright |].
          apply List.in_or_app.
          right.
          exact Hfact.
        * right.
          exists cell, instance, row.
          split; [exact Hleft |].
          split; [exact Hright |].
          apply List.in_or_app.
          right.
          exact Hfact.
    - destruct (V1.eval_region idx rs region (region_program region))
        as [value events] eqn:Hregion.
      cbn [snd List.app].
      intros Hin.
      destruct Hin as [Heq | Hin]; [discriminate Heq |].
      apply List.in_app_or in Hin.
      destruct Hin as [Hin | [Heq | []]]; [| discriminate Heq].
      left.
      pose proof (region_copy_event_fact idx rs region
        (region_program region) left right) as Hfact.
      rewrite Hregion in Hfact.
      exact (Hfact Hin).
    - intros [Heq | []].
      injection Heq as <- <-.
      right.
      exists cell, instance, row.
      split; [reflexivity |].
      split; [reflexivity |].
      left.
      reflexivity.
    - intros Hin.
      exfalso.
      exact (init_lookup_table_events_no_copy idx usable_rows name entries
        left right Hin).
    - destruct (V1.eval_layouter idx rs usable_rows nested)
        as [value events] eqn:Hnested.
      cbn [snd List.app].
      intros Hin.
      destruct Hin as [Heq | Hin]; [discriminate Heq |].
      apply List.in_app_or in Hin.
      destruct Hin as [Hin | [Heq | []]]; [| discriminate Heq].
      exact (IHnested Hin).
  Qed.

  (** ** The constants seam

      [𝓡.ConstrainConstant] contributes no event to [V1.eval_layouter]'s
      stream: the real V1 floor planner materializes queued constants only
      after synthesis, as a trailing block of constants-column
      [Raw.Event.AssignFixed] + [Raw.Event.Copy] events with allocator-chosen
      rows.  [constants_materialized] names what that block must provide for
      each [Fact.CellIsConstant] obligation of the program: a [Copy] linking
      the constrained cell to some fixed-column cell, and the [AssignFixed]
      pinning that fixed cell to the constant.  A program with no
      [ConstrainConstant] satisfies it vacuously. *)
  Definition constants_materialized
      (idx : Indices.t columns) (rs : RegionId -> Z)
      (facts : list (Fact.t columns RegionId))
      (events : list Raw.Event.t)
      : Prop :=
    forall (cell : Garden.Halo2.Synthesis.Cell.t columns RegionId) (value : Z),
      List.In (Fact.CellIsConstant cell value) facts ->
      exists (column row : Z) (annotation : string),
        (List.In
          (Raw.Event.Copy
            (Cell.to_raw idx rs cell)
            {|
              Raw.Cell.column := {|
                Raw.ColumnRef.kind := Raw.ColumnKind.Fixed;
                Raw.ColumnRef.index := column;
              |};
              Raw.Cell.row := row;
            |})
          events \/
         List.In
          (Raw.Event.Copy
            {|
              Raw.Cell.column := {|
                Raw.ColumnRef.kind := Raw.ColumnKind.Fixed;
                Raw.ColumnRef.index := column;
              |};
              Raw.Cell.row := row;
            |}
            (Cell.to_raw idx rs cell))
          events) /\
        List.In (Raw.Event.AssignFixed column row annotation value) events.

  (** ** Assembling the fact list *)

  (** The program-determined facts hold after any successful replay of a
      stream extending the program's events. *)
  Lemma determined_facts_hold_incl
      (idx : Indices.t columns) (rs : RegionId -> Z) (usable_rows : Z)
      {A : Set} (program : 𝓛 columns RegionId A)
      (events_all : list Raw.Event.t)
      (initial final : RawGrid.t) :
    apply_events events_all initial = Some final ->
    List.incl (snd (V1.eval_layouter idx rs usable_rows program)) events_all ->
    interpret_facts (realize idx rs final)
      (determined_facts (layouter_facts program)).
  Proof.
    intros Hreplay Hincl.
    eapply (layouter_determined_facts final events_all).
    - intros column row annotation Hin.
      exact (replay_selector_pinned _ _ _ _ _ _ Hreplay Hin).
    - intros column row annotation value Hin.
      exact (replay_fixed_pinned _ _ _ _ _ _ _ Hreplay Hin).
    - exact Hincl.
  Qed.

  (** The full fact list of a synthesis program holds in the realized
      assignment, given: the program's events inside the checked stream, the
      constants correspondence, the program-determined facts, the copy
      obligations of the stream, and the pinning of fixed writes.  The last
      two are exactly what [mock_prover_accepts] and replay success provide. *)
  Lemma circuit_facts_hold
      (idx : Indices.t columns) (rs : RegionId -> Z) (usable_rows : Z)
      {A : Set} (program : 𝓛 columns RegionId A)
      (grid : RawGrid.t)
      (events_all : list Raw.Event.t) :
    List.incl (snd (V1.eval_layouter idx rs usable_rows program)) events_all ->
    constants_materialized idx rs (layouter_facts program) events_all ->
    interpret_facts (realize idx rs grid)
      (determined_facts (layouter_facts program)) ->
    (forall left right : Raw.Cell.t,
      List.In (Raw.Event.Copy left right) events_all ->
      raw_cell_read grid left = raw_cell_read grid right) ->
    (forall (column row : Z) (annotation : string) (value : Z),
      List.In (Raw.Event.AssignFixed column row annotation value) events_all ->
      grid.(RawGrid.cell) Raw.ColumnKind.Fixed column row = value) ->
    interpret_facts (realize idx rs grid) (layouter_facts program).
  Proof.
    intros Hincl Hconstants Hdetermined Hcopy Hfixed.
    apply interpret_facts_of_in.
    intros fact Hin.
    destruct fact as
      [selector region offset | column region offset value
      | left_cell right_cell | cell instance row
      | column values default_value | cell value].
    - (* SelectorOn: program-determined *)
      apply (interpret_facts_In _ _ _ Hdetermined).
      apply List.filter_In.
      split; [exact Hin | reflexivity].
    - (* FixedIs: program-determined *)
      apply (interpret_facts_In _ _ _ Hdetermined).
      apply List.filter_In.
      split; [exact Hin | reflexivity].
    - (* CellsEqual: a copy obligation of the stream *)
      cbn [interpret_fact].
      rewrite !realize_eval_cell.
      apply Hcopy.
      apply Hincl.
      exact (layouter_cells_equal_event idx rs usable_rows program
        left_cell right_cell Hin).
    - (* InstanceIs: a copy obligation against the raw instance cell *)
      cbn [interpret_fact].
      rewrite realize_eval_cell.
      rewrite (Hcopy _ _ (Hincl _
        (layouter_instance_is_event idx rs usable_rows program cell instance row
          Hin))).
      reflexivity.
    - (* LookupTableLoaded: program-determined *)
      apply (interpret_facts_In _ _ _ Hdetermined).
      apply List.filter_In.
      split; [exact Hin | reflexivity].
    - (* CellIsConstant: the materialized constants block *)
      cbn [interpret_fact].
      rewrite realize_eval_cell.
      destruct (Hconstants cell value Hin) as
        (column & row & annotation & Hcopy_in & Hassign_in).
      pose proof (Hfixed column row annotation value Hassign_in) as Hpinned.
      destruct Hcopy_in as [Hcopy_in | Hcopy_in].
      + rewrite (Hcopy _ _ Hcopy_in).
        exact Hpinned.
      + rewrite <- (Hcopy _ _ Hcopy_in).
        exact Hpinned.
  Qed.

  (** ** The bridge theorems *)

  (** Operational soundness.  Under the named system hypotheses, a
      successful replay of the serialized events (with the floor planner's
      trailing constants block as an explicit extra input) yields: the value
      agreement, the program-determined facts outright, and — given ideal
      operational acceptance of the same stream — the full relational
      package [circuit_holds]. *)
  Theorem operational_sound
      {A : Set} (program : 𝓛 columns RegionId A)
      (idx : Indices.t columns) (rs : RegionId -> Z) (usable_rows : Z)
      (system : ConstraintSystem.t columns)
      (advice instance_ : Z -> Z -> Z) (g : RawGrid.t)
      (constants_events : list Raw.Event.t) :
    instance_free system ->
    flattening_ok system ->
    let '(v_op, evts) := V1.eval_layouter idx rs usable_rows program in
    constants_materialized idx rs (layouter_facts program)
      (evts ++ constants_events) ->
    apply_events (evts ++ constants_events) (initial_grid advice instance_) =
      Some g ->
    let Γ := realize idx rs g in
    layouter_value program = v_op /\
    interpret_facts Γ (determined_facts (layouter_facts program)) /\
    (mock_prover_accepts (Configure.to_indexed idx system)
        (evts ++ constants_events) g (layouter_table_rows program) ->
      circuit_holds Γ program system).
  Proof.
    intros Hinstance_free Hflattening_ok.
    destruct (V1.eval_layouter idx rs usable_rows program) as [v_op evts] eqn:Heval.
    intros Hconstants Hreplay.
    cbv zeta.
    assert (Hevents : snd (V1.eval_layouter idx rs usable_rows program) = evts)
      by (rewrite Heval; reflexivity).
    assert (Hincl :
      List.incl (snd (V1.eval_layouter idx rs usable_rows program))
        (evts ++ constants_events)).
    { rewrite Hevents.
      apply List.incl_appl, List.incl_refl. }
    assert (Hdetermined :
      interpret_facts (realize idx rs g)
        (determined_facts (layouter_facts program))).
    { exact (determined_facts_hold_incl idx rs usable_rows program
        (evts ++ constants_events) (initial_grid advice instance_) g
        Hreplay Hincl). }
    split; [| split].
    - (* 1. results agree *)
      rewrite (operational_sound_value idx rs usable_rows program), Heval.
      reflexivity.
    - (* 2. program-determined facts hold outright *)
      exact Hdetermined.
    - (* 3. ideal acceptance gives the relational package *)
      intros Hmock.
      destruct Hmock as (Hgates & Hlookups & Hcopies).
      split.
      + apply (circuit_facts_hold idx rs usable_rows program g
          (evts ++ constants_events)).
        * exact Hincl.
        * exact Hconstants.
        * exact Hdetermined.
        * exact Hcopies.
        * intros column row annotation value Hin.
          exact (replay_fixed_pinned _ _ _ _ _ _ _ Hreplay Hin).
      + split.
        * exact (mock_gates_to_relational idx rs g system
            Hinstance_free Hflattening_ok Hgates).
        * exact (mock_lookups_to_relational idx rs g system
            (layouter_table_rows program) Hinstance_free Hlookups).
  Qed.

  (** The same statement over the bare serialized stream (an empty constants
      tail): the form chip-level programs use, whose [ConstrainConstant]-free
      synthesis makes [constants_materialized] vacuous. *)
  Corollary operational_sound_no_tail
      {A : Set} (program : 𝓛 columns RegionId A)
      (idx : Indices.t columns) (rs : RegionId -> Z) (usable_rows : Z)
      (system : ConstraintSystem.t columns)
      (advice instance_ : Z -> Z -> Z) (g : RawGrid.t) :
    instance_free system ->
    flattening_ok system ->
    let '(v_op, evts) := V1.eval_layouter idx rs usable_rows program in
    constants_materialized idx rs (layouter_facts program) evts ->
    apply_events evts (initial_grid advice instance_) = Some g ->
    let Γ := realize idx rs g in
    layouter_value program = v_op /\
    interpret_facts Γ (determined_facts (layouter_facts program)) /\
    (mock_prover_accepts (Configure.to_indexed idx system)
        evts g (layouter_table_rows program) ->
      circuit_holds Γ program system).
  Proof.
    intros Hinstance_free Hflattening_ok.
    pose proof (operational_sound program idx rs usable_rows system advice
      instance_ g [] Hinstance_free Hflattening_ok) as Hsound.
    destruct (V1.eval_layouter idx rs usable_rows program) as [v_op evts].
    rewrite List.app_nil_r in Hsound.
    exact Hsound.
  Qed.

  (** Operational completeness.  Under the same system hypotheses plus an
      inhabitant of [RegionId], the relational package implies ideal
      operational acceptance of the serialized stream: gates and lookups
      transfer row-by-row through the realization equations, and every
      [Raw.Event.Copy] obligation is the lowering of a [Fact.CellsEqual] or
      [Fact.InstanceIs] the fact list interprets. *)
  Theorem operational_complete
      {A : Set} (program : 𝓛 columns RegionId A)
      (idx : Indices.t columns) (rs : RegionId -> Z) (usable_rows : Z)
      (system : ConstraintSystem.t columns)
      (advice instance_ : Z -> Z -> Z) (g : RawGrid.t)
      (region0 : RegionId) :
    instance_free system ->
    flattening_ok system ->
    let '(v_op, evts) := V1.eval_layouter idx rs usable_rows program in
    apply_events evts (initial_grid advice instance_) = Some g ->
    circuit_holds (realize idx rs g) program system ->
    mock_prover_accepts (Configure.to_indexed idx system) evts g
      (layouter_table_rows program).
  Proof.
    intros Hinstance_free Hflattening_ok.
    destruct (V1.eval_layouter idx rs usable_rows program) as [v_op evts] eqn:Heval.
    intros _ Hholds.
    destruct Hholds as (Hfacts & Hgates & Hlookups).
    split; [| split].
    - exact (relational_gates_to_mock idx rs g system region0
        Hinstance_free Hflattening_ok Hgates).
    - exact (relational_lookups_to_mock idx rs g system
        (layouter_table_rows program) region0 Hinstance_free Hlookups).
    - intros left right Hin.
      assert (Hin' :
        List.In (Raw.Event.Copy left right)
          (snd (V1.eval_layouter idx rs usable_rows program)))
        by (rewrite Heval; exact Hin).
      destruct (layouter_copy_event_fact idx rs usable_rows program left right
        Hin') as
        [ (left_cell & right_cell & Hleft & Hright & Hfact)
        | (cell & instance & row & Hleft & Hright & Hfact) ].
      + subst left right.
        rewrite <- !realize_eval_cell.
        exact (interpret_facts_In _ _ _ Hfacts Hfact).
      + subst left right.
        rewrite <- realize_eval_cell.
        exact (interpret_facts_In _ _ _ Hfacts Hfact).
  Qed.
End OperationalBridge.
