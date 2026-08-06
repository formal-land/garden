(** * The finite-domain reading of the ideal checker.

    [mock_prover_accepts] ([realize/sound.v]) quantifies its gate and lookup
    conjuncts over every integer row: the operational grid is unbounded, and
    off the written area the selector planes are identically [0], so the
    quantification costs nothing.  The compiled plonkish system of
    [plonkish/main.v] instead lives on the cyclic domain [[0, 2^k)] with a
    reserved blinding tail.  This file connects the two readings:
    [plonkish_accepts] restricts the same three conjuncts to the domain rows,
    and [plonkish_of_mock_prover] proves the two checkers equivalent for a
    replayed grid, under the computable finite-domain side conditions
    bundled in [finite_domain_ok_b]:

    - [selector_rows_within_b]: every [EnableSelector] event lands inside
      the usable-row prefix — the region extents of the placement fit below
      the [l_last] and blinding rows (the selector footprint is the part of
      the extents the equivalence consumes: off the enabled rows both
      checkers are vacuous, whatever the advice and fixed planes hold);
    - [gates_selector_vacuous_b]: every gate constraint partially evaluates
      to a satisfied form once every selector is [0] (via the partial
      evaluator [Complete.zero_selector_value]), so gate satisfaction is
      free off the enabled rows — the flattened [Select]-guarded constraints
      of [Configure.to_indexed] have this shape;
    - [lookup_defaults_of_events_b]: each lookup argument's padding tuple —
      its input expressions at all-zero selectors — is pinned to table
      row [0] by the table-load events, so row [0] witnesses the argument
      off the enabled rows;
    - [gate_rotations_within_b] and [tables_prefix_b]: every gate rotation
      from an enabled row stays inside the domain, and each table column's
      [FillFromRow] padding covers the usable rows from the table prefix on
      — the row-boundary facts the compiled-system transfer consumes
      ([replay_gate_rotation_in_domain]: plain rotation agrees with the
      cyclic [Domain.rot] at every active row; [replay_table_padding]: the
      padding value is constant across the usable rows above the table
      prefix, the [l_last] and blinding rows left at their initial value).

    The gate and lookup conjuncts are stated against the indexed,
    selector-carrying system of [serialize.v] — the same system
    [mock_prover_accepts] checks.  The substitution of the compressed
    selector columns into the gates is the separate
    compilation-correctness statement, which composes with this
    equivalence at the [[0, n)] satisfaction interface
    ([plonkish_accepts]). *)

Require Import Garden.Field.Field.
Require Import Garden.Plonky3.M.
Require Import Garden.Halo2.main.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.serialize.
Require Import Garden.Halo2.complete.
Require Import Garden.Halo2.realize.main.
Require Import Garden.Halo2.realize.facts.
Require Import Garden.Halo2.realize.sound.
Require Import Garden.Halo2.plonkish.main.
Require Import Stdlib.micromega.Lia.

Import ListNotations.
Global Open Scope Z_scope.

Module PlonkishMock.

Import Plonkish.

(** ** Event checks

    Boolean scans over the serialized event stream: decidable on a concrete
    stream by [vm_compute], independent of the (possibly symbolic) witness
    planes. *)

(** Some [EnableSelector] event targets the cell [(column, row)]. *)
Definition enable_selector_at_b (events : list Raw.Event.t)
    (column row : Z) : bool :=
  List.existsb
    (fun event =>
      match event with
      | Raw.Event.EnableSelector selector' row' _ =>
          andb (selector' =? column) (row' =? row)
      | _ => false
      end)
    events.

(** Every [EnableSelector] event lands inside [[0, bound)]. *)
Definition selector_rows_within_b (bound : Z) (events : list Raw.Event.t)
    : bool :=
  List.forallb
    (fun event =>
      match event with
      | Raw.Event.EnableSelector _ row _ => andb (0 <=? row) (row <? bound)
      | _ => true
      end)
    events.

(** Some fixed-plane event pins the cell [(column, 0)] to [value]: a point
    write at row [0] or a fill whose extent covers row [0]. *)
Definition table_default_pinned_b (events : list Raw.Event.t)
    (column value : Z) : bool :=
  List.existsb
    (fun event =>
      match event with
      | Raw.Event.AssignFixed column' row _ value' =>
          andb (andb (column' =? column) (row =? 0)) (value' =? value)
      | Raw.Event.FillFromRow column' from_row to_row value' =>
          andb
            (andb (andb (column' =? column) (from_row <=? 0)) (0 <? to_row))
            (value' =? value)
      | _ => false
      end)
    events.

(** Every table column of every lookup argument is padded by a
    [FillFromRow] whose extent starts at or before [table_rows] and reaches
    [usable_rows] — the table occupies a row prefix and one constant value
    covers the usable rows above it, the [l_last] and blinding rows left at
    their initial value. *)
Definition tables_prefix_b (events : list Raw.Event.t)
    (system : ConstraintSystem.t Configure.indexed_columns)
    (table_rows usable_rows : Z) : bool :=
  List.forallb
    (fun arg : LookupArgument.t Configure.indexed_columns =>
      List.forallb
        (fun pair =>
          List.existsb
            (fun event =>
              match event with
              | Raw.Event.FillFromRow column' from_row to_row _ =>
                  andb (andb (column' =? snd pair) (from_row <=? table_rows))
                    (usable_rows <=? to_row)
              | _ => false
              end)
            events)
        arg.(LookupArgument.pairs))
    system.(ConstraintSystem.lookups).

(** ** Syntactic collections over the indexed system *)

(** The rotation offsets read by an expression. *)
Fixpoint expression_offsets {columns : Columns.t}
    (expression : Expression.t columns) : list Z :=
  match expression with
  | Expression.Constant _ | Expression.Selector _ => []
  | Expression.Fixed _ rotation
  | Expression.Advice _ rotation
  | Expression.Instance_ _ rotation => [rotation.(Rotation.offset)]
  | Expression.Negated expression => expression_offsets expression
  | Expression.Sum lhs rhs | Expression.Product lhs rhs =>
      expression_offsets lhs ++ expression_offsets rhs
  | Expression.Scaled expression _ => expression_offsets expression
  end.

Fixpoint constraint_offsets {columns : Columns.t}
    (constraint : Constraint.t columns) : list Z :=
  match constraint with
  | Constraint.Select _ constraint => constraint_offsets constraint
  | Constraint.Equal lhs rhs =>
      expression_offsets lhs ++ expression_offsets rhs
  | Constraint.Boolean expression => expression_offsets expression
  | Constraint.Range expression _ => expression_offsets expression
  | Constraint.Either lhs rhs =>
      constraint_offsets lhs ++ constraint_offsets rhs
  | Constraint.EitherZeroToPrecise lhs rhs =>
      expression_offsets lhs ++ expression_offsets rhs
  | Constraint.EqualZeroToPrecise expression => expression_offsets expression
  end.

Definition gate_offsets {columns : Columns.t} (gate : Gate.t columns)
    : list Z :=
  List.flat_map
    (fun named_constraint => constraint_offsets (snd named_constraint))
    gate.(Gate.constraints).

(** The selector indexes occurring in an indexed expression. *)
Fixpoint expression_selectors
    (expression : Expression.t Configure.indexed_columns) : list Z :=
  match expression with
  | Expression.Constant _ | Expression.Fixed _ _
  | Expression.Advice _ _ | Expression.Instance_ _ _ => []
  | Expression.Selector selector => [selector]
  | Expression.Negated expression => expression_selectors expression
  | Expression.Sum lhs rhs | Expression.Product lhs rhs =>
      expression_selectors lhs ++ expression_selectors rhs
  | Expression.Scaled expression _ => expression_selectors expression
  end.

Fixpoint constraint_selectors
    (constraint : Constraint.t Configure.indexed_columns) : list Z :=
  match constraint with
  | Constraint.Select selector constraint =>
      selector :: constraint_selectors constraint
  | Constraint.Equal lhs rhs =>
      expression_selectors lhs ++ expression_selectors rhs
  | Constraint.Boolean expression => expression_selectors expression
  | Constraint.Range expression _ => expression_selectors expression
  | Constraint.Either lhs rhs =>
      constraint_selectors lhs ++ constraint_selectors rhs
  | Constraint.EitherZeroToPrecise lhs rhs =>
      expression_selectors lhs ++ expression_selectors rhs
  | Constraint.EqualZeroToPrecise expression =>
      expression_selectors expression
  end.

Definition gate_selectors (gate : Gate.t Configure.indexed_columns)
    : list Z :=
  List.flat_map
    (fun named_constraint => constraint_selectors (snd named_constraint))
    gate.(Gate.constraints).

(** For every gate: from every row where one of the gate's selectors is
    enabled, every rotation of the gate stays inside [[0, n)] — no gate
    read crosses the domain boundary at an active row. *)
Definition gate_rotations_within_b (n : Z) (events : list Raw.Event.t)
    (system : ConstraintSystem.t Configure.indexed_columns) : bool :=
  List.forallb
    (fun gate =>
      let selectors := gate_selectors gate in
      let offsets := gate_offsets gate in
      List.forallb
        (fun event =>
          match event with
          | Raw.Event.EnableSelector selector row _ =>
              if List.existsb (Z.eqb selector) selectors then
                List.forallb
                  (fun offset =>
                    andb (0 <=? row + offset) (row + offset <? n))
                  offsets
              else true
          | _ => true
          end)
        events)
    system.(ConstraintSystem.gates).

(** ** The replayed selector plane off the enabled points

    [replay_selector_pinned] ([realize/facts.v]) pins the enabled points to
    [1]; these lemmas are the other direction — a cell no [EnableSelector]
    event targets keeps its initial value, so on [initial_grid] the plane is
    [0] everywhere off the events' footprint. *)

Lemma apply_event_selector_untouched
    (state state' : ReplayState.t) (event : Raw.Event.t) (column row : Z) :
  apply_event state event = Some state' ->
  match event with
  | Raw.Event.EnableSelector selector' row' _ =>
      andb (selector' =? column) (row' =? row)
  | _ => false
  end = false ->
  state'.(ReplayState.grid).(RawGrid.sel) column row =
    state.(ReplayState.grid).(RawGrid.sel) column row.
Proof.
  destruct event as
    [ name | name | name | name | selector' row' annotation
    | column' row' annotation value | left_cell right_cell
    | column' from_row to_row value ];
    cbn;
    try (intros Happly _; injection Happly as <-; reflexivity).
  - (* EnableSelector *)
    destruct (List.existsb (write_conflicts_write selector' row' 1)
        state.(ReplayState.log).(Log.selectors));
      intros Happly Hoff; [discriminate |].
    injection Happly as <-.
    cbn.
    rewrite (Z.eqb_sym column selector'), (Z.eqb_sym row row').
    rewrite Hoff.
    reflexivity.
  - (* AssignFixed *)
    destruct (List.existsb (write_conflicts_write column' row' value)
        state.(ReplayState.log).(Log.fixeds));
      intros Happly _; [discriminate |].
    revert Happly.
    destruct (List.existsb (write_conflicts_fill column' row' value)
        state.(ReplayState.log).(Log.fills));
      intros Happly; [discriminate |].
    injection Happly as <-.
    reflexivity.
  - (* FillFromRow *)
    destruct (List.existsb (fill_conflicts_write column' from_row to_row value)
        state.(ReplayState.log).(Log.fixeds));
      intros Happly _; [discriminate |].
    revert Happly.
    destruct (List.existsb (fill_conflicts_fill column' from_row to_row value)
        state.(ReplayState.log).(Log.fills));
      intros Happly; [discriminate |].
    injection Happly as <-.
    reflexivity.
Qed.

Lemma apply_events_log_selector_off (events : list Raw.Event.t)
    (state state' : ReplayState.t) (column row : Z) :
  apply_events_log events state = Some state' ->
  enable_selector_at_b events column row = false ->
  state'.(ReplayState.grid).(RawGrid.sel) column row =
    state.(ReplayState.grid).(RawGrid.sel) column row.
Proof.
  revert state.
  induction events as [| event events IH]; intros state Happly Hoff;
    cbn in Happly.
  - injection Happly as <-.
    reflexivity.
  - cbn in Hoff.
    apply Bool.orb_false_iff in Hoff.
    destruct Hoff as [Hhead Hrest].
    destruct (apply_event state event) as [state1 |] eqn:Hevent;
      [| discriminate].
    rewrite (IH state1 Happly Hrest).
    exact (apply_event_selector_untouched state state1 event column row
      Hevent Hhead).
Qed.

Lemma replay_selector_off (events : list Raw.Event.t)
    (initial final : RawGrid.t) (column row : Z) :
  apply_events events initial = Some final ->
  enable_selector_at_b events column row = false ->
  final.(RawGrid.sel) column row = initial.(RawGrid.sel) column row.
Proof.
  unfold apply_events.
  destruct (apply_events_log events (ReplayState.init initial))
    as [state |] eqn:Hreplay; [| discriminate].
  intros Hfinal Hoff.
  injection Hfinal as <-.
  exact (apply_events_log_selector_off _ _ _ _ _ Hreplay Hoff).
Qed.

(** The replayed selector plane is [0] at every row outside the checked
    bound, in every column. *)
Lemma replay_selector_zero_outside (events : list Raw.Event.t)
    (advice instance_ : Z -> Z -> Z) (grid : RawGrid.t)
    (bound column row : Z) :
  apply_events events (initial_grid advice instance_) = Some grid ->
  selector_rows_within_b bound events = true ->
  ~ (0 <= row < bound) ->
  grid.(RawGrid.sel) column row = 0.
Proof.
  intros Hreplay Hwithin Hout.
  destruct (enable_selector_at_b events column row) eqn:Henable.
  - exfalso.
    unfold enable_selector_at_b in Henable.
    apply List.existsb_exists in Henable.
    destruct Henable as (event & Hin & Hcheck).
    destruct event as
      [ name | name | name | name | selector' row' annotation
      | column' row' annotation value | left_cell right_cell
      | column' from_row to_row value ];
      try discriminate.
    apply Bool.andb_true_iff in Hcheck.
    destruct Hcheck as [_ Hrow].
    apply Z.eqb_eq in Hrow.
    unfold selector_rows_within_b in Hwithin.
    rewrite List.forallb_forall in Hwithin.
    specialize (Hwithin _ Hin).
    apply Bool.andb_true_iff in Hwithin.
    destruct Hwithin as [Hlow Hhigh].
    apply Z.leb_le in Hlow.
    apply Z.ltb_lt in Hhigh.
    lia.
  - rewrite (replay_selector_off _ _ _ _ _ Hreplay Henable).
    reflexivity.
Qed.

(** ** The replayed fixed plane at the table anchors *)

(** A pinned table default is a fixed-plane value of the replayed grid at
    row [0]. *)
Lemma table_default_pinned_value (events : list Raw.Event.t)
    (initial grid : RawGrid.t) (column value : Z) :
  apply_events events initial = Some grid ->
  table_default_pinned_b events column value = true ->
  grid.(RawGrid.cell) Raw.ColumnKind.Fixed column 0 = value.
Proof.
  intros Hreplay Hpinned.
  unfold table_default_pinned_b in Hpinned.
  apply List.existsb_exists in Hpinned.
  destruct Hpinned as (event & Hin & Hcheck).
  destruct event as
    [ name | name | name | name | selector' row' annotation
    | column' row' annotation value' | left_cell right_cell
    | column' from_row to_row value' ];
    try discriminate.
  - (* AssignFixed *)
    apply Bool.andb_true_iff in Hcheck.
    destruct Hcheck as [Hcheck Hvalue].
    apply Bool.andb_true_iff in Hcheck.
    destruct Hcheck as [Hcolumn Hrow].
    apply Z.eqb_eq in Hcolumn, Hrow, Hvalue.
    subst column' row' value'.
    exact (replay_fixed_pinned _ _ _ _ _ _ _ Hreplay Hin).
  - (* FillFromRow *)
    apply Bool.andb_true_iff in Hcheck.
    destruct Hcheck as [Hcheck Hvalue].
    apply Bool.andb_true_iff in Hcheck.
    destruct Hcheck as [Hcheck Hto].
    apply Bool.andb_true_iff in Hcheck.
    destruct Hcheck as [Hcolumn Hfrom].
    apply Z.eqb_eq in Hcolumn, Hvalue.
    apply Z.leb_le in Hfrom.
    apply Z.ltb_lt in Hto.
    subst column' value'.
    exact (replay_fill_pinned _ _ _ _ _ _ _ _ Hreplay Hin Hfrom Hto).
Qed.

(** Each checked table column holds one constant value on the usable rows
    from [table_rows] on — the padding above the table prefix.  The [l_last]
    and blinding rows at [usable_rows] and beyond are left at their initial
    value, matching keygen's unblinded fixed column. *)
Lemma replay_table_padding (events : list Raw.Event.t)
    (initial grid : RawGrid.t)
    (system : ConstraintSystem.t Configure.indexed_columns)
    (table_rows usable_rows : Z)
    (arg : LookupArgument.t Configure.indexed_columns)
    (expression : Expression.t Configure.indexed_columns)
    (column : Z) :
  apply_events events initial = Some grid ->
  tables_prefix_b events system table_rows usable_rows = true ->
  List.In arg system.(ConstraintSystem.lookups) ->
  List.In (expression, column) arg.(LookupArgument.pairs) ->
  exists default : Z,
    forall row : Z,
      table_rows <= row ->
      row < usable_rows ->
      grid.(RawGrid.cell) Raw.ColumnKind.Fixed column row = default.
Proof.
  intros Hreplay Hprefix Hargs Hpairs.
  unfold tables_prefix_b in Hprefix.
  rewrite List.forallb_forall in Hprefix.
  specialize (Hprefix _ Hargs).
  rewrite List.forallb_forall in Hprefix.
  specialize (Hprefix _ Hpairs).
  cbn [snd] in Hprefix.
  apply List.existsb_exists in Hprefix.
  destruct Hprefix as (event & Hin & Hcheck).
  destruct event as
    [ name | name | name | name | selector' row' annotation
    | column' row' annotation value | left_cell right_cell
    | column' from_row to_row value ];
    try discriminate.
  apply Bool.andb_true_iff in Hcheck.
  destruct Hcheck as [Hcheck Hto].
  apply Bool.andb_true_iff in Hcheck.
  destruct Hcheck as [Hcolumn Hfrom].
  apply Z.eqb_eq in Hcolumn.
  apply Z.leb_le in Hfrom.
  apply Z.leb_le in Hto.
  subst column'.
  exists value.
  intros row Hrow Hrowu.
  apply (replay_fill_pinned _ _ _ _ _ _ _ _ Hreplay Hin); lia.
Qed.

(** ** Rotations from active rows stay inside the domain *)

(** At every row where one of a gate's selectors is actually on in the
    replayed grid, every rotation of the gate reads inside [[0, n)]. *)
Lemma replay_gate_rotation_in_domain (n : Z) (events : list Raw.Event.t)
    (advice instance_ : Z -> Z -> Z) (grid : RawGrid.t)
    (system : ConstraintSystem.t Configure.indexed_columns)
    (gate : Gate.t Configure.indexed_columns)
    (selector row offset : Z) :
  apply_events events (initial_grid advice instance_) = Some grid ->
  gate_rotations_within_b n events system = true ->
  List.In gate system.(ConstraintSystem.gates) ->
  List.In selector (gate_selectors gate) ->
  grid.(RawGrid.sel) selector row <> 0 ->
  List.In offset (gate_offsets gate) ->
  0 <= row + offset < n.
Proof.
  intros Hreplay Hrotations Hgate Hselector Hon Hoffset.
  destruct (enable_selector_at_b events selector row) eqn:Henable.
  2: {
    exfalso.
    apply Hon.
    rewrite (replay_selector_off _ _ _ _ _ Hreplay Henable).
    reflexivity.
  }
  unfold enable_selector_at_b in Henable.
  apply List.existsb_exists in Henable.
  destruct Henable as (event & Hin & Hcheck).
  destruct event as
    [ name | name | name | name | selector' row' annotation
    | column' row' annotation value | left_cell right_cell
    | column' from_row to_row value ];
    try discriminate.
  apply Bool.andb_true_iff in Hcheck.
  destruct Hcheck as [Hsel_eq Hrow_eq].
  apply Z.eqb_eq in Hsel_eq, Hrow_eq.
  subst selector' row'.
  unfold gate_rotations_within_b in Hrotations.
  rewrite List.forallb_forall in Hrotations.
  specialize (Hrotations _ Hgate).
  cbv beta zeta in Hrotations.
  rewrite List.forallb_forall in Hrotations.
  specialize (Hrotations _ Hin).
  cbv beta iota in Hrotations.
  assert (Hmem : List.existsb (Z.eqb selector) (gate_selectors gate) = true).
  { apply List.existsb_exists.
    exists selector.
    split; [exact Hselector | apply Z.eqb_refl]. }
  rewrite Hmem in Hrotations.
  cbv iota in Hrotations.
  rewrite List.forallb_forall in Hrotations.
  specialize (Hrotations _ Hoffset).
  apply Bool.andb_true_iff in Hrotations.
  destruct Hrotations as [Hlow Hhigh].
  apply Z.leb_le in Hlow.
  apply Z.ltb_lt in Hhigh.
  lia.
Qed.

(** Inside the domain the cyclic rotation is the plain one: the reading
    [mock_prover_accepts] uses and the reading of [Domain.rot] agree at
    every read the previous lemma bounds. *)
Lemma domain_rot_plain (domain : Domain.t) (row offset : Z) :
  0 <= row + offset < Domain.n domain ->
  Domain.rot domain row offset = row + offset.
Proof.
  intros Hrange.
  unfold Domain.rot.
  apply Z.mod_small.
  exact Hrange.
Qed.

Section WithPrime.
  Context {p : Z}.
  Context `{Prime p}.

  (** ** Partial evaluation at all-zero selectors

      The generic reading of [Complete.zero_selector_value]: at an index
      where every selector evaluates to [0], a [Some value] partial
      evaluation is the exact expression value, whatever the advice, fixed
      and instance planes hold. *)

  Lemma zero_selector_value_eval {columns0 : Columns.t} {RegionId0 : Set}
      (Γ : Assignment.t columns0 RegionId0)
      (region : RegionId0) (row : Z)
      (Hselectors :
        forall selector, eval_selector Γ (region, row) selector = 0)
      (expression : Expression.t columns0) :
    forall value : Z,
      Complete.zero_selector_value (p := p) expression = Some value ->
      eval_expression Γ (region, row) expression = value.
  Proof.
    induction expression as
      [ constant | selector | fixed rotation | advice rotation
      | instance rotation | expression IH | lhs IHl rhs IHr
      | lhs IHl rhs IHr | expression IH scale ];
      intros value Hvalue; cbn in Hvalue.
    - (* Constant *)
      injection Hvalue as <-.
      reflexivity.
    - (* Selector *)
      injection Hvalue as <-.
      exact (Hselectors selector).
    - (* Fixed *) discriminate.
    - (* Advice *) discriminate.
    - (* Instance_ *) discriminate.
    - (* Negated *)
      destruct (Complete.zero_selector_value expression)
        as [inner |] eqn:Hinner; [| discriminate].
      injection Hvalue as <-.
      cbn [eval_expression].
      rewrite (IH inner eq_refl).
      reflexivity.
    - (* Sum *)
      destruct (Complete.zero_selector_value lhs)
        as [value_l |] eqn:Hl; [| discriminate].
      destruct (Complete.zero_selector_value rhs)
        as [value_r |] eqn:Hr; [| discriminate].
      injection Hvalue as <-.
      rewrite eval_expression_sum.
      rewrite (IHl value_l eq_refl), (IHr value_r eq_refl).
      reflexivity.
    - (* Product *)
      cbn [eval_expression].
      destruct (Complete.zero_selector_value lhs)
        as [value_l |] eqn:Hl;
        destruct (Complete.zero_selector_value rhs)
          as [value_r |] eqn:Hr.
      + injection Hvalue as <-.
        rewrite (IHl value_l eq_refl), (IHr value_r eq_refl).
        reflexivity.
      + destruct (Z.eqb value_l 0) eqn:Hzero; [| discriminate].
        apply Z.eqb_eq in Hzero.
        subst value_l.
        injection Hvalue as <-.
        rewrite (IHl 0 eq_refl).
        apply FieldRewrite.mul_zero_left.
      + destruct (Z.eqb value_r 0) eqn:Hzero; [| discriminate].
        apply Z.eqb_eq in Hzero.
        subst value_r.
        injection Hvalue as <-.
        rewrite (IHr 0 eq_refl).
        apply FieldRewrite.mul_zero_right.
      + discriminate.
    - (* Scaled *)
      destruct (Complete.zero_selector_value expression)
        as [inner |] eqn:Hinner; [| discriminate].
      injection Hvalue as <-.
      cbn [eval_expression].
      rewrite (IH inner eq_refl).
      reflexivity.
  Qed.

  (** ** Selector-vacuous constraints

      A constraint whose satisfaction is free wherever every selector
      evaluates to [0]: a [Select]-guarded constraint (the implication is
      vacuous) or a flattened polynomial whose partial evaluation at
      all-zero selectors is [0] — the shape [Configure.to_indexed] gives
      every [Select]-guarded source constraint. *)

  Definition constraint_selector_vacuous_b {columns0 : Columns.t}
      (constraint : Constraint.t columns0) : bool :=
    match constraint with
    | Constraint.Select _ _ => true
    | Constraint.EqualZeroToPrecise expression =>
        match Complete.zero_selector_value (p := p) expression with
        | Some value => value =? 0
        | None => false
        end
    | _ => false
    end.

  Definition gate_selector_vacuous_b {columns0 : Columns.t}
      (gate : Gate.t columns0) : bool :=
    List.forallb
      (fun named_constraint =>
        constraint_selector_vacuous_b (snd named_constraint))
      gate.(Gate.constraints).

  Definition gates_selector_vacuous_b {columns0 : Columns.t}
      (system : ConstraintSystem.t columns0) : bool :=
    List.forallb gate_selector_vacuous_b system.(ConstraintSystem.gates).

  Lemma constraint_selector_vacuous_sound {columns0 : Columns.t}
      {RegionId0 : Set}
      (Γ : Assignment.t columns0 RegionId0)
      (region : RegionId0) (row : Z)
      (Hselectors :
        forall selector, eval_selector Γ (region, row) selector = 0)
      (constraint : Constraint.t columns0) :
    constraint_selector_vacuous_b constraint = true ->
    eval_constraint Γ (region, row) constraint.
  Proof.
    destruct constraint as
      [ selector inner | lhs rhs | expression | expression range
      | lhs rhs | lhs rhs | expression ];
      intros Hcheck; cbn in Hcheck; try discriminate.
    - (* Select *)
      cbn.
      intros Hnonzero.
      exfalso.
      exact (Hnonzero (Hselectors selector)).
    - (* EqualZeroToPrecise *)
      destruct (Complete.zero_selector_value expression)
        as [value |] eqn:Hvalue; [| discriminate].
      apply Z.eqb_eq in Hcheck.
      subst value.
      exact (zero_selector_value_eval Γ region row Hselectors expression 0
        Hvalue).
  Qed.

  Lemma gates_selector_vacuous_sound {columns0 : Columns.t}
      {RegionId0 : Set}
      (Γ : Assignment.t columns0 RegionId0)
      (region : RegionId0) (row : Z)
      (system : ConstraintSystem.t columns0) :
    gates_selector_vacuous_b system = true ->
    (forall selector, eval_selector Γ (region, row) selector = 0) ->
    eval_gates Γ (region, row) system.(ConstraintSystem.gates).
  Proof.
    intros Hcheck Hselectors.
    apply (proj2 (eval_gates_forall Γ (region, row)
      system.(ConstraintSystem.gates))).
    intros gate Hgate.
    unfold gates_selector_vacuous_b in Hcheck.
    rewrite List.forallb_forall in Hcheck.
    specialize (Hcheck _ Hgate).
    unfold gate_selector_vacuous_b in Hcheck.
    rewrite List.forallb_forall in Hcheck.
    apply (proj2 (eval_constraints_forall Γ (region, row)
      gate.(Gate.constraints))).
    intros named_constraint Hconstraint.
    specialize (Hcheck _ Hconstraint).
    destruct named_constraint as [name constraint].
    exact (constraint_selector_vacuous_sound Γ region row Hselectors
      constraint Hcheck).
  Qed.

  (** ** The replayed grid off the domain: every selector reads [0] *)

  Lemma grid_selectors_zero_outside (events : list Raw.Event.t)
      (advice instance_ : Z -> Z -> Z) (grid : RawGrid.t)
      (bound row : Z) :
    apply_events events (initial_grid advice instance_) = Some grid ->
    selector_rows_within_b bound events = true ->
    ~ (0 <= row < bound) ->
    forall selector : Z,
      eval_selector (grid_assignment grid) (tt, row) selector = 0.
  Proof.
    intros Hreplay Hwithin Hout selector.
    unfold eval_selector.
    cbn.
    rewrite (replay_selector_zero_outside _ _ _ _ _ _ _
      Hreplay Hwithin Hout).
    reflexivity.
  Qed.

  (** ** Lookup arguments off the enabled rows

      With every selector at [0], each input expression collapses to its
      padding constant, and the events pin that constant to table row [0]:
      row [0] witnesses the argument. *)

  Definition lookup_defaults_of_events_b (events : list Raw.Event.t)
      (system : ConstraintSystem.t Configure.indexed_columns)
      (table_rows : Z) : bool :=
    match system.(ConstraintSystem.lookups) with
    | [] => true
    | _ :: _ =>
        andb
          (0 <? table_rows)
          (List.forallb
            (fun arg : LookupArgument.t Configure.indexed_columns =>
              List.forallb
                (fun pair =>
                  match
                    Complete.zero_selector_value (p := p) (fst pair)
                  with
                  | Some value =>
                      table_default_pinned_b events (snd pair) value
                  | None => false
                  end)
                arg.(LookupArgument.pairs))
            system.(ConstraintSystem.lookups))
    end.

  Lemma lookup_argument_defaults_hold (events : list Raw.Event.t)
      (initial grid : RawGrid.t) (table_rows : Z)
      (arg : LookupArgument.t Configure.indexed_columns)
      (Hreplay : apply_events events initial = Some grid)
      (Htable : 0 < table_rows)
      (Hcheck :
        List.forallb
          (fun pair =>
            match Complete.zero_selector_value (p := p) (fst pair) with
            | Some value => table_default_pinned_b events (snd pair) value
            | None => false
            end)
          arg.(LookupArgument.pairs) = true)
      (row : Z)
      (Hselectors :
        forall selector : Z,
          eval_selector (grid_assignment grid) (tt, row) selector = 0) :
    eval_lookup_argument (grid_assignment grid) (tt, row) table_rows arg.
  Proof.
    exists 0.
    split; [lia |].
    apply List.Forall_forall.
    intros [expression column] Hin.
    rewrite List.forallb_forall in Hcheck.
    specialize (Hcheck _ Hin).
    cbn [fst snd] in Hcheck.
    destruct (Complete.zero_selector_value expression)
      as [value |] eqn:Hvalue; [| discriminate].
    rewrite (zero_selector_value_eval (columns0 := Configure.indexed_columns)
      _ _ _ Hselectors _ _ Hvalue).
    cbn.
    symmetry.
    exact (table_default_pinned_value _ _ _ _ _ Hreplay Hcheck).
  Qed.

  Lemma lookups_defaults_all (events : list Raw.Event.t)
      (initial grid : RawGrid.t) (table_rows : Z)
      (system : ConstraintSystem.t Configure.indexed_columns)
      (Hreplay : apply_events events initial = Some grid)
      (Hdefaults :
        lookup_defaults_of_events_b events system table_rows = true)
      (row : Z)
      (Hselectors :
        forall selector : Z,
          eval_selector (grid_assignment grid) (tt, row) selector = 0) :
    List.Forall
      (eval_lookup_argument (grid_assignment grid) (tt, row) table_rows)
      system.(ConstraintSystem.lookups).
  Proof.
    unfold lookup_defaults_of_events_b in Hdefaults.
    destruct (system.(ConstraintSystem.lookups)) as [| arg0 args]
      eqn:Hlookups; [constructor |].
    apply Bool.andb_true_iff in Hdefaults.
    destruct Hdefaults as [Htable Hall].
    apply Z.ltb_lt in Htable.
    apply List.Forall_forall.
    intros arg Hin.
    rewrite List.forallb_forall in Hall.
    exact (lookup_argument_defaults_hold events initial grid table_rows arg
      Hreplay Htable (Hall _ Hin) row Hselectors).
  Qed.

  (** ** The finite-domain side conditions, bundled

      One boolean over the concrete layout — the events, the indexed
      system, the domain and the table size — decidable by [vm_compute].
      The conjuncts are the checks above; the rotation and table-prefix
      conjuncts are not consumed by the equivalence itself (both readings
      below evaluate the same grid with the same plain rotation) but are
      part of the finite-domain contract the compiled-system transfer
      reads through [replay_gate_rotation_in_domain] and
      [replay_table_padding]. *)

  Definition finite_domain_ok_b (domain : Domain.t)
      (system : ConstraintSystem.t Configure.indexed_columns)
      (events : list Raw.Event.t)
      (table_rows : Z) : bool :=
    andb
      (andb
        (andb
          (andb
            (andb
              (0 <=? domain.(Domain.blinding_factors))
              (selector_rows_within_b (Domain.usable_rows domain) events))
            (gates_selector_vacuous_b system))
          (gate_rotations_within_b (Domain.n domain) events system))
        (lookup_defaults_of_events_b events system table_rows))
      (match system.(ConstraintSystem.lookups) with
       | [] => true
       | _ :: _ =>
           andb
             (tables_prefix_b events system table_rows
               (Domain.usable_rows domain))
             (table_rows <=? Domain.usable_rows domain)
       end).

  (** ** Satisfaction restricted to the domain

      The three conjuncts of [mock_prover_accepts] with the gate and lookup
      rows restricted to [[0, n)] — the row set of the compiled plonkish
      system.  The system is the indexed, selector-carrying one: the
      compiled-system transfer substitutes the compressed selector columns
      into the gates at this interface. *)

  Definition plonkish_accepts (domain : Domain.t)
      (system : ConstraintSystem.t Configure.indexed_columns)
      (events : list Raw.Event.t)
      (grid : RawGrid.t)
      (table_rows : Z) : Prop :=
    (forall row : Z,
      0 <= row < Domain.n domain ->
      eval_gates (grid_assignment grid) (tt, row)
        system.(ConstraintSystem.gates)) /\
    (forall row : Z,
      0 <= row < Domain.n domain ->
      List.Forall
        (eval_lookup_argument (grid_assignment grid) (tt, row) table_rows)
        system.(ConstraintSystem.lookups)) /\
    (forall left right : Raw.Cell.t,
      List.In (Raw.Event.Copy left right) events ->
      raw_cell_read grid left = raw_cell_read grid right).

  (** ** The equivalence

      For a replayed grid, acceptance by the all-integer-rows ideal checker
      and satisfaction restricted to the domain rows coincide.  Restriction
      is trivial; extension holds because every row outside the domain lies
      outside the usable-row prefix, where the replayed selector plane is
      identically [0]: the selector-vacuous gates are satisfied outright
      and table row [0] witnesses every lookup argument. *)

  Theorem plonkish_of_mock_prover (domain : Domain.t)
      (system : ConstraintSystem.t Configure.indexed_columns)
      (events : list Raw.Event.t)
      (advice instance_ : Z -> Z -> Z)
      (grid : RawGrid.t)
      (table_rows : Z)
      (Hreplay :
        apply_events events (initial_grid advice instance_) = Some grid)
      (Hok : finite_domain_ok_b domain system events table_rows = true) :
    mock_prover_accepts system events grid table_rows <->
    plonkish_accepts domain system events grid table_rows.
  Proof.
    unfold finite_domain_ok_b in Hok.
    apply Bool.andb_true_iff in Hok.
    destruct Hok as [Hok Htables].
    apply Bool.andb_true_iff in Hok.
    destruct Hok as [Hok Hdefaults].
    apply Bool.andb_true_iff in Hok.
    destruct Hok as [Hok Hrotations].
    apply Bool.andb_true_iff in Hok.
    destruct Hok as [Hok Hguard].
    apply Bool.andb_true_iff in Hok.
    destruct Hok as [Hblinding Hwithin].
    apply Z.leb_le in Hblinding.
    assert (Husable : Domain.usable_rows domain <= Domain.n domain).
    { unfold Domain.usable_rows.
      clear - Hblinding.
      lia. }
    split.
    - (* Restriction *)
      intros (Hgates & Hlookups & Hcopies).
      split; [| split].
      + intros row _.
        exact (Hgates row).
      + intros row _.
        exact (Hlookups row).
      + exact Hcopies.
    - (* Extension *)
      intros (Hgates & Hlookups & Hcopies).
      split; [| split].
      + intros row.
        destruct (andb (0 <=? row) (row <? Domain.n domain)) eqn:Hrow.
        * apply Bool.andb_true_iff in Hrow.
          destruct Hrow as [Hlow Hhigh].
          apply Z.leb_le in Hlow.
          apply Z.ltb_lt in Hhigh.
          exact (Hgates row (conj Hlow Hhigh)).
        * assert (Hout : ~ (0 <= row < Domain.usable_rows domain)).
          { apply Bool.andb_false_iff in Hrow.
            destruct Hrow as [Hrow | Hrow];
              [apply Z.leb_gt in Hrow | apply Z.ltb_ge in Hrow];
              clear - Hrow Husable;
              lia. }
          exact (gates_selector_vacuous_sound (grid_assignment grid) tt row
            system Hguard
            (grid_selectors_zero_outside _ _ _ _ _ _
              Hreplay Hwithin Hout)).
      + intros row.
        destruct (andb (0 <=? row) (row <? Domain.n domain)) eqn:Hrow.
        * apply Bool.andb_true_iff in Hrow.
          destruct Hrow as [Hlow Hhigh].
          apply Z.leb_le in Hlow.
          apply Z.ltb_lt in Hhigh.
          exact (Hlookups row (conj Hlow Hhigh)).
        * assert (Hout : ~ (0 <= row < Domain.usable_rows domain)).
          { apply Bool.andb_false_iff in Hrow.
            destruct Hrow as [Hrow | Hrow];
              [apply Z.leb_gt in Hrow | apply Z.ltb_ge in Hrow];
              clear - Hrow Husable;
              lia. }
          exact (lookups_defaults_all _ _ _ _ _ Hreplay Hdefaults row
            (grid_selectors_zero_outside _ _ _ _ _ _
              Hreplay Hwithin Hout)).
      + exact Hcopies.
  Qed.

End WithPrime.

End PlonkishMock.
