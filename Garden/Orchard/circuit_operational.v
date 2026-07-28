(** * Operational soundness of the whole Orchard action circuit.

    The realization bridge ([Halo2/realize/main.v], [Halo2/realize/sound.v])
    instantiated on the full Orchard action circuit under the concrete
    placement: the column indexes [Index.indices] ([Orchard/columns.v]), the
    V1 floor-planner placement [region_start_of]
    ([Orchard/circuit_synthesis_layout.v]), and the floor planner's trailing
    constants block ([Orchard/circuit_synthesis_constants.v]) as the
    [constants_events] tail of [operational_sound].  The pieces are:

    - the named event streams and constraint system of the circuit
      ([orchard_synthesis_events] / [orchard_constants_events] /
      [orchard_events] / [orchard_system]);
    - [vm_compute] certificates: the replay of the full stream (tail
      included) succeeds on symbolic advice/instance planes
      ([orchard_replay_ok]), and the system passes the [instance_free] /
      [flattening_ok] decision procedures;
    - the discharge of the [constants_materialized] premise
      ([orchard_constants_materialized]): every [Fact.CellIsConstant] of the
      Orchard synthesis program is covered by an [AssignFixed] + [Copy] pair
      of the constants tail, certified by a boolean coverage checker over the
      [ConstantsCheck] extraction of the [ConstrainConstant] leaves;
    - [orchard_operational_sound]: replay success and ideal operational
      acceptance of the serialized Orchard circuit give the relational
      [circuit_holds] consumed by the Orchard action theorem surface, with
      every decidable premise discharged by the certificates;
    - [orchard_action_statement_operational]: the composition with
      [OrchardAction.action_statement] — the Action statement of §4.18.4
      holds of the realized assignment, from replay success, mock acceptance,
      and the four witness-honesty side conditions. *)

Require Import Garden.Field.Field.
Require Import Garden.Halo2.main.
Require Import Garden.Halo2.Synthesis.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.serialize.
Require Import Garden.Halo2.realize.main.
Require Import Garden.Halo2.realize.sound.
Require Import Garden.Orchard.columns.
Require Import Garden.Orchard.circuit_synthesis_layout.
Require Garden.Orchard.circuit.
Require Garden.Orchard.circuit_synthesis_constants.
Require Import Garden.Orchard.circuit_synthesis_constants_check.
Require Garden.Orchard.protocol_spec.
Require Garden.Orchard.circuit_proof.inputs.
Require Garden.Orchard.circuit_proof.merkle.
Require Garden.Orchard.circuit_proof.note_commit.cmx.
Require Garden.Orchard.circuit_proof.valid_action_inputs.
Require Garden.Orchard.circuit_proof.main.

Import ListNotations.
Global Open Scope Z_scope.

#[local] Existing Instance Primes.PallasPIsPrime.

(** ** The named pieces of the serialized Orchard circuit *)

(** The serialized synthesis events of the Orchard action circuit, under the
    concrete column indexes and region placement.  Advice and instance values
    are free witness, not events. *)
Definition orchard_synthesis_events : list Raw.Event.t :=
  snd
    (V1.eval_layouter Index.indices region_start_of
      Garden.Orchard.circuit.orchard_usable_rows
      Garden.Orchard.circuit.synthesize).

(** The floor planner's trailing constants block: the constants-column
    [AssignFixed] + [Copy] events materialized after synthesis, replayed from
    the Rust implementation dump. *)
Definition orchard_constants_events : list Raw.Event.t :=
  Garden.Orchard.circuit_synthesis_constants.events.

(** The full checked stream: the synthesis events followed by the constants
    tail — the [evts ++ constants_events] stream of [operational_sound]. *)
Definition orchard_events : list Raw.Event.t :=
  orchard_synthesis_events ++ orchard_constants_events.

(** The Orchard constraint system: every gate and lookup argument of the
    action circuit's configure. *)
Definition orchard_system : ConstraintSystem.t columns :=
  𝓒.run_unit Garden.Orchard.circuit.configure ConstraintSystem.empty.

(** The same system over [Z]-indexed columns, as checked operationally. *)
Definition orchard_indexed_system
    : ConstraintSystem.t Configure.indexed_columns :=
  Configure.to_indexed Index.indices orchard_system.

(** The table-row bound of the circuit's lookup table load. *)
Definition orchard_table_rows : Z :=
  layouter_table_rows Garden.Orchard.circuit.synthesize.

(** The full stream coincides with the generated [synthesize_events], which
    appends the constants tail to the [run_with_region_start] output. *)
Lemma orchard_events_synthesize_events :
  orchard_events = Garden.Orchard.circuit.synthesize_events Index.indices.
Proof.
  unfold orchard_events, orchard_synthesis_events, orchard_constants_events,
    Garden.Orchard.circuit.synthesize_events, V1.run_with_region_start.
  destruct
    (V1.eval_layouter Index.indices region_start_of
      Garden.Orchard.circuit.orchard_usable_rows
      Garden.Orchard.circuit.synthesize)
    as [value events].
  reflexivity.
Qed.

(** ** Extraction of the [ConstrainConstant] obligations

    [ConstantsCheck.region_constants] / [ConstantsCheck.layouter_constants]
    ([circuit_synthesis_constants_check.v]) collect the [ConstrainConstant]
    leaves of a synthesis program as resolved [(raw cell, value)] pairs.  The
    lemmas below identify that extraction with the [Fact.CellIsConstant]
    entries of the reified fact list, so a boolean coverage check over the
    extraction discharges the [constants_materialized] premise. *)

Section ConstantsExtraction.
  Context {columns : Columns.t}.
  Context {RegionId : Set}.

  (** The value threaded by the extraction agrees with [region_value]. *)
  Lemma region_constants_value
      (idx : Indices.t columns) (rs : RegionId -> Z) (region : RegionId)
      {A : Set} (program : 𝓡 columns RegionId A) :
    fst (ConstantsCheck.region_constants idx rs region program) =
    region_value program.
  Proof.
    induction program as
      [A value | A B first IHfirst second IHsecond
      | selector offset annotation | annotation column offset value
      | lhs rhs | cell value];
      cbn [ConstantsCheck.region_constants region_value];
      try reflexivity.
    destruct (ConstantsCheck.region_constants idx rs region first)
      as [value_first constants_first] eqn:Hfirst.
    cbn [fst] in IHfirst.
    rewrite <- IHfirst.
    destruct (ConstantsCheck.region_constants idx rs region (second value_first))
      as [value_second constants_second] eqn:Hsecond.
    cbn [fst].
    specialize (IHsecond value_first).
    rewrite Hsecond in IHsecond.
    cbn [fst] in IHsecond.
    exact IHsecond.
  Qed.

  (** Every [Fact.CellIsConstant] of a region program appears in the
      extraction as its resolved [(raw cell, value)] pair. *)
  Lemma region_constant_fact_entry
      (idx : Indices.t columns) (rs : RegionId -> Z) (region : RegionId)
      {A : Set} (program : 𝓡 columns RegionId A)
      (cell : Garden.Halo2.Synthesis.Cell.t columns RegionId) (value : Z) :
    List.In (Fact.CellIsConstant cell value) (region_facts region program) ->
    List.In (Cell.to_raw idx rs cell, value)
      (snd (ConstantsCheck.region_constants idx rs region program)).
  Proof.
    induction program as
      [A value' | A B first IHfirst second IHsecond
      | selector offset annotation | annotation column offset value'
      | lhs rhs | cell' value'];
      cbn [ConstantsCheck.region_constants region_facts].
    - intros [].
    - pose proof (region_constants_value idx rs region first) as Hvalue.
      destruct (ConstantsCheck.region_constants idx rs region first)
        as [value_first constants_first] eqn:Hfirst.
      cbn [fst] in Hvalue.
      rewrite <- Hvalue.
      destruct
        (ConstantsCheck.region_constants idx rs region (second value_first))
        as [value_second constants_second] eqn:Hsecond.
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
        cbn [snd] in IHsecond.
        exact IHsecond.
    - intros [Heq | []].
      discriminate Heq.
    - intros [Heq | []].
      discriminate Heq.
    - intros [Heq | []].
      discriminate Heq.
    - intros [Heq | []].
      injection Heq as -> ->.
      left.
      reflexivity.
  Qed.

  Lemma layouter_constants_value
      (idx : Indices.t columns) (rs : RegionId -> Z)
      {A : Set} (program : 𝓛 columns RegionId A) :
    fst (ConstantsCheck.layouter_constants idx rs program) =
    layouter_value program.
  Proof.
    induction program as
      [A value | A B first IHfirst second IHsecond
      | A region name region_program | cell instance row
      | name entries | A name nested IHnested];
      cbn [ConstantsCheck.layouter_constants layouter_value];
      try reflexivity.
    - destruct (ConstantsCheck.layouter_constants idx rs first)
        as [value_first constants_first] eqn:Hfirst.
      cbn [fst] in IHfirst.
      rewrite <- IHfirst.
      destruct (ConstantsCheck.layouter_constants idx rs (second value_first))
        as [value_second constants_second] eqn:Hsecond.
      cbn [fst].
      specialize (IHsecond value_first).
      rewrite Hsecond in IHsecond.
      cbn [fst] in IHsecond.
      exact IHsecond.
    - exact (region_constants_value idx rs region (region_program region)).
    - exact IHnested.
  Qed.

  (** Every [Fact.CellIsConstant] of a layouter program appears in the
      extraction as its resolved [(raw cell, value)] pair. *)
  Lemma layouter_constant_fact_entry
      (idx : Indices.t columns) (rs : RegionId -> Z)
      {A : Set} (program : 𝓛 columns RegionId A)
      (cell : Garden.Halo2.Synthesis.Cell.t columns RegionId) (value : Z) :
    List.In (Fact.CellIsConstant cell value) (layouter_facts program) ->
    List.In (Cell.to_raw idx rs cell, value)
      (snd (ConstantsCheck.layouter_constants idx rs program)).
  Proof.
    induction program as
      [A value' | A B first IHfirst second IHsecond
      | A region name region_program | cell' instance row
      | name entries | A name nested IHnested];
      cbn [ConstantsCheck.layouter_constants layouter_facts].
    - intros [].
    - pose proof (layouter_constants_value idx rs first) as Hvalue.
      destruct (ConstantsCheck.layouter_constants idx rs first)
        as [value_first constants_first] eqn:Hfirst.
      cbn [fst] in Hvalue.
      rewrite <- Hvalue.
      destruct (ConstantsCheck.layouter_constants idx rs (second value_first))
        as [value_second constants_second] eqn:Hsecond.
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
        cbn [snd] in IHsecond.
        exact IHsecond.
    - exact (region_constant_fact_entry idx rs region
        (region_program region) cell value).
    - intros [Heq | []].
      discriminate Heq.
    - intros Hin.
      apply List.in_map_iff in Hin.
      destruct Hin as (entry & Heq & _).
      discriminate Heq.
    - exact IHnested.
  Qed.
End ConstantsExtraction.

(** ** The coverage checker for the constants tail *)

Definition column_kind_eqb (a b : Raw.ColumnKind.t) : bool :=
  match a, b with
  | Raw.ColumnKind.Advice, Raw.ColumnKind.Advice => true
  | Raw.ColumnKind.Fixed, Raw.ColumnKind.Fixed => true
  | Raw.ColumnKind.Instance_, Raw.ColumnKind.Instance_ => true
  | _, _ => false
  end.

Lemma column_kind_eqb_eq (a b : Raw.ColumnKind.t) :
  column_kind_eqb a b = true -> a = b.
Proof.
  destruct a, b; cbn [column_kind_eqb]; intros H;
    (reflexivity || discriminate H).
Qed.

Definition raw_cell_eqb (a b : Raw.Cell.t) : bool :=
  andb
    (andb
      (column_kind_eqb
        a.(Raw.Cell.column).(Raw.ColumnRef.kind)
        b.(Raw.Cell.column).(Raw.ColumnRef.kind))
      (a.(Raw.Cell.column).(Raw.ColumnRef.index) =?
        b.(Raw.Cell.column).(Raw.ColumnRef.index)))
    (a.(Raw.Cell.row) =? b.(Raw.Cell.row)).

Lemma raw_cell_eqb_eq (a b : Raw.Cell.t) :
  raw_cell_eqb a b = true -> a = b.
Proof.
  destruct a as [[kind_a index_a] row_a], b as [[kind_b index_b] row_b].
  unfold raw_cell_eqb.
  cbn [Raw.Cell.column Raw.Cell.row Raw.ColumnRef.kind Raw.ColumnRef.index].
  intros H.
  apply andb_prop in H.
  destruct H as [H Hrow].
  apply andb_prop in H.
  destruct H as [Hkind Hindex].
  apply column_kind_eqb_eq in Hkind.
  apply Z.eqb_eq in Hindex.
  apply Z.eqb_eq in Hrow.
  congruence.
Qed.

(** A [(raw cell, value)] obligation is covered by a constants-tail binding:
    some [ConstantCopy] entry copies its constants-column cell onto exactly
    that advice cell and pins exactly that value. *)
Definition entry_covered_by
    (bindings : list Garden.Orchard.circuit_synthesis_constants.ConstantCopy.t)
    (entry : Raw.Cell.t * Z) : bool :=
  List.existsb
    (fun binding =>
      andb
        (raw_cell_eqb
          (Garden.Orchard.circuit_synthesis_constants.advice_cell
            binding.(Garden.Orchard.circuit_synthesis_constants
              .ConstantCopy.advice_column)
            binding.(Garden.Orchard.circuit_synthesis_constants
              .ConstantCopy.advice_row))
          (fst entry))
        (binding.(Garden.Orchard.circuit_synthesis_constants
          .ConstantCopy.value) =? snd entry))
    bindings.

(** Events of a listed binding are events of the whole replay table. *)
Lemma to_event_list_in
    (binding : Garden.Orchard.circuit_synthesis_constants.ConstantCopy.t)
    (bindings : list Garden.Orchard.circuit_synthesis_constants.ConstantCopy.t)
    (event : Raw.Event.t) :
  List.In binding bindings ->
  List.In event (Garden.Orchard.circuit_synthesis_constants.to_events binding) ->
  List.In event
    (Garden.Orchard.circuit_synthesis_constants.to_event_list bindings).
Proof.
  induction bindings as [| binding' bindings IH]; intros Hbinding Hevent.
  - destruct Hbinding.
  - cbn [Garden.Orchard.circuit_synthesis_constants.to_event_list].
    apply List.in_or_app.
    destruct Hbinding as [Heq | Hbinding].
    + left.
      subst binding'.
      exact Hevent.
    + right.
      exact (IH Hbinding Hevent).
Qed.

(** A covered obligation has its [Copy] and [AssignFixed] events in the
    replay table, in the fixed-cell-to-constrained-cell orientation. *)
Lemma entry_covered_by_events
    (bindings : list Garden.Orchard.circuit_synthesis_constants.ConstantCopy.t)
    (entry : Raw.Cell.t * Z) :
  entry_covered_by bindings entry = true ->
  exists (column row : Z) (annotation : string),
    List.In
      (Raw.Event.Copy
        {|
          Raw.Cell.column := {|
            Raw.ColumnRef.kind := Raw.ColumnKind.Fixed;
            Raw.ColumnRef.index := column;
          |};
          Raw.Cell.row := row;
        |}
        (fst entry))
      (Garden.Orchard.circuit_synthesis_constants.to_event_list bindings) /\
    List.In (Raw.Event.AssignFixed column row annotation (snd entry))
      (Garden.Orchard.circuit_synthesis_constants.to_event_list bindings).
Proof.
  intros Hcovered.
  apply List.existsb_exists in Hcovered.
  destruct Hcovered as (binding & Hbinding_in & Hmatch).
  apply andb_prop in Hmatch.
  destruct Hmatch as [Hcell Hvalue].
  apply raw_cell_eqb_eq in Hcell.
  apply Z.eqb_eq in Hvalue.
  exists 3,
    binding.(Garden.Orchard.circuit_synthesis_constants
      .ConstantCopy.fixed_row),
    binding.(Garden.Orchard.circuit_synthesis_constants
      .ConstantCopy.annotation).
  split.
  - rewrite <- Hcell.
    apply (to_event_list_in binding bindings _ Hbinding_in).
    unfold Garden.Orchard.circuit_synthesis_constants.to_events.
    right.
    left.
    reflexivity.
  - rewrite <- Hvalue.
    apply (to_event_list_in binding bindings _ Hbinding_in).
    unfold Garden.Orchard.circuit_synthesis_constants.to_events.
    left.
    reflexivity.
Qed.

(** The whole-premise certificate: every extracted [ConstrainConstant]
    obligation of the Orchard synthesis program is covered by a binding of
    the constants replay table. *)
Lemma orchard_constants_check :
  List.forallb
    (entry_covered_by
      Garden.Orchard.circuit_synthesis_constants.constant_copies)
    (snd
      (ConstantsCheck.layouter_constants Index.indices region_start_of
        Garden.Orchard.circuit.synthesize)) = true.
Proof.
  vm_cast_no_check (@eq_refl bool true).
Qed.

(** The [constants_materialized] premise of [operational_sound], on the full
    Orchard stream: every [Fact.CellIsConstant] obligation is linked by a
    [Copy] to a constants-column cell pinned by an [AssignFixed], both inside
    the constants tail. *)
Lemma orchard_constants_materialized :
  constants_materialized Index.indices region_start_of
    (layouter_facts Garden.Orchard.circuit.synthesize)
    orchard_events.
Proof.
  intros cell value Hin.
  pose proof (layouter_constant_fact_entry Index.indices region_start_of
    Garden.Orchard.circuit.synthesize cell value Hin) as Hentry.
  pose proof (proj1 (List.forallb_forall
      (entry_covered_by
        Garden.Orchard.circuit_synthesis_constants.constant_copies)
      (snd
        (ConstantsCheck.layouter_constants Index.indices region_start_of
          Garden.Orchard.circuit.synthesize)))
    orchard_constants_check _ Hentry) as Hcovered.
  destruct (entry_covered_by_events
    Garden.Orchard.circuit_synthesis_constants.constant_copies
    (Cell.to_raw Index.indices region_start_of cell, value)
    Hcovered) as (column & row & annotation & Hcopy & Hassign).
  cbn [fst snd] in Hcopy, Hassign.
  exists column, row, annotation.
  split.
  - right.
    unfold orchard_events.
    apply List.in_or_app.
    right.
    exact Hcopy.
  - unfold orchard_events.
    apply List.in_or_app.
    right.
    exact Hassign.
Qed.

(** ** The decision-procedure certificates *)

(** No gate or lookup expression of the Orchard system mentions an instance
    column: instance rows are reached only through [ConstrainInstance]. *)
Lemma orchard_instance_free : instance_free orchard_system.
Proof.
  vm_cast_no_check (@eq_refl bool true).
Qed.

(** No [Constraint.Range _ 0] occurs in the Orchard system. *)
Lemma orchard_flattening_ok : flattening_ok orchard_system.
Proof.
  vm_cast_no_check (@eq_refl bool true).
Qed.

(** ** The bridge, in the projected form

    [operational_sound] binds the serialized stream through a pair
    destructuring of [V1.eval_layouter]; this corollary restates its
    [circuit_holds] conjunct with the stream named as the [snd] projection,
    the form the concrete instantiation uses. *)
Section OperationalSoundEvents.
  Context {columns : Columns.t}.
  Context {RegionId : Set}.
  Context {p : Z}.
  Context `{Prime p}.

  Lemma operational_sound_events
      {A : Set} (program : 𝓛 columns RegionId A)
      (idx : Indices.t columns) (rs : RegionId -> Z) (usable_rows : Z)
      (system : ConstraintSystem.t columns)
      (advice instance_ : Z -> Z -> Z) (grid : RawGrid.t)
      (constants_events : list Raw.Event.t) :
    instance_free system ->
    flattening_ok system ->
    constants_materialized idx rs (layouter_facts program)
      (snd (V1.eval_layouter idx rs usable_rows program) ++ constants_events) ->
    apply_events
      (snd (V1.eval_layouter idx rs usable_rows program) ++ constants_events)
      (initial_grid advice instance_) = Some grid ->
    mock_prover_accepts (Configure.to_indexed idx system)
      (snd (V1.eval_layouter idx rs usable_rows program) ++ constants_events) grid
      (layouter_table_rows program) ->
    circuit_holds (realize idx rs grid) program system.
  Proof.
    intros Hinstance_free Hflattening_ok.
    pose proof (operational_sound program idx rs usable_rows system advice
      instance_ grid constants_events Hinstance_free Hflattening_ok) as Hsound.
    destruct (V1.eval_layouter idx rs usable_rows program) as [v_op evts].
    cbn [snd].
    intros Hconstants Hreplay Hmock.
    exact (proj2 (proj2 (Hsound Hconstants Hreplay)) Hmock).
  Qed.
End OperationalSoundEvents.

(** ** The headline theorem

    Operational soundness of the whole Orchard action circuit: a successful
    replay of the full serialized stream (constants tail included) onto any
    witness planes, together with ideal operational acceptance of the
    indexed, flattened Orchard system over the resulting grid, gives the
    relational [circuit_holds] of the realized assignment — the [Holds]
    hypothesis of the Orchard action theorem surface
    ([circuit_proof/main.v]).  Every decidable premise of
    [operational_sound] is discharged by the certificates above. *)
Theorem orchard_operational_sound
    (advice instance_ : Z -> Z -> Z) (grid : RawGrid.t)
    (Hreplay :
      apply_events orchard_events (initial_grid advice instance_) =
        Some grid)
    (Hmock :
      mock_prover_accepts orchard_indexed_system orchard_events grid
        orchard_table_rows) :
  circuit_holds (realize Index.indices region_start_of grid)
    Garden.Orchard.circuit.synthesize
    orchard_system.
Proof.
  exact (operational_sound_events Garden.Orchard.circuit.synthesize
    Index.indices region_start_of Garden.Orchard.circuit.orchard_usable_rows
    orchard_system advice instance_ grid
    Garden.Orchard.circuit_synthesis_constants.events
    orchard_instance_free orchard_flattening_ok
    orchard_constants_materialized Hreplay Hmock).
Qed.

(** ** Composition with the Orchard action surface

    [OrchardAction.action_statement] consumes exactly the [circuit_holds]
    conclusion above: the §4.18.4 Action statement holds of the realized
    assignment, from replay success, mock acceptance, and the four
    witness-honesty side conditions stated on that assignment. *)
Corollary orchard_action_statement_operational
    (advice instance_ : Z -> Z -> Z) (grid : RawGrid.t)
    (Hreplay :
      apply_events orchard_events (initial_grid advice instance_) =
        Some grid)
    (Hmock :
      mock_prover_accepts orchard_indexed_system orchard_events grid
        orchard_table_rows)
    (Hmerkle_ok :
      Garden.Orchard.circuit_proof.merkle.OrchardActionMerkle.merkle_witness_ok
        (realize Index.indices region_start_of grid))
    (Hnote_ok :
      Garden.Orchard.circuit_proof.note_commit.cmx.NoteCommitNewCmx
        .note_commit_witness_ok
        (realize Index.indices region_start_of grid))
    (Hold_note_ok :
      Garden.Orchard.circuit_proof.valid_action_inputs.OrchardValidActionInputs
        .old_note_witness_ok
        (realize Index.indices region_start_of grid))
    (Hivk_ok :
      Garden.Orchard.circuit_proof.valid_action_inputs.OrchardValidActionInputs
        .commit_ivk_witness_ok
        (realize Index.indices region_start_of grid)) :
  (Garden.Orchard.circuit_proof.inputs.OrchardActionInputs.read_action_outputs
      (realize Index.indices region_start_of grid) =
    Garden.Orchard.protocol_spec.OrchardProtocolSpec.orchard_action_spec
      Garden.Orchard.circuit_proof.inputs.OrchardActionInputs
        .orchard_circuit_params
      (Garden.Orchard.circuit_proof.inputs.OrchardActionInputs
        .read_action_inputs
        (realize Index.indices region_start_of grid))) /\
  Garden.Orchard.circuit_proof.valid_action_inputs.OrchardValidActionInputs
    .ValidActionInputs
    (realize Index.indices region_start_of grid).
Proof.
  exact (Garden.Orchard.circuit_proof.main.OrchardAction.action_statement
    (realize Index.indices region_start_of grid)
    (orchard_operational_sound advice instance_ grid Hreplay Hmock)
    Hmerkle_ok Hnote_ok Hold_note_ok Hivk_ok).
Qed.

(** ** The replay certificate

    Replay of the full Orchard stream — synthesis events plus the constants
    tail — succeeds on any witness: no write collides.  The conflict check
    never reads the witness planes, so the verdict computes with [advice]
    and [instance_] symbolic. *)
Lemma orchard_replay_ok (advice instance_ : Z -> Z -> Z) :
  replay_is_ok orchard_events (initial_grid advice instance_) = true.
Proof.
  vm_cast_no_check (@eq_refl bool true).
Qed.

Lemma orchard_replay_some (advice instance_ : Z -> Z -> Z) :
  exists grid,
    apply_events orchard_events (initial_grid advice instance_) = Some grid.
Proof.
  apply replay_is_ok_some, orchard_replay_ok.
Qed.
