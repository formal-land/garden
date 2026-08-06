(** * Placement certificates for operational completeness (E1)

    The input-independent half of the grid-identification obligation: every
    fact here mentions only [layouter_facts circuit.synthesize], the
    serialized stream [orchard_events], the configured constraint system and
    the concrete placement — never a witness input.  The [vm_compute]
    certificates are therefore shared verbatim by the concrete (E1a) and the
    universal (E1b) rungs.

    - [orchard_enables_placed]: every [Raw.Event.EnableSelector] of the
      Orchard stream sits at the absolute address of an enabled selector
      point, with the matching selector index.  With the replay lemmas below
      this pins the realized selector plane to [0] off the enabled points —
      the placed replacement for [Complete.honest_selector_plane], which is
      *false* at a realized assignment because [region_start_of] is not
      row-injective.
    - [orchard_advice_inversion]: the address map
      [(advice column index, absolute row) |-> (column, region, offset)] is
      exact on every advice cell any obligation reads — the gate queries at
      the enabled points, the lookup-argument queries at the enabled points,
      and the cells named by the witness facts (155,861 cells).  This is what
      makes the free advice plane chosen in [operational/main.v] agree with
      the honest generator definitionally at every cell that matters.
    - [orchard_gate_fixed_written] / [orchard_lookup_fixed_written]: every
      fixed cell queried by a gate or a lookup argument at an enabled point
      is program-written, so its value is pinned by the replay
      ([determined_facts_hold_incl]) and equals the honest fixed plane
      ([Complete.no_conflicting_writes_fixed]) with no unwritten or aliased
      case to consider.
    - [orchard_constants_reverse]: every binding of the floor planner's
      constants tail is covered by a [Fact.CellIsConstant] of
      [Complete.witness_facts], the direction the mock checker's copy
      obligations need.

    The generic replay-plane lemmas at the top ([replay_advice_plane],
    [replay_instance_plane], [replay_selector_unwritten]) are the converses
    of [Halo2/realize/facts.v]'s pinning lemmas: [apply_event] only ever
    calls [set_selector] / [set_fixed] / [fill_fixed], so the advice and
    instance planes are replay invariants and an unenabled selector cell
    keeps its initial value. *)

Require Import Garden.Halo2.main.
Require Import Garden.Halo2.Synthesis.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.complete.
Require Import Garden.Halo2.serialize.
Require Import Garden.Halo2.realize.main.
Require Import Garden.Halo2.realize.facts.
Require Import Garden.Halo2.realize.sound.
Require Import Garden.Field.Field.
Require Import Garden.Plonky3.M.
Require Import Garden.Orchard.columns.
Require Import Garden.Orchard.decidable_eq.
Require Import Garden.Orchard.circuit_synthesis_layout.
Require Import Garden.Orchard.circuit_operational.
Require Garden.Orchard.circuit_synthesis_constants.
Require Import Garden.Orchard.circuit_completeness.generator.certificates.
Require Import Garden.Orchard.circuit_completeness.operational.agreement_congruences.
Require Garden.Orchard.circuit.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Lists.List.
Require Import Stdlib.micromega.Lia.

Import ListNotations.
Global Open Scope Z_scope.

#[local] Existing Instance Primes.PallasPIsPrime.

Module OrchardPlacementCerts.

  (** ** Replay leaves the free planes alone

      [apply_event] writes only through [RawGrid.set_selector],
      [RawGrid.set_fixed] and [RawGrid.fill_fixed], none of which touches the
      [Advice] or [Instance_] plane. *)

  Lemma apply_event_advice (state state' : ReplayState.t)
      (event : Raw.Event.t) (column row : Z) :
    apply_event state event = Some state' ->
    state'.(ReplayState.grid).(RawGrid.cell) Raw.ColumnKind.Advice column row =
    state.(ReplayState.grid).(RawGrid.cell) Raw.ColumnKind.Advice column row.
  Proof.
    destruct event; cbn [apply_event];
      try (intros Heq; injection Heq as <-; reflexivity);
      [ destruct (List.existsb _ _)
      | destruct (orb _ _)
      | destruct (orb _ _) ];
      intros Heq; try discriminate Heq; injection Heq as <-; reflexivity.
  Qed.

  Lemma apply_event_instance (state state' : ReplayState.t)
      (event : Raw.Event.t) (column row : Z) :
    apply_event state event = Some state' ->
    state'.(ReplayState.grid).(RawGrid.cell) Raw.ColumnKind.Instance_
      column row =
    state.(ReplayState.grid).(RawGrid.cell) Raw.ColumnKind.Instance_
      column row.
  Proof.
    destruct event; cbn [apply_event];
      try (intros Heq; injection Heq as <-; reflexivity);
      [ destruct (List.existsb _ _)
      | destruct (orb _ _)
      | destruct (orb _ _) ];
      intros Heq; try discriminate Heq; injection Heq as <-; reflexivity.
  Qed.

  (** A selector cell is only ever written by an [EnableSelector] event at
      exactly its address. *)
  Lemma apply_event_selector_off (state state' : ReplayState.t)
      (event : Raw.Event.t) (column row : Z) :
    apply_event state event = Some state' ->
    (forall annotation : string,
      event <> Raw.Event.EnableSelector column row annotation) ->
    state'.(ReplayState.grid).(RawGrid.sel) column row =
    state.(ReplayState.grid).(RawGrid.sel) column row.
  Proof.
    destruct event; cbn [apply_event];
      try (intros Heq _; injection Heq as <-; reflexivity);
      [ destruct (List.existsb _ _)
      | destruct (orb _ _)
      | destruct (orb _ _) ];
      intros Heq Hne; try discriminate Heq; injection Heq as <-;
      try reflexivity.
    cbn [ReplayState.grid RawGrid.set_selector RawGrid.sel].
    destruct (column =? selector) eqn:Hcolumn; cbn [andb]; [| reflexivity].
    destruct (row =? row0) eqn:Hrow; [| reflexivity].
    exfalso.
    apply Z.eqb_eq in Hcolumn, Hrow.
    subst.
    exact (Hne annotation eq_refl).
  Qed.

  Lemma apply_events_log_advice (events : list Raw.Event.t)
      (state state' : ReplayState.t) (column row : Z) :
    apply_events_log events state = Some state' ->
    state'.(ReplayState.grid).(RawGrid.cell) Raw.ColumnKind.Advice column row =
    state.(ReplayState.grid).(RawGrid.cell) Raw.ColumnKind.Advice column row.
  Proof.
    revert state.
    induction events as [| event events IH]; intros state Hreplay.
    - injection Hreplay as <-. reflexivity.
    - cbn [apply_events_log] in Hreplay.
      destruct (apply_event state event) as [state1 |] eqn:Hevent;
        [| discriminate Hreplay].
      rewrite (IH state1 Hreplay).
      exact (apply_event_advice state state1 event column row Hevent).
  Qed.

  Lemma apply_events_log_instance (events : list Raw.Event.t)
      (state state' : ReplayState.t) (column row : Z) :
    apply_events_log events state = Some state' ->
    state'.(ReplayState.grid).(RawGrid.cell) Raw.ColumnKind.Instance_
      column row =
    state.(ReplayState.grid).(RawGrid.cell) Raw.ColumnKind.Instance_
      column row.
  Proof.
    revert state.
    induction events as [| event events IH]; intros state Hreplay.
    - injection Hreplay as <-. reflexivity.
    - cbn [apply_events_log] in Hreplay.
      destruct (apply_event state event) as [state1 |] eqn:Hevent;
        [| discriminate Hreplay].
      rewrite (IH state1 Hreplay).
      exact (apply_event_instance state state1 event column row Hevent).
  Qed.

  Lemma apply_events_log_selector_off (events : list Raw.Event.t)
      (state state' : ReplayState.t) (column row : Z) :
    apply_events_log events state = Some state' ->
    (forall annotation : string,
      ~ List.In (Raw.Event.EnableSelector column row annotation) events) ->
    state'.(ReplayState.grid).(RawGrid.sel) column row =
    state.(ReplayState.grid).(RawGrid.sel) column row.
  Proof.
    revert state.
    induction events as [| event events IH]; intros state Hreplay Hnotin.
    - injection Hreplay as <-. reflexivity.
    - cbn [apply_events_log] in Hreplay.
      destruct (apply_event state event) as [state1 |] eqn:Hevent;
        [| discriminate Hreplay].
      rewrite (IH state1 Hreplay
        (fun annotation Hin => Hnotin annotation (or_intror Hin))).
      apply (apply_event_selector_off state state1 event column row Hevent).
      intros annotation Heq.
      exact (Hnotin annotation (or_introl Heq)).
  Qed.

  (** The three plane invariants, at the [apply_events] level. *)

  Lemma replay_advice_plane (events : list Raw.Event.t)
      (initial final : RawGrid.t) (column row : Z) :
    apply_events events initial = Some final ->
    final.(RawGrid.cell) Raw.ColumnKind.Advice column row =
    initial.(RawGrid.cell) Raw.ColumnKind.Advice column row.
  Proof.
    unfold apply_events.
    destruct (apply_events_log events (ReplayState.init initial))
      as [state |] eqn:Hreplay; [| discriminate].
    intros Hfinal.
    injection Hfinal as <-.
    exact (apply_events_log_advice events _ state column row Hreplay).
  Qed.

  Lemma replay_instance_plane (events : list Raw.Event.t)
      (initial final : RawGrid.t) (column row : Z) :
    apply_events events initial = Some final ->
    final.(RawGrid.cell) Raw.ColumnKind.Instance_ column row =
    initial.(RawGrid.cell) Raw.ColumnKind.Instance_ column row.
  Proof.
    unfold apply_events.
    destruct (apply_events_log events (ReplayState.init initial))
      as [state |] eqn:Hreplay; [| discriminate].
    intros Hfinal.
    injection Hfinal as <-.
    exact (apply_events_log_instance events _ state column row Hreplay).
  Qed.

  Lemma replay_selector_unwritten (events : list Raw.Event.t)
      (initial final : RawGrid.t) (column row : Z) :
    apply_events events initial = Some final ->
    (forall annotation : string,
      ~ List.In (Raw.Event.EnableSelector column row annotation) events) ->
    final.(RawGrid.sel) column row = initial.(RawGrid.sel) column row.
  Proof.
    unfold apply_events.
    destruct (apply_events_log events (ReplayState.init initial))
      as [state |] eqn:Hreplay; [| discriminate].
    intros Hfinal Hnotin.
    injection Hfinal as <-.
    exact (apply_events_log_selector_off events _ state column row Hreplay
      Hnotin).
  Qed.

  (** ** Shared abbreviations *)

  Definition facts : list (Fact.t columns RegionId.t) :=
    OrchardCompletenessCertificates.facts.

  Definition system : ConstraintSystem.t columns :=
    OrchardCompletenessCertificates.system.

  Definition enabled : list (Selector.t * RegionId.t * Z) :=
    Complete.enabled_points facts.

  (** ** Certificate 1: every selector enable sits on an enabled point *)

  Fixpoint enable_pairs (events : list Raw.Event.t) : list (Z * Z) :=
    match events with
    | [] => []
    | Raw.Event.EnableSelector selector row _ :: events =>
        (selector, row) :: enable_pairs events
    | _ :: events => enable_pairs events
    end.

  Lemma enable_pairs_In (events : list Raw.Event.t)
      (selector row : Z) (annotation : string) :
    List.In (Raw.Event.EnableSelector selector row annotation) events ->
    List.In (selector, row) (enable_pairs events).
  Proof.
    induction events as [| event events IH]; intros Hin; [contradiction |].
    destruct Hin as [Heq | Hin].
    - subst event. cbn [enable_pairs]. left. reflexivity.
    - destruct event; cbn [enable_pairs]; try exact (IH Hin).
      right. exact (IH Hin).
  Qed.

  (** The absolute addresses of the enabled selector points. *)
  Definition placed_enabled : list (Z * Z) :=
    List.map
      (fun point =>
        let '(selector, region, offset) := point in
        (Index.selector selector, region_start_of region + offset))
      enabled.

  Definition addr_eqb (address1 address2 : Z * Z) : bool :=
    ((fst address1 =? fst address2) && (snd address1 =? snd address2))%bool.

  Lemma addr_eqb_eq (address1 address2 : Z * Z) :
    addr_eqb address1 address2 = true -> address1 = address2.
  Proof.
    destruct address1 as [column1 row1], address2 as [column2 row2].
    unfold addr_eqb.
    cbn [fst snd].
    intros Heq.
    apply andb_prop in Heq.
    destruct Heq as [Hcolumn Hrow].
    apply Z.eqb_eq in Hcolumn, Hrow.
    congruence.
  Qed.

  Lemma orchard_enables_placed :
    List.forallb
      (fun address => List.existsb (addr_eqb address) placed_enabled)
      (enable_pairs orchard_events) = true.
  Proof. vm_cast_no_check (@eq_refl bool true). Qed.

  (** The consumption form: an [EnableSelector] event of the stream names the
      absolute address of some enabled point of the same selector. *)
  Lemma enable_event_point (selector row : Z) (annotation : string) :
    List.In (Raw.Event.EnableSelector selector row annotation) orchard_events ->
    exists (sel : Selector.t) (region : RegionId.t) (offset : Z),
      List.In (sel, region, offset) enabled /\
      Index.selector sel = selector /\
      region_start_of region + offset = row.
  Proof.
    intros Hin.
    pose proof (proj1
      (List.forallb_forall
        (fun address => List.existsb (addr_eqb address) placed_enabled)
        (enable_pairs orchard_events))
      orchard_enables_placed (selector, row)
      (enable_pairs_In orchard_events selector row annotation Hin)) as Hmemb.
    apply List.existsb_exists in Hmemb.
    destruct Hmemb as (address & Hplaced & Heq).
    apply addr_eqb_eq in Heq.
    unfold placed_enabled in Hplaced.
    apply List.in_map_iff in Hplaced.
    destruct Hplaced as (point & Haddress & Hpoint).
    destruct point as [ [sel region] offset].
    exists sel, region, offset.
    split; [exact Hpoint |].
    rewrite <- Haddress in Heq.
    injection Heq as Hselector Hrow.
    split; [symmetry; exact Hselector | symmetry; exact Hrow].
  Qed.

  (** ** The queried cells of the finite obligations

      The advice and fixed cells that a gate constraint body or a lookup
      argument reads at a given point, and the cells the witness facts name.
      These are pure syntax over the configured system and the reified fact
      list: no assignment, no witness input. *)

  (** The query extractors are the ones the agreement congruences are stated
      over ([agreement_congruences.v]), so no bridge is needed between the
      cell inventories certified here and the hypotheses those congruences
      consume. *)

  Definition expression_advice (expression : Expression.t columns)
      : list (Advice.t * Z) :=
    Agree.advice_queries expression.

  Definition expression_fixed (expression : Expression.t columns)
      : list (Fixed.t * Z) :=
    Agree.fixed_queries expression.

  Definition constraint_advice (constraint : Constraint.t columns)
      : list (Advice.t * Z) :=
    Agree.constraint_advice_queries constraint.

  Definition constraint_fixed (constraint : Constraint.t columns)
      : list (Fixed.t * Z) :=
    Agree.constraint_fixed_queries constraint.

  (** The constraint bodies guarded by [sel] in one gate's constraint list. *)
  Fixpoint guarded_of (sel : Selector.t) (constraints : Constraints.t columns)
      : list (Constraint.t columns) :=
    match constraints with
    | [] => []
    | (_, Constraint.Select sel' body) :: constraints =>
        if OrchardDecidableEq.selector_eqb sel sel'
        then body :: guarded_of sel constraints
        else guarded_of sel constraints
    | _ :: constraints => guarded_of sel constraints
    end.

  Lemma guarded_of_In (sel : Selector.t) (constraints : Constraints.t columns)
      (name : option string) (body : Constraint.t columns) :
    List.In (name, Constraint.Select sel body) constraints ->
    List.In body (guarded_of sel constraints).
  Proof.
    induction constraints as [| constraint constraints IH]; intros Hin;
      [contradiction |].
    destruct Hin as [Heq | Hin].
    - subst constraint.
      cbn [guarded_of].
      rewrite (proj2 (OrchardDecidableEq.selector_eqb_eq sel sel) eq_refl).
      left. reflexivity.
    - destruct constraint as [name' constraint'].
      destruct constraint' as [sel' body' | | | | | |];
        cbn [guarded_of]; try exact (IH Hin).
      destruct (OrchardDecidableEq.selector_eqb sel sel');
        [right |]; exact (IH Hin).
  Qed.

  Definition guarded_bodies (sel : Selector.t) : list (Constraint.t columns) :=
    List.flat_map
      (fun gate => guarded_of sel gate.(Gate.constraints))
      system.(ConstraintSystem.gates).

  Lemma guarded_bodies_In (sel : Selector.t) (gate : Gate.t columns)
      (name : option string) (body : Constraint.t columns) :
    List.In gate system.(ConstraintSystem.gates) ->
    List.In (name, Constraint.Select sel body) gate.(Gate.constraints) ->
    List.In body (guarded_bodies sel).
  Proof.
    intros Hgate Hbody.
    apply List.in_flat_map.
    exists gate.
    split; [exact Hgate |].
    exact (guarded_of_In sel _ name body Hbody).
  Qed.

  (** The lookup-argument expressions mentioning [sel]. *)
  Definition mentioning_expressions (sel : Selector.t)
      : list (Expression.t columns) :=
    List.flat_map
      (fun arg =>
        if Complete.arg_mentions_selector OrchardDecidableEq.selector_eqb
             sel arg
        then List.map fst arg.(LookupArgument.pairs)
        else [])
      system.(ConstraintSystem.lookups).

  Lemma mentioning_expressions_In (sel : Selector.t)
      (arg : LookupArgument.t columns) (expression : Expression.t columns)
      (column : Lookup.t) :
    List.In arg system.(ConstraintSystem.lookups) ->
    Complete.arg_mentions_selector OrchardDecidableEq.selector_eqb sel arg =
      true ->
    List.In (expression, column) arg.(LookupArgument.pairs) ->
    List.In expression (mentioning_expressions sel).
  Proof.
    intros Harg Hmention Hpair.
    apply List.in_flat_map.
    exists arg.
    split; [exact Harg |].
    rewrite Hmention.
    exact (List.in_map fst _ _ Hpair).
  Qed.

  (** ** The three cell inventories *)

  Definition point_cells {A : Set}
      (queries : Selector.t -> list (A * Z))
      : list (A * RegionId.t * Z) :=
    List.flat_map
      (fun point =>
        let '(sel, region, row) := point in
        List.map (fun query => (fst query, region, row + snd query))
          (queries sel))
      enabled.

  Definition gate_advice_queries (sel : Selector.t) : list (Advice.t * Z) :=
    List.flat_map constraint_advice (guarded_bodies sel).

  Definition gate_fixed_queries (sel : Selector.t) : list (Fixed.t * Z) :=
    List.flat_map constraint_fixed (guarded_bodies sel).

  Definition lookup_advice_queries (sel : Selector.t) : list (Advice.t * Z) :=
    List.flat_map expression_advice (mentioning_expressions sel).

  Definition lookup_fixed_queries (sel : Selector.t) : list (Fixed.t * Z) :=
    List.flat_map expression_fixed (mentioning_expressions sel).

  Definition gate_advice_cells : list (Advice.t * RegionId.t * Z) :=
    point_cells gate_advice_queries.

  Definition gate_fixed_cells : list (Fixed.t * RegionId.t * Z) :=
    point_cells gate_fixed_queries.

  Definition lookup_advice_cells : list (Advice.t * RegionId.t * Z) :=
    point_cells lookup_advice_queries.

  Definition lookup_fixed_cells : list (Fixed.t * RegionId.t * Z) :=
    point_cells lookup_fixed_queries.

  Lemma point_cells_In {A : Set}
      (queries : Selector.t -> list (A * Z))
      (sel : Selector.t) (region : RegionId.t) (row : Z)
      (column : A) (rotation : Z) :
    List.In (sel, region, row) enabled ->
    List.In (column, rotation) (queries sel) ->
    List.In (column, region, row + rotation) (point_cells queries).
  Proof.
    intros Hpoint Hquery.
    apply List.in_flat_map.
    exists (sel, region, row).
    split; [exact Hpoint |].
    exact (List.in_map
      (fun query => (fst query, region, row + snd query)) _ _ Hquery).
  Qed.

  (** The advice cells named by the witness facts. *)
  Definition cell_advice (cell : Garden.Halo2.Synthesis.Cell.t columns
      RegionId.t) : list (Advice.t * RegionId.t * Z) :=
    match cell.(Garden.Halo2.Synthesis.Cell.column) with
    | Garden.Halo2.Synthesis.ColumnRef.Advice column =>
        [(column, cell.(Garden.Halo2.Synthesis.Cell.region),
          cell.(Garden.Halo2.Synthesis.Cell.row_offset))]
    | _ => []
    end.

  Definition fact_advice_cells (fact : Fact.t columns RegionId.t)
      : list (Advice.t * RegionId.t * Z) :=
    match fact with
    | Fact.CellsEqual left_cell right_cell =>
        cell_advice left_cell ++ cell_advice right_cell
    | Fact.InstanceIs cell _ _ => cell_advice cell
    | Fact.CellIsConstant cell _ => cell_advice cell
    | _ => []
    end.

  Definition witness_advice_cells : list (Advice.t * RegionId.t * Z) :=
    List.flat_map fact_advice_cells (Complete.witness_facts facts).

  Lemma witness_advice_cells_In (fact : Fact.t columns RegionId.t)
      (cell : Advice.t * RegionId.t * Z) :
    List.In fact (Complete.witness_facts facts) ->
    List.In cell (fact_advice_cells fact) ->
    List.In cell witness_advice_cells.
  Proof.
    intros Hfact Hcell.
    apply List.in_flat_map.
    exists fact.
    split; [exact Hfact | exact Hcell].
  Qed.

  (** ** Certificate 2: the advice address map is invertible where it matters

      The needed cells: gate queries, lookup-argument queries and
      witness-fact cells.  Their absolute rows lie in [0, 1771], well inside
      the [2048]-row grid. *)

  Definition owner : Set := Advice.t * RegionId.t * Z.

  Definition needed_cells : list owner :=
    gate_advice_cells ++ lookup_advice_cells ++ witness_advice_cells.

  (** A binary trie over the packed address key.  The value type is fixed, so
      the tree carries no parameter and never enters an implicit-argument
      insertion. *)
  Inductive OwnerTree : Set :=
  | OwnerLeaf
  | OwnerNode (entry : option owner) (branch0 branch1 : OwnerTree).

  Fixpoint owner_add (key : positive) (cell : owner) (tree : OwnerTree)
      : OwnerTree :=
    match key with
    | xH =>
        match tree with
        | OwnerLeaf => OwnerNode (Some cell) OwnerLeaf OwnerLeaf
        | OwnerNode _ b0 b1 => OwnerNode (Some cell) b0 b1
        end
    | xO key =>
        match tree with
        | OwnerLeaf => OwnerNode None (owner_add key cell OwnerLeaf) OwnerLeaf
        | OwnerNode entry b0 b1 => OwnerNode entry (owner_add key cell b0) b1
        end
    | xI key =>
        match tree with
        | OwnerLeaf => OwnerNode None OwnerLeaf (owner_add key cell OwnerLeaf)
        | OwnerNode entry b0 b1 => OwnerNode entry b0 (owner_add key cell b1)
        end
    end.

  Fixpoint owner_get (key : positive) (tree : OwnerTree) : option owner :=
    match tree with
    | OwnerLeaf => None
    | OwnerNode entry b0 b1 =>
        match key with
        | xH => entry
        | xO key => owner_get key b0
        | xI key => owner_get key b1
        end
    end.

  (** The packed key of an absolute advice address.  The circuit has ten
      advice columns and rows below [2048]; the offset keeps every key
      positive. *)
  Definition address_key (column row : Z) : positive :=
    Z.to_pos (1 + column * 16384 + (row + 8192)).

  Definition cell_key (cell : owner) : positive :=
    let '(column, region, offset) := cell in
    address_key (Index.advice column) (region_start_of region + offset).

  Fixpoint owner_build (cells : list owner) (tree : OwnerTree) : OwnerTree :=
    match cells with
    | [] => tree
    | cell :: cells => owner_build cells (owner_add (cell_key cell) cell tree)
    end.

  Definition owner_table : OwnerTree := owner_build needed_cells OwnerLeaf.

  (** The address map: the inverse of [Cell.to_raw] restricted to the advice
      cells the obligations read. *)
  Definition advice_owner (column row : Z) : option owner :=
    owner_get (address_key column row) owner_table.

  Definition owner_eqb (owner1 owner2 : owner) : bool :=
    let '(column1, region1, offset1) := owner1 in
    let '(column2, region2, offset2) := owner2 in
    (OrchardDecidableEq.advice_eqb column1 column2 &&
     OrchardDecidableEq.region_id_eqb region1 region2 &&
     (offset1 =? offset2))%bool.

  Lemma owner_eqb_eq (owner1 owner2 : owner) :
    owner_eqb owner1 owner2 = true -> owner1 = owner2.
  Proof.
    destruct owner1 as [ [column1 region1] offset1].
    destruct owner2 as [ [column2 region2] offset2].
    cbn [owner_eqb].
    intros Heq.
    apply andb_prop in Heq.
    destruct Heq as [Heq Hoffset].
    apply andb_prop in Heq.
    destruct Heq as [Hcolumn Hregion].
    apply (proj1 (OrchardDecidableEq.advice_eqb_eq _ _)) in Hcolumn.
    apply (proj1 (OrchardDecidableEq.region_id_eqb_eq _ _)) in Hregion.
    apply Z.eqb_eq in Hoffset.
    congruence.
  Qed.

  Definition owner_option_eqb (entry : option owner) (cell : owner) : bool :=
    match entry with
    | Some entry => owner_eqb entry cell
    | None => false
    end.

  Lemma orchard_advice_inversion :
    List.forallb
      (fun cell => owner_option_eqb (owner_get (cell_key cell) owner_table) cell)
      needed_cells = true.
  Proof. vm_cast_no_check (@eq_refl bool true). Qed.

  (** The consumption form: at every needed cell the address map returns that
      very cell, so the free advice plane pulled back along the placement
      reproduces the region-addressed value. *)
  Lemma advice_owner_needed (column : Advice.t) (region : RegionId.t)
      (offset : Z) :
    List.In (column, region, offset) needed_cells ->
    advice_owner (Index.advice column) (region_start_of region + offset) =
      Some (column, region, offset).
  Proof.
    intros Hin.
    pose proof (proj1
      (List.forallb_forall
        (fun cell =>
          owner_option_eqb (owner_get (cell_key cell) owner_table) cell)
        needed_cells)
      orchard_advice_inversion (column, region, offset) Hin) as Hcheck.
    cbv beta in Hcheck.
    unfold advice_owner.
    change (address_key (Index.advice column)
        (region_start_of region + offset))
      with (cell_key (column, region, offset)).
    revert Hcheck.
    unfold owner_option_eqb.
    destruct (owner_get (cell_key (column, region, offset)) owner_table)
      as [entry |]; [| intros Hcheck; discriminate Hcheck].
    intros Hcheck.
    apply owner_eqb_eq in Hcheck.
    rewrite Hcheck.
    reflexivity.
  Qed.

  Lemma needed_cells_gate (column : Advice.t) (region : RegionId.t)
      (offset : Z) :
    List.In (column, region, offset) gate_advice_cells ->
    List.In (column, region, offset) needed_cells.
  Proof.
    intros Hin.
    unfold needed_cells.
    apply List.in_or_app.
    left. exact Hin.
  Qed.

  Lemma needed_cells_lookup (column : Advice.t) (region : RegionId.t)
      (offset : Z) :
    List.In (column, region, offset) lookup_advice_cells ->
    List.In (column, region, offset) needed_cells.
  Proof.
    intros Hin.
    unfold needed_cells.
    apply List.in_or_app.
    right.
    apply List.in_or_app.
    left. exact Hin.
  Qed.

  Lemma needed_cells_witness (column : Advice.t) (region : RegionId.t)
      (offset : Z) :
    List.In (column, region, offset) witness_advice_cells ->
    List.In (column, region, offset) needed_cells.
  Proof.
    intros Hin.
    unfold needed_cells.
    apply List.in_or_app.
    right.
    apply List.in_or_app.
    right. exact Hin.
  Qed.

  (** ** Certificate 3: every queried fixed cell is program-written *)

  Definition fixed_written (cell : Fixed.t * RegionId.t * Z) : bool :=
    let '(column, region, offset) := cell in
    match
      Complete.fixed_lookup OrchardDecidableEq.fixed_eqb
        OrchardDecidableEq.region_id_eqb (Complete.fixed_writes facts)
        column region offset
    with
    | Some _ => true
    | None => false
    end.

  Lemma orchard_gate_fixed_written :
    List.forallb fixed_written gate_fixed_cells = true.
  Proof. vm_cast_no_check (@eq_refl bool true). Qed.

  Lemma orchard_lookup_fixed_written :
    List.forallb fixed_written lookup_fixed_cells = true.
  Proof. vm_cast_no_check (@eq_refl bool true). Qed.

  (** The two membership converses of [Complete.fixed_writes_In]. *)

  Lemma fixed_lookup_In
      (writes : list (Fixed.t * RegionId.t * Z * Z))
      (column : Fixed.t) (region : RegionId.t) (offset value : Z) :
    Complete.fixed_lookup OrchardDecidableEq.fixed_eqb
      OrchardDecidableEq.region_id_eqb writes column region offset =
      Some value ->
    List.In (column, region, offset, value) writes.
  Proof.
    induction writes as [| write writes IH];
      cbn [Complete.fixed_lookup]; [discriminate |].
    destruct write as [ [ [column' region'] offset'] value'].
    destruct
      (OrchardDecidableEq.fixed_eqb column column' &&
       OrchardDecidableEq.region_id_eqb region region' &&
       (offset =? offset'))%bool eqn:Hmatch.
    - intros Heq.
      injection Heq as <-.
      left.
      apply andb_prop in Hmatch.
      destruct Hmatch as [Hmatch Hoffset].
      apply andb_prop in Hmatch.
      destruct Hmatch as [Hcolumn Hregion].
      apply (proj1 (OrchardDecidableEq.fixed_eqb_eq _ _)) in Hcolumn.
      apply (proj1 (OrchardDecidableEq.region_id_eqb_eq _ _)) in Hregion.
      apply Z.eqb_eq in Hoffset.
      congruence.
    - intros Hlookup.
      right.
      exact (IH Hlookup).
  Qed.

  Lemma fixed_writes_fact (fs : list (Fact.t columns RegionId.t))
      (column : Fixed.t) (region : RegionId.t) (offset value : Z) :
    List.In (column, region, offset, value) (Complete.fixed_writes fs) ->
    List.In (Fact.FixedIs column region offset value) fs.
  Proof.
    induction fs as [| fact fs IH]; intros Hin; [contradiction |].
    destruct fact as
      [ ? ? ? | column' region' offset' value' | ? ? | ? ? ? | ? ? ? | ? ? ];
      cbn [Complete.fixed_writes] in Hin;
      try (right; exact (IH Hin)).
    destruct Hin as [Heq | Hin].
    - injection Heq as Hcolumn Hregion Hoffset Hvalue.
      subst.
      left. reflexivity.
    - right. exact (IH Hin).
  Qed.

  (** The consumption form: a queried fixed cell carries a [Fact.FixedIs] of
      the synthesis program, pinning both the honest plane
      ([Complete.no_conflicting_writes_fixed]) and the replayed grid
      ([determined_facts_hold_incl]). *)
  Lemma fixed_written_fact (column : Fixed.t) (region : RegionId.t)
      (offset : Z) :
    fixed_written (column, region, offset) = true ->
    exists value : Z,
      List.In (Fact.FixedIs column region offset value) facts /\
      Complete.fixed_write_or_zero OrchardDecidableEq.fixed_eqb
        OrchardDecidableEq.region_id_eqb facts column region offset = value.
  Proof.
    unfold fixed_written.
    destruct
      (Complete.fixed_lookup OrchardDecidableEq.fixed_eqb
        OrchardDecidableEq.region_id_eqb (Complete.fixed_writes facts)
        column region offset) as [value |] eqn:Hlookup; [| discriminate].
    intros _.
    exists value.
    split.
    - exact (fixed_writes_fact facts column region offset value
        (fixed_lookup_In _ column region offset value Hlookup)).
    - unfold Complete.fixed_write_or_zero.
      rewrite Hlookup.
      reflexivity.
  Qed.

  (** ** Certificate 7: guarded gate bodies query no selector

      Every gate constraint of the Orchard system is [Constraint.Select sel
      body] with [body] free of [Expression.Selector] atoms, so transferring
      a gate body between two assignments never needs selector-plane
      agreement — only the guard's own value, which both planes read as [1]
      at an enabled point. *)

  Definition body_selector_free
      (named_constraint : option string * Constraint.t columns) : bool :=
    match snd named_constraint with
    | Constraint.Select _ body =>
        match Agree.constraint_selector_queries body with
        | [] => true
        | _ :: _ => false
        end
    | _ => true
    end.

  Lemma orchard_bodies_selector_free :
    List.forallb
      (fun gate => List.forallb body_selector_free gate.(Gate.constraints))
      system.(ConstraintSystem.gates) = true.
  Proof. vm_cast_no_check (@eq_refl bool true). Qed.

  Lemma guarded_body_selector_free (gate : Gate.t columns)
      (name : option string) (sel : Selector.t)
      (body : Constraint.t columns) :
    List.In gate system.(ConstraintSystem.gates) ->
    List.In (name, Constraint.Select sel body) gate.(Gate.constraints) ->
    Agree.constraint_selector_queries body = [].
  Proof.
    intros Hgate Hbody.
    pose proof (proj1
      (List.forallb_forall body_selector_free gate.(Gate.constraints))
      (proj1
        (List.forallb_forall
          (fun gate => List.forallb body_selector_free gate.(Gate.constraints))
          system.(ConstraintSystem.gates))
        orchard_bodies_selector_free gate Hgate)
      (name, Constraint.Select sel body) Hbody) as Hfree.
    unfold body_selector_free in Hfree.
    cbn [snd] in Hfree.
    destruct (Agree.constraint_selector_queries body) as [| q qs];
      [reflexivity | discriminate Hfree].
  Qed.


  (** ** Certificate 8: the lookup arguments' selectors are alias-free at the
      enabled points

      A lookup argument's expressions read selector cells (the gating
      [q * expr + (1 - q) * default] shape), so transferring a lookup
      obligation between the honest and the realized assignment needs
      selector-plane agreement — which, unlike the gate-body case, is not
      vacuous.  The realized plane reads [1] at an absolute address as soon
      as *some* enabled point sits there ([orchard_enables_placed]), while
      the honest plane reads [1] only at the point's own region and offset.
      The certificate says the two coincide wherever a lookup argument looks:
      at every enabled point, for every selector one of the arguments
      mentioning that point's selector reads, an enabled point at the same
      absolute address is an enabled point at the same region and offset.

      The check is phrased over the precomputed constants [enabled] and
      [placed_enabled] rather than through [Complete.enabled_memb] /
      [Placed.placed_memb], whose [facts] argument would re-run the whole
      synthesis reification at every call. *)

  Definition relevant_selectors (sel : Selector.t) : list Selector.t :=
    List.flat_map
      (fun arg =>
        if Complete.arg_mentions_selector OrchardDecidableEq.selector_eqb
             sel arg
        then Agree.arg_selector_queries arg
        else [])
      system.(ConstraintSystem.lookups).

  Lemma relevant_selectors_In (sel sel' : Selector.t)
      (arg : LookupArgument.t columns) :
    List.In arg system.(ConstraintSystem.lookups) ->
    Complete.arg_mentions_selector OrchardDecidableEq.selector_eqb sel arg =
      true ->
    List.In sel' (Agree.arg_selector_queries arg) ->
    List.In sel' (relevant_selectors sel).
  Proof.
    intros Harg Hmention Hsel.
    apply List.in_flat_map.
    exists arg.
    split; [exact Harg |].
    rewrite Hmention.
    exact Hsel.
  Qed.

  Definition point_here (sel : Selector.t) (region : RegionId.t) (offset : Z)
      : bool :=
    List.existsb
      (fun point =>
        let '(sel', region', offset') := point in
        (OrchardDecidableEq.selector_eqb sel sel' &&
         OrchardDecidableEq.region_id_eqb region region' &&
         (offset =? offset'))%bool)
      enabled.

  Lemma point_here_In (sel : Selector.t) (region : RegionId.t) (offset : Z) :
    point_here sel region offset = true ->
    List.In (sel, region, offset) enabled.
  Proof.
    unfold point_here.
    intros Hhere.
    apply List.existsb_exists in Hhere.
    destruct Hhere as (point & Hin & Hmatch).
    destruct point as [ [sel' region'] offset'].
    apply andb_prop in Hmatch.
    destruct Hmatch as [Hmatch Hoffset].
    apply andb_prop in Hmatch.
    destruct Hmatch as [Hsel Hregion].
    apply (proj1 (OrchardDecidableEq.selector_eqb_eq _ _)) in Hsel.
    apply (proj1 (OrchardDecidableEq.region_id_eqb_eq _ _)) in Hregion.
    apply Z.eqb_eq in Hoffset.
    subst.
    exact Hin.
  Qed.

  Definition point_placed (sel : Selector.t) (row : Z) : bool :=
    List.existsb
      (fun address =>
        ((Index.selector sel =? fst address) && (row =? snd address))%bool)
      placed_enabled.

  Lemma point_placed_complete (sel : Selector.t) (region : RegionId.t)
      (offset : Z) :
    List.In (sel, region, offset) enabled ->
    point_placed sel (region_start_of region + offset) = true.
  Proof.
    intros Hin.
    unfold point_placed.
    apply List.existsb_exists.
    exists (Index.selector sel, region_start_of region + offset).
    split.
    - unfold placed_enabled.
      apply (List.in_map
        (fun point =>
          let '(sel', region', offset') := point in
          (Index.selector sel', region_start_of region' + offset'))
        enabled (sel, region, offset) Hin).
    - cbn [fst snd].
      rewrite !Z.eqb_refl.
      reflexivity.
  Qed.

  Lemma point_placed_false (sel : Selector.t) (row : Z) :
    point_placed sel row = false ->
    forall (sel' : Selector.t) (region' : RegionId.t) (offset' : Z),
      List.In (sel', region', offset') enabled ->
      Index.selector sel' <> Index.selector sel \/
      region_start_of region' + offset' <> row.
  Proof.
    intros Hplaced sel' region' offset' Hin.
    destruct (Index.selector sel' =? Index.selector sel) eqn:Hsel.
    - right.
      intros Hrow.
      enough (Htrue : point_placed sel row = true) by congruence.
      unfold point_placed.
      apply List.existsb_exists.
      exists (Index.selector sel', region_start_of region' + offset').
      split.
      + unfold placed_enabled.
        apply (List.in_map
          (fun point =>
            let '(sel'', region'', offset'') := point in
            (Index.selector sel'', region_start_of region'' + offset''))
          enabled (sel', region', offset') Hin).
      + cbn [fst snd].
        apply Z.eqb_eq in Hsel.
        rewrite Hsel, Hrow, !Z.eqb_refl.
        reflexivity.
    - left.
      intros Heq.
      rewrite Heq, Z.eqb_refl in Hsel.
      discriminate Hsel.
  Qed.

  Definition selector_alias_ok (point : Selector.t * RegionId.t * Z) : bool :=
    let '(sel, region, offset) := point in
    List.forallb
      (fun sel' =>
        implb (point_placed sel' (region_start_of region + offset))
          (point_here sel' region offset))
      (relevant_selectors sel).

  Lemma orchard_lookup_selectors_alias_free :
    List.forallb selector_alias_ok enabled = true.
  Proof. vm_cast_no_check (@eq_refl bool true). Qed.

  Lemma lookup_selector_here (sel0 : Selector.t) (region : RegionId.t)
      (offset : Z) (sel : Selector.t) :
    List.In (sel0, region, offset) enabled ->
    List.In sel (relevant_selectors sel0) ->
    point_placed sel (region_start_of region + offset) = true ->
    List.In (sel, region, offset) enabled.
  Proof.
    intros Hpoint Hrel Hplaced.
    pose proof (proj1
      (List.forallb_forall selector_alias_ok enabled)
      orchard_lookup_selectors_alias_free (sel0, region, offset) Hpoint)
      as Hok.
    cbv beta iota in Hok.
    pose proof (proj1
      (List.forallb_forall
        (fun sel' =>
          implb (point_placed sel' (region_start_of region + offset))
            (point_here sel' region offset))
        (relevant_selectors sel0))
      Hok sel Hrel) as Himpl.
    cbv beta in Himpl.
    rewrite Hplaced in Himpl.
    cbn [implb] in Himpl.
    exact (point_here_In sel region offset Himpl).
  Qed.

  (** ** Certificate 4: the constants tail is covered by the witness facts *)

  Definition constant_covered
      (binding : Garden.Orchard.circuit_synthesis_constants.ConstantCopy.t)
      : bool :=
    List.existsb
      (fun fact =>
        match fact with
        | Fact.CellIsConstant cell value =>
            (raw_cell_eqb
              (Cell.to_raw Index.indices region_start_of cell)
              (Garden.Orchard.circuit_synthesis_constants.advice_cell
                binding.(Garden.Orchard.circuit_synthesis_constants
                  .ConstantCopy.advice_column)
                binding.(Garden.Orchard.circuit_synthesis_constants
                  .ConstantCopy.advice_row)) &&
            (value =?
              binding.(Garden.Orchard.circuit_synthesis_constants
                .ConstantCopy.value)))%bool
        | _ => false
        end)
      (Complete.witness_facts facts).

  Lemma orchard_constants_reverse :
    List.forallb constant_covered
      Garden.Orchard.circuit_synthesis_constants.constant_copies = true.
  Proof. vm_cast_no_check (@eq_refl bool true). Qed.

  Lemma constant_covered_fact
      (binding : Garden.Orchard.circuit_synthesis_constants.ConstantCopy.t) :
    List.In binding
      Garden.Orchard.circuit_synthesis_constants.constant_copies ->
    exists cell : Garden.Halo2.Synthesis.Cell.t columns RegionId.t,
      List.In
        (Fact.CellIsConstant cell
          binding.(Garden.Orchard.circuit_synthesis_constants
            .ConstantCopy.value))
        (Complete.witness_facts facts) /\
      Cell.to_raw Index.indices region_start_of cell =
        Garden.Orchard.circuit_synthesis_constants.advice_cell
          binding.(Garden.Orchard.circuit_synthesis_constants
            .ConstantCopy.advice_column)
          binding.(Garden.Orchard.circuit_synthesis_constants
            .ConstantCopy.advice_row).
  Proof.
    intros Hin.
    pose proof (proj1
      (List.forallb_forall constant_covered
        Garden.Orchard.circuit_synthesis_constants.constant_copies)
      orchard_constants_reverse binding Hin) as Hcovered.
    unfold constant_covered in Hcovered.
    apply List.existsb_exists in Hcovered.
    destruct Hcovered as (fact & Hfact & Hmatch).
    destruct fact as [ | | | | | cell value]; try discriminate Hmatch.
    apply andb_prop in Hmatch.
    destruct Hmatch as [Hcell Hvalue].
    apply raw_cell_eqb_eq in Hcell.
    apply Z.eqb_eq in Hvalue.
    subst value.
    exists cell.
    split; [exact Hfact | exact Hcell].
  Qed.

  (** ** Certificate 5: the three loaded lookup columns hold 1024 rows

      [Fact.LookupTableLoaded] pins only the rows [[0, length values)], and
      the mock checker reads the table only below [layouter_table_rows =
      1024]; this certificate says the two ranges coincide, so the honest
      lookup plane and the replayed grid agree exactly where the lookup
      arguments look.  Past [length values] the table column is no longer
      program-determined — the keygen-faithful fill stops at
      [orchard_usable_rows] — and nothing below reads it. *)

  Definition table_rows_ok (column : Lookup.t) : bool :=
    match
      Complete.table_lookup OrchardDecidableEq.lookup_eqb
        (Complete.table_entries facts) column
    with
    | Some (values, _) => Z.of_nat (List.length values) =? 1024
    | None => false
    end.

  Lemma orchard_table_rows_certificate :
    List.forallb table_rows_ok [Lookup.TableIdx; Lookup.TableX; Lookup.TableY]
      = true.
  Proof. vm_cast_no_check (@eq_refl bool true). Qed.

  Lemma table_lookup_In
      (entries : list (Lookup.t * list Z * Z)) (column : Lookup.t)
      (values : list Z) (default_value : Z) :
    Complete.table_lookup OrchardDecidableEq.lookup_eqb entries column =
      Some (values, default_value) ->
    List.In (column, values, default_value) entries.
  Proof.
    induction entries as [| entry entries IH];
      cbn [Complete.table_lookup]; [discriminate |].
    destruct entry as [ [column' values'] default'].
    destruct (OrchardDecidableEq.lookup_eqb column column') eqn:Hmatch.
    - intros Heq.
      injection Heq as <- <-.
      left.
      apply (proj1 (OrchardDecidableEq.lookup_eqb_eq _ _)) in Hmatch.
      congruence.
    - intros Hlookup.
      right.
      exact (IH Hlookup).
  Qed.

  Lemma table_entries_fact (fs : list (Fact.t columns RegionId.t))
      (column : Lookup.t) (values : list Z) (default_value : Z) :
    List.In (column, values, default_value) (Complete.table_entries fs) ->
    List.In (Fact.LookupTableLoaded column values default_value) fs.
  Proof.
    induction fs as [| fact fs IH]; intros Hin; [contradiction |].
    destruct fact as
      [ ? ? ? | ? ? ? ? | ? ? | ? ? ? | column' values' default' | ? ? ];
      cbn [Complete.table_entries] in Hin;
      try (right; exact (IH Hin)).
    destruct Hin as [Heq | Hin].
    - injection Heq as Hcolumn Hvalues Hdefault.
      subst.
      left. reflexivity.
    - right. exact (IH Hin).
  Qed.

  (** Each of the three lookup columns is loaded by a synthesis fact whose
      content is the 1024-row table the honest lookup plane reads. *)
  Lemma table_loaded (column : Lookup.t) :
    exists (values : list Z) (default_value : Z),
      Complete.table_lookup OrchardDecidableEq.lookup_eqb
        (Complete.table_entries facts) column =
        Some (values, default_value) /\
      Z.of_nat (List.length values) = 1024 /\
      List.In (Fact.LookupTableLoaded column values default_value) facts.
  Proof.
    assert (Hcolumn : table_rows_ok column = true). {
      pose proof (proj1
        (List.forallb_forall table_rows_ok
          [Lookup.TableIdx; Lookup.TableX; Lookup.TableY])
        orchard_table_rows_certificate) as Hall.
      destruct column.
      - exact (Hall Lookup.TableIdx (or_introl eq_refl)).
      - exact (Hall Lookup.TableX (or_intror (or_introl eq_refl))).
      - exact (Hall Lookup.TableY
          (or_intror (or_intror (or_introl eq_refl)))). }
    revert Hcolumn.
    unfold table_rows_ok.
    destruct
      (Complete.table_lookup OrchardDecidableEq.lookup_eqb
        (Complete.table_entries facts) column)
      as [ [values default_value] |] eqn:Hlookup; [| discriminate].
    intros Hlength.
    apply Z.eqb_eq in Hlength.
    exists values, default_value.
    split; [reflexivity |].
    split; [exact Hlength |].
    exact (table_entries_fact facts column values default_value
      (table_lookup_In _ column values default_value Hlookup)).
  Qed.

  (** ** Certificate 6: the witness facts name no fixed cell

      [Fact.CellsEqual] / [Fact.InstanceIs] / [Fact.CellIsConstant] of the
      Orchard program address only advice and instance cells, so their
      transfer to the realized assignment needs the advice inversion and the
      instance plane alone. *)

  Definition cell_kind_ok
      (cell : Garden.Halo2.Synthesis.Cell.t columns RegionId.t) : bool :=
    match cell.(Garden.Halo2.Synthesis.Cell.column) with
    | Garden.Halo2.Synthesis.ColumnRef.Fixed _ => false
    | _ => true
    end.

  Definition fact_cells_ok (fact : Fact.t columns RegionId.t) : bool :=
    match fact with
    | Fact.CellsEqual left_cell right_cell =>
        (cell_kind_ok left_cell && cell_kind_ok right_cell)%bool
    | Fact.InstanceIs cell _ _ => cell_kind_ok cell
    | Fact.CellIsConstant cell _ => cell_kind_ok cell
    | _ => true
    end.

  Lemma orchard_witness_cells_ok :
    List.forallb fact_cells_ok (Complete.witness_facts facts) = true.
  Proof. vm_cast_no_check (@eq_refl bool true). Qed.

  Lemma witness_fact_cells_ok (fact : Fact.t columns RegionId.t) :
    List.In fact (Complete.witness_facts facts) ->
    fact_cells_ok fact = true.
  Proof.
    exact (proj1
      (List.forallb_forall fact_cells_ok (Complete.witness_facts facts))
      orchard_witness_cells_ok fact).
  Qed.

  (** ** The constants tail: reading a [Copy] event back to its binding *)

  Lemma to_event_list_copy
      (bindings :
        list Garden.Orchard.circuit_synthesis_constants.ConstantCopy.t)
      (left right : Raw.Cell.t) :
    List.In (Raw.Event.Copy left right)
      (Garden.Orchard.circuit_synthesis_constants.to_event_list bindings) ->
    exists binding,
      List.In binding bindings /\
      left = Garden.Orchard.circuit_synthesis_constants.fixed_cell
        binding.(Garden.Orchard.circuit_synthesis_constants
          .ConstantCopy.fixed_row) /\
      right = Garden.Orchard.circuit_synthesis_constants.advice_cell
        binding.(Garden.Orchard.circuit_synthesis_constants
          .ConstantCopy.advice_column)
        binding.(Garden.Orchard.circuit_synthesis_constants
          .ConstantCopy.advice_row).
  Proof.
    induction bindings as [| binding bindings IH]; intros Hin;
      [contradiction |].
    cbn [Garden.Orchard.circuit_synthesis_constants.to_event_list] in Hin.
    apply List.in_app_or in Hin.
    destruct Hin as [Hin | Hin].
    - unfold Garden.Orchard.circuit_synthesis_constants.to_events in Hin.
      destruct Hin as [Heq | Hin]; [discriminate Heq |].
      destruct Hin as [Heq | Hin]; [| contradiction].
      injection Heq as <- <-.
      exists binding.
      split; [left; reflexivity |].
      split; reflexivity.
    - destruct (IH Hin) as (binding' & Hbinding & Hleft & Hright).
      exists binding'.
      split; [right; exact Hbinding |].
      split; [exact Hleft | exact Hright].
  Qed.

  (** The [AssignFixed] companion of a binding, as an event of the tail. *)
  Lemma binding_assign_fixed
      (binding : Garden.Orchard.circuit_synthesis_constants.ConstantCopy.t) :
    List.In binding
      Garden.Orchard.circuit_synthesis_constants.constant_copies ->
    List.In
      (Raw.Event.AssignFixed 3
        binding.(Garden.Orchard.circuit_synthesis_constants
          .ConstantCopy.fixed_row)
        binding.(Garden.Orchard.circuit_synthesis_constants
          .ConstantCopy.annotation)
        binding.(Garden.Orchard.circuit_synthesis_constants
          .ConstantCopy.value))
      orchard_events.
  Proof.
    intros Hbinding.
    unfold orchard_events, orchard_constants_events,
      Garden.Orchard.circuit_synthesis_constants.events.
    apply List.in_or_app.
    right.
    apply (to_event_list_in binding
      Garden.Orchard.circuit_synthesis_constants.constant_copies _ Hbinding).
    unfold Garden.Orchard.circuit_synthesis_constants.to_events.
    left. reflexivity.
  Qed.

End OrchardPlacementCerts.
