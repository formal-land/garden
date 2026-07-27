(** * Generator-versus-replay agreement for operational completeness (E1)

    The input-dependent half of the grid-identification obligation.  The two
    free planes of the operational grid are chosen from the honest generator:

    - [orchard_advice w] is the pull-back of the honest advice plane along
      the placement, through the input-independent address map
      [OrchardPlacementCerts.advice_owner] certified in [certs.v];
    - [orchard_instance w] is the honest instance plane, which already
      ignores its column index (the circuit has one instance column).

    Replaying [orchard_events] onto those planes — always possible, by
    [orchard_replay_some], which holds for *any* planes — gives a grid whose
    realized assignment agrees with [honest_assignment w] at every cell the
    finite [Complete.circuit_holds_intro] obligations read:

    - the selector plane is [1] at every enabled point and [0] at every
      absolute address that is not an enabled point's — the placed
      replacement for [Complete.honest_selector_plane], which is *false* at a
      realized assignment because [region_start_of] is not row-injective;
    - the fixed plane agrees at every gate- or lookup-queried cell (all of
      them program-written, [certs.v] certificate 3), the lookup plane on the
      whole range [[0, 1024)] the lookup arguments read, the advice plane at
      every needed cell, and the instance plane everywhere;
    - the witness facts of the synthesis program transfer verbatim from the
      C2 lemma [OrchardForwardLookupsWitness.witness_facts_ok];
    - the copy obligations of the floor planner's constants tail hold of the
      replayed grid.

    Everything here is universal in the honest input.  The join then runs the
    placed re-derivation of [circuit_holds] at the realized assignment
    ([placed_intro.v], since [Complete.honest_planes] is false there) through
    the query-agreement congruences and row shift of
    [agreement_congruences.v], feeding the C2 per-point obligations
    ([forward/assembly.v] [gates_all] / [lookups_all]) at the enabled point.

    The agreement is proved once, at any [replay_context] — any replayed
    stream carrying the synthesis events whose selector enables are among the
    full stream's — so one derivation serves both checked streams:

    - [orchard_grid_identification] / [orchard_grid_identification_synthesis]
      — the realized assignment of the replayed grid satisfies
      [circuit_holds], at the full stream and at the synthesis-only stream;
    - [orchard_operational_complete] — the E1 headline: the serialized
      Orchard circuit with its constants tail is accepted by the ideal
      [mock_prover_accepts] checker, via
      [operational_complete_events_app] ([replay_planes.v]) plus the tail's
      copy obligations;
    - [orchard_operational_complete_sound] — the same conclusion on the
      synthesis-only stream, obtained by applying [Halo2/realize/sound.v]'s
      [operational_complete] verbatim, every premise supplied.  The full
      stream is not a literal instance of that theorem: its replay premise
      names the synthesis stream at the *same* grid, while the Orchard
      honest grid replays [orchard_synthesis_events ++
      orchard_constants_events], whose 166 tail [AssignFixed] events change
      the fixed plane;
    - [orchard_operational_complete_ex] /
      [orchard_operational_complete_sound_ex] — the unconditional forms,
      since replay always succeeds ([orchard_replay_some] for the full
      stream, and the [conflict_free] prefix of that certificate for the
      synthesis-only stream). *)

Require Import Garden.Halo2.main.
Require Import Garden.Halo2.Synthesis.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.complete.
Require Import Garden.Halo2.serialize.
Require Import Garden.Halo2.realize.main.
Require Import Garden.Halo2.realize.facts.
Require Import Garden.Halo2.realize.sound.
Require Import Garden.Halo2.realize.disjoint.
Require Import Garden.Field.Field.
Require Import Garden.Plonky3.M.
Require Import Garden.Orchard.columns.
Require Import Garden.Orchard.decidable_eq.
Require Import Garden.Orchard.circuit_synthesis_layout.
Require Import Garden.Orchard.circuit_operational.
Require Garden.Orchard.circuit_synthesis_constants.
Require Import Garden.Orchard.circuit_completeness.generator.witness_input.
Require Import Garden.Orchard.circuit_completeness.generator.certificates.
Require Import Garden.Orchard.circuit_completeness.generator.tables.
Require Import Garden.Orchard.circuit_completeness.generator.honest_assignment.
Require Import Garden.Orchard.circuit_completeness.forward.api.
Require Import Garden.Orchard.circuit_completeness.forward.lookups_witness.
Require Import Garden.Orchard.circuit_completeness.forward.assembly.
Require Import Garden.Orchard.circuit_completeness.operational.certs.
Require Import Garden.Orchard.circuit_completeness.operational.replay_planes.
Require Import Garden.Orchard.circuit_completeness.operational.agreement_congruences.
Require Import Garden.Orchard.circuit_completeness.operational.placed_intro.
Require Garden.Orchard.circuit.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Lists.List.
Require Import Stdlib.micromega.Lia.

Import ListNotations.
Global Open Scope Z_scope.

#[local] Existing Instance Primes.PallasPIsPrime.

(** The generator's region-level derivations must never be normalized: every
    equation below is either a syntactic projection of the record or a
    rewrite by a hand lemma. *)
Strategy opaque [
  OrchardCompletenessTables.tables_of
  OrchardCompletenessTables.advice_t
  OrchardCompletenessTables.instance_t
].

Module OrchardOperationalAgreement.
  Import OrchardWitnessInput.

  (** ** The chosen free planes *)

  (** The honest advice plane, pulled back along the placement through the
      certified address map.  Outside the map's domain — the cells no
      obligation reads — the plane is [0]; nothing below looks there. *)
  Definition orchard_advice (w : HonestInput) : Z -> Z -> Z :=
    fun column row =>
      match OrchardPlacementCerts.advice_owner column row with
      | Some (column', region, offset) =>
          (OrchardHonestAssignment.honest_assignment w)
            .(Assignment.advice) column' region offset
      | None => 0
      end.

  (** The honest instance plane.  [honest_assignment]'s instance field
      already ignores its column argument (the circuit configures a single
      instance column), so no inversion is needed here. *)
  Definition orchard_instance (w : HonestInput) : Z -> Z -> Z :=
    fun _ row =>
      (OrchardHonestAssignment.honest_assignment w)
        .(Assignment.instance_) Instance_.Primary row.

  (** Replay of the whole stream onto those planes succeeds — the conflict
      check never reads the free planes. *)
  Lemma orchard_replay_planes (w : HonestInput) :
    exists grid : RawGrid.t,
      apply_events orchard_events
        (initial_grid (orchard_advice w) (orchard_instance w)) = Some grid.
  Proof.
    exact (orchard_replay_some (orchard_advice w) (orchard_instance w)).
  Qed.

  (** ** The replay context

      The agreement below is proved for *any* replayed stream that carries
      the synthesis events and whose selector enables are among the full
      stream's — which is what lets one derivation serve both the full
      Orchard stream (the E1 headline) and the synthesis-only stream (the
      literal instance of [Halo2/realize/sound.v]'s [operational_complete],
      whose replay premise names the synthesis stream alone).

      The two side conditions are placement data, never witness data:
      [Hsynthesis] feeds [determined_facts_hold_incl] and [Henables] feeds
      the [certs.v] enable-placement certificate. *)
  Definition replay_context (w : HonestInput) (g : RawGrid.t)
      (evts : list Raw.Event.t) : Prop :=
    apply_events evts
      (initial_grid (orchard_advice w) (orchard_instance w)) = Some g /\
    List.incl orchard_synthesis_events evts /\
    (forall (column row : Z) (annotation : string),
      List.In (Raw.Event.EnableSelector column row annotation) evts ->
      List.In (Raw.Event.EnableSelector column row annotation) orchard_events).

  (** The full stream is a replay context. *)
  Lemma replay_context_full (w : HonestInput) (g : RawGrid.t) :
    apply_events orchard_events
      (initial_grid (orchard_advice w) (orchard_instance w)) = Some g ->
    replay_context w g orchard_events.
  Proof.
    intros Hreplay.
    split; [exact Hreplay |].
    split.
    - unfold orchard_events.
      apply List.incl_appl, List.incl_refl.
    - intros column row annotation Hin. exact Hin.
  Qed.

  (** So is the synthesis-only stream: its enables are a sublist of the full
      stream's, since the full stream appends the constants tail. *)
  Lemma replay_context_synthesis (w : HonestInput) (g : RawGrid.t) :
    apply_events orchard_synthesis_events
      (initial_grid (orchard_advice w) (orchard_instance w)) = Some g ->
    replay_context w g orchard_synthesis_events.
  Proof.
    intros Hreplay.
    split; [exact Hreplay |].
    split.
    - apply List.incl_refl.
    - intros column row annotation Hin.
      unfold orchard_events.
      apply List.in_or_app.
      left. exact Hin.
  Qed.

  (** Replay of the synthesis-only stream also succeeds, with no new
      certificate: replay success is the grid-independent [conflict_free]
      verdict ([realize/disjoint.v]), and [conflict_free] of an append is the
      conjunction of its parts', so the full-stream certificate
      [orchard_replay_ok] already carries the prefix. *)
  (** Both steps are pure term composition.  A [rewrite] here is
      catastrophic: its occurrence search unifies the pattern against
      [replay_is_ok orchard_events _], whose arguments are the 19,617-event
      stream and the initial grid, and normalizes them on the lazy machine
      (measured 445 s for the single tactic). *)
  Lemma orchard_conflict_free : conflict_free orchard_events = true.
  Proof.
    exact (eq_trans
      (eq_sym (replay_is_ok_conflict_free orchard_events
        (initial_grid (fun _ _ : Z => 0) (fun _ _ : Z => 0))))
      (orchard_replay_ok (fun _ _ : Z => 0) (fun _ _ : Z => 0))).
  Qed.

  Lemma orchard_synthesis_conflict_free :
    conflict_free orchard_synthesis_events = true.
  Proof.
    exact (proj1 (proj1 (Bool.andb_true_iff _ _)
      (eq_trans
        (eq_sym (conflict_free_app orchard_synthesis_events
          orchard_constants_events))
        orchard_conflict_free))).
  Qed.

  Lemma orchard_synthesis_replay_planes (w : HonestInput) :
    exists grid : RawGrid.t,
      apply_events orchard_synthesis_events
        (initial_grid (orchard_advice w) (orchard_instance w)) = Some grid.
  Proof.
    exact (conflict_free_apply_events orchard_synthesis_events
      orchard_synthesis_conflict_free
      (initial_grid (orchard_advice w) (orchard_instance w))).
  Qed.

  (** ** Definitional cell readings

      Both assignments are records, so every plane read is one projection.
      Each equation is closed by [reflexivity] on a stuck projection: no
      generator derivation is ever unfolded. *)

  Lemma realize_selector_read (grid : RawGrid.t) (sel : Selector.t)
      (region : RegionId.t) (offset : Z) :
    (realize Index.indices region_start_of grid)
      .(Assignment.selector) sel region offset =
    grid.(RawGrid.sel) (Index.selector sel) (region_start_of region + offset).
  Proof. reflexivity. Qed.

  Lemma realize_advice_read (grid : RawGrid.t) (column : Advice.t)
      (region : RegionId.t) (offset : Z) :
    (realize Index.indices region_start_of grid)
      .(Assignment.advice) column region offset =
    grid.(RawGrid.cell) Raw.ColumnKind.Advice (Index.advice column)
      (region_start_of region + offset).
  Proof. reflexivity. Qed.

  Lemma realize_instance_read (grid : RawGrid.t) (column : Instance_.t)
      (row : Z) :
    (realize Index.indices region_start_of grid)
      .(Assignment.instance_) column row =
    grid.(RawGrid.cell) Raw.ColumnKind.Instance_ (Index.instance_ column) row.
  Proof. reflexivity. Qed.

  Lemma initial_advice_read (advice instance_ : Z -> Z -> Z)
      (column row : Z) :
    (initial_grid advice instance_).(RawGrid.cell) Raw.ColumnKind.Advice
      column row = advice column row.
  Proof. reflexivity. Qed.

  Lemma initial_instance_read (advice instance_ : Z -> Z -> Z)
      (column row : Z) :
    (initial_grid advice instance_).(RawGrid.cell) Raw.ColumnKind.Instance_
      column row = instance_ column row.
  Proof. reflexivity. Qed.

  Lemma initial_selector_read (advice instance_ : Z -> Z -> Z)
      (column row : Z) :
    (initial_grid advice instance_).(RawGrid.sel) column row = 0.
  Proof. reflexivity. Qed.

  Lemma honest_selector_read (w : HonestInput) (sel : Selector.t)
      (region : RegionId.t) (offset : Z) :
    (OrchardHonestAssignment.honest_assignment w)
      .(Assignment.selector) sel region offset =
    (if Complete.enabled_memb OrchardDecidableEq.selector_eqb
          OrchardDecidableEq.region_id_eqb OrchardPlacementCerts.facts
          sel region offset
     then 1 else 0).
  Proof. reflexivity. Qed.

  Lemma honest_fixed_read (w : HonestInput) (column : Fixed.t)
      (region : RegionId.t) (offset : Z) :
    (OrchardHonestAssignment.honest_assignment w)
      .(Assignment.fixed) column region offset =
    Complete.fixed_write_or_zero OrchardDecidableEq.fixed_eqb
      OrchardDecidableEq.region_id_eqb OrchardPlacementCerts.facts
      column region offset.
  Proof. reflexivity. Qed.

  Lemma honest_lookup_read (w : HonestInput) (column : Lookup.t) (row : Z) :
    (OrchardHonestAssignment.honest_assignment w).(Assignment.lookup)
      column row =
    Complete.table_value OrchardDecidableEq.lookup_eqb
      OrchardPlacementCerts.facts column row.
  Proof. reflexivity. Qed.

  (** The instance plane ignores its column: [Instance_.t] is a singleton. *)
  Lemma honest_instance_column (w : HonestInput) (column : Instance_.t)
      (row : Z) :
    (OrchardHonestAssignment.honest_assignment w)
      .(Assignment.instance_) column row =
    (OrchardHonestAssignment.honest_assignment w)
      .(Assignment.instance_) Instance_.Primary row.
  Proof. destruct column. reflexivity. Qed.

  (** The column indexing is injective on selectors: the placed hypotheses
      are stated at absolute selector indexes, the enabled points at typed
      selectors. *)
  Lemma index_selector_injective (sel1 sel2 : Selector.t) :
    Index.selector sel1 = Index.selector sel2 -> sel1 = sel2.
  Proof.
    destruct sel1; destruct sel2; intros Heq;
      first [ reflexivity | discriminate Heq ].
  Qed.

  (** ** The agreement, at a replayed grid *)

  Section Replayed.
    Context (w : HonestInput) (g : RawGrid.t) (evts : list Raw.Event.t).
    Hypothesis Hstream : replay_context w g evts.

    Notation Γop := (realize Index.indices region_start_of g).
    Notation Γhonest := (OrchardHonestAssignment.honest_assignment w).

    Let Hreplay :
      apply_events evts
        (initial_grid (orchard_advice w) (orchard_instance w)) = Some g :=
      proj1 Hstream.
    Let Hsynthesis : List.incl orchard_synthesis_events evts :=
      proj1 (proj2 Hstream).
    Let Henables :
      forall (column row : Z) (annotation : string),
        List.In (Raw.Event.EnableSelector column row annotation) evts ->
        List.In (Raw.Event.EnableSelector column row annotation)
          orchard_events :=
      proj2 (proj2 Hstream).

    (** The program-determined facts hold of the realized assignment, from
        replay success alone: this is the half the soundness direction
        already carries. *)
    Lemma determined_holds :
      interpret_facts Γop (determined_facts OrchardPlacementCerts.facts).
    Proof.
      unfold OrchardPlacementCerts.facts, OrchardCompletenessCertificates.facts.
      apply (determined_facts_hold_incl Index.indices region_start_of
        Garden.Orchard.circuit.orchard_usable_rows
        Garden.Orchard.circuit.synthesize evts
        (initial_grid (orchard_advice w) (orchard_instance w)) g Hreplay).
      exact Hsynthesis.
    Qed.

    Lemma determined_fact_holds (fact : Fact.t columns RegionId.t) :
      List.In fact OrchardPlacementCerts.facts ->
      fact_is_determined fact = true ->
      interpret_fact Γop fact.
    Proof.
      intros Hin Hdet.
      exact (interpret_facts_In Γop fact _ determined_holds
        (proj2 (List.filter_In fact_is_determined fact
          OrchardPlacementCerts.facts) (conj Hin Hdet))).
    Qed.

    (** *** The selector plane *)

    (** At an enabled point both planes read [1]. *)
    Lemma selector_agree_on (sel : Selector.t) (region : RegionId.t)
        (row : Z) :
      List.In (sel, region, row) OrchardPlacementCerts.enabled ->
      Γop.(Assignment.selector) sel region row = 1 /\
      Γhonest.(Assignment.selector) sel region row = 1.
    Proof.
      intros Hin.
      pose proof (OrchardCompletenessCertificates.enabled_points_sound
        OrchardPlacementCerts.facts sel region row Hin) as Hfact.
      split.
      - exact (determined_fact_holds (Fact.SelectorOn sel region row)
          Hfact eq_refl).
      - rewrite honest_selector_read.
        rewrite (Complete.enabled_memb_complete
          OrchardDecidableEq.selector_eqb OrchardDecidableEq.selector_eqb_eq
          OrchardDecidableEq.region_id_eqb
          OrchardDecidableEq.region_id_eqb_eq
          OrchardPlacementCerts.facts sel region row Hin).
        reflexivity.
    Qed.

    (** Off the enabled points the realized selector plane is [0].  The
        hypothesis is the *placed* one: no enabled point shares the absolute
        address, which is strictly stronger than
        [Complete.enabled_memb _ _ _ sel region row = false] because
        [region_start_of] is not row-injective. *)
    Lemma placed_selector_off (sel : Selector.t) (region : RegionId.t)
        (row : Z) :
      (forall (sel' : Selector.t) (region' : RegionId.t) (offset' : Z),
        List.In (sel', region', offset') OrchardPlacementCerts.enabled ->
        Index.selector sel' <> Index.selector sel \/
        region_start_of region' + offset' <> region_start_of region + row) ->
      Γop.(Assignment.selector) sel region row = 0.
    Proof.
      intros Hoff.
      rewrite realize_selector_read.
      rewrite (OrchardPlacementCerts.replay_selector_unwritten evts
        (initial_grid (orchard_advice w) (orchard_instance w)) g
        (Index.selector sel) (region_start_of region + row) Hreplay).
      - apply initial_selector_read.
      - intros annotation Hin.
        destruct (OrchardPlacementCerts.enable_event_point
          (Index.selector sel) (region_start_of region + row) annotation
          (Henables _ _ annotation Hin))
          as (sel' & region' & offset' & Hpoint & Hselector & Hrow).
        destruct (Hoff sel' region' offset' Hpoint) as [Hne | Hne];
          [exact (Hne Hselector) | exact (Hne Hrow)].
    Qed.

    (** *** The fixed plane *)

    Lemma fixed_agree (column : Fixed.t) (region : RegionId.t) (offset : Z) :
      OrchardPlacementCerts.fixed_written (column, region, offset) = true ->
      Γop.(Assignment.fixed) column region offset =
      Γhonest.(Assignment.fixed) column region offset.
    Proof.
      intros Hwritten.
      destruct (OrchardPlacementCerts.fixed_written_fact column region offset
        Hwritten) as (value & Hfact & Hzero).
      rewrite (determined_fact_holds (Fact.FixedIs column region offset value)
        Hfact eq_refl).
      rewrite honest_fixed_read.
      symmetry.
      exact Hzero.
    Qed.

    (** *** The lookup plane

        The loaded table pins exactly the rows [[0, 1024)]
        ([Fact.LookupTableLoaded] under the keygen-faithful fill), and the
        mock checker reads no other row ([layouter_table_rows = 1024]). *)
    Lemma lookup_agree (column : Lookup.t) (row : Z) :
      0 <= row < 1024 ->
      Γop.(Assignment.lookup) column row =
      Γhonest.(Assignment.lookup) column row.
    Proof.
      intros Hrow.
      destruct (OrchardPlacementCerts.table_loaded column)
        as (values & default_value & Hlookup & Hlength & Hfact).
      pose proof (determined_fact_holds
        (Fact.LookupTableLoaded column values default_value) Hfact eq_refl)
        as Hpin.
      cbn [interpret_fact] in Hpin.
      rewrite (Hpin row ltac:(rewrite Hlength; exact Hrow)).
      rewrite honest_lookup_read.
      unfold Complete.table_value.
      rewrite Hlookup.
      reflexivity.
    Qed.

    (** *** The advice plane

        Definitional at every needed cell: the free plane was chosen as the
        pull-back, and the address map inverts the placement there. *)
    Lemma advice_agree (column : Advice.t) (region : RegionId.t)
        (offset : Z) :
      List.In (column, region, offset) OrchardPlacementCerts.needed_cells ->
      Γop.(Assignment.advice) column region offset =
      Γhonest.(Assignment.advice) column region offset.
    Proof.
      intros Hin.
      rewrite realize_advice_read.
      rewrite (OrchardPlacementCerts.replay_advice_plane evts
        (initial_grid (orchard_advice w) (orchard_instance w)) g
        (Index.advice column) (region_start_of region + offset) Hreplay).
      rewrite initial_advice_read.
      unfold orchard_advice.
      rewrite (OrchardPlacementCerts.advice_owner_needed column region offset
        Hin).
      reflexivity.
    Qed.

    (** *** The instance plane

        Total agreement: [Cell.to_raw] and [realize] both address instance
        cells by the absolute row, and the honest plane ignores its column. *)
    Lemma instance_agree (column : Instance_.t) (row : Z) :
      Γop.(Assignment.instance_) column row =
      Γhonest.(Assignment.instance_) column row.
    Proof.
      rewrite realize_instance_read.
      rewrite (OrchardPlacementCerts.replay_instance_plane evts
        (initial_grid (orchard_advice w) (orchard_instance w)) g
        (Index.instance_ column) row Hreplay).
      rewrite initial_instance_read.
      rewrite (honest_instance_column w column row).
      reflexivity.
    Qed.

    (** *** Cells named by the witness facts *)

    Lemma eval_cell_agree
        (cell : Garden.Halo2.Synthesis.Cell.t columns RegionId.t) :
      OrchardPlacementCerts.cell_kind_ok cell = true ->
      (forall column : Advice.t,
        cell.(Garden.Halo2.Synthesis.Cell.column) =
          Garden.Halo2.Synthesis.ColumnRef.Advice column ->
        List.In (column, cell.(Garden.Halo2.Synthesis.Cell.region),
          cell.(Garden.Halo2.Synthesis.Cell.row_offset))
          OrchardPlacementCerts.needed_cells) ->
      eval_cell Γop cell = eval_cell Γhonest cell.
    Proof.
      destruct cell as [column region offset].
      destruct column as [column | column | column];
        cbn [OrchardPlacementCerts.cell_kind_ok eval_cell
          Garden.Halo2.Synthesis.Cell.column
          Garden.Halo2.Synthesis.Cell.region
          Garden.Halo2.Synthesis.Cell.row_offset];
        intros Hkind Hneeded.
      - exact (advice_agree column region offset (Hneeded column eq_refl)).
      - discriminate Hkind.
      - exact (instance_agree column offset).
    Qed.

    (** A witness fact's cells are always advice or instance cells
        ([certs.v] certificate 6), and its advice cells are needed cells. *)
    Lemma witness_cell_agree (fact : Fact.t columns RegionId.t)
        (cell : Garden.Halo2.Synthesis.Cell.t columns RegionId.t) :
      List.In fact (Complete.witness_facts OrchardPlacementCerts.facts) ->
      OrchardPlacementCerts.cell_kind_ok cell = true ->
      List.incl (OrchardPlacementCerts.cell_advice cell)
        (OrchardPlacementCerts.fact_advice_cells fact) ->
      eval_cell Γop cell = eval_cell Γhonest cell.
    Proof.
      intros Hfact Hkind Hincl.
      apply (eval_cell_agree cell Hkind).
      intros column Hcolumn.
      apply OrchardPlacementCerts.needed_cells_witness.
      apply (OrchardPlacementCerts.witness_advice_cells_In fact _ Hfact).
      apply Hincl.
      unfold OrchardPlacementCerts.cell_advice.
      rewrite Hcolumn.
      left. reflexivity.
    Qed.

    (** The whole witness-fact package transfers from the C2 lemma. *)
    Lemma witness_facts_transfer :
      interpret_facts Γhonest
        (Complete.witness_facts OrchardPlacementCerts.facts) ->
      interpret_facts Γop
        (Complete.witness_facts OrchardPlacementCerts.facts).
    Proof.
      intros Hhonest.
      apply interpret_facts_of_in.
      intros fact Hfact.
      pose proof (interpret_facts_In Γhonest fact _ Hhonest Hfact) as Hfact_honest.
      pose proof (OrchardPlacementCerts.witness_fact_cells_ok fact Hfact)
        as Hcells.
      assert (Hwit : Complete.is_witness_fact fact = true).
      { exact (proj2 (proj1
          (List.filter_In Complete.is_witness_fact fact
            OrchardPlacementCerts.facts) Hfact)). }
      destruct fact as
        [ ? ? ? | ? ? ? ? | left_cell right_cell | cell instance row
        | ? ? ? | cell value ];
        cbn [Complete.is_witness_fact] in Hwit;
        try discriminate Hwit;
        cbn [OrchardPlacementCerts.fact_cells_ok] in Hcells;
        cbn [interpret_fact] in Hfact_honest |- *.
      - (* CellsEqual *)
        apply andb_prop in Hcells.
        destruct Hcells as [Hleft Hright].
        rewrite (witness_cell_agree _ left_cell Hfact Hleft
          (List.incl_appl _ (List.incl_refl _))).
        rewrite (witness_cell_agree _ right_cell Hfact Hright
          (List.incl_appr _ (List.incl_refl _))).
        exact Hfact_honest.
      - (* InstanceIs *)
        rewrite (witness_cell_agree _ cell Hfact Hcells
          (List.incl_refl _)).
        rewrite (instance_agree instance row).
        exact Hfact_honest.
      - (* CellIsConstant *)
        rewrite (witness_cell_agree _ cell Hfact Hcells
          (List.incl_refl _)).
        exact Hfact_honest.
    Qed.

    (** *** The copy obligations of the constants tail

        The tail's [Copy] events link a constants-column fixed cell — pinned
        by the accompanying [AssignFixed] — to the advice cell of a
        [Fact.CellIsConstant] obligation ([certs.v] certificate 4), which the
        honest generator satisfies. *)
    Lemma constants_copies_hold
        (Hconstants : List.incl orchard_events evts)
        (Hwitness : interpret_facts Γhonest
          (Complete.witness_facts OrchardPlacementCerts.facts))
        (left right : Raw.Cell.t) :
      List.In (Raw.Event.Copy left right) orchard_constants_events ->
      raw_cell_read g left = raw_cell_read g right.
    Proof.
      intros Hin.
      destruct (OrchardPlacementCerts.to_event_list_copy
        Garden.Orchard.circuit_synthesis_constants.constant_copies
        left right Hin) as (binding & Hbinding & Hleft & Hright).
      subst left right.
      (* The left cell holds the binding's value, by the [AssignFixed]. *)
      assert (Hfixed :
        raw_cell_read g
          (Garden.Orchard.circuit_synthesis_constants.fixed_cell
            binding.(Garden.Orchard.circuit_synthesis_constants
              .ConstantCopy.fixed_row)) =
        binding.(Garden.Orchard.circuit_synthesis_constants
          .ConstantCopy.value)). {
        exact (replay_fixed_pinned evts _ g _ _ _ _ Hreplay
          (Hconstants _
            (OrchardPlacementCerts.binding_assign_fixed binding Hbinding))). }
      rewrite Hfixed.
      (* The right cell is the advice cell of a [CellIsConstant] fact. *)
      destruct (OrchardPlacementCerts.constant_covered_fact binding Hbinding)
        as (cell & Hfact & Hraw).
      pose proof (interpret_facts_In Γhonest _ _ Hwitness Hfact) as Hconstant.
      cbn [interpret_fact] in Hconstant.
      pose proof (OrchardPlacementCerts.witness_fact_cells_ok _ Hfact)
        as Hkind.
      cbn [OrchardPlacementCerts.fact_cells_ok] in Hkind.
      rewrite <- Hconstant.
      rewrite <- (witness_cell_agree _ cell Hfact Hkind (List.incl_refl _)).
      rewrite <- Hraw.
      rewrite (realize_eval_cell Index.indices region_start_of g cell).
      reflexivity.
    Qed.

    (** ** The placed hypotheses of [Placed.placed_circuit_holds_intro] *)

    (** The selector-off hypothesis in the boolean form the placed
        introduction lemma consumes. *)
    Lemma placed_selector_off_orchard :
      Placed.placed_selector_off OrchardDecidableEq.selector_eqb Γop
        Index.indices region_start_of OrchardPlacementCerts.facts.
    Proof.
      apply (proj2 (Placed.placed_selector_off_memb
        OrchardDecidableEq.selector_eqb Γop Index.indices region_start_of
        OrchardPlacementCerts.facts)).
      intros sel region row Hmemb.
      apply placed_selector_off.
      intros sel' region' offset' Hpoint.
      destruct (OrchardDecidableEq.selector_eqb sel sel') eqn:Hsel.
      - right.
        intros Hrow.
        apply (proj1 (OrchardDecidableEq.selector_eqb_eq sel sel')) in Hsel.
        subst sel'.
        rewrite (Placed.placed_memb_complete OrchardDecidableEq.selector_eqb
          OrchardDecidableEq.selector_eqb_eq region_start_of
          OrchardPlacementCerts.facts sel region row region' offset'
          Hpoint Hrow) in Hmemb.
        discriminate Hmemb.
      - left.
        intros Heq.
        apply index_selector_injective in Heq.
        subst sel'.
        rewrite (proj2 (OrchardDecidableEq.selector_eqb_eq sel sel) eq_refl)
          in Hsel.
        discriminate Hsel.
    Qed.

    (** The table-row-[0] equation: the special case of [lookup_agree]. *)
    Lemma placed_lookup_zero (column : Lookup.t) :
      Γop.(Assignment.lookup) column 0 =
      Complete.table_value OrchardDecidableEq.lookup_eqb
        OrchardPlacementCerts.facts column 0.
    Proof.
      rewrite (lookup_agree column 0 ltac:(lia)).
      exact (honest_lookup_read w column 0).
    Qed.

    (** ** Transfer of a guarded gate body

        A gate body's query lists are covered by the certified cell
        inventories, so the two assignments agree on everything the body
        reads at the enabled point; the guard selector itself never occurs in
        the body ([certs.v] certificate 7). *)
    Lemma gate_constraint_agree (sel : Selector.t) (region' : RegionId.t)
        (offset' : Z) (gate : Gate.t columns) (name : option string)
        (body : Constraint.t columns) :
      List.In (sel, region', offset') OrchardPlacementCerts.enabled ->
      List.In gate
        OrchardPlacementCerts.system.(ConstraintSystem.gates) ->
      List.In (name, Constraint.Select sel body) gate.(Gate.constraints) ->
      Agree.constraint_agree Γhonest Γop region' offset' body.
    Proof.
      intros Hpoint Hgate Hbody.
      split. {
        unfold Agree.selector_agree.
        rewrite (OrchardPlacementCerts.guarded_body_selector_free gate name
          sel body Hgate Hbody).
        exact (List.Forall_nil _). }
      split. {
        unfold Agree.fixed_agree.
        apply List.Forall_forall.
        intros query Hquery.
        destruct query as [column rotation].
        cbn [fst snd].
        symmetry.
        apply fixed_agree.
        apply (proj1
          (List.forallb_forall OrchardPlacementCerts.fixed_written
            OrchardPlacementCerts.gate_fixed_cells)
          OrchardPlacementCerts.orchard_gate_fixed_written).
        apply (OrchardPlacementCerts.point_cells_In
          OrchardPlacementCerts.gate_fixed_queries sel region' offset'
          column rotation Hpoint).
        apply List.in_flat_map.
        exists body.
        split;
          [ exact (OrchardPlacementCerts.guarded_bodies_In sel gate name body
              Hgate Hbody)
          | exact Hquery ]. }
      split. {
        unfold Agree.advice_agree.
        apply List.Forall_forall.
        intros query Hquery.
        destruct query as [column rotation].
        cbn [fst snd].
        symmetry.
        apply advice_agree.
        apply OrchardPlacementCerts.needed_cells_gate.
        apply (OrchardPlacementCerts.point_cells_In
          OrchardPlacementCerts.gate_advice_queries sel region' offset'
          column rotation Hpoint).
        apply List.in_flat_map.
        exists body.
        split;
          [ exact (OrchardPlacementCerts.guarded_bodies_In sel gate name body
              Hgate Hbody)
          | exact Hquery ]. }
      unfold Agree.instance_agree.
      apply List.Forall_forall.
      intros query _.
      symmetry.
      exact (instance_agree (fst query) (offset' + snd query)).
    Qed.

    (** The placed gate obligation: the honest per-point obligation of the C2
        forward API discharges the realized one at every index sharing the
        point's absolute row. *)
    Lemma gates_placed
        (Hhonest : forall (sel : Selector.t) (region : RegionId.t) (row : Z),
          List.In (sel, region, row) OrchardPlacementCerts.enabled ->
          forall gate,
            List.In gate
              OrchardPlacementCerts.system.(ConstraintSystem.gates) ->
            forall name body,
              List.In (name, Constraint.Select sel body)
                gate.(Gate.constraints) ->
              eval_constraint Γhonest (region, row) body) :
      forall (sel : Selector.t) (region : RegionId.t) (row : Z)
        (region' : RegionId.t) (offset' : Z),
        List.In (sel, region', offset')
          (Complete.enabled_points OrchardPlacementCerts.facts) ->
        region_start_of region' + offset' = region_start_of region + row ->
        forall gate,
          List.In gate
            OrchardPlacementCerts.system.(ConstraintSystem.gates) ->
          forall name body,
            List.In (name, Constraint.Select sel body)
              gate.(Gate.constraints) ->
            eval_constraint Γop (region, row) body.
    Proof.
      intros sel region row region' offset' Hpoint Hrow gate Hgate name body
        Hbody.
      apply (Agree.realize_constraint_transfer Index.indices region_start_of g
        Γhonest region row region' offset' body).
      - exact (system_gate_constraint_instance_free OrchardPlacementCerts.system
          gate name (Constraint.Select sel body) orchard_instance_free Hgate
          Hbody).
      - exact (eq_sym Hrow).
      - exact (gate_constraint_agree sel region' offset' gate name body Hpoint
          Hgate Hbody).
      - exact (Hhonest sel region' offset' Hpoint gate Hgate name body Hbody).
    Qed.

    (** *** Transfer of a lookup argument

        Unlike a gate body, a lookup argument's expressions read the selector
        plane; [certs.v] certificate 8 says the two planes agree on exactly
        those selectors at the enabled points. *)

    Lemma selector_agree_relevant (sel0 : Selector.t) (region' : RegionId.t)
        (offset' : Z) (sel : Selector.t) :
      List.In (sel0, region', offset') OrchardPlacementCerts.enabled ->
      List.In sel (OrchardPlacementCerts.relevant_selectors sel0) ->
      Γhonest.(Assignment.selector) sel region' offset' =
      Γop.(Assignment.selector) sel region' offset'.
    Proof.
      intros Hpoint Hrel.
      destruct (OrchardPlacementCerts.point_placed sel
        (region_start_of region' + offset')) eqn:Hplaced.
      - destruct (selector_agree_on sel region' offset'
          (OrchardPlacementCerts.lookup_selector_here sel0 region' offset' sel
            Hpoint Hrel Hplaced)) as [Hop Hho].
        rewrite Hop, Hho.
        reflexivity.
      - rewrite (placed_selector_off sel region' offset'
          (OrchardPlacementCerts.point_placed_false sel
            (region_start_of region' + offset') Hplaced)).
        rewrite honest_selector_read.
        destruct (Complete.enabled_memb OrchardDecidableEq.selector_eqb
          OrchardDecidableEq.region_id_eqb OrchardPlacementCerts.facts
          sel region' offset') eqn:Hmemb; [| reflexivity].
        exfalso.
        rewrite (OrchardPlacementCerts.point_placed_complete sel region'
          offset'
          (Complete.enabled_memb_sound OrchardDecidableEq.selector_eqb
            OrchardDecidableEq.selector_eqb_eq
            OrchardDecidableEq.region_id_eqb
            OrchardDecidableEq.region_id_eqb_eq OrchardPlacementCerts.facts
            sel region' offset' Hmemb)) in Hplaced.
        discriminate Hplaced.
    Qed.

    Lemma lookup_arg_agree (sel : Selector.t) (region' : RegionId.t)
        (offset' : Z) (arg : LookupArgument.t columns) :
      List.In (sel, region', offset') OrchardPlacementCerts.enabled ->
      List.In arg
        OrchardPlacementCerts.system.(ConstraintSystem.lookups) ->
      Complete.arg_mentions_selector OrchardDecidableEq.selector_eqb
        sel arg = true ->
      Agree.arg_agree Γhonest Γop region' offset' arg.
    Proof.
      intros Hpoint Harg Hmention.
      split. {
        unfold Agree.selector_agree.
        apply List.Forall_forall.
        intros sel' Hsel'.
        exact (selector_agree_relevant sel region' offset' sel' Hpoint
          (OrchardPlacementCerts.relevant_selectors_In sel sel' arg Harg
            Hmention Hsel')). }
      split. {
        unfold Agree.fixed_agree, Agree.arg_fixed_queries.
        apply List.Forall_forall.
        intros query Hquery.
        apply List.in_flat_map in Hquery.
        destruct Hquery as (pair & Hpair & Hin).
        destruct pair as [expression column'].
        cbn [fst] in Hin.
        destruct query as [column rotation].
        cbn [fst snd].
        symmetry.
        apply fixed_agree.
        apply (proj1
          (List.forallb_forall OrchardPlacementCerts.fixed_written
            OrchardPlacementCerts.lookup_fixed_cells)
          OrchardPlacementCerts.orchard_lookup_fixed_written).
        apply (OrchardPlacementCerts.point_cells_In
          OrchardPlacementCerts.lookup_fixed_queries sel region' offset'
          column rotation Hpoint).
        apply List.in_flat_map.
        exists expression.
        split;
          [ exact (OrchardPlacementCerts.mentioning_expressions_In sel arg
              expression column' Harg Hmention Hpair)
          | exact Hin ]. }
      split. {
        unfold Agree.advice_agree, Agree.arg_advice_queries.
        apply List.Forall_forall.
        intros query Hquery.
        apply List.in_flat_map in Hquery.
        destruct Hquery as (pair & Hpair & Hin).
        destruct pair as [expression column'].
        cbn [fst] in Hin.
        destruct query as [column rotation].
        cbn [fst snd].
        symmetry.
        apply advice_agree.
        apply OrchardPlacementCerts.needed_cells_lookup.
        apply (OrchardPlacementCerts.point_cells_In
          OrchardPlacementCerts.lookup_advice_queries sel region' offset'
          column rotation Hpoint).
        apply List.in_flat_map.
        exists expression.
        split;
          [ exact (OrchardPlacementCerts.mentioning_expressions_In sel arg
              expression column' Harg Hmention Hpair)
          | exact Hin ]. }
      unfold Agree.instance_agree.
      apply List.Forall_forall.
      intros query _.
      symmetry.
      exact (instance_agree (fst query) (offset' + snd query)).
    Qed.

    Lemma lookup_plane_agree_arg (arg : LookupArgument.t columns) :
      Agree.lookup_agree Γhonest Γop 1024 (Agree.arg_lookup_columns arg).
    Proof.
      apply List.Forall_forall.
      intros column _ table_row Hrange.
      symmetry.
      exact (lookup_agree column table_row Hrange).
    Qed.

    (** The placed lookup obligation. *)
    Lemma lookups_placed
        (Hhonest : forall (sel : Selector.t) (region : RegionId.t) (row : Z),
          List.In (sel, region, row) OrchardPlacementCerts.enabled ->
          forall arg,
            List.In arg
              OrchardPlacementCerts.system.(ConstraintSystem.lookups) ->
            Complete.arg_mentions_selector OrchardDecidableEq.selector_eqb
              sel arg = true ->
            eval_lookup_argument Γhonest (region, row) 1024 arg) :
      forall (sel : Selector.t) (region : RegionId.t) (row : Z)
        (region' : RegionId.t) (offset' : Z),
        List.In (sel, region', offset')
          (Complete.enabled_points OrchardPlacementCerts.facts) ->
        region_start_of region' + offset' = region_start_of region + row ->
        forall arg,
          List.In arg
            OrchardPlacementCerts.system.(ConstraintSystem.lookups) ->
          Complete.arg_mentions_selector OrchardDecidableEq.selector_eqb
            sel arg = true ->
          eval_lookup_argument Γop (region, row) 1024 arg.
    Proof.
      intros sel region row region' offset' Hpoint Hrow arg Harg Hmention.
      apply (Agree.realize_lookup_argument_transfer Index.indices
        region_start_of g Γhonest region row region' offset' 1024 arg).
      - apply (proj2 (List.forallb_forall
          (fun pair => expression_instance_free (fst pair))
          arg.(LookupArgument.pairs))).
        intros pair Hpair.
        destruct pair as [expression column].
        exact (system_lookup_expression_instance_free
          OrchardPlacementCerts.system arg expression column
          orchard_instance_free Harg Hpair).
      - exact (eq_sym Hrow).
      - exact (lookup_arg_agree sel region' offset' arg Hpoint Harg Hmention).
      - exact (lookup_plane_agree_arg arg).
      - exact (Hhonest sel region' offset' Hpoint arg Harg Hmention).
    Qed.

  End Replayed.

  (** ** The packaged agreement, universal in the honest input

      Every conjunct is the exact reading the grid-identification obligation
      consumes.  [valid] / [nondegenerate] are needed only by the last two
      conjuncts, through the C2 witness-fact lemma. *)
  Theorem orchard_replayed_agrees (w : HonestInput) (g : RawGrid.t)
      (Hvalid : valid w) (Hnondeg : nondegenerate w)
      (Hreplay :
        apply_events orchard_events
          (initial_grid (orchard_advice w) (orchard_instance w)) = Some g) :
    (* 1. the selector plane is the placed enabled-point indicator *)
    (forall (sel : Selector.t) (region : RegionId.t) (row : Z),
      List.In (sel, region, row) OrchardPlacementCerts.enabled ->
      (realize Index.indices region_start_of g)
        .(Assignment.selector) sel region row = 1 /\
      (OrchardHonestAssignment.honest_assignment w)
        .(Assignment.selector) sel region row = 1) /\
    (forall (sel : Selector.t) (region : RegionId.t) (row : Z),
      (forall (sel' : Selector.t) (region' : RegionId.t) (offset' : Z),
        List.In (sel', region', offset') OrchardPlacementCerts.enabled ->
        Index.selector sel' <> Index.selector sel \/
        region_start_of region' + offset' <> region_start_of region + row) ->
      (realize Index.indices region_start_of g)
        .(Assignment.selector) sel region row = 0) /\
    (* 2. the fixed plane agrees at every queried cell *)
    (forall (column : Fixed.t) (region : RegionId.t) (offset : Z),
      OrchardPlacementCerts.fixed_written (column, region, offset) = true ->
      (realize Index.indices region_start_of g)
        .(Assignment.fixed) column region offset =
      (OrchardHonestAssignment.honest_assignment w)
        .(Assignment.fixed) column region offset) /\
    (* 3. the lookup plane agrees on the range the arguments read *)
    (forall (column : Lookup.t) (row : Z),
      0 <= row < 1024 ->
      (realize Index.indices region_start_of g)
        .(Assignment.lookup) column row =
      (OrchardHonestAssignment.honest_assignment w)
        .(Assignment.lookup) column row) /\
    (* 4. the advice plane agrees at every cell an obligation reads *)
    (forall (column : Advice.t) (region : RegionId.t) (offset : Z),
      List.In (column, region, offset) OrchardPlacementCerts.needed_cells ->
      (realize Index.indices region_start_of g)
        .(Assignment.advice) column region offset =
      (OrchardHonestAssignment.honest_assignment w)
        .(Assignment.advice) column region offset) /\
    (* 5. the instance plane agrees everywhere *)
    (forall (column : Instance_.t) (row : Z),
      (realize Index.indices region_start_of g)
        .(Assignment.instance_) column row =
      (OrchardHonestAssignment.honest_assignment w)
        .(Assignment.instance_) column row) /\
    (* 6. the witness facts of the synthesis program transfer *)
    interpret_facts (realize Index.indices region_start_of g)
      (Complete.witness_facts OrchardPlacementCerts.facts) /\
    (* 7. the constants tail's copy obligations hold of the replayed grid *)
    (forall left right : Raw.Cell.t,
      List.In (Raw.Event.Copy left right) orchard_constants_events ->
      raw_cell_read g left = raw_cell_read g right).
  Proof.
    assert (Hwitness :
      interpret_facts (OrchardHonestAssignment.honest_assignment w)
        (Complete.witness_facts OrchardPlacementCerts.facts)).
    { unfold OrchardPlacementCerts.facts,
        OrchardCompletenessCertificates.facts.
      exact (OrchardForwardLookupsWitness.witness_facts_ok w Hvalid Hnondeg). }
    pose proof (replay_context_full w g Hreplay) as Hstream.
    split. { exact (selector_agree_on w g orchard_events Hstream). }
    split. { exact (placed_selector_off w g orchard_events Hstream). }
    split. { exact (fixed_agree w g orchard_events Hstream). }
    split. { exact (lookup_agree w g orchard_events Hstream). }
    split. { exact (advice_agree w g orchard_events Hstream). }
    split. { exact (instance_agree w g orchard_events Hstream). }
    split.
    { exact (witness_facts_transfer w g orchard_events Hstream Hwitness). }
    exact (constants_copies_hold w g orchard_events Hstream
      (List.incl_refl _) Hwitness).
  Qed.

  (** ** The grid identification and the E1 headline *)

  (** The honest witness facts, in the spelling this file uses. *)
  Lemma honest_witness_facts (w : HonestInput) :
    valid w -> nondegenerate w ->
    interpret_facts (OrchardHonestAssignment.honest_assignment w)
      (Complete.witness_facts OrchardPlacementCerts.facts).
  Proof.
    intros Hvalid Hnondeg.
    unfold OrchardPlacementCerts.facts, OrchardCompletenessCertificates.facts.
    exact (OrchardForwardLookupsWitness.witness_facts_ok w Hvalid Hnondeg).
  Qed.

  (** THE GRID-IDENTIFICATION OBLIGATION, at any replay context.  Replaying
      an Orchard event stream onto the honest free planes yields a grid whose
      realized assignment satisfies the very [circuit_holds] the C2
      completeness theorem proves of [honest_assignment w] — established
      through the placed introduction lemma, since the honest-plane
      hypotheses of [Complete.circuit_holds_intro] are false at a realized
      assignment. *)
  Theorem orchard_grid_identification_stream (w : HonestInput) (g : RawGrid.t)
      (evts : list Raw.Event.t)
      (Hvalid : valid w) (Hnondeg : nondegenerate w)
      (Hstream : replay_context w g evts) :
    circuit_holds (realize Index.indices region_start_of g)
      Garden.Orchard.circuit.synthesize orchard_system.
  Proof.
    apply (Placed.placed_circuit_holds_intro
      OrchardDecidableEq.selector_eqb OrchardDecidableEq.selector_eqb_eq
      OrchardDecidableEq.lookup_eqb
      (realize Index.indices region_start_of g)
      Index.indices region_start_of Garden.Orchard.circuit.synthesize
      orchard_system).
    - exact OrchardCompletenessCertificates.selector_guarded_certificate.
    - exact OrchardCompletenessCertificates.lookup_defaults_certificate.
    - exact (placed_selector_off_orchard w g evts Hstream).
    - exact (placed_lookup_zero w g evts Hstream).
    - exact (determined_holds w g evts Hstream).
    - exact (witness_facts_transfer w g evts Hstream
        (honest_witness_facts w Hvalid Hnondeg)).
    - apply (gates_placed w g evts Hstream).
      intros sel region row Hin gate Hgate name body Hbody.
      exact (OrchardCompletenessForward.gates_join
        OrchardCompletenessForward.all_families
        OrchardCompletenessForward.all_families_covers
        OrchardCompletenessAssembly.gates_all w Hvalid Hnondeg
        sel region row Hin gate Hgate name body Hbody).
    - rewrite OrchardCompletenessCertificates.layouter_table_rows_eq.
      apply (lookups_placed w g evts Hstream).
      intros sel region row Hin arg Harg Hmention.
      exact (OrchardCompletenessForward.lookups_join
        OrchardCompletenessForward.all_families
        OrchardCompletenessForward.all_families_covers
        OrchardCompletenessAssembly.lookups_all w Hvalid Hnondeg
        sel region row Hin arg Harg Hmention).
  Qed.

  (** The grid identification at the full checked stream. *)
  Theorem orchard_grid_identification (w : HonestInput) (g : RawGrid.t)
      (Hvalid : valid w) (Hnondeg : nondegenerate w)
      (Hreplay :
        apply_events orchard_events
          (initial_grid (orchard_advice w) (orchard_instance w)) = Some g) :
    circuit_holds (realize Index.indices region_start_of g)
      Garden.Orchard.circuit.synthesize orchard_system.
  Proof.
    exact (orchard_grid_identification_stream w g orchard_events Hvalid Hnondeg
      (replay_context_full w g Hreplay)).
  Qed.

  (** The same at the synthesis-only stream — the grid
      [Halo2/realize/sound.v]'s [operational_complete] names in its replay
      premise. *)
  Theorem orchard_grid_identification_synthesis (w : HonestInput)
      (g : RawGrid.t)
      (Hvalid : valid w) (Hnondeg : nondegenerate w)
      (Hreplay :
        apply_events orchard_synthesis_events
          (initial_grid (orchard_advice w) (orchard_instance w)) = Some g) :
    circuit_holds (realize Index.indices region_start_of g)
      Garden.Orchard.circuit.synthesize orchard_system.
  Proof.
    exact (orchard_grid_identification_stream w g orchard_synthesis_events
      Hvalid Hnondeg (replay_context_synthesis w g Hreplay)).
  Qed.

  (** THE E1 HEADLINE, the completeness mirror of
      [orchard_operational_sound]: an honest, valid, nondegenerate witness is
      accepted by the ideal checker that mirrors Rust Halo2's [MockProver] on
      the serialized Orchard circuit, constants tail included.

      The full stream is not a literal instance of [operational_complete]:
      that theorem's (stated, unused) replay premise names the synthesis
      stream at the *same* grid, whereas the Orchard honest grid is the
      replay of [orchard_synthesis_events ++ orchard_constants_events], and
      the tail's 166 [AssignFixed] events change the fixed plane.  The route
      is therefore the premise-free restatement
      [operational_complete_events_app] of [replay_planes.v] — proved from
      the same three exported lemmas of [Halo2/realize/sound.v]
      ([relational_gates_to_mock], [relational_lookups_to_mock],
      [layouter_copy_event_fact]) — with the tail's [Copy] obligations
      supplied separately.  [orchard_operational_complete_sound] below is the
      literal instance, on the stream [operational_complete] does cover. *)
  Theorem orchard_operational_complete (w : HonestInput) (g : RawGrid.t)
      (Hvalid : valid w) (Hnondeg : nondegenerate w)
      (Hreplay :
        apply_events orchard_events
          (initial_grid (orchard_advice w) (orchard_instance w)) = Some g) :
    mock_prover_accepts orchard_indexed_system orchard_events g
      orchard_table_rows.
  Proof.
    unfold orchard_indexed_system, orchard_table_rows, orchard_events,
      orchard_synthesis_events, orchard_constants_events.
    apply (operational_complete_events_app Garden.Orchard.circuit.synthesize
      Index.indices region_start_of
      Garden.Orchard.circuit.orchard_usable_rows orchard_system g
      Garden.Orchard.circuit_synthesis_constants.events
      RegionId.NoteCommitOldEquality).
    - exact orchard_instance_free.
    - exact orchard_flattening_ok.
    - exact (orchard_grid_identification w g Hvalid Hnondeg Hreplay).
    - exact (constants_copies_hold w g orchard_events
        (replay_context_full w g Hreplay) (List.incl_refl _)
        (honest_witness_facts w Hvalid Hnondeg)).
  Qed.

  (** The same conclusion on the synthesis-only stream, obtained by applying
      [Halo2/realize/sound.v]'s [operational_complete] verbatim — every
      premise supplied, the replay premise included.  This is the form that
      type-checks against the committed bridge theorem. *)
  Theorem orchard_operational_complete_sound (w : HonestInput) (g : RawGrid.t)
      (Hvalid : valid w) (Hnondeg : nondegenerate w)
      (Hreplay :
        apply_events orchard_synthesis_events
          (initial_grid (orchard_advice w) (orchard_instance w)) = Some g) :
    mock_prover_accepts orchard_indexed_system orchard_synthesis_events g
      orchard_table_rows.
  Proof.
    pose proof (orchard_grid_identification_synthesis w g Hvalid Hnondeg
      Hreplay) as Hholds.
    pose proof (operational_complete Garden.Orchard.circuit.synthesize
      Index.indices region_start_of
      Garden.Orchard.circuit.orchard_usable_rows orchard_system
      (orchard_advice w) (orchard_instance w) g
      RegionId.NoteCommitOldEquality
      orchard_instance_free orchard_flattening_ok) as Hcomplete.
    unfold orchard_indexed_system, orchard_table_rows, orchard_synthesis_events
      in Hreplay |- *.
    destruct (V1.eval_layouter Index.indices region_start_of
      Garden.Orchard.circuit.orchard_usable_rows
      Garden.Orchard.circuit.synthesize) as [v_op evts].
    cbn [snd] in Hreplay |- *.
    exact (Hcomplete Hreplay Hholds).
  Qed.

  (** The unconditional forms: the replay always succeeds, so the honest
      witness is accepted at *the* grid its planes produce.  Both streams are
      covered — the full checked stream through the headline, and the
      synthesis-only stream through the literal [operational_complete]
      instance. *)
  Theorem orchard_operational_complete_ex (w : HonestInput)
      (Hvalid : valid w) (Hnondeg : nondegenerate w) :
    exists g : RawGrid.t,
      apply_events orchard_events
        (initial_grid (orchard_advice w) (orchard_instance w)) = Some g /\
      circuit_holds (realize Index.indices region_start_of g)
        Garden.Orchard.circuit.synthesize orchard_system /\
      mock_prover_accepts orchard_indexed_system orchard_events g
        orchard_table_rows.
  Proof.
    destruct (orchard_replay_planes w) as (g & Hreplay).
    exists g.
    split; [exact Hreplay |].
    split.
    - exact (orchard_grid_identification w g Hvalid Hnondeg Hreplay).
    - exact (orchard_operational_complete w g Hvalid Hnondeg Hreplay).
  Qed.

  Theorem orchard_operational_complete_sound_ex (w : HonestInput)
      (Hvalid : valid w) (Hnondeg : nondegenerate w) :
    exists g : RawGrid.t,
      apply_events orchard_synthesis_events
        (initial_grid (orchard_advice w) (orchard_instance w)) = Some g /\
      circuit_holds (realize Index.indices region_start_of g)
        Garden.Orchard.circuit.synthesize orchard_system /\
      mock_prover_accepts orchard_indexed_system orchard_synthesis_events g
        orchard_table_rows.
  Proof.
    destruct (orchard_synthesis_replay_planes w) as (g & Hreplay).
    exists g.
    split; [exact Hreplay |].
    split.
    - exact (orchard_grid_identification_synthesis w g Hvalid Hnondeg Hreplay).
    - exact (orchard_operational_complete_sound w g Hvalid Hnondeg Hreplay).
  Qed.

End OrchardOperationalAgreement.
