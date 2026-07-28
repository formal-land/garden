(** * Algebraic acceptance: the all-challenge identity reading of a compiled system.

    The L1 layer of the refinement ladder: acceptance of a compiled
    plonkish system stated as the three polynomial-identity families the
    deployed verifier checks — the vanishing quotient for the gate
    polynomials, the four permutation product rules, and the five lookup
    rules — with every challenge ([y], [beta], [gamma], [theta])
    universally quantified.  No commitments, no transcript: the committed
    column polynomials are represented by their values on the evaluation
    domain [H = <w>] (the row dictionary [row j <-> w^j]), and the gate
    combination is carried by explicit polynomials [Es] agreeing with the
    compiled-gate row evaluations on [H].

    [algebraic_accepts] bundles:

    - [gates_agree] + [algebraic_gates_accept]: polynomials [Es] agree on
      [H] with the compiled gate polynomials evaluated on the
      combination-installed grid, and for every challenge [y] the
      verifier's Horner combination ([vanishing/verifier.rs] folds
      [h_eval * y + v], so the first gate polynomial carries the highest
      power) is divisible by [X^n - 1];
    - [algebraic_permutation_accept]: for all [beta, gamma] some running
      products satisfy the four rules of [permutation/verifier.rs]
      ([PermutationPoly.permutation_rules]) against the label assignment
      and the permutation of the closed assembly;
    - [algebraic_lookups_accept]: every compiled lookup argument satisfies
      the transcript-ordered lookup identity package
      ([PlonkishLookupPoly.lookup_identities_hold]) over its pair
      functions on the combination-installed grid.

    [algebraic_sound] discharges the acceptance into the compiled-plonkish
    satisfaction triple consumed by the R2 assembly
    ([Orchard/compiled/main.v]'s [orchard_compiled_accepts] shape):
    compiled-gate vanishing on every domain row, the indexed-system lookup
    conjunct on every domain row of the witness grid, and grid invariance
    under the permutation.  The gate conjunct is the vanishing equivalence
    ([Vanishing.vanishing_sound_horner]); the permutation conjunct is
    [PermutationPoly.permutation_sound_grid_invariant]; the lookup
    conjunct composes [PlonkishLookupPoly.lookup_arguments_sound] with the
    value-preserving substitution seam
    ([PlonkishLookup.lookup_compile_correct_installed]) on the usable rows
    and with the selector-off lookup defaults
    ([PlonkishMock.lookups_defaults_all]) on the blinding rows.

    [algebraic_complete] is the converse, along the same three seams read
    backwards: each has a constructive half already
    ([Vanishing.vanishing_sound_horner] is an equivalence,
    [PermutationPoly.permutation_complete_grid_invariant] exhibits the
    running products division-free, and
    [PlonkishLookupPoly.lookup_arguments_complete] builds the permuted
    columns and the product column from set membership).  Its conclusion is
    [algebraic_accepts_regular], which restricts the permutation conjunct
    to the challenges where no identity-side factor vanishes on a usable
    cell — at the excluded ones the running-product recurrence divides by
    zero and no honest prover has a product column either, and the lookup
    conjunct is already restricted the same way inside
    [PlonkishLookupPoly.lookup_identities_hold].  Soundness loses nothing
    there: an irregular challenge sends the identity-side product to [0],
    the escape branch the counting argument already allows, so
    [algebraic_sound_regular] concludes from the same predicate.  The two
    directions therefore meet at [algebraic_accepts_regular], with
    [algebraic_sound] / [algebraic_accepts] the all-challenge weakenings.

    The replay-facing side conditions (canonical table values, the
    tables-as-fixed-prefix coherence) are supplied as decidable booleans
    over the event stream, discharged on a concrete instance by
    [vm_compute]: [event_fixed_values_ok_b] (every fixed-plane write is a
    canonical residue, so the replayed table planes are canonical) and
    [tables_fill_row0_b] (every table column's padding fill value is also
    pinned at table row [0], so every padding row repeats row [0]). *)

Require Import Stdlib.micromega.Lia.
Require Import Garden.Field.Field.
Require Import Garden.Field.Div.
Require Import Garden.Field.Lemmas.
Require Import Garden.Halo2.main.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.serialize.
Require Import Garden.Halo2.realize.main.
Require Import Garden.Halo2.realize.facts.
Require Import Garden.Halo2.realize.sound.
Require Import Garden.Halo2.plonkish.main.
Require Import Garden.Halo2.plonkish.mock.
Require Import Garden.Halo2.plonkish.compile.
Require Import Garden.Halo2.plonkish.sigma.
Require Import Garden.Halo2.plonkish.lookup_compile.
Require Import Garden.Halo2.plonkish.poly.
Require Import Garden.Halo2.plonkish.vanishing.
Require Import Garden.Halo2.plonkish.permutation_poly.
Require Import Garden.Halo2.plonkish.lookup_poly.

Import List.ListNotations.
Import Plonkish.
Global Open Scope Z_scope.

Module PlonkishAlgebraic.

(** ** Event-level decidable side conditions *)

(** Every fixed-plane write of the stream carries a value passing
    [check]. *)
Definition event_fixed_values_ok_b (check : Z -> bool)
    (events : list Raw.Event.t) : bool :=
  List.forallb
    (fun event =>
      match event with
      | Raw.Event.AssignFixed _ _ _ value => check value
      | Raw.Event.FillFromRow _ _ _ value => check value
      | _ => true
      end)
    events.

(** No table column of the given lookup arguments lies on the avoid
    list — the table-column half of [lookup_columns_avoid_b], stated over
    an arbitrary argument list (the compiled arguments at
    instantiation). *)
Definition lookup_tables_avoid_b (avoid : list Z)
    (lookups : list (LookupArgument.t Configure.indexed_columns)) : bool :=
  List.forallb
    (fun lookup : LookupArgument.t Configure.indexed_columns =>
      List.forallb
        (fun pair => negb (List.existsb (Z.eqb (snd pair)) avoid))
        lookup.(LookupArgument.pairs))
    lookups.

(** Every table column of the given lookup arguments is padded by a
    [FillFromRow] whose extent starts at or before [table_rows], reaches
    [usable_rows], and whose value is also pinned at table row [0] — one
    constant covers the usable padding band [[table_rows, usable_rows)] and
    repeats row [0], the coherence witness of
    [PlonkishLookupPoly.table_prefix_coherent]. *)
Definition tables_fill_row0_b (events : list Raw.Event.t)
    (table_rows usable_rows : Z)
    (lookups : list (LookupArgument.t Configure.indexed_columns)) : bool :=
  List.forallb
    (fun lookup : LookupArgument.t Configure.indexed_columns =>
      List.forallb
        (fun pair =>
          List.existsb
            (fun event =>
              match event with
              | Raw.Event.FillFromRow column from_row to_row value =>
                  andb
                    (andb
                      (andb (column =? snd pair) (from_row <=? table_rows))
                      (usable_rows <=? to_row))
                    (PlonkishMock.table_default_pinned_b events column value)
              | _ => false
              end)
            events)
        lookup.(LookupArgument.pairs))
    lookups.

(** ** The replayed fixed plane preserves a value invariant

    Replay writes the fixed plane only through [AssignFixed] and
    [FillFromRow] event values, so any predicate holding of the initial
    plane and of every written value holds of the whole replayed plane. *)

Lemma apply_event_fixed_plane (P : Z -> Prop)
    (state state' : ReplayState.t) (event : Raw.Event.t)
    (Happly : apply_event state event = Some state')
    (Hvalue :
      match event with
      | Raw.Event.AssignFixed _ _ _ value => P value
      | Raw.Event.FillFromRow _ _ _ value => P value
      | _ => True
      end)
    (Hplane : forall column row : Z,
      P (state.(ReplayState.grid).(RawGrid.cell)
           Raw.ColumnKind.Fixed column row)) :
  forall column row : Z,
    P (state'.(ReplayState.grid).(RawGrid.cell)
         Raw.ColumnKind.Fixed column row).
Proof.
  intros column row.
  destruct event as
    [ name | name | name | name | selector' row' annotation
    | column' row' annotation value | left_cell right_cell
    | column' from_row to_row value ];
    cbn [apply_event] in Happly;
    try (injection Happly as <-; apply Hplane).
  - (* EnableSelector *)
    destruct (List.existsb _ _) in Happly; [discriminate Happly |].
    injection Happly as <-.
    cbn [ReplayState.grid RawGrid.set_selector RawGrid.cell].
    apply Hplane.
  - (* AssignFixed *)
    destruct (orb _ _) in Happly; [discriminate Happly |].
    injection Happly as <-.
    cbn [ReplayState.grid RawGrid.set_fixed RawGrid.cell].
    destruct (andb (column =? column') (row =? row')); [exact Hvalue |].
    apply Hplane.
  - (* FillFromRow *)
    destruct (orb _ _) in Happly; [discriminate Happly |].
    injection Happly as <-.
    cbn [ReplayState.grid RawGrid.fill_fixed RawGrid.cell].
    destruct (andb (column =? column') (andb (from_row <=? row) (row <? to_row)));
      [exact Hvalue |].
    apply Hplane.
Qed.

Lemma apply_events_log_fixed_plane (P : Z -> Prop)
    (events : list Raw.Event.t) :
  forall state state' : ReplayState.t,
  apply_events_log events state = Some state' ->
  List.Forall
    (fun event =>
      match event with
      | Raw.Event.AssignFixed _ _ _ value => P value
      | Raw.Event.FillFromRow _ _ _ value => P value
      | _ => True
      end)
    events ->
  (forall column row : Z,
    P (state.(ReplayState.grid).(RawGrid.cell)
         Raw.ColumnKind.Fixed column row)) ->
  forall column row : Z,
    P (state'.(ReplayState.grid).(RawGrid.cell)
         Raw.ColumnKind.Fixed column row).
Proof.
  induction events as [| event events IH];
    intros state state' Happly Hok Hplane;
    cbn [apply_events_log] in Happly.
  - injection Happly as <-.
    exact Hplane.
  - destruct (apply_event state event) as [next |] eqn:Hevent;
      [| discriminate Happly].
    inversion Hok as [| ? ? Hvalue Hrest]; subst.
    exact (IH next state' Happly Hrest
      (apply_event_fixed_plane P state next event Hevent Hvalue Hplane)).
Qed.

Lemma replay_fixed_plane (P : Z -> Prop) (check : Z -> bool)
    (events : list Raw.Event.t) (advice instance_ : Z -> Z -> Z)
    (grid : RawGrid.t)
    (Hreplay : apply_events events (initial_grid advice instance_) = Some grid)
    (Hcheck : event_fixed_values_ok_b check events = true)
    (Hvalue : forall value : Z, check value = true -> P value)
    (Hzero : P 0) :
  forall column row : Z,
    P (grid.(RawGrid.cell) Raw.ColumnKind.Fixed column row).
Proof.
  unfold apply_events in Hreplay.
  destruct
    (apply_events_log events (ReplayState.init (initial_grid advice instance_)))
    as [state |] eqn:Hlog; [| discriminate Hreplay].
  injection Hreplay as <-.
  apply (apply_events_log_fixed_plane P events _ _ Hlog).
  - unfold event_fixed_values_ok_b in Hcheck.
    rewrite List.forallb_forall in Hcheck.
    apply List.Forall_forall.
    intros event Hin.
    specialize (Hcheck _ Hin).
    destruct event; solve [exact I | exact (Hvalue _ Hcheck)].
  - intros column row.
    cbn [ReplayState.init ReplayState.grid initial_grid RawGrid.cell].
    exact Hzero.
Qed.

Lemma not_in_of_negb_existsb (avoid : list Z) (column : Z) :
  negb (List.existsb (Z.eqb column) avoid) = true ->
  ~ List.In column avoid.
Proof.
  intros Hcheck Hin.
  rewrite Bool.negb_true_iff in Hcheck.
  assert (Hex : List.existsb (Z.eqb column) avoid = true).
  { apply List.existsb_exists.
    exists column.
    split; [exact Hin | apply Z.eqb_refl]. }
  rewrite Hex in Hcheck.
  discriminate Hcheck.
Qed.

Section WithPrime.
  Context {p : Z}.
  Context `{Prime p}.

  (** ** The replay-supplied lookup side conditions

      The two [lookup_arguments_sound] premises about the table plane —
      canonical values and the padding-repeats-a-prefix-row coherence —
      derived from the event stream for the combination-installed grid:
      the table columns avoid the combination columns, so their installed
      reads are the replayed reads. *)

  Lemma replay_argument_table_canonical
      (events : list Raw.Event.t) (advice instance_ : Z -> Z -> Z)
      (grid : RawGrid.t) (compiled : CompiledSystem.t) (domain : Domain.t)
      (arg : LookupArgument.t Configure.indexed_columns)
      (Hreplay :
        apply_events events (initial_grid advice instance_) = Some grid)
      (Hcheck :
        event_fixed_values_ok_b (fun value => andb (0 <=? value) (value <? p))
          events = true)
      (Havoid :
        List.forallb
          (fun pair =>
            negb
              (List.existsb (Z.eqb (snd pair))
                compiled.(CompiledSystem.combination_columns)))
          arg.(LookupArgument.pairs) = true) :
    PlonkishLookupPoly.argument_table_canonical (p := p)
      (grid_assignment (PlonkishLookup.with_combination_planes compiled grid))
      domain arg.
  Proof.
    assert (Hplane : forall column row : Z,
      (grid.(RawGrid.cell) Raw.ColumnKind.Fixed column row) mod p =
      grid.(RawGrid.cell) Raw.ColumnKind.Fixed column row).
    { apply (replay_fixed_plane
        (fun value => value mod p = value)
        (fun value => andb (0 <=? value) (value <? p))
        events advice instance_ grid Hreplay Hcheck).
      - intros value Hvalue.
        apply Bool.andb_true_iff in Hvalue.
        destruct Hvalue as [Hlow Hhigh].
        apply Z.leb_le in Hlow.
        apply Z.ltb_lt in Hhigh.
        apply Z.mod_small.
        lia.
      - apply Zmod_0_l. }
    unfold PlonkishLookupPoly.argument_table_canonical.
    rewrite List.forallb_forall in Havoid.
    apply List.Forall_forall.
    intros pair Hin row Hrow.
    cbn [grid_assignment Assignment.lookup].
    rewrite (PlonkishLookup.with_combination_planes_off compiled grid
      (snd pair) row (not_in_of_negb_existsb _ _ (Havoid _ Hin))).
    apply Hplane.
  Qed.

  Lemma replay_table_prefix_coherent
      (events : list Raw.Event.t) (advice instance_ : Z -> Z -> Z)
      (grid : RawGrid.t) (compiled : CompiledSystem.t) (domain : Domain.t)
      (table_rows : Z)
      (arg : LookupArgument.t Configure.indexed_columns)
      (Hreplay :
        apply_events events (initial_grid advice instance_) = Some grid)
      (Htr_pos : 0 < table_rows)
      (Hfill :
        List.forallb
          (fun pair =>
            List.existsb
              (fun event =>
                match event with
                | Raw.Event.FillFromRow column from_row to_row value =>
                    andb
                      (andb
                        (andb (column =? snd pair) (from_row <=? table_rows))
                        (Domain.usable_rows domain <=? to_row))
                      (PlonkishMock.table_default_pinned_b events column value)
                | _ => false
                end)
              events)
          arg.(LookupArgument.pairs) = true)
      (Havoid :
        List.forallb
          (fun pair =>
            negb
              (List.existsb (Z.eqb (snd pair))
                compiled.(CompiledSystem.combination_columns)))
          arg.(LookupArgument.pairs) = true) :
    PlonkishLookupPoly.table_prefix_coherent domain
      (PlonkishLookupPoly.argument_pair_functions
        (grid_assignment (PlonkishLookup.with_combination_planes compiled grid))
        tt arg)
      table_rows.
  Proof.
    rewrite List.forallb_forall in Hfill, Havoid.
    intros row Hrow.
    exists 0.
    split; [lia |].
    unfold PlonkishLookupPoly.argument_pair_functions.
    apply List.Forall_forall.
    intros fg Hfg.
    apply List.in_map_iff in Hfg.
    destruct Hfg as (pair & Hfg & Hin).
    subst fg.
    pose proof (not_in_of_negb_existsb _ _ (Havoid _ Hin)) as Hout.
    assert (Hread : forall r : Z,
      (grid_assignment (PlonkishLookup.with_combination_planes compiled grid))
        .(Assignment.lookup) (snd pair) r =
      grid.(RawGrid.cell) Raw.ColumnKind.Fixed (snd pair) r).
    { intros r.
      exact (PlonkishLookup.with_combination_planes_off compiled grid
        (snd pair) r Hout). }
    cbn [snd].
    rewrite !Hread.
    specialize (Hfill _ Hin).
    apply List.existsb_exists in Hfill.
    destruct Hfill as (event & Hev_in & Hev_check).
    destruct event as
      [ name | name | name | name | selector' row' annotation
      | column' row' annotation value | left_cell right_cell
      | column' from_row to_row value ];
      try discriminate Hev_check.
    apply Bool.andb_true_iff in Hev_check.
    destruct Hev_check as [Hev_check Hpinned].
    apply Bool.andb_true_iff in Hev_check.
    destruct Hev_check as [Hev_check Hcover].
    apply Bool.andb_true_iff in Hev_check.
    destruct Hev_check as [Hcolumn Hfrom].
    apply Z.eqb_eq in Hcolumn.
    apply Z.leb_le in Hfrom.
    apply Z.leb_le in Hcover.
    subst column'.
    rewrite (replay_fill_pinned events (initial_grid advice instance_) grid
      (snd pair) from_row to_row value row Hreplay Hev_in
      (Z.le_trans _ _ _ Hfrom (proj1 Hrow))
      (Z.lt_le_trans _ _ _ (proj2 Hrow) Hcover)).
    rewrite (PlonkishMock.table_default_pinned_value events
      (initial_grid advice instance_) grid (snd pair) value Hreplay Hpinned).
    reflexivity.
  Qed.

  (** ** The acceptance statement and its soundness *)

  Section Acceptance.
    (** The evaluation domain and its primitive [2^s]-th root. *)
    Variable domain : Domain.t.
    Variable w : Z.
    Variable s : nat.
    Hypothesis Hs : (1 <= s)%nat.
    Hypothesis Hp2 : 2 < p.
    Hypothesis Hw_full : Fpow w (2 ^ Z.of_nat s) = 1.
    Hypothesis Hw_half : Fpow w (2 ^ (Z.of_nat s - 1)) = UnOp.from (-1).
    Hypothesis Hn : Domain.n domain = Z.of_nat (2 ^ s).

    (** The compiled system, its compilation equation, and the replayed
        witness grid. *)
    Variable system : ConstraintSystem.t Configure.indexed_columns.
    Variable infos : list Compile.SelectorInfo.t.
    Variable num_fixed_columns : Z.
    Variable permutation_columns : list Raw.ColumnRef.t.
    Variable constants : list Z.
    Variable compiled : CompiledSystem.t.
    Variable events : list Raw.Event.t.
    Variable advice instance_ : Z -> Z -> Z.
    Variable grid : RawGrid.t.
    Variable table_rows : Z.

    (** The grid the compiled gates and lookups read: the witness grid
        with the keygen-materialized combination fixed planes
        installed. *)
    Definition cgrid : RawGrid.t :=
      PlonkishLookup.with_combination_planes compiled grid.

    (** The permutation reading: the cell values [gperm], the coset label
        assignment [lbl] (instantiated by [delta^i * w^j]), and the closed
        assembly. *)
    Variable ncols chunk_len : nat.
    Variable gperm lbl : Sigma.cell -> Z.
    Variable assembly : Sigma.t.

    (** The gate-combination polynomials: [Es] lists one polynomial per
        compiled gate polynomial, agreeing on [H] with its evaluation on
        the installed grid — the "column polynomials agreeing with the
        grid on [H]" reading of the gate conjunct. *)
    Variable Es : list Poly.t.

    Definition gates_agree : Prop :=
      List.length Es = List.length compiled.(CompiledSystem.gates) /\
      (forall i : nat, (i < List.length Es)%nat ->
       forall j : nat, (j < 2 ^ s)%nat ->
       Poly.eval (p := p) (List.nth i Es []) (Fpow w (Z.of_nat j)) =
       eval_expression (grid_assignment cgrid) (tt, Z.of_nat j)
         (List.nth i compiled.(CompiledSystem.gates)
           (Expression.Constant 0))).

    (** The vanishing conjunct: for every challenge [y] the verifier's
        Horner combination of [Es] is divisible by [X^n - 1]. *)
    Definition algebraic_gates_accept : Prop :=
      forall y : Z, exists h : Poly.t,
        Poly.peq (p := p) (Vanishing.combine_horner (p := p) y Es)
          (Poly.pmul (p := p) h (Poly.xn1 (p := p) (2 ^ s)%nat)).

    (** The permutation conjunct: for all [beta, gamma] some running
        products satisfy the four product rules against [Sigma.perm] of
        the assembly. *)
    Definition algebraic_permutation_accept : Prop :=
      forall beta gamma : Z, exists zs : list (Z -> Z),
        PermutationPoly.permutation_rules domain ncols chunk_len gperm lbl
          (Sigma.perm assembly) beta gamma zs.

    (** The lookup conjunct: every compiled lookup argument satisfies the
        transcript-ordered five-rule identity package over its pair
        functions on the installed grid. *)
    Definition algebraic_lookups_accept : Prop :=
      List.Forall
        (fun arg : LookupArgument.t Configure.indexed_columns =>
          PlonkishLookupPoly.lookup_identities_hold (p := p) domain
            (PlonkishLookupPoly.argument_pair_functions
              (grid_assignment cgrid) tt arg))
        compiled.(CompiledSystem.lookups).

    Definition algebraic_accepts : Prop :=
      gates_agree /\
      algebraic_gates_accept /\
      algebraic_permutation_accept /\
      algebraic_lookups_accept.

    (** *** The regular-challenge reading

        The permutation conjunct above quantifies over every [(β, γ)], but
        at an irregular challenge — one where an identity-side factor
        [v + β·lbl(c) + γ] vanishes on a usable cell — the running-product
        recurrence divides by zero and no honest prover has a product
        column either.  The completeness direction is therefore stated over
        the regular challenges, exactly as the lookup conjunct already is
        ([PlonkishLookupPoly.lookup_challenge_regular] sits inside
        [lookup_identities_hold]).

        Soundness loses nothing by moving to the same reading: an irregular
        challenge sends the identity-side product to [0] outright, which is
        the escape branch the counting argument already allows, so
        [algebraic_sound_regular] below derives the same conclusion from
        the weaker hypothesis.  [algebraic_accepts_regular] is thus the
        predicate where the two directions meet. *)

    Definition permutation_challenge_regular (beta gamma : Z) : Prop :=
      PermutationPoly.challenge_regular (p := p) domain ncols gperm lbl
        beta gamma.

    Definition algebraic_permutation_accept_regular : Prop :=
      forall beta gamma : Z,
        permutation_challenge_regular beta gamma ->
        exists zs : list (Z -> Z),
          PermutationPoly.permutation_rules domain ncols chunk_len gperm lbl
            (Sigma.perm assembly) beta gamma zs.

    Definition algebraic_accepts_regular : Prop :=
      gates_agree /\
      algebraic_gates_accept /\
      algebraic_permutation_accept_regular /\
      algebraic_lookups_accept.

    Lemma algebraic_accepts_regular_of_accepts :
      algebraic_accepts -> algebraic_accepts_regular.
    Proof.
      intros (Hagree & Hgates & Hperm & Hlookups).
      exact (conj Hagree
        (conj Hgates
          (conj (fun beta gamma _ => Hperm beta gamma) Hlookups))).
    Qed.

    (** *** The gate conjunct: vanishing quotient to row-wise gate zero *)

    Lemma algebraic_gates_sound
        (Hcount : Z.of_nat (List.length compiled.(CompiledSystem.gates)) <= p)
        (Hagree : gates_agree)
        (Haccept : algebraic_gates_accept) :
      PlonkishCompile.compiled_gates_hold domain compiled cgrid.
    Proof.
      destruct Hagree as [Hlen Hrows].
      set (rowv := fun i j : nat =>
        eval_expression (grid_assignment cgrid) (tt, Z.of_nat j)
          (List.nth i compiled.(CompiledSystem.gates)
            (Expression.Constant 0))).
      assert (Hcount' : Z.of_nat (List.length Es) <= p)
        by (rewrite Hlen; exact Hcount).
      assert (Hcanon : forall i j : nat, rowv i j mod p = rowv i j).
      { intros i j.
        unfold rowv.
        exact (PlonkishCompile.eval_expression_reduced _ tt _ _). }
      assert (Hagree' : forall i : nat, (i < List.length Es)%nat ->
        forall j : nat, (j < 2 ^ s)%nat ->
        Poly.eval (p := p) (List.nth i Es []) (Fpow w (Z.of_nat j)) =
        rowv i j mod p).
      { intros i Hi j Hj.
        rewrite (Hcanon i j).
        exact (Hrows i Hi j Hj). }
      assert (Hvanish :
        forall i : nat, (i < List.length Es)%nat ->
        forall j : nat, (j < 2 ^ s)%nat ->
        Poly.eval (p := p) (List.nth i Es []) (Fpow w (Z.of_nat j)) = 0).
      { exact (proj1 (Vanishing.vanishing_sound_horner w s Hs Hp2
          Hw_full Hw_half Es Hcount') Haccept). }
      intros row Hrow poly Hin.
      destruct (List.In_nth _ _ (Expression.Constant 0) Hin)
        as (i & Hi & Hpoly).
      rewrite <- Hlen in Hi.
      assert (Hj : (Z.to_nat row < 2 ^ s)%nat).
      { rewrite Hn in Hrow.
        assert (Hup : Z.of_nat (Z.to_nat row) < Z.of_nat (2 ^ s))
          by (rewrite Z2Nat.id; lia).
        lia. }
      pose proof (Hvanish i Hi (Z.to_nat row) Hj) as Hzero.
      rewrite (Hagree' i Hi (Z.to_nat row) Hj) in Hzero.
      rewrite Hcanon in Hzero.
      unfold rowv in Hzero.
      rewrite Z2Nat.id in Hzero by lia.
      rewrite Hpoly in Hzero.
      exact Hzero.
    Qed.

    (** *** The permutation conjunct: product rules to grid invariance *)

    Lemma algebraic_permutation_sound_regular
        (Hk : 0 <= domain.(Domain.k))
        (Hbf : 0 <= domain.(Domain.blinding_factors))
        (Hur : 0 <= Domain.usable_rows domain)
        (Hchunk : (0 < chunk_len)%nat)
        (Hbig :
          2 * Z.of_nat
            (List.length (PermutationPoly.all_cells domain ncols chunk_len)) +
          1 <= p)
        (Hinj : forall c d : Sigma.cell,
          PermutationPoly.space_cell domain ncols c ->
          PermutationPoly.space_cell domain ncols d ->
          lbl c mod p = lbl d mod p -> c = d)
        (Hrange : forall c : Sigma.cell,
          PermutationPoly.usable_cell domain ncols c ->
          PermutationPoly.space_cell domain ncols (Sigma.perm assembly c))
        (Hfix : forall c : Sigma.cell,
          ~ PermutationPoly.usable_cell domain ncols c ->
          Sigma.perm assembly c = c)
        (Hred : forall c : Sigma.cell,
          PermutationPoly.usable_cell domain ncols c -> 0 <= gperm c < p)
        (Haccept : algebraic_permutation_accept_regular) :
      grid_invariant gperm assembly.
    Proof.
      exact (PermutationPoly.permutation_sound_grid_invariant_regular domain
        Hk Hbf Hur ncols chunk_len Hchunk gperm lbl (Sigma.perm assembly)
        assembly (fun _ => eq_refl) Hbig Hinj Hrange Hfix Hred Haccept).
    Qed.

    (** *** The lookup conjunct: identities to indexed-system membership *)

    Lemma algebraic_lookups_sound
        (Hreplay :
          apply_events events (initial_grid advice instance_) = Some grid)
        (Hcompiled :
          compiled =
          Compile.compile system infos num_fixed_columns permutation_columns
            constants)
        (Hbf : 0 <= domain.(Domain.blinding_factors))
        (Hur : 0 <= Domain.usable_rows domain)
        (Htr_pos : 0 < table_rows)
        (Htr_le : table_rows <= Domain.usable_rows domain)
        (Hp_pts :
          Z.of_nat (2 * Z.to_nat (Domain.usable_rows domain) + 2) <= p)
        (Hp_theta :
          List.Forall
            (fun arg : LookupArgument.t Configure.indexed_columns =>
              Z.of_nat
                (Z.to_nat (Domain.usable_rows domain) *
                 List.length arg.(LookupArgument.pairs) + 1) <= p)
            compiled.(CompiledSystem.lookups))
        (Hcanon_events :
          event_fixed_values_ok_b
            (fun value => andb (0 <=? value) (value <? p)) events = true)
        (Hfill :
          tables_fill_row0_b events table_rows (Domain.usable_rows domain)
            compiled.(CompiledSystem.lookups) = true)
        (Htables_avoid :
          lookup_tables_avoid_b
            compiled.(CompiledSystem.combination_columns)
            compiled.(CompiledSystem.lookups) = true)
        (Hact : forall s0 row : Z,
          0 <= row < Domain.n domain ->
          grid.(RawGrid.sel) s0 row =
          (if List.nth (Z.to_nat row)
              (PlonkishCompile.info_activations infos s0) false
           then 1 else 0))
        (Hexact :
          PlonkishLookup.lookup_replacements_exact_b
            (PlonkishCompile.combination_view compiled)
            (PlonkishCompile.info_activations infos)
            (Z.to_nat (Domain.n domain))
            compiled.(CompiledSystem.selector_assignments)
            system = true)
        (Hlookup_avoid :
          PlonkishLookup.lookup_columns_avoid_b
            compiled.(CompiledSystem.combination_columns) system = true)
        (Hwithin :
          PlonkishMock.selector_rows_within_b (Domain.usable_rows domain)
            events = true)
        (Hdefaults :
          PlonkishMock.lookup_defaults_of_events_b events system table_rows =
          true)
        (Haccept : algebraic_lookups_accept) :
      forall row : Z,
      0 <= row < Domain.n domain ->
      List.Forall
        (eval_lookup_argument (grid_assignment grid) (tt, row) table_rows)
        system.(ConstraintSystem.lookups).
    Proof.
      intros row Hrow.
      destruct (Z_lt_le_dec row (Domain.usable_rows domain)) as [Hlt | Hge].
      - (* Usable rows: the lookup identities give compiled-argument
           membership, and the substitution seam transfers it to the
           indexed system on the witness grid. *)
        apply (proj1 (PlonkishLookup.lookup_compile_correct_installed domain
          system infos num_fixed_columns permutation_columns constants grid
          compiled table_rows Hcompiled Hact Hexact Hlookup_avoid row Hrow)).
        assert (Hargs :
          List.Forall
            (fun arg : LookupArgument.t Configure.indexed_columns =>
              PlonkishLookupPoly.argument_table_canonical (p := p)
                (grid_assignment cgrid) domain arg /\
              PlonkishLookupPoly.table_prefix_coherent domain
                (PlonkishLookupPoly.argument_pair_functions
                  (grid_assignment cgrid) tt arg) table_rows /\
              Z.of_nat
                (Z.to_nat (Domain.usable_rows domain) *
                 List.length arg.(LookupArgument.pairs) + 1) <= p /\
              PlonkishLookupPoly.lookup_identities_hold (p := p) domain
                (PlonkishLookupPoly.argument_pair_functions
                  (grid_assignment cgrid) tt arg))
            compiled.(CompiledSystem.lookups)).
        { unfold tables_fill_row0_b in Hfill.
          unfold lookup_tables_avoid_b in Htables_avoid.
          unfold algebraic_lookups_accept in Haccept.
          rewrite List.forallb_forall in Hfill, Htables_avoid.
          rewrite List.Forall_forall in Hp_theta, Haccept.
          apply List.Forall_forall.
          intros arg Hin.
          refine (conj _ (conj _ (conj (Hp_theta _ Hin) (Haccept _ Hin)))).
          - exact (replay_argument_table_canonical events advice instance_
              grid compiled domain arg Hreplay Hcanon_events
              (Htables_avoid _ Hin)).
          - exact (replay_table_prefix_coherent events advice instance_
              grid compiled domain table_rows arg Hreplay Htr_pos
              (Hfill _ Hin) (Htables_avoid _ Hin)). }
        exact (PlonkishLookupPoly.lookup_arguments_sound domain
          (grid_assignment cgrid) tt compiled.(CompiledSystem.lookups)
          table_rows Hbf Hur Htr_pos Htr_le Hp_pts Hargs row
          (conj (proj1 Hrow) Hlt)).
      - (* Blinding rows: every selector reads [0], so each argument holds
           at its pinned table-row-[0] default. *)
        apply (PlonkishMock.lookups_defaults_all events
          (initial_grid advice instance_) grid table_rows system Hreplay
          Hdefaults row).
        intros selector.
        exact (PlonkishMock.grid_selectors_zero_outside events advice
          instance_ grid (Domain.usable_rows domain) row Hreplay Hwithin
          ltac:(lia) selector).
    Qed.

    (** *** The bundle: algebraic acceptance to compiled satisfaction

        The conclusion is the compiled-plonkish satisfaction triple in the
        exact shape the R2 assembly consumes ([orchard_compiled_accepts]):
        compiled gates vanish on the installed grid over every domain row,
        the indexed-system lookup arguments hold on the witness grid over
        every domain row, and the grid is invariant under the assembly's
        permutation. *)

    Theorem algebraic_sound_regular
        (Hreplay :
          apply_events events (initial_grid advice instance_) = Some grid)
        (Hcompiled :
          compiled =
          Compile.compile system infos num_fixed_columns permutation_columns
            constants)
        (Hcount : Z.of_nat (List.length compiled.(CompiledSystem.gates)) <= p)
        (Hk : 0 <= domain.(Domain.k))
        (Hbf : 0 <= domain.(Domain.blinding_factors))
        (Hur : 0 <= Domain.usable_rows domain)
        (Hchunk : (0 < chunk_len)%nat)
        (Hbig :
          2 * Z.of_nat
            (List.length (PermutationPoly.all_cells domain ncols chunk_len)) +
          1 <= p)
        (Hinj : forall c d : Sigma.cell,
          PermutationPoly.space_cell domain ncols c ->
          PermutationPoly.space_cell domain ncols d ->
          lbl c mod p = lbl d mod p -> c = d)
        (Hrange : forall c : Sigma.cell,
          PermutationPoly.usable_cell domain ncols c ->
          PermutationPoly.space_cell domain ncols (Sigma.perm assembly c))
        (Hfix : forall c : Sigma.cell,
          ~ PermutationPoly.usable_cell domain ncols c ->
          Sigma.perm assembly c = c)
        (Hred : forall c : Sigma.cell,
          PermutationPoly.usable_cell domain ncols c -> 0 <= gperm c < p)
        (Htr_pos : 0 < table_rows)
        (Htr_le : table_rows <= Domain.usable_rows domain)
        (Hp_pts :
          Z.of_nat (2 * Z.to_nat (Domain.usable_rows domain) + 2) <= p)
        (Hp_theta :
          List.Forall
            (fun arg : LookupArgument.t Configure.indexed_columns =>
              Z.of_nat
                (Z.to_nat (Domain.usable_rows domain) *
                 List.length arg.(LookupArgument.pairs) + 1) <= p)
            compiled.(CompiledSystem.lookups))
        (Hcanon_events :
          event_fixed_values_ok_b
            (fun value => andb (0 <=? value) (value <? p)) events = true)
        (Hfill :
          tables_fill_row0_b events table_rows (Domain.usable_rows domain)
            compiled.(CompiledSystem.lookups) = true)
        (Htables_avoid :
          lookup_tables_avoid_b
            compiled.(CompiledSystem.combination_columns)
            compiled.(CompiledSystem.lookups) = true)
        (Hact : forall s0 row : Z,
          0 <= row < Domain.n domain ->
          grid.(RawGrid.sel) s0 row =
          (if List.nth (Z.to_nat row)
              (PlonkishCompile.info_activations infos s0) false
           then 1 else 0))
        (Hexact :
          PlonkishLookup.lookup_replacements_exact_b
            (PlonkishCompile.combination_view compiled)
            (PlonkishCompile.info_activations infos)
            (Z.to_nat (Domain.n domain))
            compiled.(CompiledSystem.selector_assignments)
            system = true)
        (Hlookup_avoid :
          PlonkishLookup.lookup_columns_avoid_b
            compiled.(CompiledSystem.combination_columns) system = true)
        (Hwithin :
          PlonkishMock.selector_rows_within_b (Domain.usable_rows domain)
            events = true)
        (Hdefaults :
          PlonkishMock.lookup_defaults_of_events_b events system table_rows =
          true)
        (Haccept : algebraic_accepts_regular) :
      PlonkishCompile.compiled_gates_hold domain compiled cgrid /\
      (forall row : Z,
        0 <= row < Domain.n domain ->
        List.Forall
          (eval_lookup_argument (grid_assignment grid) (tt, row) table_rows)
          system.(ConstraintSystem.lookups)) /\
      grid_invariant gperm assembly.
    Proof.
      destruct Haccept as (Hagree & Hgates & Hperm & Hlookups).
      split; [| split].
      - exact (algebraic_gates_sound Hcount Hagree Hgates).
      - exact (algebraic_lookups_sound Hreplay Hcompiled Hbf Hur Htr_pos
          Htr_le Hp_pts Hp_theta Hcanon_events Hfill Htables_avoid Hact
          Hexact Hlookup_avoid Hwithin Hdefaults Hlookups).
      - exact (algebraic_permutation_sound_regular Hk Hbf Hur Hchunk Hbig
          Hinj Hrange Hfix Hred Hperm).
    Qed.

    (** The all-challenge reading, a weakening of the hypothesis. *)
    Theorem algebraic_sound
        (Hreplay :
          apply_events events (initial_grid advice instance_) = Some grid)
        (Hcompiled :
          compiled =
          Compile.compile system infos num_fixed_columns permutation_columns
            constants)
        (Hcount : Z.of_nat (List.length compiled.(CompiledSystem.gates)) <= p)
        (Hk : 0 <= domain.(Domain.k))
        (Hbf : 0 <= domain.(Domain.blinding_factors))
        (Hur : 0 <= Domain.usable_rows domain)
        (Hchunk : (0 < chunk_len)%nat)
        (Hbig :
          2 * Z.of_nat
            (List.length (PermutationPoly.all_cells domain ncols chunk_len)) +
          1 <= p)
        (Hinj : forall c d : Sigma.cell,
          PermutationPoly.space_cell domain ncols c ->
          PermutationPoly.space_cell domain ncols d ->
          lbl c mod p = lbl d mod p -> c = d)
        (Hrange : forall c : Sigma.cell,
          PermutationPoly.usable_cell domain ncols c ->
          PermutationPoly.space_cell domain ncols (Sigma.perm assembly c))
        (Hfix : forall c : Sigma.cell,
          ~ PermutationPoly.usable_cell domain ncols c ->
          Sigma.perm assembly c = c)
        (Hred : forall c : Sigma.cell,
          PermutationPoly.usable_cell domain ncols c -> 0 <= gperm c < p)
        (Htr_pos : 0 < table_rows)
        (Htr_le : table_rows <= Domain.usable_rows domain)
        (Hp_pts :
          Z.of_nat (2 * Z.to_nat (Domain.usable_rows domain) + 2) <= p)
        (Hp_theta :
          List.Forall
            (fun arg : LookupArgument.t Configure.indexed_columns =>
              Z.of_nat
                (Z.to_nat (Domain.usable_rows domain) *
                 List.length arg.(LookupArgument.pairs) + 1) <= p)
            compiled.(CompiledSystem.lookups))
        (Hcanon_events :
          event_fixed_values_ok_b
            (fun value => andb (0 <=? value) (value <? p)) events = true)
        (Hfill :
          tables_fill_row0_b events table_rows (Domain.usable_rows domain)
            compiled.(CompiledSystem.lookups) = true)
        (Htables_avoid :
          lookup_tables_avoid_b
            compiled.(CompiledSystem.combination_columns)
            compiled.(CompiledSystem.lookups) = true)
        (Hact : forall s0 row : Z,
          0 <= row < Domain.n domain ->
          grid.(RawGrid.sel) s0 row =
          (if List.nth (Z.to_nat row)
              (PlonkishCompile.info_activations infos s0) false
           then 1 else 0))
        (Hexact :
          PlonkishLookup.lookup_replacements_exact_b
            (PlonkishCompile.combination_view compiled)
            (PlonkishCompile.info_activations infos)
            (Z.to_nat (Domain.n domain))
            compiled.(CompiledSystem.selector_assignments)
            system = true)
        (Hlookup_avoid :
          PlonkishLookup.lookup_columns_avoid_b
            compiled.(CompiledSystem.combination_columns) system = true)
        (Hwithin :
          PlonkishMock.selector_rows_within_b (Domain.usable_rows domain)
            events = true)
        (Hdefaults :
          PlonkishMock.lookup_defaults_of_events_b events system table_rows =
          true)
        (Haccept : algebraic_accepts) :
      PlonkishCompile.compiled_gates_hold domain compiled cgrid /\
      (forall row : Z,
        0 <= row < Domain.n domain ->
        List.Forall
          (eval_lookup_argument (grid_assignment grid) (tt, row) table_rows)
          system.(ConstraintSystem.lookups)) /\
      grid_invariant gperm assembly.
    Proof.
      exact (algebraic_sound_regular Hreplay Hcompiled Hcount Hk Hbf Hur
        Hchunk Hbig Hinj Hrange Hfix Hred Htr_pos Htr_le Hp_pts Hp_theta
        Hcanon_events Hfill Htables_avoid Hact Hexact Hlookup_avoid Hwithin
        Hdefaults (algebraic_accepts_regular_of_accepts Haccept)).
    Qed.

    (** ** Completeness: compiled satisfaction to algebraic acceptance

        The converse of [algebraic_sound_regular], along the same three
        seams read backwards.  Each has a constructive half already:
        [Vanishing.vanishing_sound_horner] is an equivalence, so gate
        polynomials agreeing with a satisfying grid on [H] have a vanishing
        quotient at every challenge;
        [PermutationPoly.permutation_complete_grid_invariant] exhibits the
        running products division-free from σ-invariance; and
        [PlonkishLookupPoly.lookup_arguments_complete] builds the permuted
        columns and the product column from set membership, carried to the
        compiled arguments by the substitution seam
        ([PlonkishLookup.lookup_compile_correct_installed]) in its other
        direction. *)

    (** *** The gate conjunct: row-wise gate zero to vanishing quotient *)

    Lemma algebraic_gates_complete
        (Hcount : Z.of_nat (List.length compiled.(CompiledSystem.gates)) <= p)
        (Hagree : gates_agree)
        (Hhold : PlonkishCompile.compiled_gates_hold domain compiled cgrid) :
      algebraic_gates_accept.
    Proof.
      destruct Hagree as [Hlen Hrows].
      assert (Hcount' : Z.of_nat (List.length Es) <= p)
        by (rewrite Hlen; exact Hcount).
      refine (proj2 (Vanishing.vanishing_sound_horner w s Hs Hp2
        Hw_full Hw_half Es Hcount') _).
      intros i Hi j Hj.
      rewrite (Hrows i Hi j Hj).
      apply (Hhold (Z.of_nat j)).
      - rewrite Hn. lia.
      - apply List.nth_In. rewrite <- Hlen. exact Hi.
    Qed.

    (** *** The permutation conjunct: grid invariance to product rules *)

    Lemma algebraic_permutation_complete
        (Hk : 0 <= domain.(Domain.k))
        (Hbf : 0 <= domain.(Domain.blinding_factors))
        (Hur : 0 <= Domain.usable_rows domain)
        (Hchunk : (0 < chunk_len)%nat)
        (Hfix : forall c : Sigma.cell,
          ~ PermutationPoly.usable_cell domain ncols c ->
          Sigma.perm assembly c = c)
        (Hginj : forall c d : Sigma.cell,
          Sigma.perm assembly c = Sigma.perm assembly d -> c = d)
        (Hsigma : grid_invariant gperm assembly) :
      algebraic_permutation_accept_regular.
    Proof.
      intros beta gamma Hreg.
      exact (PermutationPoly.permutation_complete_grid_invariant domain
        Hk Hbf Hur ncols chunk_len Hchunk gperm lbl (Sigma.perm assembly)
        assembly (fun _ => eq_refl) Hsigma Hfix Hginj beta gamma Hreg).
    Qed.

    (** *** The lookup conjunct: membership to the identity package *)

    Lemma algebraic_lookups_complete
        (Hcompiled :
          compiled =
          Compile.compile system infos num_fixed_columns permutation_columns
            constants)
        (Hbf : 0 <= domain.(Domain.blinding_factors))
        (Hur : 0 <= Domain.usable_rows domain)
        (Htr_le : table_rows <= Domain.usable_rows domain)
        (Hact : forall s0 row : Z,
          0 <= row < Domain.n domain ->
          grid.(RawGrid.sel) s0 row =
          (if List.nth (Z.to_nat row)
              (PlonkishCompile.info_activations infos s0) false
           then 1 else 0))
        (Hexact :
          PlonkishLookup.lookup_replacements_exact_b
            (PlonkishCompile.combination_view compiled)
            (PlonkishCompile.info_activations infos)
            (Z.to_nat (Domain.n domain))
            compiled.(CompiledSystem.selector_assignments)
            system = true)
        (Hlookup_avoid :
          PlonkishLookup.lookup_columns_avoid_b
            compiled.(CompiledSystem.combination_columns) system = true)
        (Hhold : forall row : Z,
          0 <= row < Domain.n domain ->
          List.Forall
            (eval_lookup_argument (grid_assignment grid) (tt, row) table_rows)
            system.(ConstraintSystem.lookups)) :
      algebraic_lookups_accept.
    Proof.
      assert (Hlt : Domain.usable_rows domain < Domain.n domain)
        by (unfold Domain.usable_rows in *; lia).
      apply (PlonkishLookupPoly.lookup_arguments_complete domain
        (grid_assignment cgrid) tt compiled.(CompiledSystem.lookups)
        table_rows Hbf Hur Htr_le).
      intros row Hrow.
      assert (Hrow' : 0 <= row < Domain.n domain) by lia.
      apply (proj2 (PlonkishLookup.lookup_compile_correct_installed domain
        system infos num_fixed_columns permutation_columns constants grid
        compiled table_rows Hcompiled Hact Hexact Hlookup_avoid row Hrow')).
      exact (Hhold row Hrow').
    Qed.

    (** *** The bundle: compiled satisfaction to algebraic acceptance

        The hypothesis is exactly the conclusion of
        [algebraic_sound_regular] — the compiled-plonkish satisfaction
        triple — plus the two σ side conditions the completeness direction
        needs (σ fixes the non-usable cells and is injective) and the
        prover's choice of gate polynomials.  The conclusion is the
        acceptance predicate soundness consumes, so the two theorems
        compose in both directions at [algebraic_accepts_regular]. *)

    Theorem algebraic_complete
        (Hcompiled :
          compiled =
          Compile.compile system infos num_fixed_columns permutation_columns
            constants)
        (Hcount : Z.of_nat (List.length compiled.(CompiledSystem.gates)) <= p)
        (Hk : 0 <= domain.(Domain.k))
        (Hbf : 0 <= domain.(Domain.blinding_factors))
        (Hur : 0 <= Domain.usable_rows domain)
        (Hchunk : (0 < chunk_len)%nat)
        (Htr_le : table_rows <= Domain.usable_rows domain)
        (Hact : forall s0 row : Z,
          0 <= row < Domain.n domain ->
          grid.(RawGrid.sel) s0 row =
          (if List.nth (Z.to_nat row)
              (PlonkishCompile.info_activations infos s0) false
           then 1 else 0))
        (Hexact :
          PlonkishLookup.lookup_replacements_exact_b
            (PlonkishCompile.combination_view compiled)
            (PlonkishCompile.info_activations infos)
            (Z.to_nat (Domain.n domain))
            compiled.(CompiledSystem.selector_assignments)
            system = true)
        (Hlookup_avoid :
          PlonkishLookup.lookup_columns_avoid_b
            compiled.(CompiledSystem.combination_columns) system = true)
        (Hfix : forall c : Sigma.cell,
          ~ PermutationPoly.usable_cell domain ncols c ->
          Sigma.perm assembly c = c)
        (Hginj : forall c d : Sigma.cell,
          Sigma.perm assembly c = Sigma.perm assembly d -> c = d)
        (Hagree : gates_agree)
        (Hgates : PlonkishCompile.compiled_gates_hold domain compiled cgrid)
        (Hlookups : forall row : Z,
          0 <= row < Domain.n domain ->
          List.Forall
            (eval_lookup_argument (grid_assignment grid) (tt, row) table_rows)
            system.(ConstraintSystem.lookups))
        (Hsigma : grid_invariant gperm assembly) :
      algebraic_accepts_regular.
    Proof.
      refine (conj Hagree (conj _ (conj _ _))).
      - exact (algebraic_gates_complete Hcount Hagree Hgates).
      - exact (algebraic_permutation_complete Hk Hbf Hur Hchunk Hfix Hginj
          Hsigma).
      - exact (algebraic_lookups_complete Hcompiled Hbf Hur Htr_le Hact
          Hexact Hlookup_avoid Hlookups).
    Qed.

  End Acceptance.

  (** ** Inhabitation of the gate-polynomial witness

      [gates_agree] pins the prover's gate polynomials only on [H], so
      wherever the compiled gates already vanish there, the zero
      polynomials satisfy it.  Acceptance is therefore never out of reach
      for want of an [Es]: on a satisfying grid this witness feeds
      [algebraic_complete], so [algebraic_accepts_regular] is inhabited
      rather than merely implied. *)

  Definition zero_gate_polys (compiled : CompiledSystem.t) : list Poly.t :=
    List.repeat [] (List.length compiled.(CompiledSystem.gates)).

  Lemma gates_agree_zero (domain : Domain.t) (w : Z) (s : nat)
      (compiled : CompiledSystem.t) (grid : RawGrid.t)
      (Hn : Domain.n domain = Z.of_nat (2 ^ s))
      (Hhold :
        PlonkishCompile.compiled_gates_hold domain compiled
          (cgrid compiled grid)) :
    gates_agree w s compiled grid (zero_gate_polys compiled).
  Proof.
    unfold zero_gate_polys.
    split; [apply List.repeat_length |].
    intros i Hi j Hj.
    rewrite List.repeat_length in Hi.
    rewrite List.nth_repeat.
    cbn [Poly.eval].
    symmetry.
    apply (Hhold (Z.of_nat j)); [rewrite Hn; lia |].
    apply List.nth_In.
    exact Hi.
  Qed.

End WithPrime.

End PlonkishAlgebraic.
