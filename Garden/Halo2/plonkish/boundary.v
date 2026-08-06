(** * The proof-system boundary: named external hypotheses and the single-challenge corollary.

    The refinement ladder proves the algebraic layer ([algebraic.v]) down
    from the *all-challenge* acceptance [algebraic_accepts]; the deployed
    verifier checks the same identities at *one* challenge tuple
    [(θ, β, γ, y)] derived by the Fiat–Shamir transcript, against
    commitments opened through the IPA.  This file names the residual
    external content of that gap — never as axioms, always as documented
    hypotheses in the style of [OrchardBundle.SignatureKnowledge] — and
    proves the in-model part: by the counting lemmas ([counting.v]),
    verifier-style acceptance at a single challenge tuple outside the
    instance's bounded bad sets already yields the compiled-plonkish
    satisfaction triple of [PlonkishAlgebraic.algebraic_sound].

    The named external hypotheses, for a future L0 composition:

    - [IPABinding]: one commitment opens to at most one polynomial;
    - [MultiopenReduction]: an accepted multipoint opening pins every
      claimed evaluation to the committed polynomial's true evaluation;
    - [FiatShamirChallengeGood]: a transcript-derived challenge avoids a
      specific, cardinality-bounded bad set.

    The in-model corollaries, over the [algebraic.v] instance data:

    - [algebraic_sound_at_challenge]: single-tuple acceptance
      ([algebraic_accepts_at]) plus goodness of the tuple
      ([challenges_good] — the tuple avoids the three per-family bad
      sets, whose cardinality bounds are
      [PlonkishCounting.vanishing_bad_card] (≤ #gates − 1),
      [PlonkishCounting.permutation_bad_card] (nested [N] × [2·N]), and
      [PlonkishCounting.lookup_theta_bad_card] /
      [PlonkishCounting.lookup_pair_grid_bound] (≤ u·m, resp. [2·u]
      grid sides)) implies the R2 satisfaction triple;
    - [algebraic_accepts_at_cases]: without any goodness premise,
      acceptance implies the triple or membership of the tuple in one of
      the bad sets, with the cardinality bounds carried in the
      disjunction. *)

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
Require Import Garden.Halo2.plonkish.algebraic.
Require Import Garden.Halo2.plonkish.counting.

Import List.ListNotations.
Import Plonkish.
Global Open Scope Z_scope.

Module PlonkishBoundary.

Section WithPrime.
  Context {p : Z}.
  Context `{Prime p}.

  (** ** [IPABinding] — polynomial-commitment binding

      The inner-product-argument commitment scheme over the Vesta group
      ([halo2_proofs/src/poly/commitment/]).  The semantic content an L0
      composition consumes: one commitment opens to at most one
      polynomial (up to coefficientwise equality mod [p]).  Stated over
      an abstract commitment space and opening relation; discharging it
      for the concrete IPA is the discrete-log (group-model) content of
      the Halo 2 polynomial commitment and stays a hypothesis at this
      layer — the reduction-style analogue of
      [OrchardBundle.SignatureKnowledge]. *)
  Definition IPABinding (Commitment : Type)
      (opens : Commitment -> Poly.t -> Prop) : Prop :=
    forall (C : Commitment) (f g : Poly.t),
      opens C f -> opens C g -> Poly.peq (p := p) f g.

  (** ** [MultiopenReduction] — the multipoint opening argument

      The batch opening layer ([halo2_proofs/src/poly/multiopen.rs])
      reduces the verifier's many claimed evaluations to one IPA check.
      The content an L0 composition consumes: if the multiopen check
      accepts a query set, every claimed evaluation [(C, (x, v))] in it
      is the true evaluation at [x] of any polynomial [C] opens to.
      Together with [IPABinding] this turns the transcript's claimed
      evaluations into facts about the committed column polynomials.
      Stays a named hypothesis. *)
  Definition MultiopenReduction (Commitment : Type)
      (opens : Commitment -> Poly.t -> Prop)
      (multiopen_valid : list (Commitment * (Z * Z)) -> Prop) : Prop :=
    forall queries : list (Commitment * (Z * Z)),
      multiopen_valid queries ->
      forall (C : Commitment) (x v : Z),
        List.In (C, (x, v)) queries ->
        forall f : Poly.t,
          opens C f -> Poly.eval (p := p) f x = v mod p.

  (** ** [FiatShamirChallengeGood] — transcript-challenge goodness

      The verifier's challenges are hash digests of the transcript
      prefix ([halo2_proofs/src/transcript.rs], BLAKE2b).  The
      random-oracle content an L0 composition consumes: a hash-derived
      challenge does not land in a *specific, instance-determined* bad
      set.  It must only ever be assumed for bad sets carrying a proved
      cardinality bound ([PlonkishCounting.card_at_most bad d] with [d]
      far below [p]), so the assumption's quantitative content is
      exactly "the transcript hash avoids a set of density [d / p]" —
      the counting lemmas of [counting.v] supply those bounds.  Stays a
      named hypothesis. *)
  Definition FiatShamirChallengeGood (bad : Z -> Prop) (challenge : Z)
      : Prop :=
    ~ bad challenge.

  (** ** The single-challenge corollary

      Over the exact instance data of
      [PlonkishAlgebraic.Soundness]: the compiled system and its replayed
      witness grid, the permutation reading, and the gate-combination
      polynomials [Es]. *)

  Section SingleChallenge.
    Variable domain : Domain.t.
    Variable w : Z.
    Variable s : nat.
    Hypothesis Hs : (1 <= s)%nat.
    Hypothesis Hp2 : 2 < p.
    Hypothesis Hw_full : Fpow w (2 ^ Z.of_nat s) = 1.
    Hypothesis Hn : Domain.n domain = Z.of_nat (2 ^ s).

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
    Variable ncols chunk_len : nat.
    Variable gperm lbl : Sigma.cell -> Z.
    Variable assembly : Sigma.t.
    Variable Es : list Poly.t.

    Local Notation cgrid := (PlonkishAlgebraic.cgrid compiled grid).
    Local Notation apf arg :=
      (PlonkishLookupPoly.argument_pair_functions
        (grid_assignment cgrid) tt arg).

    (** Verifier-style acceptance at one challenge tuple [(θ, β, γ, y)]:
        the polynomials [Es] agree with the compiled gates on [H], the
        quotient identity holds at [y], the permutation product rules
        hold at [(β, γ)], and every compiled lookup argument's five rules
        hold at [(θ, β, γ)] — each family with its per-challenge
        witnesses ([h], [zs], [A'], [S'], [Z]) chosen freely. *)
    Definition algebraic_accepts_at (theta beta gamma y : Z) : Prop :=
      PlonkishAlgebraic.gates_agree (p := p) w s compiled grid Es /\
      PlonkishCounting.vanishing_accepts_at (p := p) s Es y /\
      PlonkishCounting.permutation_accepts_at (p := p) domain ncols
        chunk_len gperm lbl (Sigma.perm assembly) beta gamma /\
      List.Forall
        (fun arg : LookupArgument.t Configure.indexed_columns =>
          PlonkishCounting.lookup_accepts_at (p := p) domain (apf arg)
            theta beta gamma)
        compiled.(CompiledSystem.lookups).

    (** The tuple avoids the instance's three bad sets — precisely the
        [FiatShamirChallengeGood] assumption for this instance.  The
        bounds: [PlonkishCounting.vanishing_bad_card] ([≤ #gates − 1]),
        [PlonkishCounting.permutation_bad_card] (at most [N] values of
        [β] carry more than [2·N] bad [γ]),
        [PlonkishCounting.lookup_theta_bad_card] ([≤ u·m] per argument)
        with [PlonkishCounting.lookup_pair_grid_bound]. *)
    Definition challenges_good (theta beta gamma y : Z) : Prop :=
      FiatShamirChallengeGood
        (PlonkishCounting.vanishing_bad (p := p) w s Es) y /\
      ~ PlonkishCounting.permutation_bad (p := p) domain ncols chunk_len
          gperm lbl (Sigma.perm assembly) beta gamma /\
      List.Forall
        (fun arg : LookupArgument.t Configure.indexed_columns =>
          ~ PlonkishCounting.lookup_bad (p := p) domain (apf arg)
              table_rows theta beta gamma)
        compiled.(CompiledSystem.lookups).

    (** Row-wise gate vanishing plus the agreement bridge yields the
        compiled-gate conjunct — the challenge-free half of
        [PlonkishAlgebraic.algebraic_gates_sound]. *)
    Lemma gates_vanish_compiled
        (Hagree : PlonkishAlgebraic.gates_agree (p := p) w s compiled grid
          Es)
        (Hvanish : PlonkishCounting.gates_vanish (p := p) w s Es) :
      PlonkishCompile.compiled_gates_hold domain compiled cgrid.
    Proof.
      destruct Hagree as [Hlen Hrows].
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
      rewrite (Hrows i Hi (Z.to_nat row) Hj) in Hzero.
      rewrite Z2Nat.id in Hzero by lia.
      rewrite Hpoly in Hzero.
      exact Hzero.
    Qed.

    (** Tuple membership of every compiled lookup argument yields the
        indexed-system lookup conjunct on the witness grid: on the usable
        rows through the substitution seam
        ([PlonkishLookup.lookup_compile_correct_installed]) and the
        membership reading
        ([PlonkishLookupPoly.membership_eval_lookup_argument]); on the
        blinding rows through the pinned table-row-0 defaults
        ([PlonkishMock.lookups_defaults_all]). *)
    Lemma lookups_membership_sound
        (Hreplay :
          apply_events events (initial_grid advice instance_) = Some grid)
        (Hcompiled :
          compiled =
          Compile.compile system infos num_fixed_columns
            permutation_columns constants)
        (Hur : 0 <= Domain.usable_rows domain)
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
          PlonkishMock.lookup_defaults_of_events_b events system
            table_rows = true)
        (Hmem : List.Forall
          (fun arg : LookupArgument.t Configure.indexed_columns =>
            PlonkishLookupPoly.lookup_membership domain (apf arg)
              table_rows)
          compiled.(CompiledSystem.lookups)) :
      forall row : Z,
      0 <= row < Domain.n domain ->
      List.Forall
        (eval_lookup_argument (grid_assignment grid) (tt, row) table_rows)
        system.(ConstraintSystem.lookups).
    Proof.
      intros row Hrow.
      destruct (Z_lt_le_dec row (Domain.usable_rows domain)) as [Hlt | Hge].
      - apply (proj1 (PlonkishLookup.lookup_compile_correct_installed
          domain system infos num_fixed_columns permutation_columns
          constants grid compiled table_rows
          (f_equal CompiledSystem.lookups Hcompiled)
          (f_equal CompiledSystem.selector_assignments Hcompiled)
          Hact Hexact Hlookup_avoid row Hrow)).
        rewrite List.Forall_forall in Hmem.
        apply List.Forall_forall.
        intros arg Hin.
        apply (proj1 (PlonkishLookupPoly.membership_eval_lookup_argument
          (grid_assignment cgrid) tt arg table_rows row)).
        exact (Hmem arg Hin row (conj (proj1 Hrow) Hlt)).
      - apply (PlonkishMock.lookups_defaults_all events
          (initial_grid advice instance_) grid table_rows system Hreplay
          Hdefaults row).
        intros selector.
        exact (PlonkishMock.grid_selectors_zero_outside events advice
          instance_ grid (Domain.usable_rows domain) row Hreplay Hwithin
          ltac:(lia) selector).
    Qed.

    (** The composed single-challenge corollary: acceptance at one tuple
        outside the bad sets yields the compiled-plonkish satisfaction
        triple of [PlonkishAlgebraic.algebraic_sound] — the same
        conclusion the all-challenge reading gives, with the challenge
        gap reduced to [challenges_good]. *)
    Theorem algebraic_sound_at_challenge
        (theta beta gamma y : Z)
        (Hreplay :
          apply_events events (initial_grid advice instance_) = Some grid)
        (Hcompiled :
          compiled =
          Compile.compile system infos num_fixed_columns
            permutation_columns constants)
        (Hur : 0 <= Domain.usable_rows domain)
        (Hchunk : (0 < chunk_len)%nat)
        (Hfix : forall c : Sigma.cell,
          ~ PermutationPoly.usable_cell domain ncols c ->
          Sigma.perm assembly c = c)
        (Hred : forall c : Sigma.cell,
          PermutationPoly.usable_cell domain ncols c -> 0 <= gperm c < p)
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
          PlonkishMock.lookup_defaults_of_events_b events system
            table_rows = true)
        (Haccept : algebraic_accepts_at theta beta gamma y)
        (Hgood : challenges_good theta beta gamma y) :
      PlonkishCompile.compiled_gates_hold domain compiled cgrid /\
      (forall row : Z,
        0 <= row < Domain.n domain ->
        List.Forall
          (eval_lookup_argument (grid_assignment grid) (tt, row)
            table_rows)
          system.(ConstraintSystem.lookups)) /\
      grid_invariant gperm assembly.
    Proof.
      destruct Haccept as (Hagree & Hy & Hbgacc & Hlk).
      destruct Hgood as (Hy_good & Hbg_good & Hlk_good).
      split; [| split].
      - destruct (PlonkishCounting.gates_vanish_dec (p := p) w s Es)
          as [Hvan | Hnvan].
        + exact (gates_vanish_compiled Hagree Hvan).
        + exfalso. exact (Hy_good (conj Hy Hnvan)).
      - apply (lookups_membership_sound Hreplay Hcompiled Hur Hact Hexact
          Hlookup_avoid Hwithin Hdefaults).
        rewrite List.Forall_forall in Hlk, Hlk_good.
        apply List.Forall_forall.
        intros arg Hin.
        destruct (PlonkishCounting.lookup_membership_dec domain (apf arg)
          table_rows) as [HM | HnM]; [exact HM |].
        exfalso.
        exact (Hlk_good arg Hin (conj (Hlk arg Hin) HnM)).
      - destruct (PlonkishCounting.perm_usable_invariant_dec (p := p)
          domain ncols chunk_len Hchunk gperm lbl (Sigma.perm assembly))
          as [Hinv | Hninv].
        + exact (PlonkishCounting.perm_invariant_grid_invariant (p := p)
            domain ncols chunk_len Hchunk gperm lbl (Sigma.perm assembly)
            assembly (fun c => eq_refl) Hfix Hred Hinv).
        + exfalso. exact (Hbg_good (conj Hbgacc Hninv)).
    Qed.

    (** The case form, with the cardinality bounds carried in the
        disjunction: acceptance at one tuple yields the triple, or the
        tuple lies in one of the three bad sets — each disjunct paired
        with its explicit bound. *)
    Theorem algebraic_accepts_at_cases
        (theta beta gamma y : Z)
        (Hreplay :
          apply_events events (initial_grid advice instance_) = Some grid)
        (Hcompiled :
          compiled =
          Compile.compile system infos num_fixed_columns
            permutation_columns constants)
        (Hk : 0 <= domain.(Domain.k))
        (Hbf : 0 <= domain.(Domain.blinding_factors))
        (Hur : 0 <= Domain.usable_rows domain)
        (Hchunk : (0 < chunk_len)%nat)
        (Hfix : forall c : Sigma.cell,
          ~ PermutationPoly.usable_cell domain ncols c ->
          Sigma.perm assembly c = c)
        (Hred : forall c : Sigma.cell,
          PermutationPoly.usable_cell domain ncols c -> 0 <= gperm c < p)
        (Hinj : forall c d : Sigma.cell,
          PermutationPoly.space_cell domain ncols c ->
          PermutationPoly.space_cell domain ncols d ->
          lbl c mod p = lbl d mod p -> c = d)
        (Hrange : forall c : Sigma.cell,
          PermutationPoly.usable_cell domain ncols c ->
          PermutationPoly.space_cell domain ncols (Sigma.perm assembly c))
        (Htr_pos : 0 < table_rows)
        (Htr_le : table_rows <= Domain.usable_rows domain)
        (Hcanon_events :
          PlonkishAlgebraic.event_fixed_values_ok_b
            (fun value => andb (0 <=? value) (value <? p)) events = true)
        (Hfill :
          PlonkishAlgebraic.tables_fill_row0_b events table_rows
            (Domain.usable_rows domain)
            compiled.(CompiledSystem.lookups) = true)
        (Htables_avoid :
          PlonkishAlgebraic.lookup_tables_avoid_b
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
          PlonkishMock.lookup_defaults_of_events_b events system
            table_rows = true)
        (Haccept : algebraic_accepts_at theta beta gamma y) :
      (PlonkishCompile.compiled_gates_hold domain compiled cgrid /\
       (forall row : Z,
         0 <= row < Domain.n domain ->
         List.Forall
           (eval_lookup_argument (grid_assignment grid) (tt, row)
             table_rows)
           system.(ConstraintSystem.lookups)) /\
       grid_invariant gperm assembly) \/
      (PlonkishCounting.vanishing_bad (p := p) w s Es y /\
       PlonkishCounting.card_at_most (p := p)
         (PlonkishCounting.vanishing_bad (p := p) w s Es)
         (List.length Es - 1)) \/
      (PlonkishCounting.permutation_bad (p := p) domain ncols chunk_len
         gperm lbl (Sigma.perm assembly) beta gamma /\
       PlonkishCounting.pair_card_at_most (p := p)
         (PlonkishCounting.permutation_bad (p := p) domain ncols chunk_len
           gperm lbl (Sigma.perm assembly))
         (List.length (PermutationPoly.all_cells domain ncols chunk_len))
         (2 * List.length
            (PermutationPoly.all_cells domain ncols chunk_len))) \/
      (List.Exists
         (fun arg : LookupArgument.t Configure.indexed_columns =>
           PlonkishCounting.lookup_bad (p := p) domain (apf arg)
             table_rows theta beta gamma)
         compiled.(CompiledSystem.lookups) /\
       List.Forall
         (fun arg : LookupArgument.t Configure.indexed_columns =>
           PlonkishCounting.card_at_most (p := p)
             (PlonkishCounting.lookup_theta_bad (p := p) domain (apf arg)
               table_rows)
             (Z.to_nat (Domain.usable_rows domain) *
              List.length (apf arg)))
         compiled.(CompiledSystem.lookups)).
    Proof.
      destruct Haccept as (Hagree & Hy & Hbgacc & Hlk).
      destruct (PlonkishCounting.gates_vanish_dec (p := p) w s Es)
        as [Hvan | Hnvan].
      2:{ right; left.
          split; [exact (conj Hy Hnvan) |].
          exact (PlonkishCounting.vanishing_bad_card (p := p) w s Hs Hp2
            Hw_full Es). }
      destruct (PlonkishCounting.perm_usable_invariant_dec (p := p)
        domain ncols chunk_len Hchunk gperm lbl (Sigma.perm assembly))
        as [Hinv | Hninv].
      2:{ right; right; left.
          split; [exact (conj Hbgacc Hninv) |].
          exact (PlonkishCounting.permutation_bad_card (p := p) domain
            Hk Hbf Hur ncols chunk_len Hchunk gperm lbl
            (Sigma.perm assembly) Hinj Hrange). }
      destruct (List.Forall_dec
        (fun arg : LookupArgument.t Configure.indexed_columns =>
          PlonkishLookupPoly.lookup_membership domain (apf arg) table_rows)
        (fun arg => PlonkishCounting.lookup_membership_dec domain
          (apf arg) table_rows)
        compiled.(CompiledSystem.lookups)) as [Hmem | HnF].
      2:{ right; right; right.
          split.
          - pose proof (List.neg_Forall_Exists_neg
              (fun arg => PlonkishCounting.lookup_membership_dec domain
                (apf arg) table_rows) HnF) as HexN.
            apply List.Exists_exists in HexN.
            destruct HexN as (arg & Hin & HnM).
            apply List.Exists_exists.
            exists arg.
            split; [exact Hin |].
            rewrite List.Forall_forall in Hlk.
            exact (conj (Hlk arg Hin) HnM).
          - unfold PlonkishAlgebraic.tables_fill_row0_b in Hfill.
            unfold PlonkishAlgebraic.lookup_tables_avoid_b
              in Htables_avoid.
            rewrite List.forallb_forall in Hfill, Htables_avoid.
            apply List.Forall_forall.
            intros arg Hin.
            pose proof (PlonkishAlgebraic.replay_argument_table_canonical
              events advice instance_ grid compiled domain arg Hreplay
              Hcanon_events (Htables_avoid _ Hin)) as Htab.
            pose proof (PlonkishAlgebraic.replay_table_prefix_coherent
              events advice instance_ grid compiled domain table_rows arg
              Hreplay Htr_pos (Hfill _ Hin) (Htables_avoid _ Hin))
              as Hcoh.
            exact (PlonkishCounting.lookup_theta_bad_card (p := p) domain
              (apf arg) table_rows Hbf Hur Htr_pos Htr_le
              (PlonkishLookupPoly.argument_pairs_canonical
                (grid_assignment cgrid) tt domain arg Htab)
              Hcoh). }
      left.
      split; [| split].
      - exact (gates_vanish_compiled Hagree Hvan).
      - exact (lookups_membership_sound Hreplay Hcompiled Hur Hact Hexact
          Hlookup_avoid Hwithin Hdefaults Hmem).
      - exact (PlonkishCounting.perm_invariant_grid_invariant (p := p)
          domain ncols chunk_len Hchunk gperm lbl (Sigma.perm assembly)
          assembly (fun c => eq_refl) Hfix Hred Hinv).
    Qed.

  End SingleChallenge.

End WithPrime.

End PlonkishBoundary.
