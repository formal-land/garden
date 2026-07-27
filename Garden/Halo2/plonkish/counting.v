(** * Schwartz–Zippel counting: finite challenge sets replace the all-challenge quantifiers.

    The R3 identity families ([vanishing.v], [permutation_poly.v],
    [lookup_poly.v]) read acceptance with every verifier challenge
    universally quantified.  The deployed verifier checks the identities at
    one challenge tuple sampled by the Fiat–Shamir transcript; the gap
    between the two readings is the random-challenge step of the proof
    system.  This file states that step as pure finite-cardinality lemmas —
    no probability theory — built on the root bound
    ([Poly.roots_le_pdeg] / [Poly.zero_of_roots]):

    - per family, a *counting theorem*: acceptance on a repetition-free
      challenge set of an explicit instance-derived size forces the grid
      property the R3 soundness lemma extracts (row-wise gate vanishing,
      σ-invariance on the usable cells, lookup membership);
    - per family, a *bad set* — the challenges at which the identity holds
      although the grid property fails — with an explicit cardinality
      bound derived from the counting theorem: any repetition-free list of
      bad challenges is no longer than the bound;
    - per family, a *case corollary*: acceptance at one challenge tuple
      yields the grid property or membership of the tuple in the bounded
      bad set.

    The concrete bounds, with [N] the permutation cell count and
    [u = usable_rows]:

    - vanishing ([plonk/vanishing/verifier.rs]): the bad-[y] set has at
      most [#gates − 1] residues — a nonzero challenge polynomial with the
      gate evaluations as coefficients has fewer roots than gates;
    - permutation ([plonk/permutation/verifier.rs]): the set of [β] whose
      accepting-[γ] slice exceeds [2·N] residues has at most [N] elements
      (the nested reading of "the bad [(β, γ)] set has at most [3·N·p]
      pairs");
    - lookup ([plonk/lookup/verifier.rs]): the set of [θ] at which the
      combined values agree row-wise but tuple membership fails has at most
      [u·m] residues ([m] the pair count), and for a [θ] without row-wise
      agreement no acceptance grid with both sides beyond [2·u] distinct
      challenges exists.

    The counting theorems re-run the R3 soundness arguments with the
    instantiation pools generalized from the canonical residue pools
    ([PermutationPoly.zpool], [PlonkishLookupPoly.pick_good_points]) to
    arbitrary repetition-free challenge lists; the finite grid properties
    are decidable ([gates_vanish_dec], [perm_usable_invariant_dec],
    [lookup_membership_dec]), which keeps the case corollaries
    constructive.  The single-challenge acceptance composition down to the
    compiled-plonkish triple is [boundary.v]'s job. *)

Require Import Stdlib.Bool.Bool.
Require Import Stdlib.micromega.Lia.
Require Import Garden.Field.Field.
Require Import Garden.Field.Div.
Require Import Garden.Field.Lemmas.
Require Import Garden.Halo2.lemmas.
Require Import Garden.Halo2.main.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.serialize.
Require Import Garden.Halo2.plonkish.main.
Require Import Garden.Halo2.plonkish.sigma.
Require Import Garden.Halo2.plonkish.poly.
Require Import Garden.Halo2.plonkish.vanishing.
Require Import Garden.Halo2.plonkish.permutation_poly.
Require Import Garden.Halo2.plonkish.lookup_poly.

Import List.ListNotations.
Import Plonkish.
Global Open Scope Z_scope.

Module PlonkishCounting.

(** ** Decidability of bounded quantifications

    The grid properties the counting lemmas conclude are finite
    conjunctions of decidable equalities; these helpers decide them, so
    the case corollaries stay free of classical axioms. *)

Lemma forall_bound_dec (P : nat -> Prop) (n : nat)
    (Hdec : forall k : nat, (k < n)%nat -> {P k} + {~ P k}) :
  {forall k : nat, (k < n)%nat -> P k} +
  {~ forall k : nat, (k < n)%nat -> P k}.
Proof.
  induction n as [| n IH].
  - left. intros k Hk. lia.
  - assert (Hdec' : forall k : nat, (k < n)%nat -> {P k} + {~ P k})
      by (intros k Hk; apply Hdec; lia).
    destruct (IH Hdec') as [Hall | Hnot].
    + destruct (Hdec n (Nat.lt_succ_diag_r n)) as [Hn | Hn].
      * left. intros k Hk.
        destruct (Nat.eq_dec k n) as [-> | Hne]; [exact Hn |].
        apply Hall. lia.
      * right. intros Hall'. exact (Hn (Hall' n (Nat.lt_succ_diag_r n))).
    + right. intros Hall'. apply Hnot. intros k Hk. apply Hall'. lia.
Qed.

Lemma exists_bound_dec (P : nat -> Prop) (n : nat)
    (Hdec : forall k : nat, (k < n)%nat -> {P k} + {~ P k}) :
  {exists k : nat, (k < n)%nat /\ P k} +
  {~ exists k : nat, (k < n)%nat /\ P k}.
Proof.
  induction n as [| n IH].
  - right. intros (k & Hk & _). lia.
  - assert (Hdec' : forall k : nat, (k < n)%nat -> {P k} + {~ P k})
      by (intros k Hk; apply Hdec; lia).
    destruct (IH Hdec') as [Hex | Hnot].
    + left. destruct Hex as (k & Hk & HP). exists k. split; [lia | exact HP].
    + destruct (Hdec n (Nat.lt_succ_diag_r n)) as [Hn | Hn].
      * left. exists n. split; [lia | exact Hn].
      * right. intros (k & Hk & HP).
        destruct (Nat.eq_dec k n) as [-> | Hne]; [exact (Hn HP) |].
        apply Hnot. exists k. split; [lia | exact HP].
Qed.

Lemma forall_range_Z_dec (P : Z -> Prop) (hi : Z)
    (Hdec : forall z : Z, 0 <= z < hi -> {P z} + {~ P z}) :
  {forall z : Z, 0 <= z < hi -> P z} +
  {~ forall z : Z, 0 <= z < hi -> P z}.
Proof.
  destruct (forall_bound_dec (fun j => P (Z.of_nat j)) (Z.to_nat hi))
    as [Hall | Hnot].
  - intros k Hk. apply Hdec. lia.
  - left. intros z Hz.
    replace z with (Z.of_nat (Z.to_nat z)) by lia.
    apply Hall. lia.
  - right. intros Hall. apply Hnot. intros j Hj. apply Hall. lia.
Qed.

Lemma exists_range_Z_dec (P : Z -> Prop) (hi : Z)
    (Hdec : forall z : Z, 0 <= z < hi -> {P z} + {~ P z}) :
  {exists z : Z, 0 <= z < hi /\ P z} +
  {~ exists z : Z, 0 <= z < hi /\ P z}.
Proof.
  destruct (exists_bound_dec (fun j => P (Z.of_nat j)) (Z.to_nat hi))
    as [Hex | Hnot].
  - intros k Hk. apply Hdec. lia.
  - left. destruct Hex as (j & Hj & HP).
    exists (Z.of_nat j). split; [lia | exact HP].
  - right. intros (z & Hz & HP). apply Hnot.
    exists (Z.to_nat z). split; [lia |].
    replace (Z.of_nat (Z.to_nat z)) with z by lia.
    exact HP.
Qed.

(** A list mapping without repetition has no repetition itself. *)
Lemma NoDup_of_map {A B : Type} (f : A -> B) (l : list A) :
  List.NoDup (List.map f l) -> List.NoDup l.
Proof.
  induction l as [| a l IH]; cbn [List.map]; intros Hnd; [constructor |].
  inversion Hnd as [| ? ? Hnotin Hnd']; subst.
  constructor; [| exact (IH Hnd')].
  intros Hin. exact (Hnotin (List.in_map f l a Hin)).
Qed.

(** Tuple membership of one lookup argument is a finite decidable
    property ([PlonkishLookupPoly.lookup_membership] carries no modulus:
    it compares raw values). *)
Lemma lookup_membership_dec (domain : Domain.t)
    (pairs : list ((Z -> Z) * (Z -> Z))) (table_rows : Z) :
  {PlonkishLookupPoly.lookup_membership domain pairs table_rows} +
  {~ PlonkishLookupPoly.lookup_membership domain pairs table_rows}.
Proof.
  unfold PlonkishLookupPoly.lookup_membership.
  apply forall_range_Z_dec.
  intros row _.
  apply exists_range_Z_dec.
  intros t _.
  apply List.Forall_dec.
  intros fg.
  destruct (Z.eq_dec (fst fg row) (snd fg t)) as [He | He];
    [left; exact He | right; exact He].
Qed.

Section WithPrime.
  Context {p : Z}.
  Context `{Prime p}.

  (** ** Cardinality vocabulary

      A subset of the field is read as a predicate on [Z], with
      cardinality measured against repetition-free residue lists
      ([Poly.NoDupP]): [card_at_most S d] says no [d + 1] pairwise
      distinct residues all satisfy [S]. *)

  Definition card_at_most (S : Z -> Prop) (d : nat) : Prop :=
    forall ys : list Z,
      Poly.NoDupP (p := p) ys ->
      List.Forall S ys ->
      (List.length ys <= d)%nat.

  (** The [β]-slice of a challenge-pair set is *large* when it holds more
      than [dg] distinct [γ] residues. *)
  Definition pair_slice_large (S : Z -> Z -> Prop) (dg : nat) (beta : Z)
      : Prop :=
    exists gammas : list Z,
      Poly.NoDupP (p := p) gammas /\
      (dg < List.length gammas)%nat /\
      List.Forall (S beta) gammas.

  (** A pair set is small when at most [db] distinct [β] carry a large
      slice — the nested-quantifier reading of "at most
      [db·p + p·dg] pairs". *)
  Definition pair_card_at_most (S : Z -> Z -> Prop) (db dg : nat) : Prop :=
    card_at_most (pair_slice_large S dg) db.

  (** ** Selection from repetition-free pools, avoiding a residue list

      The generalization of the canonical pools of the R3 proofs
      ([PermutationPoly.zpool], [PlonkishLookupPoly.pick_good_points]):
      any repetition-free pool with room beyond the avoided list yields a
      repetition-free selection of the requested size. *)

  (** ** The vanishing family

      [vanishing_accepts_at Es y] is the single-challenge quotient
      identity the verifier checks at its sampled [y]
      ([plonk/vanishing/verifier.rs], the Horner fold order of
      [Vanishing.combine_horner]); [gates_vanish] is the row-wise gate
      vanishing the R3 equivalence extracts.  Acceptance at [#gates]
      distinct challenges forces the property; the bad set is bounded by
      [#gates − 1]. *)

  Section VanishingCounting.
    Variable w : Z.
    Variable s : nat.
    Hypothesis Hs : (1 <= s)%nat.
    Hypothesis Hp2 : 2 < p.
    Hypothesis Hw_full : Fpow w (2 ^ Z.of_nat s) = 1.

    Definition gates_vanish (Es : list Poly.t) : Prop :=
      forall i : nat, (i < List.length Es)%nat ->
      forall j : nat, (j < 2 ^ s)%nat ->
      Poly.eval (p := p) (List.nth i Es []) (Fpow w (Z.of_nat j)) = 0.

    Definition vanishing_accepts_at (Es : list Poly.t) (y : Z) : Prop :=
      exists h : Poly.t,
        Poly.peq (p := p) (Vanishing.combine_horner (p := p) y Es)
          (Poly.pmul (p := p) h (Poly.xn1 (p := p) (2 ^ s)%nat)).

    Lemma gates_vanish_dec (Es : list Poly.t) :
      {gates_vanish Es} + {~ gates_vanish Es}.
    Proof.
      apply forall_bound_dec.
      intros i _.
      apply forall_bound_dec.
      intros j _.
      destruct (Z.eq_dec
        (Poly.eval (p := p) (List.nth i Es []) (Fpow w (Z.of_nat j))) 0)
        as [He | He]; [left; exact He | right; exact He].
    Qed.

    (** The counting theorem: acceptance on a repetition-free challenge
        list at least as long as the gate list forces row-wise vanishing —
        at each domain point the gate evaluations are the coefficients of
        a challenge polynomial with more roots than significant
        coefficients ([Poly.zero_of_roots]). *)
    Theorem vanishing_counting (Es : list Poly.t) (ys : list Z)
        (Hnd : Poly.NoDupP (p := p) ys)
        (Hlen : (List.length Es <= List.length ys)%nat)
        (Haccept : forall y, List.In y ys -> vanishing_accepts_at Es y) :
      gates_vanish Es.
    Proof.
      intros i Hi j Hj.
      set (x := Fpow w (Z.of_nat j)).
      set (A := List.map (fun E => Poly.eval (p := p) E x) (List.rev Es)).
      assert (HA : forall y, List.In y ys -> Poly.eval (p := p) A y = 0).
      { intros y Hy.
        destruct (Haccept y Hy) as [h Hh].
        unfold A.
        rewrite <- Vanishing.eval_combine.
        rewrite <- (Poly.eval_peq (p := p) _ _ x
          (Vanishing.combine_horner_rev (p := p) y Es)).
        rewrite (Poly.eval_peq (p := p) _ _ x Hh).
        rewrite Poly.eval_pmul.
        unfold x.
        rewrite (Vanishing.xn1_domain_root w s Hs Hp2 Hw_full j Hj).
        rewrite Z.mul_0_r.
        apply Zmod_0_l. }
      assert (Hnil : Poly.norm (p := p) A = []).
      { apply (Poly.zero_of_roots (p := p) A ys Hnd).
        - rewrite List.Forall_forall. exact HA.
        - eapply Nat.le_trans; [apply Vanishing.pdeg_le_length |].
          unfold A.
          rewrite List.length_map, List.length_rev.
          exact Hlen. }
      pose proof (Poly.norm_nil_coef (p := p) A Hnil
        (List.length Es - S i)%nat) as Hc.
      unfold Poly.coef in Hc.
      assert (Hnth : List.nth (List.length Es - S i) A 0 =
        Poly.eval (p := p)
          (List.nth (List.length Es - S i) (List.rev Es) []) x).
      { unfold A.
        exact (List.map_nth (fun E => Poly.eval (p := p) E x)
          (List.rev Es) [] (List.length Es - S i)%nat). }
      rewrite Hnth in Hc.
      rewrite List.rev_nth in Hc by lia.
      replace (List.length Es - S (List.length Es - S i))%nat with i in Hc
        by lia.
      rewrite Poly.eval_canonical in Hc.
      exact Hc.
    Qed.

    (** The bad set: challenges accepted although some gate fails
        somewhere on the domain.  Any repetition-free bad list is shorter
        than the gate list. *)
    Definition vanishing_bad (Es : list Poly.t) (y : Z) : Prop :=
      vanishing_accepts_at Es y /\ ~ gates_vanish Es.

    Theorem vanishing_bad_card (Es : list Poly.t) :
      card_at_most (vanishing_bad Es) (List.length Es - 1).
    Proof.
      intros ys Hnd HF.
      destruct (Compare_dec.le_lt_dec (List.length ys)
        (List.length Es - 1)%nat) as [Hle | Hgt]; [exact Hle |].
      exfalso.
      destruct ys as [| y0 ys']; [cbn in Hgt; lia |].
      inversion HF as [| ? ? Hbad0 HFrest]; subst.
      destruct Hbad0 as [_ HnP].
      apply HnP.
      destruct (Nat.eq_dec (List.length Es) 0) as [HEs0 | HEsn].
      - intros i Hi. lia.
      - apply (vanishing_counting Es (y0 :: ys') Hnd);
          [cbn [List.length] in *; lia |].
        intros y Hy.
        rewrite List.Forall_forall in HF.
        exact (proj1 (HF y Hy)).
    Qed.

    (** The case corollary, with the bound explicit. *)
    Corollary vanishing_accept_cases (Es : list Poly.t) (y : Z)
        (Haccept : vanishing_accepts_at Es y) :
      gates_vanish Es \/
      (vanishing_bad Es y /\
       card_at_most (vanishing_bad Es) (List.length Es - 1)).
    Proof.
      destruct (gates_vanish_dec Es) as [HP | HnP].
      - left. exact HP.
      - right.
        split; [exact (conj Haccept HnP) | apply vanishing_bad_card].
    Qed.

  End VanishingCounting.

  (** ** The permutation family

      The counting reading of [PermutationPoly.permutation_sound]: the
      canonical instantiation pools of the R3 proof are generalized to
      arbitrary repetition-free challenge lists — a [β] pool of
      [N + 1] residues ([N = length all_cells]) whose every member
      carries an accepting [γ] pool of [2·N + 1] residues forces
      σ-invariance on the usable cells. *)

  Section PermutationCounting.
    Variable domain : Domain.t.
    Hypothesis Hk : 0 <= domain.(Domain.k).
    Hypothesis Hbf : 0 <= domain.(Domain.blinding_factors).
    Hypothesis Hur : 0 <= Domain.usable_rows domain.
    Variables ncols chunk_len : nat.
    Hypothesis Hchunk : (0 < chunk_len)%nat.
    Variables g lbl : Sigma.cell -> Z.
    Variable sigma : Sigma.cell -> Sigma.cell.

    Local Notation all_cells :=
      (PermutationPoly.all_cells domain ncols chunk_len).
    Local Notation usable_cell := (PermutationPoly.usable_cell domain ncols).
    Local Notation space_cell := (PermutationPoly.space_cell domain ncols).
    Local Notation iprod :=
      (PermutationPoly.iprod (p := p) domain ncols chunk_len g lbl).
    Local Notation sprod :=
      (PermutationPoly.sprod (p := p) domain ncols chunk_len g lbl sigma).
    Local Notation iroots :=
      (PermutationPoly.iroots domain ncols chunk_len g lbl).
    Local Notation sroots :=
      (PermutationPoly.sroots domain ncols chunk_len g lbl sigma).

    (** The single-challenge acceptance of the four product rules
        ([plonk/permutation/verifier.rs], [Evaluated::expressions]) at one
        [(β, γ)] pair, with the running products chosen per challenge. *)
    Definition permutation_accepts_at (beta gamma : Z) : Prop :=
      exists zs : list (Z -> Z),
        PermutationPoly.permutation_rules (p := p) domain ncols chunk_len
          g lbl sigma beta gamma zs.

    (** The grid property the R3 soundness lemma extracts: every usable
        cell has a usable σ-image carrying the same residue. *)
    Definition perm_usable_invariant : Prop :=
      forall c : Sigma.cell,
        usable_cell c ->
        usable_cell (sigma c) /\ g c mod p = g (sigma c) mod p.

    Lemma usable_cell_dec (c : Sigma.cell) :
      {usable_cell c} + {~ usable_cell c}.
    Proof.
      destruct (Compare_dec.le_lt_dec ncols (fst c)) as [H1 | H1];
        [right; intros [Hc1 _]; lia |].
      destruct (Compare_dec.le_lt_dec (PermutationPoly.un domain) (snd c))
        as [H2 | H2]; [right; intros [_ Hc2]; lia |].
      left. exact (conj H1 H2).
    Qed.

    Lemma perm_usable_invariant_dec :
      {perm_usable_invariant} + {~ perm_usable_invariant}.
    Proof.
      set (Q := fun c : Sigma.cell =>
        usable_cell (sigma c) /\ g c mod p = g (sigma c) mod p).
      assert (HQdec : forall c : Sigma.cell, {Q c} + {~ Q c}).
      { intros c. unfold Q.
        destruct (usable_cell_dec (sigma c)) as [Hu | Hu];
          [| right; intros [Hu' _]; exact (Hu Hu')].
        destruct (Z.eq_dec (g c mod p) (g (sigma c) mod p)) as [He | He];
          [| right; intros [_ He']; exact (He He')].
        left. exact (conj Hu He). }
      destruct (forall_bound_dec
        (fun i => forall j : nat,
          (j < PermutationPoly.un domain)%nat -> Q (i, j)) ncols
        (fun i _ => forall_bound_dec (fun j => Q (i, j))
          (PermutationPoly.un domain) (fun j _ => HQdec (i, j))))
        as [Hall | Hnot].
      - left. intros c Hc.
        destruct c as [i j].
        destruct Hc as [H1 H2].
        exact (Hall i H1 j H2).
      - right. intros Hinv. apply Hnot.
        intros i Hi j Hj.
        exact (Hinv (i, j) (conj Hi Hj)).
    Qed.

    (** The counting theorem: an accepting [(N + 1) × (2·N + 1)] nested
        challenge family forces σ-invariance on the usable cells, under
        the same label-injectivity and range side conditions as
        [PermutationPoly.permutation_sound]. *)
    Theorem permutation_counting
        (Hinj : forall c d, space_cell c -> space_cell d ->
          lbl c mod p = lbl d mod p -> c = d)
        (Hrange : forall c, usable_cell c -> space_cell (sigma c))
        (betas : list Z)
        (Hnb : Poly.NoDupP (p := p) betas)
        (Hlb : (List.length all_cells + 1 <= List.length betas)%nat)
        (Hslice : forall beta, List.In beta betas ->
          exists gammas : list Z,
            Poly.NoDupP (p := p) gammas /\
            (2 * List.length all_cells + 1 <= List.length gammas)%nat /\
            forall gamma, List.In gamma gammas ->
              permutation_accepts_at beta gamma) :
      perm_usable_invariant.
    Proof.
      intros c Hc.
      assert (Hslice' : forall beta, List.In beta betas ->
        exists gammas : list Z,
          Poly.NoDupP (p := p) gammas /\
          (2 * List.length all_cells + 1 <= List.length gammas)%nat /\
          forall gamma, List.In gamma gammas ->
            iprod beta gamma = 0 \/ iprod beta gamma = sprod beta gamma).
      { intros beta Hbin.
        destruct (Hslice beta Hbin) as (gammas & Hndg & Hleng & Hacc).
        exists gammas.
        split; [exact Hndg |].
        split; [exact Hleng |].
        intros gamma Hgin.
        exact (PermutationPoly.rules_products domain Hk Hbf Hur
          ncols chunk_len Hchunk g lbl sigma beta gamma (Hacc gamma Hgin)). }
      destruct (PermutationPoly.match_cell_of_pools domain ncols chunk_len
        Hchunk g lbl sigma betas Hnb Hlb Hslice' c
        (proj2 (PermutationPoly.in_all_cells domain ncols chunk_len Hchunk c)
          Hc)) as (d & Hdin & Hgd & Hld).
      assert (Hd : d = sigma c).
      { apply Hinj.
        - apply (PermutationPoly.usable_cell_space domain Hk Hbf
            ncols chunk_len Hchunk g lbl sigma).
          apply (proj1 (PermutationPoly.in_all_cells domain ncols chunk_len
            Hchunk d)).
          exact Hdin.
        - exact (Hrange c Hc).
        - exact Hld. }
      subst d.
      split.
      - apply (proj1 (PermutationPoly.in_all_cells domain ncols chunk_len
          Hchunk (sigma c))).
        exact Hdin.
      - symmetry. exact Hgd.
    Qed.

    (** The composition into [sigma.v]'s [grid_invariant], for [σ] the
        permutation of a closed assembly fixing every non-usable cell over
        a reduced grid — the counting analogue of
        [PermutationPoly.permutation_sound_grid_invariant]. *)
    Theorem perm_invariant_grid_invariant (assembly : Sigma.t)
        (Hsig : forall c, sigma c = Sigma.perm assembly c)
        (Hfix : forall c, ~ usable_cell c -> sigma c = c)
        (Hred : forall c, usable_cell c -> 0 <= g c < p)
        (Hinv : perm_usable_invariant) :
      grid_invariant g assembly.
    Proof.
      intro c.
      rewrite <- Hsig.
      destruct (usable_cell_dec c) as [Hc | Hc].
      - destruct (Hinv c Hc) as [Hu Hg2].
        rewrite <- (Z.mod_small (g c) p (Hred c Hc)).
        rewrite <- (Z.mod_small (g (sigma c)) p (Hred (sigma c) Hu)).
        exact Hg2.
      - rewrite Hfix; [reflexivity | exact Hc].
    Qed.

    (** The bad set: pairs accepted although σ-invariance fails somewhere
        on the usable cells, bounded in the nested reading — at most [N]
        distinct [β] carry more than [2·N] distinct bad [γ]. *)
    Definition permutation_bad (beta gamma : Z) : Prop :=
      permutation_accepts_at beta gamma /\ ~ perm_usable_invariant.

    Theorem permutation_bad_card
        (Hinj : forall c d, space_cell c -> space_cell d ->
          lbl c mod p = lbl d mod p -> c = d)
        (Hrange : forall c, usable_cell c -> space_cell (sigma c)) :
      pair_card_at_most permutation_bad
        (List.length all_cells) (2 * List.length all_cells).
    Proof.
      intros betas Hnb HF.
      destruct (Compare_dec.le_lt_dec (List.length betas)
        (List.length all_cells)) as [Hle | Hgt]; [exact Hle |].
      exfalso.
      destruct betas as [| b0 betas']; [cbn in Hgt; lia |].
      inversion HF as [| ? ? Hb0 HFrest]; subst.
      destruct Hb0 as (gammas0 & Hnd0 & Hlen0 & Hall0).
      destruct gammas0 as [| g0 gs0]; [cbn in Hlen0; lia |].
      inversion Hall0 as [| ? ? Hbad0 Hrest0]; subst.
      destruct Hbad0 as [_ HnP].
      apply HnP.
      apply (permutation_counting Hinj Hrange (b0 :: betas') Hnb
        ltac:(cbn [List.length] in *; lia)).
      intros beta Hbin.
      rewrite List.Forall_forall in HF.
      destruct (HF beta Hbin) as (gammas & Hndg & Hleng & Hall).
      exists gammas.
      split; [exact Hndg |].
      split; [lia |].
      intros gamma Hgin.
      rewrite List.Forall_forall in Hall.
      exact (proj1 (Hall gamma Hgin)).
    Qed.

    (** The case corollary, with the nested bound explicit. *)
    Corollary permutation_accept_cases
        (Hinj : forall c d, space_cell c -> space_cell d ->
          lbl c mod p = lbl d mod p -> c = d)
        (Hrange : forall c, usable_cell c -> space_cell (sigma c))
        (beta gamma : Z)
        (Haccept : permutation_accepts_at beta gamma) :
      perm_usable_invariant \/
      (permutation_bad beta gamma /\
       pair_card_at_most permutation_bad
         (List.length all_cells) (2 * List.length all_cells)).
    Proof.
      destruct perm_usable_invariant_dec as [HP | HnP].
      - left. exact HP.
      - right.
        split; [exact (conj Haccept HnP) |].
        exact (permutation_bad_card Hinj Hrange).
    Qed.

  End PermutationCounting.

  (** ** The lookup family

      The counting reading of [PlonkishLookupPoly.lookup_sound], split at
      its two challenge layers.  The per-[θ] multiset step is
      [PlonkishLookupPoly.per_theta_membership_of_pools], stated over the
      bounded challenge pools this layer supplies.
      [lookup_theta_counting] generalizes the [θ]-de-combination
      pigeonhole: row-wise combined agreement at [u·m + 1] distinct [θ]
      forces tuple membership. *)

  Local Notation comb_input := (@PlonkishLookupPoly.comb_input p).
  Local Notation comb_table := (@PlonkishLookupPoly.comb_table p).
  Local Notation prodl := (@PlonkishLookupPoly.prodl p).
  Local Notation lookup_rules_hold :=
    (@PlonkishLookupPoly.lookup_rules_hold p).
  Local Notation lookup_challenge_regular :=
    (@PlonkishLookupPoly.lookup_challenge_regular p).


  (** Row-wise combined agreement at one [θ] — the property the per-[θ]
      step yields and the [θ]-pigeonhole consumes. *)
  Definition lookup_comb_agree (domain : Domain.t)
      (pairs : list ((Z -> Z) * (Z -> Z))) (theta : Z) : Prop :=
    forall row : Z, 0 <= row < Domain.usable_rows domain ->
    exists t : nat, (t < Z.to_nat (Domain.usable_rows domain))%nat /\
      comb_input pairs theta row = comb_table pairs theta (Z.of_nat t).

  Lemma lookup_comb_agree_dec (domain : Domain.t)
      (pairs : list ((Z -> Z) * (Z -> Z))) (theta : Z) :
    {lookup_comb_agree domain pairs theta} +
    {~ lookup_comb_agree domain pairs theta}.
  Proof.
    apply forall_range_Z_dec.
    intros row _.
    apply exists_bound_dec.
    intros t _.
    exact (Z.eq_dec (comb_input pairs theta row)
      (comb_table pairs theta (Z.of_nat t))).
  Qed.

  (** The [θ]-level counting theorem: row-wise combined agreement at
      [u·m + 1] distinct [θ] de-combines into tuple membership — over
      that many challenge points some table row witnesses [m] of them,
      and two degree-[< m] polynomials agreeing on [m] repetition-free
      points have equal coefficients, the tuples themselves
      ([Poly.interpolant_unique]).  The generalization of the pigeonhole
      half of [PlonkishLookupPoly.lookup_sound]. *)
  Theorem lookup_theta_counting (domain : Domain.t)
      (pairs : list ((Z -> Z) * (Z -> Z))) (table_rows : Z)
      (Hbf : 0 <= domain.(Domain.blinding_factors))
      (Hu : 0 <= Domain.usable_rows domain)
      (Htr_pos : 0 < table_rows)
      (Htr_le : table_rows <= Domain.usable_rows domain)
      (Hcanon : PlonkishLookupPoly.pairs_canonical (p := p) domain pairs)
      (Hcoh : PlonkishLookupPoly.table_prefix_coherent domain pairs
        table_rows)
      (thetas : list Z)
      (Hth_ndp : Poly.NoDupP (p := p) thetas)
      (Hth_room : (Z.to_nat (Domain.usable_rows domain) *
        List.length pairs + 1 <= List.length thetas)%nat)
      (Hcomb_all : forall theta, List.In theta thetas ->
        lookup_comb_agree domain pairs theta) :
    PlonkishLookupPoly.lookup_membership domain pairs table_rows.
  Proof.
    intros row Hrow.
    set (u := Domain.usable_rows domain) in *.
    set (un := Z.to_nat u) in *.
    set (m := List.length pairs) in *.
    assert (Hun : Z.of_nat un = u) by (exact (Z2Nat.id u Hu)).
    set (j0 := Z.to_nat row).
    assert (Hrow_eq : Z.of_nat j0 = row)
      by (clear -Hrow; unfold j0; lia).
    assert (Hj0 : Z.of_nat j0 < u) by (clear -Hrow; unfold j0; lia).
    (* the combined-value membership, for every pool θ *)
    assert (Hcomb : forall theta, List.In theta thetas ->
      exists t, (t < un)%nat /\
      comb_input pairs theta row = comb_table pairs theta (Z.of_nat t)).
    { intros theta Hth.
      exact (Hcomb_all theta Hth row Hrow). }
    (* the degenerate empty-tuple case *)
    destruct (Nat.eq_dec m 0) as [Hm0 | Hmpos].
    { assert (Hnil : pairs = [])
        by (exact (proj1 (List.length_zero_iff_nil pairs) Hm0)).
      exists 0. split; [clear -Htr_pos; lia |].
      rewrite Hnil. constructor. }
    (* the fiber choice over the θ pool *)
    set (m' := (m - 1)%nat).
    set (pickb := fun th : Z =>
      match List.find (fun t =>
        comb_input pairs th row =? comb_table pairs th (Z.of_nat t))
        (List.seq 0 un) with
      | Some t => t
      | None => 0%nat
      end).
    assert (Hpick : forall th, List.In th thetas ->
      (pickb th < un)%nat /\
      comb_input pairs th row =
      comb_table pairs th (Z.of_nat (pickb th))).
    { intros th Hthin.
      destruct (Hcomb th Hthin) as (t & Ht & Heq).
      unfold pickb.
      destruct (List.find (fun t' =>
        comb_input pairs th row =? comb_table pairs th (Z.of_nat t'))
        (List.seq 0 un)) as [t' |] eqn:Hfind.
      - apply List.find_some in Hfind.
        destruct Hfind as [Hin' Heq'].
        apply List.in_seq in Hin'.
        apply Z.eqb_eq in Heq'.
        split; [clear -Hin'; lia | exact Heq'].
      - exfalso.
        pose proof (List.find_none _ _ Hfind t) as Hnone.
        assert (Hin : List.In t (List.seq 0 un))
          by (apply List.in_seq; clear -Ht; lia).
        specialize (Hnone Hin).
        apply Z.eqb_neq in Hnone.
        exact (Hnone Heq). }
    assert (Hmul_le : (un * m' <= un * m)%nat)
      by (apply Nat.mul_le_mono_l; unfold m'; clear; lia).
    assert (Hpool_bound : (un * m' < List.length thetas)%nat)
      by (clear -Hth_room Hmul_le; lia).
    destruct (PlonkishLookupPoly.fiber_pigeonhole un m' pickb thetas
      (fun x Hx => proj1 (Hpick x Hx)) Hpool_bound) as (t & Ht_lt & Hfib).
    set (fiber := List.filter (fun th => Nat.eqb (pickb th) t) thetas)
      in *.
    set (ths := List.firstn m fiber).
    assert (Hfib_m : (m <= List.length fiber)%nat)
      by (clear -Hfib Hmpos; unfold m' in Hfib; lia).
    assert (Hth_len : List.length ths = m)
      by (unfold ths; apply List.firstn_length_le; exact Hfib_m).
    assert (Hth_in_pool : forall th, List.In th ths -> List.In th thetas).
    { intros th Hth.
      unfold ths in Hth.
      apply In_firstn in Hth.
      unfold fiber in Hth.
      apply List.filter_In in Hth. exact (proj1 Hth). }
    assert (Hths_ndp : Poly.NoDupP (p := p) ths).
    { unfold Poly.NoDupP, ths.
      rewrite <- List.firstn_map.
      apply NoDup_firstn.
      unfold fiber.
      apply NoDup_map_filter.
      exact Hth_ndp. }
    assert (Hth_agree : forall th, List.In th ths ->
      comb_input pairs th row = comb_table pairs th (Z.of_nat t)).
    { intros th Hth.
      assert (Hth' : List.In th fiber)
        by (unfold ths in Hth;
            exact (In_firstn m fiber th Hth)).
      unfold fiber in Hth'.
      apply List.filter_In in Hth'.
      destruct Hth' as [Hthin Hpickt].
      apply Nat.eqb_eq in Hpickt.
      rewrite <- Hpickt.
      exact (proj2 (Hpick th Hthin)). }
    (* interpolation: the two tuples agree coefficientwise *)
    set (in_tup := PlonkishLookupPoly.input_tuple pairs row).
    set (tab_tup := PlonkishLookupPoly.table_tuple pairs (Z.of_nat t)).
    assert (Hin_len : List.length in_tup = m)
      by (unfold in_tup, PlonkishLookupPoly.input_tuple;
          apply List.length_map).
    assert (Htab_len : List.length tab_tup = m)
      by (unfold tab_tup, PlonkishLookupPoly.table_tuple;
          apply List.length_map).
    assert (Hpeq : Poly.peq (p := p) (List.rev in_tup) (List.rev tab_tup)).
    { apply (Poly.interpolant_unique (p := p) ths).
      - exact Hths_ndp.
      - eapply Nat.le_trans; [apply Vanishing.pdeg_le_length |].
        rewrite List.length_rev, Hin_len, Hth_len.
        apply Nat.le_refl.
      - eapply Nat.le_trans; [apply Vanishing.pdeg_le_length |].
        rewrite List.length_rev, Htab_len, Hth_len.
        apply Nat.le_refl.
      - intros th Hth.
        rewrite <- !PlonkishLookupPoly.comb_eval.
        exact (Hth_agree th Hth). }
    pose proof (fun i => proj1 (Poly.peq_iff_coef (p := p) _ _) Hpeq i)
      as Hcoef.
    set (dfg := ((fun _ : Z => 0), (fun _ : Z => 0)) : (Z -> Z) * (Z -> Z)).
    assert (Hrow_u : 0 <= row < Domain.usable_rows domain) by (exact Hrow).
    assert (Ht_u : 0 <= Z.of_nat t < Domain.usable_rows domain).
    { assert (Hg : 0 <= Z.of_nat t < u).
      { split; [clear; lia |].
        rewrite <- Hun. apply Nat2Z.inj_lt. exact Ht_lt. }
      exact Hg. }
    unfold PlonkishLookupPoly.pairs_canonical in Hcanon.
    rewrite List.Forall_forall in Hcanon.
    assert (Hnth : forall i, (i < m)%nat ->
      fst (List.nth i pairs dfg) row =
      snd (List.nth i pairs dfg) (Z.of_nat t)).
    { intros i Hi.
      assert (Hi' : (i < List.length pairs)%nat) by (exact Hi).
      pose proof (Hcoef (m - 1 - i)%nat) as Hc.
      unfold Poly.coef in Hc.
      rewrite (List.rev_nth in_tup 0) in Hc
        by (rewrite Hin_len; clear -Hi Hmpos; lia).
      rewrite (List.rev_nth tab_tup 0) in Hc
        by (rewrite Htab_len; clear -Hi Hmpos; lia).
      replace (List.length in_tup - S (m - 1 - i))%nat with i in Hc
        by (rewrite Hin_len; clear -Hi Hmpos; lia).
      replace (List.length tab_tup - S (m - 1 - i))%nat with i in Hc
        by (rewrite Htab_len; clear -Hi Hmpos; lia).
      assert (Hin_nth :
        List.nth i in_tup 0 = fst (List.nth i pairs dfg) row).
      { unfold in_tup, PlonkishLookupPoly.input_tuple.
        rewrite (List.nth_indep (List.map (fun fg => fst fg row) pairs)
          0 (fst dfg row))
          by (rewrite List.length_map; exact Hi').
        exact (List.map_nth
          (fun fg : (Z -> Z) * (Z -> Z) => fst fg row) pairs dfg i). }
      assert (Htab_nth :
        List.nth i tab_tup 0 = snd (List.nth i pairs dfg) (Z.of_nat t)).
      { unfold tab_tup, PlonkishLookupPoly.table_tuple.
        rewrite (List.nth_indep
          (List.map (fun fg => snd fg (Z.of_nat t)) pairs)
          0 (snd dfg (Z.of_nat t)))
          by (rewrite List.length_map; exact Hi').
        exact (List.map_nth
          (fun fg : (Z -> Z) * (Z -> Z) => snd fg (Z.of_nat t))
          pairs dfg i). }
      rewrite Hin_nth, Htab_nth in Hc.
      assert (Hfg_in : List.In (List.nth i pairs dfg) pairs)
        by (apply List.nth_In; exact Hi').
      destruct (Hcanon _ Hfg_in row Hrow_u) as [Hcan_f _].
      destruct (Hcanon _ Hfg_in (Z.of_nat t) Ht_u) as [_ Hcan_g].
      rewrite Hcan_f, Hcan_g in Hc.
      exact Hc. }
    assert (Hforall : List.Forall
      (fun fg => fst fg row = snd fg (Z.of_nat t)) pairs).
    { apply List.Forall_forall.
      intros fg Hfg.
      destruct (List.In_nth pairs fg dfg Hfg) as (i & Hi & Hfg_eq).
      rewrite <- Hfg_eq.
      apply Hnth. exact Hi. }
    (* the prefix condition moves the witness into the loaded prefix *)
    destruct (Z.ltb_spec (Z.of_nat t) table_rows) as [Hlt | Hge].
    - exists (Z.of_nat t).
      split; [clear -Hlt; lia | exact Hforall].
    - assert (Hbound : table_rows <= Z.of_nat t < Domain.usable_rows domain)
        by (exact (conj Hge (proj2 Ht_u))).
      destruct (Hcoh (Z.of_nat t) Hbound) as (t' & Ht' & Hall2).
      exists t'.
      split; [exact Ht' |].
      apply List.Forall_forall.
      intros fg Hfg.
      rewrite List.Forall_forall in Hforall, Hall2.
      rewrite (Hforall fg Hfg).
      exact (Hall2 fg Hfg).
  Qed.

  (** The lookup counting theorem: the transcript-shaped nested challenge
      family — [u·m + 1] distinct [θ], each with committed [A'], [S'] and
      an accepting [(β, γ)] grid of [2·u + 1] distinct residues per side —
      forces tuple membership. *)
  Theorem lookup_counting (domain : Domain.t)
      (pairs : list ((Z -> Z) * (Z -> Z))) (table_rows : Z)
      (Hbf : 0 <= domain.(Domain.blinding_factors))
      (Hu : 0 <= Domain.usable_rows domain)
      (Htr_pos : 0 < table_rows)
      (Htr_le : table_rows <= Domain.usable_rows domain)
      (Hcanon : PlonkishLookupPoly.pairs_canonical (p := p) domain pairs)
      (Hcoh : PlonkishLookupPoly.table_prefix_coherent domain pairs
        table_rows)
      (thetas : list Z)
      (Hth_ndp : Poly.NoDupP (p := p) thetas)
      (Hth_room : (Z.to_nat (Domain.usable_rows domain) *
        List.length pairs + 1 <= List.length thetas)%nat)
      (Hacc : forall theta, List.In theta thetas ->
        exists (A' S' : Z -> Z) (betas gammas : list Z),
          Poly.NoDupP (p := p) betas /\
          (2 * Z.to_nat (Domain.usable_rows domain) + 1 <=
           List.length betas)%nat /\
          Poly.NoDupP (p := p) gammas /\
          (2 * Z.to_nat (Domain.usable_rows domain) + 1 <=
           List.length gammas)%nat /\
          (forall beta gamma, List.In beta betas -> List.In gamma gammas ->
            lookup_challenge_regular domain pairs theta beta gamma ->
            exists Zp,
              lookup_rules_hold domain pairs theta beta gamma A' S' Zp)) :
    PlonkishLookupPoly.lookup_membership domain pairs table_rows.
  Proof.
    apply (lookup_theta_counting domain pairs table_rows Hbf Hu Htr_pos
      Htr_le Hcanon Hcoh thetas Hth_ndp Hth_room).
    intros theta Hth row Hrow.
    destruct (Hacc theta Hth)
      as (A' & S' & betas & gammas & Hnb & Hlb & Hng & Hlg & Hbg).
    assert (Hj0 : Z.of_nat (Z.to_nat row) < Domain.usable_rows domain)
      by lia.
    destruct (PlonkishLookupPoly.per_theta_membership_of_pools domain pairs theta Hbf Hu
      A' S' betas gammas Hnb Hlb Hng Hlg Hbg (Z.to_nat row) Hj0)
      as (t & Ht & Heq).
    exists t.
    split; [exact Ht |].
    replace row with (Z.of_nat (Z.to_nat row)) by lia.
    exact Heq.
  Qed.

  (** The single-challenge acceptance of the five lookup rules
      ([plonk/lookup/verifier.rs], [expressions()]) at one
      [(θ, β, γ)] triple, with the permuted columns and the running
      product chosen with the challenges. *)
  Definition lookup_accepts_at (domain : Domain.t)
      (pairs : list ((Z -> Z) * (Z -> Z))) (theta beta gamma : Z) : Prop :=
    exists A' S' Zp : Z -> Z,
      lookup_rules_hold domain pairs theta beta gamma A' S' Zp.

  (** The [θ]-level bad set: combined agreement holds row-wise although
      tuple membership fails — at most [u·m] residues. *)
  Definition lookup_theta_bad (domain : Domain.t)
      (pairs : list ((Z -> Z) * (Z -> Z))) (table_rows : Z) (theta : Z)
      : Prop :=
    lookup_comb_agree domain pairs theta /\
    ~ PlonkishLookupPoly.lookup_membership domain pairs table_rows.

  Theorem lookup_theta_bad_card (domain : Domain.t)
      (pairs : list ((Z -> Z) * (Z -> Z))) (table_rows : Z)
      (Hbf : 0 <= domain.(Domain.blinding_factors))
      (Hu : 0 <= Domain.usable_rows domain)
      (Htr_pos : 0 < table_rows)
      (Htr_le : table_rows <= Domain.usable_rows domain)
      (Hcanon : PlonkishLookupPoly.pairs_canonical (p := p) domain pairs)
      (Hcoh : PlonkishLookupPoly.table_prefix_coherent domain pairs
        table_rows) :
    card_at_most (lookup_theta_bad domain pairs table_rows)
      (Z.to_nat (Domain.usable_rows domain) * List.length pairs).
  Proof.
    intros ys Hnd HF.
    destruct (Compare_dec.le_lt_dec (List.length ys)
      (Z.to_nat (Domain.usable_rows domain) * List.length pairs)%nat)
      as [Hle | Hgt]; [exact Hle |].
    exfalso.
    destruct ys as [| th0 ys']; [cbn in Hgt; lia |].
    inversion HF as [| ? ? Hbad0 HFrest]; subst.
    destruct Hbad0 as [_ HnM].
    apply HnM.
    apply (lookup_theta_counting domain pairs table_rows Hbf Hu Htr_pos
      Htr_le Hcanon Hcoh (th0 :: ys') Hnd
      ltac:(cbn [List.length] in *; lia)).
    intros theta Hth.
    rewrite List.Forall_forall in HF.
    exact (proj1 (HF theta Hth)).
  Qed.

  (** The [(β, γ)]-level grid bound: at a [θ] without row-wise combined
      agreement, no acceptance grid for committed [A'], [S'] extends
      beyond [2·u] distinct residues on both sides. *)
  Theorem lookup_pair_grid_bound (domain : Domain.t)
      (pairs : list ((Z -> Z) * (Z -> Z)))
      (Hbf : 0 <= domain.(Domain.blinding_factors))
      (Hu : 0 <= Domain.usable_rows domain)
      (theta : Z) (A' S' : Z -> Z)
      (HnX : ~ lookup_comb_agree domain pairs theta)
      (betas gammas : list Z)
      (Hnb : Poly.NoDupP (p := p) betas)
      (Hng : Poly.NoDupP (p := p) gammas)
      (Hbg : forall beta gamma, List.In beta betas ->
        List.In gamma gammas ->
        lookup_challenge_regular domain pairs theta beta gamma ->
        exists Zp,
          lookup_rules_hold domain pairs theta beta gamma A' S' Zp) :
    (List.length betas <= 2 * Z.to_nat (Domain.usable_rows domain))%nat \/
    (List.length gammas <= 2 * Z.to_nat (Domain.usable_rows domain))%nat.
  Proof.
    destruct (Compare_dec.le_lt_dec (List.length betas)
      (2 * Z.to_nat (Domain.usable_rows domain))%nat) as [Hb | Hb];
      [left; exact Hb |].
    destruct (Compare_dec.le_lt_dec (List.length gammas)
      (2 * Z.to_nat (Domain.usable_rows domain))%nat) as [Hg | Hg];
      [right; exact Hg |].
    exfalso.
    apply HnX.
    intros row Hrow.
    assert (Hj0 : Z.of_nat (Z.to_nat row) < Domain.usable_rows domain)
      by lia.
    destruct (PlonkishLookupPoly.per_theta_membership_of_pools domain pairs theta Hbf Hu
      A' S' betas gammas Hnb ltac:(lia) Hng ltac:(lia) Hbg
      (Z.to_nat row) Hj0) as (t & Ht & Heq).
    exists t.
    split; [exact Ht |].
    replace row with (Z.of_nat (Z.to_nat row)) by lia.
    exact Heq.
  Qed.

  (** The flat bad set at the [(θ, β, γ)] triple, and the case corollary
      carrying both bounds. *)
  Definition lookup_bad (domain : Domain.t)
      (pairs : list ((Z -> Z) * (Z -> Z))) (table_rows : Z)
      (theta beta gamma : Z) : Prop :=
    lookup_accepts_at domain pairs theta beta gamma /\
    ~ PlonkishLookupPoly.lookup_membership domain pairs table_rows.

  Corollary lookup_accept_cases (domain : Domain.t)
      (pairs : list ((Z -> Z) * (Z -> Z))) (table_rows : Z)
      (Hbf : 0 <= domain.(Domain.blinding_factors))
      (Hu : 0 <= Domain.usable_rows domain)
      (Htr_pos : 0 < table_rows)
      (Htr_le : table_rows <= Domain.usable_rows domain)
      (Hcanon : PlonkishLookupPoly.pairs_canonical (p := p) domain pairs)
      (Hcoh : PlonkishLookupPoly.table_prefix_coherent domain pairs
        table_rows)
      (theta beta gamma : Z)
      (Haccept : lookup_accepts_at domain pairs theta beta gamma) :
    PlonkishLookupPoly.lookup_membership domain pairs table_rows \/
    (lookup_bad domain pairs table_rows theta beta gamma /\
     card_at_most (lookup_theta_bad domain pairs table_rows)
       (Z.to_nat (Domain.usable_rows domain) * List.length pairs) /\
     (forall (theta' : Z) (A' S' : Z -> Z),
       ~ lookup_comb_agree domain pairs theta' ->
       forall betas gammas : list Z,
         Poly.NoDupP (p := p) betas ->
         Poly.NoDupP (p := p) gammas ->
         (forall beta' gamma', List.In beta' betas ->
           List.In gamma' gammas ->
           lookup_challenge_regular domain pairs theta' beta' gamma' ->
           exists Zp, lookup_rules_hold domain pairs theta' beta' gamma'
             A' S' Zp) ->
         (List.length betas <=
          2 * Z.to_nat (Domain.usable_rows domain))%nat \/
         (List.length gammas <=
          2 * Z.to_nat (Domain.usable_rows domain))%nat)).
  Proof.
    destruct (lookup_membership_dec domain pairs table_rows) as [HM | HnM].
    - left. exact HM.
    - right.
      split; [exact (conj Haccept HnM) |].
      split.
      + exact (lookup_theta_bad_card domain pairs table_rows Hbf Hu
          Htr_pos Htr_le Hcanon Hcoh).
      + intros theta' A' S' HnX betas gammas Hnb Hng Hbg.
        exact (lookup_pair_grid_bound domain pairs Hbf Hu theta' A' S'
          HnX betas gammas Hnb Hng Hbg).
  Qed.

End WithPrime.

End PlonkishCounting.
