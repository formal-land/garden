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

  Lemma pool_avoid_sublist (bad pool : list Z) (k : nat)
      (Hnd : Poly.NoDupP (p := p) pool)
      (Hroom : (List.length bad + k <= List.length pool)%nat) :
    exists xs : list Z,
      List.length xs = k /\
      Poly.NoDupP (p := p) xs /\
      (forall x, List.In x xs -> List.In x pool) /\
      (forall x r, List.In x xs -> List.In r bad -> (x - r) mod p <> 0).
  Proof.
    set (filt := List.filter
      (fun x => negb (List.existsb (fun r => ((x - r) mod p =? 0)%Z) bad))
      pool).
    assert (Hfl : (k <= List.length filt)%nat).
    { pose proof (PermutationPoly.filter_avoid_length (p := p) bad pool Hnd)
        as Havoid.
      unfold filt. lia. }
    exists (List.firstn k filt).
    split; [apply List.firstn_length_le; exact Hfl |].
    split; [| split].
    - unfold Poly.NoDupP.
      rewrite <- List.firstn_map.
      apply PlonkishLookupPoly.NoDup_firstn.
      unfold filt.
      apply PermutationPoly.NoDup_map_filter.
      exact Hnd.
    - intros x Hx.
      pose proof (PlonkishLookupPoly.In_firstn k filt x Hx) as Hxf.
      apply List.filter_In in Hxf.
      exact (proj1 Hxf).
    - intros x r Hx Hr Hzero.
      pose proof (PlonkishLookupPoly.In_firstn k filt x Hx) as Hxf.
      apply List.filter_In in Hxf.
      destruct Hxf as [_ Hgood].
      apply Bool.negb_true_iff in Hgood.
      assert (Hex : List.existsb (fun r' => ((x - r') mod p =? 0)%Z) bad
        = true).
      { apply List.existsb_exists.
        exists r.
        split; [exact Hr | apply Z.eqb_eq; exact Hzero]. }
      congruence.
  Qed.

  Lemma pool_avoid_pick (bad pool : list Z)
      (Hnd : Poly.NoDupP (p := p) pool)
      (Hroom : (List.length bad < List.length pool)%nat) :
    exists x : Z,
      List.In x pool /\
      forall r, List.In r bad -> (x - r) mod p <> 0.
  Proof.
    destruct (pool_avoid_sublist bad pool 1 Hnd ltac:(lia))
      as (xs & Hlen & _ & Hsub & Havoid).
    destruct xs as [| x rest]; [cbn in Hlen; discriminate |].
    exists x.
    split; [apply Hsub; left; reflexivity |].
    intros r Hr.
    exact (Havoid x r (or_introl eq_refl) Hr).
  Qed.

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

    (** At a fixed [β], the total-product disjunction on a [γ] pool of
        [2·N + 1] distinct residues forces the total identity at every
        [γ] — the generalized [PermutationPoly.products_eq_all]: at least
        [N + 1] pool points avoid the [N] roots of the identity-side
        product, and the difference of the two monic products (degree
        [N + 1]) vanishes on all of them. *)
    Lemma products_eq_of_pool (beta : Z) (gammas : list Z)
        (Hnd : Poly.NoDupP (p := p) gammas)
        (Hlen : (2 * List.length all_cells + 1 <= List.length gammas)%nat)
        (Hor : forall gamma, List.In gamma gammas ->
          iprod beta gamma = 0 \/ iprod beta gamma = sprod beta gamma) :
      forall gamma : Z, iprod beta gamma = sprod beta gamma.
    Proof.
      intros gamma.
      set (good := List.filter
        (fun x => negb (List.existsb (fun r => ((x - r) mod p =? 0)%Z)
          (iroots beta)))
        gammas).
      assert (Hgood :
        (List.length all_cells + 1 <= List.length good)%nat).
      { pose proof (PermutationPoly.filter_avoid_length (p := p)
          (iroots beta) gammas Hnd) as Hfl.
        unfold good.
        rewrite (PermutationPoly.iroots_length
          domain ncols chunk_len g lbl beta) in Hfl.
        lia. }
      assert (Hroots : forall x, List.In x good ->
        Poly.eval (p := p)
          (Poly.psub (p := p) (Poly.prod_lin (p := p) (iroots beta))
            (Poly.prod_lin (p := p) (sroots beta))) x = 0).
      { intros x Hx.
        apply List.filter_In in Hx.
        destruct Hx as [Hxin Hav].
        assert (HPD : Poly.eval (p := p)
          (Poly.prod_lin (p := p) (iroots beta)) x <> 0).
        { intro Hz.
          apply PermutationPoly.prod_lin_root_of_zero in Hz.
          destruct Hz as [r [Hr Hxr]].
          assert (Hex : List.existsb (fun r0 => ((x - r0) mod p =? 0)%Z)
            (iroots beta) = true).
          { apply List.existsb_exists.
            exists r.
            split; [exact Hr | apply Z.eqb_eq; exact Hxr]. }
          rewrite Hex in Hav.
          discriminate. }
        destruct (Hor x Hxin) as [H0 | Heqx].
        - exfalso.
          apply HPD.
          rewrite <- (PermutationPoly.iprod_eval (p := p)
            domain ncols chunk_len g lbl beta x).
          exact H0.
        - rewrite Poly.eval_psub.
          rewrite <- (PermutationPoly.iprod_eval (p := p)
            domain ncols chunk_len g lbl beta x).
          rewrite <- (PermutationPoly.sprod_eval (p := p)
            domain ncols chunk_len g lbl sigma beta x).
          rewrite Heqx, Z.sub_diag.
          apply Zmod_0_l. }
      assert (Hzero : Poly.norm (p := p)
        (Poly.psub (p := p) (Poly.prod_lin (p := p) (iroots beta))
          (Poly.prod_lin (p := p) (sroots beta))) = []).
      { apply (Poly.zero_of_roots (p := p) _ good).
        - unfold Poly.NoDupP, good.
          apply PermutationPoly.NoDup_map_filter.
          exact Hnd.
        - rewrite List.Forall_forall. exact Hroots.
        - pose proof (Poly.pdeg_psub_le (p := p)
            (Poly.prod_lin (p := p) (iroots beta))
            (Poly.prod_lin (p := p) (sroots beta))) as Hle.
          pose proof (proj2 (Poly.prod_lin_monic (p := p) (iroots beta)))
            as Hd1.
          pose proof (proj2 (Poly.prod_lin_monic (p := p) (sroots beta)))
            as Hd2.
          rewrite (PermutationPoly.iroots_length
            domain ncols chunk_len g lbl beta) in Hd1.
          rewrite (PermutationPoly.sroots_length
            domain ncols chunk_len g lbl sigma beta) in Hd2.
          lia. }
      rewrite (PermutationPoly.iprod_eval (p := p)
        domain ncols chunk_len g lbl beta gamma).
      rewrite (PermutationPoly.sprod_eval (p := p)
        domain ncols chunk_len g lbl sigma beta gamma).
      pose proof (Poly.eval_norm_nil (p := p) _ gamma Hzero) as He0.
      rewrite Poly.eval_psub in He0.
      change ((Poly.eval (p := p) (Poly.prod_lin (p := p) (iroots beta)) gamma
        - Poly.eval (p := p) (Poly.prod_lin (p := p) (sroots beta)) gamma)
          mod p)
        with (BinOp.sub (p := p)
          (Poly.eval (p := p) (Poly.prod_lin (p := p) (iroots beta)) gamma)
          (Poly.eval (p := p) (Poly.prod_lin (p := p) (sroots beta)) gamma))
        in He0.
      apply sub_zero_equiv in He0.
      unfold UnOp.from in He0.
      rewrite !Poly.eval_canonical in He0.
      exact He0.
    Qed.

    (** The generalized [PermutationPoly.match_cell]: a [β] pool of
        [N + 1] residues, each member with an accepting [γ] pool, matches
        every enumerated cell to a cell agreeing in value and σ-label —
        some pool [β] avoids the [≤ N] residues that could make a
        spurious identity factor vanish. *)
    Lemma match_cell_of_pools (betas : list Z)
        (Hnb : Poly.NoDupP (p := p) betas)
        (Hlb : (List.length all_cells + 1 <= List.length betas)%nat)
        (Hslice : forall beta, List.In beta betas ->
          exists gammas : list Z,
            Poly.NoDupP (p := p) gammas /\
            (2 * List.length all_cells + 1 <= List.length gammas)%nat /\
            forall gamma, List.In gamma gammas ->
              iprod beta gamma = 0 \/ iprod beta gamma = sprod beta gamma) :
      forall c, List.In c all_cells ->
      exists d, List.In d all_cells /\
        g d mod p = g c mod p /\ lbl d mod p = lbl (sigma c) mod p.
    Proof.
      intros c Hc.
      pose proof (prime_range (p := p)) as Hp1.
      assert (Heq : forall beta, List.In beta betas ->
        forall gamma, iprod beta gamma = sprod beta gamma).
      { intros beta Hbin gamma0.
        destruct (Hslice beta Hbin) as (gammas & Hndg & Hleng & Hor).
        exact (products_eq_of_pool beta gammas Hndg Hleng Hor gamma0). }
      set (bad := List.map
        (fun d => (- (g d - g c)) * mod_inverse (lbl d - lbl (sigma c)) p)
        all_cells).
      assert (Hpick : exists bstar, List.In bstar betas /\
        forall r, List.In r bad -> (bstar - r) mod p <> 0).
      { apply pool_avoid_pick; [exact Hnb |].
        unfold bad.
        rewrite List.length_map.
        lia. }
      destruct Hpick as (bstar & Hbin & Havoid).
      assert (Hsfac0 : PermutationPoly.sfac (p := p) g lbl sigma bstar
        (- (g c + bstar * lbl (sigma c))) c = 0).
      { unfold PermutationPoly.sfac.
        replace (g c + bstar * lbl (sigma c)
          + - (g c + bstar * lbl (sigma c))) with 0 by ring.
        apply Zmod_0_l. }
      assert (Hip0 : iprod bstar (- (g c + bstar * lbl (sigma c))) = 0).
      { rewrite (Heq bstar Hbin).
        unfold PermutationPoly.sprod.
        apply PermutationPoly.fprod_zero_iff.
        exists (PermutationPoly.sfac (p := p) g lbl sigma bstar
          (- (g c + bstar * lbl (sigma c))) c).
        split.
        - apply List.in_map. exact Hc.
        - rewrite Hsfac0. apply Zmod_0_l. }
      unfold PermutationPoly.iprod in Hip0.
      apply PermutationPoly.fprod_zero_iff in Hip0.
      destruct Hip0 as [v [Hvin Hvm]].
      apply List.in_map_iff in Hvin.
      destruct Hvin as [d [Hvd Hdin]].
      subst v.
      assert (Hifac0 : PermutationPoly.ifac (p := p) g lbl bstar
        (- (g c + bstar * lbl (sigma c))) d = 0).
      { unfold PermutationPoly.ifac in *.
        rewrite Zmod_mod in Hvm.
        exact Hvm. }
      assert (Hkey : ((g d - g c)
        + bstar * (lbl d - lbl (sigma c))) mod p = 0).
      { rewrite <- Hifac0.
        unfold PermutationPoly.ifac.
        f_equal.
        ring. }
      destruct (Z.eq_dec ((lbl d - lbl (sigma c)) mod p) 0) as [Hld | Hld].
      - exists d.
        split; [exact Hdin |].
        split.
        + assert (Hgd : (g d - g c) mod p = 0).
          { replace (g d - g c)
              with (((g d - g c) + bstar * (lbl d - lbl (sigma c)))
                - bstar * (lbl d - lbl (sigma c))) by ring.
            rewrite Zminus_mod, Hkey.
            assert (Hmx : (bstar * (lbl d - lbl (sigma c))) mod p = 0)
              by (rewrite Zmult_mod, Hld, Z.mul_0_r; reflexivity).
            rewrite Hmx.
            reflexivity. }
          change ((g d - g c) mod p)
            with (BinOp.sub (p := p) (g d) (g c)) in Hgd.
          apply sub_zero_equiv in Hgd.
          unfold UnOp.from in Hgd.
          exact Hgd.
        + change ((lbl d - lbl (sigma c)) mod p)
            with (BinOp.sub (p := p) (lbl d) (lbl (sigma c))) in Hld.
          apply sub_zero_equiv in Hld.
          unfold UnOp.from in Hld.
          exact Hld.
      - exfalso.
        pose proof (mod_inverse_mul_prime (p := p)
          (lbl d - lbl (sigma c)) Hld) as Hinv.
        unfold BinOp.mul in Hinv.
        assert (Hby : (bstar * (lbl d - lbl (sigma c))) mod p
          = (- (g d - g c)) mod p).
        { replace (bstar * (lbl d - lbl (sigma c)))
            with (((g d - g c) + bstar * (lbl d - lbl (sigma c)))
              - (g d - g c)) by ring.
          replace (- (g d - g c)) with (0 - (g d - g c)) by ring.
          rewrite Zminus_mod, Hkey, (Zminus_mod 0 (g d - g c)), Zmod_0_l.
          reflexivity. }
        assert (Hbstar : bstar mod p
          = ((- (g d - g c)) * mod_inverse (lbl d - lbl (sigma c)) p)
              mod p).
        { transitivity ((bstar * (mod_inverse (lbl d - lbl (sigma c)) p
            * (lbl d - lbl (sigma c)))) mod p).
          - symmetry.
            rewrite <- (Zmult_mod_idemp_r
              (mod_inverse (lbl d - lbl (sigma c)) p
                * (lbl d - lbl (sigma c))) bstar).
            rewrite Hinv, Z.mul_1_r.
            reflexivity.
          - replace (bstar * (mod_inverse (lbl d - lbl (sigma c)) p
              * (lbl d - lbl (sigma c))))
              with ((bstar * (lbl d - lbl (sigma c)))
                * mod_inverse (lbl d - lbl (sigma c)) p) by ring.
            rewrite <- (Zmult_mod_idemp_l
              (bstar * (lbl d - lbl (sigma c)))
              (mod_inverse (lbl d - lbl (sigma c)) p)).
            rewrite Hby.
            rewrite Zmult_mod_idemp_l.
            reflexivity. }
        apply (Havoid
          ((- (g d - g c)) * mod_inverse (lbl d - lbl (sigma c)) p)).
        + unfold bad.
          exact (List.in_map _ all_cells d Hdin).
        + rewrite Zminus_mod, Hbstar, Z.sub_diag.
          apply Zmod_0_l.
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
      destruct (match_cell_of_pools betas Hnb Hlb Hslice' c
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
      its two challenge layers.  [per_theta_membership_of_pools]
      generalizes the per-[θ] multiset step: with the permuted columns
      [A'], [S'] fixed, an accepting [(β, γ)] grid drawn from two pools of
      [2·u + 1] distinct residues each identifies the factor polynomials
      and carries every combined input value into the combined table
      values.  [lookup_theta_counting] generalizes the [θ]-de-combination
      pigeonhole: row-wise combined agreement at [u·m + 1] distinct [θ]
      forces tuple membership. *)

  Local Notation comb_input := (@PlonkishLookupPoly.comb_input p).
  Local Notation comb_table := (@PlonkishLookupPoly.comb_table p).
  Local Notation prodl := (@PlonkishLookupPoly.prodl p).
  Local Notation lookup_rules_hold :=
    (@PlonkishLookupPoly.lookup_rules_hold p).
  Local Notation lookup_challenge_regular :=
    (@PlonkishLookupPoly.lookup_challenge_regular p).

  Lemma per_theta_membership_of_pools (domain : Domain.t)
      (pairs : list ((Z -> Z) * (Z -> Z))) (theta : Z)
      (Hbf : 0 <= domain.(Domain.blinding_factors))
      (Hu : 0 <= Domain.usable_rows domain)
      (A' S' : Z -> Z)
      (betas gammas : list Z)
      (Hnb : Poly.NoDupP (p := p) betas)
      (Hlb : (2 * Z.to_nat (Domain.usable_rows domain) + 1 <=
              List.length betas)%nat)
      (Hng : Poly.NoDupP (p := p) gammas)
      (Hlg : (2 * Z.to_nat (Domain.usable_rows domain) + 1 <=
              List.length gammas)%nat)
      (Hbg : forall beta gamma : Z,
        List.In beta betas -> List.In gamma gammas ->
        lookup_challenge_regular domain pairs theta beta gamma ->
        exists Zp : Z -> Z,
          lookup_rules_hold domain pairs theta beta gamma A' S' Zp) :
    forall j0 : nat, Z.of_nat j0 < Domain.usable_rows domain ->
    exists t : nat, (t < Z.to_nat (Domain.usable_rows domain))%nat /\
      comb_input pairs theta (Z.of_nat j0) =
      comb_table pairs theta (Z.of_nat t).
  Proof.
    set (u := Domain.usable_rows domain) in *.
    set (un := Z.to_nat u) in *.
    assert (Hun : Z.of_nat un = u) by (exact (Z2Nat.id u Hu)).
    intros j0 Hj0.
    set (Na := List.map
      (fun j => (- comb_input pairs theta (Z.of_nat j)) mod p)
      (List.seq 0 un)).
    set (Ns := List.map
      (fun j => (- comb_table pairs theta (Z.of_nat j)) mod p)
      (List.seq 0 un)).
    set (NA' := List.map (fun j => (- A' (Z.of_nat j)) mod p)
      (List.seq 0 un)).
    set (NS' := List.map (fun j => (- S' (Z.of_nat j)) mod p)
      (List.seq 0 un)).
    assert (HNa_len : List.length Na = un)
      by (unfold Na; rewrite List.length_map, List.length_seq;
          reflexivity).
    assert (HNs_len : List.length Ns = un)
      by (unfold Ns; rewrite List.length_map, List.length_seq;
          reflexivity).
    assert (HNA'_len : List.length NA' = un)
      by (unfold NA'; rewrite List.length_map, List.length_seq;
          reflexivity).
    assert (HNS'_len : List.length NS' = un)
      by (unfold NS'; rewrite List.length_map, List.length_seq;
          reflexivity).
    (* avoiding the two bad-residue lists makes a challenge pair regular *)
    assert (Hreg_mk : forall x g0,
      (forall r, List.In r Na -> (x - r) mod p <> 0) ->
      (forall r, List.In r Ns -> (g0 - r) mod p <> 0) ->
      lookup_challenge_regular domain pairs theta x g0).
    { intros x g0 Hx Hg0 row Hrow.
      set (j := Z.to_nat row).
      assert (Hjlt : (j < un)%nat) by (unfold j, un; lia).
      assert (Hrow_eq : Z.of_nat j = row) by (unfold j; lia).
      assert (Hin_a :
        List.In ((- comb_input pairs theta (Z.of_nat j)) mod p) Na).
      { unfold Na.
        apply (List.in_map
          (fun j' => (- comb_input pairs theta (Z.of_nat j')) mod p)).
        apply List.in_seq. clear -Hjlt. lia. }
      assert (Hin_s :
        List.In ((- comb_table pairs theta (Z.of_nat j)) mod p) Ns).
      { unfold Ns.
        apply (List.in_map
          (fun j' => (- comb_table pairs theta (Z.of_nat j')) mod p)).
        apply List.in_seq. clear -Hjlt. lia. }
      split.
      - intros Hc.
        apply (Hx _ Hin_a).
        rewrite <- Hrow_eq in Hc.
        rewrite <- Hc. mod_ring_solve.
      - intros Hc.
        apply (Hg0 _ Hin_s).
        rewrite <- Hrow_eq in Hc.
        rewrite <- Hc. mod_ring_solve. }
    (* the fixed regular γ0, drawn from the γ pool *)
    assert (Hg0pick : exists gamma0, List.In gamma0 gammas /\
      forall r, List.In r Ns -> (gamma0 - r) mod p <> 0).
    { apply pool_avoid_pick; [exact Hng |].
      rewrite HNs_len. lia. }
    destruct Hg0pick as (gamma0 & Hg0_in & Hg0).
    (* the β point family, drawn from the β pool *)
    destruct (pool_avoid_sublist Na betas (S un) Hnb
      ltac:(rewrite HNa_len; lia))
      as (xs & Hxs_len & Hxs_ndp & Hxs_sub & Hxs_avoid).
    assert (Hxs_ne : exists x0, List.In x0 xs).
    { destruct xs as [| x0 rest]; [cbn in Hxs_len; discriminate |].
      exists x0. left. reflexivity. }
    destruct Hxs_ne as (x0 & Hx0_in).
    (* rules instances along the β family *)
    assert (Hper_x : forall x, List.In x xs ->
      exists Zp, lookup_rules_hold domain pairs theta x gamma0 A' S' Zp).
    { intros x Hx.
      apply (Hbg x gamma0 (Hxs_sub x Hx) Hg0_in).
      apply Hreg_mk; [intros r Hr; exact (Hxs_avoid x r Hx Hr)
                     | exact Hg0]. }
    set (cS' := prodl (List.map (fun j => S' (Z.of_nat j) + gamma0)
      (List.seq 0 un))).
    set (cs := prodl (List.map
      (fun j => comb_table pairs theta (Z.of_nat j) + gamma0)
      (List.seq 0 un))).
    (* the pointwise scaled agreement along the β family *)
    assert (Hpointwise : forall x, List.In x xs ->
      (cS' * Poly.eval (p := p) (Poly.prod_lin (p := p) NA') x) mod p =
      (cs * Poly.eval (p := p) (Poly.prod_lin (p := p) Na) x) mod p).
    { intros x Hx.
      destruct (Hper_x x Hx) as (Zp & Hrules).
      destruct (PlonkishLookupPoly.lookup_rules_consequences (p := p)
        domain pairs theta x gamma0 A' S' Zp Hbf Hu
        (Hreg_mk x gamma0 (fun r Hr => Hxs_avoid x r Hx Hr) Hg0)
        Hrules) as [Hprod _].
      fold u in Hprod. fold un in Hprod.
      rewrite (PlonkishLookupPoly.prodl_split (p := p)
        (fun k => ((A' (Z.of_nat k) + x) *
                   (S' (Z.of_nat k) + gamma0)) mod p)
        (fun k => A' (Z.of_nat k) + x)
        (fun k => S' (Z.of_nat k) + gamma0)
        (List.seq 0 un)) in Hprod by (intros; reflexivity).
      rewrite (PlonkishLookupPoly.prodl_split (p := p)
        (fun k => ((comb_input pairs theta (Z.of_nat k) + x) *
                   (comb_table pairs theta (Z.of_nat k) + gamma0)) mod p)
        (fun k => comb_input pairs theta (Z.of_nat k) + x)
        (fun k => comb_table pairs theta (Z.of_nat k) + gamma0)
        (List.seq 0 un)) in Hprod by (intros; reflexivity).
      assert (HevA' :
        prodl (List.map (fun k => A' (Z.of_nat k) + x) (List.seq 0 un)) =
        Poly.eval (p := p) (Poly.prod_lin (p := p) NA') x)
        by (exact (PlonkishLookupPoly.prodl_shift_eval (p := p)
          (fun k => A' (Z.of_nat k)) un x)).
      assert (HevA :
        prodl (List.map
          (fun k => comb_input pairs theta (Z.of_nat k) + x)
          (List.seq 0 un)) =
        Poly.eval (p := p) (Poly.prod_lin (p := p) Na) x)
        by (exact (PlonkishLookupPoly.prodl_shift_eval (p := p)
          (fun k => comb_input pairs theta (Z.of_nat k)) un x)).
      rewrite HevA', HevA in Hprod.
      fold cS' in Hprod. fold cs in Hprod.
      rewrite (Z.mul_comm cS'), (Z.mul_comm cs).
      exact Hprod. }
    (* the x0-instance factor facts *)
    destruct (Hper_x x0 Hx0_in) as (Zp0 & Hrules0).
    destruct (PlonkishLookupPoly.lookup_rules_consequences (p := p)
      domain pairs theta x0 gamma0 A' S' Zp0 Hbf Hu
      (Hreg_mk x0 gamma0 (fun r Hr => Hxs_avoid x0 r Hx0_in Hr) Hg0)
      Hrules0) as [_ Hfac].
    assert (HcS'_nz : cS' <> 0).
    { unfold cS'. apply PlonkishLookupPoly.prodl_nonzero.
      intros v Hv. apply List.in_map_iff in Hv.
      destruct Hv as (k & <- & Hk). apply List.in_seq in Hk.
      assert (Hk' : (k < Z.to_nat (Domain.usable_rows domain))%nat)
        by (exact (proj2 Hk)).
      exact (proj2 (Hfac k Hk')). }
    (* the A'-side polynomial identity *)
    assert (Hwl_len : List.length NA' = List.length Na)
      by (rewrite HNA'_len, HNa_len; reflexivity).
    assert (Hxs_len' : List.length xs = S (List.length NA'))
      by (rewrite HNA'_len; exact Hxs_len).
    destruct (PlonkishLookupPoly.prod_lin_scaled_agreement (p := p)
      NA' Na xs cS' cs Hwl_len Hxs_ndp Hxs_len'
      (PlonkishLookupPoly.prodl_canonical (p := p) _)
      (PlonkishLookupPoly.prodl_canonical (p := p) _) HcS'_nz
      Hpointwise) as [_ HpeqA].
    (* the γ point family, at the designated regular β = x0 *)
    destruct (pool_avoid_sublist Ns gammas (S un) Hng
      ltac:(rewrite HNs_len; lia))
      as (gs & Hgs_len & Hgs_ndp & Hgs_sub & Hgs_avoid).
    set (dA' := prodl (List.map (fun j => A' (Z.of_nat j) + x0)
      (List.seq 0 un))).
    set (da := prodl (List.map
      (fun j => comb_input pairs theta (Z.of_nat j) + x0)
      (List.seq 0 un))).
    assert (Hpointwise_g : forall g0, List.In g0 gs ->
      (dA' * Poly.eval (p := p) (Poly.prod_lin (p := p) NS') g0) mod p =
      (da * Poly.eval (p := p) (Poly.prod_lin (p := p) Ns) g0) mod p).
    { intros g0 Hg.
      assert (Hreg_g : lookup_challenge_regular domain pairs theta x0 g0).
      { apply Hreg_mk;
          [intros r Hr; exact (Hxs_avoid x0 r Hx0_in Hr)
          | intros r Hr; exact (Hgs_avoid g0 r Hg Hr)]. }
      destruct (Hbg x0 g0 (Hxs_sub x0 Hx0_in) (Hgs_sub g0 Hg) Hreg_g)
        as (Zpg & Hrulesg).
      destruct (PlonkishLookupPoly.lookup_rules_consequences (p := p)
        domain pairs theta x0 g0 A' S' Zpg Hbf Hu Hreg_g Hrulesg)
        as [Hprod _].
      fold u in Hprod. fold un in Hprod.
      rewrite (PlonkishLookupPoly.prodl_split (p := p)
        (fun k => ((A' (Z.of_nat k) + x0) *
                   (S' (Z.of_nat k) + g0)) mod p)
        (fun k => A' (Z.of_nat k) + x0)
        (fun k => S' (Z.of_nat k) + g0)
        (List.seq 0 un)) in Hprod by (intros; reflexivity).
      rewrite (PlonkishLookupPoly.prodl_split (p := p)
        (fun k => ((comb_input pairs theta (Z.of_nat k) + x0) *
                   (comb_table pairs theta (Z.of_nat k) + g0)) mod p)
        (fun k => comb_input pairs theta (Z.of_nat k) + x0)
        (fun k => comb_table pairs theta (Z.of_nat k) + g0)
        (List.seq 0 un)) in Hprod by (intros; reflexivity).
      assert (HevS' :
        prodl (List.map (fun k => S' (Z.of_nat k) + g0) (List.seq 0 un)) =
        Poly.eval (p := p) (Poly.prod_lin (p := p) NS') g0)
        by (exact (PlonkishLookupPoly.prodl_shift_eval (p := p)
          (fun k => S' (Z.of_nat k)) un g0)).
      assert (HevS :
        prodl (List.map
          (fun k => comb_table pairs theta (Z.of_nat k) + g0)
          (List.seq 0 un)) =
        Poly.eval (p := p) (Poly.prod_lin (p := p) Ns) g0)
        by (exact (PlonkishLookupPoly.prodl_shift_eval (p := p)
          (fun k => comb_table pairs theta (Z.of_nat k)) un g0)).
      rewrite HevS', HevS in Hprod.
      fold dA' in Hprod. fold da in Hprod.
      transitivity ((prodl (List.map (fun j => A' (Z.of_nat j) + x0)
          (List.seq 0 un)) *
        Poly.eval (p := p) (Poly.prod_lin (p := p) NS') g0) mod p);
        [reflexivity |].
      exact Hprod. }
    assert (HdA'_nz : dA' <> 0).
    { unfold dA'. apply PlonkishLookupPoly.prodl_nonzero.
      intros v Hv. apply List.in_map_iff in Hv.
      destruct Hv as (k & <- & Hk). apply List.in_seq in Hk.
      assert (Hk' : (k < Z.to_nat (Domain.usable_rows domain))%nat)
        by (exact (proj2 Hk)).
      exact (proj1 (Hfac k Hk')). }
    assert (Hwl_len2 : List.length NS' = List.length Ns)
      by (rewrite HNS'_len, HNs_len; reflexivity).
    assert (Hgs_len' : List.length gs = S (List.length NS'))
      by (rewrite HNS'_len; exact Hgs_len).
    destruct (PlonkishLookupPoly.prod_lin_scaled_agreement (p := p)
      NS' Ns gs dA' da Hwl_len2 Hgs_ndp Hgs_len'
      (PlonkishLookupPoly.prodl_canonical (p := p) _)
      (PlonkishLookupPoly.prodl_canonical (p := p) _) HdA'_nz
      Hpointwise_g) as [_ HpeqS].
    (* membership extraction *)
    set (v := comb_input pairs theta (Z.of_nat j0)).
    assert (Hj0un : (j0 < un)%nat) by (clear -Hj0 Hu; unfold un; lia).
    assert (Hroot_a :
      Poly.eval (p := p) (Poly.prod_lin (p := p) Na) ((- v) mod p) = 0).
    { apply (Poly.eval_prod_lin_zero (p := p) Na ((- v) mod p)
        ((- v) mod p)).
      - unfold Na, v.
        apply (List.in_map
          (fun j => (- comb_input pairs theta (Z.of_nat j)) mod p)).
        apply List.in_seq. clear -Hj0un. lia.
      - rewrite Z.sub_diag. apply Zmod_0_l. }
    assert (Hroot_A' :
      Poly.eval (p := p) (Poly.prod_lin (p := p) NA') ((- v) mod p) = 0).
    { rewrite (Poly.eval_peq (p := p) _ _ ((- v) mod p) HpeqA).
      exact Hroot_a. }
    destruct (PlonkishLookupPoly.eval_prod_lin_zero_inv (p := p)
      NA' ((- v) mod p) Hroot_A')
      as (r & Hr_in & Hr_zero).
    unfold NA' in Hr_in.
    apply List.in_map_iff in Hr_in.
    destruct Hr_in as (j1 & Hr_eq & Hj1).
    apply List.in_seq in Hj1.
    subst r.
    assert (HvA : A' (Z.of_nat j1) mod p = v mod p).
    { apply PlonkishLookupPoly.sub_mod_zero_iff in Hr_zero.
      rewrite !Zmod_mod in Hr_zero.
      rewrite <- (PlonkishLookupPoly.opp_mod_opp (p := p)
        (A' (Z.of_nat j1))).
      rewrite <- Hr_zero.
      apply PlonkishLookupPoly.opp_mod_opp. }
    (* the chain into the S' values *)
    assert (Hj1u : Z.of_nat j1 < u)
      by (clear -Hun Hj1; rewrite <- Hun; apply Nat2Z.inj_lt; lia).
    assert (Hj1u' : Z.of_nat j1 < Domain.usable_rows domain)
      by (exact Hj1u).
    destruct (PlonkishLookupPoly.permuted_chain (p := p)
      domain pairs theta x0 gamma0 A' S' Zp0
      Hbf Hu Hrules0 j1 Hj1u') as (j' & Hj'le & HAS).
    assert (HvS : S' (Z.of_nat j') mod p = v mod p)
      by (rewrite <- HAS; exact HvA).
    assert (Hroot_S' :
      Poly.eval (p := p) (Poly.prod_lin (p := p) NS') ((- v) mod p) = 0).
    { apply (Poly.eval_prod_lin_zero (p := p) NS' ((- v) mod p)
        ((- S' (Z.of_nat j')) mod p)).
      - unfold NS'.
        apply (List.in_map (fun j => (- S' (Z.of_nat j)) mod p)).
        apply List.in_seq. clear -Hj'le Hj1. lia.
      - apply PlonkishLookupPoly.sub_mod_zero_iff.
        rewrite !Zmod_mod.
        apply PlonkishLookupPoly.opp_mod_congr.
        symmetry. exact HvS. }
    assert (Hroot_s :
      Poly.eval (p := p) (Poly.prod_lin (p := p) Ns) ((- v) mod p) = 0).
    { rewrite <- (Poly.eval_peq (p := p) _ _ ((- v) mod p) HpeqS).
      exact Hroot_S'. }
    destruct (PlonkishLookupPoly.eval_prod_lin_zero_inv (p := p)
      Ns ((- v) mod p) Hroot_s)
      as (r2 & Hr2_in & Hr2_zero).
    unfold Ns in Hr2_in.
    apply List.in_map_iff in Hr2_in.
    destruct Hr2_in as (t & Hr2_eq & Ht).
    apply List.in_seq in Ht.
    subst r2.
    exists t.
    split; [exact (proj2 Ht) |].
    assert (Hct : comb_table pairs theta (Z.of_nat t) mod p = v mod p).
    { apply PlonkishLookupPoly.sub_mod_zero_iff in Hr2_zero.
      rewrite !Zmod_mod in Hr2_zero.
      rewrite <- (PlonkishLookupPoly.opp_mod_opp (p := p)
        (comb_table pairs theta (Z.of_nat t))).
      rewrite <- Hr2_zero.
      apply PlonkishLookupPoly.opp_mod_opp. }
    unfold v in Hct.
    unfold PlonkishLookupPoly.comb_input, PlonkishLookupPoly.comb_table
      in Hct |- *.
    rewrite !PlonkishLookupPoly.comb_canonical in Hct.
    symmetry. exact Hct.
  Qed.

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
      apply PlonkishLookupPoly.In_firstn in Hth.
      unfold fiber in Hth.
      apply List.filter_In in Hth. exact (proj1 Hth). }
    assert (Hths_ndp : Poly.NoDupP (p := p) ths).
    { unfold Poly.NoDupP, ths.
      rewrite <- List.firstn_map.
      apply PlonkishLookupPoly.NoDup_firstn.
      unfold fiber.
      apply PermutationPoly.NoDup_map_filter.
      exact Hth_ndp. }
    assert (Hth_agree : forall th, List.In th ths ->
      comb_input pairs th row = comb_table pairs th (Z.of_nat t)).
    { intros th Hth.
      assert (Hth' : List.In th fiber)
        by (unfold ths in Hth;
            exact (PlonkishLookupPoly.In_firstn m fiber th Hth)).
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
    destruct (per_theta_membership_of_pools domain pairs theta Hbf Hu
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
    destruct (per_theta_membership_of_pools domain pairs theta Hbf Hu
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
