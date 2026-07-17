(** * Orbit theory of an injective self-map on a finite domain.

    Generic support for the forward direction of the permutation
    correctness proof ([Halo2/plonkish/sigma.v]): reachability by
    iterating a function that is injective on, and closed over, a
    finite domain is an equivalence relation, decidable, and every
    point has a positive period (pigeonhole on the iterates).  On top
    of that, the merge section characterises the splice
    [f' = f ∘ τ_{a,b}] — the mapping surgery [Sigma.copy] performs —
    when [a] and [b] lie in distinct orbits of [f]: the two orbits fuse
    into a single orbit of [f'] and every other orbit is untouched.
    The file is generic over the point type; nothing is specific to
    cells, grids, or Orchard. *)

Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.Arith.Wf_nat.
Require Import Stdlib.micromega.Lia.

Import ListNotations.

Module FiniteOrbit.

(** [d] is reachable from [c] by iterating [f]; the shape matches the
    [reach] of [Halo2/plonkish/sigma.v] definitionally. *)
Definition reach {A : Type} (f : A -> A) (c d : A) : Prop :=
  exists k, Nat.iter k f c = d.

Lemma reach_refl {A : Type} (f : A -> A) (c : A) : reach f c c.
Proof. exists O. reflexivity. Qed.

Lemma reach_step {A : Type} (f : A -> A) (c : A) : reach f c (f c).
Proof. exists 1%nat. reflexivity. Qed.

Lemma reach_trans {A : Type} (f : A -> A) (c d e : A) :
  reach f c d -> reach f d e -> reach f c e.
Proof.
  intros [k Hk] [l Hl]. exists (l + k)%nat.
  rewrite Nat.iter_add. rewrite Hk. exact Hl.
Qed.

Lemma reach_f {A : Type} (f : A -> A) (c d : A) :
  reach f c d -> reach f c (f d).
Proof.
  intro H. eapply reach_trans; [exact H | apply reach_step].
Qed.

(** ** Minimal witnesses of decidable predicates on [nat] *)

Lemma dec_ex_lt (P : nat -> Prop) (Pdec : forall n, {P n} + {~ P n}) :
  forall N, {exists j, (j < N)%nat /\ P j} + {forall j, (j < N)%nat -> ~ P j}.
Proof.
  induction N as [|N IH].
  - right. intros j Hj. lia.
  - destruct IH as [Hyes | Hno].
    + left. destruct Hyes as [j [Hj HP]]. exists j. split; [lia | exact HP].
    + destruct (Pdec N) as [HP | HP].
      * left. exists N. split; [lia | exact HP].
      * right. intros j Hj.
        destruct (Nat.eq_dec j N) as [-> | Hne]; [exact HP |].
        apply Hno. lia.
Qed.

Lemma min_witness (P : nat -> Prop) (Pdec : forall n, {P n} + {~ P n}) :
  forall n, P n ->
  exists m, (m <= n)%nat /\ P m /\ forall j, (j < m)%nat -> ~ P j.
Proof.
  intros n. induction n as [n IH] using lt_wf_ind. intro Hn.
  destruct (dec_ex_lt P Pdec n) as [Hyes | Hno].
  - destruct Hyes as [j [Hj HP]].
    destruct (IH j Hj HP) as [m [Hle [HPm Hmin]]].
    exists m. split; [lia | split; assumption].
  - exists n. split; [lia | split; [exact Hn | exact Hno]].
Qed.

(** ** Pigeonhole: a list longer than its support has a repeated entry *)

Lemma pigeonhole_nth {A : Type}
    (eq_dec : forall x y : A, {x = y} + {x <> y}) (d : A) :
  forall (l bound : list A),
    (forall x, In x l -> In x bound) ->
    (List.length bound < List.length l)%nat ->
    exists i j,
      (i < j)%nat /\ (j < List.length l)%nat /\
      List.nth i l d = List.nth j l d.
Proof.
  induction l as [|a l IH]; intros bound Hincl Hlen; simpl in Hlen; [lia |].
  destruct (in_dec eq_dec a l) as [Hin | Hnotin].
  - (* the head repeats inside the tail *)
    destruct (In_nth l a d Hin) as [j [Hj Hnth]].
    exists O, (S j). split; [lia |]. split; [simpl; lia |].
    simpl. symmetry. exact Hnth.
  - (* the head is fresh: shrink the support and recurse *)
    assert (Hin_a : In a bound) by (apply Hincl; left; reflexivity).
    destruct (IH (remove eq_dec a bound)) as [i [j [Hij [Hj Heq]]]].
    + intros x Hx. apply in_in_remove.
      * intro; subst x. exact (Hnotin Hx).
      * apply Hincl. right. exact Hx.
    + pose proof (remove_length_lt eq_dec bound a Hin_a). lia.
    + exists (S i), (S j). split; [lia |]. split; [simpl; lia |].
      simpl. exact Heq.
Qed.

Lemma nth_map_seq' {A : Type} (F : nat -> A) (len i : nat) (d : A) :
  (i < len)%nat -> List.nth i (List.map F (List.seq 0 len)) d = F i.
Proof.
  intro H.
  rewrite (nth_indep _ d (F O))
    by (rewrite length_map, length_seq; exact H).
  rewrite map_nth. rewrite seq_nth by exact H. reflexivity.
Qed.

Section WithDomain.
  Context {A : Type}.
  Context (eq_dec : forall x y : A, {x = y} + {x <> y}).
  Context (dom : A -> Prop).
  Context (enum : list A).
  Context (Henum : forall x, dom x -> In x enum).

  Section Basic.
    Context (f : A -> A).
    Context (Hclosed : forall x, dom x -> dom (f x)).
    Context (Hinj : forall x y, dom x -> dom y -> f x = f y -> x = y).

    Lemma iter_dom (k : nat) (x : A) : dom x -> dom (Nat.iter k f x).
    Proof.
      intro Hx. induction k as [|k IH]; simpl; [exact Hx |].
      apply Hclosed. exact IH.
    Qed.

    Lemma iter_inj (k : nat) (x y : A) :
      dom x -> dom y -> Nat.iter k f x = Nat.iter k f y -> x = y.
    Proof.
      intros Hx Hy. induction k as [|k IH]; simpl; intro H; [exact H |].
      apply IH. apply Hinj; [apply iter_dom; exact Hx | apply iter_dom; exact Hy | exact H].
    Qed.

    Lemma reach_dom (x y : A) : dom x -> reach f x y -> dom y.
    Proof.
      intros Hx [k Hk]. subst y. apply iter_dom. exact Hx.
    Qed.

    (** Cancellation of a common iterate prefix. *)
    Lemma iter_cancel (i j : nat) (x : A) :
      dom x -> (i <= j)%nat -> Nat.iter i f x = Nat.iter j f x ->
      Nat.iter (j - i) f x = x.
    Proof.
      intros Hx Hij H.
      apply (iter_inj i); [apply iter_dom; exact Hx | exact Hx |].
      rewrite <- Nat.iter_add.
      replace (i + (j - i))%nat with j by lia.
      symmetry. exact H.
    Qed.

    (** Pigeonhole on the iterates: every domain point has a positive
        period. *)
    Lemma period_exists (x : A) :
      dom x -> exists m, (0 < m)%nat /\ Nat.iter m f x = x.
    Proof.
      intro Hx.
      set (l := List.map (fun k => Nat.iter k f x) (List.seq 0 (S (List.length enum)))).
      assert (Hlen : List.length l = S (List.length enum)).
      { unfold l. rewrite length_map, length_seq. reflexivity. }
      destruct (pigeonhole_nth eq_dec x l enum) as [i [j [Hij [Hj Heq]]]].
      - intros y Hy. unfold l in Hy.
        apply in_map_iff in Hy. destruct Hy as [k [Hk _]]. subst y.
        apply Henum. apply iter_dom. exact Hx.
      - rewrite Hlen. lia.
      - rewrite Hlen in Hj.
        unfold l in Heq.
        rewrite (nth_map_seq' _ _ i) in Heq by lia.
        rewrite (nth_map_seq' _ _ j) in Heq by lia.
        exists (j - i)%nat. split; [lia |].
        apply iter_cancel; [exact Hx | lia | exact Heq].
    Qed.

    Lemma iter_eq_dec (x y : A) (k : nat) :
      {Nat.iter k f x = y} + {Nat.iter k f x <> y}.
    Proof. apply eq_dec. Qed.

    (** The minimal positive period, bounded by the domain size. *)
    Lemma minimal_period (x : A) :
      dom x ->
      exists m,
        (0 < m)%nat /\ (m <= List.length enum)%nat /\
        Nat.iter m f x = x /\
        forall j, (0 < j < m)%nat -> Nat.iter j f x <> x.
    Proof.
      intro Hx.
      destruct (period_exists x Hx) as [m0 [Hm0 Hiter0]].
      assert (Pdec : forall n,
        {(0 < n)%nat /\ Nat.iter n f x = x} +
        {~ ((0 < n)%nat /\ Nat.iter n f x = x)}).
      { intro n. destruct n as [|n].
        - right. intros [H _]. lia.
        - destruct (eq_dec (Nat.iter (S n) f x) x) as [He | Hne].
          + left. split; [lia | exact He].
          + right. intros [_ H]. exact (Hne H). }
      destruct (min_witness
                  (fun m => (0 < m)%nat /\ Nat.iter m f x = x)
                  Pdec m0 (conj Hm0 Hiter0))
        as [m [Hle [[Hpos Hiter] Hmin]]].
      assert (Hbound : (m <= List.length enum)%nat).
      { (* the [m] iterates are pairwise distinct domain points *)
        set (l := List.map (fun k => Nat.iter k f x) (List.seq 0 m)).
        assert (Hlenl : List.length l = m).
        { unfold l. rewrite length_map, length_seq. reflexivity. }
        rewrite <- Hlenl.
        apply NoDup_incl_length.
        - apply NoDup_nth with (d := x).
          intros i j Hi Hj Heq.
          rewrite Hlenl in Hi, Hj.
          unfold l in Heq.
          rewrite (nth_map_seq' _ _ i) in Heq by exact Hi.
          rewrite (nth_map_seq' _ _ j) in Heq by exact Hj.
          destruct (Nat.lt_trichotomy i j) as [Hlt | [He | Hlt]]; [| exact He |].
          + exfalso. apply (Hmin (j - i)%nat); [lia |]. split; [lia |].
            apply iter_cancel; [exact Hx | lia | exact Heq].
          + exfalso. apply (Hmin (i - j)%nat); [lia |]. split; [lia |].
            apply iter_cancel; [exact Hx | lia | symmetry; exact Heq].
        - intros y Hy. unfold l in Hy.
          apply in_map_iff in Hy. destruct Hy as [k [Hk _]]. subst y.
          apply Henum. apply iter_dom. exact Hx. }
      exists m. split; [exact Hpos | split; [exact Hbound | split; [exact Hiter |]]].
      intros j Hj Heq. apply (Hmin j); [lia |]. split; [lia | exact Heq].
    Qed.

    Lemma iter_period_mult (x : A) (m q : nat) :
      Nat.iter m f x = x -> Nat.iter (q * m) f x = x.
    Proof.
      intro Hm. induction q as [|q IH]; simpl; [reflexivity |].
      rewrite Nat.iter_add. rewrite IH. exact Hm.
    Qed.

    (** Reachability reduced below any period. *)
    Lemma reach_reduce (x y : A) (m : nat) :
      (0 < m)%nat -> Nat.iter m f x = x -> reach f x y ->
      exists j, (j < m)%nat /\ Nat.iter j f x = y.
    Proof.
      intros Hm Hiter [k Hk].
      exists (k mod m)%nat. split; [apply Nat.mod_upper_bound; lia |].
      replace k with (k mod m + k / m * m)%nat in Hk
        by (pose proof (Nat.div_mod_eq k m); lia).
      rewrite Nat.iter_add in Hk.
      rewrite (iter_period_mult x m (k / m) Hiter) in Hk.
      exact Hk.
    Qed.

    (** Reachability is symmetric on the domain. *)
    Lemma reach_sym (x y : A) : dom x -> reach f x y -> reach f y x.
    Proof.
      intros Hx [k Hk].
      destruct (period_exists x Hx) as [m [Hm Hiter]].
      exists (k * m - k)%nat.
      subst y. rewrite <- Nat.iter_add.
      replace (k * m - k + k)%nat with (k * m)%nat by nia.
      apply iter_period_mult. exact Hiter.
    Qed.

    (** Reachability is decidable on the domain. *)
    Lemma reach_dec (x y : A) : dom x -> {reach f x y} + {~ reach f x y}.
    Proof.
      intro Hx.
      destruct (dec_ex_lt (fun j => Nat.iter j f x = y)
                  (fun j => iter_eq_dec x y j)
                  (S (List.length enum)))
        as [Hyes | Hno].
      - left. destruct Hyes as [j [_ Hj]]. exists j. exact Hj.
      - right. intro Hr.
        destruct (minimal_period x Hx) as [m [Hpos [Hbound [Hiter _]]]].
        destruct (reach_reduce x y m Hpos Hiter Hr) as [j [Hj Hj_eq]].
        apply (Hno j); [lia | exact Hj_eq].
    Qed.
  End Basic.

  (** ** The two-orbit merge

      [f'] agrees with [f] except at [a] and [b], whose images are
      swapped ([f' = f ∘ τ_{a,b}]).  When [a] and [b] lie in distinct
      orbits of [f], the orbits of [a] and [b] fuse into a single orbit
      of [f'] and every orbit avoiding both is untouched. *)
  Section Merge.
    Context (f : A -> A).
    Context (Hclosed : forall x, dom x -> dom (f x)).
    Context (Hinj : forall x y, dom x -> dom y -> f x = f y -> x = y).
    Context (a b : A).
    Context (Hda : dom a) (Hdb : dom b).
    Context (Hab : a <> b).
    Context (Hsep_ab : ~ reach f a b) (Hsep_ba : ~ reach f b a).
    Context (f' : A -> A).
    Context (Hf'a : f' a = f b).
    Context (Hf'b : f' b = f a).
    Context (Hf'o : forall x, x <> a -> x <> b -> f' x = f x).

    Lemma merge_closed (x : A) : dom x -> dom (f' x).
    Proof.
      intro Hx.
      destruct (eq_dec x a) as [-> | Hxa].
      { rewrite Hf'a. apply Hclosed. exact Hdb. }
      destruct (eq_dec x b) as [-> | Hxb].
      { rewrite Hf'b. apply Hclosed. exact Hda. }
      rewrite Hf'o by assumption. apply Hclosed. exact Hx.
    Qed.

    Lemma merge_inj (x y : A) : dom x -> dom y -> f' x = f' y -> x = y.
    Proof.
      intros Hx Hy H.
      destruct (eq_dec x a) as [-> | Hxa];
        destruct (eq_dec y a) as [-> | Hya];
        try reflexivity.
      - destruct (eq_dec y b) as [-> | Hyb].
        + rewrite Hf'a, Hf'b in H.
          exfalso. apply Hab. symmetry. apply Hinj; assumption.
        + rewrite Hf'a, (Hf'o y Hya Hyb) in H.
          exfalso. apply Hyb. symmetry. apply Hinj; assumption.
      - destruct (eq_dec x b) as [-> | Hxb].
        + rewrite Hf'b, Hf'a in H.
          exfalso. apply Hab. apply Hinj; assumption.
        + rewrite (Hf'o x Hxa Hxb), Hf'a in H.
          exfalso. apply Hxb. apply Hinj; assumption.
      - destruct (eq_dec x b) as [-> | Hxb];
          destruct (eq_dec y b) as [-> | Hyb];
          try reflexivity.
        + rewrite Hf'b, (Hf'o y Hya Hyb) in H.
          exfalso. apply Hya. symmetry. apply Hinj; assumption.
        + rewrite (Hf'o x Hxa Hxb), Hf'b in H.
          exfalso. apply Hxa. apply Hinj; assumption.
        + rewrite (Hf'o x Hxa Hxb), (Hf'o y Hya Hyb) in H.
          apply Hinj; assumption.
    Qed.

    (** Iterates avoiding [a] and [b] transport from [f] to [f']. *)
    Lemma iter_transport (k : nat) (x : A) :
      (forall i, (i < k)%nat ->
        Nat.iter i f x <> a /\ Nat.iter i f x <> b) ->
      Nat.iter k f' x = Nat.iter k f x.
    Proof.
      induction k as [|k IH]; intro Havoid; simpl; [reflexivity |].
      rewrite IH by (intros i Hi; apply Havoid; lia).
      destruct (Havoid k ltac:(lia)) as [Hna Hnb].
      apply Hf'o; assumption.
    Qed.

    (** The [f']-path out of [a] runs along the [f]-orbit of [b]. *)
    Lemma merge_path_b (m i : nat) :
      Nat.iter m f b = b ->
      (forall j, (0 < j < m)%nat -> Nat.iter j f b <> b) ->
      (0 < i <= m)%nat ->
      Nat.iter i f' a = Nat.iter i f b.
    Proof.
      intros Hper Hmin Hi.
      destruct i as [|i]; [lia |].
      rewrite Nat.iter_succ_r, Hf'a.
      rewrite iter_transport.
      - rewrite <- Nat.iter_succ_r. reflexivity.
      - intros j Hj.
        rewrite <- Nat.iter_succ_r.
        split.
        + intro Heq. apply Hsep_ba. exists (S j). exact Heq.
        + intro Heq. apply (Hmin (S j)); [lia | exact Heq].
    Qed.

    (** Symmetric path: the [f']-path out of [b] runs along the
        [f]-orbit of [a]. *)
    Lemma merge_path_a (m i : nat) :
      Nat.iter m f a = a ->
      (forall j, (0 < j < m)%nat -> Nat.iter j f a <> a) ->
      (0 < i <= m)%nat ->
      Nat.iter i f' b = Nat.iter i f a.
    Proof.
      intros Hper Hmin Hi.
      destruct i as [|i]; [lia |].
      rewrite Nat.iter_succ_r, Hf'b.
      rewrite iter_transport.
      - rewrite <- Nat.iter_succ_r. reflexivity.
      - intros j Hj.
        rewrite <- Nat.iter_succ_r.
        split.
        + intro Heq. apply (Hmin (S j)); [lia | exact Heq].
        + intro Heq. apply Hsep_ab. exists (S j). exact Heq.
    Qed.

    Lemma merge_reach_ab : reach f' a b.
    Proof.
      destruct (minimal_period f Hclosed Hinj b Hdb)
        as [m [Hpos [_ [Hper Hmin]]]].
      exists m.
      rewrite (merge_path_b m m Hper Hmin ltac:(lia)).
      exact Hper.
    Qed.

    (** Every point of either fused orbit is [f']-reachable from [a]. *)
    Lemma merge_reach_from_a (z : A) :
      dom z -> reach f a z \/ reach f b z -> reach f' a z.
    Proof.
      intros Hz [Hr | Hr].
      - destruct (minimal_period f Hclosed Hinj a Hda)
          as [m [Hpos [_ [Hper Hmin]]]].
        destruct (reach_reduce f a z m Hpos Hper Hr) as [j [Hj Hjeq]].
        destruct j as [|j].
        + simpl in Hjeq. subst z. apply reach_refl.
        + apply reach_trans with (d := b); [exact merge_reach_ab |].
          exists (S j).
          rewrite (merge_path_a m (S j) Hper Hmin ltac:(lia)).
          exact Hjeq.
      - destruct (minimal_period f Hclosed Hinj b Hdb)
          as [m [Hpos [_ [Hper Hmin]]]].
        destruct (reach_reduce f b z m Hpos Hper Hr) as [j [Hj Hjeq]].
        destruct j as [|j].
        + simpl in Hjeq. subst z. exact merge_reach_ab.
        + exists (S j).
          rewrite (merge_path_b m (S j) Hper Hmin ltac:(lia)).
          exact Hjeq.
    Qed.

    (** Orbits avoiding [a] and [b] are untouched by the splice. *)
    Lemma untouched_iter (x : A) :
      dom x -> ~ reach f x a -> ~ reach f x b ->
      forall n, Nat.iter n f' x = Nat.iter n f x.
    Proof.
      intros Hx Hna Hnb n.
      apply iter_transport.
      intros i _. split.
      - intro Heq. apply Hna. exists i. exact Heq.
      - intro Heq. apply Hnb. exists i. exact Heq.
    Qed.

    (** Reachability is preserved by the merge. *)
    Lemma merge_preserve (x y : A) :
      dom x -> reach f x y -> reach f' x y.
    Proof.
      intros Hx Hr.
      destruct (reach_dec f Hclosed Hinj x a Hx) as [Hxa | Hxa].
      - (* x lies in the orbit of a *)
        pose proof (reach_sym f Hclosed Hinj x a Hx Hxa) as Hax.
        pose proof (reach_trans f a x y Hax Hr) as Hay.
        assert (H'ax : reach f' a x).
        { apply merge_reach_from_a; [exact Hx | left; exact Hax]. }
        assert (H'ay : reach f' a y).
        { apply merge_reach_from_a;
            [exact (reach_dom f Hclosed a y Hda Hay) | left; exact Hay]. }
        exact (reach_trans f' x a y
          (reach_sym f' merge_closed merge_inj a x Hda H'ax) H'ay).
      - destruct (reach_dec f Hclosed Hinj x b Hx) as [Hxb | Hxb].
        + (* x lies in the orbit of b *)
          pose proof (reach_sym f Hclosed Hinj x b Hx Hxb) as Hbx.
          pose proof (reach_trans f b x y Hbx Hr) as Hby.
          assert (H'ax : reach f' a x).
          { apply merge_reach_from_a; [exact Hx | right; exact Hbx]. }
          assert (H'ay : reach f' a y).
          { apply merge_reach_from_a;
              [exact (reach_dom f Hclosed b y Hdb Hby) | right; exact Hby]. }
          exact (reach_trans f' x a y
            (reach_sym f' merge_closed merge_inj a x Hda H'ax) H'ay).
        + (* the orbit of x avoids both *)
          destruct Hr as [k Hk].
          exists k. rewrite untouched_iter; assumption.
    Qed.

    (** The fused orbit is closed under [f']-iteration. *)
    Lemma merge_orbit_step (z : A) :
      dom z -> reach f a z \/ reach f b z ->
      reach f a (f' z) \/ reach f b (f' z).
    Proof.
      intros Hz Hr.
      destruct (eq_dec z a) as [-> | Hza].
      { right. rewrite Hf'a. apply reach_step. }
      destruct (eq_dec z b) as [-> | Hzb].
      { left. rewrite Hf'b. apply reach_step. }
      rewrite Hf'o by assumption.
      destruct Hr as [Hr | Hr]; [left | right]; apply reach_f; exact Hr.
    Qed.

    Lemma merge_orbit_iter (z : A) (n : nat) :
      dom z -> reach f a z \/ reach f b z ->
      dom (Nat.iter n f' z) /\
      (reach f a (Nat.iter n f' z) \/ reach f b (Nat.iter n f' z)).
    Proof.
      intros Hz Hr. induction n as [|n [IHdom IHr]]; simpl.
      - split; assumption.
      - split.
        + apply merge_closed. exact IHdom.
        + apply merge_orbit_step; assumption.
    Qed.
  End Merge.
End WithDomain.

End FiniteOrbit.
