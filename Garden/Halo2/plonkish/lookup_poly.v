(** * Polynomial semantics of the halo2 lookup argument.

    The deployed verifier checks five polynomial rules per lookup argument
    ([plonk/lookup/verifier.rs] [expressions()]), over the running product
    [Z], the permuted input column [A'] and the permuted table column [S'],
    with the compressed input [A = θ^{m−1}·a_0 + … + a_{m−1}] and table
    [S] combined by the challenge [θ] and offset by the challenges
    [β], [γ]:

    - [l_0 · (1 − Z) = 0];
    - [l_last · (Z² − Z) = 0];
    - [(1 − (l_last + l_blind)) ·
       (Z(ωX)·(A'+β)(S'+γ) − Z(X)·(A+β)(S+γ)) = 0];
    - [l_0 · (A' − S') = 0];
    - [(1 − (l_last + l_blind)) · (A' − S')·(A' − A'(ω⁻¹X)) = 0].

    This file proves the rules equivalent to the set-membership reading the
    relational model uses ([eval_lookup_argument], [Halo2/proof.v]): every
    usable-row input tuple appears among the table rows.  The rules are
    stated on the row set of the cyclic domain — the identity at [ω^row]
    reads the witness functions at [row], and the rotations [ωX] / [ω⁻¹X]
    read [Domain.rot] — with the challenges quantified:

    - [θ] universally — the permuted columns [A'], [S'] may depend on it
      (they are committed after [θ] is drawn);
    - [β], [γ] universally over the *regular* challenges
      ([lookup_challenge_regular]: no compressed input or table factor
      vanishes), with the product [Z] chosen per challenge (it is committed
      after [β], [γ]).  The excluded set has at most [2·usable_rows]
      residues per [θ]; on it the running-product recurrence divides by
      zero, so even the honest witness satisfies no product column — the
      exclusion is what makes the completeness direction true, and the
      soundness direction never consumes the excluded challenges.

    [lookup_sound]: the rules force membership.  The proof telescopes the
    product rule over the usable rows (the boolean [l_last] escape is
    closed by the nonvanishing chain), reads the two factor products as
    monic linear-factor polynomials evaluated at the challenge, identifies
    them via the root bound ([prod_lin_scaled_agreement]), walks the
    permuted-column chain ([l_0] boot plus the [A' − A'(ω⁻¹X)] rule), and
    de-combines the [θ]-Horner equality into tuple equality by pigeonhole
    over [usable_rows · m + 1] challenge points.  Membership lands in the
    table *columns* over the usable rows; the decidable prefix condition
    [table_prefix_coherent_b] (each padding row repeats a loaded-prefix
    row) moves the witness into the loaded [table_rows] prefix — the
    tables-as-fixed-prefix coherence of the lookup model.

    [lookup_complete]: membership yields witnesses.  [A'] sorts the
    compressed inputs ([zsort]), [S'] aligns each run start with a table
    occurrence ([build_s]), and [Z] is the running product built with
    [mod_inverse].

    The statements are value-level over abstract per-pair functions
    [(input, table) : (Z -> Z) * (Z -> Z)]; [argument_pair_functions]
    instantiates them for a [LookupArgument.t] under an assignment, and
    [lookup_argument_sound] / [lookup_argument_complete] /
    [lookup_arguments_sound] restate the equivalence against
    [eval_lookup_argument] — the exact conjunct shape of
    [PlonkishLookup.plonkish_accepts_compiled]. *)

Require Import Garden.Field.Field.
Require Import Garden.Field.Div.
Require Import Garden.Field.Lemmas.
Require Import Garden.Halo2.main.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.lemmas.
Require Import Garden.Halo2.plonkish.main.
Require Import Garden.Halo2.plonkish.poly.
Require Import Stdlib.Sorting.Permutation.
Require Import Stdlib.micromega.Lia.

Import ListNotations.
Global Open Scope Z_scope.

Module PlonkishLookupPoly.

Import Plonkish.

Section WithPrime.
  Context {p : Z}.
  Context `{Prime p}.

  (** ** Products of field residues *)

  Definition prodl (l : list Z) : Z :=
    List.fold_right (fun v acc => (v * acc) mod p) 1 l.

  Lemma prodl_nil : prodl [] = 1.
  Proof. reflexivity. Qed.

  Lemma prodl_cons (v : Z) (l : list Z) :
    prodl (v :: l) = (v * prodl l) mod p.
  Proof. reflexivity. Qed.

  Lemma prodl_canonical (l : list Z) : prodl l mod p = prodl l.
  Proof.
    destruct l.
    - rewrite prodl_nil. apply Z.mod_1_l. exact (prime_range (p := p)).
    - rewrite prodl_cons. apply Zmod_mod.
  Qed.

  Lemma prodl_app (l1 l2 : list Z) :
    prodl (l1 ++ l2) = (prodl l1 * prodl l2) mod p.
  Proof.
    induction l1 as [| v l1 IH].
    - cbn [List.app]. rewrite prodl_nil, Z.mul_1_l.
      symmetry. apply prodl_canonical.
    - cbn [List.app]. rewrite !prodl_cons, IH. mod_ring_solve.
  Qed.

  Lemma prodl_perm (l1 l2 : list Z) :
    Permutation l1 l2 -> prodl l1 = prodl l2.
  Proof.
    intros Hperm; induction Hperm.
    - reflexivity.
    - rewrite !prodl_cons, IHHperm. reflexivity.
    - rewrite !prodl_cons. mod_ring_solve.
    - congruence.
  Qed.

  Lemma prodl_map_congr {A : Set} (f g : A -> Z) (l : list A) :
    (forall a, List.In a l -> f a mod p = g a mod p) ->
    prodl (List.map f l) = prodl (List.map g l).
  Proof.
    induction l as [| a l IH]; intros Hfg; [reflexivity |].
    cbn [List.map]. rewrite !prodl_cons.
    rewrite IH by (intros b Hb; apply Hfg; right; exact Hb).
    rewrite Zmult_mod, (Hfg a (or_introl eq_refl)), <- Zmult_mod.
    reflexivity.
  Qed.

  Lemma prodl_nonzero (l : list Z) :
    (forall v, List.In v l -> v mod p <> 0) -> prodl l <> 0.
  Proof.
    induction l as [| v l IH]; intros Hnz.
    - rewrite prodl_nil. lia.
    - rewrite prodl_cons. intros Hc.
      change ((v * prodl l) mod p) with (BinOp.mul v (prodl l)) in Hc.
      apply mul_zero_implies_zero in Hc.
      unfold UnOp.from in Hc.
      destruct Hc as [Hc | Hc].
      + exact (Hnz v (or_introl eq_refl) Hc).
      + rewrite prodl_canonical in Hc.
        exact (IH (fun w Hw => Hnz w (or_intror Hw)) Hc).
  Qed.

  Lemma prodl_split {A : Set} (h f g : A -> Z) (l : list A) :
    (forall a, List.In a l -> h a = (f a * g a) mod p) ->
    prodl (List.map h l) =
    (prodl (List.map f l) * prodl (List.map g l)) mod p.
  Proof.
    induction l as [| a l IH]; intros Hh.
    - cbn [List.map]. rewrite !prodl_nil, Z.mul_1_l.
      symmetry. apply Z.mod_1_l. exact (prime_range (p := p)).
    - cbn [List.map]. rewrite !prodl_cons.
      rewrite (Hh a (or_introl eq_refl)).
      rewrite IH by (intros b Hb; apply Hh; right; exact Hb).
      mod_ring_solve.
  Qed.

  (** ** Field-residue facts *)

  Lemma sub_mod_zero_iff (x y : Z) :
    (x - y) mod p = 0 <-> x mod p = y mod p.
  Proof. exact (sub_zero_equiv x y). Qed.

  Lemma mul_mod_zero_iff (x y : Z) :
    (x * y) mod p = 0 <-> x mod p = 0 \/ y mod p = 0.
  Proof. exact (mul_zero_implies_zero x y). Qed.

  Lemma mul_mod_zero_l (x y : Z) : x mod p = 0 -> (x * y) mod p = 0.
  Proof. intros Hx. apply mul_mod_zero_iff. left. exact Hx. Qed.

  Lemma mulmod_cancel_l (c x y : Z) :
    c mod p <> 0 -> (c * x) mod p = (c * y) mod p -> x mod p = y mod p.
  Proof.
    intros Hc He.
    pose proof (mod_inverse_mul_prime c Hc) as Hi.
    change (BinOp.mul (mod_inverse c p) c) with ((mod_inverse c p * c) mod p)
      in Hi.
    transitivity ((mod_inverse c p * c * x) mod p).
    - symmetry. rewrite Zmult_mod, Hi, Z.mul_1_l, Zmod_mod. reflexivity.
    - transitivity ((mod_inverse c p * (c * x)) mod p); [mod_ring_solve |].
      rewrite Zmult_mod, He, <- Zmult_mod.
      transitivity ((mod_inverse c p * c * y) mod p); [mod_ring_solve |].
      rewrite Zmult_mod, Hi, Z.mul_1_l, Zmod_mod. reflexivity.
  Qed.

  (** ** Removal of one occurrence, and of a distinct-value batch *)

  Fixpoint remove_one (v : Z) (l : list Z) : list Z :=
    match l with
    | [] => []
    | w :: l' => if w =? v then l' else w :: remove_one v l'
    end.

  Lemma remove_one_perm (v : Z) (l : list Z) :
    List.In v l -> Permutation l (v :: remove_one v l).
  Proof.
    induction l as [| w l IH]; intros Hin; [destruct Hin |].
    simpl. destruct (Z.eqb_spec w v) as [-> | Hne].
    - apply Permutation_refl.
    - destruct Hin as [-> | Hin]; [congruence |].
      eapply Permutation_trans; [apply perm_skip, (IH Hin) |].
      apply perm_swap.
  Qed.

  Lemma remove_one_in_other (v w : Z) (l : list Z) :
    List.In w l -> w <> v -> List.In w (remove_one v l).
  Proof.
    induction l as [| x l IH]; intros Hin Hne; [destruct Hin |].
    simpl. destruct (Z.eqb_spec x v) as [-> | Hxv].
    - destruct Hin as [-> | Hin]; [congruence | exact Hin].
    - destruct Hin as [-> | Hin];
        [left; reflexivity | right; exact (IH Hin Hne)].
  Qed.

  Definition remove_all (vs l : list Z) : list Z :=
    List.fold_left (fun acc v => remove_one v acc) vs l.

  Lemma remove_all_perm (vs : list Z) :
    forall l : list Z,
    List.NoDup vs -> (forall v, List.In v vs -> List.In v l) ->
    Permutation l (vs ++ remove_all vs l).
  Proof.
    induction vs as [| v vs IH]; intros l Hnd Hin; simpl.
    - apply Permutation_refl.
    - inversion Hnd as [| ? ? Hnotin Hnd']; subst.
      eapply Permutation_trans;
        [apply (remove_one_perm v l (Hin v (or_introl eq_refl))) |].
      apply perm_skip.
      apply IH; [exact Hnd' |].
      intros w Hw.
      apply remove_one_in_other; [apply Hin; right; exact Hw |].
      intros ->. exact (Hnotin Hw).
  Qed.

  (** ** Insertion sort *)

  Fixpoint zinsert (v : Z) (l : list Z) : list Z :=
    match l with
    | [] => [v]
    | w :: l' => if v <=? w then v :: w :: l' else w :: zinsert v l'
    end.

  Fixpoint zsort (l : list Z) : list Z :=
    match l with
    | [] => []
    | v :: l' => zinsert v (zsort l')
    end.

  Lemma zinsert_perm (v : Z) (l : list Z) :
    Permutation (v :: l) (zinsert v l).
  Proof.
    induction l as [| w l IH]; simpl.
    - apply Permutation_refl.
    - destruct (v <=? w).
      + apply Permutation_refl.
      + eapply Permutation_trans; [apply perm_swap |].
        apply perm_skip. exact IH.
  Qed.

  Lemma zsort_perm (l : list Z) : Permutation l (zsort l).
  Proof.
    induction l as [| v l IH]; simpl; [apply Permutation_refl |].
    eapply Permutation_trans; [apply perm_skip, IH |].
    apply zinsert_perm.
  Qed.

  (** [chain prev l]: the list ascends, starting at or above [prev]. *)
  Fixpoint chain (prev : Z) (l : list Z) : Prop :=
    match l with
    | [] => True
    | v :: l' => prev <= v /\ chain v l'
    end.

  Definition ascending (l : list Z) : Prop :=
    match l with
    | [] => True
    | v :: l' => chain v l'
    end.

  Lemma chain_zinsert (l : list Z) :
    forall prev v : Z,
    chain prev l -> prev <= v -> chain prev (zinsert v l).
  Proof.
    induction l as [| w l IH]; intros prev v Hc Hpv; simpl.
    - exact (conj Hpv I).
    - destruct Hc as [Hpw Hc].
      destruct (Z.leb_spec v w) as [Hvw | Hwv]; simpl.
      + exact (conj Hpv (conj Hvw Hc)).
      + refine (conj Hpw (IH w v Hc _)). lia.
  Qed.

  Lemma zinsert_ascending (v : Z) (l : list Z) :
    ascending l -> ascending (zinsert v l).
  Proof.
    destruct l as [| w l]; simpl; intros Hasc.
    - exact I.
    - destruct (Z.leb_spec v w) as [Hvw | Hwv]; simpl.
      + exact (conj Hvw Hasc).
      + refine (chain_zinsert l w v Hasc _). lia.
  Qed.

  Lemma zsort_ascending (l : list Z) : ascending (zsort l).
  Proof.
    induction l as [| v l IH]; simpl;
      [exact I | exact (zinsert_ascending v _ IH)].
  Qed.

  (** ** Run structure of a grouped list *)

  (** The run-start values (first of each block of equal adjacent values). *)
  Fixpoint dedup_from (prev : Z) (l : list Z) : list Z :=
    match l with
    | [] => []
    | v :: l' => if v =? prev then dedup_from prev l' else v :: dedup_from v l'
    end.

  (** The number of positions equal to their predecessor. *)
  Fixpoint repeats_from (prev : Z) (l : list Z) : nat :=
    match l with
    | [] => O
    | v :: l' =>
        if v =? prev then S (repeats_from prev l') else repeats_from v l'
    end.

  Lemma dedup_repeats_length (l : list Z) :
    forall prev : Z,
    List.length l =
    (List.length (dedup_from prev l) + repeats_from prev l)%nat.
  Proof.
    induction l as [| v l IH]; intros prev; simpl; [reflexivity |].
    destruct (v =? prev); simpl; [rewrite (IH prev) | rewrite (IH v)]; lia.
  Qed.

  Lemma dedup_from_lower (l : list Z) :
    forall prev : Z,
    chain prev l -> forall w, List.In w (dedup_from prev l) -> prev < w.
  Proof.
    induction l as [| v l IH]; intros prev Hc w Hin; simpl in Hin;
      [destruct Hin |].
    destruct Hc as [Hpv Hc].
    destruct (Z.eqb_spec v prev) as [-> | Hne].
    - exact (IH prev Hc w Hin).
    - destruct Hin as [-> | Hin]; [lia |].
      pose proof (IH v Hc w Hin). lia.
  Qed.

  Lemma dedup_from_nodup (l : list Z) :
    forall prev : Z,
    chain prev l -> List.NoDup (dedup_from prev l).
  Proof.
    induction l as [| v l IH]; intros prev Hc; simpl; [constructor |].
    destruct Hc as [Hpv Hc].
    destruct (Z.eqb_spec v prev) as [-> | Hne].
    - exact (IH prev Hc).
    - constructor.
      + intros Hin. pose proof (dedup_from_lower l v Hc v Hin). lia.
      + exact (IH v Hc).
  Qed.

  Lemma dedup_from_incl (l : list Z) :
    forall (prev w : Z),
    List.In w (dedup_from prev l) -> List.In w l.
  Proof.
    induction l as [| v l IH]; intros prev w Hin; simpl in Hin;
      [exact Hin |].
    destruct (v =? prev).
    - right. exact (IH prev w Hin).
    - destruct Hin as [-> | Hin];
        [left; reflexivity | right; exact (IH v w Hin)].
  Qed.

  (** The aligned permuted table column: a run start emits the input value,
      a repeated position consumes the next spare table value. *)
  Fixpoint build_s (prev : Z) (a rest : list Z) : list Z :=
    match a with
    | [] => []
    | v :: a' =>
        if v =? prev then
          match rest with
          | [] => []
          | w :: rest' => w :: build_s v a' rest'
          end
        else v :: build_s v a' rest
    end.

  Lemma build_s_perm (a : list Z) :
    forall (prev : Z) (rest : list Z),
    List.length rest = repeats_from prev a ->
    Permutation (build_s prev a rest) (dedup_from prev a ++ rest).
  Proof.
    induction a as [| v a IH]; intros prev rest Hlen; simpl in *.
    - destruct rest; simpl in Hlen; [apply Permutation_refl | discriminate].
    - destruct (Z.eqb_spec v prev) as [-> | Hne].
      + destruct rest as [| w rest']; simpl in Hlen; [discriminate |].
        injection Hlen as Hlen.
        eapply Permutation_trans; [apply perm_skip, (IH prev rest' Hlen) |].
        apply Permutation_middle.
      + simpl. apply perm_skip. exact (IH v rest Hlen).
  Qed.

  Lemma build_s_align (a : list Z) :
    forall (prev : Z) (rest : list Z) (j : nat),
    (j < List.length a)%nat ->
    List.length rest = repeats_from prev a ->
    List.nth j (build_s prev a rest) 0 = List.nth j a 0 \/
    List.nth j a 0 =
      (match j with O => prev | S j' => List.nth j' a 0 end).
  Proof.
    induction a as [| v a IH]; intros prev rest j Hj Hlen; simpl in Hj;
      [lia |].
    simpl in Hlen. simpl.
    destruct (Z.eqb_spec v prev) as [-> | Hne].
    - destruct rest as [| w rest']; simpl in Hlen; [discriminate |].
      injection Hlen as Hlen.
      destruct j as [| j'].
      + right. reflexivity.
      + destruct (IH prev rest' j' ltac:(lia) Hlen) as [Hl | Hr].
        * left. exact Hl.
        * right. destruct j'; exact Hr.
    - destruct j as [| j'].
      + left. reflexivity.
      + destruct (IH v rest j' ltac:(lia) Hlen) as [Hl | Hr].
        * left. exact Hl.
        * right. destruct j'; exact Hr.
  Qed.

  (** ** Fibers of a bounded choice function: pigeonhole *)

  Lemma filter_length_split {A : Set} (f : A -> bool) (l : list A) :
    List.length l =
    (List.length (List.filter f l) +
     List.length (List.filter (fun a => negb (f a)) l))%nat.
  Proof.
    induction l as [| a l IH]; simpl; [reflexivity |].
    destruct (f a); simpl; lia.
  Qed.

  Lemma filter_filter_absorb {A : Set} (f g : A -> bool) (l : list A) :
    (forall a, f a = true -> g a = true) ->
    List.filter f (List.filter g l) = List.filter f l.
  Proof.
    induction l as [| a l IH]; intros Hfg; simpl; [reflexivity |].
    destruct (g a) eqn:Hg; simpl.
    - rewrite (IH Hfg). reflexivity.
    - destruct (f a) eqn:Hf.
      + pose proof (Hfg a Hf). congruence.
      + exact (IH Hfg).
  Qed.

  Lemma fiber_pigeonhole (B : nat) :
    forall (k : nat) (pick : Z -> nat) (l : list Z),
    (forall x, List.In x l -> (pick x < B)%nat) ->
    (B * k < List.length l)%nat ->
    exists t, (t < B)%nat /\
      (k < List.length
        (List.filter (fun x => Nat.eqb (pick x) t) l))%nat.
  Proof.
    induction B as [| B IH]; intros k pick l Hbound Hlen.
    - destruct l as [| x l]; simpl in Hlen; [lia |].
      pose proof (Hbound x (or_introl eq_refl)). lia.
    - destruct
        (Nat.ltb k
          (List.length (List.filter (fun x => Nat.eqb (pick x) B) l)))
        eqn:Hfib.
      + apply Nat.ltb_lt in Hfib.
        exists B. split; [lia | exact Hfib].
      + apply Nat.ltb_ge in Hfib.
        set (l' := List.filter (fun x => negb (Nat.eqb (pick x) B)) l).
        destruct (IH k pick l') as (t & Ht & Hfib').
        * intros x Hx.
          apply List.filter_In in Hx. destruct Hx as [Hx Hneq].
          apply Bool.negb_true_iff, Nat.eqb_neq in Hneq.
          pose proof (Hbound x Hx). lia.
        * pose proof
            (filter_length_split (fun x => Nat.eqb (pick x) B) l) as Hsplit.
          cbv beta in Hsplit. fold l' in Hsplit. lia.
        * exists t. split; [lia |].
          unfold l' in Hfib'.
          rewrite (filter_filter_absorb
            (fun x => Nat.eqb (pick x) t)
            (fun x => negb (Nat.eqb (pick x) B)) l) in Hfib';
            [exact Hfib' |].
          intros x Hx. apply Nat.eqb_eq in Hx.
          apply Bool.negb_true_iff, Nat.eqb_neq. lia.
  Qed.

  (** ** Repetition-free lists of canonical residues *)

  Lemma NoDup_map_inj {A B : Set} (f : A -> B) (l : list A) :
    (forall a b, f a = f b -> a = b) ->
    List.NoDup l -> List.NoDup (List.map f l).
  Proof.
    intros Hinj Hnd; induction Hnd; simpl; constructor.
    - intros Hin. apply List.in_map_iff in Hin.
      destruct Hin as (b & Hfb & Hb).
      apply Hinj in Hfb. subst. contradiction.
    - assumption.
  Qed.

  Lemma map_mod_id (l : list Z) :
    (forall x, List.In x l -> x mod p = x) ->
    List.map (fun x => x mod p) l = l.
  Proof.
    induction l as [| a l IH]; intros Hcan; simpl; [reflexivity |].
    rewrite (Hcan a (or_introl eq_refl)).
    rewrite IH by (intros x Hx; apply Hcan; right; exact Hx).
    reflexivity.
  Qed.

  Lemma NoDupP_of_canonical (l : list Z) :
    (forall x, List.In x l -> x mod p = x) ->
    List.NoDup l -> Poly.NoDupP (p := p) l.
  Proof.
    intros Hcan Hnd.
    unfold Poly.NoDupP.
    rewrite (map_mod_id l Hcan).
    exact Hnd.
  Qed.

  (** ** Selection of points avoiding a bad-residue list *)

  Lemma pick_good_points (bad : list Z) (g : nat) :
    Z.of_nat (List.length bad + g) <= p ->
    exists goodl : list Z,
      List.length goodl = g /\
      List.NoDup goodl /\
      (forall x, List.In x goodl -> 0 <= x < p) /\
      (forall x r, List.In x goodl -> List.In r bad ->
        (x - r) mod p <> 0).
  Proof.
    intros Hsize.
    set (N := (List.length bad + g)%nat).
    set (pool := List.map Z.of_nat (List.seq 0 N)).
    set (isgood :=
      fun x => negb (List.existsb (fun r => (r mod p) =? x) bad)).
    set (filt := List.filter isgood pool).
    assert (Hpool_len : List.length pool = N).
    { unfold pool. rewrite List.length_map, List.length_seq. reflexivity. }
    assert (Hpool_nd : List.NoDup pool).
    { unfold pool.
      apply NoDup_map_inj; [exact Nat2Z.inj | apply List.seq_NoDup]. }
    assert (Hpool_range : forall x, List.In x pool -> 0 <= x < p).
    { intros x Hx. unfold pool in Hx.
      apply List.in_map_iff in Hx. destruct Hx as (i & <- & Hi).
      apply List.in_seq in Hi.
      split; [lia |].
      apply Z.lt_le_trans with (Z.of_nat N); [lia | exact Hsize]. }
    assert (Hbadlen :
      (List.length (List.filter (fun x => negb (isgood x)) pool) <=
       List.length bad)%nat).
    { rewrite <- (List.length_map (fun r => r mod p) bad).
      apply List.NoDup_incl_length.
      - apply List.NoDup_filter. exact Hpool_nd.
      - intros x Hx.
        apply List.filter_In in Hx. destruct Hx as [Hx Hbad].
        unfold isgood in Hbad. rewrite Bool.negb_involutive in Hbad.
        apply List.existsb_exists in Hbad.
        destruct Hbad as (r & Hr & Heq).
        apply Z.eqb_eq in Heq.
        rewrite <- Heq.
        exact (List.in_map (fun v => v mod p) bad r Hr). }
    assert (Hfiltlen : (g <= List.length filt)%nat).
    { pose proof (filter_length_split isgood pool) as Hsplit.
      fold filt in Hsplit. lia. }
    exists (List.firstn g filt).
    assert (Hin_filt : forall x, List.In x (List.firstn g filt) ->
      List.In x pool /\ isgood x = true).
    { intros x Hx.
      apply List.filter_In.
      exact (In_firstn g filt x Hx). }
    split; [| split; [| split]].
    - apply List.firstn_length_le. exact Hfiltlen.
    - apply NoDup_firstn. apply List.NoDup_filter. exact Hpool_nd.
    - intros x Hx. apply Hpool_range. exact (proj1 (Hin_filt x Hx)).
    - intros x r Hx Hr Hzero.
      destruct (Hin_filt x Hx) as [Hxpool Hgood].
      unfold isgood in Hgood.
      apply Bool.negb_true_iff in Hgood.
      apply sub_mod_zero_iff in Hzero.
      assert (Hex : List.existsb (fun r' => (r' mod p) =? x) bad = true).
      { apply List.existsb_exists.
        exists r. split; [exact Hr |].
        apply Z.eqb_eq.
        rewrite <- Hzero.
        apply Z.mod_small. exact (Hpool_range x Hxpool). }
      congruence.
  Qed.

  (** ** The θ-Horner combination
      ([lookup/verifier.rs] [compress_expressions]:
      [θ^{m−1}·a_0 + … + a_{m−1}]) *)

  Definition comb (theta : Z) (values : list Z) : Z :=
    List.fold_left (fun acc v => (acc * theta + v) mod p) values 0.

  Lemma comb_canonical (theta : Z) (values : list Z) :
    comb theta values mod p = comb theta values.
  Proof.
    unfold comb.
    assert (Haux : forall (vs : list Z) (acc : Z),
      acc mod p = acc ->
      List.fold_left (fun a v => (a * theta + v) mod p) vs acc mod p =
      List.fold_left (fun a v => (a * theta + v) mod p) vs acc).
    { induction vs as [| v vs IH]; intros acc Hacc; simpl; [exact Hacc |].
      apply IH. apply Zmod_mod. }
    apply Haux. apply Zmod_0_l.
  Qed.

  Lemma comb_eval (theta : Z) (values : list Z) :
    comb theta values = Poly.eval (p := p) (List.rev values) theta.
  Proof.
    unfold comb.
    induction values as [| v values IH] using List.rev_ind.
    - simpl. reflexivity.
    - rewrite List.fold_left_app. simpl.
      rewrite List.rev_app_distr. simpl.
      rewrite <- IH.
      f_equal. ring.
  Qed.

  (** ** Linear-factor products against [prodl] *)

  Lemma eval_prod_lin_prodl (l : list Z) (x : Z) :
    Poly.eval (p := p) (Poly.prod_lin (p := p) l) x =
    prodl (List.map (fun r => (x - r) mod p) l).
  Proof.
    induction l as [| r l IH].
    - cbn [Poly.prod_lin List.map].
      rewrite prodl_nil.
      cbn [Poly.eval].
      rewrite Z.mul_0_r, Z.add_0_r.
      apply Z.mod_1_l. exact (prime_range (p := p)).
    - cbn [Poly.prod_lin List.map].
      rewrite Poly.eval_pmul, Poly.eval_lin, prodl_cons, IH.
      reflexivity.
  Qed.

  (** Two monic linear-factor products agreeing pointwise up to nonzero
      scalars on one more point than their degree are equal, and the
      scalars coincide. *)
  Lemma prod_lin_scaled_agreement (wl vl xs : list Z) (c c0 : Z) :
    List.length wl = List.length vl ->
    Poly.NoDupP (p := p) xs ->
    List.length xs = S (List.length wl) ->
    c mod p = c -> c0 mod p = c0 -> c <> 0 ->
    (forall x, List.In x xs ->
      (c * Poly.eval (p := p) (Poly.prod_lin (p := p) wl) x) mod p =
      (c0 * Poly.eval (p := p) (Poly.prod_lin (p := p) vl) x) mod p) ->
    c = c0 /\
    Poly.peq (p := p)
      (Poly.prod_lin (p := p) wl) (Poly.prod_lin (p := p) vl).
  Proof.
    intros Hlen Hnd Hxs Hc_can Hc0_can Hc Hagree.
    set (F := Poly.pscale (p := p) c (Poly.prod_lin (p := p) wl)).
    set (G := Poly.pscale (p := p) c0 (Poly.prod_lin (p := p) vl)).
    assert (HFG : Poly.peq (p := p) F G).
    { apply (Poly.eval_ext (p := p) F G xs Hnd).
      - intros r Hr. unfold F, G. rewrite !Poly.eval_pscale.
        exact (Hagree r Hr).
      - unfold F.
        eapply Nat.le_trans; [apply Poly.pdeg_pscale_le |].
        rewrite (proj2 (Poly.prod_lin_monic (p := p) wl)), Hxs. lia.
      - unfold G.
        eapply Nat.le_trans; [apply Poly.pdeg_pscale_le |].
        rewrite (proj2 (Poly.prod_lin_monic (p := p) vl)), Hxs, Hlen.
        lia. }
    pose proof (fun i => proj1 (Poly.peq_iff_coef (p := p) F G) HFG i)
      as Hcoef.
    assert (Hw1 :
      Poly.coef (p := p) (Poly.prod_lin (p := p) wl) (List.length wl) = 1).
    { destruct (Poly.prod_lin_monic (p := p) wl) as [Hm Hd].
      pose proof (Poly.monic_top_coef (p := p) _ Hm) as Ht.
      rewrite Hd in Ht.
      replace (S (List.length wl) - 1)%nat with (List.length wl) in Ht
        by lia.
      exact Ht. }
    assert (Hv1 :
      Poly.coef (p := p) (Poly.prod_lin (p := p) vl) (List.length wl) = 1).
    { destruct (Poly.prod_lin_monic (p := p) vl) as [Hm Hd].
      pose proof (Poly.monic_top_coef (p := p) _ Hm) as Ht.
      rewrite Hd in Ht.
      replace (S (List.length vl) - 1)%nat with (List.length vl) in Ht
        by lia.
      rewrite Hlen. exact Ht. }
    assert (Htop : c = c0).
    { pose proof (Hcoef (List.length wl)) as Hc_top.
      unfold F, G in Hc_top. rewrite !Poly.coef_pscale in Hc_top.
      rewrite Hw1, Hv1, !Z.mul_1_r in Hc_top.
      rewrite Hc_can, Hc0_can in Hc_top.
      exact Hc_top. }
    split; [exact Htop |].
    apply (proj2 (Poly.peq_iff_coef (p := p) _ _)).
    intros i.
    pose proof (Hcoef i) as Hi.
    unfold F, G in Hi. rewrite !Poly.coef_pscale in Hi.
    rewrite <- Htop in Hi.
    rewrite <- (Poly.coef_canonical (p := p) (Poly.prod_lin (p := p) wl) i).
    rewrite <- (Poly.coef_canonical (p := p) (Poly.prod_lin (p := p) vl) i).
    apply (mulmod_cancel_l c); [| exact Hi].
    rewrite Hc_can. exact Hc.
  Qed.

  Lemma mul_mod_zero_r (x y : Z) : y mod p = 0 -> (x * y) mod p = 0.
  Proof. intros Hy. apply mul_mod_zero_iff. right. exact Hy. Qed.

  Lemma map_nth_seq_id {A : Set} (l : list A) (d : A) :
    List.map (fun j => List.nth j l d) (List.seq 0 (List.length l)) = l.
  Proof.
    induction l as [| a l IH]; [reflexivity |].
    cbn [List.length List.seq List.map].
    f_equal.
    rewrite <- List.seq_shift, List.map_map.
    exact IH.
  Qed.

  (** ** The five lookup rules on the cyclic domain

      The row-selector values of [Domain.l_0] / [Domain.l_last] /
      [Domain.l_blind] as field constants, and the active-row factor
      [1 − (l_last + l_blind)] of [lookup/verifier.rs]. *)

  Definition l0_z (domain : Domain.t) (row : Z) : Z :=
    if Domain.l_0 domain row then 1 else 0.

  Definition l_last_z (domain : Domain.t) (row : Z) : Z :=
    if Domain.l_last domain row then 1 else 0.

  Definition l_blind_z (domain : Domain.t) (row : Z) : Z :=
    if Domain.l_blind domain row then 1 else 0.

  Definition active_z (domain : Domain.t) (row : Z) : Z :=
    1 - (l_last_z domain row + l_blind_z domain row).

  Lemma l0_z_zero (domain : Domain.t) : l0_z domain 0 = 1.
  Proof. reflexivity. Qed.

  Lemma l0_z_other (domain : Domain.t) (row : Z) :
    row <> 0 -> l0_z domain row = 0.
  Proof.
    intros Hne. unfold l0_z, Domain.l_0.
    destruct (Z.eqb_spec row 0); [congruence | reflexivity].
  Qed.

  Lemma l_last_z_at (domain : Domain.t) :
    l_last_z domain (Domain.usable_rows domain) = 1.
  Proof.
    unfold l_last_z, Domain.l_last. rewrite Z.eqb_refl. reflexivity.
  Qed.

  Lemma l_last_z_other (domain : Domain.t) (row : Z) :
    row <> Domain.usable_rows domain -> l_last_z domain row = 0.
  Proof.
    intros Hne. unfold l_last_z, Domain.l_last.
    destruct (Z.eqb_spec row (Domain.usable_rows domain));
      [congruence | reflexivity].
  Qed.

  Lemma active_z_usable (domain : Domain.t) (row : Z) :
    0 <= row < Domain.usable_rows domain -> active_z domain row = 1.
  Proof.
    intros Hrow.
    unfold active_z, l_last_z, l_blind_z, Domain.l_last, Domain.l_blind.
    destruct (Z.eqb_spec row (Domain.usable_rows domain)) as [Heq | Hne];
      [lia |].
    destruct (Z.ltb_spec (Domain.usable_rows domain) row) as [Hlt | Hge];
      [lia | reflexivity].
  Qed.

  Lemma active_z_off (domain : Domain.t) (row : Z) :
    Domain.usable_rows domain <= row < Domain.n domain ->
    active_z domain row = 0.
  Proof.
    intros Hrow.
    unfold active_z, l_last_z, l_blind_z, Domain.l_last, Domain.l_blind.
    destruct (Z.eqb_spec row (Domain.usable_rows domain)) as [Heq | Hne].
    - destruct (Z.ltb_spec (Domain.usable_rows domain) row) as [Hlt | Hge];
        [lia | reflexivity].
    - destruct (Z.ltb_spec (Domain.usable_rows domain) row) as [Hlt | Hge];
        [| lia].
      destruct (Z.ltb_spec row (Domain.n domain)) as [Hlt2 | Hge2];
        [reflexivity | lia].
  Qed.

  (** ** The statement data

      One lookup argument is a list of pairs of value functions: the input
      expression value and the table column value, both per domain row. *)

  Definition input_tuple (pairs : list ((Z -> Z) * (Z -> Z))) (row : Z)
      : list Z :=
    List.map (fun fg => fst fg row) pairs.

  Definition table_tuple (pairs : list ((Z -> Z) * (Z -> Z))) (row : Z)
      : list Z :=
    List.map (fun fg => snd fg row) pairs.

  Definition comb_input (pairs : list ((Z -> Z) * (Z -> Z)))
      (theta row : Z) : Z :=
    comb theta (input_tuple pairs row).

  Definition comb_table (pairs : list ((Z -> Z) * (Z -> Z)))
      (theta row : Z) : Z :=
    comb theta (table_tuple pairs row).

  (** The five rules of [lookup/verifier.rs] [expressions()], read on the
      domain rows: the identity at [ω^row] evaluates the columns at [row],
      [Z(ωX)] at [Domain.rot domain row 1] and [A'(ω⁻¹X)] at
      [Domain.rot domain row (-1)]. *)
  Definition lookup_rules_hold (domain : Domain.t)
      (pairs : list ((Z -> Z) * (Z -> Z)))
      (theta beta gamma : Z) (A' S' Zp : Z -> Z) : Prop :=
    (* l_0 · (1 − Z) = 0 *)
    (forall row, 0 <= row < Domain.n domain ->
      (l0_z domain row * (1 - Zp row)) mod p = 0) /\
    (* l_last · (Z² − Z) = 0 *)
    (forall row, 0 <= row < Domain.n domain ->
      (l_last_z domain row * (Zp row * Zp row - Zp row)) mod p = 0) /\
    (* (1 − (l_last + l_blind)) ·
       (Z(ωX)·(A'+β)(S'+γ) − Z(X)·(A+β)(S+γ)) = 0 *)
    (forall row, 0 <= row < Domain.n domain ->
      (active_z domain row *
       (Zp (Domain.rot domain row 1) *
          ((A' row + beta) * (S' row + gamma)) -
        Zp row *
          ((comb_input pairs theta row + beta) *
           (comb_table pairs theta row + gamma)))) mod p = 0) /\
    (* l_0 · (A' − S') = 0 *)
    (forall row, 0 <= row < Domain.n domain ->
      (l0_z domain row * (A' row - S' row)) mod p = 0) /\
    (* (1 − (l_last + l_blind)) · (A' − S')·(A' − A'(ω⁻¹X)) = 0 *)
    (forall row, 0 <= row < Domain.n domain ->
      (active_z domain row *
       ((A' row - S' row) *
        (A' row - A' (Domain.rot domain row (-1))))) mod p = 0).

  (** Regular challenges: no compressed input or table factor of the
      product rule vanishes on a usable row.  The excluded [(β, γ)] set has
      at most [2 · usable_rows] residues per [θ]; on it the running-product
      recurrence divides by zero and even the honest witness has no product
      column. *)
  Definition lookup_challenge_regular (domain : Domain.t)
      (pairs : list ((Z -> Z) * (Z -> Z)))
      (theta beta gamma : Z) : Prop :=
    forall row, 0 <= row < Domain.usable_rows domain ->
      (comb_input pairs theta row + beta) mod p <> 0 /\
      (comb_table pairs theta row + gamma) mod p <> 0.

  (** The all-challenge acceptance package.  The permuted columns [A'],
      [S'] are committed after [θ] and before [β], [γ]; the product [Z]
      after [β], [γ] — the quantifier alternation mirrors the transcript
      order. *)
  Definition lookup_identities_hold (domain : Domain.t)
      (pairs : list ((Z -> Z) * (Z -> Z))) : Prop :=
    forall theta : Z, exists A' S' : Z -> Z,
      forall beta gamma : Z,
        lookup_challenge_regular domain pairs theta beta gamma ->
        exists Zp : Z -> Z,
          lookup_rules_hold domain pairs theta beta gamma A' S' Zp.

  (** The set-membership reading: every usable-row input tuple appears
      among the loaded table rows — the [eval_lookup_argument] shape. *)
  Definition lookup_membership (domain : Domain.t)
      (pairs : list ((Z -> Z) * (Z -> Z))) (table_rows : Z) : Prop :=
    forall row, 0 <= row < Domain.usable_rows domain ->
      exists table_row, 0 <= table_row < table_rows /\
        List.Forall (fun fg => fst fg row = snd fg table_row) pairs.

  (** Canonical values on the rows the equivalence reads. *)
  Definition pairs_canonical (domain : Domain.t)
      (pairs : list ((Z -> Z) * (Z -> Z))) : Prop :=
    List.Forall
      (fun fg =>
        forall row, 0 <= row < Domain.usable_rows domain ->
          (fst fg row) mod p = fst fg row /\
          (snd fg row) mod p = snd fg row)
      pairs.

  (** The tables-as-fixed-prefix coherence: every table row between the
      loaded prefix and the usable bound repeats a loaded-prefix row.  The
      polynomial rules read the table columns on all usable rows, the
      membership reading only on the loaded prefix; this is the condition
      that reconciles them. *)
  Definition table_prefix_coherent (domain : Domain.t)
      (pairs : list ((Z -> Z) * (Z -> Z))) (table_rows : Z) : Prop :=
    forall row, table_rows <= row < Domain.usable_rows domain ->
      exists table_row, 0 <= table_row < table_rows /\
        List.Forall (fun fg => snd fg row = snd fg table_row) pairs.

  (** The decidable form, for a concrete instance: one boolean scan over
      the padding rows. *)
  Definition table_prefix_coherent_b (domain : Domain.t)
      (pairs : list ((Z -> Z) * (Z -> Z))) (table_rows : Z) : bool :=
    List.forallb
      (fun row =>
        List.existsb
          (fun table_row =>
            List.forallb
              (fun fg =>
                snd fg (Z.of_nat row) =? snd fg (Z.of_nat table_row))
              pairs)
          (List.seq 0 (Z.to_nat table_rows)))
      (List.seq (Z.to_nat table_rows)
        (Z.to_nat (Domain.usable_rows domain) - Z.to_nat table_rows)).

  Lemma table_prefix_coherent_b_sound (domain : Domain.t)
      (pairs : list ((Z -> Z) * (Z -> Z))) (table_rows : Z) :
    0 <= table_rows ->
    table_prefix_coherent_b domain pairs table_rows = true ->
    table_prefix_coherent domain pairs table_rows.
  Proof.
    intros Htr Hb row Hrow.
    unfold table_prefix_coherent_b in Hb.
    rewrite List.forallb_forall in Hb.
    assert (Hin_row : List.In (Z.to_nat row)
      (List.seq (Z.to_nat table_rows)
        (Z.to_nat (Domain.usable_rows domain) - Z.to_nat table_rows))).
    { apply List.in_seq. lia. }
    specialize (Hb (Z.to_nat row) Hin_row).
    apply List.existsb_exists in Hb.
    destruct Hb as (table_row & Hin & Hall).
    apply List.in_seq in Hin.
    exists (Z.of_nat table_row).
    split; [lia |].
    rewrite List.forallb_forall in Hall.
    apply List.Forall_forall.
    intros fg Hfg.
    specialize (Hall fg Hfg).
    apply Z.eqb_eq in Hall.
    rewrite Z2Nat.id in Hall by lia.
    exact Hall.
  Qed.

  (** ** The permuted-column construction

      From a value column [al] whose every value occurs in the table
      column [sl]: the sorted copy of [al] and a permutation of [sl] that
      agrees with it at every run start — the witness pair for the [l_0]
      boot and the [(A' − S')·(A' − A'(ω⁻¹X))] rule. *)

  Lemma aligned_witness (al sl : list Z) :
    List.length sl = List.length al ->
    (forall v, List.In v al -> List.In v sl) ->
    exists A'l S'l : list Z,
      Permutation al A'l /\ Permutation sl S'l /\
      (forall j : nat, (j < List.length al)%nat ->
        List.nth j A'l 0 = List.nth j S'l 0 \/
        ((1 <= j)%nat /\ List.nth j A'l 0 = List.nth (j - 1) A'l 0)).
  Proof.
    intros Hlen Hincl.
    pose proof (zsort_perm al) as HpermA.
    pose proof (zsort_ascending al) as Hasc.
    destruct (zsort al) as [| v0 tl] eqn:HA.
    - (* the empty column *)
      apply Permutation_sym, Permutation_nil in HpermA.
      exists [], sl.
      split; [rewrite HpermA; apply Permutation_refl |].
      split; [apply Permutation_refl |].
      intros j Hj. rewrite HpermA in Hj. simpl in Hj. lia.
    - simpl in Hasc.
      set (needed := v0 :: dedup_from v0 tl).
      set (rest := remove_all needed sl).
      set (S'l := v0 :: build_s v0 tl rest).
      assert (Hnd_needed : List.NoDup needed).
      { unfold needed. constructor.
        - intros Hin. pose proof (dedup_from_lower tl v0 Hasc v0 Hin). lia.
        - exact (dedup_from_nodup tl v0 Hasc). }
      assert (Hin_needed : forall v, List.In v needed -> List.In v sl).
      { intros v Hv.
        apply Hincl.
        apply (Permutation_in _ (Permutation_sym HpermA)).
        destruct Hv as [-> | Hv]; [left; reflexivity |].
        right. exact (dedup_from_incl tl v0 v Hv). }
      pose proof (remove_all_perm needed sl Hnd_needed Hin_needed)
        as Hperm_rest.
      fold rest in Hperm_rest.
      assert (Hlen_al : List.length al = S (List.length tl)).
      { rewrite (Permutation_length HpermA). reflexivity. }
      assert (Hlen_rest : List.length rest = repeats_from v0 tl).
      { pose proof (Permutation_length Hperm_rest) as Hl1.
        rewrite List.length_app in Hl1.
        pose proof (dedup_repeats_length tl v0) as Hl2.
        assert (Hneed_len :
          List.length needed = S (List.length (dedup_from v0 tl)))
          by reflexivity.
        lia. }
      assert (Hperm_S : Permutation sl S'l).
      { eapply Permutation_trans; [exact Hperm_rest |].
        apply Permutation_sym.
        unfold S'l, needed.
        simpl List.app.
        apply perm_skip.
        exact (build_s_perm tl v0 rest Hlen_rest). }
      exists (v0 :: tl), S'l.
      split; [exact HpermA |].
      split; [exact Hperm_S |].
      intros j Hj.
      rewrite Hlen_al in Hj.
      destruct j as [| j'].
      + left. reflexivity.
      + assert (Hj' : (j' < List.length tl)%nat) by lia.
        destruct (build_s_align tl v0 rest j' Hj' Hlen_rest) as [Hl | Hr].
        * left. simpl. symmetry. exact Hl.
        * right. split; [lia |].
          simpl. rewrite Nat.sub_0_r.
          destruct j'; exact Hr.
  Qed.

  (** ** The running product *)

  Fixpoint zp_go (R L : nat -> Z) (k : nat) : Z :=
    match k with
    | O => 1
    | S k' => (zp_go R L k' * (R k' * mod_inverse (L k') p)) mod p
    end.

  Lemma zp_go_canonical (R L : nat -> Z) (k : nat) :
    zp_go R L k mod p = zp_go R L k.
  Proof.
    destruct k.
    - apply Z.mod_1_l. exact (prime_range (p := p)).
    - apply Zmod_mod.
  Qed.

  Lemma zp_go_step (R L : nat -> Z) (k : nat) :
    L k mod p <> 0 ->
    (zp_go R L (S k) * L k) mod p = (zp_go R L k * R k) mod p.
  Proof.
    intros HL.
    pose proof (mod_inverse_mul_prime (L k) HL) as Hi.
    change (BinOp.mul (mod_inverse (L k) p) (L k)) with
      ((mod_inverse (L k) p * L k) mod p) in Hi.
    cbn [zp_go].
    transitivity
      ((zp_go R L k * R k * (mod_inverse (L k) p * L k)) mod p);
      [mod_ring_solve |].
    rewrite Zmult_mod, Hi, Z.mul_1_r, Zmod_mod.
    reflexivity.
  Qed.

  Lemma zp_go_telescope (R L : nat -> Z) (k : nat) :
    (forall i, (i < k)%nat -> L i mod p <> 0) ->
    (zp_go R L k * prodl (List.map L (List.seq 0 k))) mod p =
    prodl (List.map R (List.seq 0 k)).
  Proof.
    induction k as [| k IH]; intros HL.
    - cbn [zp_go List.seq List.map]. rewrite prodl_nil.
      rewrite Z.mul_1_r. apply Z.mod_1_l. exact (prime_range (p := p)).
    - rewrite List.seq_S, Nat.add_0_l, !List.map_app, !prodl_app.
      cbn [List.map].
      rewrite !prodl_cons, !prodl_nil.
      transitivity
        (((zp_go R L (S k) * L k) mod p *
          prodl (List.map L (List.seq 0 k))) mod p);
        [mod_ring_solve |].
      rewrite (zp_go_step R L k (HL k (Nat.lt_succ_diag_r k))).
      transitivity
        ((R k * ((zp_go R L k *
          prodl (List.map L (List.seq 0 k))) mod p)) mod p);
        [mod_ring_solve |].
      rewrite IH by (intros i Hi; apply HL; lia).
      mod_ring_solve.
  Qed.

  Lemma zp_go_one (R L : nat -> Z) (k : nat) :
    (forall i, (i < k)%nat -> L i mod p <> 0) ->
    prodl (List.map L (List.seq 0 k)) = prodl (List.map R (List.seq 0 k)) ->
    zp_go R L k = 1.
  Proof.
    intros HL Heq.
    pose proof (zp_go_telescope R L k HL) as Htel.
    rewrite <- Heq in Htel.
    assert (HP : prodl (List.map L (List.seq 0 k)) mod p <> 0).
    { rewrite prodl_canonical. apply prodl_nonzero. intros v Hv.
      apply List.in_map_iff in Hv. destruct Hv as (i & <- & Hi).
      apply List.in_seq in Hi. apply HL. lia. }
    assert (Hz : zp_go R L k mod p = 1 mod p).
    { apply (mulmod_cancel_l (prodl (List.map L (List.seq 0 k))));
        [exact HP |].
      rewrite Z.mul_1_r.
      rewrite (Z.mul_comm (prodl (List.map L (List.seq 0 k)))
        (zp_go R L k)).
      rewrite Htel. symmetry. apply prodl_canonical. }
    rewrite zp_go_canonical in Hz.
    rewrite Z.mod_1_l in Hz; [exact Hz | exact (prime_range (p := p))].
  Qed.

  (** ** Completeness: membership yields the five rules *)

  Theorem lookup_complete (domain : Domain.t)
      (pairs : list ((Z -> Z) * (Z -> Z))) (table_rows : Z)
      (Hbf : 0 <= domain.(Domain.blinding_factors))
      (Hu : 0 <= Domain.usable_rows domain)
      (Htr : table_rows <= Domain.usable_rows domain)
      (Hmem : lookup_membership domain pairs table_rows) :
    lookup_identities_hold domain pairs.
  Proof.
    set (u := Domain.usable_rows domain) in *.
    set (un := Z.to_nat u).
    assert (Hun : Z.of_nat un = u) by (apply Z2Nat.id; exact Hu).
    assert (Hu_lt_n : u < Domain.n domain)
      by (unfold u, Domain.usable_rows; lia).
    intros theta.
    set (al :=
      List.map (fun j => comb_input pairs theta (Z.of_nat j))
        (List.seq 0 un)).
    set (sl :=
      List.map (fun j => comb_table pairs theta (Z.of_nat j))
        (List.seq 0 un)).
    assert (Hlen_al : List.length al = un)
      by (unfold al; rewrite List.length_map, List.length_seq; reflexivity).
    assert (Hlen_sl : List.length sl = List.length al)
      by (unfold sl; rewrite List.length_map, List.length_seq, Hlen_al;
          reflexivity).
    assert (Hrow_of_index : forall i, (i < un)%nat -> 0 <= Z.of_nat i < u).
    { intros i Hi. split; [lia |].
      rewrite <- Hun. apply Nat2Z.inj_lt. exact Hi. }
    assert (Hincl : forall v, List.In v al -> List.In v sl).
    { intros v Hv.
      unfold al in Hv. apply List.in_map_iff in Hv.
      destruct Hv as (j & <- & Hj). apply List.in_seq in Hj.
      assert (Hrow : 0 <= Z.of_nat j < u)
        by (apply Hrow_of_index; lia).
      destruct (Hmem (Z.of_nat j) Hrow) as (trow & Htrow & Hall).
      assert (Htuple :
        input_tuple pairs (Z.of_nat j) = table_tuple pairs trow).
      { unfold input_tuple, table_tuple. apply List.map_ext_in.
        intros fg Hfg. rewrite List.Forall_forall in Hall.
        exact (Hall fg Hfg). }
      unfold comb_input. rewrite Htuple.
      unfold sl.
      apply List.in_map_iff.
      exists (Z.to_nat trow).
      split.
      - unfold comb_table. rewrite Z2Nat.id by lia. reflexivity.
      - apply List.in_seq. unfold un. lia. }
    destruct (aligned_witness al sl Hlen_sl Hincl)
      as (A'l & S'l & HpermA & HpermS & Halign).
    assert (HlenA : List.length A'l = un)
      by (rewrite <- (Permutation_length HpermA); exact Hlen_al).
    assert (HlenS : List.length S'l = un)
      by (rewrite <- (Permutation_length HpermS),
            Hlen_sl; exact Hlen_al).
    exists (fun row => List.nth (Z.to_nat row) A'l 0).
    exists (fun row => List.nth (Z.to_nat row) S'l 0).
    intros beta gamma Hreg.
    (* value origin of the permuted columns *)
    assert (HA_in : forall j, (j < un)%nat -> exists i, (i < un)%nat /\
      List.nth j A'l 0 = comb_input pairs theta (Z.of_nat i)).
    { intros j Hj.
      assert (Hin : List.In (List.nth j A'l 0) al).
      { apply (Permutation_in _ (Permutation_sym HpermA)).
        apply List.nth_In. lia. }
      unfold al in Hin. apply List.in_map_iff in Hin.
      destruct Hin as (i & Heqv & Hi). apply List.in_seq in Hi.
      exists i. split; [lia | symmetry; exact Heqv]. }
    assert (HS_in : forall j, (j < un)%nat -> exists i, (i < un)%nat /\
      List.nth j S'l 0 = comb_table pairs theta (Z.of_nat i)).
    { intros j Hj.
      assert (Hin : List.In (List.nth j S'l 0) sl).
      { apply (Permutation_in _ (Permutation_sym HpermS)).
        apply List.nth_In. lia. }
      unfold sl in Hin. apply List.in_map_iff in Hin.
      destruct Hin as (i & Heqv & Hi). apply List.in_seq in Hi.
      exists i. split; [lia | symmetry; exact Heqv]. }
    (* the factor sequences *)
    set (Lf := fun j : nat =>
      ((List.nth j A'l 0 + beta) * (List.nth j S'l 0 + gamma)) mod p).
    set (Rf := fun i : nat =>
      ((comb_input pairs theta (Z.of_nat i) + beta) *
       (comb_table pairs theta (Z.of_nat i) + gamma)) mod p).
    assert (HLf_nz : forall j, (j < un)%nat -> Lf j mod p <> 0).
    { intros j Hj. unfold Lf. rewrite Zmod_mod.
      intros Hc. apply mul_mod_zero_iff in Hc.
      destruct Hc as [Hc | Hc].
      - destruct (HA_in j Hj) as (i & Hi & Heqv).
        rewrite Heqv in Hc.
        exact (proj1 (Hreg (Z.of_nat i) (Hrow_of_index i Hi)) Hc).
      - destruct (HS_in j Hj) as (i & Hi & Heqv).
        rewrite Heqv in Hc.
        exact (proj2 (Hreg (Z.of_nat i) (Hrow_of_index i Hi)) Hc). }
    (* the product identity via the permutations *)
    assert (Hprod_eq :
      prodl (List.map Lf (List.seq 0 un)) =
      prodl (List.map Rf (List.seq 0 un))).
    { unfold Lf, Rf.
      rewrite (prodl_split
        (fun j => ((List.nth j A'l 0 + beta) *
                   (List.nth j S'l 0 + gamma)) mod p)
        (fun j => List.nth j A'l 0 + beta)
        (fun j => List.nth j S'l 0 + gamma)
        (List.seq 0 un)) by (intros; reflexivity).
      rewrite (prodl_split
        (fun i => ((comb_input pairs theta (Z.of_nat i) + beta) *
                   (comb_table pairs theta (Z.of_nat i) + gamma)) mod p)
        (fun i => comb_input pairs theta (Z.of_nat i) + beta)
        (fun i => comb_table pairs theta (Z.of_nat i) + gamma)
        (List.seq 0 un)) by (intros; reflexivity).
      assert (HAside :
        prodl (List.map (fun j => List.nth j A'l 0 + beta)
          (List.seq 0 un)) =
        prodl (List.map
          (fun i => comb_input pairs theta (Z.of_nat i) + beta)
          (List.seq 0 un))).
      { rewrite <- (List.map_map (fun j => List.nth j A'l 0)
          (fun v => v + beta)).
        rewrite <- HlenA, map_nth_seq_id, HlenA.
        rewrite <- (List.map_map
          (fun i => comb_input pairs theta (Z.of_nat i))
          (fun v => v + beta)).
        apply prodl_perm.
        apply Permutation_map.
        apply Permutation_sym.
        exact HpermA. }
      assert (HSside :
        prodl (List.map (fun j => List.nth j S'l 0 + gamma)
          (List.seq 0 un)) =
        prodl (List.map
          (fun i => comb_table pairs theta (Z.of_nat i) + gamma)
          (List.seq 0 un))).
      { rewrite <- (List.map_map (fun j => List.nth j S'l 0)
          (fun v => v + gamma)).
        rewrite <- HlenS, map_nth_seq_id, HlenS.
        rewrite <- (List.map_map
          (fun i => comb_table pairs theta (Z.of_nat i))
          (fun v => v + gamma)).
        apply prodl_perm.
        apply Permutation_map.
        apply Permutation_sym.
        exact HpermS. }
      rewrite HAside, HSside. reflexivity. }
    (* boot equality of the two permuted heads *)
    assert (H0eq : List.nth 0 A'l 0 = List.nth 0 S'l 0).
    { destruct (Nat.ltb_spec 0 un) as [Hpos | Hzero].
      - destruct (Halign 0%nat ltac:(lia)) as [He | [Habs _]];
          [exact He | lia].
      - assert (HAnil : A'l = [])
          by (destruct A'l; [reflexivity | cbn in HlenA; lia]).
        assert (HSnil : S'l = [])
          by (destruct S'l; [reflexivity | cbn in HlenS; lia]).
        rewrite HAnil, HSnil. reflexivity. }
    exists (fun row => zp_go Rf Lf (Z.to_nat row)).
    cbv beta.
    assert (Hz_last : zp_go Rf Lf un = 1)
      by (exact (zp_go_one Rf Lf un HLf_nz Hprod_eq)).
    split; [| split; [| split; [| split]]].
    - (* l_0 · (1 − Z) *)
      intros row Hrow.
      destruct (Z.eqb_spec row 0) as [-> | Hne].
      + rewrite l0_z_zero.
        change (Z.to_nat 0) with O.
        cbn [zp_go].
        rewrite Z.sub_diag, Z.mul_0_r. apply Zmod_0_l.
      + rewrite (l0_z_other domain row Hne).
        rewrite Z.mul_0_l. apply Zmod_0_l.
    - (* l_last · (Z² − Z) *)
      intros row Hrow.
      destruct (Z.eqb_spec row u) as [-> | Hne].
      + fold u. rewrite l_last_z_at.
        fold un. rewrite Hz_last.
        replace (1 * (1 * 1 - 1)) with 0 by ring.
        apply Zmod_0_l.
      + rewrite (l_last_z_other domain row Hne).
        rewrite Z.mul_0_l. apply Zmod_0_l.
    - (* the product rule *)
      intros row Hrow.
      destruct (Z.ltb_spec row u) as [Hlt | Hge].
      + rewrite (active_z_usable domain row (conj (proj1 Hrow) Hlt)).
        rewrite Z.mul_1_l.
        apply (proj2 (sub_mod_zero_iff _ _)).
        assert (Hrot : Domain.rot domain row 1 = row + 1).
        { unfold Domain.rot. apply Z.mod_small. lia. }
        rewrite Hrot.
        set (k := Z.to_nat row).
        assert (Hk : (k < un)%nat) by (unfold k, un; lia).
        assert (Hrowk : row = Z.of_nat k) by (unfold k; lia).
        rewrite Hrowk.
        replace (Z.of_nat k + 1) with (Z.of_nat (S k)) by lia.
        rewrite !Nat2Z.id.
        transitivity ((zp_go Rf Lf (S k) * Lf k) mod p).
        { unfold Lf. rewrite Zmult_mod_idemp_r. reflexivity. }
        rewrite (zp_go_step Rf Lf k (HLf_nz k Hk)).
        unfold Rf. rewrite Zmult_mod_idemp_r. reflexivity.
      + rewrite (active_z_off domain row (conj Hge (proj2 Hrow))).
        rewrite Z.mul_0_l. apply Zmod_0_l.
    - (* l_0 · (A' − S') *)
      intros row Hrow.
      destruct (Z.eqb_spec row 0) as [-> | Hne].
      + rewrite l0_z_zero.
        change (Z.to_nat 0) with O.
        rewrite H0eq, Z.sub_diag, Z.mul_1_l. apply Zmod_0_l.
      + rewrite (l0_z_other domain row Hne).
        rewrite Z.mul_0_l. apply Zmod_0_l.
    - (* (A' − S')·(A' − A'(ω⁻¹X)) *)
      intros row Hrow.
      destruct (Z.ltb_spec row u) as [Hlt | Hge].
      + rewrite (active_z_usable domain row (conj (proj1 Hrow) Hlt)).
        rewrite Z.mul_1_l.
        set (k := Z.to_nat row).
        assert (Hk : (k < un)%nat) by (unfold k, un; lia).
        destruct k as [| k'] eqn:Hkcase.
        * (* row 0: the boot equality *)
          assert (Hrow0 : row = 0) by (unfold k in Hkcase; lia).
          rewrite Hrow0.
          change (Z.to_nat 0) with O.
          apply mul_mod_zero_l.
          rewrite H0eq, Z.sub_diag. apply Zmod_0_l.
        * (* the chain step *)
          rewrite <- Hlen_al in Hk.
          destruct (Halign k ltac:(lia)) as [He | [Hge1 Hchain]];
            rewrite <- Hkcase in *.
          -- apply mul_mod_zero_l.
             rewrite He, Z.sub_diag. apply Zmod_0_l.
          -- apply mul_mod_zero_r.
             assert (Hrot : Domain.rot domain row (-1) = row - 1).
             { unfold Domain.rot. apply Z.mod_small.
               unfold k in Hkcase. lia. }
             rewrite Hrot.
             replace (Z.to_nat (row - 1)) with (k - 1)%nat
               by (unfold k; lia).
             fold k.
             rewrite Hchain, Z.sub_diag. apply Zmod_0_l.
      + rewrite (active_z_off domain row (conj Hge (proj2 Hrow))).
        rewrite Z.mul_0_l. apply Zmod_0_l.
  Qed.

  (** ** Soundness infrastructure *)

  Lemma mul_mod_nonzero (x y : Z) :
    x mod p <> 0 -> y mod p <> 0 -> (x * y) mod p <> 0.
  Proof.
    intros Hx Hy Hc. apply mul_mod_zero_iff in Hc. tauto.
  Qed.

  Lemma opp_mod_opp (a : Z) : (- ((- a) mod p)) mod p = a mod p.
  Proof.
    rewrite <- (Z.sub_0_l ((- a) mod p)), Zminus_mod_idemp_r.
    f_equal. ring.
  Qed.

  Lemma opp_mod_congr (a b : Z) :
    a mod p = b mod p -> (- a) mod p = (- b) mod p.
  Proof.
    intros Hab.
    rewrite <- (Z.sub_0_l a), <- (Z.sub_0_l b).
    rewrite Zminus_mod, Hab, <- Zminus_mod.
    reflexivity.
  Qed.

  Lemma eval_prod_lin_zero_inv (l : list Z) (x : Z) :
    Poly.eval (p := p) (Poly.prod_lin (p := p) l) x = 0 ->
    exists r, List.In r l /\ (x - r) mod p = 0.
  Proof.
    intros Hz.
    destruct (List.existsb (fun r => (x - r) mod p =? 0) l) eqn:Hex.
    - apply List.existsb_exists in Hex.
      destruct Hex as (r & Hr & Heq). apply Z.eqb_eq in Heq.
      exists r. exact (conj Hr Heq).
    - exfalso.
      refine (Poly.eval_prod_lin_nonzero (p := p) l x _ Hz).
      intros r Hr Heq.
      assert (Hex' : List.existsb (fun r' => (x - r') mod p =? 0) l = true).
      { apply List.existsb_exists. exists r.
        split; [exact Hr | apply Z.eqb_eq; exact Heq]. }
      congruence.
  Qed.

  Lemma pdeg_le_length (f : Poly.t) :
    (Poly.pdeg (p := p) f <= List.length f)%nat.
  Proof.
    induction f as [| c f IH]; [cbn; lia |].
    unfold Poly.pdeg in *. cbn [Poly.norm].
    destruct (Poly.norm (p := p) f) as [| z g] eqn:E.
    - destruct (c mod p =? 0); cbn [List.length] in *; lia.
    - cbn [List.length] in *. lia.
  Qed.

  (** The shifted product [∏ (v_j + x)] as the linear-factor polynomial
      over the negated values, evaluated at [x]. *)
  Lemma prodl_shift_eval (vf : nat -> Z) (un : nat) (x : Z) :
    prodl (List.map (fun j => vf j + x) (List.seq 0 un)) =
    Poly.eval (p := p) (Poly.prod_lin (p := p)
      (List.map (fun j => (- vf j) mod p) (List.seq 0 un))) x.
  Proof.
    rewrite eval_prod_lin_prodl, List.map_map.
    apply prodl_map_congr.
    intros j Hj. mod_ring_solve.
  Qed.

  (** Telescoping the product rule: the running product against the
      partial factor products, from the boot value. *)
  Lemma zp_telescope (Zp : Z -> Z) (Lf Rf : nat -> Z) (un : nat)
      (Hboot : Zp 0 mod p = 1)
      (Hstep : forall k, (k < un)%nat ->
        (Zp (Z.of_nat (S k)) * Lf k) mod p =
        (Zp (Z.of_nat k) * Rf k) mod p) :
    forall k, (k <= un)%nat ->
    (Zp (Z.of_nat k) * prodl (List.map Lf (List.seq 0 k))) mod p =
    prodl (List.map Rf (List.seq 0 k)).
  Proof.
    induction k as [| k IH]; intros Hk.
    - cbn [List.seq List.map]. rewrite prodl_nil, Z.mul_1_r.
      change (Z.of_nat 0) with 0. exact Hboot.
    - rewrite List.seq_S, Nat.add_0_l, !List.map_app, !prodl_app.
      cbn [List.map].
      rewrite !prodl_cons, !prodl_nil.
      assert (Hk' : (k < un)%nat) by lia.
      assert (Hk'' : (k <= un)%nat) by lia.
      transitivity
        (((Zp (Z.of_nat (S k)) * Lf k) mod p *
          prodl (List.map Lf (List.seq 0 k))) mod p); [mod_ring_solve |].
      rewrite (Hstep k Hk').
      transitivity
        ((Rf k * ((Zp (Z.of_nat k) *
          prodl (List.map Lf (List.seq 0 k))) mod p)) mod p);
        [mod_ring_solve |].
      rewrite (IH Hk'').
      mod_ring_solve.
  Qed.

  (** With every right factor nonzero, the running product and every left
      factor are nonzero — the boolean [l_last] escape is closed. *)
  Lemma zp_nonzero_chain (Zp : Z -> Z) (Lf Rf : nat -> Z) (un : nat)
      (Hboot : Zp 0 mod p = 1)
      (Hstep : forall k, (k < un)%nat ->
        (Zp (Z.of_nat (S k)) * Lf k) mod p =
        (Zp (Z.of_nat k) * Rf k) mod p)
      (HR : forall k, (k < un)%nat -> Rf k mod p <> 0) :
    (forall k, (k <= un)%nat -> Zp (Z.of_nat k) mod p <> 0) /\
    (forall k, (k < un)%nat -> Lf k mod p <> 0).
  Proof.
    assert (HZ : forall k, (k <= un)%nat -> Zp (Z.of_nat k) mod p <> 0).
    { intros k. induction k as [| k IH]; intros Hk.
      - change (Z.of_nat 0) with 0. rewrite Hboot. lia.
      - assert (Hk' : (k < un)%nat) by lia.
        assert (Hk'' : (k <= un)%nat) by lia.
        intros Hc.
        assert (H0 : (Zp (Z.of_nat k) * Rf k) mod p = 0)
          by (rewrite <- (Hstep k Hk'); apply mul_mod_zero_l; exact Hc).
        apply mul_mod_zero_iff in H0.
        destruct H0 as [H0 | H0].
        + exact (IH Hk'' H0).
        + exact (HR k Hk' H0). }
    split; [exact HZ |].
    intros k Hk Hc.
    assert (Hk'' : (k <= un)%nat) by lia.
    assert (H0 : (Zp (Z.of_nat k) * Rf k) mod p = 0)
      by (rewrite <- (Hstep k Hk); apply mul_mod_zero_r; exact Hc).
    apply mul_mod_zero_iff in H0.
    destruct H0 as [H0 | H0].
    - exact (HZ k Hk'' H0).
    - exact (HR k Hk H0).
  Qed.

  (** The permuted-column chain: rules 4 and 5 force every [A'] value on a
      usable row to equal an [S'] value at or before it. *)
  Lemma permuted_chain (domain : Domain.t)
      (pairs : list ((Z -> Z) * (Z -> Z)))
      (theta beta gamma : Z) (A' S' Zp : Z -> Z)
      (Hbf : 0 <= domain.(Domain.blinding_factors))
      (Hu : 0 <= Domain.usable_rows domain)
      (Hrules : lookup_rules_hold domain pairs theta beta gamma A' S' Zp) :
    forall j : nat, Z.of_nat j < Domain.usable_rows domain ->
    exists j', (j' <= j)%nat /\
      A' (Z.of_nat j) mod p = S' (Z.of_nat j') mod p.
  Proof.
    destruct Hrules as (_ & _ & _ & H4 & H5).
    assert (Hnn : Domain.usable_rows domain < Domain.n domain)
      by (unfold Domain.usable_rows; lia).
    intros j. induction j as [| j IH]; intros Hj.
    - exists 0%nat. split; [lia |].
      assert (Hr0 : 0 <= 0 < Domain.n domain) by lia.
      specialize (H4 0 Hr0).
      rewrite l0_z_zero, Z.mul_1_l in H4.
      apply sub_mod_zero_iff in H4.
      exact H4.
    - assert (Hrn : 0 <= Z.of_nat (S j) < Domain.n domain) by lia.
      assert (Hru : 0 <= Z.of_nat (S j) < Domain.usable_rows domain)
        by lia.
      specialize (H5 (Z.of_nat (S j)) Hrn).
      rewrite (active_z_usable domain _ Hru), Z.mul_1_l in H5.
      apply mul_mod_zero_iff in H5.
      destruct H5 as [Hl | Hr].
      + exists (S j). split; [lia |].
        apply sub_mod_zero_iff in Hl. exact Hl.
      + assert (Hrot : Domain.rot domain (Z.of_nat (S j)) (-1) = Z.of_nat j).
        { unfold Domain.rot.
          replace (Z.of_nat (S j) + -1) with (Z.of_nat j) by lia.
          apply Z.mod_small. lia. }
        rewrite Hrot in Hr.
        apply sub_mod_zero_iff in Hr.
        assert (Hj' : Z.of_nat j < Domain.usable_rows domain) by lia.
        destruct (IH Hj') as (j' & Hle & Heq).
        exists j'. split; [lia |].
        rewrite Hr. exact Heq.
  Qed.

  (** The packaged per-challenge consequences of the five rules at a
      regular challenge: the total factor-product identity, and every left
      factor nonzero. *)
  Lemma lookup_rules_consequences (domain : Domain.t)
      (pairs : list ((Z -> Z) * (Z -> Z)))
      (theta beta gamma : Z) (A' S' Zp : Z -> Z)
      (Hbf : 0 <= domain.(Domain.blinding_factors))
      (Hu : 0 <= Domain.usable_rows domain)
      (Hreg : lookup_challenge_regular domain pairs theta beta gamma)
      (Hrules : lookup_rules_hold domain pairs theta beta gamma A' S' Zp) :
    prodl (List.map (fun k =>
        ((A' (Z.of_nat k) + beta) * (S' (Z.of_nat k) + gamma)) mod p)
      (List.seq 0 (Z.to_nat (Domain.usable_rows domain)))) =
    prodl (List.map (fun k =>
        ((comb_input pairs theta (Z.of_nat k) + beta) *
         (comb_table pairs theta (Z.of_nat k) + gamma)) mod p)
      (List.seq 0 (Z.to_nat (Domain.usable_rows domain)))) /\
    (forall k, (k < Z.to_nat (Domain.usable_rows domain))%nat ->
      (A' (Z.of_nat k) + beta) mod p <> 0 /\
      (S' (Z.of_nat k) + gamma) mod p <> 0).
  Proof.
    set (u := Domain.usable_rows domain) in *.
    set (un := Z.to_nat u) in *.
    assert (Hun : Z.of_nat un = u) by (exact (Z2Nat.id u Hu)).
    assert (Hult : u < Domain.n domain)
      by (unfold u, Domain.usable_rows; lia).
    assert (Hnpos : 0 < Domain.n domain) by lia.
    destruct Hrules as (H1 & H2 & H3 & H4 & H5).
    set (Lf := fun k : nat =>
      ((A' (Z.of_nat k) + beta) * (S' (Z.of_nat k) + gamma)) mod p).
    set (Rf := fun k : nat =>
      ((comb_input pairs theta (Z.of_nat k) + beta) *
       (comb_table pairs theta (Z.of_nat k) + gamma)) mod p).
    assert (Hrow_of : forall k, (k < un)%nat -> 0 <= Z.of_nat k < u)
      by (intros k Hk; unfold un in Hk; lia).
    assert (Hboot : Zp 0 mod p = 1).
    { assert (Hr0 : 0 <= 0 < Domain.n domain) by lia.
      specialize (H1 0 Hr0).
      rewrite l0_z_zero, Z.mul_1_l in H1.
      apply sub_mod_zero_iff in H1.
      rewrite Z.mod_1_l in H1 by (exact (prime_range (p := p))).
      symmetry. exact H1. }
    assert (Hstep : forall k, (k < un)%nat ->
      (Zp (Z.of_nat (S k)) * Lf k) mod p =
      (Zp (Z.of_nat k) * Rf k) mod p).
    { intros k Hk.
      pose proof (Hrow_of k Hk) as Hrk.
      assert (Hrn : 0 <= Z.of_nat k < Domain.n domain) by lia.
      specialize (H3 (Z.of_nat k) Hrn).
      rewrite (active_z_usable domain _ Hrk), Z.mul_1_l in H3.
      apply sub_mod_zero_iff in H3.
      assert (Hrot : Domain.rot domain (Z.of_nat k) 1 = Z.of_nat (S k)).
      { unfold Domain.rot.
        replace (Z.of_nat k + 1) with (Z.of_nat (S k)) by lia.
        apply Z.mod_small. lia. }
      rewrite Hrot in H3.
      unfold Lf, Rf.
      rewrite !Zmult_mod_idemp_r.
      exact H3. }
    assert (HRnz : forall k, (k < un)%nat -> Rf k mod p <> 0).
    { intros k Hk. unfold Rf. rewrite Zmod_mod.
      destruct (Hreg (Z.of_nat k) (Hrow_of k Hk)) as [Hi Ht].
      exact (mul_mod_nonzero _ _ Hi Ht). }
    pose proof (zp_nonzero_chain Zp Lf Rf un Hboot Hstep HRnz)
      as [HZnz HLnz].
    assert (Hlast : Zp u mod p = 1).
    { assert (Hrn : 0 <= u < Domain.n domain) by lia.
      specialize (H2 u Hrn).
      assert (Hll : l_last_z domain u = 1) by (exact (l_last_z_at domain)).
      rewrite Hll, Z.mul_1_l in H2.
      replace (Zp u * Zp u - Zp u) with (Zp u * (Zp u - 1)) in H2 by ring.
      apply mul_mod_zero_iff in H2.
      destruct H2 as [Hz | Hone].
      - exfalso.
        assert (Hle : (un <= un)%nat) by lia.
        pose proof (HZnz un Hle) as Hnz.
        rewrite Hun in Hnz.
        exact (Hnz Hz).
      - apply sub_mod_zero_iff in Hone.
        rewrite Z.mod_1_l in Hone by (exact (prime_range (p := p))).
        exact Hone. }
    split.
    - pose proof (zp_telescope Zp Lf Rf un Hboot Hstep un (Nat.le_refl un))
        as Htel.
      transitivity
        ((Zp (Z.of_nat un) * prodl (List.map Lf (List.seq 0 un))) mod p).
      + symmetry.
        rewrite Zmult_mod, Hun, Hlast, Z.mul_1_l, Zmod_mod.
        apply prodl_canonical.
      + exact Htel.
    - intros k Hk.
      pose proof (HLnz k Hk) as Hnz.
      unfold Lf in Hnz. rewrite Zmod_mod in Hnz.
      split.
      + intros Hc. apply Hnz. apply mul_mod_zero_l. exact Hc.
      + intros Hc. apply Hnz. apply mul_mod_zero_r. exact Hc.
  Qed.

  (** ** The per-θ multiset step, from bounded challenge pools

      The pool-indexed form of [per_theta_membership]: with the permuted
      columns [A'], [S'] fixed, an accepting [(β, γ)] grid drawn from two
      pools of [2·u + 1] residues that are pairwise distinct mod [p]
      already identifies the factor polynomials and carries every combined
      input value into the combined table values.  Only the pool sizes
      matter, so the counting layer can supply explicit finite pools while
      [per_theta_membership] instantiates both with [0 .. 2·u]. *)
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
    { apply Poly.pool_avoid_pick; [exact Hng |].
      rewrite HNs_len. lia. }
    destruct Hg0pick as (gamma0 & Hg0_in & Hg0).
    (* the β point family, drawn from the β pool *)
    destruct (Poly.pool_avoid_sublist Na betas (S un) Hnb
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
      destruct (lookup_rules_consequences
        domain pairs theta x gamma0 A' S' Zp Hbf Hu
        (Hreg_mk x gamma0 (fun r Hr => Hxs_avoid x r Hx Hr) Hg0)
        Hrules) as [Hprod _].
      fold u in Hprod. fold un in Hprod.
      rewrite (prodl_split
        (fun k => ((A' (Z.of_nat k) + x) *
                   (S' (Z.of_nat k) + gamma0)) mod p)
        (fun k => A' (Z.of_nat k) + x)
        (fun k => S' (Z.of_nat k) + gamma0)
        (List.seq 0 un)) in Hprod by (intros; reflexivity).
      rewrite (prodl_split
        (fun k => ((comb_input pairs theta (Z.of_nat k) + x) *
                   (comb_table pairs theta (Z.of_nat k) + gamma0)) mod p)
        (fun k => comb_input pairs theta (Z.of_nat k) + x)
        (fun k => comb_table pairs theta (Z.of_nat k) + gamma0)
        (List.seq 0 un)) in Hprod by (intros; reflexivity).
      assert (HevA' :
        prodl (List.map (fun k => A' (Z.of_nat k) + x) (List.seq 0 un)) =
        Poly.eval (p := p) (Poly.prod_lin (p := p) NA') x)
        by (exact (prodl_shift_eval
          (fun k => A' (Z.of_nat k)) un x)).
      assert (HevA :
        prodl (List.map
          (fun k => comb_input pairs theta (Z.of_nat k) + x)
          (List.seq 0 un)) =
        Poly.eval (p := p) (Poly.prod_lin (p := p) Na) x)
        by (exact (prodl_shift_eval
          (fun k => comb_input pairs theta (Z.of_nat k)) un x)).
      rewrite HevA', HevA in Hprod.
      fold cS' in Hprod. fold cs in Hprod.
      rewrite (Z.mul_comm cS'), (Z.mul_comm cs).
      exact Hprod. }
    (* the x0-instance factor facts *)
    destruct (Hper_x x0 Hx0_in) as (Zp0 & Hrules0).
    destruct (lookup_rules_consequences
      domain pairs theta x0 gamma0 A' S' Zp0 Hbf Hu
      (Hreg_mk x0 gamma0 (fun r Hr => Hxs_avoid x0 r Hx0_in Hr) Hg0)
      Hrules0) as [_ Hfac].
    assert (HcS'_nz : cS' <> 0).
    { unfold cS'. apply prodl_nonzero.
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
    destruct (prod_lin_scaled_agreement
      NA' Na xs cS' cs Hwl_len Hxs_ndp Hxs_len'
      (prodl_canonical _)
      (prodl_canonical _) HcS'_nz
      Hpointwise) as [_ HpeqA].
    (* the γ point family, at the designated regular β = x0 *)
    destruct (Poly.pool_avoid_sublist Ns gammas (S un) Hng
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
      destruct (lookup_rules_consequences
        domain pairs theta x0 g0 A' S' Zpg Hbf Hu Hreg_g Hrulesg)
        as [Hprod _].
      fold u in Hprod. fold un in Hprod.
      rewrite (prodl_split
        (fun k => ((A' (Z.of_nat k) + x0) *
                   (S' (Z.of_nat k) + g0)) mod p)
        (fun k => A' (Z.of_nat k) + x0)
        (fun k => S' (Z.of_nat k) + g0)
        (List.seq 0 un)) in Hprod by (intros; reflexivity).
      rewrite (prodl_split
        (fun k => ((comb_input pairs theta (Z.of_nat k) + x0) *
                   (comb_table pairs theta (Z.of_nat k) + g0)) mod p)
        (fun k => comb_input pairs theta (Z.of_nat k) + x0)
        (fun k => comb_table pairs theta (Z.of_nat k) + g0)
        (List.seq 0 un)) in Hprod by (intros; reflexivity).
      assert (HevS' :
        prodl (List.map (fun k => S' (Z.of_nat k) + g0) (List.seq 0 un)) =
        Poly.eval (p := p) (Poly.prod_lin (p := p) NS') g0)
        by (exact (prodl_shift_eval
          (fun k => S' (Z.of_nat k)) un g0)).
      assert (HevS :
        prodl (List.map
          (fun k => comb_table pairs theta (Z.of_nat k) + g0)
          (List.seq 0 un)) =
        Poly.eval (p := p) (Poly.prod_lin (p := p) Ns) g0)
        by (exact (prodl_shift_eval
          (fun k => comb_table pairs theta (Z.of_nat k)) un g0)).
      rewrite HevS', HevS in Hprod.
      fold dA' in Hprod. fold da in Hprod.
      transitivity ((prodl (List.map (fun j => A' (Z.of_nat j) + x0)
          (List.seq 0 un)) *
        Poly.eval (p := p) (Poly.prod_lin (p := p) NS') g0) mod p);
        [reflexivity |].
      exact Hprod. }
    assert (HdA'_nz : dA' <> 0).
    { unfold dA'. apply prodl_nonzero.
      intros v Hv. apply List.in_map_iff in Hv.
      destruct Hv as (k & <- & Hk). apply List.in_seq in Hk.
      assert (Hk' : (k < Z.to_nat (Domain.usable_rows domain))%nat)
        by (exact (proj2 Hk)).
      exact (proj1 (Hfac k Hk')). }
    assert (Hwl_len2 : List.length NS' = List.length Ns)
      by (rewrite HNS'_len, HNs_len; reflexivity).
    assert (Hgs_len' : List.length gs = S (List.length NS'))
      by (rewrite HNS'_len; exact Hgs_len).
    destruct (prod_lin_scaled_agreement
      NS' Ns gs dA' da Hwl_len2 Hgs_ndp Hgs_len'
      (prodl_canonical _)
      (prodl_canonical _) HdA'_nz
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
    destruct (eval_prod_lin_zero_inv
      NA' ((- v) mod p) Hroot_A')
      as (r & Hr_in & Hr_zero).
    unfold NA' in Hr_in.
    apply List.in_map_iff in Hr_in.
    destruct Hr_in as (j1 & Hr_eq & Hj1).
    apply List.in_seq in Hj1.
    subst r.
    assert (HvA : A' (Z.of_nat j1) mod p = v mod p).
    { apply sub_mod_zero_iff in Hr_zero.
      rewrite !Zmod_mod in Hr_zero.
      rewrite <- (opp_mod_opp
        (A' (Z.of_nat j1))).
      rewrite <- Hr_zero.
      apply opp_mod_opp. }
    (* the chain into the S' values *)
    assert (Hj1u : Z.of_nat j1 < u)
      by (clear -Hun Hj1; rewrite <- Hun; apply Nat2Z.inj_lt; lia).
    assert (Hj1u' : Z.of_nat j1 < Domain.usable_rows domain)
      by (exact Hj1u).
    destruct (permuted_chain
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
      - apply sub_mod_zero_iff.
        rewrite !Zmod_mod.
        apply opp_mod_congr.
        symmetry. exact HvS. }
    assert (Hroot_s :
      Poly.eval (p := p) (Poly.prod_lin (p := p) Ns) ((- v) mod p) = 0).
    { rewrite <- (Poly.eval_peq (p := p) _ _ ((- v) mod p) HpeqS).
      exact Hroot_S'. }
    destruct (eval_prod_lin_zero_inv
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
    { apply sub_mod_zero_iff in Hr2_zero.
      rewrite !Zmod_mod in Hr2_zero.
      rewrite <- (opp_mod_opp
        (comb_table pairs theta (Z.of_nat t))).
      rewrite <- Hr2_zero.
      apply opp_mod_opp. }
    unfold v in Hct.
    unfold comb_input, comb_table
      in Hct |- *.
    rewrite !comb_canonical in Hct.
    symmetry. exact Hct.
  Qed.

  (** ** The per-θ multiset step

      At a fixed [θ] with committed [A'], [S']: the rules at every regular
      [(β, γ)] identify the [A']-factor polynomial with the input-factor
      polynomial and the [S']-factor polynomial with the table-factor
      polynomial (via the root bound over one more point than the degree),
      and the permuted-column chain then carries every usable-row combined
      input value into the combined table values. *)
  Lemma per_theta_membership (domain : Domain.t)
      (pairs : list ((Z -> Z) * (Z -> Z))) (theta : Z)
      (Hbf : 0 <= domain.(Domain.blinding_factors))
      (Hu : 0 <= Domain.usable_rows domain)
      (Hp_pts :
        Z.of_nat (2 * Z.to_nat (Domain.usable_rows domain) + 2) <= p)
      (A' S' : Z -> Z)
      (Hbg : forall beta gamma : Z,
        lookup_challenge_regular domain pairs theta beta gamma ->
        exists Zp,
          lookup_rules_hold domain pairs theta beta gamma A' S' Zp) :
    forall j0 : nat, Z.of_nat j0 < Domain.usable_rows domain ->
    exists t : nat, (t < Z.to_nat (Domain.usable_rows domain))%nat /\
      comb_input pairs theta (Z.of_nat j0) =
      comb_table pairs theta (Z.of_nat t).
  Proof.
    set (un := Z.to_nat (Domain.usable_rows domain)) in *.
    set (pool := List.map Z.of_nat (List.seq 0 (2 * un + 1))).
    assert (Hnd : Poly.NoDupP (p := p) pool).
    { apply Poly.NoDupP_of_nat_seq. lia. }
    assert (Hlen : (2 * un + 1 <= List.length pool)%nat).
    { unfold pool. rewrite List.length_map, List.length_seq. lia. }
    apply (per_theta_membership_of_pools domain pairs theta Hbf Hu A' S'
             pool pool Hnd Hlen Hnd Hlen).
    intros beta gamma _ _ Hreg. exact (Hbg beta gamma Hreg).
  Qed.

  (** ** Soundness: the five rules force membership

      The [θ]-Horner combination is de-combined by pigeonhole: over
      [usable_rows · m + 1] challenge points some table row witnesses [m]
      of them, and two degree-[< m] polynomials agreeing on [m]
      repetition-free points have equal coefficients — the tuples
      themselves.  The prefix condition then moves the witness into the
      loaded [table_rows] prefix. *)

  Theorem lookup_sound (domain : Domain.t)
      (pairs : list ((Z -> Z) * (Z -> Z))) (table_rows : Z)
      (Hbf : 0 <= domain.(Domain.blinding_factors))
      (Hu : 0 <= Domain.usable_rows domain)
      (Htr_pos : 0 < table_rows)
      (Htr_le : table_rows <= Domain.usable_rows domain)
      (Hcanon : pairs_canonical domain pairs)
      (Hcoh : table_prefix_coherent domain pairs table_rows)
      (Hp_pts :
        Z.of_nat (2 * Z.to_nat (Domain.usable_rows domain) + 2) <= p)
      (Hp_theta :
        Z.of_nat (Z.to_nat (Domain.usable_rows domain) *
          List.length pairs + 1) <= p)
      (Hid : lookup_identities_hold domain pairs) :
    lookup_membership domain pairs table_rows.
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
    (* the combined-value membership, for every θ *)
    assert (Hcomb : forall theta, exists t, (t < un)%nat /\
      comb_input pairs theta row = comb_table pairs theta (Z.of_nat t)).
    { intros theta.
      destruct (Hid theta) as (A' & S' & Hbg).
      assert (Hj0' : Z.of_nat j0 < Domain.usable_rows domain)
        by (exact Hj0).
      destruct (per_theta_membership domain pairs theta Hbf Hu Hp_pts
        A' S' Hbg j0 Hj0') as (t & Ht & Heq).
      exists t.
      split; [exact Ht |].
      rewrite <- Hrow_eq. exact Heq. }
    (* the degenerate empty-tuple case *)
    destruct (Nat.eq_dec m 0) as [Hm0 | Hmpos].
    { assert (Hnil : pairs = [])
        by (exact (proj1 (List.length_zero_iff_nil pairs) Hm0)).
      exists 0. split; [clear -Htr_pos; lia |].
      rewrite Hnil. constructor. }
    (* the challenge pool and the fiber choice *)
    set (m' := (m - 1)%nat).
    set (npool := (un * m + 1)%nat) in *.
    set (pool := List.map Z.of_nat (List.seq 0 npool)).
    set (pickb := fun th : Z =>
      match List.find (fun t =>
        comb_input pairs th row =? comb_table pairs th (Z.of_nat t))
        (List.seq 0 un) with
      | Some t => t
      | None => 0%nat
      end).
    assert (Hpick : forall th, (pickb th < un)%nat /\
      comb_input pairs th row =
      comb_table pairs th (Z.of_nat (pickb th))).
    { intros th.
      destruct (Hcomb th) as (t & Ht & Heq).
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
    assert (Hpool_len : List.length pool = npool)
      by (unfold pool; rewrite List.length_map, List.length_seq;
          reflexivity).
    assert (Hpool_bound : (un * m' < List.length pool)%nat)
      by (rewrite Hpool_len; unfold npool; clear -Hmul_le; lia).
    destruct (fiber_pigeonhole un m' pickb pool
      (fun x _ => proj1 (Hpick x)) Hpool_bound) as (t & Ht_lt & Hfib).
    set (fiber := List.filter (fun th => Nat.eqb (pickb th) t) pool) in *.
    set (thetas := List.firstn m fiber).
    assert (Hfib_m : (m <= List.length fiber)%nat)
      by (clear -Hfib Hmpos; unfold m' in Hfib; lia).
    assert (Hth_len : List.length thetas = m)
      by (unfold thetas; apply List.firstn_length_le; exact Hfib_m).
    assert (Hth_nd : List.NoDup thetas).
    { unfold thetas. apply NoDup_firstn.
      unfold fiber. apply List.NoDup_filter.
      unfold pool.
      apply NoDup_map_inj; [exact Nat2Z.inj | apply List.seq_NoDup]. }
    assert (Hth_in_pool : forall th, List.In th thetas -> List.In th pool).
    { intros th Hth.
      unfold thetas in Hth.
      apply In_firstn in Hth.
      unfold fiber in Hth.
      apply List.filter_In in Hth. exact (proj1 Hth). }
    assert (Hth_canon : forall th, List.In th thetas -> 0 <= th < p).
    { intros th Hth.
      pose proof (Hth_in_pool th Hth) as Hpoolin.
      unfold pool in Hpoolin.
      apply List.in_map_iff in Hpoolin.
      destruct Hpoolin as (i & <- & Hi).
      apply List.in_seq in Hi.
      split; [clear; lia |].
      apply Z.lt_le_trans with (Z.of_nat npool);
        [clear -Hi; lia | exact Hp_theta]. }
    assert (Hth_ndp : Poly.NoDupP (p := p) thetas).
    { apply NoDupP_of_canonical; [| exact Hth_nd].
      intros th Hth. apply Z.mod_small. exact (Hth_canon th Hth). }
    assert (Hth_agree : forall th, List.In th thetas ->
      comb_input pairs th row = comb_table pairs th (Z.of_nat t)).
    { intros th Hth.
      assert (Hth' : List.In th fiber)
        by (unfold thetas in Hth; exact (In_firstn m fiber th Hth)).
      unfold fiber in Hth'.
      apply List.filter_In in Hth'.
      destruct Hth' as [_ Hpickt].
      apply Nat.eqb_eq in Hpickt.
      rewrite <- Hpickt.
      exact (proj2 (Hpick th)). }
    (* interpolation: the two tuples agree coefficientwise *)
    set (in_tup := input_tuple pairs row).
    set (tab_tup := table_tuple pairs (Z.of_nat t)).
    assert (Hin_len : List.length in_tup = m)
      by (unfold in_tup, input_tuple; apply List.length_map).
    assert (Htab_len : List.length tab_tup = m)
      by (unfold tab_tup, table_tuple; apply List.length_map).
    assert (Hpeq : Poly.peq (p := p) (List.rev in_tup) (List.rev tab_tup)).
    { apply (Poly.interpolant_unique (p := p) thetas).
      - exact Hth_ndp.
      - eapply Nat.le_trans; [apply pdeg_le_length |].
        rewrite List.length_rev, Hin_len, Hth_len.
        apply Nat.le_refl.
      - eapply Nat.le_trans; [apply pdeg_le_length |].
        rewrite List.length_rev, Htab_len, Hth_len.
        apply Nat.le_refl.
      - intros th Hth.
        rewrite <- !comb_eval.
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
    unfold pairs_canonical in Hcanon.
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
      { unfold in_tup, input_tuple.
        rewrite (List.nth_indep (List.map (fun fg => fst fg row) pairs)
          0 (fst dfg row))
          by (rewrite List.length_map; exact Hi').
        exact (List.map_nth
          (fun fg : (Z -> Z) * (Z -> Z) => fst fg row) pairs dfg i). }
      assert (Htab_nth :
        List.nth i tab_tup 0 = snd (List.nth i pairs dfg) (Z.of_nat t)).
      { unfold tab_tup, table_tuple.
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

  (** The equivalence, under the soundness-side conditions. *)
  Corollary lookup_poly_iff (domain : Domain.t)
      (pairs : list ((Z -> Z) * (Z -> Z))) (table_rows : Z)
      (Hbf : 0 <= domain.(Domain.blinding_factors))
      (Hu : 0 <= Domain.usable_rows domain)
      (Htr_pos : 0 < table_rows)
      (Htr_le : table_rows <= Domain.usable_rows domain)
      (Hcanon : pairs_canonical domain pairs)
      (Hcoh : table_prefix_coherent domain pairs table_rows)
      (Hp_pts :
        Z.of_nat (2 * Z.to_nat (Domain.usable_rows domain) + 2) <= p)
      (Hp_theta :
        Z.of_nat (Z.to_nat (Domain.usable_rows domain) *
          List.length pairs + 1) <= p) :
    lookup_identities_hold domain pairs <->
    lookup_membership domain pairs table_rows.
  Proof.
    split.
    - intros Hid.
      exact (lookup_sound domain pairs table_rows Hbf Hu Htr_pos Htr_le
        Hcanon Hcoh Hp_pts Hp_theta Hid).
    - intros Hmem.
      exact (lookup_complete domain pairs table_rows Hbf Hu Htr_le Hmem).
  Qed.

  (** ** The assignment-level reading

      [argument_pair_functions] instantiates the abstract pair functions
      for a [LookupArgument.t] under an assignment: the input function is
      the expression value per row, the table function the raw lookup-plane
      read — exactly the two sides [eval_lookup_argument] compares. *)

  Definition argument_pair_functions {columns0 : Columns.t}
      {RegionId0 : Set}
      (Γ : Assignment.t columns0 RegionId0) (region : RegionId0)
      (arg : LookupArgument.t columns0) : list ((Z -> Z) * (Z -> Z)) :=
    List.map
      (fun pair =>
        ((fun row : Z => eval_expression Γ (region, row) (fst pair)),
         (fun table_row : Z =>
            Γ.(Assignment.lookup) (snd pair) table_row)))
      arg.(LookupArgument.pairs).

  (** The membership reading over the instantiated pair functions is
      exactly [eval_lookup_argument] — the acceptance conjunct of the
      compiled lookup interface. *)
  Lemma membership_eval_lookup_argument {columns0 : Columns.t}
      {RegionId0 : Set}
      (Γ : Assignment.t columns0 RegionId0) (region : RegionId0)
      (arg : LookupArgument.t columns0)
      (table_rows row : Z) :
    (exists table_row, 0 <= table_row < table_rows /\
       List.Forall (fun fg => fst fg row = snd fg table_row)
         (argument_pair_functions Γ region arg)) <->
    eval_lookup_argument Γ (region, row) table_rows arg.
  Proof.
    unfold argument_pair_functions.
    split; intros (table_row & Htr & HF); exists table_row;
      (split; [exact Htr |]);
      rewrite List.Forall_forall in HF; apply List.Forall_forall.
    - intros [expression column] Hin.
      pose proof
        (HF _ (List.in_map _ arg.(LookupArgument.pairs) _ Hin)) as Hp'.
      cbn [fst snd] in Hp'.
      exact Hp'.
    - intros fg Hin.
      apply List.in_map_iff in Hin.
      destruct Hin as (pair & Hfg & Hin).
      subst fg.
      destruct pair as [expression column].
      pose proof (HF _ Hin) as Hp'.
      cbn [fst snd].
      exact Hp'.
  Qed.

  (** Expression values are canonical residues: every evaluation head is a
      field operation. *)
  Lemma eval_expression_canonical {columns0 : Columns.t}
      {RegionId0 : Set}
      (Γ : Assignment.t columns0 RegionId0) (index : RegionId0 * Z)
      (expression : Expression.t columns0) :
    eval_expression Γ index expression mod p =
    eval_expression Γ index expression.
  Proof.
    destruct index as [region row].
    destruct expression as
      [ constant | selector | fixed rotation | advice rotation
      | instance rotation | inner | lhs rhs | lhs rhs | inner scale ];
      cbn [eval_expression]; try apply Zmod_mod.
    destruct rhs; apply Zmod_mod.
  Qed.

  (** The table-plane values the argument reads are canonical residues —
      discharged on a concrete instance by computation over the loaded
      table columns. *)
  Definition argument_table_canonical {columns0 : Columns.t}
      {RegionId0 : Set}
      (Γ : Assignment.t columns0 RegionId0) (domain : Domain.t)
      (arg : LookupArgument.t columns0) : Prop :=
    List.Forall
      (fun pair =>
        forall row, 0 <= row < Domain.usable_rows domain ->
          (Γ.(Assignment.lookup) (snd pair) row) mod p =
          Γ.(Assignment.lookup) (snd pair) row)
      arg.(LookupArgument.pairs).

  Lemma argument_pairs_canonical {columns0 : Columns.t} {RegionId0 : Set}
      (Γ : Assignment.t columns0 RegionId0) (region : RegionId0)
      (domain : Domain.t) (arg : LookupArgument.t columns0) :
    argument_table_canonical Γ domain arg ->
    pairs_canonical domain (argument_pair_functions Γ region arg).
  Proof.
    intros Htab.
    unfold pairs_canonical, argument_pair_functions.
    unfold argument_table_canonical in Htab.
    rewrite List.Forall_forall in Htab.
    apply List.Forall_forall.
    intros fg Hfg.
    apply List.in_map_iff in Hfg.
    destruct Hfg as (pair & Hfg & Hin).
    subst fg.
    intros row Hrow.
    split.
    - cbn [fst]. apply eval_expression_canonical.
    - cbn [snd]. exact (Htab pair Hin row Hrow).
  Qed.

  (** ** The per-argument equivalence against [eval_lookup_argument] *)

  Theorem lookup_argument_sound {columns0 : Columns.t} {RegionId0 : Set}
      (domain : Domain.t)
      (Γ : Assignment.t columns0 RegionId0) (region : RegionId0)
      (arg : LookupArgument.t columns0) (table_rows : Z)
      (Hbf : 0 <= domain.(Domain.blinding_factors))
      (Hu : 0 <= Domain.usable_rows domain)
      (Htr_pos : 0 < table_rows)
      (Htr_le : table_rows <= Domain.usable_rows domain)
      (Htab_canon : argument_table_canonical Γ domain arg)
      (Hcoh : table_prefix_coherent domain
        (argument_pair_functions Γ region arg) table_rows)
      (Hp_pts :
        Z.of_nat (2 * Z.to_nat (Domain.usable_rows domain) + 2) <= p)
      (Hp_theta :
        Z.of_nat (Z.to_nat (Domain.usable_rows domain) *
          List.length arg.(LookupArgument.pairs) + 1) <= p)
      (Hid : lookup_identities_hold domain
        (argument_pair_functions Γ region arg)) :
    forall row, 0 <= row < Domain.usable_rows domain ->
    eval_lookup_argument Γ (region, row) table_rows arg.
  Proof.
    intros row Hrow.
    assert (Hp_theta' :
      Z.of_nat (Z.to_nat (Domain.usable_rows domain) *
        List.length (argument_pair_functions Γ region arg) + 1) <= p).
    { unfold argument_pair_functions. rewrite List.length_map.
      exact Hp_theta. }
    pose proof (lookup_sound domain (argument_pair_functions Γ region arg)
      table_rows Hbf Hu Htr_pos Htr_le
      (argument_pairs_canonical Γ region domain arg Htab_canon)
      Hcoh Hp_pts Hp_theta' Hid) as Hmem.
    apply (proj1 (membership_eval_lookup_argument Γ region arg
      table_rows row)).
    exact (Hmem row Hrow).
  Qed.

  Theorem lookup_argument_complete {columns0 : Columns.t}
      {RegionId0 : Set}
      (domain : Domain.t)
      (Γ : Assignment.t columns0 RegionId0) (region : RegionId0)
      (arg : LookupArgument.t columns0) (table_rows : Z)
      (Hbf : 0 <= domain.(Domain.blinding_factors))
      (Hu : 0 <= Domain.usable_rows domain)
      (Htr_le : table_rows <= Domain.usable_rows domain)
      (Heval : forall row, 0 <= row < Domain.usable_rows domain ->
        eval_lookup_argument Γ (region, row) table_rows arg) :
    lookup_identities_hold domain (argument_pair_functions Γ region arg).
  Proof.
    apply (lookup_complete domain _ table_rows Hbf Hu Htr_le).
    intros row Hrow.
    apply (proj2 (membership_eval_lookup_argument Γ region arg
      table_rows row)).
    exact (Heval row Hrow).
  Qed.

  (** The list-level reading: the conjunct shape of
      [PlonkishLookup.plonkish_accepts_compiled]. *)
  Theorem lookup_arguments_sound {columns0 : Columns.t} {RegionId0 : Set}
      (domain : Domain.t)
      (Γ : Assignment.t columns0 RegionId0) (region : RegionId0)
      (lookups : list (LookupArgument.t columns0)) (table_rows : Z)
      (Hbf : 0 <= domain.(Domain.blinding_factors))
      (Hu : 0 <= Domain.usable_rows domain)
      (Htr_pos : 0 < table_rows)
      (Htr_le : table_rows <= Domain.usable_rows domain)
      (Hp_pts :
        Z.of_nat (2 * Z.to_nat (Domain.usable_rows domain) + 2) <= p)
      (Hargs : List.Forall (fun arg =>
        argument_table_canonical Γ domain arg /\
        table_prefix_coherent domain
          (argument_pair_functions Γ region arg) table_rows /\
        Z.of_nat (Z.to_nat (Domain.usable_rows domain) *
          List.length arg.(LookupArgument.pairs) + 1) <= p /\
        lookup_identities_hold domain
          (argument_pair_functions Γ region arg)) lookups) :
    forall row, 0 <= row < Domain.usable_rows domain ->
    List.Forall (eval_lookup_argument Γ (region, row) table_rows) lookups.
  Proof.
    intros row Hrow.
    rewrite List.Forall_forall in Hargs.
    apply List.Forall_forall.
    intros arg Hin.
    destruct (Hargs arg Hin) as (Hc1 & Hc2 & Hc3 & Hc4).
    exact (lookup_argument_sound domain Γ region arg table_rows
      Hbf Hu Htr_pos Htr_le Hc1 Hc2 Hp_pts Hc3 Hc4 row Hrow).
  Qed.

  Theorem lookup_arguments_complete {columns0 : Columns.t}
      {RegionId0 : Set}
      (domain : Domain.t)
      (Γ : Assignment.t columns0 RegionId0) (region : RegionId0)
      (lookups : list (LookupArgument.t columns0)) (table_rows : Z)
      (Hbf : 0 <= domain.(Domain.blinding_factors))
      (Hu : 0 <= Domain.usable_rows domain)
      (Htr_le : table_rows <= Domain.usable_rows domain)
      (Heval : forall row, 0 <= row < Domain.usable_rows domain ->
        List.Forall (eval_lookup_argument Γ (region, row) table_rows)
          lookups) :
    List.Forall (fun arg =>
      lookup_identities_hold domain
        (argument_pair_functions Γ region arg)) lookups.
  Proof.
    apply List.Forall_forall.
    intros arg Hin.
    apply (lookup_argument_complete domain Γ region arg table_rows
      Hbf Hu Htr_le).
    intros row Hrow.
    pose proof (Heval row Hrow) as HF.
    rewrite List.Forall_forall in HF.
    exact (HF arg Hin).
  Qed.

End WithPrime.

End PlonkishLookupPoly.
