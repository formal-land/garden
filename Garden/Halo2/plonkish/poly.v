(** * Univariate polynomials over [Z/pZ] as coefficient lists.

    The polynomial toolkit for the algebraic (L1) layer of the plonkish
    refinement: coefficient-list polynomials over the mod-[p] arithmetic
    of [Field.Field], with evaluation, ring operations, normalization
    ([norm] canonicalizes every coefficient and strips trailing zeros;
    [peq] is normalized equality), degree, division by monic divisors
    (existence and uniqueness of quotient and remainder), the
    root / linear-factor correspondence, the root-count bound for nonzero
    polynomials, Lagrange interpolation on a repetition-free point list,
    and the product decomposition [X^n - 1 = prod_j (X - w^j)] for a
    primitive [2^s]-th root of unity [w].

    The library is deliberately minimal: no FFTs, no resultants, no UFD
    theory.  The all-challenge equivalence families of the vanishing /
    permutation / lookup arguments need evaluation, quotient existence
    and uniqueness by plain division, the root bound, and interpolation,
    and nothing else. *)

Require Import Garden.Field.Field.
Require Import Garden.Field.Div.
Require Import Garden.Field.Lemmas.
Require Import Stdlib.ZArith.Zpower.
Require Import Stdlib.ZArith.Zpow_facts.
Require Import Stdlib.Sorting.Permutation.

Import List.ListNotations.
Global Open Scope Z_scope.

Module Poly.
Section WithPrime.
  Context {p : Z} `{Prime p}.

  (** Coefficient lists, low degree first.  Coefficients are arbitrary
      integers; every reading ([coef], [eval]) reduces mod [p]. *)
  Definition t : Set := list Z.

  Lemma p_big : 1 < p.
  Proof. exact (prime_range (p := p)). Qed.

  (** ** The coefficient view *)

  Definition coef (f : t) (i : nat) : Z := (List.nth i f 0) mod p.

  Lemma coef_canonical (f : t) (i : nat) : coef f i mod p = coef f i.
  Proof. unfold coef. apply Zmod_mod. Qed.

  Lemma coef_nil (i : nat) : coef [] i = 0.
  Proof. unfold coef. destruct i; simpl; apply Zmod_0_l. Qed.

  Lemma coef_cons_0 (a : Z) (f : t) : coef (a :: f) 0 = a mod p.
  Proof. reflexivity. Qed.

  Lemma coef_cons_S (a : Z) (f : t) (i : nat) : coef (a :: f) (S i) = coef f i.
  Proof. reflexivity. Qed.

  (** ** Normalization: canonical coefficients, trailing zeros stripped *)

  Fixpoint norm (f : t) : t :=
    match f with
    | [] => []
    | c :: f' =>
      match norm f' with
      | [] => if c mod p =? 0 then [] else [c mod p]
      | g => (c mod p) :: g
      end
    end.

  (** Polynomial equality: equal normal forms (equivalently, pointwise
      equal coefficient functions — [peq_iff_coef]). *)
  Definition peq (f g : t) : Prop := norm f = norm g.

  (** [pdeg f] is the number of significant coefficients: [0] exactly for
      the zero polynomial, otherwise [degree + 1]. *)
  Definition pdeg (f : t) : nat := List.length (norm f).

  Definition lead (f : t) : Z := List.last (norm f) 0.

  Lemma norm_nil_coef (f : t) : norm f = [] -> forall i, coef f i = 0.
  Proof.
    induction f as [| c f' IH]; intros Hn i.
    - apply coef_nil.
    - simpl in Hn.
      destruct (norm f') as [| z g] eqn:E; [| discriminate Hn].
      destruct (c mod p =? 0) eqn:Ec; [| discriminate Hn].
      apply Z.eqb_eq in Ec.
      destruct i as [| j].
      + rewrite coef_cons_0. exact Ec.
      + rewrite coef_cons_S. apply IH. reflexivity.
  Qed.

  Lemma coef_zero_norm_nil (f : t) : (forall i, coef f i = 0) -> norm f = [].
  Proof.
    induction f as [| c f' IH]; intros Hc.
    - reflexivity.
    - simpl.
      rewrite IH by (intros i; exact (Hc (S i))).
      pose proof (Hc O) as H0. rewrite coef_cons_0 in H0.
      rewrite H0. reflexivity.
  Qed.

  Lemma norm_coef (f : t) (i : nat) : coef (norm f) i = coef f i.
  Proof.
    revert i; induction f as [| c f' IH]; intros i.
    - reflexivity.
    - simpl. destruct (norm f') as [| z g] eqn:E.
      + destruct (c mod p =? 0) eqn:Ec.
        * apply Z.eqb_eq in Ec.
          rewrite coef_nil.
          destruct i as [| j].
          -- rewrite coef_cons_0. symmetry; exact Ec.
          -- rewrite coef_cons_S. rewrite <- (IH j). symmetry; apply coef_nil.
        * destruct i as [| j].
          -- rewrite !coef_cons_0. apply Zmod_mod.
          -- rewrite !coef_cons_S. exact (IH j).
      + destruct i as [| j].
        * rewrite !coef_cons_0. apply Zmod_mod.
        * rewrite !coef_cons_S. exact (IH j).
  Qed.

  Lemma coef_ext (f g : t) : (forall i, coef f i = coef g i) -> norm f = norm g.
  Proof.
    revert g; induction f as [| a f' IH]; intros g Hc.
    - symmetry. apply coef_zero_norm_nil. intros i. rewrite <- Hc. apply coef_nil.
    - destruct g as [| b g'].
      + apply coef_zero_norm_nil. intros i. rewrite Hc. apply coef_nil.
      + assert (Ht : norm f' = norm g').
        { apply IH. intros i.
          pose proof (Hc (S i)) as HS. rewrite !coef_cons_S in HS. exact HS. }
        pose proof (Hc O) as H0. rewrite !coef_cons_0 in H0.
        simpl. rewrite Ht, H0. reflexivity.
  Qed.

  Lemma peq_iff_coef (f g : t) : peq f g <-> (forall i, coef f i = coef g i).
  Proof.
    split.
    - intros Hn i. rewrite <- (norm_coef f i), <- (norm_coef g i).
      unfold peq in Hn. rewrite Hn. reflexivity.
    - apply coef_ext.
  Qed.

  Lemma peq_refl (f : t) : peq f f.
  Proof. reflexivity. Qed.

  Lemma peq_sym (f g : t) : peq f g -> peq g f.
  Proof. unfold peq; auto. Qed.

  Lemma peq_trans (f g h : t) : peq f g -> peq g h -> peq f h.
  Proof. unfold peq; congruence. Qed.

  Lemma norm_idem (f : t) : norm (norm f) = norm f.
  Proof. apply coef_ext. intros i. apply norm_coef. Qed.

  Lemma pdeg_peq (f g : t) : peq f g -> pdeg f = pdeg g.
  Proof. unfold peq, pdeg. intros Hn. rewrite Hn. reflexivity. Qed.

  Lemma peq_nil_norm (f : t) : peq f [] <-> norm f = [].
  Proof. unfold peq. simpl. tauto. Qed.

  (** ** The leading coefficient *)

  Lemma last_nth (l : list Z) (d : Z) :
    l <> [] -> List.nth (List.length l - 1) l d = List.last l d.
  Proof.
    induction l as [| a l' IH]; intros Hne.
    - congruence.
    - destruct l' as [| b l''].
      + reflexivity.
      + replace (List.length (a :: b :: l'') - 1)%nat
          with (S (List.length (b :: l'') - 1))%nat by (simpl; lia).
        change (List.nth (S (List.length (b :: l'') - 1)) (a :: b :: l'') d)
          with (List.nth (List.length (b :: l'') - 1) (b :: l'') d).
        change (List.last (a :: b :: l'') d) with (List.last (b :: l'') d).
        apply IH. discriminate.
  Qed.

  Lemma norm_last_facts (f : t) :
    norm f = [] \/
    (List.last (norm f) 0 <> 0 /\ (List.last (norm f) 0) mod p = List.last (norm f) 0).
  Proof.
    induction f as [| c f' IH].
    - left; reflexivity.
    - simpl. destruct (norm f') as [| z g] eqn:E.
      + destruct (c mod p =? 0) eqn:Ec.
        * left; reflexivity.
        * right. apply Z.eqb_neq in Ec. simpl. split; [exact Ec | apply Zmod_mod].
      + right. destruct IH as [IH | IH]; [congruence |].
        simpl in IH |- *. exact IH.
  Qed.

  Lemma lead_nonzero (f : t) : norm f <> [] -> lead f <> 0.
  Proof.
    intros Hne. unfold lead.
    destruct (norm_last_facts f) as [Hc | [Hc _]]; [congruence | exact Hc].
  Qed.

  Lemma lead_canonical (f : t) : lead f mod p = lead f.
  Proof.
    unfold lead. destruct (norm_last_facts f) as [Hc | [_ Hc]].
    - rewrite Hc. simpl. apply Zmod_0_l.
    - exact Hc.
  Qed.

  Lemma lead_coef (f : t) : norm f <> [] -> coef f (pdeg f - 1) = lead f.
  Proof.
    intros Hne. unfold pdeg.
    rewrite <- (norm_coef f). unfold coef.
    rewrite (last_nth (norm f) 0 Hne).
    exact (lead_canonical f).
  Qed.

  (** ** Degree bridges *)

  Lemma coef_ge (f : t) (i : nat) : (List.length f <= i)%nat -> coef f i = 0.
  Proof.
    intros Hle. unfold coef. rewrite List.nth_overflow by exact Hle. apply Zmod_0_l.
  Qed.

  Lemma coef_ge_pdeg (f : t) (i : nat) : (pdeg f <= i)%nat -> coef f i = 0.
  Proof. intros Hle. rewrite <- norm_coef. apply coef_ge. exact Hle. Qed.

  Lemma pdeg_nil_iff (f : t) : pdeg f = O <-> norm f = [].
  Proof.
    unfold pdeg. split; intros Hn.
    - apply List.length_zero_iff_nil; auto.
    - rewrite Hn; reflexivity.
  Qed.

  Lemma pdeg_le_of_coef (f : t) (k : nat) :
    (forall i, (k <= i)%nat -> coef f i = 0) -> (pdeg f <= k)%nat.
  Proof.
    intros Hc.
    destruct (norm f) as [| z g] eqn:E.
    - assert (Hz : pdeg f = O) by (apply pdeg_nil_iff; exact E). lia.
    - destruct (Nat.le_gt_cases (pdeg f) k) as [Hle | Hgt]; [exact Hle |].
      exfalso.
      assert (Hne : norm f <> []) by (rewrite E; discriminate).
      pose proof (lead_coef f Hne) as Hl.
      pose proof (lead_nonzero f Hne) as Hnz.
      apply Hnz. rewrite <- Hl. apply Hc. lia.
  Qed.

  Lemma pdeg_gt_of_coef (f : t) (i : nat) : coef f i <> 0 -> (i < pdeg f)%nat.
  Proof.
    intros Hc. destruct (Nat.le_gt_cases (pdeg f) i) as [Hle |]; [| assumption].
    exfalso. apply Hc. apply coef_ge_pdeg. exact Hle.
  Qed.

  (** ** Ring operations *)

  Fixpoint padd (f g : t) : t :=
    match f, g with
    | [], _ => g
    | _, [] => f
    | a :: f', b :: g' => ((a + b) mod p) :: padd f' g'
    end.

  Definition pscale (c : Z) (f : t) : t := List.map (fun b => (c * b) mod p) f.

  Definition popp (f : t) : t := List.map (fun b => (- b) mod p) f.

  Definition psub (f g : t) : t := padd f (popp g).

  (** Multiplication by [X^d]. *)
  Definition shift (d : nat) (f : t) : t := List.repeat 0 d ++ f.

  Fixpoint pmul (f g : t) : t :=
    match f with
    | [] => []
    | a :: f' => padd (pscale a g) (0 :: pmul f' g)
    end.

  Lemma padd_nil_l (g : t) : padd [] g = g.
  Proof. reflexivity. Qed.

  Lemma padd_nil_r (f : t) : padd f [] = f.
  Proof. destruct f; reflexivity. Qed.

  Lemma coef_padd (f g : t) (i : nat) :
    coef (padd f g) i = (coef f i + coef g i) mod p.
  Proof.
    revert g i; induction f as [| a f' IH]; intros g i.
    - rewrite padd_nil_l, coef_nil, Z.add_0_l. symmetry. apply coef_canonical.
    - destruct g as [| b g'].
      + rewrite padd_nil_r, coef_nil, Z.add_0_r. symmetry. apply coef_canonical.
      + destruct i as [| j]; simpl padd.
        * rewrite !coef_cons_0. now rewrite Zmod_mod, Zplus_mod.
        * rewrite !coef_cons_S. apply IH.
  Qed.

  Lemma coef_pscale (c : Z) (f : t) (i : nat) :
    coef (pscale c f) i = (c * coef f i) mod p.
  Proof.
    revert i; induction f as [| b f' IH]; intros i.
    - rewrite !coef_nil. now rewrite Z.mul_0_r, Zmod_0_l.
    - destruct i as [| j]; unfold pscale; simpl List.map.
      + rewrite !coef_cons_0. now rewrite Zmod_mod, Zmult_mod_idemp_r.
      + rewrite !coef_cons_S. apply IH.
  Qed.

  Lemma coef_popp (f : t) (i : nat) : coef (popp f) i = (- coef f i) mod p.
  Proof.
    revert i; induction f as [| b f' IH]; intros i.
    - rewrite !coef_nil. reflexivity.
    - destruct i as [| j]; unfold popp; simpl List.map.
      + rewrite !coef_cons_0. rewrite Zmod_mod.
        rewrite <- (Z.sub_0_l b), <- (Z.sub_0_l (b mod p)).
        now rewrite Zminus_mod_idemp_r.
      + rewrite !coef_cons_S. apply IH.
  Qed.

  Lemma coef_psub (f g : t) (i : nat) :
    coef (psub f g) i = (coef f i - coef g i) mod p.
  Proof.
    unfold psub. rewrite coef_padd, coef_popp.
    rewrite Zplus_mod_idemp_r. f_equal; ring.
  Qed.

  Lemma coef_shift (d : nat) (f : t) (i : nat) :
    coef (shift d f) i = if (i <? d)%nat then 0 else coef f (i - d)%nat.
  Proof.
    revert i; induction d as [| d' IH]; intros i.
    - unfold shift. simpl. rewrite Nat.sub_0_r. destruct i; reflexivity.
    - destruct i as [| j].
      + unfold shift. simpl. apply Zmod_0_l.
      + unfold shift in *. simpl. rewrite coef_cons_S. apply IH.
  Qed.

  (** ** Evaluation (Horner), always reduced mod [p] *)

  Fixpoint eval (f : t) (x : Z) : Z :=
    match f with
    | [] => 0
    | a :: f' => (a + x * eval f' x) mod p
    end.

  Lemma eval_canonical (f : t) (x : Z) : eval f x mod p = eval f x.
  Proof. destruct f; simpl; [apply Zmod_0_l | apply Zmod_mod]. Qed.

  (** The recurring Horner-step reduction. *)
  Lemma horner_mod (u x v : Z) : (u + x * (v mod p)) mod p = (u + x * v) mod p.
  Proof. rewrite Zplus_mod, Zmult_mod_idemp_r, <- Zplus_mod. reflexivity. Qed.

  Lemma eval_norm_nil (f : t) (x : Z) : norm f = [] -> eval f x = 0.
  Proof.
    induction f as [| c f' IH]; intros Hn; [reflexivity |].
    simpl in Hn |- *.
    destruct (norm f') as [| z g] eqn:E; [| discriminate Hn].
    destruct (c mod p =? 0) eqn:Ec; [| discriminate Hn].
    apply Z.eqb_eq in Ec.
    rewrite IH by reflexivity.
    rewrite Z.mul_0_r, Z.add_0_r. exact Ec.
  Qed.

  Lemma eval_norm (f : t) (x : Z) : eval (norm f) x = eval f x.
  Proof.
    induction f as [| c f' IH]; [reflexivity |].
    simpl. destruct (norm f') as [| z g] eqn:E.
    - assert (Hf' : eval f' x = 0).
      { apply eval_norm_nil. exact E. }
      destruct (c mod p =? 0) eqn:Ec.
      + apply Z.eqb_eq in Ec. simpl.
        rewrite Hf', Z.mul_0_r, Z.add_0_r. symmetry. exact Ec.
      + simpl.
        rewrite Hf', !Z.mul_0_r, !Z.add_0_r. now rewrite Zmod_mod.
    - simpl in IH |- *.
      rewrite IH.
      apply Zplus_mod_idemp_l.
  Qed.

  Lemma eval_peq (f g : t) (x : Z) : peq f g -> eval f x = eval g x.
  Proof.
    intros Hn. rewrite <- (eval_norm f), <- (eval_norm g).
    unfold peq in Hn. now rewrite Hn.
  Qed.

  Lemma eval_padd (f g : t) (x : Z) :
    eval (padd f g) x = (eval f x + eval g x) mod p.
  Proof.
    revert g; induction f as [| a f' IH]; intros g.
    - rewrite padd_nil_l. simpl. now rewrite eval_canonical.
    - destruct g as [| b g'].
      + rewrite padd_nil_r. simpl (eval [] x). rewrite Z.add_0_r.
        now rewrite eval_canonical.
      + simpl. rewrite IH.
        rewrite Zplus_mod_idemp_l, horner_mod.
        rewrite <- Zplus_mod.
        f_equal; ring.
  Qed.

  Lemma eval_pscale (c : Z) (f : t) (x : Z) :
    eval (pscale c f) x = (c * eval f x) mod p.
  Proof.
    induction f as [| b f' IH].
    - simpl. now rewrite Z.mul_0_r, Zmod_0_l.
    - unfold pscale in *. simpl. rewrite IH.
      rewrite Zplus_mod_idemp_l, horner_mod.
      rewrite Zmult_mod_idemp_r.
      f_equal; ring.
  Qed.

  Lemma eval_popp (f : t) (x : Z) : eval (popp f) x = (- eval f x) mod p.
  Proof.
    induction f as [| b f' IH].
    - simpl. reflexivity.
    - unfold popp in *. simpl. rewrite IH.
      rewrite Zplus_mod_idemp_l, horner_mod.
      rewrite <- (Z.sub_0_l ((b + x * eval f' x) mod p)).
      rewrite Zminus_mod_idemp_r.
      f_equal; ring.
  Qed.

  Lemma eval_psub (f g : t) (x : Z) :
    eval (psub f g) x = (eval f x - eval g x) mod p.
  Proof.
    unfold psub. rewrite eval_padd, eval_popp.
    rewrite Zplus_mod_idemp_r. f_equal; ring.
  Qed.

  Lemma eval_pmul (f g : t) (x : Z) :
    eval (pmul f g) x = (eval f x * eval g x) mod p.
  Proof.
    induction f as [| a f' IH].
    - simpl. now rewrite Zmod_0_l.
    - simpl pmul. rewrite eval_padd, eval_pscale.
      simpl (eval (0 :: pmul f' g) x). rewrite IH.
      rewrite Zplus_mod_idemp_l, Zplus_mod_idemp_r, horner_mod.
      simpl (eval (a :: f') x).
      rewrite Zmult_mod_idemp_l.
      f_equal; ring.
  Qed.

  Lemma eval_shift (d : nat) (f : t) (x : Z) :
    eval (shift d f) x = (Zpower_nat x d * eval f x) mod p.
  Proof.
    induction d as [| d' IH].
    - unfold shift. simpl List.repeat. simpl List.app.
      change (Zpower_nat x 0) with 1.
      rewrite Z.mul_1_l. now rewrite eval_canonical.
    - unfold shift in *.
      change (List.repeat 0 (S d') ++ f) with (0 :: (List.repeat 0 d' ++ f)).
      change (eval (0 :: (List.repeat 0 d' ++ f)) x)
        with ((0 + x * eval (List.repeat 0 d' ++ f) x) mod p).
      rewrite IH.
      rewrite Z.add_0_l, Zmult_mod_idemp_r.
      rewrite Zpower_nat_succ_r.
      f_equal; ring.
  Qed.

  (** ** Plain integer sums, and the convolution formula for [pmul] *)

  Definition zsum (l : list Z) : Z := List.fold_right Z.add 0 l.

  Lemma zsum_cons (a : Z) (l : list Z) : zsum (a :: l) = a + zsum l.
  Proof. reflexivity. Qed.

  Lemma zsum_map_ext_in {A : Set} (h1 h2 : A -> Z) (l : list A) :
    (forall a, List.In a l -> h1 a = h2 a) ->
    zsum (List.map h1 l) = zsum (List.map h2 l).
  Proof.
    induction l as [| a l' IH]; intros Hh; [reflexivity |].
    simpl. rewrite (Hh a) by (left; reflexivity).
    rewrite IH by (intros b Hb; apply Hh; right; exact Hb).
    reflexivity.
  Qed.

  Lemma zsum_map_zero {A : Set} (h : A -> Z) (l : list A) :
    (forall a, List.In a l -> h a = 0) -> zsum (List.map h l) = 0.
  Proof.
    induction l as [| a l' IH]; intros Hh; [reflexivity |].
    simpl. rewrite (Hh a) by (left; reflexivity).
    rewrite IH by (intros b Hb; apply Hh; right; exact Hb).
    reflexivity.
  Qed.

  Lemma zsum_map_add {A : Set} (h1 h2 : A -> Z) (l : list A) :
    zsum (List.map (fun a => h1 a + h2 a) l) =
    zsum (List.map h1 l) + zsum (List.map h2 l).
  Proof.
    induction l as [| a l' IH]; simpl; [reflexivity | rewrite IH; ring].
  Qed.

  Lemma zsum_map_single {A : Set} (h : A -> Z) (l : list A) (a0 : A) :
    List.NoDup l -> List.In a0 l ->
    (forall a, List.In a l -> a <> a0 -> h a = 0) ->
    zsum (List.map h l) = h a0.
  Proof.
    induction l as [| a l' IH]; intros Hnd Hin Hz; [destruct Hin |].
    inversion Hnd as [| ? ? Hnotin Hnd']; subst.
    destruct Hin as [-> | Hin].
    - simpl. rewrite (zsum_map_zero h l').
      + ring.
      + intros b Hb. apply Hz; [right; exact Hb |].
        intros ->. exact (Hnotin Hb).
    - simpl. rewrite (Hz a) by (try (left; reflexivity); intros ->; exact (Hnotin Hin)).
      rewrite (IH Hnd' Hin) by (intros b Hb Hne; apply Hz; [right; exact Hb | exact Hne]).
      ring.
  Qed.

  (** Lifting pointwise mod-[p] agreement through a sum. *)
  Lemma zsum_mod_map_ext {A : Set} (h1 h2 : A -> Z) (l : list A) :
    (forall a, List.In a l -> h1 a mod p = h2 a mod p) ->
    zsum (List.map h1 l) mod p = zsum (List.map h2 l) mod p.
  Proof.
    induction l as [| a l' IH]; intros Hh; [reflexivity |].
    simpl.
    rewrite (Zplus_mod (h1 a)), (Zplus_mod (h2 a)).
    rewrite (Hh a) by (left; reflexivity).
    rewrite IH by (intros b Hb; apply Hh; right; exact Hb).
    reflexivity.
  Qed.

  Definition conv (f g : t) (k : nat) : Z :=
    zsum (List.map (fun i => coef f i * coef g (k - i)%nat) (List.seq 0 (S k))) mod p.

  Lemma coef_pmul (f g : t) (k : nat) : coef (pmul f g) k = conv f g k.
  Proof.
    revert k; induction f as [| a f' IH]; intros k.
    - simpl pmul. rewrite coef_nil. unfold conv.
      rewrite zsum_map_zero.
      + now rewrite Zmod_0_l.
      + intros i _. rewrite coef_nil. apply Z.mul_0_l.
    - simpl pmul. rewrite coef_padd, coef_pscale.
      destruct k as [| k'].
      + rewrite coef_cons_0, Zmod_0_l, Z.add_0_r, Zmod_mod.
        unfold conv.
        change (List.seq 0 1) with [O].
        rewrite List.map_cons, zsum_cons. cbn beta.
        simpl List.map. change (zsum []) with 0.
        rewrite Z.add_0_r.
        rewrite coef_cons_0.
        rewrite Zmult_mod_idemp_l.
        change (0 - 0)%nat with O.
        reflexivity.
      + rewrite coef_cons_S, IH.
        unfold conv.
        rewrite <- Zplus_mod.
        change (List.seq 0 (S (S k'))) with (O :: List.seq 1 (S k')).
        rewrite List.map_cons, zsum_cons. cbn beta.
        rewrite <- List.seq_shift, List.map_map.
        rewrite coef_cons_0.
        rewrite (Zplus_mod (a mod p * coef g (S k' - 0)%nat)).
        rewrite Zmult_mod_idemp_l.
        rewrite <- Zplus_mod.
        change (S k' - 0)%nat with (S k').
        reflexivity.
  Qed.

  (** ** Congruence of the operations with respect to [peq] *)

  Lemma padd_compat (f f' g g' : t) :
    peq f f' -> peq g g' -> peq (padd f g) (padd f' g').
  Proof.
    rewrite !peq_iff_coef. intros Hf Hg i.
    rewrite !coef_padd, Hf, Hg. reflexivity.
  Qed.

  Lemma conv_ext (f f' g g' : t) (k : nat) :
    (forall i, coef f i = coef f' i) -> (forall i, coef g i = coef g' i) ->
    conv f g k = conv f' g' k.
  Proof.
    intros Hf Hg. unfold conv. f_equal.
    apply zsum_map_ext_in. intros i _. rewrite Hf, Hg. reflexivity.
  Qed.

  Lemma pmul_compat (f f' g g' : t) :
    peq f f' -> peq g g' -> peq (pmul f g) (pmul f' g').
  Proof.
    rewrite !peq_iff_coef. intros Hf Hg k.
    rewrite !coef_pmul. apply conv_ext; assumption.
  Qed.

  Lemma psub_compat (f f' g g' : t) :
    peq f f' -> peq g g' -> peq (psub f g) (psub f' g').
  Proof.
    rewrite !peq_iff_coef. intros Hf Hg i.
    rewrite !coef_psub, Hf, Hg. reflexivity.
  Qed.

  (** ** Algebraic identities up to [peq] *)

  Lemma padd_comm (f g : t) : peq (padd f g) (padd g f).
  Proof. apply coef_ext. intros i. rewrite !coef_padd. f_equal; ring. Qed.

  Lemma padd_swap (x y z : t) : peq (padd (padd x y) z) (padd (padd x z) y).
  Proof.
    apply coef_ext. intros i.
    rewrite !coef_padd, !Zplus_mod_idemp_l. f_equal; ring.
  Qed.

  Lemma padd_zero_r (f z : t) : norm z = [] -> peq (padd f z) f.
  Proof.
    intros Hz. apply coef_ext. intros i.
    rewrite coef_padd, (norm_nil_coef z Hz), Z.add_0_r. apply coef_canonical.
  Qed.

  Lemma psub_padd_cancel (f h : t) : peq (padd (psub f h) h) f.
  Proof.
    apply coef_ext. intros i.
    rewrite coef_padd, coef_psub, Zplus_mod_idemp_l.
    replace (coef f i - coef h i + coef h i) with (coef f i) by ring.
    apply coef_canonical.
  Qed.

  Lemma psub_zero_iff (f g : t) : peq (psub f g) [] <-> peq f g.
  Proof.
    rewrite !peq_iff_coef.
    split; intros Hc i; pose proof (Hc i) as Hi; clear Hc.
    - rewrite coef_psub, coef_nil in Hi.
      change ((coef f i - coef g i) mod p) with (BinOp.sub (coef f i) (coef g i)) in Hi.
      apply sub_zero_equiv in Hi.
      unfold UnOp.from in Hi. rewrite !coef_canonical in Hi. exact Hi.
    - rewrite coef_psub, coef_nil, Hi, Z.sub_diag. apply Zmod_0_l.
  Qed.

  Lemma padd_cross (a x b y : t) :
    peq (padd a x) (padd b y) -> peq (psub a b) (psub y x).
  Proof.
    rewrite !peq_iff_coef. intros Hc i. pose proof (Hc i) as Hi; clear Hc.
    rewrite !coef_padd in Hi. rewrite !coef_psub.
    replace (coef a i - coef b i)
      with ((coef a i + coef x i) - (coef b i + coef x i)) by ring.
    rewrite Zminus_mod, Hi, <- Zminus_mod.
    f_equal; ring.
  Qed.

  Lemma zsum_map_sub {A : Set} (h1 h2 : A -> Z) (l : list A) :
    zsum (List.map (fun a => h1 a - h2 a) l) =
    zsum (List.map h1 l) - zsum (List.map h2 l).
  Proof.
    induction l as [| a l' IH]; simpl; [reflexivity | rewrite IH; ring].
  Qed.

  Lemma pmul_padd_distr_r (a b g : t) :
    peq (pmul (padd a b) g) (padd (pmul a g) (pmul b g)).
  Proof.
    apply coef_ext. intros k.
    rewrite coef_padd, !coef_pmul. unfold conv.
    rewrite <- Zplus_mod, <- zsum_map_add.
    apply zsum_mod_map_ext. intros i _. cbn beta.
    rewrite coef_padd, Zmult_mod_idemp_l.
    f_equal; ring.
  Qed.

  Lemma pmul_psub_distr_r (a b g : t) :
    peq (pmul (psub a b) g) (psub (pmul a g) (pmul b g)).
  Proof.
    apply coef_ext. intros k.
    rewrite coef_psub, !coef_pmul. unfold conv.
    rewrite <- Zminus_mod, <- zsum_map_sub.
    apply zsum_mod_map_ext. intros i _. cbn beta.
    rewrite coef_psub, Zmult_mod_idemp_l.
    f_equal; ring.
  Qed.

  Lemma coef_single (c : Z) (i : nat) :
    coef [c] i = if (i =? 0)%nat then c mod p else 0.
  Proof. destruct i as [| j]; [reflexivity | exact (coef_nil j)]. Qed.

  Lemma pmul_shift_single (c : Z) (d : nat) (g : t) :
    peq (pmul (shift d [c]) g) (shift d (pscale c g)).
  Proof.
    apply coef_ext. intros k.
    rewrite coef_pmul. unfold conv.
    rewrite coef_shift.
    destruct (Nat.ltb_spec k d) as [Hlt | Hge].
    - rewrite zsum_map_zero.
      + now rewrite Zmod_0_l.
      + intros i Hi. cbn beta.
        rewrite coef_shift.
        apply List.in_seq in Hi.
        destruct (Nat.ltb_spec i d) as [Hid | Hid].
        * apply Z.mul_0_l.
        * lia.
    - rewrite (zsum_map_single _ _ d).
      + cbn beta. rewrite coef_shift.
        destruct (Nat.ltb_spec d d) as [Hdd | _]; [lia |].
        rewrite Nat.sub_diag, coef_single.
        simpl (0 =? 0)%nat.
        rewrite coef_pscale.
        now rewrite Zmult_mod_idemp_l.
      + apply List.seq_NoDup.
      + apply List.in_seq. lia.
      + intros i Hi Hne. cbn beta. rewrite coef_shift.
        apply List.in_seq in Hi.
        destruct (Nat.ltb_spec i d) as [Hid | Hid].
        * apply Z.mul_0_l.
        * rewrite coef_single.
          destruct (Nat.eqb_spec (i - d) 0) as [He | He].
          -- exfalso. apply Hne. lia.
          -- apply Z.mul_0_l.
  Qed.

  (** ** Degree bounds *)

  Lemma pdeg_pos (f : t) : norm f <> [] -> (1 <= pdeg f)%nat.
  Proof.
    intros Hne. destruct (pdeg f) eqn:E; [| lia].
    exfalso. apply Hne. apply pdeg_nil_iff. exact E.
  Qed.

  Lemma pdeg_padd_le (f g : t) :
    (pdeg (padd f g) <= Nat.max (pdeg f) (pdeg g))%nat.
  Proof.
    apply pdeg_le_of_coef. intros i Hi.
    rewrite coef_padd, !coef_ge_pdeg by lia. reflexivity.
  Qed.

  Lemma pdeg_psub_le (f g : t) :
    (pdeg (psub f g) <= Nat.max (pdeg f) (pdeg g))%nat.
  Proof.
    apply pdeg_le_of_coef. intros i Hi.
    rewrite coef_psub, !coef_ge_pdeg by lia. reflexivity.
  Qed.

  Lemma pdeg_pscale_le (c : Z) (f : t) : (pdeg (pscale c f) <= pdeg f)%nat.
  Proof.
    apply pdeg_le_of_coef. intros i Hi.
    rewrite coef_pscale, coef_ge_pdeg by lia.
    now rewrite Z.mul_0_r, Zmod_0_l.
  Qed.

  Lemma pmul_coef_high (f g : t) (k : nat) :
    (pdeg f + pdeg g <= S k)%nat -> coef (pmul f g) k = 0.
  Proof.
    intros Hk. rewrite coef_pmul. unfold conv.
    rewrite zsum_map_zero.
    - now rewrite Zmod_0_l.
    - intros i Hi. apply List.in_seq in Hi. cbn beta.
      destruct (Nat.le_gt_cases (pdeg f) i) as [Hf | Hf].
      + rewrite (coef_ge_pdeg f) by lia. apply Z.mul_0_l.
      + rewrite (coef_ge_pdeg g) by lia. apply Z.mul_0_r.
  Qed.

  Lemma coef_pmul_top (f g : t) (df dg : nat) :
    pdeg f = S df -> pdeg g = S dg ->
    coef (pmul f g) (df + dg)%nat = (lead f * lead g) mod p.
  Proof.
    intros Hf Hg.
    assert (Hnef : norm f <> []).
    { intro E. apply pdeg_nil_iff in E; congruence. }
    assert (Hneg : norm g <> []).
    { intro E. apply pdeg_nil_iff in E; congruence. }
    rewrite coef_pmul. unfold conv.
    rewrite (zsum_map_single _ _ df).
    - cbn beta.
      replace (df + dg - df)%nat with dg by lia.
      pose proof (lead_coef f Hnef) as Hlf.
      pose proof (lead_coef g Hneg) as Hlg.
      rewrite Hf in Hlf. rewrite Hg in Hlg.
      simpl in Hlf, Hlg.
      rewrite Nat.sub_0_r in Hlf, Hlg.
      now rewrite Hlf, Hlg.
    - apply List.seq_NoDup.
    - apply List.in_seq. lia.
    - intros i Hi Hne. apply List.in_seq in Hi. cbn beta.
      destruct (Nat.le_gt_cases (pdeg f) i) as [Hif | Hif].
      + rewrite (coef_ge_pdeg f) by lia. apply Z.mul_0_l.
      + rewrite (coef_ge_pdeg g) by lia. apply Z.mul_0_r.
  Qed.

  Lemma lead_mul_nonzero (f g : t) :
    norm f <> [] -> norm g <> [] -> (lead f * lead g) mod p <> 0.
  Proof.
    intros Hf Hg Hc.
    change ((lead f * lead g) mod p) with (BinOp.mul (lead f) (lead g)) in Hc.
    apply mul_zero_implies_zero in Hc.
    unfold UnOp.from in Hc. rewrite !lead_canonical in Hc.
    destruct Hc as [Hc | Hc].
    - exact (lead_nonzero f Hf Hc).
    - exact (lead_nonzero g Hg Hc).
  Qed.

  Lemma pdeg_pmul (f g : t) :
    norm f <> [] -> norm g <> [] ->
    pdeg (pmul f g) = (pdeg f + pdeg g - 1)%nat.
  Proof.
    intros Hf Hg.
    pose proof (pdeg_pos f Hf) as H1f. pose proof (pdeg_pos g Hg) as H1g.
    destruct (pdeg f) as [| df] eqn:Ef; [lia |].
    destruct (pdeg g) as [| dg] eqn:Eg; [lia |].
    assert (Htop : coef (pmul f g) (df + dg)%nat = (lead f * lead g) mod p)
      by (apply coef_pmul_top; assumption).
    apply Nat.le_antisymm.
    - replace (S df + S dg - 1)%nat with (S (df + dg))%nat by lia.
      apply pdeg_le_of_coef. intros i Hi. apply pmul_coef_high. lia.
    - replace (S df + S dg - 1)%nat with (S (df + dg))%nat by lia.
      apply pdeg_gt_of_coef. rewrite Htop.
      apply lead_mul_nonzero; assumption.
  Qed.

  Lemma pmul_nonnil (f g : t) :
    norm f <> [] -> norm g <> [] -> norm (pmul f g) <> [].
  Proof.
    intros Hf Hg E.
    pose proof (pdeg_pmul f g Hf Hg) as Hd.
    pose proof (pdeg_pos f Hf). pose proof (pdeg_pos g Hg).
    assert (Hz : pdeg (pmul f g) = O) by (apply pdeg_nil_iff; exact E).
    lia.
  Qed.

  Lemma lead_pmul (f g : t) :
    norm f <> [] -> norm g <> [] ->
    lead (pmul f g) = (lead f * lead g) mod p.
  Proof.
    intros Hf Hg.
    pose proof (pdeg_pos f Hf) as H1f. pose proof (pdeg_pos g Hg) as H1g.
    pose proof (pmul_nonnil f g Hf Hg) as Hne.
    pose proof (lead_coef (pmul f g) Hne) as Hl.
    rewrite (pdeg_pmul f g Hf Hg) in Hl.
    destruct (pdeg f) as [| df] eqn:Ef; [lia |].
    destruct (pdeg g) as [| dg] eqn:Eg; [lia |].
    replace (S df + S dg - 1 - 1)%nat with (df + dg)%nat in Hl by lia.
    rewrite coef_pmul_top in Hl by assumption.
    symmetry; exact Hl.
  Qed.

  (** ** Division by a monic divisor: existence and uniqueness *)

  Definition monic (g : t) : Prop := lead g = 1.

  Lemma monic_nonnil (g : t) : monic g -> norm g <> [].
  Proof.
    unfold monic, lead. intros Hm E. rewrite E in Hm. simpl in Hm. lia.
  Qed.

  Lemma monic_pdeg_pos (g : t) : monic g -> (1 <= pdeg g)%nat.
  Proof. intros Hm. apply pdeg_pos, monic_nonnil, Hm. Qed.

  Lemma monic_top_coef (g : t) : monic g -> coef g (pdeg g - 1) = 1.
  Proof.
    intros Hm. rewrite lead_coef by (apply monic_nonnil, Hm). exact Hm.
  Qed.

  (** One elimination step: subtract [lead f * X^(pdeg f - pdeg g) * g].
      The top coefficient cancels, so the degree strictly drops. *)
  Lemma division_step_deg (f g : t) :
    monic g -> (pdeg g <= pdeg f)%nat -> norm f <> [] ->
    (pdeg (psub f (shift (pdeg f - pdeg g) (pscale (lead f) g))) < pdeg f)%nat.
  Proof.
    intros Hg Hle Hf.
    pose proof (pdeg_pos f Hf) as H1f.
    pose proof (monic_pdeg_pos g Hg) as H1g.
    assert (Hstep : (pdeg (psub f (shift (pdeg f - pdeg g) (pscale (lead f) g)))
                     <= pdeg f - 1)%nat); [| lia].
    apply pdeg_le_of_coef. intros i Hi.
    rewrite coef_psub, coef_shift.
    destruct (Nat.ltb_spec i (pdeg f - pdeg g)) as [Hid | Hid]; [lia |].
    rewrite coef_pscale.
    destruct (Nat.eq_dec i (pdeg f - 1)%nat) as [-> | Hne].
    - replace (pdeg f - 1 - (pdeg f - pdeg g))%nat with (pdeg g - 1)%nat by lia.
      rewrite (monic_top_coef g Hg).
      rewrite lead_coef by exact Hf.
      rewrite Z.mul_1_r.
      rewrite Zminus_mod_idemp_r.
      now rewrite Z.sub_diag, Zmod_0_l.
    - rewrite (coef_ge_pdeg f i) by lia.
      rewrite (coef_ge_pdeg g) by lia.
      rewrite Z.mul_0_r. reflexivity.
  Qed.

  Fixpoint pdivmod_fuel (fuel : nat) (f g : t) : t * t :=
    match fuel with
    | O => ([], f)
    | S fu =>
      if (pdeg f <? pdeg g)%nat then ([], f)
      else
        let d := (pdeg f - pdeg g)%nat in
        let c := lead f in
        let f1 := psub f (shift d (pscale c g)) in
        let '(q, r) := pdivmod_fuel fu f1 g in
        (padd q (shift d [c]), r)
    end.

  Definition pdivmod (f g : t) : t * t := pdivmod_fuel (pdeg f) f g.
  Definition pdiv (f g : t) : t := fst (pdivmod f g).
  Definition pmod (f g : t) : t := snd (pdivmod f g).

  Lemma pdivmod_fuel_spec (g : t) (Hg : monic g) :
    forall (fuel : nat) (f : t), (pdeg f <= fuel)%nat ->
    peq f (padd (pmul (fst (pdivmod_fuel fuel f g)) g) (snd (pdivmod_fuel fuel f g))) /\
    (pdeg (snd (pdivmod_fuel fuel f g)) < pdeg g)%nat.
  Proof.
    pose proof (monic_pdeg_pos g Hg) as H1g.
    induction fuel as [| fu IH]; intros f Hfuel.
    - simpl. split; [exact (peq_refl f) | lia].
    - simpl.
      destruct (Nat.ltb_spec (pdeg f) (pdeg g)) as [Hlt | Hge].
      + simpl. split; [exact (peq_refl f) | exact Hlt].
      + assert (Hf : norm f <> []).
        { intro E.
          assert (Hz : pdeg f = O) by (apply pdeg_nil_iff; exact E). lia. }
        pose proof (division_step_deg f g Hg Hge Hf) as Hdrop.
        specialize (IH (psub f (shift (pdeg f - pdeg g) (pscale (lead f) g)))
                       ltac:(lia)).
        destruct (pdivmod_fuel fu
                    (psub f (shift (pdeg f - pdeg g) (pscale (lead f) g))) g)
          as [q r] eqn:Erec.
        simpl in IH |- *.
        destruct IH as [IHeq IHdeg].
        split; [| exact IHdeg].
        eapply peq_trans.
        { apply peq_sym.
          apply (psub_padd_cancel f
                   (shift (pdeg f - pdeg g) (pscale (lead f) g))). }
        eapply peq_trans.
        { apply padd_compat; [exact IHeq | apply peq_refl]. }
        eapply peq_trans.
        { apply padd_swap. }
        apply padd_compat; [| apply peq_refl].
        eapply peq_trans; [| apply peq_sym; apply pmul_padd_distr_r].
        apply padd_compat; [apply peq_refl |].
        apply peq_sym. apply pmul_shift_single.
  Qed.

  Theorem pdivmod_spec (f g : t) :
    monic g ->
    peq f (padd (pmul (pdiv f g) g) (pmod f g)) /\ (pdeg (pmod f g) < pdeg g)%nat.
  Proof.
    intros Hg. exact (pdivmod_fuel_spec g Hg (pdeg f) f (Nat.le_refl _)).
  Qed.

  (** Uniqueness of the quotient and remainder: two decompositions with
      remainders below [pdeg g] agree up to [peq]. *)
  Theorem pdivmod_unique (g q r q' r' : t) :
    monic g ->
    (pdeg r < pdeg g)%nat -> (pdeg r' < pdeg g)%nat ->
    peq (padd (pmul q g) r) (padd (pmul q' g) r') ->
    peq q q' /\ peq r r'.
  Proof.
    intros Hg Hr Hr' Heq.
    pose proof (padd_cross _ _ _ _ Heq) as Hcross.
    assert (Hprod : peq (pmul (psub q q') g) (psub r' r)).
    { eapply peq_trans; [apply pmul_psub_distr_r | exact Hcross]. }
    destruct (norm (psub q q')) as [| z zs] eqn:ED.
    - assert (Hqq : peq q q').
      { apply psub_zero_iff. unfold peq. rewrite ED. reflexivity. }
      split; [exact Hqq |].
      assert (Hz2 : peq (pmul (psub q q') g) []).
      { eapply peq_trans.
        - apply (pmul_compat (psub q q') [] g g);
            [unfold peq; rewrite ED; reflexivity | apply peq_refl].
        - apply peq_refl. }
      assert (Hrr : peq (psub r' r) []).
      { eapply peq_trans; [apply peq_sym; exact Hprod | exact Hz2]. }
      apply (proj1 (psub_zero_iff r' r)) in Hrr.
      apply peq_sym. exact Hrr.
    - exfalso.
      assert (HD : norm (psub q q') <> []) by (rewrite ED; discriminate).
      assert (Hgn : norm g <> []) by (apply monic_nonnil; exact Hg).
      pose proof (pdeg_pmul (psub q q') g HD Hgn) as Hdeg.
      pose proof (pdeg_pos _ HD) as H1D.
      pose proof (monic_pdeg_pos g Hg) as H1g.
      pose proof (pdeg_peq _ _ Hprod) as Hpe.
      pose proof (pdeg_psub_le r' r) as Hrb.
      lia.
  Qed.

  (** ** Roots, linear factors, and the root-count bound *)

  (** The monic linear polynomial [X - r]. *)
  Definition lin (r : Z) : t := [(- r) mod p; 1].

  Lemma eval_lin (r x : Z) : eval (lin r) x = (x - r) mod p.
  Proof.
    pose proof p_big.
    unfold lin.
    change (eval [(- r) mod p; 1] x)
      with (((- r) mod p + x * ((1 + x * 0) mod p)) mod p).
    rewrite Z.mul_0_r, Z.add_0_r.
    rewrite (Z.mod_1_l p) by lia.
    rewrite Z.mul_1_r.
    rewrite Zplus_mod_idemp_l.
    f_equal; ring.
  Qed.

  Lemma norm_lin (r : Z) : norm (lin r) = [(- r) mod p; 1].
  Proof.
    pose proof p_big.
    unfold lin. simpl.
    rewrite (Z.mod_1_l p) by lia.
    simpl.
    rewrite Zmod_mod. reflexivity.
  Qed.

  Lemma monic_lin (r : Z) : monic (lin r).
  Proof. unfold monic, lead. rewrite norm_lin. reflexivity. Qed.

  Lemma pdeg_lin (r : Z) : pdeg (lin r) = 2%nat.
  Proof. unfold pdeg. rewrite norm_lin. reflexivity. Qed.

  Lemma lin_nonnil (r : Z) : norm (lin r) <> [].
  Proof. rewrite norm_lin. discriminate. Qed.

  (** The root / linear-factor correspondence. *)
  Lemma root_factor (f : t) (r : Z) :
    eval f r = 0 <-> exists q, peq f (pmul q (lin r)).
  Proof.
    split.
    - intros Hroot.
      pose proof (pdivmod_spec f (lin r) (monic_lin r)) as [Heq Hdeg].
      exists (pdiv f (lin r)).
      assert (Hrem0 : eval (pmod f (lin r)) r = 0).
      { pose proof (eval_peq _ _ r Heq) as He.
        rewrite eval_padd, eval_pmul, eval_lin in He.
        rewrite Z.sub_diag, Zmod_0_l, Z.mul_0_r, Zmod_0_l, Z.add_0_l in He.
        rewrite eval_canonical in He. congruence. }
      assert (Hnil : norm (pmod f (lin r)) = []).
      { rewrite pdeg_lin in Hdeg.
        destruct (norm (pmod f (lin r))) as [| c [| c' cs]] eqn:Erm;
          [reflexivity | |].
        - exfalso.
          pose proof (norm_last_facts (pmod f (lin r))) as Hlf.
          rewrite Erm in Hlf.
          destruct Hlf as [Hc | [Hnz Hcan]]; [discriminate |].
          simpl in Hnz, Hcan.
          pose proof (eval_norm (pmod f (lin r)) r) as Hev.
          rewrite Erm in Hev. simpl in Hev.
          rewrite Z.mul_0_r, Z.add_0_r in Hev.
          rewrite Hcan in Hev.
          congruence.
        - exfalso. unfold pdeg in Hdeg. rewrite Erm in Hdeg. simpl in Hdeg. lia. }
      eapply peq_trans; [exact Heq |].
      apply padd_zero_r. exact Hnil.
    - intros [q Hq].
      rewrite (eval_peq _ _ r Hq).
      rewrite eval_pmul, eval_lin.
      rewrite Z.sub_diag, Zmod_0_l, Z.mul_0_r. apply Zmod_0_l.
  Qed.

  (** Repetition-free point lists: pairwise distinct mod [p]. *)
  Definition NoDupP (l : list Z) : Prop :=
    List.NoDup (List.map (fun x => x mod p) l).

  (** A nonzero polynomial has fewer roots than significant coefficients:
      at most [pdeg f - 1 = degree] pairwise-distinct roots. *)
  Lemma roots_le_pdeg (rs : list Z) :
    forall (f : t), norm f <> [] -> NoDupP rs ->
    List.Forall (fun r => eval f r = 0) rs ->
    (List.length rs < pdeg f)%nat.
  Proof.
    induction rs as [| r rs' IH]; intros f Hf Hnd Hroots.
    - pose proof (pdeg_pos f Hf). simpl. lia.
    - inversion Hroots as [| ? ? Hr Hrs']; subst.
      unfold NoDupP in Hnd. simpl in Hnd.
      inversion Hnd as [| ? ? Hnotin Hnd']; subst.
      destruct (proj1 (root_factor f r) Hr) as [q Hq].
      assert (Hqn : norm q <> []).
      { intro E.
        apply Hf.
        assert (Hfnil : peq f []).
        { eapply peq_trans; [exact Hq |].
          eapply peq_trans.
          - apply (pmul_compat q [] (lin r) (lin r));
              [unfold peq; rewrite E; reflexivity | apply peq_refl].
          - apply peq_refl. }
        unfold peq in Hfnil. simpl in Hfnil. exact Hfnil. }
      assert (Hdegf : pdeg f = S (pdeg q)).
      { rewrite (pdeg_peq _ _ Hq).
        rewrite pdeg_pmul; [| exact Hqn | exact (lin_nonnil r)].
        rewrite pdeg_lin.
        pose proof (pdeg_pos q Hqn). lia. }
      assert (Hqroots : List.Forall (fun s => eval q s = 0) rs').
      { rewrite List.Forall_forall in Hrs' |- *. intros s Hs.
        pose proof (Hrs' s Hs) as Hfs.
        rewrite (eval_peq _ _ s Hq) in Hfs.
        rewrite eval_pmul, eval_lin in Hfs.
        change ((eval q s * ((s - r) mod p)) mod p)
          with (BinOp.mul (eval q s) ((s - r) mod p)) in Hfs.
        apply mul_zero_implies_zero in Hfs.
        unfold UnOp.from in Hfs.
        rewrite eval_canonical, Zmod_mod in Hfs.
        destruct Hfs as [Hz | Hz]; [exact Hz |].
        exfalso.
        apply Hnotin.
        assert (Hsr : s mod p = r mod p).
        { change ((s - r) mod p) with (BinOp.sub s r) in Hz.
          apply sub_zero_equiv in Hz. exact Hz. }
        rewrite <- Hsr.
        exact (List.in_map (fun x : Z => x mod p) rs' s Hs). }
      pose proof (IH q Hqn Hnd' Hqroots) as Hlt.
      simpl. lia.
  Qed.

  (** The zero test: a polynomial of degree below the number of its
      pairwise-distinct roots is the zero polynomial. *)
  Lemma zero_of_roots (f : t) (rs : list Z) :
    NoDupP rs -> List.Forall (fun r => eval f r = 0) rs ->
    (pdeg f <= List.length rs)%nat -> norm f = [].
  Proof.
    intros Hnd Hroots Hle.
    destruct (norm f) as [| z zs] eqn:E; [reflexivity |].
    exfalso.
    assert (Hne : norm f <> []) by (rewrite E; discriminate).
    pose proof (roots_le_pdeg rs f Hne Hnd Hroots). lia.
  Qed.

  (** Two polynomials of degree at most [length rs] agreeing on the
      repetition-free point list [rs] are equal. *)
  Lemma eval_ext (f g : t) (rs : list Z) :
    NoDupP rs ->
    (forall r, List.In r rs -> eval f r = eval g r) ->
    (pdeg f <= List.length rs)%nat -> (pdeg g <= List.length rs)%nat ->
    peq f g.
  Proof.
    intros Hnd Hev Hf Hg.
    apply psub_zero_iff.
    apply peq_nil_norm.
    apply (zero_of_roots (psub f g) rs Hnd).
    - rewrite List.Forall_forall. intros r Hr.
      rewrite eval_psub, (Hev r Hr), Z.sub_diag. apply Zmod_0_l.
    - pose proof (pdeg_psub_le f g). lia.
  Qed.

  (** ** Products of monic linear factors *)

  Fixpoint prod_lin (l : list Z) : t :=
    match l with
    | [] => [1]
    | r :: l' => pmul (lin r) (prod_lin l')
    end.

  Lemma norm_one : norm [1] = [1].
  Proof.
    pose proof p_big. simpl.
    rewrite (Z.mod_1_l p) by lia.
    reflexivity.
  Qed.

  Lemma prod_lin_monic (l : list Z) :
    monic (prod_lin l) /\ pdeg (prod_lin l) = S (List.length l).
  Proof.
    induction l as [| r l' IH].
    - split.
      + unfold monic, lead. cbn [prod_lin]. rewrite norm_one. reflexivity.
      + unfold pdeg. cbn [prod_lin]. rewrite norm_one. reflexivity.
    - destruct IH as [IHm IHd].
      assert (Hne : norm (prod_lin l') <> []) by (apply monic_nonnil; exact IHm).
      split.
      + unfold monic. cbn [prod_lin].
        rewrite lead_pmul; [| exact (lin_nonnil r) | exact Hne].
        pose proof (monic_lin r) as Hml. unfold monic in Hml, IHm.
        rewrite Hml, IHm.
        apply Z.mod_1_l. exact p_big.
      + cbn [prod_lin].
        rewrite pdeg_pmul; [| exact (lin_nonnil r) | exact Hne].
        rewrite pdeg_lin, IHd. simpl List.length. lia.
  Qed.

  Lemma prod_lin_nonnil (l : list Z) : norm (prod_lin l) <> [].
  Proof. apply monic_nonnil. apply (proj1 (prod_lin_monic l)). Qed.

  Lemma eval_prod_lin_zero (l : list Z) (x r : Z) :
    List.In r l -> (x - r) mod p = 0 -> eval (prod_lin l) x = 0.
  Proof.
    induction l as [| a l' IH]; intros Hin Hz; [destruct Hin |].
    cbn [prod_lin].
    rewrite eval_pmul, eval_lin.
    destruct Hin as [-> | Hin].
    - rewrite Hz. now rewrite Z.mul_0_l.
    - rewrite (IH Hin Hz). now rewrite Z.mul_0_r.
  Qed.

  Lemma eval_prod_lin_nonzero (l : list Z) (x : Z) :
    (forall r, List.In r l -> (x - r) mod p <> 0) ->
    eval (prod_lin l) x <> 0.
  Proof.
    induction l as [| a l' IH]; intros Hnz.
    - pose proof p_big.
      change (eval (prod_lin []) x) with ((1 + x * 0) mod p).
      rewrite Z.mul_0_r, Z.add_0_r.
      rewrite (Z.mod_1_l p) by lia. lia.
    - cbn [prod_lin]. rewrite eval_pmul, eval_lin.
      intro Hc.
      change (((x - a) mod p * eval (prod_lin l') x) mod p)
        with (BinOp.mul ((x - a) mod p) (eval (prod_lin l') x)) in Hc.
      apply mul_zero_implies_zero in Hc.
      unfold UnOp.from in Hc.
      rewrite Zmod_mod, eval_canonical in Hc.
      destruct Hc as [Hc | Hc].
      + exact (Hnz a (or_introl eq_refl) Hc).
      + assert (Hnz' : forall s, List.In s l' -> (x - s) mod p <> 0)
          by (intros s Hs; apply Hnz; right; exact Hs).
        exact (IH Hnz' Hc).
  Qed.

  (** ** Lagrange interpolation on a repetition-free point list *)

  Definition lag_term (others : list Z) (xi yi : Z) : t :=
    pscale (yi * mod_inverse (eval (prod_lin others) xi) p) (prod_lin others).

  Fixpoint lagrange_go (acc rest : list Z) (v : Z -> Z) : t :=
    match rest with
    | [] => []
    | x :: rest' =>
        padd (lag_term (acc ++ rest') x (v x)) (lagrange_go (x :: acc) rest' v)
    end.

  (** The interpolant of [v] on the point list [xs]. *)
  Definition lagrange (xs : list Z) (v : Z -> Z) : t := lagrange_go [] xs v.

  Lemma lagrange_go_eval_zero (v : Z -> Z) :
    forall (rest acc : list Z) (x0 : Z),
      (exists a, List.In a acc /\ (x0 - a) mod p = 0) ->
      eval (lagrange_go acc rest v) x0 = 0.
  Proof.
    induction rest as [| x rest' IH]; intros acc x0 Hacc; [reflexivity |].
    simpl lagrange_go.
    rewrite eval_padd.
    destruct Hacc as [a [Hina Hza]].
    unfold lag_term.
    rewrite eval_pscale.
    rewrite (eval_prod_lin_zero (acc ++ rest') x0 a);
      [| apply List.in_or_app; left; exact Hina | exact Hza].
    rewrite Z.mul_0_r, Zmod_0_l.
    rewrite (IH (x :: acc) x0).
    - reflexivity.
    - exists a. split; [right; exact Hina | exact Hza].
  Qed.

  Lemma lagrange_go_eval (v : Z -> Z) :
    forall (rest acc : list Z) (x0 : Z),
      NoDupP (acc ++ rest) -> List.In x0 rest ->
      eval (lagrange_go acc rest v) x0 = v x0 mod p.
  Proof.
    induction rest as [| x rest' IH]; intros acc x0 Hnd Hin; [destruct Hin |].
    pose proof Hnd as Hnd0.
    simpl lagrange_go.
    rewrite eval_padd.
    unfold NoDupP in Hnd.
    rewrite List.map_app in Hnd. simpl in Hnd.
    pose proof (List.NoDup_remove _ _ _ Hnd) as [Hnd2 Hnotin].
    rewrite <- List.map_app in Hnd2, Hnotin.
    destruct Hin as [-> | Hin].
    - rewrite (lagrange_go_eval_zero v rest' (x0 :: acc) x0).
      2: { exists x0. split; [left; reflexivity |].
           now rewrite Z.sub_diag. }
      unfold lag_term.
      rewrite eval_pscale.
      set (E := eval (prod_lin (acc ++ rest')) x0).
      assert (HE : E <> 0).
      { apply eval_prod_lin_nonzero.
        intros s Hs Hz.
        apply Hnotin.
        assert (Hsx : s mod p = x0 mod p).
        { change ((x0 - s) mod p) with (BinOp.sub x0 s) in Hz.
          apply sub_zero_equiv in Hz.
          symmetry. exact Hz. }
        rewrite <- Hsx.
        exact (List.in_map (fun y : Z => y mod p) (acc ++ rest') s Hs). }
      assert (Hinv : (mod_inverse E p * E) mod p = 1).
      { pose proof (mod_inverse_mul_prime (p := p) E) as Hm.
        unfold BinOp.mul in Hm. apply Hm.
        unfold E. rewrite eval_canonical. exact HE. }
      rewrite Z.add_0_r, Zmod_mod.
      rewrite <- Z.mul_assoc.
      rewrite <- Zmult_mod_idemp_r.
      rewrite Hinv.
      now rewrite Z.mul_1_r.
    - unfold lag_term.
      rewrite eval_pscale.
      rewrite (eval_prod_lin_zero (acc ++ rest') x0 x0);
        [| apply List.in_or_app; right; exact Hin | now rewrite Z.sub_diag].
      rewrite Z.mul_0_r, Zmod_0_l, Z.add_0_l.
      rewrite (IH (x :: acc) x0).
      + apply Zmod_mod.
      + unfold NoDupP in Hnd0 |- *.
        eapply Permutation_NoDup; [| exact Hnd0].
        apply Permutation_map.
        change ((x :: acc) ++ rest') with (x :: (acc ++ rest')).
        apply Permutation_sym. apply Permutation_middle.
      + exact Hin.
  Qed.

  Lemma lagrange_go_pdeg (v : Z -> Z) :
    forall (rest acc : list Z),
      (pdeg (lagrange_go acc rest v) <= List.length acc + List.length rest)%nat.
  Proof.
    induction rest as [| x rest' IH]; intros acc.
    - change (pdeg (lagrange_go acc [] v)) with (pdeg []).
      change (pdeg []) with O. lia.
    - simpl lagrange_go.
      eapply Nat.le_trans; [apply pdeg_padd_le |].
      apply Nat.max_lub.
      + unfold lag_term.
        eapply Nat.le_trans; [apply pdeg_pscale_le |].
        rewrite (proj2 (prod_lin_monic (acc ++ rest'))).
        rewrite List.length_app.
        simpl List.length. lia.
      + eapply Nat.le_trans; [apply (IH (x :: acc)) |].
        simpl List.length. lia.
  Qed.

  Theorem lagrange_eval (xs : list Z) (v : Z -> Z) (x : Z) :
    NoDupP xs -> List.In x xs -> eval (lagrange xs v) x = v x mod p.
  Proof.
    intros Hnd Hin. apply lagrange_go_eval; [exact Hnd | exact Hin].
  Qed.

  Theorem lagrange_pdeg (xs : list Z) (v : Z -> Z) :
    (pdeg (lagrange xs v) <= List.length xs)%nat.
  Proof.
    unfold lagrange.
    pose proof (lagrange_go_pdeg v xs []) as Hb. simpl in Hb. exact Hb.
  Qed.

  (** Uniqueness of the interpolant among polynomials of degree below the
      number of points. *)
  Theorem interpolant_unique (xs : list Z) (f g : t) :
    NoDupP xs ->
    (pdeg f <= List.length xs)%nat -> (pdeg g <= List.length xs)%nat ->
    (forall x, List.In x xs -> eval f x = eval g x) ->
    peq f g.
  Proof. intros Hnd Hf Hg Hev. exact (eval_ext f g xs Hnd Hev Hf Hg). Qed.

  (** The Kronecker-delta interpolant at the point [x0] (the shape of the
      [l_0] / [l_last] Lagrange selectors). *)
  Definition lagrange_delta (xs : list Z) (x0 : Z) : t :=
    lagrange xs (fun x => if x =? x0 then 1 else 0).

  Lemma lagrange_delta_eval (xs : list Z) (x0 x : Z) :
    NoDupP xs -> List.In x xs ->
    eval (lagrange_delta xs x0) x = (if x =? x0 then 1 else 0).
  Proof.
    intros Hnd Hin. unfold lagrange_delta.
    rewrite (lagrange_eval xs _ x Hnd Hin).
    pose proof p_big.
    destruct (x =? x0); [apply Z.mod_1_l; lia | apply Zmod_0_l].
  Qed.

  Lemma lagrange_delta_pdeg (xs : list Z) (x0 : Z) :
    (pdeg (lagrange_delta xs x0) <= List.length xs)%nat.
  Proof. apply lagrange_pdeg. Qed.

  (** ** The vanishing polynomial [X^n - 1] *)

  Definition xn1 (n : nat) : t := psub (shift n [1]) [1].

  Lemma eval_xn1 (n : nat) (x : Z) :
    eval (xn1 n) x = (Zpower_nat x n - 1) mod p.
  Proof.
    pose proof p_big.
    unfold xn1. rewrite eval_psub, eval_shift.
    change (eval [1] x) with ((1 + x * 0) mod p).
    rewrite Z.mul_0_r, Z.add_0_r.
    rewrite (Z.mod_1_l p) by lia.
    rewrite Z.mul_1_r.
    rewrite Zminus_mod_idemp_l.
    reflexivity.
  Qed.

  Lemma coef_xn1_top (n : nat) : (1 <= n)%nat -> coef (xn1 n) n = 1.
  Proof.
    intros Hn. pose proof p_big.
    unfold xn1. rewrite coef_psub, coef_shift.
    destruct (Nat.ltb_spec n n) as [|_]; [lia |].
    rewrite Nat.sub_diag.
    change (coef [1] 0) with (1 mod p).
    rewrite (coef_ge [1] n) by (simpl; lia).
    rewrite Z.sub_0_r, Zmod_mod.
    apply Z.mod_1_l; lia.
  Qed.

  Lemma coef_xn1_high (n i : nat) : (n < i)%nat -> coef (xn1 n) i = 0.
  Proof.
    intros Hi.
    unfold xn1. rewrite coef_psub, coef_shift.
    destruct (Nat.ltb_spec i n); [lia |].
    rewrite (coef_ge [1] (i - n)%nat) by (simpl; lia).
    rewrite (coef_ge [1] i) by (simpl; lia).
    reflexivity.
  Qed.

  Lemma xn1_pdeg (n : nat) : (1 <= n)%nat -> pdeg (xn1 n) = S n.
  Proof.
    intros Hn.
    apply Nat.le_antisymm.
    - apply pdeg_le_of_coef. intros i Hi. apply coef_xn1_high. lia.
    - apply pdeg_gt_of_coef. rewrite coef_xn1_top by exact Hn. lia.
  Qed.

  Lemma xn1_monic (n : nat) : (1 <= n)%nat -> monic (xn1 n).
  Proof.
    intros Hn. unfold monic.
    assert (Hne : norm (xn1 n) <> []).
    { intro E.
      assert (Hz : pdeg (xn1 n) = O) by (apply pdeg_nil_iff; exact E).
      pose proof (xn1_pdeg n Hn). lia. }
    pose proof (lead_coef (xn1 n) Hne) as Hl.
    rewrite (xn1_pdeg n Hn) in Hl.
    replace (S n - 1)%nat with n in Hl by lia.
    rewrite coef_xn1_top in Hl by exact Hn.
    symmetry; exact Hl.
  Qed.

  (** ** Primitive [2^s]-th roots of unity: powers enumerate without
      repetition, and [X^n - 1] splits into the linear factors over them *)

  Section PrimitiveRoot.
    Variable w : Z.
    Variable s : nat.
    Hypothesis Hs : (1 <= s)%nat.
    Hypothesis Hp2 : 2 < p.
    (** [w^(2^s) = 1] and [w^(2^(s-1)) = -1]: [w] has order exactly [2^s]. *)
    Hypothesis Hw_full : Fpow w (2 ^ Z.of_nat s) = 1.
    Hypothesis Hw_half : Fpow w (2 ^ (Z.of_nat s - 1)) = UnOp.from (-1).

    Lemma of_nat_pow2 (k : nat) : Z.of_nat (2 ^ k)%nat = 2 ^ Z.of_nat k.
    Proof.
      induction k as [| k' IH]; [reflexivity |].
      rewrite Nat.pow_succ_r'.
      rewrite Nat2Z.inj_mul, IH.
      change (Z.of_nat 2) with 2.
      rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
      reflexivity.
    Qed.

    Lemma from_neg1 : UnOp.from (-1) = p - 1.
    Proof.
      unfold UnOp.from.
      rewrite <- (Z.mod_add (-1) 1 p) by lia.
      replace (-1 + 1 * p) with (p - 1) by ring.
      apply Z.mod_small. lia.
    Qed.

    Lemma Fpow_one_l (n : Z) : 0 <= n -> Fpow 1 n = 1.
    Proof.
      intros Hn. unfold Fpow, UnOp.from.
      rewrite Z.pow_1_l by exact Hn. apply Z.mod_1_l. lia.
    Qed.

    Lemma Fpow_from_base (a n : Z) : Fpow (UnOp.from a) n = Fpow a n.
    Proof.
      unfold Fpow, UnOp.from.
      rewrite <- (Zpower_mod a n p) by lia.
      reflexivity.
    Qed.

    Lemma Fpow_neg1_odd (u : Z) :
      0 <= u -> Z.odd u = true -> Fpow (-1) u = UnOp.from (-1).
    Proof.
      intros Hu Hodd.
      destruct (proj1 (Z.odd_spec u) Hodd) as [v Hv].
      subst u.
      assert (Hv0 : 0 <= v) by lia.
      unfold Fpow.
      rewrite Z.pow_add_r by lia.
      rewrite Z.pow_mul_r by lia.
      change ((-1) ^ 2) with 1.
      rewrite Z.pow_1_l by exact Hv0.
      rewrite Z.pow_1_r.
      now rewrite Z.mul_1_l.
    Qed.

    (** The 2-adic order argument: an element with [a^(2^k) = 1] and
        [a^(2^(k-1)) = -1] has no power [a^m = 1] for [0 < m < 2^k].
        Odd [m] contradicts [(-1)^m = -1]; even [m] recurses on [a^2]. *)
    Lemma pow2_order_aux :
      forall (k : nat) (a : Z),
        (1 <= k)%nat ->
        Fpow a (2 ^ Z.of_nat k) = 1 ->
        Fpow a (2 ^ (Z.of_nat k - 1)) = UnOp.from (-1) ->
        forall m, 0 < m < 2 ^ Z.of_nat k -> Fpow a m <> 1.
    Proof.
      induction k as [| k' IH]; intros a Hk Hfull Hhalf m Hm Hc; [lia |].
      assert (Hexp : Z.of_nat (S k') - 1 = Z.of_nat k')
        by (rewrite Nat2Z.inj_succ; lia).
      rewrite Hexp in Hhalf.
      assert (He2 : 2 ^ Z.of_nat (S k') = 2 * 2 ^ Z.of_nat k').
      { rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. reflexivity. }
      assert (Hme : 0 <= m) by lia.
      assert (Hee : 0 <= 2 ^ Z.of_nat k') by (apply Z.pow_nonneg; lia).
      destruct (Z.odd m) eqn:Hodd.
      - assert (H1 : Fpow (Fpow a m) (2 ^ Z.of_nat k') = 1).
        { rewrite Hc. apply Fpow_one_l. exact Hee. }
        rewrite Fpow_mul in H1 by assumption.
        assert (H2 : Fpow (Fpow a (2 ^ Z.of_nat k')) m
                     = Fpow a (m * 2 ^ Z.of_nat k')).
        { rewrite Fpow_mul by assumption. f_equal; ring. }
        rewrite Hhalf, Fpow_from_base in H2.
        rewrite Fpow_neg1_odd in H2 by assumption.
        rewrite H1 in H2.
        rewrite from_neg1 in H2. lia.
      - assert (Hev : Z.Even m).
        { apply Z.even_spec. rewrite <- Z.negb_odd, Hodd. reflexivity. }
        destruct Hev as [m' Hm']. subst m.
        destruct k' as [| k''].
        + change (2 ^ Z.of_nat 1) with 2 in Hm. lia.
        + set (b := Fpow a 2).
          assert (Hbfull : Fpow b (2 ^ Z.of_nat (S k'')) = 1).
          { unfold b.
            rewrite Fpow_mul by (try apply Z.pow_nonneg; lia).
            rewrite <- He2. exact Hfull. }
          assert (Hbhalf : Fpow b (2 ^ (Z.of_nat (S k'') - 1)) = UnOp.from (-1)).
          { unfold b.
            rewrite Fpow_mul by (try apply Z.pow_nonneg; lia).
            replace (2 * 2 ^ (Z.of_nat (S k'') - 1)) with (2 ^ Z.of_nat (S k'')).
            - exact Hhalf.
            - rewrite <- Z.pow_succ_r by lia.
              f_equal. lia. }
          assert (Hbm : Fpow b m' = 1).
          { unfold b.
            rewrite Fpow_mul by lia.
            exact Hc. }
          refine (IH b _ Hbfull Hbhalf m' _ Hbm); [lia |].
          rewrite He2 in Hm. lia.
    Qed.

    Lemma w_pow_order (m : Z) : 0 < m < 2 ^ Z.of_nat s -> Fpow w m <> 1.
    Proof. intros Hm. exact (pow2_order_aux s w Hs Hw_full Hw_half m Hm). Qed.

    Lemma w_nonzero : UnOp.from w <> 0.
    Proof.
      intro Hw0.
      pose proof Hw_full as Hf.
      unfold Fpow, UnOp.from in Hf, Hw0.
      rewrite (Zpower_mod w _ p) in Hf by lia.
      rewrite Hw0 in Hf.
      rewrite Z.pow_0_l in Hf by (apply Z.pow_pos_nonneg; lia).
      rewrite Zmod_0_l in Hf. lia.
    Qed.

    Lemma w_pow_cancel (i j : Z) :
      0 <= i -> 0 <= j -> Fpow w i = Fpow w (i + j) -> Fpow w j = 1.
    Proof.
      intros Hi Hj Heq.
      rewrite Fpow_add in Heq by assumption.
      assert (Hnz : Fpow w i <> 0)
        by (apply Fpow_nonzero; [exact Hi | exact w_nonzero]).
      assert (Hz : BinOp.mul (Fpow w i) (BinOp.sub (Fpow w j) 1) = 0).
      { unfold BinOp.mul, BinOp.sub.
        rewrite Zmult_mod_idemp_r.
        replace (Fpow w i * (Fpow w j - 1))
          with (Fpow w i * Fpow w j - Fpow w i) by ring.
        rewrite Zminus_mod.
        change ((Fpow w i * Fpow w j) mod p) with (Fpow w i *F Fpow w j).
        rewrite <- Heq.
        change (Fpow w i mod p) with (UnOp.from (Fpow w i)).
        rewrite Fpow_reduced.
        now rewrite Z.sub_diag. }
      apply mul_zero_implies_zero in Hz.
      destruct Hz as [Hz | Hz].
      - exfalso. apply Hnz. rewrite Fpow_reduced in Hz. exact Hz.
      - unfold BinOp.sub in Hz.
        unfold UnOp.from in Hz.
        rewrite Zmod_mod in Hz.
        change ((Fpow w j - 1) mod p) with (BinOp.sub (Fpow w j) 1) in Hz.
        apply sub_zero_equiv in Hz.
        rewrite Fpow_reduced in Hz.
        unfold UnOp.from in Hz.
        rewrite Z.mod_1_l in Hz by lia.
        exact Hz.
    Qed.

    Lemma w_pow_inj (i j : Z) :
      0 <= i < 2 ^ Z.of_nat s -> 0 <= j < 2 ^ Z.of_nat s ->
      Fpow w i = Fpow w j -> i = j.
    Proof.
      intros Hi Hj Heq.
      destruct (Z.eq_dec i j) as [-> | Hne]; [reflexivity | exfalso].
      destruct (Z.le_gt_cases i j) as [Hle | Hgt].
      - assert (Hone : Fpow w (j - i) = 1).
        { apply (w_pow_cancel i (j - i)); [lia | lia |].
          replace (i + (j - i)) with j by ring. exact Heq. }
        apply (w_pow_order (j - i)); [lia | exact Hone].
      - assert (Hone : Fpow w (i - j) = 1).
        { apply (w_pow_cancel j (i - j)); [lia | lia |].
          replace (j + (i - j)) with i by ring. symmetry. exact Heq. }
        apply (w_pow_order (i - j)); [lia | exact Hone].
    Qed.

    (** The enumeration of [H = { w^j : 0 <= j < 2^s }], built by iterated
        multiplication (canonical residues throughout). *)
    Fixpoint w_pows_from (a : Z) (k : nat) : list Z :=
      match k with
      | O => []
      | S k' => a :: w_pows_from ((w * a) mod p) k'
      end.

    Definition w_pows : list Z := w_pows_from 1 (2 ^ s)%nat.

    Lemma w_pows_from_length (a : Z) (k : nat) :
      List.length (w_pows_from a k) = k.
    Proof.
      revert a; induction k as [| k' IH]; intros a; simpl; [reflexivity |].
      now rewrite IH.
    Qed.

    Lemma w_pows_length : List.length w_pows = (2 ^ s)%nat.
    Proof. apply w_pows_from_length. Qed.

    Lemma w_pows_from_nth (k : nat) :
      forall (a : Z) (j : nat), a mod p = a -> (j < k)%nat ->
      List.nth j (w_pows_from a k) 0 = (a * w ^ Z.of_nat j) mod p.
    Proof.
      induction k as [| k' IH]; intros a j Ha Hj; [lia |].
      destruct j as [| j'].
      - simpl. rewrite Z.mul_1_r. symmetry. exact Ha.
      - simpl List.nth.
        rewrite IH; [| apply Zmod_mod | lia].
        rewrite Zmult_mod_idemp_l.
        rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
        f_equal; ring.
    Qed.

    Lemma w_pows_nth (j : nat) :
      (j < 2 ^ s)%nat -> List.nth j w_pows 0 = Fpow w (Z.of_nat j).
    Proof.
      intros Hj. unfold w_pows.
      rewrite w_pows_from_nth; [| apply Z.mod_1_l; exact p_big | exact Hj].
      unfold Fpow, UnOp.from. f_equal; ring.
    Qed.

    Lemma w_pows_NoDupP : NoDupP w_pows.
    Proof.
      unfold NoDupP.
      assert (Hcan : forall (k : nat) (a : Z), a mod p = a ->
        List.map (fun x => x mod p) (w_pows_from a k) = w_pows_from a k).
      { induction k as [| k' IH]; intros a Ha; [reflexivity |].
        simpl. rewrite Ha. rewrite IH by apply Zmod_mod. reflexivity. }
      unfold w_pows.
      rewrite (Hcan _ 1) by (apply Z.mod_1_l, p_big).
      apply (proj2 (List.NoDup_nth _ 0)).
      intros i j Hi Hj Hnth.
      rewrite w_pows_from_length in Hi, Hj.
      change (w_pows_from 1 (2 ^ s)%nat) with w_pows in Hnth.
      rewrite !w_pows_nth in Hnth by assumption.
      apply Nat2Z.inj.
      apply (w_pow_inj (Z.of_nat i) (Z.of_nat j)).
      - split; [lia |]. rewrite <- of_nat_pow2. lia.
      - split; [lia |]. rewrite <- of_nat_pow2. lia.
      - exact Hnth.
    Qed.

    Lemma w_pows_in_char (x : Z) :
      List.In x w_pows ->
      exists j : nat, (j < 2 ^ s)%nat /\ x = Fpow w (Z.of_nat j).
    Proof.
      intros Hin.
      destruct (List.In_nth w_pows x 0 Hin) as [j [Hj Hx]].
      rewrite w_pows_length in Hj.
      exists j. split; [exact Hj |].
      rewrite <- Hx. apply w_pows_nth. exact Hj.
    Qed.

    Lemma w_pows_root (x : Z) :
      List.In x w_pows -> eval (xn1 (2 ^ s)%nat) x = 0.
    Proof.
      intros Hin.
      destruct (w_pows_in_char x Hin) as [j [Hj ->]].
      rewrite eval_xn1, Zpower_nat_Z, of_nat_pow2.
      rewrite Zminus_mod.
      change (Fpow w (Z.of_nat j) ^ 2 ^ Z.of_nat s mod p)
        with (Fpow (Fpow w (Z.of_nat j)) (2 ^ Z.of_nat s)).
      rewrite Fpow_mul by (try apply Z.pow_nonneg; lia).
      replace (Z.of_nat j * 2 ^ Z.of_nat s)
        with (2 ^ Z.of_nat s * Z.of_nat j) by ring.
      rewrite <- Fpow_mul by (try apply Z.pow_nonneg; lia).
      rewrite Hw_full.
      rewrite Fpow_one_l by lia.
      pose proof p_big.
      rewrite (Z.mod_1_l p) by lia.
      now rewrite Z.sub_diag.
    Qed.

    (** [X^(2^s) - 1 = prod_{j < 2^s} (X - w^j)] over the enumeration. *)
    Theorem xn1_factorization :
      peq (xn1 (2 ^ s)%nat) (prod_lin w_pows).
    Proof.
      pose proof p_big.
      assert (H2s : (2 ^ s <> 0)%nat) by (apply Nat.pow_nonzero; lia).
      assert (Hn1 : (1 <= 2 ^ s)%nat) by lia.
      apply psub_zero_iff.
      apply peq_nil_norm.
      apply (zero_of_roots _ w_pows w_pows_NoDupP).
      - rewrite List.Forall_forall. intros x Hx.
        rewrite eval_psub.
        rewrite (w_pows_root x Hx).
        rewrite (eval_prod_lin_zero w_pows x x Hx)
          by (now rewrite Z.sub_diag).
        reflexivity.
      - rewrite w_pows_length.
        apply pdeg_le_of_coef. intros i Hi.
        rewrite coef_psub.
        pose proof (prod_lin_monic w_pows) as [Hm Hd].
        destruct (Nat.eq_dec i (2 ^ s)%nat) as [-> | Hne].
        + rewrite coef_xn1_top by exact Hn1.
          assert (Hpl : coef (prod_lin w_pows) (2 ^ s)%nat = 1).
          { pose proof (lead_coef (prod_lin w_pows) (monic_nonnil _ Hm)) as Hl.
            rewrite Hd in Hl.
            replace (S (List.length w_pows) - 1)%nat
              with (List.length w_pows) in Hl by lia.
            rewrite w_pows_length in Hl.
            unfold monic in Hm. rewrite Hm in Hl. exact Hl. }
          rewrite Hpl. reflexivity.
        + rewrite coef_xn1_high by lia.
          rewrite (coef_ge_pdeg (prod_lin w_pows))
            by (rewrite Hd, w_pows_length; lia).
          reflexivity.
    Qed.

  End PrimitiveRoot.

End WithPrime.
End Poly.
