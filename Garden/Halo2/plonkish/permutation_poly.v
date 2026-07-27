(** * The permutation argument: all-challenge product rules ↔ σ-invariance.

    The permutation conjunct of the deployed verifier
    ([plonk/permutation/verifier.rs], [Evaluated::expressions]) checks four
    families of gated equations on the evaluation domain, per chunk of
    [chunk_len = cs.degree() - 2] permutation columns with one running
    product [Z_a] each:

    - boot ([l_0 * (1 - z_0) = 0], first chunk only);
    - the main product rule
      [(1 - (l_last + l_blind)) *
         (z_a(ωX) * Π (v + β s + γ) - z_a(X) * Π (v + β δ^i X + γ)) = 0],
      where [s] is the σ label of the cell and [δ^i X] its own label
      ([i] the global column index, realized as the chunk offset
      [chunk_index * chunk_len] plus the per-column step);
    - chunk chaining ([l_0 * (z_a - z_{a-1}(ω^{-(bf+1)} X)) = 0], the
      reference row is the [l_last] spare row);
    - the boolean rule ([l_last * (z_l² - z_l) = 0], last chunk only).

    This file proves the all-challenge reading of those rules equivalent to
    grid invariance under the permutation, generically over the label
    assignment: cells are [Sigma.cell]s, [g] the grid values, [lbl] an
    injective labeling (instantiated by the coset labels [δ^i ω^j]), and
    [sigma] the permutation ([Sigma.perm] of a closed assembly, so the
    conclusion is [sigma.v]'s [grid_invariant] verbatim).

    [permutation_sound]: if for every β, γ some running products satisfy
    the four rules on the domain, then every usable cell carries the value
    of its σ-image.  The proof telescopes the running products over the
    usable rows and across chunks into one total identity
    [iprod = 0 ∨ iprod = sprod] (the boolean rule's zero escape is the
    [0] branch); the escape is then eliminated per fixed β by the
    univariate root bound in γ ([Poly.zero_of_roots] on the difference of
    the two monic factor products — a nonzero difference cannot vanish at
    [N + 1] points avoiding the [N] roots of [iprod]); finally each σ-side
    factor is matched to an identity-side factor by evaluating at its root
    and choosing a β avoiding the ≤ N spurious solutions, and label
    injectivity turns the matching into cell equality.  No polynomial
    factorization theory is used: only evaluation, cancellation by a
    nonzero factor, and the root bound.

    [permutation_complete]: a σ-invariant grid satisfies the rules at
    every challenge where no factor vanishes (the honest prover's running
    products need the inverse of the total factor product; at a vanishing
    challenge the boot and product rules are jointly unsatisfiable, which
    is why the completeness direction excludes exactly those challenges).
    The running products are exhibited division-free as
    [prefix(identity side) * suffix(σ side) * total⁻¹], so the row
    recurrence holds identically and only the endpoints use invariance. *)

Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Lists.List.
Require Import Stdlib.Sorting.Permutation.
Require Import Stdlib.micromega.Lia.
Require Import Garden.Field.Field.
Require Import Garden.Field.Div.
Require Import Garden.Field.Lemmas.
Require Import Garden.Halo2.lemmas.
Require Import Garden.Halo2.main.
Require Import Garden.Halo2.serialize.
Require Import Garden.Halo2.plonkish.main.
Require Import Garden.Halo2.plonkish.sigma.
Require Import Garden.Halo2.plonkish.poly.

Import ListNotations.
Import Plonkish.
Global Open Scope Z_scope.

Module PermutationPoly.

(** ** Chunking a column list

    [chunk_list k l] splits [l] into consecutive pieces of size [k] (the
    last piece possibly shorter), mirroring Rust's [slice::chunks] used on
    the permutation columns. *)

Fixpoint chunk_go {A : Type} (fuel k : nat) (l : list A) : list (list A) :=
  match l with
  | [] => []
  | _ :: _ =>
      match fuel with
      | O => [l]
      | S fuel => List.firstn k l :: chunk_go fuel k (List.skipn k l)
      end
  end.

Definition chunk_list {A : Type} (k : nat) (l : list A) : list (list A) :=
  chunk_go (List.length l) k l.

Lemma chunk_go_concat {A : Type} (fuel k : nat) (l : list A) :
  List.concat (chunk_go fuel k l) = l.
Proof.
  revert l. induction fuel as [| fuel IH]; intros l; destruct l as [| x l'];
    cbn; try reflexivity.
  - rewrite app_nil_r. reflexivity.
  - rewrite IH. apply firstn_skipn.
Qed.

Lemma chunk_list_concat {A : Type} (k : nat) (l : list A) :
  List.concat (chunk_list k l) = l.
Proof. apply chunk_go_concat. Qed.

Lemma chunk_go_nonempty {A : Type} (fuel k : nat) (l : list A) :
  (0 < k)%nat -> forall ch, In ch (chunk_go fuel k l) -> ch <> [].
Proof.
  intro Hk. revert l. induction fuel as [| fuel IH]; intros l ch Hin;
    destruct l as [| x l']; cbn in Hin; try (destruct Hin; fail).
  - destruct Hin as [Heq | []]. rewrite <- Heq. discriminate.
  - destruct Hin as [Heq | Hin].
    + rewrite <- Heq. destruct k; [lia |]. cbn. discriminate.
    + exact (IH _ _ Hin).
Qed.

(** ** Positional surgery on lists *)

Lemma firstn_snoc {A : Type} (l : list A) (a : nat) (x : A) :
  List.nth_error l a = Some x ->
  List.firstn (S a) l = List.firstn a l ++ [x].
Proof.
  revert l. induction a as [| a IH]; intros l Hx; destruct l as [| y l'];
    cbn in *; try discriminate.
  - injection Hx as ->. reflexivity.
  - f_equal. apply IH. exact Hx.
Qed.

Lemma skipn_cons_nth {A : Type} (l : list A) (a : nat) (x : A) :
  List.nth_error l a = Some x ->
  List.skipn a l = x :: List.skipn (S a) l.
Proof.
  revert l. induction a as [| a IH]; intros l Hx; destruct l as [| y l'];
    cbn in *; try discriminate.
  - injection Hx as ->. reflexivity.
  - apply IH. exact Hx.
Qed.

(** ** A repetition-free battery for nested enumerations *)

Lemma NoDup_app_intro {A : Type} (l1 l2 : list A) :
  NoDup l1 -> NoDup l2 -> (forall x, In x l1 -> ~ In x l2) ->
  NoDup (l1 ++ l2).
Proof.
  induction l1 as [| a l1 IH]; cbn; intros H1 H2 Hd; [exact H2 |].
  inversion H1; subst. constructor.
  - intro Hin. apply in_app_iff in Hin.
    destruct Hin as [Hin | Hin]; [contradiction |].
    exact (Hd a (or_introl eq_refl) Hin).
  - apply IH; [assumption | assumption |].
    intros x Hx. apply Hd. right. exact Hx.
Qed.

Lemma NoDup_app_inv {A : Type} (l1 l2 : list A) :
  NoDup (l1 ++ l2) ->
  NoDup l1 /\ NoDup l2 /\ (forall x, In x l1 -> ~ In x l2).
Proof.
  induction l1 as [| a l1 IH]; cbn; intro Hnd.
  - split; [constructor |]. split; [exact Hnd |]. intros x [].
  - inversion Hnd as [| ? ? Hnotin Hnd']; subst.
    destruct (IH Hnd') as [H1 [H2 Hd]].
    split; [| split; [exact H2 |]].
    + constructor; [| exact H1].
      intro Hin. apply Hnotin. apply in_app_iff. left. exact Hin.
    + intros x [-> | Hx].
      * intro Hin2. apply Hnotin. apply in_app_iff. right. exact Hin2.
      * exact (Hd x Hx).
Qed.

(** Groups indexed by a repetition-free list, every element naming its
    group through a tag function. *)
Lemma NoDup_flat_map_tag {A B : Type} (f : A -> list B) (tag : B -> A)
    (l : list A) :
  NoDup l ->
  (forall x, In x l -> NoDup (f x)) ->
  (forall x b, In x l -> In b (f x) -> tag b = x) ->
  NoDup (List.flat_map f l).
Proof.
  induction l as [| a l IH]; cbn; intros Hnd Hf Ht; [constructor |].
  inversion Hnd; subst.
  apply NoDup_app_intro.
  - apply Hf. left. reflexivity.
  - apply IH; [assumption | |].
    + intros x Hx. apply Hf. right. exact Hx.
    + intros x b Hx Hb. apply Ht; [right; exact Hx | exact Hb].
  - intros b Hba Hbl.
    apply in_flat_map in Hbl. destruct Hbl as [y [Hy Hby]].
    assert (Hta : tag b = a) by (apply Ht; [left; reflexivity | exact Hba]).
    assert (Hty : tag b = y) by (apply Ht; [right; exact Hy | exact Hby]).
    rewrite Hta in Hty. subst y. contradiction.
Qed.

(** Groups with pairwise-disjoint images over a repetition-free index. *)
Lemma NoDup_flat_map_disjoint {A B : Type} (f : A -> list B) (l : list A) :
  NoDup l ->
  (forall x, In x l -> NoDup (f x)) ->
  (forall x y b, In x l -> In y l -> In b (f x) -> In b (f y) -> x = y) ->
  NoDup (List.flat_map f l).
Proof.
  induction l as [| a l IH]; cbn; intros Hnd Hf Hdisj; [constructor |].
  inversion Hnd; subst.
  apply NoDup_app_intro.
  - apply Hf. left. reflexivity.
  - apply IH; [assumption | |].
    + intros x Hx. apply Hf. right. exact Hx.
    + intros x y b Hx Hy Hbx Hby.
      apply (Hdisj x y b); [right; exact Hx | right; exact Hy | exact Hbx | exact Hby].
  - intros b Hba Hbl.
    apply in_flat_map in Hbl. destruct Hbl as [y [Hy Hby]].
    assert (a = y)
      by (apply (Hdisj a y b);
          [left; reflexivity | right; exact Hy | exact Hba | exact Hby]).
    subst y. contradiction.
Qed.

Lemma NoDup_concat_member {A : Type} (ll : list (list A)) (l : list A) :
  NoDup (List.concat ll) -> In l ll -> NoDup l.
Proof.
  induction ll as [| h t IH]; cbn; intros Hnd Hin; [destruct Hin |].
  apply NoDup_app_inv in Hnd. destruct Hnd as [Hh [Ht _]].
  destruct Hin as [-> | Hin]; [exact Hh | exact (IH Ht Hin)].
Qed.

Lemma NoDup_concat_disjoint {A : Type} (ll : list (list A))
    (l1 l2 : list A) (x : A) :
  NoDup (List.concat ll) -> In l1 ll -> In l2 ll ->
  In x l1 -> In x l2 -> l1 = l2.
Proof.
  induction ll as [| h t IH]; cbn; intros Hnd H1 H2 Hx1 Hx2; [destruct H1 |].
  apply NoDup_app_inv in Hnd. destruct Hnd as [Hh [Ht Hd]].
  destruct H1 as [-> | H1]; destruct H2 as [-> | H2].
  - reflexivity.
  - exfalso. apply (Hd x Hx1). apply in_concat. eauto.
  - exfalso. apply (Hd x Hx2). apply in_concat. eauto.
  - exact (IH Ht H1 H2 Hx1 Hx2).
Qed.

Lemma NoDup_pieces {A : Type} (ll : list (list A)) :
  NoDup (List.concat ll) -> (forall l, In l ll -> l <> []) -> NoDup ll.
Proof.
  induction ll as [| h t IH]; cbn; intros Hnd Hne; [constructor |].
  apply NoDup_app_inv in Hnd. destruct Hnd as [Hh [Ht Hd]].
  constructor.
  - intro Hin.
    assert (Hne' : h <> []) by (apply Hne; left; reflexivity).
    destruct h as [| x h']; [congruence |].
    apply (Hd x (or_introl eq_refl)). apply in_concat.
    exists (x :: h'). split; [exact Hin | left; reflexivity].
  - apply IH; [exact Ht |]. intros l Hl. apply Hne. right. exact Hl.
Qed.

Lemma NoDup_map_in {A B : Type} (f : A -> B) (l : list A) :
  NoDup l -> (forall x y, In x l -> In y l -> f x = f y -> x = y) ->
  NoDup (List.map f l).
Proof.
  induction l as [| a l IH]; cbn; intros Hnd Hinj; [constructor |].
  inversion Hnd; subst. constructor.
  - intro Hin. apply in_map_iff in Hin. destruct Hin as [y [Hfy Hy]].
    assert (y = a)
      by (apply Hinj; [right; exact Hy | left; reflexivity | exact Hfy]).
    subst y. contradiction.
  - apply IH; [assumption |].
    intros x y Hx Hy. apply Hinj; right; assumption.
Qed.

Section WithPrime.
  Context {p : Z} `{Prime p}.

  Local Notation peval := (Poly.eval (p := p)).
  Local Notation prod_lin := (Poly.prod_lin (p := p)).
  Local Notation psub := (Poly.psub (p := p)).
  Local Notation pdeg := (Poly.pdeg (p := p)).
  Local Notation pnorm := (Poly.norm (p := p)).

  (** ** Field products of value lists *)

  Definition fprod (l : list Z) : Z := List.fold_right BinOp.mul 1 l.

  Lemma fprod_cons (x : Z) (l : list Z) :
    fprod (x :: l) = BinOp.mul x (fprod l).
  Proof. reflexivity. Qed.

  Lemma fmul_canonical (x y : Z) : BinOp.mul x y mod p = BinOp.mul x y.
  Proof. unfold BinOp.mul. apply Zmod_mod. Qed.

  Lemma fsub_canonical (x y : Z) : BinOp.sub x y mod p = BinOp.sub x y.
  Proof. unfold BinOp.sub. apply Zmod_mod. Qed.

  Lemma fmul_1_l (x : Z) : BinOp.mul 1 x = x mod p.
  Proof. unfold BinOp.mul. rewrite Z.mul_1_l. reflexivity. Qed.

  Lemma fmul_0_l (x : Z) : BinOp.mul 0 x = 0.
  Proof. unfold BinOp.mul. rewrite Z.mul_0_l. apply Zmod_0_l. Qed.

  Lemma fmul_comm (x y : Z) : BinOp.mul x y = BinOp.mul y x.
  Proof. unfold BinOp.mul. rewrite Z.mul_comm. reflexivity. Qed.

  Lemma fmul_mod_l (x x' y : Z) :
    x mod p = x' mod p -> BinOp.mul x y = BinOp.mul x' y.
  Proof.
    intro Hx. unfold BinOp.mul.
    rewrite <- Zmult_mod_idemp_l, Hx, Zmult_mod_idemp_l. reflexivity.
  Qed.

  Lemma fmul_mod_r (x y y' : Z) :
    y mod p = y' mod p -> BinOp.mul x y = BinOp.mul x y'.
  Proof.
    intro Hy. unfold BinOp.mul.
    rewrite <- Zmult_mod_idemp_r, Hy, Zmult_mod_idemp_r. reflexivity.
  Qed.

  Lemma fmul_inv_r (x : Z) :
    x mod p = x -> x <> 0 -> BinOp.mul x (mod_inverse x p) = 1.
  Proof.
    intros Hc Hnz.
    rewrite fmul_comm. apply mod_inverse_mul_prime.
    rewrite Hc. exact Hnz.
  Qed.

  Lemma fprod_canonical (l : list Z) : fprod l mod p = fprod l.
  Proof.
    destruct l as [| x l'].
    - cbn. apply Z.mod_1_l. exact (prime_range (p := p)).
    - rewrite fprod_cons. apply fmul_canonical.
  Qed.

  Lemma fprod_app (l1 l2 : list Z) :
    fprod (l1 ++ l2) = BinOp.mul (fprod l1) (fprod l2).
  Proof.
    induction l1 as [| x l1 IH]; cbn [List.app].
    - change (fprod []) with 1. symmetry.
      rewrite fmul_1_l. apply fprod_canonical.
    - rewrite !fprod_cons, IH. mod_ring_solve.
  Qed.

  Lemma fprod_single (x : Z) : fprod [x] = x mod p.
  Proof.
    rewrite fprod_cons. change (fprod []) with 1.
    unfold BinOp.mul. rewrite Z.mul_1_r. reflexivity.
  Qed.

  Lemma fprod_snoc (l : list Z) (x : Z) :
    fprod (l ++ [x]) = BinOp.mul (fprod l) x.
  Proof.
    rewrite fprod_app, fprod_single.
    apply fmul_mod_r. apply Zmod_mod.
  Qed.

  Lemma fprod_perm (l l' : list Z) :
    Permutation l l' -> fprod l = fprod l'.
  Proof.
    induction 1 as [| x l1 l2 Hp IH | x y l1 | l1 l2 l3 Hp1 IH1 Hp2 IH2].
    - reflexivity.
    - rewrite !fprod_cons, IH. reflexivity.
    - rewrite !fprod_cons. mod_ring_solve.
    - congruence.
  Qed.

  Lemma fprod_map_ext_in {A : Type} (f g : A -> Z) (l : list A) :
    (forall x, In x l -> f x = g x) ->
    fprod (List.map f l) = fprod (List.map g l).
  Proof.
    induction l as [| a l IH]; cbn [List.map]; intro Hfg; [reflexivity |].
    rewrite !fprod_cons, (Hfg a (or_introl eq_refl)), IH;
      [reflexivity | intros x Hx; apply Hfg; right; exact Hx].
  Qed.

  Lemma fprod_map_flat_map {A B : Type} (f : B -> Z) (h : A -> list B)
      (l : list A) :
    fprod (List.map f (List.flat_map h l))
      = fprod (List.map (fun x => fprod (List.map f (h x))) l).
  Proof.
    induction l as [| a l IH]; cbn [List.flat_map List.map]; [reflexivity |].
    rewrite map_app, fprod_app, IH, fprod_cons. reflexivity.
  Qed.

  Lemma fprod_zero_iff (l : list Z) :
    fprod l = 0 <-> exists x, In x l /\ x mod p = 0.
  Proof.
    induction l as [| x l' IH].
    - cbn. split; [lia | intros [x [[] _]]].
    - rewrite fprod_cons, mul_zero_implies_zero.
      unfold UnOp.from. rewrite fprod_canonical.
      split.
      + intros [Hx | Hl].
        * exists x. split; [left; reflexivity | exact Hx].
        * apply IH in Hl. destruct Hl as [y [Hy Hym]].
          exists y. split; [right; exact Hy | exact Hym].
      + intros [y [[-> | Hy] Hym]]; [left; exact Hym |].
        right. apply IH. exists y. split; assumption.
  Qed.

  (** Splitting a mapped product at one position. *)
  Lemma fprod_map_split {A : Type} (f : A -> Z) (l : list A) (a : nat)
      (x : A) :
    List.nth_error l a = Some x ->
    fprod (List.map f l)
      = BinOp.mul
          (BinOp.mul (fprod (List.map f (List.firstn a l))) (f x))
          (fprod (List.map f (List.skipn (S a) l))).
  Proof.
    revert l. induction a as [| a IH]; intros l Hx;
      destruct l as [| y l']; cbn in Hx; try discriminate.
    - injection Hx as ->. cbn [List.firstn List.skipn List.map].
      rewrite fprod_cons. change (fprod []) with 1. mod_ring_solve.
    - rewrite firstn_cons, skipn_cons. cbn [List.map].
      rewrite !fprod_cons, (IH l' Hx). mod_ring_solve.
  Qed.

  (** ** Challenge pools and root-avoiding counting *)

  Definition zpool (m : nat) : list Z := List.map Z.of_nat (List.seq 0 m).

  Lemma zpool_length (m : nat) : List.length (zpool m) = m.
  Proof. unfold zpool. rewrite length_map, length_seq. reflexivity. Qed.

  Lemma zpool_NoDup_mod (m : nat) :
    Z.of_nat m <= p ->
    NoDup (List.map (fun x => x mod p) (zpool m)).
  Proof.
    intro Hm. unfold zpool. rewrite map_map.
    rewrite (map_ext_in (fun x : nat => Z.of_nat x mod p) Z.of_nat).
    - apply NoDup_map_of_nat. apply seq_NoDup.
    - intros a Ha. apply in_seq in Ha. apply Z.mod_small. lia.
  Qed.

  (** Evaluating a product of monic linear factors is the field product of
      the shifted evaluation points. *)
  Lemma eval_prod_lin_fprod (l : list Z) (x : Z) :
    peval (prod_lin l) x = fprod (List.map (fun r => (x - r) mod p) l).
  Proof.
    induction l as [| r l' IH].
    - change (peval (prod_lin []) x) with ((1 + x * 0) mod p).
      rewrite Z.mul_0_r, Z.add_0_r.
      apply Z.mod_1_l. exact (prime_range (p := p)).
    - cbn [Poly.prod_lin List.map].
      rewrite Poly.eval_pmul, Poly.eval_lin, fprod_cons, IH.
      reflexivity.
  Qed.

  Section WithSystem.
    Context (domain : Domain.t).
    Context (Hk : 0 <= domain.(Domain.k)).
    Context (Hbf : 0 <= domain.(Domain.blinding_factors)).
    Context (Hur : 0 <= Domain.usable_rows domain).
    Context (ncols chunk_len : nat).
    Context (Hchunk : (0 < chunk_len)%nat).
    Context (g lbl : Sigma.cell -> Z).
    Context (sigma : Sigma.cell -> Sigma.cell).

    (** ** The cell enumeration, chunked as the verifier chunks columns *)

    Definition un : nat := Z.to_nat (Domain.usable_rows domain).
    Definition nn : nat := Z.to_nat (Domain.n domain).

    Definition col_chunks : list (list nat) :=
      chunk_list chunk_len (List.seq 0 ncols).

    Definition K : nat := List.length col_chunks.

    Definition usable_cell (c : Sigma.cell) : Prop :=
      (fst c < ncols)%nat /\ (snd c < un)%nat.

    Definition space_cell (c : Sigma.cell) : Prop :=
      (fst c < ncols)%nat /\ (snd c < nn)%nat.

    Definition chunk_row_cells (ch : list nat) (j : nat) : list Sigma.cell :=
      List.map (fun i => (i, j)) ch.

    Definition chunk_cells (ch : list nat) : list Sigma.cell :=
      List.flat_map (chunk_row_cells ch) (List.seq 0 un).

    Definition all_cells : list Sigma.cell :=
      List.flat_map chunk_cells col_chunks.

    (** ** The two factor families

        [ifac] is the identity-side factor [v + β·lbl(c) + γ] (the label of
        the cell itself — [δ^i ω^j] at instantiation, [δ^i β X + γ] in the
        verifier); [sfac] carries the σ label [lbl(σ(c))] (the σ-polynomial
        evaluation [s_i(ω^j)]). *)

    Definition ifac (beta gamma : Z) (c : Sigma.cell) : Z :=
      (g c + beta * lbl c + gamma) mod p.

    Definition sfac (beta gamma : Z) (c : Sigma.cell) : Z :=
      (g c + beta * lbl (sigma c) + gamma) mod p.

    Definition irow (beta gamma : Z) (ch : list nat) (j : nat) : Z :=
      fprod (List.map (ifac beta gamma) (chunk_row_cells ch j)).

    Definition srow (beta gamma : Z) (ch : list nat) (j : nat) : Z :=
      fprod (List.map (sfac beta gamma) (chunk_row_cells ch j)).

    Definition icum (beta gamma : Z) (ch : list nat) (m : nat) : Z :=
      fprod (List.map (irow beta gamma ch) (List.seq 0 m)).

    Definition scum (beta gamma : Z) (ch : list nat) (m : nat) : Z :=
      fprod (List.map (srow beta gamma ch) (List.seq 0 m)).

    Definition iprod (beta gamma : Z) : Z :=
      fprod (List.map (ifac beta gamma) all_cells).

    Definition sprod (beta gamma : Z) : Z :=
      fprod (List.map (sfac beta gamma) all_cells).

    (** ** The four product rules

        Pointwise on the domain rows, with the Lagrange selectors read as
        0/1 field values ([Domain.l_0]/[l_last]/[l_blind] at the row) and
        [z_a] the running-product values [j ↦ Z_a(ω^j)].  The shapes
        mirror [permutation/verifier.rs] [Evaluated::expressions]. *)

    Definition sel (b : bool) : Z := if b then 1 else 0.

    Definition active (row : Z) : Z :=
      BinOp.sub 1
        (BinOp.add (sel (Domain.l_last domain row))
          (sel (Domain.l_blind domain row))).

    (** [l_0(X) * (1 - z_0(X)) = 0] *)
    Definition boot_rule (z0 : Z -> Z) : Prop :=
      forall row, 0 <= row < Domain.n domain ->
      BinOp.mul (sel (Domain.l_0 domain row)) (BinOp.sub 1 (z0 row)) = 0.

    (** [(1 - (l_last + l_blind)) *
         (z_a(ωX)·Π(v + β s + γ) - z_a(X)·Π(v + β δ^i X + γ)) = 0] *)
    Definition product_rule (beta gamma : Z) (ch : list nat) (z : Z -> Z)
        : Prop :=
      forall row, 0 <= row < Domain.n domain ->
      BinOp.mul (active row)
        (BinOp.sub
          (BinOp.mul (z (Domain.rot domain row 1))
            (srow beta gamma ch (Z.to_nat row)))
          (BinOp.mul (z row) (irow beta gamma ch (Z.to_nat row))))
      = 0.

    (** [l_0(X) * (z_a(X) - z_(a-1)(ω^(-(bf+1)) X)) = 0] *)
    Definition chain_rule (zp z : Z -> Z) : Prop :=
      forall row, 0 <= row < Domain.n domain ->
      BinOp.mul (sel (Domain.l_0 domain row))
        (BinOp.sub (z row)
          (zp (Domain.rot domain row
            (- (domain.(Domain.blinding_factors) + 1)))))
      = 0.

    (** [l_last(X) * (z_l(X)² - z_l(X)) = 0] *)
    Definition last_rule (z : Z -> Z) : Prop :=
      forall row, 0 <= row < Domain.n domain ->
      BinOp.mul (sel (Domain.l_last domain row))
        (BinOp.sub (BinOp.mul (z row) (z row)) (z row))
      = 0.

    (** The whole conjunct: one running product per chunk, the boot rule on
        the first, chaining between consecutive ones, the boolean rule on
        the last. *)
    Definition permutation_rules (beta gamma : Z) (zs : list (Z -> Z))
        : Prop :=
      List.length zs = K /\
      (forall z0, List.nth_error zs 0 = Some z0 -> boot_rule z0) /\
      (forall a ch z,
        List.nth_error col_chunks a = Some ch ->
        List.nth_error zs a = Some z ->
        product_rule beta gamma ch z) /\
      (forall a zp z,
        (1 <= a)%nat ->
        List.nth_error zs (a - 1) = Some zp ->
        List.nth_error zs a = Some z ->
        chain_rule zp z) /\
      (forall zl, List.nth_error zs (K - 1) = Some zl -> last_rule zl).

    (** ** Domain bookkeeping *)

    Lemma n_pos : 0 < Domain.n domain.
    Proof. unfold Domain.n. apply Z.pow_pos_nonneg; lia. Qed.

    Lemma urows_lt_n : Domain.usable_rows domain < Domain.n domain.
    Proof. unfold Domain.usable_rows. pose proof n_pos. lia. Qed.

    Lemma urows_of_un : Z.of_nat un = Domain.usable_rows domain.
    Proof. unfold un. apply Z2Nat.id. exact Hur. Qed.

    Lemma un_le_nn : (un <= nn)%nat.
    Proof. unfold un, nn. pose proof urows_lt_n. pose proof n_pos. lia. Qed.

    Lemma rot_next (row : Z) :
      0 <= row < Domain.usable_rows domain ->
      Domain.rot domain row 1 = row + 1.
    Proof.
      intros Hrow. unfold Domain.rot. apply Z.mod_small.
      pose proof urows_lt_n. lia.
    Qed.

    (** The chaining reference row: rotation by [-(bf + 1)] from row 0
        lands on the [l_last] spare row [usable_rows]. *)
    Lemma rot_last :
      Domain.rot domain 0 (- (domain.(Domain.blinding_factors) + 1))
        = Domain.usable_rows domain.
    Proof.
      unfold Domain.rot.
      replace (0 + - (domain.(Domain.blinding_factors) + 1))
        with (Domain.usable_rows domain + (-1) * Domain.n domain)
        by (unfold Domain.usable_rows; ring).
      rewrite Z_mod_plus_full. apply Z.mod_small.
      pose proof urows_lt_n. lia.
    Qed.

    (** ** Selector values at the pinned rows *)

    Lemma sel_l0_0 : sel (Domain.l_0 domain 0) = 1.
    Proof. reflexivity. Qed.

    Lemma sel_l0_off (row : Z) :
      row <> 0 -> sel (Domain.l_0 domain row) = 0.
    Proof.
      intro Hrow. unfold Domain.l_0.
      replace (row =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hrow).
      reflexivity.
    Qed.

    Lemma sel_llast_at :
      sel (Domain.l_last domain (Domain.usable_rows domain)) = 1.
    Proof. unfold Domain.l_last. rewrite Z.eqb_refl. reflexivity. Qed.

    Lemma sel_llast_off (row : Z) :
      row <> Domain.usable_rows domain -> sel (Domain.l_last domain row) = 0.
    Proof.
      intro Hrow. unfold Domain.l_last.
      replace (row =? Domain.usable_rows domain) with false
        by (symmetry; apply Z.eqb_neq; exact Hrow).
      reflexivity.
    Qed.

    Lemma active_usable (row : Z) :
      0 <= row < Domain.usable_rows domain -> active row = 1.
    Proof.
      intros Hrow. pose proof (prime_range (p := p)).
      unfold active. rewrite sel_llast_off by lia.
      unfold Domain.l_blind.
      replace (Domain.usable_rows domain <? row) with false
        by (symmetry; apply Z.ltb_ge; lia).
      cbn [andb sel].
      unfold BinOp.add. change (0 + 0) with 0. rewrite Zmod_0_l.
      unfold BinOp.sub. change (1 - 0) with 1. apply Z.mod_1_l. lia.
    Qed.

    Lemma active_off (row : Z) :
      Domain.usable_rows domain <= row < Domain.n domain -> active row = 0.
    Proof.
      intros Hrow. pose proof (prime_range (p := p)).
      unfold active.
      destruct (Z.eqb_spec row (Domain.usable_rows domain)) as [Heq | Hne].
      - rewrite Heq, sel_llast_at.
        unfold Domain.l_blind.
        replace (Domain.usable_rows domain <? Domain.usable_rows domain)
          with false by (symmetry; apply Z.ltb_ge; lia).
        cbn [andb sel].
        unfold BinOp.add. change (1 + 0) with 1. rewrite Z.mod_1_l by lia.
        unfold BinOp.sub. change (1 - 1) with 0. apply Zmod_0_l.
      - rewrite sel_llast_off by exact Hne.
        unfold Domain.l_blind.
        replace (Domain.usable_rows domain <? row) with true
          by (symmetry; apply Z.ltb_lt; lia).
        replace (row <? Domain.n domain) with true
          by (symmetry; apply Z.ltb_lt; lia).
        cbn [andb sel].
        unfold BinOp.add. change (0 + 1) with 1. rewrite Z.mod_1_l by lia.
        unfold BinOp.sub. change (1 - 1) with 0. apply Zmod_0_l.
    Qed.

    (** ** Reading the gated equations *)

    Lemma gate_intro (s A B : Z) : A = B -> BinOp.mul s (BinOp.sub A B) = 0.
    Proof.
      intros ->. unfold BinOp.sub. rewrite Z.sub_diag, Zmod_0_l.
      unfold BinOp.mul. rewrite Z.mul_0_r. apply Zmod_0_l.
    Qed.

    Lemma gate_one_elim (A B : Z) :
      A mod p = A -> B mod p = B ->
      BinOp.mul 1 (BinOp.sub A B) = 0 -> A = B.
    Proof.
      intros HA HB Hm. rewrite fmul_1_l, fsub_canonical in Hm.
      apply sub_zero_equiv in Hm. unfold UnOp.from in Hm. congruence.
    Qed.

    Lemma boot_elim (z0 : Z -> Z) : boot_rule z0 -> z0 0 mod p = 1.
    Proof.
      intro Hrule. pose proof (prime_range (p := p)).
      specialize (Hrule 0 (conj (Z.le_refl 0) n_pos)).
      rewrite sel_l0_0, fmul_1_l, fsub_canonical in Hrule.
      apply sub_zero_equiv in Hrule. unfold UnOp.from in Hrule.
      rewrite Z.mod_1_l in Hrule by lia.
      symmetry. exact Hrule.
    Qed.

    Lemma product_elim (beta gamma : Z) (ch : list nat) (z : Z -> Z) :
      product_rule beta gamma ch z ->
      forall j, (j < un)%nat ->
      BinOp.mul (z (Z.of_nat j + 1)) (srow beta gamma ch j)
        = BinOp.mul (z (Z.of_nat j)) (irow beta gamma ch j).
    Proof.
      intros Hrule j Hj.
      assert (Hju : Z.of_nat j < Domain.usable_rows domain).
      { rewrite <- urows_of_un. lia. }
      assert (Hrow : 0 <= Z.of_nat j < Domain.n domain)
        by (pose proof urows_lt_n; lia).
      specialize (Hrule (Z.of_nat j) Hrow).
      rewrite active_usable in Hrule by lia.
      rewrite rot_next in Hrule by lia.
      rewrite Nat2Z.id in Hrule.
      exact (gate_one_elim _ _ (fmul_canonical _ _) (fmul_canonical _ _) Hrule).
    Qed.

    Lemma chain_elim (zp z : Z -> Z) :
      chain_rule zp z ->
      z 0 mod p = zp (Domain.usable_rows domain) mod p.
    Proof.
      intro Hrule.
      specialize (Hrule 0 (conj (Z.le_refl 0) n_pos)).
      rewrite sel_l0_0, rot_last, fmul_1_l, fsub_canonical in Hrule.
      apply sub_zero_equiv in Hrule. unfold UnOp.from in Hrule.
      exact Hrule.
    Qed.

    Lemma last_elim (z : Z -> Z) :
      last_rule z ->
      z (Domain.usable_rows domain) mod p = 0 \/
      z (Domain.usable_rows domain) mod p = 1.
    Proof.
      intro Hrule. pose proof (prime_range (p := p)).
      specialize (Hrule (Domain.usable_rows domain) (conj Hur urows_lt_n)).
      rewrite sel_llast_at, fmul_1_l, fsub_canonical in Hrule.
      apply sub_zero_equiv in Hrule. unfold UnOp.from in Hrule.
      rewrite fmul_canonical in Hrule.
      set (zu := z (Domain.usable_rows domain)) in *.
      assert (Hfac : BinOp.mul zu (BinOp.sub zu 1) = 0).
      { unfold BinOp.mul, BinOp.sub in *.
        rewrite Zmult_mod_idemp_r.
        replace (zu * (zu - 1)) with (zu * zu - zu) by ring.
        rewrite Zminus_mod, Hrule, Z.sub_diag. apply Zmod_0_l. }
      apply mul_zero_implies_zero in Hfac.
      destruct Hfac as [Hz | Hz]; unfold UnOp.from in Hz.
      - left. exact Hz.
      - right. rewrite fsub_canonical in Hz.
        apply sub_zero_equiv in Hz. unfold UnOp.from in Hz.
        rewrite Z.mod_1_l in Hz by lia. exact Hz.
    Qed.

    (** ** Telescoping the running products *)

    Lemma icum_S (beta gamma : Z) (ch : list nat) (m : nat) :
      icum beta gamma ch (S m)
        = BinOp.mul (icum beta gamma ch m) (irow beta gamma ch m).
    Proof.
      unfold icum. rewrite seq_S, Nat.add_0_l, map_app.
      cbn [List.map]. apply fprod_snoc.
    Qed.

    Lemma scum_S (beta gamma : Z) (ch : list nat) (m : nat) :
      scum beta gamma ch (S m)
        = BinOp.mul (scum beta gamma ch m) (srow beta gamma ch m).
    Proof.
      unfold scum. rewrite seq_S, Nat.add_0_l, map_app.
      cbn [List.map]. apply fprod_snoc.
    Qed.

    (** One chunk, rows [0..m): the row recurrence telescopes into
        [z(ω^m) · Π σ-side = z(1) · Π id-side]. *)
    Lemma chunk_telescope (beta gamma : Z) (ch : list nat) (z : Z -> Z)
        (Hstep : forall j, (j < un)%nat ->
          BinOp.mul (z (Z.of_nat j + 1)) (srow beta gamma ch j)
            = BinOp.mul (z (Z.of_nat j)) (irow beta gamma ch j)) :
      forall m, (m <= un)%nat ->
      BinOp.mul (z (Z.of_nat m)) (scum beta gamma ch m)
        = BinOp.mul (z 0) (icum beta gamma ch m).
    Proof.
      induction m as [| m IH]; intro Hm; [reflexivity |].
      rewrite icum_S, scum_S.
      replace (Z.of_nat (S m)) with (Z.of_nat m + 1) by lia.
      transitivity
        (BinOp.mul (BinOp.mul (z (Z.of_nat m + 1)) (srow beta gamma ch m))
          (scum beta gamma ch m));
        [mod_ring_solve |].
      rewrite (Hstep m ltac:(lia)).
      transitivity
        (BinOp.mul (BinOp.mul (z (Z.of_nat m)) (scum beta gamma ch m))
          (irow beta gamma ch m));
        [mod_ring_solve |].
      rewrite IH by lia. mod_ring_solve.
    Qed.

    (** Chunks [0..b): the per-chunk telescopes compose through the boot
        and chaining rules into one identity for the [b-1]-th running
        product at the spare row. *)
    Lemma chunks_telescope (beta gamma : Z) (zs : list (Z -> Z))
        (Hlen : List.length zs = K)
        (Hboot : forall z0, List.nth_error zs 0 = Some z0 -> boot_rule z0)
        (Hprod : forall a ch z,
          List.nth_error col_chunks a = Some ch ->
          List.nth_error zs a = Some z ->
          product_rule beta gamma ch z)
        (Hchain : forall a zp z,
          (1 <= a)%nat ->
          List.nth_error zs (a - 1) = Some zp ->
          List.nth_error zs a = Some z ->
          chain_rule zp z) :
      forall b, (1 <= b <= K)%nat ->
      forall z, List.nth_error zs (b - 1) = Some z ->
      BinOp.mul (z (Domain.usable_rows domain))
        (fprod (List.map (fun ch => scum beta gamma ch un)
          (List.firstn b col_chunks)))
      = fprod (List.map (fun ch => icum beta gamma ch un)
          (List.firstn b col_chunks)).
    Proof.
      induction b as [| b IH]; intros Hb z Hz; [lia |].
      replace (S b - 1)%nat with b in Hz by lia.
      assert (Hbe : (b < K)%nat) by lia.
      assert (Hch : List.nth_error col_chunks b
        = Some (List.nth b col_chunks [])).
      { apply nth_error_nth'. exact Hbe. }
      assert (Hstep := product_elim beta gamma (List.nth b col_chunks []) z
        (Hprod b _ z Hch Hz)).
      assert (Hct := chunk_telescope beta gamma (List.nth b col_chunks []) z
        Hstep un (Nat.le_refl un)).
      rewrite urows_of_un in Hct.
      rewrite (firstn_snoc col_chunks b _ Hch).
      rewrite !map_app. cbn [List.map]. rewrite !fprod_snoc.
      destruct b as [| b'].
      - cbn [List.firstn List.map]. change (fprod []) with 1.
        pose proof (boot_elim z (Hboot z Hz)) as Hb1.
        transitivity
          (BinOp.mul (z (Domain.usable_rows domain))
            (scum beta gamma (List.nth 0 col_chunks []) un));
          [mod_ring_solve |].
        rewrite Hct.
        apply fmul_mod_l.
        rewrite Z.mod_1_l by exact (prime_range (p := p)).
        exact Hb1.
      - set (bb := S b') in *.
        assert (Hzp : exists zp, List.nth_error zs (bb - 1) = Some zp).
        { destruct (List.nth_error zs (bb - 1)) as [zp |] eqn:E; [eauto |].
          apply nth_error_None in E. lia. }
        destruct Hzp as [zp Hzp].
        assert (IH' := IH ltac:(lia) zp Hzp).
        pose proof (chain_elim zp z (Hchain bb zp z ltac:(lia) Hzp Hz)) as Hcc.
        transitivity
          (BinOp.mul
            (BinOp.mul (z (Domain.usable_rows domain))
              (scum beta gamma (List.nth bb col_chunks []) un))
            (fprod (List.map (fun ch => scum beta gamma ch un)
              (List.firstn bb col_chunks))));
          [mod_ring_solve |].
        rewrite Hct.
        rewrite (fmul_mod_l (z 0) (zp (Domain.usable_rows domain)) _ Hcc).
        transitivity
          (BinOp.mul
            (BinOp.mul (zp (Domain.usable_rows domain))
              (fprod (List.map (fun ch => scum beta gamma ch un)
                (List.firstn bb col_chunks))))
            (icum beta gamma (List.nth bb col_chunks []) un));
          [mod_ring_solve |].
        rewrite IH'. reflexivity.
    Qed.

    (** ** The total products, chunk-grouped *)

    Lemma firstn_K : List.firstn K col_chunks = col_chunks.
    Proof. apply firstn_all. Qed.

    Lemma iprod_map (beta gamma : Z) :
      iprod beta gamma
        = fprod (List.map (fun ch => icum beta gamma ch un) col_chunks).
    Proof.
      unfold iprod, all_cells. rewrite fprod_map_flat_map.
      apply fprod_map_ext_in. intros ch _.
      unfold chunk_cells. rewrite fprod_map_flat_map.
      unfold icum. apply fprod_map_ext_in. intros j _. reflexivity.
    Qed.

    Lemma sprod_map (beta gamma : Z) :
      sprod beta gamma
        = fprod (List.map (fun ch => scum beta gamma ch un) col_chunks).
    Proof.
      unfold sprod, all_cells. rewrite fprod_map_flat_map.
      apply fprod_map_ext_in. intros ch _.
      unfold chunk_cells. rewrite fprod_map_flat_map.
      unfold scum. apply fprod_map_ext_in. intros j _. reflexivity.
    Qed.

    (** The rules at one challenge pair collapse to the total identity:
        the identity-side product is the σ-side product, or zero (the
        boolean rule's escape branch). *)
    Lemma rules_products (beta gamma : Z) :
      (exists zs, permutation_rules beta gamma zs) ->
      iprod beta gamma = 0 \/ iprod beta gamma = sprod beta gamma.
    Proof.
      intros [zs [Hlen [Hboot [Hprod [Hchain Hlast]]]]].
      destruct (Nat.eq_dec K 0) as [HK0 | HK0].
      - right.
        assert (Hnil : col_chunks = []) by (apply length_zero_iff_nil; exact HK0).
        unfold iprod, sprod, all_cells. rewrite Hnil. reflexivity.
      - assert (HK : (1 <= K)%nat) by lia.
        assert (Hex : exists zl, List.nth_error zs (K - 1) = Some zl).
        { destruct (List.nth_error zs (K - 1)) as [zl |] eqn:E; [eauto |].
          apply nth_error_None in E. lia. }
        destruct Hex as [zl Hzl].
        pose proof (chunks_telescope beta gamma zs Hlen Hboot Hprod Hchain K
          (conj HK (Nat.le_refl K)) zl Hzl) as Htel.
        rewrite firstn_K in Htel.
        pose proof (last_elim zl (Hlast zl Hzl)) as [Hz0 | Hz1].
        + left. rewrite iprod_map, <- Htel.
          rewrite (fmul_mod_l (zl (Domain.usable_rows domain)) 0)
            by (rewrite Hz0, Zmod_0_l; reflexivity).
          apply fmul_0_l.
        + right. rewrite iprod_map, sprod_map, <- Htel.
          rewrite (fmul_mod_l (zl (Domain.usable_rows domain)) 1)
            by (rewrite Z.mod_1_l by exact (prime_range (p := p)); exact Hz1).
          rewrite fmul_1_l. apply fprod_canonical.
    Qed.

    (** ** The cell enumeration covers exactly the usable cells *)

    Lemma in_all_cells (c : Sigma.cell) : In c all_cells <-> usable_cell c.
    Proof.
      unfold all_cells, usable_cell. split.
      - intro Hin. apply in_flat_map in Hin. destruct Hin as [ch [Hch Hin]].
        unfold chunk_cells in Hin. apply in_flat_map in Hin.
        destruct Hin as [j [Hj Hin]].
        unfold chunk_row_cells in Hin. apply in_map_iff in Hin.
        destruct Hin as [i [Hic Hiin]].
        subst c. cbn [fst snd]. apply in_seq in Hj.
        split; [| lia].
        assert (Hcc : In i (List.concat col_chunks))
          by (apply in_concat; exists ch; split; assumption).
        unfold col_chunks in Hcc. rewrite chunk_list_concat in Hcc.
        apply in_seq in Hcc. lia.
      - intros [Hi Hj]. destruct c as [i j]. cbn [fst snd] in *.
        assert (Hcc : In i (List.concat col_chunks)).
        { unfold col_chunks. rewrite chunk_list_concat. apply in_seq. lia. }
        apply in_concat in Hcc. destruct Hcc as [ch [Hch Hiin]].
        apply in_flat_map. exists ch. split; [exact Hch |].
        unfold chunk_cells. apply in_flat_map. exists j.
        split; [apply in_seq; lia |].
        unfold chunk_row_cells. apply in_map_iff. exists i.
        split; [reflexivity | exact Hiin].
    Qed.

    Lemma usable_cell_space (c : Sigma.cell) : usable_cell c -> space_cell c.
    Proof.
      intros [H1 H2]. split; [exact H1 |]. pose proof un_le_nn. lia.
    Qed.

    (** ** The factor products as evaluations of monic linear products

        In the variable γ, at a fixed β, the identity-side product is the
        evaluation of [Π (X - r)] over the roots [-(v + β·lbl)], and
        likewise for the σ side. *)

    Definition iroots (beta : Z) : list Z :=
      List.map (fun c => - (g c + beta * lbl c)) all_cells.

    Definition sroots (beta : Z) : list Z :=
      List.map (fun c => - (g c + beta * lbl (sigma c))) all_cells.

    Lemma iroots_length (beta : Z) :
      List.length (iroots beta) = List.length all_cells.
    Proof. apply length_map. Qed.

    Lemma sroots_length (beta : Z) :
      List.length (sroots beta) = List.length all_cells.
    Proof. apply length_map. Qed.

    Lemma iprod_eval (beta gamma : Z) :
      iprod beta gamma = peval (prod_lin (iroots beta)) gamma.
    Proof.
      unfold iprod, iroots. rewrite eval_prod_lin_fprod, map_map.
      apply fprod_map_ext_in. intros c _. unfold ifac. f_equal. ring.
    Qed.

    Lemma sprod_eval (beta gamma : Z) :
      sprod beta gamma = peval (prod_lin (sroots beta)) gamma.
    Proof.
      unfold sprod, sroots. rewrite eval_prod_lin_fprod, map_map.
      apply fprod_map_ext_in. intros c _. unfold sfac. f_equal. ring.
    Qed.

    Lemma prod_lin_root_of_zero (l : list Z) (x : Z) :
      peval (prod_lin l) x = 0 ->
      exists r, In r l /\ (x - r) mod p = 0.
    Proof.
      rewrite eval_prod_lin_fprod. intro Hz.
      apply fprod_zero_iff in Hz. destruct Hz as [v [Hv Hvm]].
      apply in_map_iff in Hv. destruct Hv as [r [Hvr Hr]]. subst v.
      rewrite Zmod_mod in Hvm.
      exists r. split; [exact Hr | exact Hvm].
    Qed.

    (** ** Eliminating the zero escape: the products agree at every
        challenge

        At a fixed β, the difference of the two monic products (degree
        [N = #cells] in γ) vanishes at every pool point avoiding the [N]
        roots of the identity-side product — at least [N + 1] of the
        [2N + 1] pool points — so it is the zero polynomial. *)

    (** ** The product identity from a bounded challenge pool

        The pool-indexed form of [products_eq_all] at a fixed [β]: a
        [γ]-pool of [2·N + 1] residues that are pairwise distinct mod [p]
        already forces [iprod β = sprod β] everywhere, since more than [N]
        of its members avoid the [N] roots of the input factor. *)
    (** At a fixed [β], the total-product disjunction on a [γ] pool of
        [2·N + 1] distinct residues forces the total identity at every
        [γ] — the generalized [products_eq_all]: at least
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
      { pose proof (Poly.filter_avoid_length (p := p)
          (iroots beta) gammas Hnd) as Hfl.
        unfold good.
        rewrite (iroots_length beta) in Hfl.
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
          apply prod_lin_root_of_zero in Hz.
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
          rewrite <- (iprod_eval beta x).
          exact H0.
        - rewrite Poly.eval_psub.
          rewrite <- (iprod_eval beta x).
          rewrite <- (sprod_eval beta x).
          rewrite Heqx, Z.sub_diag.
          apply Zmod_0_l. }
      assert (Hzero : Poly.norm (p := p)
        (Poly.psub (p := p) (Poly.prod_lin (p := p) (iroots beta))
          (Poly.prod_lin (p := p) (sroots beta))) = []).
      { apply (Poly.zero_of_roots (p := p) _ good).
        - unfold Poly.NoDupP, good.
          apply NoDup_map_filter.
          exact Hnd.
        - rewrite List.Forall_forall. exact Hroots.
        - pose proof (Poly.pdeg_psub_le (p := p)
            (Poly.prod_lin (p := p) (iroots beta))
            (Poly.prod_lin (p := p) (sroots beta))) as Hle.
          pose proof (proj2 (Poly.prod_lin_monic (p := p) (iroots beta)))
            as Hd1.
          pose proof (proj2 (Poly.prod_lin_monic (p := p) (sroots beta)))
            as Hd2.
          rewrite (iroots_length beta) in Hd1.
          rewrite (sroots_length beta) in Hd2.
          lia. }
      rewrite (iprod_eval beta gamma).
      rewrite (sprod_eval beta gamma).
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

    Lemma products_eq_all
        (Hbig : 2 * Z.of_nat (List.length all_cells) + 1 <= p)
        (Hor : forall beta gamma,
          iprod beta gamma = 0 \/ iprod beta gamma = sprod beta gamma) :
      forall beta gamma, iprod beta gamma = sprod beta gamma.
    Proof.
      intros beta gamma.
      apply (products_eq_of_pool beta (zpool (2 * List.length all_cells + 1))).
      - unfold Poly.NoDupP. apply zpool_NoDup_mod. lia.
      - rewrite zpool_length. lia.
      - intros gamma0 _. apply Hor.
    Qed.

    (** ** Matching each σ-side factor to an identity-side factor

        For a cell [c], evaluating at the root of its σ-side factor kills
        the σ-side product, hence the identity-side product; the vanishing
        identity factor names a cell [d] with
        [(g d - g c) + β·(lbl d - lbl (σ c)) ≡ 0].  For each [d] with
        [lbl d ≢ lbl (σ c)] that equation pins β to a single residue, so a
        pool of [N + 1] challenges contains a β avoiding all of them; at
        that β the matching cell agrees with [c] in both components. *)

    (** ** The cell match from bounded challenge pools

        The pool-indexed form of [match_cell]: a [β]-pool of [N + 1]
        residues, each carrying a [γ]-pool that forces the product
        identity, already matches every cell.  Only the pool sizes matter,
        so the counting layer supplies explicit finite pools while
        [match_cell] instantiates them with [zpool]. *)
    (** The generalized [match_cell]: a [β] pool of
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
      pose proof (prime_range) as Hp1.
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
      { apply Poly.pool_avoid_pick; [exact Hnb |].
        unfold bad.
        rewrite List.length_map.
        lia. }
      destruct Hpick as (bstar & Hbin & Havoid).
      assert (Hsfac0 : sfac bstar
        (- (g c + bstar * lbl (sigma c))) c = 0).
      { unfold sfac.
        replace (g c + bstar * lbl (sigma c)
          + - (g c + bstar * lbl (sigma c))) with 0 by ring.
        apply Zmod_0_l. }
      assert (Hip0 : iprod bstar (- (g c + bstar * lbl (sigma c))) = 0).
      { rewrite (Heq bstar Hbin).
        unfold sprod.
        apply fprod_zero_iff.
        exists (sfac bstar
          (- (g c + bstar * lbl (sigma c))) c).
        split.
        - apply List.in_map. exact Hc.
        - rewrite Hsfac0. apply Zmod_0_l. }
      unfold iprod in Hip0.
      apply fprod_zero_iff in Hip0.
      destruct Hip0 as [v [Hvin Hvm]].
      apply List.in_map_iff in Hvin.
      destruct Hvin as [d [Hvd Hdin]].
      subst v.
      assert (Hifac0 : ifac bstar
        (- (g c + bstar * lbl (sigma c))) d = 0).
      { unfold ifac in *.
        rewrite Zmod_mod in Hvm.
        exact Hvm. }
      assert (Hkey : ((g d - g c)
        + bstar * (lbl d - lbl (sigma c))) mod p = 0).
      { rewrite <- Hifac0.
        unfold ifac.
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
        pose proof (mod_inverse_mul_prime
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

    Lemma match_cell
        (Hbig : 2 * Z.of_nat (List.length all_cells) + 1 <= p)
        (Hor : forall beta gamma,
          iprod beta gamma = 0 \/ iprod beta gamma = sprod beta gamma) :
      forall c, In c all_cells ->
      exists d, In d all_cells /\
        g d mod p = g c mod p /\ lbl d mod p = lbl (sigma c) mod p.
    Proof.
      apply (match_cell_of_pools (zpool (List.length all_cells + 1))).
      - unfold Poly.NoDupP. apply zpool_NoDup_mod. lia.
      - rewrite zpool_length. lia.
      - intros beta _.
        exists (zpool (2 * List.length all_cells + 1)).
        split; [unfold Poly.NoDupP; apply zpool_NoDup_mod; lia |].
        split; [rewrite zpool_length; lia |].
        intros gamma _. apply Hor.
    Qed.

    (** ** Soundness: the all-challenge rules force σ-invariance

        Label injectivity resolves the matched cell to [σ c], so the σ
        image of a usable cell is usable and carries the same value. *)

    Theorem permutation_sound
        (Hbig : 2 * Z.of_nat (List.length all_cells) + 1 <= p)
        (Hinj : forall c d, space_cell c -> space_cell d ->
          lbl c mod p = lbl d mod p -> c = d)
        (Hrange : forall c, usable_cell c -> space_cell (sigma c))
        (Hrules : forall beta gamma,
          exists zs, permutation_rules beta gamma zs) :
      forall c, usable_cell c ->
      usable_cell (sigma c) /\ g c mod p = g (sigma c) mod p.
    Proof.
      intros c Hc.
      assert (Hor : forall beta gamma,
        iprod beta gamma = 0 \/ iprod beta gamma = sprod beta gamma)
        by (intros beta gamma; apply rules_products; exact (Hrules beta gamma)).
      destruct (match_cell Hbig Hor c (proj2 (in_all_cells c) Hc))
        as [d [Hdin [Hgd Hld]]].
      assert (Hd : d = sigma c).
      { apply Hinj.
        - apply usable_cell_space. apply (proj1 (in_all_cells d)). exact Hdin.
        - exact (Hrange c Hc).
        - exact Hld. }
      subst d. split.
      - apply (proj1 (in_all_cells (sigma c))). exact Hdin.
      - symmetry. exact Hgd.
    Qed.

    (** The composition form: with σ the permutation of a closed assembly,
        fixing every non-usable cell, and a reduced grid, the conclusion is
        [sigma.v]'s [grid_invariant] verbatim — the hypothesis
        [sigma_correct] turns into the copy equalities. *)
    Theorem permutation_sound_grid_invariant
        (assembly : Sigma.t)
        (Hsig : forall c, sigma c = Sigma.perm assembly c)
        (Hbig : 2 * Z.of_nat (List.length all_cells) + 1 <= p)
        (Hinj : forall c d, space_cell c -> space_cell d ->
          lbl c mod p = lbl d mod p -> c = d)
        (Hrange : forall c, usable_cell c -> space_cell (sigma c))
        (Hfix : forall c, ~ usable_cell c -> sigma c = c)
        (Hred : forall c, usable_cell c -> 0 <= g c < p)
        (Hrules : forall beta gamma,
          exists zs, permutation_rules beta gamma zs) :
      grid_invariant g assembly.
    Proof.
      intro c. rewrite <- Hsig.
      destruct (Nat.ltb_spec (fst c) ncols) as [H1 | H1];
        [destruct (Nat.ltb_spec (snd c) un) as [H2 | H2] |].
      - destruct (permutation_sound Hbig Hinj Hrange Hrules c (conj H1 H2))
          as [Hu Hg].
        rewrite <- (Z.mod_small (g c) p (Hred c (conj H1 H2))).
        rewrite <- (Z.mod_small (g (sigma c)) p (Hred (sigma c) Hu)).
        exact Hg.
      - rewrite Hfix; [reflexivity |]. intros [_ Hc2]. lia.
      - rewrite Hfix; [reflexivity |]. intros [Hc1 _]. lia.
    Qed.

    (** ** Completeness: a σ-invariant grid satisfies the rules

        The running products are exhibited division-free: the value at
        chunk [a], row [m] is
        [Π(id side before) · Π(σ side from here on) · total⁻¹], so the row
        recurrence and the chunk chaining hold by regrouping, the boot and
        boolean endpoints collapse to [total · total⁻¹ = 1], and only the
        endpoints use σ-invariance (through the total-product equality
        [sprod = iprod], by reindexing along σ). *)

    Lemma NoDup_all_cells : NoDup all_cells.
    Proof.
      assert (Hcc : List.concat col_chunks = List.seq 0 ncols)
        by (unfold col_chunks; apply chunk_list_concat).
      assert (Hnd : NoDup (List.concat col_chunks))
        by (rewrite Hcc; apply seq_NoDup).
      unfold all_cells.
      apply NoDup_flat_map_disjoint.
      - apply NoDup_pieces; [exact Hnd |].
        intros l Hl. unfold col_chunks, chunk_list in Hl.
        exact (chunk_go_nonempty _ _ _ Hchunk l Hl).
      - intros ch Hch. unfold chunk_cells.
        apply (NoDup_flat_map_tag (chunk_row_cells ch) snd).
        + apply seq_NoDup.
        + intros j _. unfold chunk_row_cells.
          apply NoDup_map_in.
          * exact (NoDup_concat_member col_chunks ch Hnd Hch).
          * intros x y _ _ Hxy. congruence.
        + intros j b _ Hb. unfold chunk_row_cells in Hb.
          apply in_map_iff in Hb. destruct Hb as [i [Hib _]].
          subst b. reflexivity.
      - intros ch1 ch2 c H1 H2 Hc1 Hc2.
        assert (Hf1 : In (fst c) ch1).
        { unfold chunk_cells in Hc1. apply in_flat_map in Hc1.
          destruct Hc1 as [j [_ Hc1]].
          unfold chunk_row_cells in Hc1. apply in_map_iff in Hc1.
          destruct Hc1 as [i [Hi Hin]]. subst c. exact Hin. }
        assert (Hf2 : In (fst c) ch2).
        { unfold chunk_cells in Hc2. apply in_flat_map in Hc2.
          destruct Hc2 as [j [_ Hc2]].
          unfold chunk_row_cells in Hc2. apply in_map_iff in Hc2.
          destruct Hc2 as [i [Hi Hin]]. subst c. exact Hin. }
        exact (NoDup_concat_disjoint col_chunks ch1 ch2 (fst c)
          Hnd H1 H2 Hf1 Hf2).
    Qed.

    (** The σ-side row products of a chunk, rows [m..un). *)
    Definition stail (beta gamma : Z) (ch : list nat) (m : nat) : Z :=
      fprod (List.map (srow beta gamma ch) (List.seq m (un - m))).

    Lemma stail_zero (beta gamma : Z) (ch : list nat) :
      stail beta gamma ch 0 = scum beta gamma ch un.
    Proof. unfold stail, scum. rewrite Nat.sub_0_r. reflexivity. Qed.

    Lemma stail_full (beta gamma : Z) (ch : list nat) :
      stail beta gamma ch un = 1.
    Proof. unfold stail. rewrite Nat.sub_diag. reflexivity. Qed.

    Lemma stail_S (beta gamma : Z) (ch : list nat) (m : nat) :
      (m < un)%nat ->
      stail beta gamma ch m
        = BinOp.mul (srow beta gamma ch m) (stail beta gamma ch (S m)).
    Proof.
      intro Hm. unfold stail.
      replace (un - m)%nat with (S (un - S m))%nat by lia.
      cbn [List.seq List.map]. rewrite fprod_cons. reflexivity.
    Qed.

    (** The honest running-product value at chunk [a], row [m0] (clamped
        to the usable prefix; rows past it are unconstrained). *)
    Definition zval (beta gamma : Z) (a m0 : nat) : Z :=
      BinOp.mul
        (BinOp.mul
          (fprod (List.map (fun ch => icum beta gamma ch un)
            (List.firstn a col_chunks)))
          (icum beta gamma (List.nth a col_chunks []) (Nat.min m0 un)))
        (BinOp.mul
          (BinOp.mul
            (stail beta gamma (List.nth a col_chunks []) (Nat.min m0 un))
            (fprod (List.map (fun ch => scum beta gamma ch un)
              (List.skipn (S a) col_chunks))))
          (mod_inverse (iprod beta gamma) p)).

    Lemma skipn_K : List.skipn K col_chunks = [].
    Proof. unfold K. apply skipn_all. Qed.

    (** The row recurrence holds identically: stepping the row moves one
        σ-side row factor to the identity side. *)
    Lemma zval_step (beta gamma : Z) (a : nat) (ch : list nat) (j : nat)
        (Hch : List.nth_error col_chunks a = Some ch)
        (Hj : (j < un)%nat) :
      BinOp.mul (zval beta gamma a (S j)) (srow beta gamma ch j)
        = BinOp.mul (zval beta gamma a j) (irow beta gamma ch j).
    Proof.
      assert (Hnth : List.nth a col_chunks [] = ch)
        by (apply nth_error_nth; exact Hch).
      unfold zval. rewrite Hnth.
      replace (Nat.min (S j) un) with (S j) by lia.
      replace (Nat.min j un) with j by lia.
      rewrite icum_S.
      rewrite (stail_S beta gamma ch j Hj).
      mod_ring_solve.
    Qed.

    (** The boot endpoint: the whole σ-side times the inverse total. *)
    Lemma zval_boot (beta gamma : Z)
        (HK : (1 <= K)%nat)
        (Hst : sprod beta gamma = iprod beta gamma)
        (Hnz : iprod beta gamma <> 0) :
      zval beta gamma 0 0 = 1.
    Proof.
      unfold zval.
      change (Nat.min 0 un) with 0%nat.
      rewrite stail_zero.
      cbn [List.firstn List.map].
      change (fprod []) with 1.
      change (icum beta gamma (List.nth 0 col_chunks []) 0) with 1.
      set (ti := mod_inverse (iprod beta gamma) p).
      assert (Hs : sprod beta gamma
        = BinOp.mul
            (BinOp.mul 1 (scum beta gamma (List.nth 0 col_chunks []) un))
            (fprod (List.map (fun ch => scum beta gamma ch un)
              (List.skipn 1 col_chunks)))).
      { rewrite sprod_map.
        apply (fprod_map_split (fun ch => scum beta gamma ch un)
          col_chunks 0).
        apply nth_error_nth'. exact HK. }
      rewrite Hst in Hs.
      transitivity (BinOp.mul (iprod beta gamma) ti).
      - rewrite Hs. mod_ring_solve.
      - unfold ti. apply fmul_inv_r; [| exact Hnz].
        unfold iprod. apply fprod_canonical.
    Qed.

    (** The chaining endpoint: the boundary values of consecutive chunks
        are the same regrouping of the total. *)
    Lemma zval_chain (beta gamma : Z) (a : nat)
        (Ha : (1 <= a)%nat) (HaK : (a < K)%nat) :
      zval beta gamma a 0 = zval beta gamma (a - 1) un.
    Proof.
      unfold K in HaK.
      destruct a as [| a']; [lia |].
      replace (S a' - 1)%nat with a' by lia.
      unfold zval.
      change (Nat.min 0 un) with 0%nat.
      rewrite Nat.min_id.
      rewrite stail_zero, stail_full.
      change (icum beta gamma (List.nth (S a') col_chunks []) 0) with 1.
      assert (HneA : List.nth_error col_chunks a'
        = Some (List.nth a' col_chunks []))
        by (apply nth_error_nth'; lia).
      assert (HneS : List.nth_error col_chunks (S a')
        = Some (List.nth (S a') col_chunks []))
        by (apply nth_error_nth'; lia).
      rewrite (firstn_snoc col_chunks a' _ HneA), map_app.
      cbn [List.map]. rewrite fprod_snoc.
      rewrite (skipn_cons_nth col_chunks (S a') _ HneS).
      cbn [List.map]. rewrite fprod_cons.
      mod_ring_solve.
    Qed.

    (** The boolean endpoint: the whole identity side times the inverse
        total. *)
    Lemma zval_last (beta gamma : Z)
        (HK : (1 <= K)%nat)
        (Hnz : iprod beta gamma <> 0) :
      zval beta gamma (K - 1) un = 1.
    Proof.
      unfold zval.
      rewrite Nat.min_id, stail_full.
      replace (S (K - 1)) with K by lia.
      rewrite skipn_K.
      cbn [List.map]. change (fprod []) with 1.
      set (ti := mod_inverse (iprod beta gamma) p).
      assert (Hi : iprod beta gamma
        = BinOp.mul
            (BinOp.mul
              (fprod (List.map (fun ch => icum beta gamma ch un)
                (List.firstn (K - 1) col_chunks)))
              (icum beta gamma (List.nth (K - 1) col_chunks []) un))
            (fprod (List.map (fun ch => icum beta gamma ch un)
              (List.skipn (S (K - 1)) col_chunks)))).
      { rewrite iprod_map.
        apply (fprod_map_split (fun ch => icum beta gamma ch un)
          col_chunks (K - 1)).
        apply nth_error_nth'. unfold K in *. lia. }
      replace (S (K - 1)) with K in Hi by lia.
      rewrite skipn_K in Hi.
      cbn [List.map] in Hi. change (fprod []) with 1 in Hi.
      transitivity (BinOp.mul (iprod beta gamma) ti).
      - rewrite Hi. mod_ring_solve.
      - unfold ti. apply fmul_inv_r; [| exact Hnz].
        unfold iprod. apply fprod_canonical.
    Qed.

    Theorem permutation_complete
        (Hinv : forall c, usable_cell c -> g c mod p = g (sigma c) mod p)
        (Hpres : forall c, usable_cell c -> usable_cell (sigma c))
        (Hsinj : forall c d, usable_cell c -> usable_cell d ->
          sigma c = sigma d -> c = d)
        (beta gamma : Z)
        (Hnz : forall c, usable_cell c -> ifac beta gamma c <> 0) :
      exists zs, permutation_rules beta gamma zs.
    Proof.
      assert (Hperm : Permutation (List.map sigma all_cells) all_cells).
      { apply NoDup_Permutation_bis.
        - apply NoDup_map_in; [exact NoDup_all_cells |].
          intros x y Hx Hy Hxy.
          apply (Hsinj x y);
            [apply (proj1 (in_all_cells x)); exact Hx
            | apply (proj1 (in_all_cells y)); exact Hy
            | exact Hxy].
        - rewrite length_map. apply Nat.le_refl.
        - intros x Hx. apply in_map_iff in Hx.
          destruct Hx as [c [Hc Hcin]]. subst x.
          apply (proj2 (in_all_cells (sigma c))).
          apply Hpres. apply (proj1 (in_all_cells c)). exact Hcin. }
      assert (Hst : sprod beta gamma = iprod beta gamma).
      { unfold sprod.
        transitivity (fprod (List.map (ifac beta gamma)
          (List.map sigma all_cells))).
        - rewrite map_map. apply fprod_map_ext_in.
          intros c Hc. unfold sfac, ifac.
          assert (Hg : g c mod p = g (sigma c) mod p)
            by (apply Hinv; apply (proj1 (in_all_cells c)); exact Hc).
          replace (g c + beta * lbl (sigma c) + gamma)
            with (g c + (beta * lbl (sigma c) + gamma)) by ring.
          replace (g (sigma c) + beta * lbl (sigma c) + gamma)
            with (g (sigma c) + (beta * lbl (sigma c) + gamma)) by ring.
          rewrite (Zplus_mod (g c)), Hg, <- Zplus_mod. reflexivity.
        - unfold iprod. apply fprod_perm.
          exact (Permutation_map (ifac beta gamma) Hperm). }
      assert (HT : iprod beta gamma <> 0).
      { unfold iprod. intro Hz. apply fprod_zero_iff in Hz.
        destruct Hz as [v [Hv Hvm]].
        apply in_map_iff in Hv. destruct Hv as [c [Hvc Hcin]]. subst v.
        apply (Hnz c).
        - apply (proj1 (in_all_cells c)). exact Hcin.
        - unfold ifac in *. rewrite Zmod_mod in Hvm. exact Hvm. }
      exists (List.map
        (fun a => (fun r : Z => zval beta gamma a (Z.to_nat r)))
        (List.seq 0 K)).
      assert (Hznth : forall a, (a < K)%nat ->
        List.nth_error
          (List.map
            (fun a0 => (fun r : Z => zval beta gamma a0 (Z.to_nat r)))
            (List.seq 0 K)) a
        = Some (fun r : Z => zval beta gamma a (Z.to_nat r))).
      { intros a Ha. rewrite nth_error_map.
        rewrite (nth_error_nth' (List.seq 0 K) 0%nat)
          by (rewrite length_seq; exact Ha).
        rewrite seq_nth by exact Ha.
        reflexivity. }
      refine (conj _ (conj _ (conj _ (conj _ _)))).
      - rewrite length_map, length_seq. reflexivity.
      - (* boot *)
        intros z0 Hz0.
        destruct (Nat.eq_dec K 0) as [HK0 | HK0].
        + rewrite HK0 in Hz0. cbn in Hz0. discriminate.
        + assert (HK : (1 <= K)%nat) by lia.
          rewrite (Hznth 0%nat ltac:(lia)) in Hz0.
          injection Hz0 as Hz0. subst z0.
          intros row Hrow.
          destruct (Z.eq_dec row 0) as [-> | Hne].
          * rewrite sel_l0_0. apply gate_intro. symmetry. cbv beta.
            exact (zval_boot beta gamma HK Hst HT).
          * rewrite sel_l0_off by exact Hne. apply fmul_0_l.
      - (* product *)
        intros a ch z Hcha Hza.
        assert (HaK : (a < K)%nat).
        { assert (Htmp : List.nth_error col_chunks a <> None)
            by (rewrite Hcha; discriminate).
          apply nth_error_Some in Htmp. exact Htmp. }
        rewrite (Hznth a HaK) in Hza. injection Hza as Hza. subst z.
        intros row Hrow.
        destruct (Z_lt_le_dec row (Domain.usable_rows domain)) as [Hlt | Hge].
        + rewrite active_usable by lia.
          rewrite rot_next by lia.
          apply gate_intro. cbv beta.
          set (j := Z.to_nat row).
          replace (Z.to_nat (row + 1)) with (S j) by (unfold j; lia).
          apply (zval_step beta gamma a ch j Hcha).
          unfold j, un. lia.
        + rewrite active_off by lia. apply fmul_0_l.
      - (* chaining *)
        intros a zp z Ha1 Hzp Hz.
        assert (HaK : (a < K)%nat).
        { assert (Htmp : List.nth_error
            (List.map
              (fun a0 => (fun r : Z => zval beta gamma a0 (Z.to_nat r)))
              (List.seq 0 K)) a <> None)
            by (rewrite Hz; discriminate).
          apply nth_error_Some in Htmp.
          rewrite length_map, length_seq in Htmp. exact Htmp. }
        rewrite (Hznth a HaK) in Hz. injection Hz as Hz. subst z.
        rewrite (Hznth (a - 1)%nat ltac:(lia)) in Hzp.
        injection Hzp as Hzp. subst zp.
        intros row Hrow.
        destruct (Z.eq_dec row 0) as [-> | Hne].
        + rewrite sel_l0_0, rot_last.
          apply gate_intro. cbv beta.
          change (Z.to_nat 0) with 0%nat.
          change (Z.to_nat (Domain.usable_rows domain)) with un.
          exact (zval_chain beta gamma a Ha1 HaK).
        + rewrite sel_l0_off by exact Hne. apply fmul_0_l.
      - (* boolean *)
        intros zl Hzl.
        destruct (Nat.eq_dec K 0) as [HK0 | HK0].
        + rewrite HK0 in Hzl. cbn in Hzl. discriminate.
        + assert (HK : (1 <= K)%nat) by lia.
          rewrite (Hznth (K - 1)%nat ltac:(lia)) in Hzl.
          injection Hzl as Hzl. subst zl.
          intros row Hrow.
          destruct (Z.eq_dec row (Domain.usable_rows domain)) as [-> | Hne].
          * rewrite sel_llast_at.
            apply gate_intro. cbv beta.
            change (Z.to_nat (Domain.usable_rows domain)) with un.
            rewrite (zval_last beta gamma HK HT).
            rewrite fmul_1_l. apply Z.mod_1_l.
            exact (prime_range (p := p)).
          * rewrite sel_llast_off by exact Hne. apply fmul_0_l.
    Qed.

    (** The composition form: [grid_invariant] of a closed assembly whose
        permutation fixes the non-usable cells and is injective satisfies
        the rules at every challenge where no identity-side factor
        vanishes. *)
    Theorem permutation_complete_grid_invariant
        (assembly : Sigma.t)
        (Hsig : forall c, sigma c = Sigma.perm assembly c)
        (Hgi : grid_invariant g assembly)
        (Hfix : forall c, ~ usable_cell c -> sigma c = c)
        (Hginj : forall c d, sigma c = sigma d -> c = d)
        (beta gamma : Z)
        (Hnz : forall c, usable_cell c -> ifac beta gamma c <> 0) :
      exists zs, permutation_rules beta gamma zs.
    Proof.
      apply permutation_complete; [| | | exact Hnz].
      - intros c _. rewrite Hsig, <- (Hgi c). reflexivity.
      - intros c Hc.
        destruct (Nat.ltb_spec (fst (sigma c)) ncols) as [H1 | H1];
          [destruct (Nat.ltb_spec (snd (sigma c)) un) as [H2 | H2] |].
        + split; assumption.
        + exfalso.
          assert (Hnu : ~ usable_cell (sigma c))
            by (intros [Ha Hb]; lia).
          pose proof (Hfix _ Hnu) as Hfd.
          assert (Hdc : sigma c = c) by (apply Hginj; exact Hfd).
          rewrite Hdc in Hnu. exact (Hnu Hc).
        + exfalso.
          assert (Hnu : ~ usable_cell (sigma c))
            by (intros [Ha Hb]; lia).
          pose proof (Hfix _ Hnu) as Hfd.
          assert (Hdc : sigma c = c) by (apply Hginj; exact Hfd).
          rewrite Hdc in Hnu. exact (Hnu Hc).
      - intros c d _ _. apply Hginj.
    Qed.

  End WithSystem.

End WithPrime.
End PermutationPoly.
