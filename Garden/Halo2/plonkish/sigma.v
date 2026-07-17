(** * Correctness of the permutation σ: grid invariance ↔ copy equalities.

    [Sigma.sigma_of_copies] closes a list of [Copy] obligations into an
    explicit permutation of the equality-enabled cell set (the port of
    [plonk/permutation/keygen.rs]).  This file proves the compilation
    correctness of that construction: a grid is invariant under the
    permutation — every cell carries the same value as its image — exactly
    when every copy of the list holds as an equality of the two cell
    values.  The statement is generic over the value type of the grid and
    over the permutation column list, with no Orchard specifics.

    The proof follows the orbit reading of the permutation.  The backward
    direction (copy equalities ⇒ grid invariant) is a local fact about the
    one-step splice [Sigma.copy] performs: invariance under the running
    [mapping] is preserved by each copy, because the two entries the splice
    swaps carry equal grid values.  The forward direction (grid invariant ⇒
    copy equalities) reads the copies off the orbit structure: the two cells
    of every processed copy lie in a common orbit of the constructed
    permutation, and a grid invariant under the permutation is constant on
    each orbit. *)

Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.micromega.Lia.
Require Import Garden.Halo2.main.
Require Import Garden.Halo2.serialize.
Require Import Garden.Halo2.plonkish.main.
Require Import Garden.Halo2.plonkish.orbit.

Import ListNotations.
Import Plonkish.
Global Open Scope Z_scope.

(** ** List surgery lemmas

    [list_set] overwrites one position of a list; [Sigma.get2]/[Sigma.set2]
    read and write one cell of a matrix.  The compiled permutation is a
    matrix of cells, so every step of the construction is a composition of
    these. *)

Lemma list_set_length {A : Set} (l : list A) (i : nat) (v : A) :
  List.length (list_set l i v) = List.length l.
Proof.
  revert i; induction l as [|x l IH]; intros [|i]; simpl; auto.
Qed.

(** The single characterisation of [nth] after [list_set], covering every
    combination of in/out of range and matching/non-matching index. *)
Lemma nth_list_set {A : Set} (l : list A) (i j : nat) (v d : A) :
  List.nth i (list_set l j v) d =
    (if andb (Nat.eqb i j) (Nat.ltb i (List.length l)) then v else List.nth i l d).
Proof.
  revert i j; induction l as [|x l IH]; intros [|i] [|j]; simpl; try reflexivity.
  - destruct (Nat.eqb i j); reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma nth_list_set_eq {A : Set} (l : list A) (i : nat) (v d : A) :
  (i < List.length l)%nat -> List.nth i (list_set l i v) d = v.
Proof.
  intro H. rewrite nth_list_set.
  rewrite Nat.eqb_refl.
  destruct (Nat.ltb i (List.length l)) eqn:E; [reflexivity|].
  apply Nat.ltb_ge in E. lia.
Qed.

(** The [i]-th entry of a [map] over an initial segment. *)
Lemma nth_map_seq {A : Set} (F : nat -> A) (len i : nat) (d : A) :
  (i < len)%nat -> List.nth i (List.map F (List.seq 0 len)) d = F i.
Proof.
  intro H.
  rewrite (nth_indep _ d (F O)) by (rewrite length_map, length_seq; exact H).
  rewrite map_nth. rewrite seq_nth by exact H. reflexivity.
Qed.

Section Get2Set2.
  Context {A : Set}.

  Lemma get2_set2_eq (default : A) (M : list (list A)) (c : Sigma.cell) (v : A) :
    (fst c < List.length M)%nat ->
    (snd c < List.length (List.nth (fst c) M []))%nat ->
    Sigma.get2 default (Sigma.set2 M c v) c = v.
  Proof.
    intros H1 H2. unfold Sigma.get2, Sigma.set2.
    rewrite nth_list_set_eq by exact H1.
    rewrite nth_list_set_eq by exact H2.
    reflexivity.
  Qed.

  Lemma get2_set2_neq (default : A) (M : list (list A)) (c d : Sigma.cell) (v : A) :
    Sigma.cell_eqb c d = false ->
    Sigma.get2 default (Sigma.set2 M c v) d = Sigma.get2 default M d.
  Proof.
    intro Hcd. unfold Sigma.get2, Sigma.set2.
    rewrite nth_list_set.
    destruct (andb (Nat.eqb (fst d) (fst c)) (Nat.ltb (fst d) (List.length M))) eqn:E.
    - apply andb_prop in E as [Ee _]. apply Nat.eqb_eq in Ee.
      rewrite nth_list_set.
      assert (Hsnd : Nat.eqb (snd d) (snd c) = false).
      { rewrite Nat.eqb_sym.
        unfold Sigma.cell_eqb in Hcd.
        rewrite Ee, Nat.eqb_refl in Hcd. simpl in Hcd. exact Hcd. }
      rewrite Hsnd. simpl. rewrite Ee. reflexivity.
    - reflexivity.
  Qed.

  Lemma set2_length (M : list (list A)) (c : Sigma.cell) (v : A) :
    List.length (Sigma.set2 M c v) = List.length M.
  Proof. unfold Sigma.set2. apply list_set_length. Qed.

  Lemma set2_nth_length (M : list (list A)) (c : Sigma.cell) (v : A) (i : nat) :
    List.length (List.nth i (Sigma.set2 M c v) (@nil A)) =
      List.length (List.nth i M []).
  Proof.
    unfold Sigma.set2. rewrite nth_list_set.
    destruct (andb (Nat.eqb i (fst c)) (Nat.ltb i (List.length M))) eqn:E.
    - apply andb_prop in E as [Ee _]. apply Nat.eqb_eq in Ee. subst i.
      rewrite list_set_length. reflexivity.
    - reflexivity.
  Qed.
End Get2Set2.

(** ** Cell equality *)

Lemma cell_eqb_eq (c d : Sigma.cell) : Sigma.cell_eqb c d = true <-> c = d.
Proof.
  unfold Sigma.cell_eqb. split.
  - intro H. apply andb_prop in H as [Hf Hs].
    apply Nat.eqb_eq in Hf. apply Nat.eqb_eq in Hs.
    destruct c, d; simpl in *; subst; reflexivity.
  - intro H; subst d. rewrite !Nat.eqb_refl. reflexivity.
Qed.

Lemma cell_eqb_refl (c : Sigma.cell) : Sigma.cell_eqb c c = true.
Proof. apply cell_eqb_eq. reflexivity. Qed.

Lemma cell_eqb_sym (c d : Sigma.cell) : Sigma.cell_eqb c d = Sigma.cell_eqb d c.
Proof.
  unfold Sigma.cell_eqb. rewrite (Nat.eqb_sym (fst c)), (Nat.eqb_sym (snd c)).
  reflexivity.
Qed.

Lemma cell_eqb_neq (c d : Sigma.cell) : c <> d -> Sigma.cell_eqb c d = false.
Proof.
  intro H. destruct (Sigma.cell_eqb c d) eqn:E; [| reflexivity].
  apply cell_eqb_eq in E. contradiction.
Qed.

Definition cell_eq_dec (c d : Sigma.cell) : {c = d} + {c <> d}.
Proof.
  destruct (Sigma.cell_eqb c d) eqn:E.
  - left. apply cell_eqb_eq. exact E.
  - right. intro H. subst d. rewrite cell_eqb_refl in E. discriminate.
Defined.

(** [list_set] preserves a pointwise predicate when the new entry
    satisfies it. *)
Lemma Forall_list_set {A : Set} (P : A -> Prop) (l : list A) (i : nat) (v : A) :
  List.Forall P l -> P v -> List.Forall P (list_set l i v).
Proof.
  revert i. induction l as [|x l IH]; intros i HF Hv; destruct i as [|i];
    simpl.
  - exact HF.
  - exact HF.
  - inversion HF; subst. constructor; assumption.
  - inversion HF; subst. constructor; [assumption | apply IH; assumption].
Qed.

(** [list_sum] of a constant list. *)
Lemma fold_left_add_shift (l : list nat) (acc : nat) :
  List.fold_left Nat.add l acc = (acc + List.fold_left Nat.add l O)%nat.
Proof.
  revert acc. induction l as [|x l IH]; intro acc; simpl.
  - lia.
  - rewrite (IH (acc + x)%nat), (IH x). lia.
Qed.

Lemma list_sum_const (l : list nat) (n : nat) :
  List.Forall (fun x => x = n) l -> list_sum l = (List.length l * n)%nat.
Proof.
  induction l as [|x l IH]; intro HF; [reflexivity |].
  inversion HF; subst.
  unfold list_sum in *. simpl.
  rewrite fold_left_add_shift. rewrite IH by assumption. lia.
Qed.

(** Iterates of a pointwise-identity function. *)
Lemma iter_pointwise_id {A : Type} (f : A -> A) (Hf : forall x, f x = x)
    (k : nat) (c : A) :
  Nat.iter k f c = c.
Proof.
  induction k as [|k IH]; simpl; [reflexivity | rewrite IH; apply Hf].
Qed.

(** ** Column resolution *)

Lemma column_position_lt (columns : list Raw.ColumnRef.t)
    (column : Raw.ColumnRef.t) (p : nat) :
  Sigma.column_position columns column = Some p ->
  (p < List.length columns)%nat.
Proof.
  revert p; induction columns as [|x columns IH]; simpl; intros p H.
  - discriminate.
  - destruct (Sigma.column_eqb x column).
    + injection H as H; subst p. lia.
    + destruct (Sigma.column_position columns column) as [q|] eqn:E;
        simpl in H; try discriminate.
      injection H as H; subst p. specialize (IH q eq_refl). lia.
Qed.

(** ** The grid, invariance, and orbit reachability *)

Section GridCorrectness.
  Context {V : Type} (g : Sigma.cell -> V).
  Context (cols : list Raw.ColumnRef.t).

  (** The [Sigma.cell] a raw copy cell resolves to under the permutation
      column list; [None] exactly when the column is not equality-enabled. *)
  Definition resolve_cell (c : Raw.Cell.t) : option Sigma.cell :=
    match Sigma.column_position cols c.(Raw.Cell.column) with
    | Some pos => Some (pos, Z.to_nat c.(Raw.Cell.row))
    | None => None
    end.

  (** A copy holds as a grid equality: its two resolved cells carry the same
      value.  Copies over non-equality columns are vacuous — they never
      arise when [sigma_of_copies] succeeds. *)
  Definition copy_holds (p : Raw.Cell.t * Raw.Cell.t) : Prop :=
    match resolve_cell (fst p), resolve_cell (snd p) with
    | Some cl, Some cr => g cl = g cr
    | _, _ => True
    end.

  (** The grid is invariant under the assembly's permutation: every cell has
      the value of its image. *)
  Definition grid_invariant (self : Sigma.t) : Prop :=
    forall c, g c = g (Sigma.perm self c).

  (** [d] is reachable from [c] by iterating the permutation. *)
  Definition reach (f : Sigma.cell -> Sigma.cell) (c d : Sigma.cell) : Prop :=
    exists k, Nat.iter k f c = d.

  (** A grid invariant under a permutation is constant along reachability. *)
  Lemma reach_grid_invariant (self : Sigma.t) (c d : Sigma.cell) :
    grid_invariant self -> reach (Sigma.perm self) c d -> g c = g d.
  Proof.
    intros GI [k Hk]. subst d.
    induction k as [|k IH]; simpl.
    - reflexivity.
    - rewrite IH. apply GI.
  Qed.

  (** ** Well-formedness threaded through the fold

      Only the column count of [mapping] and the fixed column list are
      needed: they bound the cells the splice touches. *)
  Definition WF (self : Sigma.t) : Prop :=
    Sigma.columns self = cols /\
    List.length (Sigma.mapping self) = List.length cols.

  Lemma WF_init (n_rows : nat) : WF (Sigma.init cols n_rows).
  Proof.
    split; simpl.
    - reflexivity.
    - rewrite map_length, seq_length. reflexivity.
  Qed.

  (** The identity assembly maps every cell to itself. *)
  Lemma perm_init (n_rows : nat) (c : Sigma.cell) :
    Sigma.perm (Sigma.init cols n_rows) c = c.
  Proof.
    destruct c as [i j].
    unfold Sigma.perm.
    replace (Sigma.mapping (Sigma.init cols n_rows))
      with (List.map (fun i0 => List.map (fun j0 => (i0, j0)) (List.seq 0 n_rows))
                     (List.seq 0 (List.length cols)))
      by reflexivity.
    unfold Sigma.get2. cbn [fst snd].
    destruct (Nat.ltb i (List.length cols)) eqn:Ei.
    - apply Nat.ltb_lt in Ei.
      rewrite nth_map_seq by exact Ei.
      cbn beta.
      destruct (Nat.ltb j n_rows) eqn:Ej.
      + apply Nat.ltb_lt in Ej.
        rewrite nth_map_seq by exact Ej.
        reflexivity.
      + apply Nat.ltb_ge in Ej.
        rewrite nth_overflow by (rewrite length_map, length_seq; exact Ej).
        reflexivity.
    - apply Nat.ltb_ge in Ei.
      rewrite (@nth_overflow _ _ i)
        by (rewrite length_map, length_seq; exact Ei).
      destruct j; reflexivity.
  Qed.

  Lemma copy_preserves_WF (self self' : Sigma.t) (left right : Raw.Cell.t) :
    WF self -> Sigma.copy self left right = Some self' -> WF self'.
  Proof.
    intros [Hc Hlen] H. unfold Sigma.copy in H.
    destruct (Sigma.column_position self.(Sigma.columns) left.(Raw.Cell.column))
      as [pl|] eqn:El; [|discriminate].
    destruct (Sigma.column_position self.(Sigma.columns) right.(Raw.Cell.column))
      as [pr|] eqn:Er; [|discriminate].
    destruct (negb _) eqn:Eb; [discriminate|].
    destruct (Sigma.cell_eqb _ _) eqn:Ecyc.
    - injection H as H; subst self'. split; assumption.
    - destruct (Nat.ltb _ _);
        injection H as H; subst self'; split; simpl;
        try assumption;
        rewrite !set2_length; exact Hlen.
  Qed.

  (** ** Backward direction: copy equalities preserve grid invariance *)

  (** The one-step fact: if the grid is invariant under [self]'s permutation
      and the copy holds as a grid equality, it is invariant under the
      spliced permutation.  The splice rewrites exactly the images of the
      two copied cells, whose values are pinned equal by the invariant plus
      the copy equality. *)
  Lemma backward_step (self self' : Sigma.t) (left right : Raw.Cell.t) :
    WF self ->
    grid_invariant self ->
    copy_holds (left, right) ->
    Sigma.copy self left right = Some self' ->
    grid_invariant self'.
  Proof.
    intros [Hc Hlen] GI Hch H.
    unfold Sigma.copy in H. rewrite Hc in H.
    destruct (Sigma.column_position cols left.(Raw.Cell.column))
      as [pl|] eqn:El; [|discriminate].
    destruct (Sigma.column_position cols right.(Raw.Cell.column))
      as [pr|] eqn:Er; [|discriminate].
    destruct (negb _) eqn:Eb; [discriminate|].
    apply negb_false_iff in Eb.
    apply andb_prop in Eb as [Ebl Ebr].
    apply andb_prop in Ebl as [Ebl0 Ebl1].
    apply andb_prop in Ebr as [Ebr0 Ebr1].
    apply Z.leb_le in Ebl0. apply Z.ltb_lt in Ebl1.
    apply Z.leb_le in Ebr0. apply Z.ltb_lt in Ebr1.
    (* Bounds on the two touched cells. *)
    set (left_cell := (pl, Z.to_nat left.(Raw.Cell.row))) in *.
    set (right_cell := (pr, Z.to_nat right.(Raw.Cell.row))) in *.
    assert (Hpl : (pl < List.length (Sigma.mapping self))%nat).
    { rewrite Hlen. eapply column_position_lt; exact El. }
    assert (Hpr : (pr < List.length (Sigma.mapping self))%nat).
    { rewrite Hlen. eapply column_position_lt; exact Er. }
    assert (HrowL : (Z.to_nat left.(Raw.Cell.row) <
                      List.length (List.nth pl (Sigma.mapping self) []))%nat).
    { apply Nat2Z.inj_lt. rewrite Z2Nat.id by exact Ebl0. exact Ebl1. }
    assert (HrowR : (Z.to_nat right.(Raw.Cell.row) <
                      List.length (List.nth pr (Sigma.mapping self) []))%nat).
    { apply Nat2Z.inj_lt. rewrite Z2Nat.id by exact Ebr0. exact Ebr1. }
    (* Distinctness of the two cells in the splice branch. *)
    destruct (Sigma.cell_eqb
                (Sigma.get2 left_cell self.(Sigma.aux) left_cell)
                (Sigma.get2 right_cell self.(Sigma.aux) right_cell)) eqn:Ecyc.
    { (* early return: assembly unchanged *)
      injection H as H; subst self'; exact GI. }
    assert (Hne : Sigma.cell_eqb left_cell right_cell = false).
    { destruct (Sigma.cell_eqb left_cell right_cell) eqn:E; [|reflexivity].
      apply cell_eqb_eq in E. rewrite E in Ecyc.
      rewrite cell_eqb_refl in Ecyc. discriminate. }
    assert (HneR : Sigma.cell_eqb right_cell left_cell = false).
    { rewrite cell_eqb_sym. exact Hne. }
    (* The spliced mapping. *)
    set (right_image := Sigma.get2 right_cell self.(Sigma.mapping) right_cell).
    set (left_image := Sigma.get2 left_cell self.(Sigma.mapping) left_cell).
    set (M1 := Sigma.set2 self.(Sigma.mapping) left_cell right_image).
    set (M2 := Sigma.set2 M1 right_cell left_image).
    assert (Hmap : Sigma.mapping self' = M2).
    { destruct (Nat.ltb _ _); injection H as H; subst self'; reflexivity. }
    clear H.
    unfold grid_invariant, Sigma.perm. intro c. rewrite Hmap.
    (* Case on whether c is one of the two touched cells. *)
    destruct (Sigma.cell_eqb c left_cell) eqn:Hcl.
    { apply cell_eqb_eq in Hcl. subst c.
      unfold M2. rewrite (get2_set2_neq _ _ _ _ _ HneR).
      unfold M1. rewrite get2_set2_eq by (unfold left_cell; assumption).
      (* goal: g left_cell = g right_image *)
      unfold copy_holds, resolve_cell in Hch. simpl in Hch.
      rewrite El, Er in Hch.
      change (g left_cell = g right_image).
      transitivity (g right_cell); [exact Hch|].
      unfold right_image. exact (GI right_cell). }
    destruct (Sigma.cell_eqb c right_cell) eqn:Hcr.
    { apply cell_eqb_eq in Hcr. subst c.
      unfold M2. rewrite get2_set2_eq.
      2:{ unfold right_cell, M1; rewrite set2_length; assumption. }
      2:{ unfold right_cell, M1. rewrite set2_nth_length. assumption. }
      (* goal: g right_cell = g left_image *)
      unfold copy_holds, resolve_cell in Hch. simpl in Hch.
      rewrite El, Er in Hch.
      change (g right_cell = g left_image).
      transitivity (g left_cell); [symmetry; exact Hch|].
      unfold left_image. exact (GI left_cell). }
    { (* c untouched *)
      assert (HclR : Sigma.cell_eqb left_cell c = false).
      { rewrite cell_eqb_sym. exact Hcl. }
      assert (HcrR : Sigma.cell_eqb right_cell c = false).
      { rewrite cell_eqb_sym. exact Hcr. }
      unfold M2. rewrite (get2_set2_neq _ _ _ _ _ HcrR).
      unfold M1. rewrite (get2_set2_neq _ _ _ _ _ HclR).
      apply (GI c). }
  Qed.

  (** The [None]-absorbing fold. *)
  Lemma fold_copy_none (copies : list (Raw.Cell.t * Raw.Cell.t)) :
    List.fold_left
      (fun state pair =>
        match state with
        | None => None
        | Some self => Sigma.copy self (fst pair) (snd pair)
        end)
      copies None = None.
  Proof.
    induction copies as [|p copies IH]; simpl; auto.
  Qed.

  Lemma fold_backward (copies : list (Raw.Cell.t * Raw.Cell.t)) :
    forall (s0 a : Sigma.t),
      WF s0 -> grid_invariant s0 -> Forall copy_holds copies ->
      List.fold_left
        (fun state pair =>
          match state with
          | None => None
          | Some self => Sigma.copy self (fst pair) (snd pair)
          end)
        copies (Some s0) = Some a ->
      grid_invariant a.
  Proof.
    induction copies as [|p copies IH]; simpl; intros s0 a Hwf GI Hall Hfold.
    - injection Hfold as Hfold; subst a; exact GI.
    - inversion Hall as [|? ? Hp Hrest]; subst.
      destruct (Sigma.copy s0 (fst p) (snd p)) as [s1|] eqn:Ec.
      + apply (IH s1 a).
        * eapply copy_preserves_WF; [exact Hwf|exact Ec].
        * destruct p as [l r]. eapply backward_step; try eassumption.
        * exact Hrest.
        * exact Hfold.
      + rewrite fold_copy_none in Hfold. discriminate.
  Qed.

  (** ** Forward direction: infrastructure

      The forward proof follows the union-find reading of
      [plonk/permutation/keygen.rs]: along the fold, the permutation is
      an injective self-map of the cell domain, and [aux] names each
      orbit by one of its members, constantly across the orbit.  A
      processed copy leaves its two cells in a common orbit — the early
      return of [Sigma.copy] fires exactly when the two labels agree,
      i.e. when the cells already share an orbit, and the splice
      otherwise merges two distinct orbits (the generic [FiniteOrbit]
      merge).  Orbits only ever merge, so every processed copy stays
      connected in the final assembly. *)

  (** The cell domain of an assembly over [cols] with [n_rows] rows,
      with its enumeration. *)
  Definition cell_dom (n_rows : nat) (c : Sigma.cell) : Prop :=
    (fst c < List.length cols)%nat /\ (snd c < n_rows)%nat.

  Definition cell_enum (n_rows : nat) : list Sigma.cell :=
    List.list_prod (List.seq 0 (List.length cols)) (List.seq 0 n_rows).

  Lemma cell_enum_complete (n_rows : nat) (c : Sigma.cell) :
    cell_dom n_rows c -> List.In c (cell_enum n_rows).
  Proof.
    intros [H1 H2]. destruct c as [i j]. unfold cell_enum.
    apply in_prod; apply in_seq; simpl in *; lia.
  Qed.

  Lemma cell_enum_length (n_rows : nat) :
    List.length (cell_enum n_rows) = (List.length cols * n_rows)%nat.
  Proof.
    unfold cell_enum.
    etransitivity;
      [exact (length_prod (List.seq 0 (List.length cols)) (List.seq 0 n_rows)) |].
    rewrite !length_seq. reflexivity.
  Qed.

  (** A well-formed matrix plane: one row of [n_rows] entries per
      permutation column. *)
  Definition matrix_wf {A : Set} (n_rows : nat) (M : list (list A)) : Prop :=
    List.length M = List.length cols /\
    List.Forall (fun row => List.length row = n_rows) M.

  Lemma matrix_wf_nth {A : Set} (n_rows : nat) (M : list (list A)) (i : nat) :
    matrix_wf n_rows M -> (i < List.length cols)%nat ->
    List.length (List.nth i M []) = n_rows.
  Proof.
    intros [Hlen Hall] Hi.
    eapply Forall_forall in Hall; [exact Hall |].
    apply nth_In. rewrite Hlen. exact Hi.
  Qed.

  Lemma set2_preserves_wf {A : Set} (n_rows : nat) (M : list (list A))
      (c : Sigma.cell) (v : A) :
    matrix_wf n_rows M -> (fst c < List.length cols)%nat ->
    matrix_wf n_rows (Sigma.set2 M c v).
  Proof.
    intros Hwf Hc. split.
    - rewrite set2_length. exact (proj1 Hwf).
    - unfold Sigma.set2. apply Forall_list_set; [exact (proj2 Hwf) |].
      rewrite list_set_length.
      exact (matrix_wf_nth n_rows M (fst c) Hwf Hc).
  Qed.

  Lemma get2_set2_eq_wf {A : Set} (n_rows : nat) (default : A)
      (M : list (list A)) (c : Sigma.cell) (v : A) :
    matrix_wf n_rows M -> cell_dom n_rows c ->
    Sigma.get2 default (Sigma.set2 M c v) c = v.
  Proof.
    intros Hwf [H1 H2]. apply get2_set2_eq.
    - rewrite (proj1 Hwf). exact H1.
    - rewrite (matrix_wf_nth n_rows M (fst c) Hwf H1). exact H2.
  Qed.

  (** The relabeling walk of [Sigma.copy], characterised on the orbit
      of its start cell: with enough fuel it writes [lc] on exactly the
      cells [rc, f rc, …] up to the period of [rc], and leaves every
      other cell's label unchanged. *)
  Lemma relabel_cycle_spec (n_rows : nat) (M : list (list Sigma.cell))
      (f : Sigma.cell -> Sigma.cell) (rc lc : Sigma.cell) (m : nat)
      (Hf : forall c, f c = Sigma.get2 c M c)
      (HMwf : matrix_wf n_rows M)
      (Hclosed : forall c, cell_dom n_rows c -> cell_dom n_rows (f c))
      (Hrc : cell_dom n_rows rc)
      (Hm : (0 < m)%nat)
      (Hper : Nat.iter m f rc = rc)
      (Hdist : forall i j, (i < j)%nat -> (j < m)%nat ->
        Nat.iter i f rc <> Nat.iter j f rc) :
    forall (fuel : nat) (k : nat) (X : list (list Sigma.cell)),
      (k < m)%nat -> (m - k <= fuel)%nat ->
      matrix_wf n_rows X ->
      matrix_wf n_rows
        (Sigma.relabel_cycle fuel M X (Nat.iter k f rc) rc lc) /\
      (forall j, (k <= j)%nat -> (j < m)%nat ->
        Sigma.get2 (Nat.iter j f rc)
          (Sigma.relabel_cycle fuel M X (Nat.iter k f rc) rc lc)
          (Nat.iter j f rc) = lc) /\
      (forall c,
        (forall j, (k <= j)%nat -> (j < m)%nat -> Nat.iter j f rc <> c) ->
        Sigma.get2 c (Sigma.relabel_cycle fuel M X (Nat.iter k f rc) rc lc) c
          = Sigma.get2 c X c).
  Proof.
    intros fuel; induction fuel as [|fuel IH]; intros k X Hk Hfuel HXwf.
    - exfalso. lia.
    - assert (Hikdom : cell_dom n_rows (Nat.iter k f rc))
        by (exact (FiniteOrbit.iter_dom (cell_dom n_rows) f Hclosed k rc Hrc)).
      cbn [Sigma.relabel_cycle].
      rewrite <- (Hf (Nat.iter k f rc)).
      change (f (Nat.iter k f rc)) with (Nat.iter (S k) f rc).
      destruct (Sigma.cell_eqb (Nat.iter (S k) f rc) rc) eqn:Estop.
      + (* the walk closes: [k] is the last index of the orbit *)
        apply cell_eqb_eq in Estop.
        assert (Hkm : S k = m).
        { destruct (Nat.eq_dec (S k) m) as [He | Hne]; [exact He |].
          exfalso.
          exact (Hdist O (S k) ltac:(lia) ltac:(lia) (eq_sym Estop)). }
        split; [| split].
        * apply set2_preserves_wf; [exact HXwf | exact (proj1 Hikdom)].
        * intros j Hkj Hjm.
          assert (Hjk : j = k) by lia. subst j.
          exact (get2_set2_eq_wf n_rows _ X _ lc HXwf Hikdom).
        * intros c Havoid.
          apply get2_set2_neq. apply cell_eqb_neq.
          apply (Havoid k); lia.
      + (* the walk continues on the next orbit cell *)
        assert (Hkm : (S k < m)%nat).
        { destruct (Nat.eq_dec (S k) m) as [He | Hne]; [| lia].
          exfalso. rewrite He, Hper in Estop.
          rewrite cell_eqb_refl in Estop. discriminate. }
        destruct (IH (S k) (Sigma.set2 X (Nat.iter k f rc) lc) Hkm
          ltac:(lia)
          (set2_preserves_wf n_rows X (Nat.iter k f rc) lc HXwf
            (proj1 Hikdom)))
          as (IHwf & IHlab & IHother).
        split; [exact IHwf | split].
        * intros j Hkj Hjm.
          destruct (Nat.eq_dec j k) as [-> | Hjk]; [| apply IHlab; lia].
          rewrite IHother.
          -- exact (get2_set2_eq_wf n_rows _ X _ lc HXwf Hikdom).
          -- intros j' Hj'1 Hj'2 Heq.
             exact (Hdist k j' ltac:(lia) Hj'2 (eq_sym Heq)).
        * intros c Havoid.
          rewrite IHother by (intros j' Hj'1 Hj'2; apply Havoid; lia).
          apply get2_set2_neq. apply cell_eqb_neq.
          apply (Havoid k); lia.
  Qed.

  (** The label [aux] assigns to a cell. *)
  Definition auxread (self : Sigma.t) (c : Sigma.cell) : Sigma.cell :=
    Sigma.get2 c self.(Sigma.aux) c.

  (** The forward fold invariant: both planes are well-formed, the
      permutation is an injective self-map of the domain, and [aux] is
      constant on each orbit and names it by one of its members. *)
  Definition assembly_inv (n_rows : nat) (self : Sigma.t) : Prop :=
    Sigma.columns self = cols /\
    matrix_wf n_rows self.(Sigma.mapping) /\
    matrix_wf n_rows self.(Sigma.aux) /\
    (forall c, cell_dom n_rows c -> cell_dom n_rows (Sigma.perm self c)) /\
    (forall c d, cell_dom n_rows c -> cell_dom n_rows d ->
      Sigma.perm self c = Sigma.perm self d -> c = d) /\
    (forall c, cell_dom n_rows c ->
      reach (Sigma.perm self) c (auxread self c)) /\
    (forall c d, cell_dom n_rows c -> cell_dom n_rows d ->
      reach (Sigma.perm self) c d -> auxread self c = auxread self d).

  Lemma identity_matrix_wf (n_rows : nat) :
    matrix_wf n_rows
      (List.map (fun i => List.map (fun j => (i, j)) (List.seq 0 n_rows))
        (List.seq 0 (List.length cols))).
  Proof.
    split.
    - rewrite length_map, length_seq. reflexivity.
    - apply Forall_forall. intros row Hrow.
      apply in_map_iff in Hrow. destruct Hrow as [i [<- _]].
      rewrite length_map, length_seq. reflexivity.
  Qed.

  Lemma assembly_inv_init (n_rows : nat) :
    assembly_inv n_rows (Sigma.init cols n_rows).
  Proof.
    assert (Hread : forall c, auxread (Sigma.init cols n_rows) c = c)
      by (exact (perm_init n_rows)).
    split; [reflexivity | split; [| split; [| split; [| split; [| split]]]]].
    - exact (identity_matrix_wf n_rows).
    - exact (identity_matrix_wf n_rows).
    - intros c Hc. rewrite perm_init. exact Hc.
    - intros c d _ _ H. rewrite !(perm_init n_rows) in H. exact H.
    - intros c _. rewrite Hread. exists O. reflexivity.
    - intros c d _ _ [k Hk].
      rewrite (iter_pointwise_id _ (perm_init n_rows)) in Hk.
      subst d. reflexivity.
  Qed.

  (** One splice: [self'] carries the spliced mapping — the images of
      [u] and [v] swapped — and the relabeled [aux]; [u] and [v] carry
      distinct labels, hence lie in distinct orbits.  The invariant
      transfers, all reachability is preserved, and [u] and [v] become
      mutually reachable. *)
  Lemma splice_inv (n_rows : nat) (self self' : Sigma.t)
      (u v : Sigma.cell) :
    assembly_inv n_rows self ->
    cell_dom n_rows u -> cell_dom n_rows v ->
    auxread self u <> auxread self v ->
    Sigma.columns self' = cols ->
    matrix_wf n_rows self'.(Sigma.mapping) ->
    self'.(Sigma.aux) =
      Sigma.relabel_cycle (S (Sigma.total_cells self)) self.(Sigma.mapping)
        self.(Sigma.aux) (auxread self v) (auxread self v)
        (auxread self u) ->
    Sigma.perm self' u = Sigma.perm self v ->
    Sigma.perm self' v = Sigma.perm self u ->
    (forall c, c <> u -> c <> v -> Sigma.perm self' c = Sigma.perm self c) ->
    assembly_inv n_rows self' /\
    (forall x y, cell_dom n_rows x -> reach (Sigma.perm self) x y ->
      reach (Sigma.perm self') x y) /\
    reach (Sigma.perm self') u v /\ reach (Sigma.perm self') v u.
  Proof.
    intros Hinv Hdu Hdv Hlab Hcols' HM'wf Haux' Hf'u Hf'v Hf'o.
    pose proof Hinv as (Hcols & HMwf & HXwf & Hclosed & Hinj & HA1 & HA2).
    set (f := Sigma.perm self) in *.
    set (f' := Sigma.perm self') in *.
    set (rc := auxread self v) in *.
    set (lc := auxread self u) in *.
    assert (Huv : u <> v)
      by (intro He; exact (Hlab (f_equal (auxread self) He))).
    assert (Hsep_uv : ~ reach f u v)
      by (intro Hr; exact (Hlab (HA2 u v Hdu Hdv Hr))).
    assert (Hsep_vu : ~ reach f v u).
    { intro Hr. apply Hlab. symmetry. exact (HA2 v u Hdv Hdu Hr). }
    (* the merged permutation is an injective self-map of the domain *)
    assert (Hclosed' : forall c, cell_dom n_rows c -> cell_dom n_rows (f' c))
      by (exact (FiniteOrbit.merge_closed cell_eq_dec (cell_dom n_rows) f
        Hclosed u v Hdu Hdv f' Hf'u Hf'v Hf'o)).
    assert (Hinj' : forall c d, cell_dom n_rows c -> cell_dom n_rows d ->
      f' c = f' d -> c = d)
      by (exact (FiniteOrbit.merge_inj cell_eq_dec (cell_dom n_rows) f
        Hinj u v Hdu Hdv Huv f' Hf'u Hf'v Hf'o)).
    (* symmetry and decidability of reachability, on both permutations *)
    pose proof (FiniteOrbit.reach_sym cell_eq_dec (cell_dom n_rows)
      (cell_enum n_rows) (cell_enum_complete n_rows) f Hclosed Hinj) as Hsym.
    pose proof (FiniteOrbit.reach_sym cell_eq_dec (cell_dom n_rows)
      (cell_enum n_rows) (cell_enum_complete n_rows) f' Hclosed' Hinj')
      as Hsym'.
    pose proof (FiniteOrbit.reach_dec cell_eq_dec (cell_dom n_rows)
      (cell_enum n_rows) (cell_enum_complete n_rows) f Hclosed Hinj) as Hdec.
    pose proof (FiniteOrbit.reach_dom (cell_dom n_rows) f Hclosed) as Hdomr.
    (* the two spliced cells become mutually reachable *)
    assert (Hr'_uv : reach f' u v)
      by (exact (FiniteOrbit.merge_reach_ab cell_eq_dec (cell_dom n_rows)
        (cell_enum n_rows) (cell_enum_complete n_rows) f Hclosed Hinj
        u v Hdv Hsep_vu f' Hf'u Hf'o)).
    assert (Hfrom_u : forall z, cell_dom n_rows z ->
      reach f u z \/ reach f v z -> reach f' u z)
      by (exact (FiniteOrbit.merge_reach_from_a cell_eq_dec (cell_dom n_rows)
        (cell_enum n_rows) (cell_enum_complete n_rows) f Hclosed Hinj
        u v Hdu Hdv Hsep_uv Hsep_vu f' Hf'u Hf'v Hf'o)).
    assert (Hpres : forall x y, cell_dom n_rows x -> reach f x y ->
      reach f' x y)
      by (exact (FiniteOrbit.merge_preserve cell_eq_dec (cell_dom n_rows)
        (cell_enum n_rows) (cell_enum_complete n_rows) f Hclosed Hinj
        u v Hdu Hdv Huv Hsep_uv Hsep_vu f' Hf'u Hf'v Hf'o)).
    (* the relabeled [aux] plane *)
    assert (Hrvrc : reach f v rc) by (exact (HA1 v Hdv)).
    assert (Hrulc : reach f u lc) by (exact (HA1 u Hdu)).
    assert (Hdrc : cell_dom n_rows rc) by (exact (Hdomr v rc Hdv Hrvrc)).
    assert (Hdlc : cell_dom n_rows lc) by (exact (Hdomr u lc Hdu Hrulc)).
    assert (Hrcv : reach f rc v) by (exact (Hsym v rc Hdv Hrvrc)).
    assert (Hrc_to_v : forall c, reach f rc c -> reach f v c)
      by (intros c Hr; exact (FiniteOrbit.reach_trans f v rc c Hrvrc Hr)).
    assert (Hv_to_rc : forall c, reach f v c -> reach f rc c)
      by (intros c Hr; exact (FiniteOrbit.reach_trans f rc v c Hrcv Hr)).
    destruct (FiniteOrbit.minimal_period cell_eq_dec (cell_dom n_rows)
      (cell_enum n_rows) (cell_enum_complete n_rows) f Hclosed Hinj rc Hdrc)
      as (m & Hm & Hmbound & Hmper & Hmmin).
    assert (Hdist : forall i j, (i < j)%nat -> (j < m)%nat ->
      Nat.iter i f rc <> Nat.iter j f rc).
    { intros i j Hij Hjm Heq.
      apply (Hmmin (j - i)%nat); [lia |].
      exact (FiniteOrbit.iter_cancel (cell_dom n_rows) f Hclosed Hinj
        i j rc Hdrc ltac:(lia) Heq). }
    assert (Htc : Sigma.total_cells self = (List.length cols * n_rows)%nat).
    { unfold Sigma.total_cells.
      rewrite (list_sum_const _ n_rows).
      - rewrite length_map, (proj1 HMwf). reflexivity.
      - apply Forall_map. exact (proj2 HMwf). }
    assert (Hfuel : (m - 0 <= S (Sigma.total_cells self))%nat).
    { rewrite cell_enum_length in Hmbound. lia. }
    destruct (relabel_cycle_spec n_rows self.(Sigma.mapping) f rc lc m
      (fun c => eq_refl) HMwf Hclosed Hdrc Hm Hmper Hdist
      (S (Sigma.total_cells self)) O self.(Sigma.aux) Hm Hfuel HXwf)
      as (HX'wf & Hlab1 & Hlab2).
    change (Nat.iter O f rc) with rc in HX'wf.
    change (Nat.iter O f rc) with rc in Hlab1.
    change (Nat.iter O f rc) with rc in Hlab2.
    rewrite <- Haux' in HX'wf, Hlab1, Hlab2.
    assert (Hax_in : forall c, reach f rc c -> auxread self' c = lc).
    { intros c Hr.
      destruct (FiniteOrbit.reach_reduce f rc c m Hm Hmper Hr)
        as (j & Hj & Hje).
      unfold auxread. rewrite <- Hje. apply Hlab1; lia. }
    assert (Hax_out : forall c, ~ reach f rc c ->
      auxread self' c = auxread self c).
    { intros c Hnr. unfold auxread. apply Hlab2.
      intros j _ _ Heq. apply Hnr. exists j. exact Heq. }
    (* labels across the fused orbit and the untouched orbits *)
    assert (Hto_lc : forall c, cell_dom n_rows c ->
      reach f u c \/ reach f v c -> reach f' c lc).
    { intros c Hc Hor.
      apply (FiniteOrbit.reach_trans f' c u lc).
      - exact (Hsym' u c Hdu (Hfrom_u c Hc Hor)).
      - apply Hfrom_u; [exact Hdlc | left; exact Hrulc]. }
    assert (Hlab_fused : forall z, cell_dom n_rows z ->
      reach f u z \/ reach f v z -> auxread self' z = lc).
    { intros z Hz [Huz | Hvz].
      - assert (Hnrc : ~ reach f rc z).
        { intro Hr0.
          apply Hsep_vu.
          apply (FiniteOrbit.reach_trans f v z u).
          - exact (Hrc_to_v z Hr0).
          - exact (Hsym u z Hdu Huz). }
        rewrite (Hax_out z Hnrc).
        symmetry. exact (HA2 u z Hdu Hz Huz).
      - exact (Hax_in z (Hv_to_rc z Hvz)). }
    assert (HA1' : forall c, cell_dom n_rows c ->
      reach f' c (auxread self' c)).
    { intros c Hc.
      destruct (Hdec v c Hdv) as [Hvc | Hvc].
      - rewrite (Hlab_fused c Hc (or_intror Hvc)).
        apply Hto_lc; [exact Hc | right; exact Hvc].
      - destruct (Hdec u c Hdu) as [Huc | Huc].
        + rewrite (Hlab_fused c Hc (or_introl Huc)).
          apply Hto_lc; [exact Hc | left; exact Huc].
        + assert (Hncu : ~ reach f c u)
            by (intro Hr; exact (Huc (Hsym c u Hc Hr))).
          assert (Hncv : ~ reach f c v)
            by (intro Hr; exact (Hvc (Hsym c v Hc Hr))).
          assert (Hnrc : ~ reach f rc c)
            by (intro Hr; exact (Hvc (Hrc_to_v c Hr))).
          rewrite (Hax_out c Hnrc).
          destruct (HA1 c Hc) as [k Hk].
          exists k.
          rewrite (FiniteOrbit.untouched_iter (cell_dom n_rows) f u v f'
            Hf'o c Hc Hncu Hncv k).
          exact Hk. }
    assert (HA2' : forall c d, cell_dom n_rows c -> cell_dom n_rows d ->
      reach f' c d -> auxread self' c = auxread self' d).
    { intros c d Hc Hd Hr'.
      destruct (Hdec u c Hdu) as [Huc | Huc];
        [| destruct (Hdec v c Hdv) as [Hvc | Hvc]].
      - (* c in the fused orbit, via u *)
        destruct Hr' as [n Hn].
        destruct (FiniteOrbit.merge_orbit_iter cell_eq_dec (cell_dom n_rows)
          f Hclosed u v Hdu Hdv f' Hf'u Hf'v Hf'o c n Hc (or_introl Huc))
          as [_ Horn].
        rewrite Hn in Horn.
        rewrite (Hlab_fused c Hc (or_introl Huc)),
          (Hlab_fused d Hd Horn).
        reflexivity.
      - (* c in the fused orbit, via v *)
        destruct Hr' as [n Hn].
        destruct (FiniteOrbit.merge_orbit_iter cell_eq_dec (cell_dom n_rows)
          f Hclosed u v Hdu Hdv f' Hf'u Hf'v Hf'o c n Hc (or_intror Hvc))
          as [_ Horn].
        rewrite Hn in Horn.
        rewrite (Hlab_fused c Hc (or_intror Hvc)),
          (Hlab_fused d Hd Horn).
        reflexivity.
      - (* untouched orbit *)
        assert (Hncu : ~ reach f c u)
          by (intro Hr; exact (Huc (Hsym c u Hc Hr))).
        assert (Hncv : ~ reach f c v)
          by (intro Hr; exact (Hvc (Hsym c v Hc Hr))).
        assert (Hrcd : reach f c d).
        { destruct Hr' as [n Hn]. exists n.
          rewrite <- (FiniteOrbit.untouched_iter (cell_dom n_rows) f u v f'
            Hf'o c Hc Hncu Hncv n).
          exact Hn. }
        assert (Hnrcc : ~ reach f rc c)
          by (intro Hr; exact (Hvc (Hrc_to_v c Hr))).
        assert (Hnrcd : ~ reach f rc d).
        { intro Hr. apply Hncv.
          apply (FiniteOrbit.reach_trans f c d v Hrcd).
          exact (Hsym v d Hdv (Hrc_to_v d Hr)). }
        rewrite (Hax_out c Hnrcc), (Hax_out d Hnrcd).
        exact (HA2 c d Hc Hd Hrcd). }
    refine (conj _ (conj Hpres (conj Hr'_uv (Hsym' u v Hdu Hr'_uv)))).
    split; [exact Hcols' | split; [exact HM'wf | split;
      [exact HX'wf | split; [exact Hclosed' | split;
      [exact Hinj' | split; [exact HA1' | exact HA2']]]]]].
  Qed.

  (** One [Sigma.copy] step: the invariant transfers, all reachability
      is preserved, and the copied pair's two resolved cells are
      reach-connected. *)
  Lemma copy_forward_step (n_rows : nat) (self self' : Sigma.t)
      (left right : Raw.Cell.t) :
    assembly_inv n_rows self ->
    Sigma.copy self left right = Some self' ->
    assembly_inv n_rows self' /\
    (forall x y, cell_dom n_rows x -> reach (Sigma.perm self) x y ->
      reach (Sigma.perm self') x y) /\
    (exists cl cr,
      resolve_cell left = Some cl /\ resolve_cell right = Some cr /\
      cell_dom n_rows cl /\ cell_dom n_rows cr /\
      reach (Sigma.perm self') cl cr).
  Proof.
    intros Hinv Hcopy.
    pose proof Hinv as (Hcols & HMwf & HXwf & Hclosed & Hinj & HA1 & HA2).
    unfold Sigma.copy in Hcopy. rewrite Hcols in Hcopy.
    destruct (Sigma.column_position cols left.(Raw.Cell.column))
      as [pl|] eqn:El; [| discriminate].
    destruct (Sigma.column_position cols right.(Raw.Cell.column))
      as [pr|] eqn:Er; [| discriminate].
    destruct (negb _) eqn:Eb; [discriminate |].
    apply negb_false_iff in Eb.
    apply andb_prop in Eb as [Ebl Ebr].
    apply andb_prop in Ebl as [Ebl0 Ebl1].
    apply andb_prop in Ebr as [Ebr0 Ebr1].
    apply Z.leb_le in Ebl0. apply Z.ltb_lt in Ebl1.
    apply Z.leb_le in Ebr0. apply Z.ltb_lt in Ebr1.
    set (left_cell := (pl, Z.to_nat left.(Raw.Cell.row))) in *.
    set (right_cell := (pr, Z.to_nat right.(Raw.Cell.row))) in *.
    assert (Hpl : (pl < List.length cols)%nat)
      by (eapply column_position_lt; exact El).
    assert (Hpr : (pr < List.length cols)%nat)
      by (eapply column_position_lt; exact Er).
    rewrite (matrix_wf_nth n_rows _ pl HMwf Hpl) in Ebl1.
    rewrite (matrix_wf_nth n_rows _ pr HMwf Hpr) in Ebr1.
    assert (Hrowl : (Z.to_nat left.(Raw.Cell.row) < n_rows)%nat).
    { apply Nat2Z.inj_lt. rewrite Z2Nat.id by exact Ebl0. exact Ebl1. }
    assert (Hrowr : (Z.to_nat right.(Raw.Cell.row) < n_rows)%nat).
    { apply Nat2Z.inj_lt. rewrite Z2Nat.id by exact Ebr0. exact Ebr1. }
    assert (Hdl : cell_dom n_rows left_cell)
      by (split; [exact Hpl | exact Hrowl]).
    assert (Hdr : cell_dom n_rows right_cell)
      by (split; [exact Hpr | exact Hrowr]).
    assert (Hresl : resolve_cell left = Some left_cell)
      by (unfold resolve_cell; rewrite El; reflexivity).
    assert (Hresr : resolve_cell right = Some right_cell)
      by (unfold resolve_cell; rewrite Er; reflexivity).
    destruct (Sigma.cell_eqb
      (Sigma.get2 left_cell self.(Sigma.aux) left_cell)
      (Sigma.get2 right_cell self.(Sigma.aux) right_cell)) eqn:Ecyc.
    { (* early return: the two cells already share an orbit *)
      injection Hcopy as Hcopy; subst self'.
      split; [exact Hinv | split; [intros x y _ Hr; exact Hr |]].
      exists left_cell, right_cell.
      split; [exact Hresl | split; [exact Hresr |
        split; [exact Hdl | split; [exact Hdr |]]]].
      apply cell_eqb_eq in Ecyc.
      assert (Eaux : auxread self left_cell = auxread self right_cell)
        by (exact Ecyc).
      pose proof (HA1 left_cell Hdl) as H1.
      pose proof (HA1 right_cell Hdr) as H2.
      rewrite Eaux in H1.
      apply (FiniteOrbit.reach_trans (Sigma.perm self) left_cell _
        right_cell H1).
      exact (FiniteOrbit.reach_sym cell_eq_dec (cell_dom n_rows)
        (cell_enum n_rows) (cell_enum_complete n_rows) (Sigma.perm self)
        Hclosed Hinj right_cell _ Hdr H2). }
    assert (Hlabne : auxread self left_cell <> auxread self right_cell).
    { intro He.
      assert (Efalse : Sigma.cell_eqb (auxread self left_cell)
        (auxread self right_cell) = false) by (exact Ecyc).
      rewrite He in Efalse. rewrite cell_eqb_refl in Efalse. discriminate. }
    assert (Hab_ne : left_cell <> right_cell)
      by (intro He; apply Hlabne; rewrite He; reflexivity).
    destruct (Nat.ltb _ _).
    - (* the sizes swap: the label of [left_cell]'s side is absorbed *)
      injection Hcopy as Hcopy. subst self'.
      match goal with
      | |- assembly_inv _ ?s /\ _ => set (self1 := s)
      end.
      assert (Hcols1 : Sigma.columns self1 = cols) by reflexivity.
      assert (HM1wf : matrix_wf n_rows self1.(Sigma.mapping)).
      { apply set2_preserves_wf; [| exact (proj1 Hdr)].
        apply set2_preserves_wf; [exact HMwf | exact (proj1 Hdl)]. }
      assert (Haux1 : self1.(Sigma.aux) =
        Sigma.relabel_cycle (S (Sigma.total_cells self)) self.(Sigma.mapping)
          self.(Sigma.aux) (auxread self left_cell)
          (auxread self left_cell) (auxread self right_cell))
        by reflexivity.
      assert (Hp_uv : Sigma.perm self1 right_cell = Sigma.perm self left_cell).
      { unfold Sigma.perm, self1. cbn [Sigma.mapping].
        apply (get2_set2_eq_wf n_rows).
        - apply set2_preserves_wf; [exact HMwf | exact (proj1 Hdl)].
        - exact Hdr. }
      assert (Hp_vu : Sigma.perm self1 left_cell = Sigma.perm self right_cell).
      { unfold Sigma.perm, self1. cbn [Sigma.mapping].
        rewrite get2_set2_neq
          by (apply cell_eqb_neq; intro He; exact (Hab_ne (eq_sym He))).
        apply (get2_set2_eq_wf n_rows); [exact HMwf | exact Hdl]. }
      assert (Hp_other : forall c, c <> left_cell -> c <> right_cell ->
        Sigma.perm self1 c = Sigma.perm self c).
      { intros c Hc1 Hc2. unfold Sigma.perm, self1. cbn [Sigma.mapping].
        rewrite get2_set2_neq
          by (apply cell_eqb_neq; intro He; exact (Hc2 (eq_sym He))).
        rewrite get2_set2_neq
          by (apply cell_eqb_neq; intro He; exact (Hc1 (eq_sym He))).
        reflexivity. }
      destruct (splice_inv n_rows self self1 right_cell left_cell Hinv
        Hdr Hdl (fun He => Hlabne (eq_sym He)) Hcols1 HM1wf Haux1
        Hp_uv Hp_vu (fun c H1 H2 => Hp_other c H2 H1))
        as (Hinv1 & Hpres1 & Hr_uv1 & Hr_vu1).
      split; [exact Hinv1 | split; [exact Hpres1 |]].
      exists left_cell, right_cell.
      split; [exact Hresl | split; [exact Hresr |
        split; [exact Hdl | split; [exact Hdr | exact Hr_vu1]]]].
    - (* no swap: the label of [right_cell]'s side is absorbed *)
      injection Hcopy as Hcopy. subst self'.
      match goal with
      | |- assembly_inv _ ?s /\ _ => set (self1 := s)
      end.
      assert (Hcols1 : Sigma.columns self1 = cols) by reflexivity.
      assert (HM1wf : matrix_wf n_rows self1.(Sigma.mapping)).
      { apply set2_preserves_wf; [| exact (proj1 Hdr)].
        apply set2_preserves_wf; [exact HMwf | exact (proj1 Hdl)]. }
      assert (Haux1 : self1.(Sigma.aux) =
        Sigma.relabel_cycle (S (Sigma.total_cells self)) self.(Sigma.mapping)
          self.(Sigma.aux) (auxread self right_cell)
          (auxread self right_cell) (auxread self left_cell))
        by reflexivity.
      assert (Hp_uv : Sigma.perm self1 left_cell = Sigma.perm self right_cell).
      { unfold Sigma.perm, self1. cbn [Sigma.mapping].
        rewrite get2_set2_neq
          by (apply cell_eqb_neq; intro He; exact (Hab_ne (eq_sym He))).
        apply (get2_set2_eq_wf n_rows); [exact HMwf | exact Hdl]. }
      assert (Hp_vu : Sigma.perm self1 right_cell = Sigma.perm self left_cell).
      { unfold Sigma.perm, self1. cbn [Sigma.mapping].
        apply (get2_set2_eq_wf n_rows).
        - apply set2_preserves_wf; [exact HMwf | exact (proj1 Hdl)].
        - exact Hdr. }
      assert (Hp_other : forall c, c <> left_cell -> c <> right_cell ->
        Sigma.perm self1 c = Sigma.perm self c).
      { intros c Hc1 Hc2. unfold Sigma.perm, self1. cbn [Sigma.mapping].
        rewrite get2_set2_neq
          by (apply cell_eqb_neq; intro He; exact (Hc2 (eq_sym He))).
        rewrite get2_set2_neq
          by (apply cell_eqb_neq; intro He; exact (Hc1 (eq_sym He))).
        reflexivity. }
      destruct (splice_inv n_rows self self1 left_cell right_cell Hinv
        Hdl Hdr Hlabne Hcols1 HM1wf Haux1 Hp_uv Hp_vu Hp_other)
        as (Hinv1 & Hpres1 & Hr_uv1 & Hr_vu1).
      split; [exact Hinv1 | split; [exact Hpres1 |]].
      exists left_cell, right_cell.
      split; [exact Hresl | split; [exact Hresr |
        split; [exact Hdl | split; [exact Hdr | exact Hr_uv1]]]].
  Qed.

  (** The forward fold: the invariant and the connectivity of every
      processed copy carry to the final assembly. *)
  Lemma fold_forward (n_rows : nat) (copies : list (Raw.Cell.t * Raw.Cell.t)) :
    forall (s0 assembly : Sigma.t),
      assembly_inv n_rows s0 ->
      List.fold_left
        (fun state pair =>
          match state with
          | None => None
          | Some self => Sigma.copy self (fst pair) (snd pair)
          end)
        copies (Some s0) = Some assembly ->
      assembly_inv n_rows assembly /\
      (forall x y, cell_dom n_rows x -> reach (Sigma.perm s0) x y ->
        reach (Sigma.perm assembly) x y) /\
      Forall
        (fun p =>
          exists cl cr,
            resolve_cell (fst p) = Some cl /\
            resolve_cell (snd p) = Some cr /\
            reach (Sigma.perm assembly) cl cr)
        copies.
  Proof.
    induction copies as [|p copies IH]; simpl; intros s0 assembly Hinv Hfold.
    - injection Hfold as Hfold; subst assembly.
      split; [exact Hinv | split; [| constructor]].
      intros x y _ Hr; exact Hr.
    - destruct (Sigma.copy s0 (fst p) (snd p)) as [s1|] eqn:Ec;
        [| rewrite fold_copy_none in Hfold; discriminate].
      destruct (copy_forward_step n_rows s0 s1 (fst p) (snd p) Hinv Ec)
        as (Hinv1 & Hpres01 & (cl & cr & Hcl & Hcr & Hdcl & Hdcr & Hr1)).
      destruct (IH s1 assembly Hinv1 Hfold) as (HinvA & Hpres1A & Hall).
      split; [exact HinvA | split].
      + intros x y Hx Hr. apply (Hpres1A x y Hx). apply (Hpres01 x y Hx Hr).
      + constructor; [| exact Hall].
        exists cl, cr.
        split; [exact Hcl | split; [exact Hcr |]].
        apply (Hpres1A cl cr Hdcl Hr1).
  Qed.

  (** ** Forward direction: grid invariance forces the copy equalities

      The two cells of every processed copy lie in a common orbit of the
      constructed permutation; grid invariance is constant on orbits. *)
  Lemma sigma_copies_connected (n_rows : nat)
      (copies : list (Raw.Cell.t * Raw.Cell.t)) (assembly : Sigma.t) :
    Sigma.sigma_of_copies cols n_rows copies = Some assembly ->
    Forall
      (fun p =>
        match resolve_cell (fst p), resolve_cell (snd p) with
        | Some cl, Some cr =>
            reach (Sigma.perm assembly) cl cr \/ reach (Sigma.perm assembly) cr cl
        | _, _ => True
        end)
      copies.
  Proof.
    intro Hsig.
    unfold Sigma.sigma_of_copies in Hsig.
    destruct (fold_forward n_rows copies (Sigma.init cols n_rows) assembly
      (assembly_inv_init n_rows) Hsig) as (_ & _ & Hall).
    eapply Forall_impl; [| exact Hall].
    intros p (cl & cr & Hcl & Hcr & Hr).
    rewrite Hcl, Hcr. left. exact Hr.
  Qed.

  (** ** The correctness theorem *)

  Theorem sigma_correct (n_rows : nat)
      (copies : list (Raw.Cell.t * Raw.Cell.t)) (assembly : Sigma.t) :
    Sigma.sigma_of_copies cols n_rows copies = Some assembly ->
    grid_invariant assembly <-> Forall copy_holds copies.
  Proof.
    intro Hsig. split.
    - (* forward: invariance ⇒ copies hold *)
      intro GI.
      pose proof (sigma_copies_connected n_rows copies assembly Hsig) as Hconn.
      apply Forall_forall. intros p Hp.
      rewrite Forall_forall in Hconn. specialize (Hconn p Hp).
      unfold copy_holds.
      destruct (resolve_cell (fst p)) as [cl|] eqn:Ecl; [|exact I].
      destruct (resolve_cell (snd p)) as [cr|] eqn:Ecr; [|exact I].
      destruct Hconn as [Hr | Hr].
      + eapply reach_grid_invariant; eassumption.
      + symmetry. eapply reach_grid_invariant; eassumption.
    - (* backward: copies hold ⇒ invariance *)
      intro Hall.
      unfold Sigma.sigma_of_copies in Hsig.
      eapply fold_backward.
      + apply WF_init.
      + intro c. rewrite perm_init. reflexivity.
      + exact Hall.
      + exact Hsig.
  Qed.

End GridCorrectness.
