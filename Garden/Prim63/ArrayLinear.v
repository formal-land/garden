(** * Linear-use helpers for Rocq primitive arrays

    [PrimArray.array] is persistent at the Rocq level.  Its runtime
    representation is efficient when a computation threads only the most
    recently returned version through subsequent writes.  This file supplies
    the extensional interface used to reason about such computations: natural
    indices are embedded into [PrimInt63.int], an exact list view records the
    observable array contents, and [set_at] is related to a purely functional
    list update.

    Out-of-bounds primitive reads return the array default and out-of-bounds
    writes are ignored.  Consequently, every same-index write theorem below
    has an explicit [in_bounds] premise; callers should not erase it. *)

From Corelib Require Import PrimArray ArrayAxioms.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Numbers.Cyclic.Int63.Uint63.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import micromega.Lia.

Import ListNotations.
Local Open Scope uint63_scope.

Set Universe Polymorphism.

Module ArrayLinear.

  (** ** Natural and primitive indices *)

  Definition word_capacity : Z := Uint63Axioms.wB.

  Definition fits_nat (n : nat) : Prop :=
    (Z.of_nat n < word_capacity)%Z.

  Definition index (n : nat) : PrimInt63.int :=
    Uint63Axioms.of_Z (Z.of_nat n).

  Definition index_nat (i : PrimInt63.int) : nat :=
    Z.to_nat (Uint63Axioms.to_Z i).

  Lemma fits_nat_lt (n m : nat) :
    n < m -> fits_nat m -> fits_nat n.
  Proof.
    intros Hnm Hm.
    apply Nat2Z.inj_lt in Hnm.
    unfold fits_nat in *.
    lia.
  Qed.

  Lemma fits_nat_le (n m : nat) :
    n <= m -> fits_nat m -> fits_nat n.
  Proof.
    intros Hnm Hm.
    apply Nat2Z.inj_le in Hnm.
    unfold fits_nat in *.
    lia.
  Qed.

  Lemma to_Z_index (n : nat) :
    fits_nat n ->
    Uint63Axioms.to_Z (index n) = Z.of_nat n.
  Proof.
    intros Hfit.
    unfold index.
    rewrite Uint63.of_Z_spec.
    apply Z.mod_small.
    unfold fits_nat, word_capacity in Hfit.
    lia.
  Qed.

  Lemma index_nat_index (n : nat) :
    fits_nat n -> index_nat (index n) = n.
  Proof.
    intros Hfit.
    unfold index_nat.
    rewrite to_Z_index by exact Hfit.
    apply Nat2Z.id.
  Qed.

  Lemma index_index_nat (i : PrimInt63.int) :
    index (index_nat i) = i.
  Proof.
    apply Uint63.to_Z_inj.
    rewrite to_Z_index.
    - unfold index_nat.
      rewrite Z2Nat.id.
      + reflexivity.
      + pose proof (Uint63.to_Z_bounded i).
        lia.
    - unfold fits_nat, index_nat, word_capacity.
      rewrite Z2Nat.id.
      + apply (proj2 (Uint63.to_Z_bounded i)).
      + apply (proj1 (Uint63.to_Z_bounded i)).
  Qed.

  Lemma index_inj (n m : nat) :
    fits_nat n -> fits_nat m -> index n = index m -> n = m.
  Proof.
    intros Hn Hm Heq.
    apply Nat2Z.inj.
    rewrite <- (to_Z_index n Hn), <- (to_Z_index m Hm), Heq.
    reflexivity.
  Qed.

  Lemma index_succ (n : nat) :
    fits_nat (S n) ->
    PrimInt63.add (index n) 1%uint63 = index (S n).
  Proof.
    intro Hfit.
    apply Uint63.to_Z_inj.
    rewrite Uint63.add_spec, Uint63.to_Z_1.
    rewrite (to_Z_index n), (to_Z_index (S n)).
    - rewrite Z.mod_small.
      + f_equal; lia.
      + unfold fits_nat, word_capacity in Hfit.
        split; lia.
    - exact Hfit.
    - exact (fits_nat_lt n (S n) (Nat.lt_succ_diag_r n) Hfit).
  Qed.

  Lemma index_add (n m : nat) :
    fits_nat (n + m) ->
    PrimInt63.add (index n) (index m) = index (n + m).
  Proof.
    intro Hfit.
    apply Uint63.to_Z_inj.
    rewrite Uint63.add_spec.
    rewrite (to_Z_index n), (to_Z_index m), (to_Z_index (n + m)).
    - rewrite Z.mod_small.
      + rewrite Nat2Z.inj_add; reflexivity.
      + unfold fits_nat, word_capacity in Hfit.
        rewrite Nat2Z.inj_add in Hfit.
        split; lia.
    - exact Hfit.
    - unfold fits_nat, word_capacity in *.
      rewrite Nat2Z.inj_add in Hfit.
      lia.
    - unfold fits_nat, word_capacity in *.
      rewrite Nat2Z.inj_add in Hfit.
      lia.
  Qed.

  Lemma index_ltb_iff (n m : nat) :
    fits_nat n -> fits_nat m ->
    PrimInt63.ltb (index n) (index m) = true <-> n < m.
  Proof.
    intros Hn Hm.
    rewrite Uint63Axioms.ltb_spec, !to_Z_index by assumption.
    symmetry.
    exact (Nat2Z.inj_lt n m).
  Qed.

  (** Primitive-array bounds and direct specifications. *)

  Definition in_bounds {A : Type} (a : PrimArray.array A)
      (i : PrimInt63.int) : Prop :=
    PrimInt63.ltb i (PrimArray.length a) = true.

  Definition get_at {A : Type} (a : PrimArray.array A) (n : nat) : A :=
    PrimArray.get a (index n).

  Definition set_at {A : Type} (a : PrimArray.array A) (n : nat) (x : A) :
      PrimArray.array A :=
    PrimArray.set a (index n) x.

  Lemma get_set_same {A : Type} (a : PrimArray.array A)
      (i : PrimInt63.int) (x : A) :
    in_bounds a i -> PrimArray.get (PrimArray.set a i x) i = x.
  Proof.
    intros Hbound.
    exact (@ArrayAxioms.get_set_same A a i x Hbound).
  Qed.

  Lemma get_set_other {A : Type} (a : PrimArray.array A)
      (i j : PrimInt63.int) (x : A) :
    i <> j -> PrimArray.get (PrimArray.set a i x) j = PrimArray.get a j.
  Proof.
    intros Hneq.
    exact (@ArrayAxioms.get_set_other A a i j x Hneq).
  Qed.

  Lemma length_set {A : Type} (a : PrimArray.array A)
      (i : PrimInt63.int) (x : A) :
    PrimArray.length (PrimArray.set a i x) = PrimArray.length a.
  Proof. exact (@ArrayAxioms.length_set A a i x). Qed.

  Lemma default_set {A : Type} (a : PrimArray.array A)
      (i : PrimInt63.int) (x : A) :
    PrimArray.default (PrimArray.set a i x) = PrimArray.default a.
  Proof. exact (@ArrayAxioms.default_set A a i x). Qed.

  (** ** Pure list update *)

  Fixpoint list_set {A : Type} (n : nat) (x : A) (xs : list A) : list A :=
    match n, xs with
    | O, _ :: xs' => x :: xs'
    | S n', y :: xs' => y :: list_set n' x xs'
    | _, [] => []
    end.

  Lemma length_list_set {A : Type} (xs : list A) (n : nat) (x : A) :
    List.length (list_set n x xs) = List.length xs.
  Proof.
    revert n.
    induction xs as [|y xs IH]; intros [|n]; simpl; auto.
  Qed.

  Lemma nth_error_list_set_same {A : Type} (xs : list A)
      (n : nat) (x : A) :
    n < List.length xs ->
    List.nth_error (list_set n x xs) n = Some x.
  Proof.
    revert n.
    induction xs as [|y xs IH]; intros [|n] Hn; simpl in *; try lia.
    - reflexivity.
    - apply IH.
      lia.
  Qed.

  Lemma nth_error_list_set_other {A : Type} (xs : list A)
      (n m : nat) (x : A) :
    n <> m ->
    List.nth_error (list_set n x xs) m = List.nth_error xs m.
  Proof.
    revert n m.
    induction xs as [|y xs IH]; intros [|n] [|m] Hneq;
      simpl in *; try reflexivity; try contradiction.
    apply IH.
    lia.
  Qed.

  (** ** Exact array/list views *)

  Record view {A : Type} (a : PrimArray.array A) (xs : list A) : Prop := {
    view_fits : fits_nat (List.length xs);
    view_length : PrimArray.length a = index (List.length xs);
    view_nth : forall (n : nat) (x : A),
      List.nth_error xs n = Some x -> get_at a n = x;
  }.

  Arguments view_fits {_ _ _} _.
  Arguments view_length {_ _ _} _.
  Arguments view_nth {_ _ _} _ _ _ _.

  Lemma view_index_in_bounds {A : Type} (a : PrimArray.array A)
      (xs : list A) (n : nat) :
    view a xs -> n < List.length xs -> in_bounds a (index n).
  Proof.
    intros Hview Hn.
    unfold in_bounds.
    rewrite (view_length Hview).
    apply (proj2 (index_ltb_iff n (List.length xs)
      (fits_nat_lt n (List.length xs) Hn (view_fits Hview))
      (view_fits Hview))).
    exact Hn.
  Qed.

  Lemma view_get {A : Type} (a : PrimArray.array A) (xs : list A)
      (n : nat) (x : A) :
    view a xs -> List.nth_error xs n = Some x -> get_at a n = x.
  Proof. intros Hview; apply (view_nth Hview). Qed.

  Lemma view_copy {A : Type} (a : PrimArray.array A) (xs : list A) :
    view a xs -> view (PrimArray.copy a) xs.
  Proof.
    intros Hview.
    constructor.
    - exact (view_fits Hview).
    - rewrite ArrayAxioms.length_copy.
      exact (view_length Hview).
    - intros n x Hnth.
      unfold get_at.
      rewrite ArrayAxioms.get_copy.
      exact (view_nth Hview n x Hnth).
  Qed.

  Lemma view_set {A : Type} (a : PrimArray.array A) (xs : list A)
      (n : nat) (x : A) :
    view a xs -> n < List.length xs ->
    view (set_at a n x) (list_set n x xs).
  Proof.
    intros Hview Hn.
    constructor.
    - rewrite length_list_set.
      exact (view_fits Hview).
    - unfold set_at.
      rewrite ArrayAxioms.length_set, length_list_set.
      exact (view_length Hview).
    - intros m y Hmy.
      destruct (Nat.eq_dec n m) as [-> | Hneq].
      + pose proof (nth_error_list_set_same xs m x Hn) as Hx.
        rewrite Hx in Hmy.
        inversion Hmy; subst y.
        unfold get_at, set_at.
        exact (@get_set_same A a (index m) x
          (view_index_in_bounds a xs m Hview Hn)).
      + rewrite nth_error_list_set_other in Hmy by exact Hneq.
        assert (Hm : m < List.length xs).
        { apply (proj1 (List.nth_error_Some xs m)).
          rewrite Hmy.
          discriminate. }
        assert (Hidx : index n <> index m).
        { intros Heq.
          apply Hneq.
          apply index_inj.
          - exact (fits_nat_lt n (List.length xs) Hn
              (view_fits Hview)).
          - exact (fits_nat_lt m (List.length xs) Hm
              (view_fits Hview)).
          - exact Heq. }
        unfold get_at, set_at.
        transitivity (PrimArray.get a (index m)).
        * exact (@get_set_other A a (index n) (index m) x Hidx).
        * exact (view_nth Hview m y Hmy).
  Qed.

  Lemma nth_error_repeat_value {A : Type} (x : A) (size n : nat) :
    n < size -> List.nth_error (List.repeat x size) n = Some x.
  Proof.
    revert n.
    induction size as [|size IH]; intros [|n] Hn; simpl in *; try lia.
    - reflexivity.
    - apply IH.
      lia.
  Qed.

  Lemma view_make {A : Type} (x : A) (size : nat) :
    fits_nat size ->
    PrimInt63.leb (index size) PrimArray.max_length = true ->
    view (PrimArray.make (index size) x) (List.repeat x size).
  Proof.
    intros Hfit Hmax.
    constructor.
    - rewrite List.repeat_length.
      exact Hfit.
    - rewrite ArrayAxioms.length_make, Hmax, List.repeat_length.
      reflexivity.
    - intros n y Hnth.
      assert (Hn : n < size).
      { assert (Hlist : n < List.length (List.repeat x size)).
        { apply (proj1 (List.nth_error_Some (List.repeat x size) n)).
          rewrite Hnth.
          discriminate. }
        rewrite List.repeat_length in Hlist.
        exact Hlist. }
      pose proof (nth_error_repeat_value x size n Hn) as Hx.
      rewrite Hx in Hnth.
      inversion Hnth; subst y.
      unfold get_at.
      exact (@ArrayAxioms.get_make A x (index size) (index n)).
  Qed.

  (** ** Sizes used by the Orchard commitment computation *)

  Definition vector_size_nat : nat := 2048.
  Definition vector_size : PrimInt63.int := index vector_size_nat.

  Definition pippenger_window_bits_nat : nat := 8.
  Definition pippenger_radix_nat : nat := 256.
  Definition pippenger_bucket_count_nat : nat := 255.
  Definition pippenger_window_count_nat : nat := 32.

  Definition pippenger_bucket_count : PrimInt63.int :=
    index pippenger_bucket_count_nat.

  Lemma vector_size_fits_word : fits_nat vector_size_nat.
  Proof. vm_compute. reflexivity. Qed.

  Lemma bucket_count_fits_word : fits_nat pippenger_bucket_count_nat.
  Proof. vm_compute. reflexivity. Qed.

  Lemma window_count_fits_word : fits_nat pippenger_window_count_nat.
  Proof. vm_compute. reflexivity. Qed.

  Lemma vector_size_fits_array :
    PrimInt63.leb vector_size PrimArray.max_length = true.
  Proof. vm_compute. reflexivity. Qed.

  Lemma bucket_count_fits_array :
    PrimInt63.leb pippenger_bucket_count PrimArray.max_length = true.
  Proof. vm_compute. reflexivity. Qed.

  Lemma vector_index_bound (n : nat) :
    n < vector_size_nat -> PrimInt63.ltb (index n) vector_size = true.
  Proof.
    intros Hn.
    apply (proj2 (index_ltb_iff n vector_size_nat
      (fits_nat_lt n vector_size_nat Hn vector_size_fits_word)
      vector_size_fits_word)).
    exact Hn.
  Qed.

  Lemma bucket_index_bound (n : nat) :
    n < pippenger_bucket_count_nat ->
    PrimInt63.ltb (index n) pippenger_bucket_count = true.
  Proof.
    intros Hn.
    apply (proj2 (index_ltb_iff n pippenger_bucket_count_nat
      (fits_nat_lt n pippenger_bucket_count_nat Hn
        bucket_count_fits_word)
      bucket_count_fits_word)).
    exact Hn.
  Qed.

  Lemma make_vector_length {A : Type} (x : A) :
    PrimArray.length (PrimArray.make vector_size x) = vector_size.
  Proof.
    rewrite ArrayAxioms.length_make, vector_size_fits_array.
    reflexivity.
  Qed.

  Lemma make_bucket_length {A : Type} (x : A) :
    PrimArray.length (PrimArray.make pippenger_bucket_count x) =
    pippenger_bucket_count.
  Proof.
    rewrite ArrayAxioms.length_make, bucket_count_fits_array.
    reflexivity.
  Qed.

  Lemma make_vector_index_in_bounds {A : Type} (x : A) (n : nat) :
    n < vector_size_nat ->
    in_bounds (PrimArray.make vector_size x) (index n).
  Proof.
    intros Hn.
    unfold in_bounds.
    rewrite make_vector_length.
    apply vector_index_bound.
    exact Hn.
  Qed.

  Lemma make_bucket_index_in_bounds {A : Type} (x : A) (n : nat) :
    n < pippenger_bucket_count_nat ->
    in_bounds (PrimArray.make pippenger_bucket_count x) (index n).
  Proof.
    intros Hn.
    unfold in_bounds.
    rewrite make_bucket_length.
    apply bucket_index_bound.
    exact Hn.
  Qed.

  (** ** Executed smoke checks

      These goals exercise allocation, persistence, reads, writes, and the
      concrete production sizes using the VM implementation of primitive
      arrays and primitive integers. *)

  Module Smoke.
    Definition base : PrimArray.array PrimInt63.int :=
      PrimArray.make 8 0.

    Definition updated : PrimArray.array PrimInt63.int :=
      set_at (set_at base 3 42) 5 99.

    Goal PrimArray.length updated = 8.
    Proof. vm_compute. reflexivity. Qed.

    Goal get_at updated 3 = 42.
    Proof. vm_compute. reflexivity. Qed.

    Goal get_at updated 5 = 99.
    Proof. vm_compute. reflexivity. Qed.

    (** Observing an older version forces persistence to be respected. *)
    Goal get_at base 3 = 0.
    Proof. vm_compute. reflexivity. Qed.

    Goal PrimArray.length
      (PrimArray.make vector_size (0 : PrimInt63.int)) = 2048.
    Proof. vm_compute. reflexivity. Qed.

    Goal PrimArray.length
      (PrimArray.make pippenger_bucket_count (0 : PrimInt63.int)) = 255.
    Proof. vm_compute. reflexivity. Qed.
  End Smoke.

End ArrayLinear.
