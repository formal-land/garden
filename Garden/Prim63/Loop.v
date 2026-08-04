(** * Tail-recursive loops that thread the latest primitive-array version

    The computational convention in this file is deliberate: a step consumes
    the current state, and the recursive call receives only the state returned
    by that step.  Instantiating the state with [PrimArray.array A] therefore
    follows the efficient linear-use path of Rocq's persistent primitive-array
    runtime.

    [foldi_from] exposes natural indices and is convenient for refinement
    proofs.  [foldi_u63] maintains its counter as a primitive unsigned integer
    and is intended for larger closed computations. *)

From Corelib Require Import PrimInt63 PrimArray.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
Require Import Garden.Prim63.ArrayLinear.

Local Open Scope uint63_scope.

Set Universe Polymorphism.

Module Prim63Loop.

  (** ** Proof-oriented and primitive-counter folds *)

  Fixpoint foldi_from {State : Type} (count start : nat)
      (step : nat -> State -> State) (state : State) : State :=
    match count with
    | O => state
    | S count' =>
        let state' := step start state in
        foldi_from count' (S start) step state'
    end.

  Fixpoint advance_u63 (count : nat) (i : PrimInt63.int) : PrimInt63.int :=
    match count with
    | O => i
    | S count' => advance_u63 count' (PrimInt63.add i 1%uint63)
    end.

  Fixpoint foldi_u63 {State : Type} (count : nat) (i : PrimInt63.int)
      (step : PrimInt63.int -> State -> State) (state : State) : State :=
    match count with
    | O => state
    | S count' =>
        let state' := step i state in
        foldi_u63 count' (PrimInt63.add i 1%uint63) step state'
    end.

  Lemma foldi_from_zero {State : Type} (start : nat)
      (step : nat -> State -> State) (state : State) :
    foldi_from 0 start step state = state.
  Proof. reflexivity. Qed.

  Lemma foldi_from_succ {State : Type} (count start : nat)
      (step : nat -> State -> State) (state : State) :
    foldi_from (S count) start step state =
    foldi_from count (S start) step (step start state).
  Proof. reflexivity. Qed.

  Lemma foldi_u63_zero {State : Type} (i : PrimInt63.int)
      (step : PrimInt63.int -> State -> State) (state : State) :
    foldi_u63 0 i step state = state.
  Proof. reflexivity. Qed.

  Lemma foldi_u63_succ {State : Type} (count : nat)
      (i : PrimInt63.int) (step : PrimInt63.int -> State -> State)
      (state : State) :
    foldi_u63 (S count) i step state =
    foldi_u63 count (PrimInt63.add i 1%uint63) step (step i state).
  Proof. reflexivity. Qed.

  Lemma foldi_from_append {State : Type} (left right start : nat)
      (step : nat -> State -> State) (state : State) :
    foldi_from (left + right) start step state =
    foldi_from right (start + left) step
      (foldi_from left start step state).
  Proof.
    revert start state.
    induction left as [|left IH]; intros start state; simpl.
    - replace (start + 0)%nat with start by lia.
      reflexivity.
    - rewrite IH.
      replace (S start + left) with (start + S left) by lia.
      reflexivity.
  Qed.

  Lemma foldi_from_invariant {State : Type}
      (Inv : nat -> State -> Prop) (count start : nat)
      (step : nat -> State -> State) (state : State) :
    Inv start state ->
    (forall i current,
      start <= i < start + count ->
      Inv i current -> Inv (S i) (step i current)) ->
    Inv (start + count) (foldi_from count start step state).
  Proof.
    revert start state.
    induction count as [|count IH]; intros start state HInv Hstep; simpl.
    - replace (start + 0) with start by lia.
      exact HInv.
    - replace (start + S count) with (S start + count) by lia.
      apply IH.
      + apply Hstep; [lia | exact HInv].
      + intros i current Hi Hcurrent.
        apply Hstep; [lia | exact Hcurrent].
  Qed.

  Lemma foldi_u63_invariant {State : Type}
      (Inv : PrimInt63.int -> State -> Prop) (count : nat)
      (start : PrimInt63.int)
      (step : PrimInt63.int -> State -> State) (state : State) :
    Inv start state ->
    (forall i current,
      Inv i current ->
      Inv (PrimInt63.add i 1%uint63) (step i current)) ->
    Inv (advance_u63 count start) (foldi_u63 count start step state).
  Proof.
    revert start state.
    induction count as [|count IH]; intros start state HInv Hstep; simpl.
    - exact HInv.
    - apply IH.
      + apply Hstep.
        exact HInv.
      + exact Hstep.
  Qed.

  Lemma advance_u63_index (count start : nat) :
    ArrayLinear.fits_nat (start + count) ->
    advance_u63 count (ArrayLinear.index start) =
      ArrayLinear.index (start + count).
  Proof.
    revert start.
    induction count as [|count IH]; intro start; simpl.
    - replace (start + 0)%nat with start by lia.
      reflexivity.
    - intro Hfit.
      rewrite ArrayLinear.index_succ.
      + rewrite IH.
        * f_equal; lia.
        * replace (S start + count)%nat with (start + S count)%nat by lia.
          exact Hfit.
      + apply (ArrayLinear.fits_nat_le (S start) (start + S count));
          [lia | exact Hfit].
  Qed.

  Lemma foldi_u63_index {State : Type} (count start : nat)
      (step : PrimInt63.int -> State -> State) (state : State) :
    ArrayLinear.fits_nat (start + count) ->
    foldi_u63 count (ArrayLinear.index start) step state =
      foldi_from count start (fun i => step (ArrayLinear.index i)) state.
  Proof.
    revert start state.
    induction count as [|count IH]; intros start state Hfit; simpl.
    - reflexivity.
    - rewrite ArrayLinear.index_succ.
      + apply IH.
        replace (S start + count)%nat with (start + S count)%nat by lia.
        exact Hfit.
      + apply (ArrayLinear.fits_nat_le (S start) (start + S count));
          [lia | exact Hfit].
  Qed.

  (** ** Primitive-array specializations *)

  Definition array_loop_from {A : Type} (count start : nat)
      (step : nat -> PrimArray.array A -> PrimArray.array A)
      (a : PrimArray.array A) : PrimArray.array A :=
    foldi_from count start step a.

  Definition array_loop_u63 {A : Type} (count : nat)
      (start : PrimInt63.int)
      (step : PrimInt63.int -> PrimArray.array A -> PrimArray.array A)
      (a : PrimArray.array A) : PrimArray.array A :=
    foldi_u63 count start step a.

  Lemma array_loop_u63_index {A : Type} (count start : nat)
      (step : PrimInt63.int -> PrimArray.array A -> PrimArray.array A)
      (a : PrimArray.array A) :
    ArrayLinear.fits_nat (start + count) ->
    array_loop_u63 count (ArrayLinear.index start) step a =
      array_loop_from count start
        (fun i => step (ArrayLinear.index i)) a.
  Proof.
    unfold array_loop_u63, array_loop_from.
    apply foldi_u63_index.
  Qed.

  Lemma array_loop_from_length {A : Type} (count start : nat)
      (step : nat -> PrimArray.array A -> PrimArray.array A)
      (a : PrimArray.array A) :
    (forall i current,
      PrimArray.length (step i current) = PrimArray.length current) ->
    PrimArray.length (array_loop_from count start step a) =
    PrimArray.length a.
  Proof.
    intros Hstep.
    unfold array_loop_from.
    revert start a.
    induction count as [|count IH]; intros start a; simpl.
    - reflexivity.
    - rewrite IH, Hstep.
      reflexivity.
  Qed.

  Lemma array_loop_u63_length {A : Type} (count : nat)
      (start : PrimInt63.int)
      (step : PrimInt63.int -> PrimArray.array A -> PrimArray.array A)
      (a : PrimArray.array A) :
    (forall i current,
      PrimArray.length (step i current) = PrimArray.length current) ->
    PrimArray.length (array_loop_u63 count start step a) =
    PrimArray.length a.
  Proof.
    intros Hstep.
    unfold array_loop_u63.
    revert start a.
    induction count as [|count IH]; intros start a; simpl.
    - reflexivity.
    - rewrite IH, Hstep.
      reflexivity.
  Qed.

  Definition set_loop_from {A : Type} (count start : nat)
      (value : nat -> A) (a : PrimArray.array A) : PrimArray.array A :=
    array_loop_from count start
      (fun i current => ArrayLinear.set_at current i (value i)) a.

  Definition list_set_loop_from {A : Type} (count start : nat)
      (value : nat -> A) (xs : list A) : list A :=
    foldi_from count start
      (fun i current => ArrayLinear.list_set i (value i) current) xs.

  Definition set_loop_u63 {A : Type} (count : nat)
      (start : PrimInt63.int) (value : PrimInt63.int -> A)
      (a : PrimArray.array A) : PrimArray.array A :=
    array_loop_u63 count start
      (fun i current => PrimArray.set current i (value i)) a.

  Lemma set_loop_u63_index {A : Type} (count start : nat)
      (value : PrimInt63.int -> A) (a : PrimArray.array A) :
    ArrayLinear.fits_nat (start + count) ->
    set_loop_u63 count (ArrayLinear.index start) value a =
      set_loop_from count start (fun i => value (ArrayLinear.index i)) a.
  Proof.
    intro Hfit.
    unfold set_loop_u63, set_loop_from.
    rewrite (array_loop_u63_index count start
      (fun i current => PrimArray.set current i (value i)) a Hfit).
    reflexivity.
  Qed.

  Lemma set_loop_from_length {A : Type} (count start : nat)
      (value : nat -> A) (a : PrimArray.array A) :
    PrimArray.length (set_loop_from count start value a) =
    PrimArray.length a.
  Proof.
    unfold set_loop_from.
    apply array_loop_from_length.
    intros i current.
    unfold ArrayLinear.set_at.
    exact (@ArrayLinear.length_set A current (ArrayLinear.index i)
      (value i)).
  Qed.

  Lemma set_loop_u63_length {A : Type} (count : nat)
      (start : PrimInt63.int) (value : PrimInt63.int -> A)
      (a : PrimArray.array A) :
    PrimArray.length (set_loop_u63 count start value a) =
    PrimArray.length a.
  Proof.
    unfold set_loop_u63.
    apply array_loop_u63_length.
    intros i current.
    exact (@ArrayLinear.length_set A current i (value i)).
  Qed.

  Lemma set_loop_from_view {A : Type} (count start : nat)
      (value : nat -> A) (a : PrimArray.array A) (xs : list A) :
    ArrayLinear.view a xs ->
    start + count <= List.length xs ->
    ArrayLinear.view (set_loop_from count start value a)
      (list_set_loop_from count start value xs).
  Proof.
    revert start a xs.
    induction count as [|count IH]; intros start a xs Hview Hrange; simpl.
    - exact Hview.
    - apply IH.
      + apply ArrayLinear.view_set.
        * exact Hview.
        * lia.
      + rewrite ArrayLinear.length_list_set.
        lia.
  Qed.

  Lemma set_loop_u63_view {A : Type} (count start : nat)
      (value : PrimInt63.int -> A) (a : PrimArray.array A) (xs : list A) :
    ArrayLinear.view a xs ->
    start + count <= List.length xs ->
    ArrayLinear.view
      (set_loop_u63 count (ArrayLinear.index start) value a)
      (list_set_loop_from count start
        (fun i => value (ArrayLinear.index i)) xs).
  Proof.
    intros Hview Hrange.
    rewrite set_loop_u63_index.
    - apply set_loop_from_view; assumption.
    - exact (ArrayLinear.fits_nat_le
        (start + count) (List.length xs) Hrange
        (ArrayLinear.view_fits Hview)).
  Qed.

  (** ** Executed production-size smoke checks *)

  Module Smoke.
    Definition fill_vector : PrimArray.array PrimInt63.int :=
      set_loop_u63 ArrayLinear.vector_size_nat 0 (fun i => i)
        (PrimArray.make ArrayLinear.vector_size 0).

    Goal PrimArray.length fill_vector = ArrayLinear.vector_size.
    Proof. vm_compute. reflexivity. Qed.

    Goal PrimArray.get fill_vector 0 = 0.
    Proof. vm_compute. reflexivity. Qed.

    Goal PrimArray.get fill_vector 2047 = 2047.
    Proof. vm_compute. reflexivity. Qed.

    Definition fill_buckets : PrimArray.array PrimInt63.int :=
      set_loop_u63 ArrayLinear.pippenger_bucket_count_nat 0 (fun i => i)
        (PrimArray.make ArrayLinear.pippenger_bucket_count 0).

    Goal PrimArray.get fill_buckets 254 = 254.
    Proof. vm_compute. reflexivity. Qed.

    (** A modest stress check: 32768 latest-version updates distributed over
        the 2048 vector slots.  Every slot is incremented exactly 16 times. *)
    Definition bump_step (i : PrimInt63.int)
        (a : PrimArray.array PrimInt63.int) :
        PrimArray.array PrimInt63.int :=
      let j := PrimInt63.mod i ArrayLinear.vector_size in
      PrimArray.set a j (PrimInt63.add (PrimArray.get a j) 1%uint63).

    Definition stress_vector : PrimArray.array PrimInt63.int :=
      array_loop_u63 32768 0 bump_step
        (PrimArray.make ArrayLinear.vector_size 0).

    Goal PrimArray.get stress_vector 0 = 16.
    Proof. Time (vm_compute; reflexivity). Qed.

    Goal PrimArray.get stress_vector 2047 = 16.
    Proof. Time (vm_compute; reflexivity). Qed.
  End Smoke.

End Prim63Loop.
