(** * Semantic view of the provenance list-to-array loader

    Generated witnesses are written as readable lists and loaded once into
    primitive arrays.  This file proves that the loader preserves every list
    entry.  The proof is structural: it never evaluates a production-size
    array. *)

From Corelib Require Import PrimArray.
From Stdlib Require Import Lists.List micromega.Lia.
Require Import Garden.Prim63.ArrayLinear.
Require Import Garden.Orchard.vk.provenance.Jacobian.

Import ListNotations.

Module VkArrayOfListRefinement.
  Fixpoint list_load_from {A : Type} (values : list A) (index : nat)
      (contents : list A) : list A :=
    match values with
    | [] => contents
    | value :: values' =>
        list_load_from values' (S index)
          (ArrayLinear.list_set index value contents)
    end.

  Lemma list_load_from_length {A : Type} (values contents : list A)
      (index : nat) :
    List.length (list_load_from values index contents) =
      List.length contents.
  Proof.
    revert index contents.
    induction values as [|value values IH]; intros index contents; cbn.
    - reflexivity.
    - rewrite IH, ArrayLinear.length_list_set. reflexivity.
  Qed.

  Lemma load_list_from_view {A : Type} (values contents : list A)
      (index : nat) (array : PrimArray.array A) :
    ArrayLinear.view array contents ->
    (index + List.length values <= List.length contents)%nat ->
    ArrayLinear.view
      (VkJacobian.load_list_from values index array)
      (list_load_from values index contents).
  Proof.
    revert index array contents.
    induction values as [|value values IH];
      intros index array contents Hview Hrange; cbn.
    - exact Hview.
    - apply IH.
      + apply ArrayLinear.view_set; [exact Hview |].
        cbn in Hrange. lia.
      + rewrite ArrayLinear.length_list_set.
        cbn in Hrange. lia.
  Qed.

  Lemma list_set_app_length {A : Type} (prefix suffix : list A)
      (old value : A) :
    ArrayLinear.list_set (List.length prefix) value
      (prefix ++ old :: suffix) =
    prefix ++ value :: suffix.
  Proof.
    induction prefix as [|head prefix IH]; cbn.
    - reflexivity.
    - now rewrite IH.
  Qed.

  Lemma list_load_from_repeat {A : Type} (values prefix suffix : list A)
      (default : A) :
    list_load_from values (List.length prefix)
      (prefix ++ List.repeat default (List.length values) ++ suffix) =
    prefix ++ values ++ suffix.
  Proof.
    revert prefix.
    induction values as [|value values IH]; intros prefix.
    - cbn. reflexivity.
    - cbn [List.length List.repeat list_load_from].
      change
        (list_load_from values (S (List.length prefix))
          (ArrayLinear.list_set (List.length prefix) value
            (prefix ++ (default ::
              (List.repeat default (List.length values) ++ suffix)))) =
         prefix ++ (value :: values) ++ suffix).
      rewrite list_set_app_length.
      replace (S (List.length prefix))
        with (List.length (prefix ++ [value]))
        by (rewrite List.length_app; cbn; lia).
      replace (prefix ++ value :: List.repeat default (List.length values)
          ++ suffix)
        with ((prefix ++ [value]) ++
          List.repeat default (List.length values) ++ suffix)
        by (rewrite <- List.app_assoc; reflexivity).
      rewrite IH.
      rewrite <- List.app_assoc. reflexivity.
  Qed.

  Theorem array_of_list_view {A : Type} (default : A) (values : list A) :
    ArrayLinear.fits_nat (List.length values) ->
    PrimInt63.leb (ArrayLinear.index (List.length values))
      PrimArray.max_length = true ->
    ArrayLinear.view (VkJacobian.array_of_list default values) values.
  Proof.
    intros Hfits Hallowed.
    unfold VkJacobian.array_of_list.
    pose proof (ArrayLinear.view_make default (List.length values)
      Hfits Hallowed) as Hinitial.
    pose proof (load_list_from_view values
      (List.repeat default (List.length values)) O
      (PrimArray.make (ArrayLinear.index (List.length values)) default)
      Hinitial) as Hloaded.
    rewrite List.repeat_length in Hloaded.
    specialize (Hloaded ltac:(lia)).
    cbn [List.length] in Hloaded.
    assert (Hexact :
      list_load_from values O
        (List.repeat default (List.length values)) = values).
    { pose proof (list_load_from_repeat values [] [] default) as Hcontents.
      cbn in Hcontents.
      now rewrite !List.app_nil_r in Hcontents. }
    now rewrite Hexact in Hloaded.
  Qed.

  Corollary array_of_list_get {A : Type} (default value : A)
      (values : list A) (index : nat) :
    ArrayLinear.fits_nat (List.length values) ->
    PrimInt63.leb (ArrayLinear.index (List.length values))
      PrimArray.max_length = true ->
    List.nth_error values index = Some value ->
    PrimArray.get (VkJacobian.array_of_list default values)
      (ArrayLinear.index index) = value.
  Proof.
    intros Hfits Hallowed Hnth.
    exact (ArrayLinear.view_nth
      (array_of_list_view default values Hfits Hallowed)
      index value Hnth).
  Qed.
End VkArrayOfListRefinement.
