(** * Generic list lemmas shared by the finite certificate files

    A boolean check over a rectangular index grid is packaged as a
    doubly-nested [List.forallb]; [forallb_nested_entry] extracts the
    per-entry fact from the whole-grid boolean.  The lemma is generic over the
    checked function [f], so its proof runs on abstract terms — no concrete
    table ever enters a reduction here. *)

Require Import Stdlib.Lists.List.

Lemma forallb_nested_entry (f : nat -> nat -> bool) (la lb : list nat) (w i : nat) :
  List.forallb (fun w0 => List.forallb (f w0) lb) la = true ->
  In w la -> In i lb -> f w i = true.
Proof.
  intros Hall Hw Hi.
  rewrite forallb_forall in Hall.
  specialize (Hall w Hw).
  rewrite forallb_forall in Hall.
  exact (Hall i Hi).
Qed.
