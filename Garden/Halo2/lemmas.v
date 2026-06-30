(** General-purpose proof helpers shared across the Halo2 proofs, not tied to
    any one translated Rust module. An [X_proof.v] is reserved for proofs about
    the corresponding [X.rs]; helpers that several proofs share — list lemmas,
    field-element records, the field-solving tactic — live here. *)

Require Import Stdlib.Lists.List.
Require Import Garden.Field.Field.
Require Import Garden.Plonky3.M.

Global Open Scope Z_scope.

(* [List.nth] of a [map] over an initial segment: at an in-range index the
   value is just [f] applied to that index. *)
Lemma nth_map_seq {B : Type} (f : nat -> B) (n k : nat) (d : B) :
    (k < n)%nat ->
    List.nth k (List.map f (List.seq 0 n)) d = f k.
Proof.
  intros Hk.
  rewrite (List.nth_indep (List.map f (List.seq 0 n)) d (f 0%nat))
    by (rewrite List.length_map, List.length_seq; exact Hk).
  rewrite List.map_nth.
  rewrite List.seq_nth by exact Hk.
  reflexivity.
Qed.

(* [field_solve] discharges Pallas-base-field equalities that are linear once
   every [BinOp.mul] of two cells is read as a single opaque atom (e.g. the
   "solve a polynomial constraint for one reduced trace cell" goals that show
   up in the ECC determinism proofs). It unfolds the field operations to
   [Z.modulo], rewrites the modulus to the concrete Pallas prime literal so the
   euclidean [p * q] products stay linear, and finishes with [lia] under the
   [Z.to_euclidean_division_equations] post-hook installed in
   [Garden.Plonky3.M]. Clear unused constraint hypotheses first so no genuinely
   non-linear hypothesis reaches [lia]. *)
Ltac field_solve :=
  unfold BinOp.add, BinOp.sub, BinOp.mul, UnOp.from in *;
  change Primes.pallas_p with
    28948022309329048855892746252171976963363056481941560715954676764349967630337
    in *;
  lia.

Module Point.
  Record t : Set := {
    x : Z;
    y : Z;
  }.

  Global Instance IsMapMod {p : Z} `{Prime p} : MapMod t := {
    map_mod point := {|
      x := UnOp.from point.(x);
      y := UnOp.from point.(y);
    |};
  }.
End Point.

(* A two-field field-element record, symmetric to [Point]. *)
Module Pair.
  Record t : Set := {
    left : Z;
    right : Z;
  }.

  Global Instance IsMapMod {p : Z} `{Prime p} : MapMod t := {
    map_mod pair := {|
      left := UnOp.from pair.(left);
      right := UnOp.from pair.(right);
    |};
  }.
End Pair.
