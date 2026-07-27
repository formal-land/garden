(** General-purpose proof helpers shared across the Halo2 proofs, not tied to
    any one translated Rust module. An [X_proof.v] is reserved for proofs about
    the corresponding [X.rs]; helpers that several proofs share — list lemmas,
    field-element records, the field-solving tactic — live here. *)

Require Import Stdlib.Lists.List.
Require Import Stdlib.Classes.RelationClasses.
Require Import Stdlib.Classes.Morphisms.
Require Import Stdlib.Setoids.Setoid.
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

(* Setoid morphisms for congruence modulo a fixed prime: [Zdiv.eqm p] as an
   equivalence with [Z.add]/[Z.sub]/[Z.mul] compatible, from the stdlib
   [Z*_eqm] lemmas. These let [setoid_rewrite (Zdiv.Zmod_eqm p)] strip inner
   [mod p] occurrences at any depth of an [eqm]-shaped goal — the plain
   [Z.*_mod_idemp_*] rewrites only reach a [mod] that is an immediate operand
   of the enclosing modded operation. *)
#[export] Instance eqm_setoid (p : Z) : Equivalence (Zdiv.eqm p).
Proof. unfold Zdiv.eqm. constructor; congruence. Qed.
#[export] Instance Zadd_eqm_mor (p : Z) :
  Proper (Zdiv.eqm p ==> Zdiv.eqm p ==> Zdiv.eqm p) Z.add := Zdiv.Zplus_eqm p.
#[export] Instance Zsub_eqm_mor (p : Z) :
  Proper (Zdiv.eqm p ==> Zdiv.eqm p ==> Zdiv.eqm p) Z.sub := Zdiv.Zminus_eqm p.
#[export] Instance Zmul_eqm_mor (p : Z) :
  Proper (Zdiv.eqm p ==> Zdiv.eqm p ==> Zdiv.eqm p) Z.mul := Zdiv.Zmult_eqm p.

(* [mod_ring_solve] discharges reduced-form ring identities
   [UnOp.from E1 = UnOp.from E2] (both sides built from the field operations):
   it unfolds the operations to [Z] arithmetic modulo the prime, strips every
   inner [mod] through the [eqm] morphisms above, and closes the resulting
   bare polynomial identity with [ring]. Unlike [field_solve] it never
   invokes [lia], so the cost stays linear in the term size — no
   euclidean-equation search over the 255-bit modulus. Use it for goals that
   are polynomial identities; [field_solve] remains the tool when the goal
   genuinely needs linear-arithmetic reasoning (bounds, cell solving). *)
Ltac mod_ring_solve :=
  unfold BinOp.add, BinOp.sub, BinOp.mul, UnOp.from;
  lazymatch goal with
  | |- ?x mod ?q = ?y mod ?q =>
      change (Zdiv.eqm q x y);
      repeat setoid_rewrite (Zdiv.Zmod_eqm q)
  end;
  unfold Zdiv.eqm; f_equal; ring.

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
