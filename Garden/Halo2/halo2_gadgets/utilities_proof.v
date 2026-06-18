Require Import Garden.Halo2.main.
Require Import Garden.Field.Field.
Require Import Garden.Plonky3.M.

Global Open Scope Z_scope.

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

Definition square {p : Z} `{Prime p}
    (value : Z)
    : Z :=
  value *F value.

Definition ternary {p : Z} `{Prime p}
    (selector when_true when_false : Z)
    : Z :=
  selector *F when_true +F
    (UnOp.from 1 -F selector) *F when_false.

Fixpoint pow_nat {p : Z} `{Prime p}
    (value : Z)
    (power : nat)
    : Z :=
  match power with
  | O => UnOp.from 1
  | S power => pow_nat value power *F value
  end.

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
