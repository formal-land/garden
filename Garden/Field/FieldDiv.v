(** * Correctness of [BinOp.div] as field division

    [BinOp.div x y = x *F mod_inverse y p] (see [Field.Field]). This file proves
    that [mod_inverse] (the square-and-multiply [a^(p-2) mod p]) inverts a
    nonzero field element, and hence the field-division law
    [(x / y) *F y = x] (mod p). The inverse correctness rests on Fermat's little
    theorem from [Field.Fermat]. *)

Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.ZArith.Znumtheory.
Require Import Stdlib.ZArith.Zpow_facts.
Require Import Stdlib.micromega.Lia.
Require Import Garden.Field.Field.
Require Import Garden.Field.Fermat.

Open Scope Z_scope.

(** ** [mod_inverse] computes [a^(p-2) mod p] *)

(** Square-and-multiply is correct modulo [m]. *)
Lemma fast_pow_correct (m : Z) (Hm : 0 < m) :
  forall (e : positive) (acc base : Z),
    fast_pow_modulo_positive acc base m e = (acc * base ^ (Z.pos e)) mod m.
Proof.
  induction e as [p IH | p IH | ]; intros acc base; cbn [fast_pow_modulo_positive].
  - rewrite IH.
    rewrite Pos2Z.inj_xI.
    rewrite Zmult_mod.
    rewrite Z.mod_mod by lia.
    rewrite <- (Zpower_mod (base * base) (Z.pos p) m Hm).
    rewrite <- Zmult_mod.
    replace (base * base) with (base ^ 2) by (rewrite Z.pow_2_r; reflexivity).
    rewrite <- Z.pow_mul_r by lia.
    f_equal.
    rewrite Z.pow_add_r by lia. rewrite Z.pow_1_r. ring.
  - rewrite IH.
    rewrite Pos2Z.inj_xO.
    rewrite Zmult_mod.
    rewrite <- (Zpower_mod (base * base) (Z.pos p) m Hm).
    rewrite <- Zmult_mod.
    replace (base * base) with (base ^ 2) by (rewrite Z.pow_2_r; reflexivity).
    rewrite <- Z.pow_mul_r by lia.
    reflexivity.
  - rewrite Z.pow_1_r. reflexivity.
Qed.

(** The double predecessor of the prime exponent. *)
Lemma pos_pred_pred (p' : positive) :
  2 < Z.pos p' -> Z.pos (Pos.pred (Pos.pred p')) = Z.pos p' - 2.
Proof.
  intros H.
  assert (Hp1 : p' <> 1%positive) by (intro Hc; subst p'; lia).
  assert (Hq1 : Pos.pred p' <> 1%positive).
  { intro Hc.
    pose proof (Pos.succ_pred p' Hp1) as Hs.
    rewrite Hc in Hs.
    replace (Pos.succ 1%positive) with 2%positive in Hs by reflexivity.
    subst p'. lia. }
  pose proof (Pos.succ_pred p' Hp1) as Hs1.
  pose proof (Pos.succ_pred (Pos.pred p') Hq1) as Hs2.
  apply (f_equal Z.pos) in Hs1.
  apply (f_equal Z.pos) in Hs2.
  rewrite Pos2Z.inj_succ in Hs1, Hs2.
  lia.
Qed.

Lemma mod_inverse_eq (a p : Z) :
  2 < p -> mod_inverse a p = (a ^ (p - 2)) mod p.
Proof.
  intros Hp.
  unfold mod_inverse.
  destruct p as [|p'|p']; try lia.
  rewrite (fast_pow_correct (Z.pos p') ltac:(lia)).
  rewrite Z.mul_1_l.
  rewrite pos_pred_pred by lia.
  reflexivity.
Qed.

(** ** The field-inverse and field-division laws *)

(** [mod_inverse y p] is a two-sided inverse of [y] in the field. *)
Lemma mod_inverse_mul {p} `{Prime p} (y : Z) :
  2 < p -> y mod p <> 0 -> BinOp.mul (mod_inverse y p) y = 1.
Proof.
  intros Hp2 Hnz.
  pose proof (@is_prime p _) as Hp. unfold IsPrime in Hp.
  unfold BinOp.mul.
  rewrite mod_inverse_eq by lia.
  rewrite Z.mul_comm.
  apply inv_correct_gen; assumption.
Qed.

(** The defining law of field division: [(x / y) *F y = x] (reduced) for a
    nonzero divisor [y]. *)
Lemma div_mul {p} `{Prime p} (x y : Z) :
  2 < p -> y mod p <> 0 -> BinOp.mul (BinOp.div x y) y = x mod p.
Proof.
  intros Hp2 Hnz.
  pose proof (mod_inverse_mul (p := p) y Hp2 Hnz) as Hinv.
  unfold BinOp.mul in Hinv.
  unfold BinOp.div, BinOp.mul.
  rewrite Zmult_mod_idemp_l.
  replace (x * mod_inverse y p * y) with (x * (mod_inverse y p * y)) by ring.
  rewrite <- Zmult_mod_idemp_r.
  rewrite Hinv.
  rewrite Z.mul_1_r.
  reflexivity.
Qed.
