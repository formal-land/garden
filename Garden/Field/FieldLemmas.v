Require Import Garden.Field.Field.

Global Open Scope Z_scope.

(* Ring and integral-domain facts for the field operations [UnOp.from] and
   [BinOp.add/sub/mul] (reduced modulo a prime [p]), parametric in any
   [{p : Z} `{Prime p}]. The point-addition determinism proofs use them at the
   Pallas base field to clear the field-division gradient and the nonzero
   [x_p - x_q] / [x_p - x_q]^2 / [2 y_p] factors. *)

(* The result of [BinOp.sub] / [BinOp.mul] is reduced modulo [p]. *)
Lemma from_sub_reduced {p : Z} `{Prime p} (a b : Z) :
    UnOp.from (BinOp.sub a b) = BinOp.sub a b.
Proof.
  unfold UnOp.from, BinOp.sub. apply Zmod_mod.
Qed.

Lemma from_mul_reduced {p : Z} `{Prime p} (a b : Z) :
    UnOp.from (BinOp.mul a b) = BinOp.mul a b.
Proof.
  unfold UnOp.from, BinOp.mul. apply Zmod_mod.
Qed.

Lemma field_mul_comm {p : Z} `{Prime p} (a b : Z) :
    BinOp.mul a b = BinOp.mul b a.
Proof.
  unfold BinOp.mul. now rewrite Z.mul_comm.
Qed.

Lemma field_mul_assoc {p : Z} `{Prime p} (a b c : Z) :
    BinOp.mul (BinOp.mul a b) c = BinOp.mul a (BinOp.mul b c).
Proof.
  unfold BinOp.mul.
  rewrite Zmult_mod_idemp_l, Zmult_mod_idemp_r.
  f_equal. ring.
Qed.

Lemma field_mul_swap_inner {p : Z} `{Prime p} (a b c d : Z) :
    BinOp.mul (BinOp.mul a b) (BinOp.mul c d) =
    BinOp.mul (BinOp.mul a c) (BinOp.mul b d).
Proof.
  unfold BinOp.mul.
  rewrite !Zmult_mod_idemp_l, !Zmult_mod_idemp_r.
  f_equal. ring.
Qed.

Lemma field_mul_cancel_r {p : Z} `{Prime p} (a b c : Z) :
    UnOp.from c <> 0 ->
    BinOp.mul a c = BinOp.mul b c ->
    UnOp.from a = UnOp.from b.
Proof.
  intros Hc Heq.
  assert (Hzero : BinOp.mul (BinOp.sub a b) c = 0).
  { unfold BinOp.mul, BinOp.sub in *.
    rewrite Zmult_mod_idemp_l.
    replace ((a - b) * c) with (a * c - b * c) by ring.
    rewrite Zminus_mod, Heq, Z.sub_diag.
    apply Zmod_0_l. }
  rewrite mul_zero_implies_zero in Hzero.
  destruct Hzero as [Hz | Hz].
  - rewrite from_sub_reduced in Hz.
    now rewrite sub_zero_equiv in Hz.
  - contradiction.
Qed.

(* Solve a nonexceptional coordinate constraint for the reduced next-row cell:
   from [m - a - b - c = 0] (field) with [c] reduced, [c = m - a - b]. *)
Lemma field_solve_xr {p : Z} `{Prime p} (m a b c : Z) :
    UnOp.from c = c ->
    UnOp.from (m -F a -F b -F c) = 0 ->
    c = m -F a -F b.
Proof.
  intros Hc Hh.
  rewrite from_sub_reduced in Hh.
  apply sub_zero_equiv in Hh.
  rewrite from_sub_reduced, Hc in Hh.
  symmetry. exact Hh.
Qed.

Lemma field_solve_yr {p : Z} `{Prime p} (m a c : Z) :
    UnOp.from c = c ->
    UnOp.from (m -F a -F c) = 0 ->
    c = m -F a.
Proof.
  intros Hc Hh.
  rewrite from_sub_reduced in Hh.
  apply sub_zero_equiv in Hh.
  rewrite from_sub_reduced, Hc in Hh.
  symmetry. exact Hh.
Qed.

Lemma field_add_comm {p : Z} `{Prime p} (a b : Z) :
    BinOp.add a b = BinOp.add b a.
Proof.
  unfold BinOp.add. now rewrite Z.add_comm.
Qed.

Lemma field_mul_cong {p : Z} `{Prime p} (a b c d : Z) :
    UnOp.from a = UnOp.from c ->
    UnOp.from b = UnOp.from d ->
    BinOp.mul a b = BinOp.mul c d.
Proof.
  intros Hac Hbd.
  unfold BinOp.mul, UnOp.from in *.
  rewrite Zmult_mod, Hac, Hbd, <- Zmult_mod.
  reflexivity.
Qed.

Lemma field_mul_eq_zero_cancel {p : Z} `{Prime p} (a b : Z) :
    UnOp.from a <> 0 ->
    BinOp.mul a b = 0 ->
    UnOp.from b = 0.
Proof.
  intros Ha Hab.
  rewrite mul_zero_implies_zero in Hab.
  destruct Hab as [Hz | Hz]; [contradiction | exact Hz].
Qed.

Lemma field_mul_sub_distr {p : Z} `{Prime p} (a b c : Z) :
    BinOp.mul a (BinOp.sub b c) =
    BinOp.sub (BinOp.mul a b) (BinOp.mul a c).
Proof.
  unfold BinOp.mul, BinOp.sub.
  rewrite Zmult_mod_idemp_r, <- Zminus_mod.
  f_equal. ring.
Qed.

Lemma field_from_mul_nonzero {p : Z} `{Prime p} (a b : Z) :
    UnOp.from a <> 0 ->
    UnOp.from b <> 0 ->
    UnOp.from (BinOp.mul a b) <> 0.
Proof.
  intros Ha Hb Hcontra.
  rewrite from_mul_reduced in Hcontra.
  rewrite mul_zero_implies_zero in Hcontra.
  destruct Hcontra; [apply Ha | apply Hb]; assumption.
Qed.
