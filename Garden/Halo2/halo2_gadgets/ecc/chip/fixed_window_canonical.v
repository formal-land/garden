Require Import Garden.Halo2.main.
Require Import Garden.Halo2.lemmas.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.spec.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.constants.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.window_disc.
Require Import Garden.Field.Field.
Require Import Garden.Field.Lemmas.
Require Import Garden.Field.Sqrt.
Require Import Garden.Plonky3.M.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Bool.Bool.

(** * Canonical (witness-free) fixed-base window points on the Pallas curve

    A fixed-base window point has its x by Lagrange interpolation of the digit
    ([EccSpec.fixed_window_point]'s x) and recovers y from a witnessed square root
    [u] as [u² − z].  The genuine y is determined without the witness: of the two
    on-curve roots [±Y], exactly one has [y + fw_z] a quadratic residue (admits a
    [u]), and that is the y the circuit must witness.  This file names that
    canonical point and the per-window forcing lemma pinning the witnessed point
    to it. *)

#[local] Existing Instance Primes.PallasPIsPrime.
Global Open Scope Z_scope.

(** The canonical (witness-free) window point: the circuit's interpolated x, and
    the on-curve y selected by the z-table's quadratic-residue branch. *)
Definition fixed_window_point_canonical
    (w : EccSpec.fixed_window) (digit : Z) : Point.t :=
  let x := EccSpec.fixed_interp (EccSpec.fw_coeffs w) digit (UnOp.from 1) in
  let r := field_sqrt (x *F x *F x +F UnOp.from pallas_b) in
  let y := if is_square (r +F EccSpec.fw_z w) then r else 0 -F r in
  {| Point.x := x; Point.y := y |}.

(** ** [is_square] algebra (local copies)

    The three [is_square] facts the forcing lemmas need, proved from the Euler
    scaffolding of [Field/Sqrt.v] / [Field/Lemmas.v].  A canonical home is
    [Field/Sqrt.v]; the local copies keep the witnessed
    corollary [window_point_forced_of_disc] derivable from this file's
    dependencies alone. *)

(** [is_square] depends only on the residue class of its argument. *)
Lemma mul_cong_r (x a b : Z) :
  UnOp.from a = UnOp.from b -> x *F a = x *F b.
Proof.
  intro Hab. unfold BinOp.mul.
  rewrite <- (Zmult_mod_idemp_r a x), <- (Zmult_mod_idemp_r b x).
  unfold UnOp.from in Hab. rewrite Hab. reflexivity.
Qed.

Lemma modpow_pos_cong (a b : Z) (q : positive) :
  UnOp.from a = UnOp.from b -> modpow_pos a q = modpow_pos b q.
Proof.
  intro Hab. induction q as [q IH | q IH | ]; cbn [modpow_pos].
  - rewrite IH. apply mul_cong_r. exact Hab.
  - rewrite IH. reflexivity.
  - exact Hab.
Qed.

Lemma modpow_cong (a b e : Z) :
  UnOp.from a = UnOp.from b -> modpow a e = modpow b e.
Proof.
  intro Hab. unfold modpow. destruct e as [| q | q]; try reflexivity.
  apply modpow_pos_cong. exact Hab.
Qed.

Lemma is_square_cong (a b : Z) :
  UnOp.from a = UnOp.from b -> is_square a = is_square b.
Proof.
  intro Hab. unfold is_square.
  rewrite Hab, (modpow_cong a b _ Hab). reflexivity.
Qed.

(** Every square [u^2] is a quadratic residue.  ([Euler]: nonzero [u^2] has
    [(u^2)^((p-1)/2) = u^(p-1) = 1].) *)
Lemma is_square_sq (u : Z) : is_square (u *F u) = true.
Proof.
  unfold is_square.
  destruct (UnOp.from (u *F u) =? 0) eqn:Ez; [reflexivity |].
  apply orb_true_iff. right. apply Z.eqb_eq.
  apply Z.eqb_neq in Ez.
  assert (Hu : UnOp.from u <> 0).
  { intro Hu0. apply Ez.
    unfold BinOp.mul, UnOp.from in *.
    rewrite Z.mod_mod by (pose proof prime_gt1; lia).
    rewrite <- Zmult_mod_idemp_l, Hu0, Z.mul_0_l. apply Zmod_0_l. }
  rewrite modpow_correct by (apply half_nonneg).
  rewrite Fpow_mul_base by (apply half_nonneg).
  rewrite Fpow_sqr by (apply half_nonneg).
  replace (2 * ((Primes.pallas_p - 1) / 2)) with (Primes.pallas_p - 1)
    by (vm_compute; reflexivity).
  apply fermat_Fpow. exact Hu.
Qed.

(** ** Field-algebra helpers for the sign forcing

    Pure [UnOp.from]/[BinOp] identities (with no [is_square]/[field_sqrt] in
    scope, so [field_solve] stays linear on the ones that use it) that turn
    [Honcurve]/[Hqr]/[Hdisc] into the canonical y.  Products are handled by hand;
    the three linear congruences use [field_solve]. *)

Lemma from_add_reduced (a b : Z) : UnOp.from (a +F b) = a +F b.
Proof. unfold UnOp.from, BinOp.add. apply Zmod_mod. Qed.

Lemma add_sub_cancel_l (a b : Z) : a +F (b -F a) = UnOp.from b.
Proof.
  unfold BinOp.add, BinOp.sub, UnOp.from.
  rewrite Zplus_mod_idemp_r. f_equal. ring.
Qed.

(** From the on-curve equation [Y² − x³ − b = 0], the square-root argument
    [x³ + b] equals [Y²] as reduced field values. *)
Lemma add_b_eq_sq (X3 cb Y : Z) :
  Y *F Y -F X3 -F cb = 0 -> X3 +F UnOp.from cb = Y *F Y.
Proof.
  intro Hh. apply sub_zero_equiv in Hh. rewrite from_sub_reduced in Hh.
  rewrite <- Hh, add_sub_cancel_l. apply from_mul_reduced.
Qed.

(** Integral-domain split of [a² = c²] into [a = ±c] (as residue classes). *)
Lemma diff_squares_zero (a c : Z) :
  a *F a = c *F c -> UnOp.from (a -F c) = 0 \/ UnOp.from (a +F c) = 0.
Proof.
  intro Hac.
  assert (Hz : (a -F c) *F (a +F c) = 0).
  { unfold BinOp.mul, BinOp.sub, BinOp.add.
    rewrite Zmult_mod_idemp_l, Zmult_mod_idemp_r.
    replace ((a - c) * (a + c)) with (a * a - c * c) by ring.
    rewrite Zminus_mod. unfold BinOp.mul in Hac. rewrite Hac.
    rewrite Z.sub_diag. apply Zmod_0_l. }
  apply mul_zero_implies_zero in Hz. exact Hz.
Qed.

(** Difference of squares: [(a − c)(a + c) = a² − c²] modulo [p]. *)
Lemma sub_squares_factor (a c : Z) :
  UnOp.from ((a -F c) *F (a +F c)) = UnOp.from (a *F a -F c *F c).
Proof.
  unfold BinOp.mul, BinOp.sub, BinOp.add, UnOp.from.
  rewrite !Zmod_mod.
  rewrite Zmult_mod_idemp_l, Zmult_mod_idemp_r.
  rewrite <- Zminus_mod.
  f_equal. ring.
Qed.

Lemma add_zero_opp (r py : Z) : r +F py = 0 -> UnOp.from py = 0 -F r.
Proof. intro Hh. field_solve. Qed.

Lemma rz_eq_zpy (r z py : Z) :
  r +F py = 0 -> UnOp.from (r +F z) = UnOp.from (z -F py).
Proof. intro Hh. field_solve. Qed.

Lemma add_z_cong_pos (r z py : Z) :
  UnOp.from r = UnOp.from py -> UnOp.from (r +F z) = UnOp.from (z +F py).
Proof. intro Hh. field_solve. Qed.

(** ** The shared forcing lemma [window_y_forced_of_disc]

    The single lemma BOTH consumers ([action_spec_us_free] and
    [spend_auth_g_full_window_correct]) depend on.  Given a point [P] whose x is
    the window's Lagrange interpolation, on the curve, with [fw_z + Point.y P] a
    quadratic residue ([Hqr]) and the discriminant [window_disc] a non-residue
    ([Hdisc]), [P] is the canonical window point.  [Honcurve] is the exact shape
    the on-curve extraction produces ([point_on_curve], i.e.
    [circuit_proof.fixed_base.full_width_*_on_curve]); [Hred] records that the
    witnessed y is reduced mod [p] (both consumers pass a reduced point).

    Proof.  x-coords agree definitionally; [add_b_eq_sq] turns [Honcurve] into
    [x³ + b = (Point.y P)²], so [x³ + b] is a square ([is_square_sq]) and
    [field_sqrt_sound] gives [r² = (Point.y P)²]; [diff_squares_zero] splits
    [Point.y P] into the two roots [±r].  On the [+r] root [Hqr] makes
    [is_square (r + z)] true (the canonical [then]-branch); on the [−r] root the
    discriminant identity [window_disc = (z − y)(z + y)] with [Hqr] and [Hdisc]
    ([is_square_mul_cancel_r]) makes [is_square (r + z)] false (the [else]-branch
    [0 − r]).  [Hred] plus [field_sqrt_reduced] upgrade the residue-class equality
    to the raw point equality. *)
Lemma window_y_forced_of_disc
    (w : EccSpec.fixed_window) (digit : Z) (P : Point.t)
    (Hx :
      Point.x P =
        EccSpec.fixed_interp (EccSpec.fw_coeffs w) digit (UnOp.from 1))
    (Honcurve :
      Point.y P *F Point.y P -F
        (Point.x P *F Point.x P *F Point.x P) -F
        Garden.Halo2.halo2_gadgets.ecc.chip.constants.pallas_b = 0)
    (Hqr :
      is_square (UnOp.from (EccSpec.fw_z w +F Point.y P)) = true)
    (Hdisc : is_square (window_disc w digit) = false)
    (Hred : UnOp.from (Point.y P) = Point.y P) :
    P = fixed_window_point_canonical w digit.
Proof.
  destruct P as [px py]. cbn [Point.x Point.y] in *. subst px.
  unfold fixed_window_point_canonical. cbv zeta.
  set (x := EccSpec.fixed_interp (EccSpec.fw_coeffs w) digit (UnOp.from 1)) in *.
  set (z := EccSpec.fw_z w) in *.
  set (cb := Garden.Halo2.halo2_gadgets.ecc.chip.constants.pallas_b) in *.
  pose proof (add_b_eq_sq (x *F x *F x) cb py Honcurve) as HD.
  assert (Hsqok : is_square (x *F x *F x +F UnOp.from cb) = true).
  { rewrite (is_square_cong (x *F x *F x +F UnOp.from cb) (py *F py)).
    - apply is_square_sq.
    - rewrite HD. reflexivity. }
  pose proof (field_sqrt_sound _ Hsqok) as Hrr.
  set (r := field_sqrt (x *F x *F x +F UnOp.from cb)) in *.
  rewrite from_add_reduced in Hrr. rewrite HD in Hrr.
  assert (Hqr' : is_square (z +F py) = true).
  { rewrite (is_square_cong (z +F py) (UnOp.from (z +F py))
              (eq_sym (from_idem (z +F py)))). exact Hqr. }
  f_equal.
  destruct (diff_squares_zero r py Hrr) as [Hpos | Hneg].
  - (* [py] and [r] are the same root: the canonical [then]-branch. *)
    rewrite from_sub_reduced in Hpos. apply sub_zero_equiv in Hpos.
    assert (Hdec : is_square (r +F z) = true).
    { rewrite (is_square_cong (r +F z) (z +F py) (add_z_cong_pos r z py Hpos)).
      exact Hqr'. }
    rewrite Hdec, <- Hred, <- Hpos.
    exact (field_sqrt_reduced (x *F x *F x +F UnOp.from cb)).
  - (* [py = −r]: the discriminant forces the canonical [else]-branch. *)
    rewrite from_add_reduced in Hneg.
    pose proof (add_zero_opp r py Hneg) as HpyN.
    assert (Hwd : is_square ((z -F py) *F (z +F py)) = false).
    { rewrite (is_square_cong ((z -F py) *F (z +F py)) (window_disc w digit)).
      - exact Hdisc.
      - change (window_disc w digit)
          with (UnOp.from (z *F z -F (x *F x *F x +F UnOp.from cb))).
        rewrite from_idem, HD. apply sub_squares_factor. }
    pose proof (is_square_mul_cancel_r (z -F py) (z +F py) Hqr' Hwd) as Hzmpy.
    assert (Hdec : is_square (r +F z) = false).
    { rewrite (is_square_cong (r +F z) (z -F py) (rz_eq_zpy r z py Hneg)).
      exact Hzmpy. }
    rewrite Hdec, <- Hred. exact HpyN.
Qed.

(** ** The witnessed corollary [window_point_forced_of_disc]

    [window_y_forced_of_disc] applied to [P := fixed_window_point w digit u]: the
    x-coordinate hypothesis holds definitionally and [Hqr] is free
    ([fw_z + (u^2 - z) = u^2] is a square by [is_square_sq]), leaving only
    [Honcurve] and [Hdisc].  This is the witnessed-point forcing that part B
    ([action_spec_us_free]) and F2 (the RK path) consume. *)
Lemma window_point_forced_of_disc
    (w : EccSpec.fixed_window) (digit u : Z)
    (Honcurve :
      let P := EccSpec.fixed_window_point w digit u in
      Point.y P *F Point.y P -F
        (Point.x P *F Point.x P *F Point.x P) -F
        Garden.Halo2.halo2_gadgets.ecc.chip.constants.pallas_b = 0)
    (Hdisc : is_square (window_disc w digit) = false) :
    EccSpec.fixed_window_point w digit u = fixed_window_point_canonical w digit.
Proof.
  apply (window_y_forced_of_disc w digit
           (EccSpec.fixed_window_point w digit u)).
  - reflexivity.
  - exact Honcurve.
  - cbn [EccSpec.fixed_window_point Point.y].
    rewrite (is_square_cong _ (u *F u)).
    + apply is_square_sq.
    + rewrite from_idem. generalize (u *F u); intro a. field_solve.
  - exact Hdisc.
  - cbn [EccSpec.fixed_window_point Point.y]. apply from_sub_reduced.
Qed.
