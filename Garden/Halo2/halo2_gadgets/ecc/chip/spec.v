Require Import Stdlib.Lists.List.
Require Import Garden.Halo2.main.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.lemmas.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.add_proof.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.add_incomplete_proof.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.mul_fixed_proof.
Require Import Garden.Orchard.columns.
Require Import Garden.Field.Field.
Require Import Garden.Field.Lemmas.
Require Import Garden.Field.Div.
Require Import Garden.Field.Fermat.
Require Import Garden.Plonky3.M.
Require Import Stdlib.ZArith.Znumtheory.
Require Import Stdlib.ZArith.Zpow_facts.

#[local] Existing Instance Primes.PallasPIsPrime.

Global Open Scope Z_scope.

(** * Elliptic-curve math primitives (Layer A of the crypto-soundness track)

    Math-level point operations reused as the abstract operations the ECC chips
    are proved to compute.  Complete and incomplete addition are taken verbatim
    from the chip [output] functions ([CompleteAddition.output] /
    [IncompleteAddition.output]); on top of them we build [extract_x], the
    identity, and a canonical scalar multiplication [scalar_mul] (double-and-add
    by iterated complete addition).

    [scalar_mul] (variable-base, double-and-add) is the canonical group multiple,
    used where the base is an honest point (Sinsemilla blinding seed).

    [fixed_scalar_mul] instead mirrors the circuit's *internal* fixed-base
    computation: the Orchard fixed bases exist only as windowed Lagrange tables
    (no affine generator), so it folds the per-window [mul_fixed] points over the
    concrete table directly.  This keeps every constant concrete — see
    [docs/crypto-soundness.md], "internal soundness". *)

Module EccSpec.
  (** The affine identity in the chips' [(0, 0)]-sentinel convention (the
      representation [CompleteAddition.output] treats as the neutral element). *)
  Definition identity : Point.t := {| Point.x := 0; Point.y := 0 |}.

  (** Complete (total) point addition — covers all exceptional cases. *)
  Definition point_add (P Q : Point.t) : Point.t :=
    CompleteAddition.output
      P.(Point.x) P.(Point.y) Q.(Point.x) Q.(Point.y).

  (** Incomplete point addition — the Sinsemilla/fixed-base inner operation,
      valid only when the x-coordinates differ. *)
  Definition point_add_incomplete (P Q : Point.t) : Point.t :=
    IncompleteAddition.output
      P.(Point.x) P.(Point.y) Q.(Point.x) Q.(Point.y).

  (** [Extract_P]: the x-coordinate of a curve point, used to project [RK],
      [NF_OLD] and [CMX] to their field-element instance values. *)
  Definition extract_x (P : Point.t) : Z := P.(Point.x).

  (** Canonical scalar multiplication [k]·P by iterated complete addition.
      [Z.iter] adds [P] to the accumulator [|k|] times (and is the identity for
      [k <= 0]), so this is the group multiple of [P] by a non-negative [k]. *)
  Definition scalar_mul (k : Z) (P : Point.t) : Point.t :=
    Z.iter k (fun acc => point_add acc P) identity.

  (** ** Internal-soundness fixed-base scalar multiplication

      The Orchard fixed bases are stored not as affine generators but as the
      circuit's windowed Lagrange tables (8 interpolation coefficients of the
      window-multiple x-coordinates, plus a [z] offset, per 3-bit window).  We
      mirror [mul_fixed] directly over those concrete tables. *)

  (** One window of a fixed-base table: the 8 Lagrange coefficients and the [z]
      used to recover [y] via [y = u² − z]. *)
  Record fixed_window : Set := {
    fw_coeffs : list Z;
    fw_z : Z;
  }.
  Definition fixed_table : Set := list fixed_window.

  (** Project a window out of the circuit's row representation: a row is
      [8 coeffs] then the [FixedZ] value, each tagged [(Fixed.t, annotation, Z)]. *)
  Definition fixed_window_of_row {A : Type}
      (row : list (Fixed.t * A * Z)) : fixed_window := {|
    fw_coeffs := Stdlib.Lists.List.map snd (Stdlib.Lists.List.firstn 8 row);
    fw_z :=
      match Stdlib.Lists.List.nth_error row 8 with
      | Some e => snd e
      | None => 0
      end;
  |}.
  Definition fixed_table_of_rows {A : Type}
      (rows : list (list (Fixed.t * A * Z))) : fixed_table :=
    Stdlib.Lists.List.map fixed_window_of_row rows.

  (** Lagrange interpolation [Σᵢ coeffᵢ · digitⁱ] = the window point's
      x-coordinate ([mul_fixed_proof.interpolated_x]). *)
  Fixpoint fixed_interp (cs : list Z) (digit pow : Z) : Z :=
    match cs with
    | [] => 0
    | c :: cs' => c *F pow +F fixed_interp cs' digit (pow *F digit)
    end.

  (** The window point: x by interpolation, y recovered from the witnessed
      square root [u] as [u² − z] ([RunningSumCoordinatesCheck]/[CoordsCheck]). *)
  Definition fixed_window_point (w : fixed_window) (digit u : Z) : Point.t := {|
    Point.x := fixed_interp w.(fw_coeffs) digit (UnOp.from 1);
    Point.y := u *F u -F w.(fw_z);
  |}.

  (** Concrete arithmetic fact for the Pallas base field: the curve constant
      [b = 5] is not a square. This is intentionally much narrower than any
      gadget/table correctness assumption; it only records the residue status
      of one field element. *)
  Lemma pallas_b_quadratic_nonresidue :
    forall y : Z,
      UnOp.from (y *F y) <>
      UnOp.from Garden.Halo2.halo2_gadgets.ecc.chip.constants.pallas_b.
  Proof.
    intros y Hy.
    set (p := Primes.pallas_p) in *.
    set (e := (p - 1) / 2) in *.
    assert (Hpprime : Znumtheory.prime p).
    { subst p.
      pose proof (@is_prime Primes.pallas_p Primes.PallasPIsPrime) as Hp.
      exact Hp. }
    assert (Hpgt2 : 2 < p)
      by (subst p; unfold Primes.pallas_p, Primes.t_p; lia).
    assert (Hebounds : 0 <= e) by (subst e; lia).
    assert (Htwice : 2 * e = p - 1)
      by (subst e; subst p; unfold Primes.pallas_p, Primes.t_p; cbn; lia).
    assert (Hy_sq : (y * y) mod p = 5).
    { subst p.
      unfold BinOp.mul, UnOp.from in Hy.
      cbn in Hy.
      rewrite Z.mod_mod in Hy by (unfold Primes.pallas_p, Primes.t_p; lia).
      exact Hy. }
    assert (Hy_nonzero : y mod p <> 0).
    { intro H0.
      assert (Hyy0 : (y * y) mod p = 0).
      { rewrite <- Zmult_mod_idemp_l.
        rewrite H0, Z.mul_0_l.
        apply Zmod_0_l. }
      rewrite Hyy0 in Hy_sq.
      discriminate. }
    assert (H5pow_y : (5 ^ e) mod p = ((y * y) ^ e) mod p).
    { rewrite <- Hy_sq at 1.
      symmetry.
      rewrite Zpower_mod by lia.
      reflexivity. }
    assert (Hyfermat : (y ^ (p - 1)) mod p = 1).
    { assert (Hr : 0 < y mod p < p).
      { pose proof (Z.mod_pos_bound y p ltac:(lia)) as Hrange.
        split; [lia | tauto]. }
      pose proof (flt_pow_pred (y mod p) p Hpprime Hr) as Hflt.
      rewrite Zpower_mod by lia.
      exact Hflt. }
    assert (H5pow_one : (5 ^ e) mod p = 1).
    { rewrite H5pow_y.
      replace ((y * y) ^ e) with (y ^ (2 * e)).
      - rewrite Htwice.
        exact Hyfermat.
      - rewrite Z.pow_mul_r by lia.
        rewrite Z.pow_2_r.
        reflexivity. }
    assert (Hcompute :
        fast_pow_modulo_positive 1 5 p (Z.to_pos e) = p - 1).
    { subst e p.
      cbv.
      reflexivity. }
    pose proof (fast_pow_correct p ltac:(lia) (Z.to_pos e) 1 5) as Hfast.
    rewrite Hcompute in Hfast.
    assert (He_pos : 0 < e).
    { subst e.
      clear Hy Hy_sq Hy_nonzero H5pow_y Hyfermat H5pow_one Hcompute Hfast
        Hpprime Hebounds.
      lia. }
    pose proof (Z2Pos.id e He_pos) as Heqpos.
    rewrite Heqpos in Hfast.
    rewrite Z.mul_1_l in Hfast.
    assert (H5pow_minus : 5 ^ e mod p = p - 1) by (symmetry; exact Hfast).
    rewrite H5pow_one in H5pow_minus.
    clear Hy Hy_sq Hy_nonzero H5pow_y Hyfermat Hcompute Hfast H5pow_one Heqpos
      Hpprime Hebounds Htwice.
    lia.
  Qed.

  Lemma pallas_curve_x_nonzero
      (x y : Z)
      (Hcurve :
        y *F y -F (x *F x *F x) -F
          Garden.Halo2.halo2_gadgets.ecc.chip.constants.pallas_b = 0) :
    UnOp.from x <> 0.
  Proof.
    intro Hx0.
    apply (pallas_b_quadratic_nonresidue y).
    apply sub_zero_equiv in Hcurve.
    rewrite FieldRewrite.from_sub in Hcurve.
    assert (Hcube : x *F x *F x = 0).
    { unfold BinOp.mul.
      unfold UnOp.from in Hx0.
      rewrite <- Zmult_mod_idemp_r.
      rewrite Hx0.
      rewrite Z.mul_0_r.
      reflexivity. }
    rewrite Hcube in Hcurve.
    rewrite FieldRewrite.sub_zero_right in Hcurve.
    exact Hcurve.
  Qed.

  Lemma fixed_interp_8_eq_interpolated_x
      (c0 c1 c2 c3 c4 c5 c6 c7 digit : Z) :
    fixed_interp [c0; c1; c2; c3; c4; c5; c6; c7]
      digit (UnOp.from 1) =
    interpolated_x c0 c1 c2 c3 c4 c5 c6 c7 digit.
  Proof.
    unfold interpolated_x.
    cbn [fixed_interp].
    unfold Garden.Halo2.halo2_gadgets.utilities_proof.pow_nat.
    field_solve.
  Qed.

  Lemma fixed_interp_8_eq_interpolated_x_from
      (c0 c1 c2 c3 c4 c5 c6 c7 digit : Z) :
    fixed_interp [c0; c1; c2; c3; c4; c5; c6; c7]
      digit (UnOp.from 1) =
    interpolated_x
      (UnOp.from c0) (UnOp.from c1) (UnOp.from c2) (UnOp.from c3)
      (UnOp.from c4) (UnOp.from c5) (UnOp.from c6) (UnOp.from c7)
      digit.
  Proof.
    unfold interpolated_x.
    cbn [fixed_interp].
    unfold Garden.Halo2.halo2_gadgets.utilities_proof.pow_nat.
    field_solve.
  Qed.

  (** The 3-bit window digit [i] of the scalar [k]. *)
  Definition window_digit (k : Z) (i : nat) : Z :=
    (k / 8 ^ Z.of_nat i) mod 8.

  Fixpoint fixed_scalar_mul_aux
      (ws : fixed_table) (k : Z) (us : list Z) (i : nat) (acc : Point.t)
      : Point.t :=
    match ws with
    | [] => acc
    | w :: ws' =>
        fixed_scalar_mul_aux ws' k us (S i)
          (point_add acc
            (fixed_window_point w (window_digit k i)
              (Stdlib.Lists.List.nth i us 0)))
    end.

  (** [k]·G as the windowed running sum the circuit computes: complete-add the
      per-window points across [tbl], with the per-window square-root witnesses
      [us] read from the assignment.  No affine generator appears — [tbl] is a
      concrete circuit constant. *)
  Definition fixed_scalar_mul (tbl : fixed_table) (k : Z) (us : list Z) : Point.t :=
    fixed_scalar_mul_aux tbl k us 0%nat identity.

  Lemma div_sub_swap
      (a b c d : Z)
      (Hden : UnOp.from (c -F d) <> 0) :
    BinOp.div (a -F b) (c -F d) =
    BinOp.div (b -F a) (d -F c).
  Proof.
    set (L1 := BinOp.div (a -F b) (c -F d)).
    set (L2 := BinOp.div (b -F a) (d -F c)).
    assert (Hden' : UnOp.from (d -F c) <> 0).
    { rewrite FieldRewrite.from_sub in *.
      intro Hc.
      apply sub_zero_equiv in Hc.
      symmetry in Hc.
      apply sub_zero_equiv in Hc.
      exact (Hden Hc). }
    assert (HL1 : L1 *F (c -F d) = a -F b).
    { subst L1. rewrite div_mul.
      - apply FieldRewrite.from_sub.
      - unfold Primes.pallas_p, Primes.t_p; lia.
      - exact Hden. }
    assert (HL2 : L2 *F (d -F c) = b -F a).
    { subst L2. rewrite div_mul.
      - apply FieldRewrite.from_sub.
      - unfold Primes.pallas_p, Primes.t_p; lia.
      - exact Hden'. }
    assert (Hfrom : UnOp.from L1 = UnOp.from L2).
    { apply (field_mul_cancel_r L1 L2 (c -F d) Hden).
      rewrite HL1.
      replace (L2 *F (c -F d)) with (a -F b).
      - reflexivity.
      - field_solve. }
    assert (Hred1 : UnOp.from L1 = L1).
    { unfold UnOp.from. symmetry. apply InField.make. }
    assert (Hred2 : UnOp.from L2 = L2).
    { unfold UnOp.from. symmetry. apply InField.make. }
    rewrite Hred1, Hred2 in Hfrom.
    exact Hfrom.
  Qed.

  Lemma point_add_comm_x_distinct
      (P Q : Point.t)
      (HPx : UnOp.from (Point.x P) <> 0)
      (HQx : UnOp.from (Point.x Q) <> 0)
      (Hx_distinct : UnOp.from (Point.x P) <> UnOp.from (Point.x Q)) :
    point_add P Q = point_add Q P.
  Proof.
    destruct P as [xp yp].
    destruct Q as [xq yq].
    cbn [Point.x Point.y] in *.
    unfold point_add.
    cbn [Point.x Point.y].
    unfold add_proof.CompleteAddition.output,
      Garden.Halo2.halo2_gadgets.utilities_proof.square.
    destruct (xp =? 0) eqn:Hxp0.
    { apply Z.eqb_eq in Hxp0. subst xp. contradiction. }
    destruct (xq =? 0) eqn:Hxq0.
    { apply Z.eqb_eq in Hxq0. subst xq. contradiction. }
    assert (Hxpq : (xp =? xq) = false).
    { apply Z.eqb_neq. intro Hc.
      apply Hx_distinct. rewrite Hc. reflexivity. }
    assert (Hxqp : (xq =? xp) = false).
    { apply Z.eqb_neq. intro Hc.
      apply Hx_distinct. rewrite Hc. reflexivity. }
    rewrite Hxpq, Hxqp.
    cbn [andb].
    set (L1 := BinOp.div (yq -F yp) (xq -F xp)).
    set (L2 := BinOp.div (yp -F yq) (xp -F xq)).
    assert (Hd : UnOp.from (xq -F xp) <> 0).
    { rewrite FieldRewrite.from_sub. intro Hc.
      apply sub_zero_equiv in Hc. exact (Hx_distinct (eq_sym Hc)). }
    assert (Hlam : L1 *F (xq -F xp) = yq -F yp).
    { subst L1. rewrite div_mul.
      - apply FieldRewrite.from_sub.
      - unfold Primes.pallas_p, Primes.t_p; lia.
      - exact Hd. }
    assert (HL : L1 = L2).
    { subst L1 L2. apply div_sub_swap. exact Hd. }
    subst L2.
    rewrite <- HL.
    assert (Hxcoord :
        L1 *F L1 -F xp -F xq = L1 *F L1 -F xq -F xp).
    { clear HPx HQx Hx_distinct Hxp0 Hxq0 Hxpq Hxqp Hd Hlam HL.
      field_solve. }
    rewrite Hxcoord.
    f_equal.
    clear HPx HQx Hx_distinct Hxp0 Hxq0 Hxpq Hxqp Hd HL Hxcoord.
    field_solve.
  Qed.

  Lemma point_add_comm_x_distinct_x
      (P Q : Point.t)
      (HPx : UnOp.from (Point.x P) <> 0)
      (HQx : UnOp.from (Point.x Q) <> 0)
      (Hx_distinct : UnOp.from (Point.x P) <> UnOp.from (Point.x Q)) :
    Point.x (point_add P Q) = Point.x (point_add Q P).
  Proof.
    rewrite (point_add_comm_x_distinct P Q HPx HQx Hx_distinct).
    reflexivity.
  Qed.

  Lemma point_add_comm_x_distinct_y
      (P Q : Point.t)
      (HPx : UnOp.from (Point.x P) <> 0)
      (HQx : UnOp.from (Point.x Q) <> 0)
      (Hx_distinct : UnOp.from (Point.x P) <> UnOp.from (Point.x Q)) :
    Point.y (point_add P Q) = Point.y (point_add Q P).
  Proof.
    rewrite (point_add_comm_x_distinct P Q HPx HQx Hx_distinct).
    reflexivity.
  Qed.

  Lemma point_add_on_curve_x_distinct
      (P Q : Point.t)
      (HPcurve :
        Point.y P *F Point.y P -F
          (Point.x P *F Point.x P *F Point.x P) -F
          Garden.Halo2.halo2_gadgets.ecc.chip.constants.pallas_b = 0)
      (HQcurve :
        Point.y Q *F Point.y Q -F
          (Point.x Q *F Point.x Q *F Point.x Q) -F
          Garden.Halo2.halo2_gadgets.ecc.chip.constants.pallas_b = 0)
      (HPx : UnOp.from (Point.x P) <> 0)
      (HQx : UnOp.from (Point.x Q) <> 0)
      (Hx_distinct : UnOp.from (Point.x P) <> UnOp.from (Point.x Q)) :
    let R := point_add P Q in
    Point.y R *F Point.y R -F
      (Point.x R *F Point.x R *F Point.x R) -F
      Garden.Halo2.halo2_gadgets.ecc.chip.constants.pallas_b = 0.
  Proof.
    destruct P as [xp yp].
    destruct Q as [xq yq].
    cbn [Point.x Point.y] in *.
    unfold point_add, CompleteAddition.output,
      Garden.Halo2.halo2_gadgets.utilities_proof.square.
    destruct (xp =? 0) eqn:Hxp0.
    { apply Z.eqb_eq in Hxp0. subst xp. contradiction. }
    destruct (xq =? 0) eqn:Hxq0.
    { apply Z.eqb_eq in Hxq0. subst xq. contradiction. }
    assert (Hxpq : (xp =? xq) = false).
    { apply Z.eqb_neq. intro Hc.
      apply Hx_distinct. rewrite Hc. reflexivity. }
    assert (Hxsum : ((xp =? xq) && (yp +F yq =? 0))%bool = false).
    { rewrite Hxpq. reflexivity. }
    cbn [Point.x Point.y].
    rewrite Hxp0, Hxq0, Hxsum, Hxpq.
    set (L := BinOp.div (yq -F yp) (xq -F xp)).
    set (xr := L *F L -F xp -F xq).
    assert (Hd : UnOp.from (xq -F xp) <> 0).
    { rewrite FieldRewrite.from_sub. intro Hc.
      apply sub_zero_equiv in Hc. exact (Hx_distinct (eq_sym Hc)). }
    assert (Hlam : L *F (xq -F xp) = yq -F yp).
    { subst L. rewrite div_mul.
      - apply FieldRewrite.from_sub.
      - unfold Primes.pallas_p, Primes.t_p; lia.
      - exact Hd. }
    subst xr.
    cbn [Point.x Point.y].
    assert (Hsecant_sum_p :
        L *F (UnOp.from 2 *F yp +F L *F (xq -F xp)) =
        xq *F xq +F xq *F xp +F xp *F xp).
    { assert (Hsecant_sum :
          L *F (yq +F yp) =
          xq *F xq +F xq *F xp +F xp *F xp).
      { apply (field_mul_cancel_r _ _ (xq -F xp) Hd).
        field_solve. }
      replace (UnOp.from 2 *F yp +F L *F (xq -F xp))
        with (yq +F yp).
      - exact Hsecant_sum.
      - field_solve. }
    apply sub_zero_equiv in HPcurve.
    apply sub_zero_equiv.
    rewrite <- HPcurve.
    clear HPcurve HQcurve HPx HQx Hx_distinct Hxp0 Hxq0 Hxpq Hxsum Hd Hlam.
    apply sub_zero_equiv.
    assert (Hfactor_mod :
      UnOp.from
        ((L *F (xp -F (L *F L -F xp -F xq)) -F yp) *F
         (L *F (xp -F (L *F L -F xp -F xq)) -F yp) -F
         (L *F L -F xp -F xq) *F (L *F L -F xp -F xq) *F
         (L *F L -F xp -F xq) -F
         (yp *F yp -F xp *F xp *F xp)) =
      UnOp.from
        ((L *F (UnOp.from 2 *F yp +F L *F (xq -F xp)) -F
          (xq *F xq +F xq *F xp +F xp *F xp)) *F
          (L *F L -F UnOp.from 2 *F xp -F xq))).
    { show_equality_modulo.
      change Primes.pallas_p with
        28948022309329048855892746252171976963363056481941560715954676764349967630337
        in *;
      lia. }
    rewrite <- from_sub_reduced.
    rewrite Hfactor_mod.
    assert (Hrel :
        L *F (UnOp.from 2 *F yp +F L *F (xq -F xp)) -F
        (xq *F xq +F xq *F xp +F xp *F xp) = 0).
    { apply sub_zero_equiv.
      rewrite Hsecant_sum_p.
      reflexivity. }
    rewrite Hrel.
    reflexivity.
  Qed.

  Lemma point_add_x_nonzero_x_distinct
      (P Q : Point.t)
      (HPcurve :
        Point.y P *F Point.y P -F
          (Point.x P *F Point.x P *F Point.x P) -F
          Garden.Halo2.halo2_gadgets.ecc.chip.constants.pallas_b = 0)
      (HQcurve :
        Point.y Q *F Point.y Q -F
          (Point.x Q *F Point.x Q *F Point.x Q) -F
          Garden.Halo2.halo2_gadgets.ecc.chip.constants.pallas_b = 0)
      (HPx : UnOp.from (Point.x P) <> 0)
      (HQx : UnOp.from (Point.x Q) <> 0)
      (Hx_distinct : UnOp.from (Point.x P) <> UnOp.from (Point.x Q)) :
    UnOp.from (Point.x (point_add P Q)) <> 0.
  Proof.
    apply (pallas_curve_x_nonzero
      (Point.x (point_add P Q))
      (Point.y (point_add P Q))).
    exact (point_add_on_curve_x_distinct
      P Q HPcurve HQcurve HPx HQx Hx_distinct).
  Qed.

  Lemma curve_same_x_y_eq_or_neg
      (x yp yq : Z)
      (Hyp_red : UnOp.from yp = yp)
      (Hyq_red : UnOp.from yq = yq)
      (HPcurve :
        yp *F yp -F (x *F x *F x) -F
          Garden.Halo2.halo2_gadgets.ecc.chip.constants.pallas_b = 0)
      (HQcurve :
        yq *F yq -F (x *F x *F x) -F
          Garden.Halo2.halo2_gadgets.ecc.chip.constants.pallas_b = 0) :
    yp = yq \/ yp +F yq = 0.
  Proof.
    assert (Hsq : UnOp.from (yp *F yp) = UnOp.from (yq *F yq)).
    { apply sub_zero_equiv in HPcurve.
      apply sub_zero_equiv in HQcurve.
      field_solve. }
    assert (Hprod : (yp -F yq) *F (yp +F yq) = 0).
    { field_solve. }
    apply mul_zero_implies_zero in Hprod.
    destruct Hprod as [Hdiff | Hsum].
    - left.
      rewrite from_sub_reduced in Hdiff.
      apply sub_zero_equiv in Hdiff.
      rewrite Hyp_red, Hyq_red in Hdiff.
      exact Hdiff.
    - right.
      unfold UnOp.from, BinOp.add in Hsum.
      rewrite Z.mod_mod in Hsum by (unfold Primes.pallas_p, Primes.t_p; lia).
      exact Hsum.
  Qed.

  Lemma point_add_comm_on_curve_nonzero_reduced
      (P Q : Point.t)
      (HPcurve :
        Point.y P *F Point.y P -F
          (Point.x P *F Point.x P *F Point.x P) -F
          Garden.Halo2.halo2_gadgets.ecc.chip.constants.pallas_b = 0)
      (HQcurve :
        Point.y Q *F Point.y Q -F
          (Point.x Q *F Point.x Q *F Point.x Q) -F
          Garden.Halo2.halo2_gadgets.ecc.chip.constants.pallas_b = 0)
      (HPx : UnOp.from (Point.x P) <> 0)
      (HQx : UnOp.from (Point.x Q) <> 0)
      (HPx_red : UnOp.from (Point.x P) = Point.x P)
      (HQx_red : UnOp.from (Point.x Q) = Point.x Q)
      (HPy_red : UnOp.from (Point.y P) = Point.y P)
      (HQy_red : UnOp.from (Point.y Q) = Point.y Q) :
    point_add P Q = point_add Q P.
  Proof.
    destruct P as [xp yp].
    destruct Q as [xq yq].
    cbn [Point.x Point.y] in *.
    unfold point_add, CompleteAddition.output,
      Garden.Halo2.halo2_gadgets.utilities_proof.square.
    destruct (xp =? 0) eqn:Hxp0.
    { apply Z.eqb_eq in Hxp0. subst xp. contradiction. }
    destruct (xq =? 0) eqn:Hxq0.
    { apply Z.eqb_eq in Hxq0. subst xq. contradiction. }
    destruct (xp =? xq) eqn:Hx_eq.
    - apply Z.eqb_eq in Hx_eq. subst xq.
      destruct (curve_same_x_y_eq_or_neg xp yp yq
        HPy_red HQy_red HPcurve HQcurve) as [Hy | Hneg].
      + subst yq.
        cbn [Point.x Point.y].
        rewrite Hxp0.
        rewrite Z.eqb_refl.
        reflexivity.
      + assert (Hneg' : yq +F yp = 0).
        { rewrite field_add_comm. exact Hneg. }
        cbn [Point.x Point.y].
        rewrite Hxp0.
        rewrite Z.eqb_refl.
        rewrite Hneg, Hneg'.
        reflexivity.
    - cbn [Point.x Point.y].
      change (point_add {| Point.x := xp; Point.y := yp |}
          {| Point.x := xq; Point.y := yq |} =
        point_add {| Point.x := xq; Point.y := yq |}
          {| Point.x := xp; Point.y := yp |}).
      apply point_add_comm_x_distinct.
      + exact HPx.
      + exact HQx.
      + intro Hfield.
        apply Z.eqb_neq in Hx_eq.
        apply Hx_eq.
        rewrite <- HPx_red, <- HQx_red.
        exact Hfield.
  Qed.

  Lemma point_add_comm_on_curve_nonzero_reduced_x
      (P Q : Point.t)
      (HPcurve :
        Point.y P *F Point.y P -F
          (Point.x P *F Point.x P *F Point.x P) -F
          Garden.Halo2.halo2_gadgets.ecc.chip.constants.pallas_b = 0)
      (HQcurve :
        Point.y Q *F Point.y Q -F
          (Point.x Q *F Point.x Q *F Point.x Q) -F
          Garden.Halo2.halo2_gadgets.ecc.chip.constants.pallas_b = 0)
      (HPx : UnOp.from (Point.x P) <> 0)
      (HQx : UnOp.from (Point.x Q) <> 0)
      (HPx_red : UnOp.from (Point.x P) = Point.x P)
      (HQx_red : UnOp.from (Point.x Q) = Point.x Q)
      (HPy_red : UnOp.from (Point.y P) = Point.y P)
      (HQy_red : UnOp.from (Point.y Q) = Point.y Q) :
    Point.x (point_add P Q) = Point.x (point_add Q P).
  Proof.
    exact (f_equal Point.x
      (point_add_comm_on_curve_nonzero_reduced
        P Q HPcurve HQcurve HPx HQx HPx_red HQx_red HPy_red HQy_red)).
  Qed.

  Lemma point_add_comm_on_curve_nonzero_reduced_y
      (P Q : Point.t)
      (HPcurve :
        Point.y P *F Point.y P -F
          (Point.x P *F Point.x P *F Point.x P) -F
          Garden.Halo2.halo2_gadgets.ecc.chip.constants.pallas_b = 0)
      (HQcurve :
        Point.y Q *F Point.y Q -F
          (Point.x Q *F Point.x Q *F Point.x Q) -F
          Garden.Halo2.halo2_gadgets.ecc.chip.constants.pallas_b = 0)
      (HPx : UnOp.from (Point.x P) <> 0)
      (HQx : UnOp.from (Point.x Q) <> 0)
      (HPx_red : UnOp.from (Point.x P) = Point.x P)
      (HQx_red : UnOp.from (Point.x Q) = Point.x Q)
      (HPy_red : UnOp.from (Point.y P) = Point.y P)
      (HQy_red : UnOp.from (Point.y Q) = Point.y Q) :
    Point.y (point_add P Q) = Point.y (point_add Q P).
  Proof.
    exact (f_equal Point.y
      (point_add_comm_on_curve_nonzero_reduced
        P Q HPcurve HQcurve HPx HQx HPx_red HQx_red HPy_red HQy_red)).
  Qed.

  Lemma point_add_identity_left (P : Point.t) :
    point_add identity P = P.
  Proof.
    destruct P.
    reflexivity.
  Qed.

  Lemma fixed_scalar_mul_aux_nil
      (k : Z) (us : list Z) (i : nat) (acc : Point.t) :
    fixed_scalar_mul_aux [] k us i acc = acc.
  Proof. reflexivity. Qed.

  Lemma fixed_scalar_mul_nil (k : Z) (us : list Z) :
    fixed_scalar_mul [] k us = identity.
  Proof. reflexivity. Qed.

  Lemma fixed_scalar_mul_aux_cons
      (w : fixed_window) (ws : fixed_table)
      (k : Z) (us : list Z) (i : nat) (acc : Point.t) :
    fixed_scalar_mul_aux (w :: ws) k us i acc =
      fixed_scalar_mul_aux ws k us (S i)
        (point_add acc
          (fixed_window_point w (window_digit k i)
            (Stdlib.Lists.List.nth i us 0))).
  Proof. reflexivity. Qed.

  Lemma fixed_scalar_mul_cons
      (w : fixed_window) (ws : fixed_table)
      (k : Z) (us : list Z) :
    fixed_scalar_mul (w :: ws) k us =
      fixed_scalar_mul_aux ws k us 1%nat
        (fixed_window_point w (window_digit k 0%nat)
          (Stdlib.Lists.List.nth 0%nat us 0)).
  Proof.
    unfold fixed_scalar_mul.
    cbn [fixed_scalar_mul_aux].
    rewrite point_add_identity_left.
    reflexivity.
  Qed.

  (** [0]·P is the identity — base case of the double-and-add recursion. *)
  Lemma scalar_mul_0 (P : Point.t) :
    scalar_mul 0 P = identity.
  Proof. reflexivity. Qed.

  (** Extraction is the [x] projection — kept as a definitional guard. *)
  Lemma extract_x_eq (P : Point.t) :
    extract_x P = P.(Point.x).
  Proof. reflexivity. Qed.
End EccSpec.
