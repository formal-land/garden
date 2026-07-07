(** * The point-level Sinsemilla round, [q_s3 = 0] rows

    [SinsemillaHashRound.round_pins], the [q_s3]-independent common core
    shared with the final-row variant ([hash_to_point_round_final_proof.v]),
    and [SinsemillaHashRound.round_correct], its [q_s3 = 0] consumer; the
    shared definitions ([acc_at], [word_at], ...) live in
    [hash_to_point_proof.v] (module [SinsemillaHash], imported here). *)

Require Import Stdlib.Lists.List.
Require Import Garden.Halo2.main.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.lemmas.
Require Import Garden.Halo2.halo2_gadgets.utilities_proof.
Require Import Garden.Orchard.columns.
Require Import Garden.Field.Field.
Require Import Garden.Field.Lemmas.
Require Import Garden.Field.Div.
Require Garden.Halo2.halo2_gadgets.sinsemilla.chip.
Require Import Garden.Halo2.halo2_gadgets.sinsemilla.chip_proof.
Require Import Garden.Halo2.halo2_gadgets.sinsemilla.spec.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.spec.
Require Import Garden.Halo2.halo2_gadgets.ecc.chip.add_incomplete_proof.
Require Garden.Halo2.halo2_gadgets.ecc.chip.constants.
Require Import Garden.Plonky3.M.

Import ListNotations.

#[local] Existing Instance Primes.PallasPIsPrime.

Global Open Scope Z_scope.
Require Import Garden.Halo2.halo2_gadgets.sinsemilla.hash_to_point_proof.

Module SinsemillaHashRound.
  Import SinsemillaHash.

  (** Componentwise equality of points. *)
  Lemma point_ext (P Q : Point.t)
      (Hx : Point.x P = Point.x Q) (Hy : Point.y P = Point.y Q) : P = Q.
  Proof. destruct P, Q; cbn in *; now subst. Qed.

  (** A cell read at [Rotation.cur] of [row + 1] and one at [Rotation.next]
      of [row] address the same absolute row. *)
  Lemma rotated_row_next (row : Z) :
    rotated_row (row + 1) Rotation.cur = rotated_row row Rotation.next.
  Proof. unfold rotated_row; cbn; lia. Qed.

  (** An enabled selector ([= 1]) is nonzero — the shape the gate
      implications consume. *)
  Lemma one_nonzero (z : Z) (Hz : z = 1) : z <> 0.
  Proof. lia. Qed.

  (** The [q_s3]-independent common core of the two per-row round theorems
      ([round_correct] below and
      [SinsemillaHashRoundFinal.round_correct_final]): the lookup pins the
      witnessed [(x_p, y_p)] to the generator [S(w)]; [Hdeg1] then
      determines [lambda_1] as the first secant gradient through the
      field-division law, [Hdeg2] determines [lambda_2] as the second, and
      the "Secant line" constraint pins the next-row [x_a] cell to the
      round output's abscissa.  The last conjunct expresses the round
      output's ordinate as the secant combination of witnessed cells that
      the two [q_s3]-specific "y check" endgames consume. *)
  Theorem round_pins
      (Γ : Assignment.t columns RegionId.t) (region : RegionId.t) (row : Z)
      (q_sinsemilla1 : Selector.t) (q_sinsemilla2 : Fixed.t)
      (x_a x_p bits lambda_1 lambda_2 : Advice.t)
      (Hactive : Γ ⊢ ⟦ Expression.Selector q_sinsemilla1 ⟧ (region, row) = 1)
      (Hgate :
        Γ ⊢ ⟦ Garden.Halo2.halo2_gadgets.sinsemilla.chip
            .sinsemilla_gate q_sinsemilla1 q_sinsemilla2 x_a x_p lambda_1 lambda_2 ⟧
          (region, row))
      (Hload :
        interpret_facts Γ (layouter_facts
          Garden.Halo2.halo2_gadgets.sinsemilla.chip.load_generator_table))
      (Hlookup :
        eval_lookup_argument Γ (region, row) GeneratorTable.table_rows
          (Garden.Halo2.halo2_gadgets.sinsemilla.chip.generator_table_argument
            q_sinsemilla1 q_sinsemilla2 x_a x_p bits lambda_1 lambda_2))
      (Hdeg1 :
        Point.x (acc_at Γ x_a x_p lambda_1 lambda_2 region row) <>
        Point.x (SinsemillaSpec.generator
          (word_at Γ q_sinsemilla2 bits region row)))
      (Hdeg2 :
        Point.x (acc_at Γ x_a x_p lambda_1 lambda_2 region row) <>
        Point.x (EccSpec.point_add_incomplete
          (acc_at Γ x_a x_p lambda_1 lambda_2 region row)
          (SinsemillaSpec.generator
            (word_at Γ q_sinsemilla2 bits region row)))) :
    (Γ ⊢ ⟦ Expression.Advice lambda_1 Rotation.cur ⟧ (region, row)) =
      UnOp.from (BinOp.div
        (Point.y (acc_at Γ x_a x_p lambda_1 lambda_2 region row) -F
          Point.y (SinsemillaSpec.generator
            (word_at Γ q_sinsemilla2 bits region row)))
        (Point.x (acc_at Γ x_a x_p lambda_1 lambda_2 region row) -F
          Point.x (SinsemillaSpec.generator
            (word_at Γ q_sinsemilla2 bits region row)))) /\
    (Γ ⊢ ⟦ Expression.Advice lambda_2 Rotation.cur ⟧ (region, row)) =
      UnOp.from (BinOp.div
        (Point.y (EccSpec.point_add_incomplete
            (acc_at Γ x_a x_p lambda_1 lambda_2 region row)
            (SinsemillaSpec.generator
              (word_at Γ q_sinsemilla2 bits region row))) -F
          Point.y (acc_at Γ x_a x_p lambda_1 lambda_2 region row))
        (Point.x (EccSpec.point_add_incomplete
            (acc_at Γ x_a x_p lambda_1 lambda_2 region row)
            (SinsemillaSpec.generator
              (word_at Γ q_sinsemilla2 bits region row))) -F
          Point.x (acc_at Γ x_a x_p lambda_1 lambda_2 region row))) /\
    (Γ ⊢ ⟦ Expression.Advice x_a Rotation.cur ⟧ (region, row + 1)) =
      Point.x (SinsemillaSpec.round
        (acc_at Γ x_a x_p lambda_1 lambda_2 region row)
        (word_at Γ q_sinsemilla2 bits region row)) /\
    Point.y (SinsemillaSpec.round
        (acc_at Γ x_a x_p lambda_1 lambda_2 region row)
        (word_at Γ q_sinsemilla2 bits region row)) =
      (Γ ⊢ ⟦ Expression.Advice lambda_2 Rotation.cur ⟧ (region, row)) *F
        ((Γ ⊢ ⟦ Garden.Halo2.halo2_gadgets.sinsemilla.chip
            .x_r x_a x_p lambda_1 Rotation.cur ⟧ (region, row)) -F
          (Γ ⊢ ⟦ Expression.Advice x_a Rotation.cur ⟧ (region, row + 1))) -F
      ((Γ ⊢ ⟦ Expression.Advice lambda_1 Rotation.cur ⟧ (region, row)) *F
        ((Γ ⊢ ⟦ Expression.Advice x_a Rotation.cur ⟧ (region, row)) -F
          (Γ ⊢ ⟦ Garden.Halo2.halo2_gadgets.sinsemilla.chip
              .x_r x_a x_p lambda_1 Rotation.cur ⟧ (region, row))) -F
        Point.y (acc_at Γ x_a x_p lambda_1 lambda_2 region row)).
  Proof.
    pose proof (GeneratorTable.sound Γ region row q_sinsemilla1 q_sinsemilla2
        x_a x_p bits lambda_1 lambda_2 Hload Hactive Hlookup)
      as (w & Hw & Hword & Hx_p & Hy_p).
    clear Hload Hlookup.
    unfold word_at in *.
    rewrite Hword in Hdeg1, Hdeg2 |- *.
    unfold Garden.Halo2.halo2_gadgets.sinsemilla.chip.sinsemilla_s_x,
      Garden.Halo2.halo2_gadgets.sinsemilla.chip.sinsemilla_s_y in Hx_p, Hy_p.
    unfold acc_at, SinsemillaSpec.round, SinsemillaSpec.generator,
      EccSpec.point_add_incomplete, IncompleteAddition.output,
      Garden.Halo2.halo2_gadgets.utilities_proof.square in *.
    with_strategy opaque [BinOp.add BinOp.sub BinOp.mul BinOp.div UnOp.from
      Garden.Halo2.halo2_gadgets.ecc.chip.constants.two_inv
      Garden.Halo2.halo2_gadgets.sinsemilla.sinsemilla_s.x
      Garden.Halo2.halo2_gadgets.sinsemilla.sinsemilla_s.y]
      cbn in Hactive, Hgate, Hdeg1, Hdeg2, Hx_p, Hy_p |- *.
    rewrite (rotated_row_next row).
    rewrite (FieldRewrite.mul_from_right _ constants.two_inv) in Hy_p.
    rewrite Hx_p in Hgate, Hy_p, Hdeg2 |- *.
    destruct Hgate as [Hsecant Hy].
    specialize (Hsecant (one_nonzero _ Hactive)).
    (* The "y check" conjunct is the [q_s3]-dependent part: not consumed
       here. *)
    clear Hy Hactive Hword.
    (* Name the current- and next-row cell values and the derived quantities:
       [xr]/[Y] the current-row [x_r]/[y_a] combinations and [yv] the actual
       accumulator ordinate. *)
    set (xa := UnOp.from
      (Γ.(Assignment.advice) x_a region (rotated_row row Rotation.cur))) in *.
    set (l1 := UnOp.from
      (Γ.(Assignment.advice) lambda_1 region (rotated_row row Rotation.cur))) in *.
    set (l2 := UnOp.from
      (Γ.(Assignment.advice) lambda_2 region (rotated_row row Rotation.cur))) in *.
    set (xa' := UnOp.from
      (Γ.(Assignment.advice) x_a region (rotated_row row Rotation.next))) in *.
    set (sx := sinsemilla_s.x w) in *.
    set (sy := sinsemilla_s.y w) in *.
    set (tinv := constants.two_inv) in *.
    set (xr := l1 *F l1 -F xa -F sx) in *.
    set (Y := (l1 +F l2) *F (xa -F xr)) in *.
    set (yv := Y *F tinv) in *.
    (* The specification-side quantities: the two division-based gradients
       [L]/[M] and the two chained incomplete additions. *)
    set (d1 := xa -F sx) in *.
    set (L := BinOp.div (yv -F sy) d1) in *.
    set (xR := L *F L -F xa -F sx) in *.
    set (yR := L *F (xa -F xR) -F yv) in *.
    set (d2 := xR -F xa) in *.
    set (M := BinOp.div (yR -F yv) d2) in *.
    set (x2 := M *F M -F xR -F xa) in *.
    set (y2 := M *F (xR -F x2) -F yR) in *.
    (* Reducedness of the named values (cell reads and [BinOp] results). *)
    assert (Hxa_red : UnOp.from xa = xa)
      by (unfold xa; apply FieldRewrite.from_from).
    assert (Hxa'_red : UnOp.from xa' = xa')
      by (unfold xa'; apply FieldRewrite.from_from).
    assert (Hl1_red : UnOp.from l1 = l1)
      by (unfold l1; apply FieldRewrite.from_from).
    assert (Hl2_red : UnOp.from l2 = l2)
      by (unfold l2; apply FieldRewrite.from_from).
    assert (Hsx_red : UnOp.from sx = sx)
      by (rewrite <- Hx_p; apply FieldRewrite.from_from).
    assert (HY_red : UnOp.from Y = Y) by (unfold Y; apply from_mul_reduced).
    assert (HxR_red : UnOp.from xR = xR) by (unfold xR; apply from_sub_reduced).
    (* First addition: [Hdeg1] makes the divisor [d1] nonzero, the division
       law recovers [L * d1], and the [y_p] lookup slot gives the same product
       for the witnessed [lambda_1], so cancellation pins [lambda_1 = L]. *)
    assert (Hd1 : UnOp.from d1 <> 0).
    { unfold d1. rewrite FieldRewrite.from_sub. intro Hc.
      rewrite sub_zero_equiv in Hc. rewrite Hxa_red, Hsx_red in Hc.
      exact (Hdeg1 Hc). }
    assert (HL : L *F d1 = yv -F sy).
    { unfold L. rewrite div_mul.
      - apply from_sub_reduced.
      - unfold Primes.pallas_p, Primes.t_p; lia.
      - exact Hd1. }
    assert (Hl1d : l1 *F d1 = yv -F sy).
    { clear - Hy_p. field_solve. }
    assert (HLl1 : l1 *F d1 = L *F d1) by (rewrite Hl1d, HL; reflexivity).
    pose proof (field_mul_cancel_r l1 L d1 Hd1 HLl1) as Hl1L0.
    assert (Hl1L : l1 = UnOp.from L)
      by (rewrite <- Hl1L0, Hl1_red; reflexivity).
    (* Hence the circuit [x_r] is the specification first-sum abscissa. *)
    assert (HxRr : xR = xr).
    { unfold xR, xr. rewrite Hl1L.
      now rewrite FieldRewrite.mul_from_left, FieldRewrite.mul_from_right. }
    (* Second addition: [Hdeg2] makes [d2] nonzero, and the [y_a] combination
       identity yields the same product for the witnessed [lambda_2]. *)
    assert (Hd2eq : d2 = xr -F xa) by (unfold d2; rewrite HxRr; reflexivity).
    assert (Hd2 : UnOp.from d2 <> 0).
    { unfold d2. rewrite FieldRewrite.from_sub. intro Hc.
      rewrite sub_zero_equiv in Hc. rewrite HxR_red, Hxa_red in Hc.
      exact (Hdeg2 (eq_sym Hc)). }
    assert (HM : M *F d2 = yR -F yv).
    { unfold M. rewrite div_mul.
      - apply from_sub_reduced.
      - unfold Primes.pallas_p, Primes.t_p; lia.
      - exact Hd2. }
    assert (HyRe : yR = l1 *F (xa -F xr) -F yv).
    { unfold yR. rewrite HxRr. rewrite Hl1L.
      now rewrite FieldRewrite.mul_from_left. }
    assert (H2yv : UnOp.from 2 *F yv = Y).
    { unfold yv, tinv. rewrite double_half. apply HY_red. }
    assert (HYexp : Y = l1 *F (xa -F xr) +F l2 *F (xa -F xr)).
    { unfold Y, BinOp.mul, BinOp.add.
      rewrite Zmult_mod_idemp_l, <- Zplus_mod.
      change Primes.pallas_p with
        28948022309329048855892746252171976963363056481941560715954676764349967630337.
      f_equal; ring. }
    assert (Hl2d : l2 *F d2 = yR -F yv).
    { rewrite Hd2eq, HyRe.
      rewrite (field_mul_sub_distr l2 xr xa), (field_mul_sub_distr l1 xa xr).
      rewrite (field_mul_sub_distr l1 xa xr),
        (field_mul_sub_distr l2 xa xr) in HYexp.
      clear - HYexp H2yv. field_solve. }
    assert (HMl2 : l2 *F d2 = M *F d2) by (rewrite Hl2d, HM; reflexivity).
    pose proof (field_mul_cancel_r l2 M d2 Hd2 HMl2) as Hl2M0.
    assert (Hl2M : l2 = UnOp.from M)
      by (rewrite <- Hl2M0, Hl2_red; reflexivity).
    (* x-coordinate: the "Secant line" constraint against the spec [x2]. *)
    assert (Hx2 : x2 = l2 *F l2 -F xr -F xa).
    { unfold x2. rewrite HxRr, Hl2M.
      now rewrite FieldRewrite.mul_from_left, FieldRewrite.mul_from_right. }
    assert (Hxfinal : xa' = x2).
    { rewrite Hx2. clear - Hsecant Hxa'_red. field_solve. }
    (* y-coordinate: the spec ordinate in circuit terms. *)
    assert (Hy2e : y2 = l2 *F (xr -F xa') -F (l1 *F (xa -F xr) -F yv)).
    { unfold y2. rewrite HxRr. rewrite <- Hxfinal. rewrite HyRe. rewrite Hl2M.
      now rewrite FieldRewrite.mul_from_left. }
    exact (conj Hl1L (conj Hl2M (conj Hxfinal Hy2e))).
  Qed.

  (** The [q_s3 = 0] "y check" endgame as a field identity over named cell
      values: the collapsed constraint
      [4 lambda_2 (x_a - x_a') = 2 y_a + 2 y_a'] only determines the doubled
      next-row combination [Y'], so the target ordinate equality is doubled
      and the invertible factor [2] cancelled.  [(l1 + l2) (xa - xr)] is the
      current-row [y_a] combination, halved by [two_inv] into the actual
      accumulator ordinate. *)
  Lemma y_check_zero (l1 l2 xa xa' xr Y' : Z)
      (HY'_red : UnOp.from Y' = Y')
      (Hy : l2 *F UnOp.from 4 *F (xa -F xa') =
        (l1 +F l2) *F (xa -F xr) *F UnOp.from 2 +F UnOp.from 2 *F Y') :
    Y' *F Garden.Halo2.halo2_gadgets.ecc.chip.constants.two_inv =
      l2 *F (xr -F xa') -F
        (l1 *F (xa -F xr) -F
          (l1 +F l2) *F (xa -F xr) *F
            Garden.Halo2.halo2_gadgets.ecc.chip.constants.two_inv).
  Proof.
    set (Y := (l1 +F l2) *F (xa -F xr)) in *.
    set (tinv := constants.two_inv) in *.
    set (yv := Y *F tinv) in *.
    assert (HY_red : UnOp.from Y = Y) by (unfold Y; apply from_mul_reduced).
    assert (H2yv : UnOp.from 2 *F yv = Y).
    { unfold yv, tinv. rewrite double_half. apply HY_red. }
    assert (HYexp : Y = l1 *F (xa -F xr) +F l2 *F (xa -F xr)).
    { unfold Y, BinOp.mul, BinOp.add.
      rewrite Zmult_mod_idemp_l, <- Zplus_mod.
      change Primes.pallas_p with
        28948022309329048855892746252171976963363056481941560715954676764349967630337.
      f_equal; ring. }
    rewrite (field_mul_comm l2 (UnOp.from 4)) in Hy.
    rewrite (field_mul_assoc (UnOp.from 4) l2 (xa -F xa')) in Hy.
    rewrite (FieldRewrite.mul_from_left 4 (l2 *F (xa -F xa'))) in Hy.
    rewrite (FieldRewrite.mul_from_right Y 2) in Hy.
    rewrite (FieldRewrite.mul_from_left 2 Y') in Hy.
    rewrite (field_mul_sub_distr l2 xa xa') in Hy.
    rewrite (field_mul_sub_distr l1 xa xr),
      (field_mul_sub_distr l2 xa xr) in HYexp.
    assert (H2ne : UnOp.from (UnOp.from 2) <> 0).
    { rewrite FieldRewrite.from_from.
      unfold UnOp.from, Primes.pallas_p, Primes.t_p. lia. }
    assert (Hdbl : (Y' *F tinv) *F UnOp.from 2 =
        (l2 *F (xr -F xa') -F (l1 *F (xa -F xr) -F yv)) *F UnOp.from 2).
    { rewrite (field_mul_comm (Y' *F tinv) (UnOp.from 2)).
      unfold tinv. rewrite double_half. rewrite HY'_red.
      rewrite (field_mul_comm
        (l2 *F (xr -F xa') -F (l1 *F (xa -F xr) -F yv)) (UnOp.from 2)).
      rewrite (FieldRewrite.mul_from_left 2
        (l2 *F (xr -F xa') -F (l1 *F (xa -F xr) -F yv))).
      rewrite (field_mul_sub_distr l2 xr xa'), (field_mul_sub_distr l1 xa xr).
      clear - Hy H2yv HYexp HY'_red. field_solve. }
    pose proof (field_mul_cancel_r (Y' *F tinv)
        (l2 *F (xr -F xa') -F (l1 *F (xa -F xr) -F yv)) (UnOp.from 2)
        H2ne Hdbl)
      as Hyfin0.
    exact (eq_trans (eq_trans (eq_sym (from_mul_reduced Y' tinv)) Hyfin0)
      (from_sub_reduced _ _)).
  Qed.

  Theorem round_correct
      (Γ : Assignment.t columns RegionId.t) (region : RegionId.t) (row : Z)
      (q_sinsemilla1 : Selector.t) (q_sinsemilla2 : Fixed.t)
      (x_a x_p bits lambda_1 lambda_2 : Advice.t)
      (Hactive : Γ ⊢ ⟦ Expression.Selector q_sinsemilla1 ⟧ (region, row) = 1)
      (Hgate :
        Γ ⊢ ⟦ Garden.Halo2.halo2_gadgets.sinsemilla.chip
            .sinsemilla_gate q_sinsemilla1 q_sinsemilla2 x_a x_p lambda_1 lambda_2 ⟧
          (region, row))
      (Hload :
        interpret_facts Γ (layouter_facts
          Garden.Halo2.halo2_gadgets.sinsemilla.chip.load_generator_table))
      (Hlookup :
        eval_lookup_argument Γ (region, row) GeneratorTable.table_rows
          (Garden.Halo2.halo2_gadgets.sinsemilla.chip.generator_table_argument
            q_sinsemilla1 q_sinsemilla2 x_a x_p bits lambda_1 lambda_2))
      (Hq_s3 :
        Γ ⊢ ⟦ Garden.Halo2.halo2_gadgets.sinsemilla.chip.q_s3 q_sinsemilla2 ⟧
          (region, row) = 0)
      (Hdeg1 :
        Point.x (acc_at Γ x_a x_p lambda_1 lambda_2 region row) <>
        Point.x (SinsemillaSpec.generator
          (word_at Γ q_sinsemilla2 bits region row)))
      (Hdeg2 :
        Point.x (acc_at Γ x_a x_p lambda_1 lambda_2 region row) <>
        Point.x (EccSpec.point_add_incomplete
          (acc_at Γ x_a x_p lambda_1 lambda_2 region row)
          (SinsemillaSpec.generator
            (word_at Γ q_sinsemilla2 bits region row)))) :
    acc_at Γ x_a x_p lambda_1 lambda_2 region (row + 1) =
      SinsemillaSpec.round
        (acc_at Γ x_a x_p lambda_1 lambda_2 region row)
        (word_at Γ q_sinsemilla2 bits region row).
  Proof.
    (* [round_pins] pins the abscissa and expresses the round ordinate in
       cell terms; the collapsed [q_s3 = 0] "y check" then hands the doubled
       next-row ordinate combination to [y_check_zero]. *)
    pose proof (round_pins Γ region row q_sinsemilla1 q_sinsemilla2
        x_a x_p bits lambda_1 lambda_2 Hactive Hgate Hload Hlookup Hdeg1 Hdeg2)
      as (_ & _ & Hxpin & Hypin).
    clear Hload Hlookup Hdeg1 Hdeg2.
    apply point_ext; [exact Hxpin |].
    rewrite Hypin.
    clear Hxpin Hypin.
    unfold acc_at.
    with_strategy opaque [BinOp.add BinOp.sub BinOp.mul BinOp.div UnOp.from
      Garden.Halo2.halo2_gadgets.ecc.chip.constants.two_inv]
      cbn in Hactive, Hgate, Hq_s3 |- *.
    rewrite (rotated_row_next row).
    destruct Hgate as [_ Hy].
    specialize (Hy (one_nonzero _ Hactive)).
    (* On a [q_s3 = 0] row the "y check" collapses to
       [4 lambda_2 (x_a - x_a') = 2 y_a + 2 y_a']. *)
    rewrite Hq_s3 in Hy.
    rewrite !FieldRewrite.mul_zero_left in Hy.
    rewrite FieldRewrite.add_zero_right in Hy.
    rewrite FieldRewrite.from_add in Hy.
    rewrite FieldRewrite.sub_zero_right in Hy.
    rewrite FieldRewrite.from_from in Hy.
    exact (y_check_zero _ _ _ _ _ _ (from_mul_reduced _ _) Hy).
  Qed.
End SinsemillaHashRound.
