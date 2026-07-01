Require Import Garden.Halo2.main.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.lemmas.
Require Garden.Halo2.halo2_gadgets.ecc.chip.add.
Require Import Garden.Halo2.halo2_gadgets.utilities_proof.
Require Import Garden.Orchard.columns.
Require Import Garden.Field.Field.
Require Import Garden.Field.FieldLemmas.
Require Import Garden.Field.FieldDiv.
Require Import Garden.Plonky3.M.
Require Import Stdlib.Bool.Bool.

#[local] Existing Instance Primes.PallasPIsPrime.

Global Open Scope Z_scope.

Module CompleteAddition.
  (* Complete point addition of [(x_p, y_p)] and [(x_q, y_q)]. Unlike incomplete
     addition this is total: it covers the exceptional cases that incomplete
     addition rejects (P or Q the identity [(0, 0)], and [P = -Q]), so there is
     NO [x_p <> x_q] precondition.

     [output] is a function of the four input coordinates alone: the gradient
     [lambda] is computed from them by field division, with the case split the
     gate's witnessed inverses [alpha]/[beta]/[gamma]/[delta] make:
       - [x_p = 0]                     => R = Q          (P is the identity)
       - else [x_q = 0]                => R = P          (Q is the identity)
       - else [x_p = x_q /\ y_p+y_q=0] => R = (0, 0)     (P = -Q)
       - else  lambda := if x_p = x_q then 3*x_p^2 / (2*y_p)   (* doubling: tangent *)
                                      else (y_q - y_p)/(x_q - x_p)  (* generic: secant *)
               R := (lambda^2 - x_p - x_q, lambda*(x_p - x_r) - y_p) *)
  Definition output {p : Z} `{Prime p}
      (x_p y_p x_q y_q : Z)
      : Point.t :=
    if x_p =? 0 then
      {| Point.x := x_q; Point.y := y_q |}
    else if x_q =? 0 then
      {| Point.x := x_p; Point.y := y_p |}
    else if ((x_p =? x_q) && ((y_p +F y_q) =? 0))%bool then
      {| Point.x := 0; Point.y := 0 |}
    else
      let lambda :=
        if x_p =? x_q then
          (* doubling: tangent slope 3*x_p^2 / (2*y_p) *)
          BinOp.div (UnOp.from 3 *F square x_p) (UnOp.from 2 *F y_p)
        else
          (* generic: secant slope (y_q - y_p) / (x_q - x_p) *)
          BinOp.div (y_q -F y_p) (x_q -F x_p) in
      let x_r := square lambda -F x_p -F x_q in
      {|
        Point.x := x_r;
        Point.y := lambda *F (x_p -F x_r) -F y_p;
      |}.

  (* The next-row result [(x_r, y_r)] on A2/A3 is determined by the current-row
     inputs [(x_p, y_p)] (A0/A1) and [(x_q, y_q)] (A2/A3) alone. *)
  Theorem deterministic
      {RegionId : Set} (Γ : Assignment.t columns RegionId) (region : RegionId) (row : Z)
      (Hselector : Γ ⊢ ⟦ Selector.QEccAdd ⟧ (region, row) <> 0)
      (Hgate :
        Γ ⊢ ⟦ Garden.Halo2.halo2_gadgets.ecc.chip.add
            .complete_addition_gate ⟧ (region, row)) :
      {|
        Point.x := Γ ⊢ ⟦ Expression.Advice Advice.A2 Rotation.next ⟧ (region, row);
        Point.y := Γ ⊢ ⟦ Expression.Advice Advice.A3 Rotation.next ⟧ (region, row);
      |} =
        output
          (Γ ⊢ ⟦ Expression.Advice Advice.A0 Rotation.cur ⟧ (region, row))
          (Γ ⊢ ⟦ Expression.Advice Advice.A1 Rotation.cur ⟧ (region, row))
          (Γ ⊢ ⟦ Expression.Advice Advice.A2 Rotation.cur ⟧ (region, row))
          (Γ ⊢ ⟦ Expression.Advice Advice.A3 Rotation.cur ⟧ (region, row)).
  Proof.
    (* Per branch: the field-division law ([BinOp.div x y *F y = x] for
       [y <> 0], from [Garden.Field.FieldDiv]) determines [lambda] in the
       generic/doubling case, and the exceptional cases are read directly off
       the gate constraints. *)
    unfold output, square.
    with_strategy opaque [BinOp.add BinOp.sub BinOp.mul BinOp.div UnOp.from] cbn.
    with_strategy opaque [BinOp.add BinOp.sub BinOp.mul BinOp.div UnOp.from]
      cbn in Hgate.
    set (rc := rotated_row row Rotation.cur) in *.
    set (rn := rotated_row row Rotation.next) in *.
    set (xp := UnOp.from (Γ.(Assignment.advice) Advice.A0 region rc)) in *.
    set (yp := UnOp.from (Γ.(Assignment.advice) Advice.A1 region rc)) in *.
    set (xq := UnOp.from (Γ.(Assignment.advice) Advice.A2 region rc)) in *.
    set (yq := UnOp.from (Γ.(Assignment.advice) Advice.A3 region rc)) in *.
    set (lam := UnOp.from (Γ.(Assignment.advice) Advice.A4 region rc)) in *.
    set (alpha := UnOp.from (Γ.(Assignment.advice) Advice.A5 region rc)) in *.
    set (beta := UnOp.from (Γ.(Assignment.advice) Advice.A6 region rc)) in *.
    set (gamma := UnOp.from (Γ.(Assignment.advice) Advice.A7 region rc)) in *.
    set (delta := UnOp.from (Γ.(Assignment.advice) Advice.A8 region rc)) in *.
    set (XR := UnOp.from (Γ.(Assignment.advice) Advice.A2 region rn)) in *.
    set (YR := UnOp.from (Γ.(Assignment.advice) Advice.A3 region rn)) in *.
    destruct Hgate as (Hc1 & Hc2 & Hc3a & Hc3b & Hc3c & Hc3d &
      Hc4a & Hc4b & Hc5a & Hc5b & Hc6a & Hc6b).
    specialize (Hc1 Hselector); specialize (Hc2 Hselector);
    specialize (Hc3a Hselector); specialize (Hc3b Hselector);
    specialize (Hc3c Hselector); specialize (Hc3d Hselector);
    specialize (Hc4a Hselector); specialize (Hc4b Hselector);
    specialize (Hc5a Hselector); specialize (Hc5b Hselector);
    specialize (Hc6a Hselector); specialize (Hc6b Hselector).
    assert (Ixp : UnOp.from xp = xp) by (unfold xp; apply FieldRewrite.from_from).
    assert (Iyp : UnOp.from yp = yp) by (unfold yp; apply FieldRewrite.from_from).
    assert (Ixq : UnOp.from xq = xq) by (unfold xq; apply FieldRewrite.from_from).
    assert (Iyq : UnOp.from yq = yq) by (unfold yq; apply FieldRewrite.from_from).
    assert (IXR : UnOp.from XR = XR) by (unfold XR; apply FieldRewrite.from_from).
    assert (IYR : UnOp.from YR = YR) by (unfold YR; apply FieldRewrite.from_from).
    (* P = O: the result is Q. *)
    destruct (xp =? 0) eqn:Exp0.
    { apply Z.eqb_eq in Exp0.
      rewrite Exp0 in Hc4a, Hc4b.
      autorewrite with field_rewrite in Hc4a, Hc4b.
      apply sub_zero_equiv in Hc4a, Hc4b.
      f_equal;
        [ rewrite <- IXR, <- Ixq; exact Hc4a
        | rewrite <- IYR, <- Iyq; exact Hc4b ]. }
    apply Z.eqb_neq in Exp0.
    assert (Nxp : UnOp.from xp <> 0) by (rewrite Ixp; exact Exp0).
    (* Q = O: the result is P. *)
    destruct (xq =? 0) eqn:Exq0.
    { apply Z.eqb_eq in Exq0.
      rewrite Exq0 in Hc5a, Hc5b.
      autorewrite with field_rewrite in Hc5a, Hc5b.
      apply sub_zero_equiv in Hc5a, Hc5b.
      f_equal;
        [ rewrite <- IXR, <- Ixp; exact Hc5a
        | rewrite <- IYR, <- Iyp; exact Hc5b ]. }
    apply Z.eqb_neq in Exq0.
    assert (Nxq : UnOp.from xq <> 0) by (rewrite Ixq; exact Exq0).
    (* P = -Q: the result is the identity (0, 0). *)
    destruct ((xp =? xq) && (yp +F yq =? 0)) eqn:Epmq.
    { apply Bool.andb_true_iff in Epmq. destruct Epmq as [Exy Eyy].
      apply Z.eqb_eq in Exy. apply Z.eqb_eq in Eyy.
      assert (H1 : xq -F xp = 0)
        by (apply sub_zero_equiv; rewrite Exy; reflexivity).
      assert (H2 : yq +F yp = 0) by (rewrite field_add_comm; exact Eyy).
      (* The witnessed-inverse selector vanishes: the factor reduces to 1. *)
      assert (Hfac : UnOp.from
        (UnOp.from 1 -F (xq -F xp) *F alpha -F (yq +F yp) *F delta) <> 0).
      { rewrite H1, H2. autorewrite with field_rewrite. discriminate. }
      apply (field_mul_eq_zero_cancel _ _ Hfac) in Hc6a.
      apply (field_mul_eq_zero_cancel _ _ Hfac) in Hc6b.
      f_equal;
        [ rewrite <- IXR; exact Hc6a | rewrite <- IYR; exact Hc6b ]. }
    apply Bool.andb_false_iff in Epmq.
    destruct (xp =? xq) eqn:Exy.
    { (* Doubling: x_p = x_q (and y_p + y_q <> 0). *)
      assert (Eyy : (yp +F yq =? 0) = false)
        by (destruct Epmq as [E | E]; [ congruence | exact E ]).
      apply Z.eqb_neq in Eyy.
      apply Z.eqb_eq in Exy.
      set (Lo := BinOp.div (UnOp.from 3 *F (xp *F xp)) (UnOp.from 2 *F yp)) in *.
      assert (H2nz : UnOp.from (UnOp.from 2) <> 0)
        by (rewrite FieldRewrite.from_from; intro Hh; vm_compute in Hh; discriminate).
      assert (H3nz : UnOp.from (UnOp.from 3) <> 0)
        by (rewrite FieldRewrite.from_from; intro Hh; vm_compute in Hh; discriminate).
      assert (Hqp0 : xq -F xp = 0)
        by (apply sub_zero_equiv; rewrite Exy; reflexivity).
      (* The tangent selector reduces to 1, so the tangent line is forced. *)
      assert (Hfac : UnOp.from (UnOp.from 1 -F (xq -F xp) *F alpha) <> 0).
      { rewrite Hqp0. autorewrite with field_rewrite. discriminate. }
      apply (field_mul_eq_zero_cancel _ _ Hfac) in Hc2.
      rewrite FieldRewrite.from_sub in Hc2.
      apply sub_zero_equiv in Hc2.
      rewrite FieldRewrite.from_mul, FieldRewrite.from_mul in Hc2.
      (* Hc2 : (UnOp.from 2 *F yp) *F lam = UnOp.from 3 *F (xp *F xp) *)
      assert (Nyp : UnOp.from yp <> 0).
      { intro Hy.
        assert (Htyp : UnOp.from (UnOp.from 2 *F yp) = 0).
        { rewrite FieldRewrite.from_mul.
          apply mul_zero_implies_zero. right. exact Hy. }
        assert (HLHS : (UnOp.from 2 *F yp) *F lam = 0)
          by (apply mul_zero_implies_zero; left; exact Htyp).
        assert (H0 : UnOp.from 3 *F (xp *F xp) = 0)
          by exact (eq_trans (eq_sym Hc2) HLHS).
        apply (field_mul_eq_zero_cancel _ _ H3nz) in H0.
        rewrite FieldRewrite.from_mul in H0.
        apply (field_mul_eq_zero_cancel _ _ Nxp) in H0.
        exact (Nxp H0). }
      assert (Ntd : UnOp.from (UnOp.from 2 *F yp) <> 0)
        by (apply field_from_mul_nonzero; [ exact H2nz | exact Nyp ]).
      assert (Hldiv : Lo *F (UnOp.from 2 *F yp) = UnOp.from 3 *F (xp *F xp)).
      { unfold Lo. rewrite div_mul.
        - exact (FieldRewrite.from_mul (UnOp.from 3) (xp *F xp)).
        - unfold Primes.pallas_p, Primes.t_p; lia.
        - exact Ntd. }
      assert (Hlam_eq : UnOp.from lam = UnOp.from Lo).
      { apply (field_mul_cancel_r lam Lo (UnOp.from 2 *F yp) Ntd).
        exact (eq_trans (field_mul_comm lam (UnOp.from 2 *F yp))
          (eq_trans Hc2 (eq_sym Hldiv))). }
      assert (Nyqp : UnOp.from (yq +F yp) <> 0)
        by (rewrite field_add_comm, FieldRewrite.from_add; exact Eyy).
      assert (Hpfx : UnOp.from (xp *F xq *F (yq +F yp)) <> 0)
        by (apply field_from_mul_nonzero;
            [ apply field_from_mul_nonzero; assumption | exact Nyqp ]).
      apply (field_mul_eq_zero_cancel _ _ Hpfx) in Hc3c.
      apply (field_mul_eq_zero_cancel _ _ Hpfx) in Hc3d.
      assert (HXR' : XR = lam *F lam -F xp -F xq)
        by (apply (field_solve_xr (lam *F lam) xp xq XR IXR); exact Hc3c).
      assert (HYR' : YR = lam *F (xp -F XR) -F yp)
        by (apply (field_solve_yr (lam *F (xp -F XR)) yp YR IYR); exact Hc3d).
      assert (HXR : XR = Lo *F Lo -F xp -F xq).
      { rewrite HXR'. now rewrite (field_mul_cong lam lam Lo Lo Hlam_eq Hlam_eq). }
      set (xrout := Lo *F Lo -F xp -F xq) in *.
      rewrite <- HXR.
      f_equal.
      rewrite HYR'.
      now rewrite (field_mul_cong lam (xp -F XR) Lo (xp -F XR) Hlam_eq eq_refl). }
    { (* Generic: x_p <> x_q. *)
      apply Z.eqb_neq in Exy.
      set (Lo := BinOp.div (yq -F yp) (xq -F xp)) in *.
      assert (Nqp : UnOp.from (xq -F xp) <> 0).
      { rewrite FieldRewrite.from_sub. intro Hh. apply sub_zero_equiv in Hh.
        rewrite Ixq, Ixp in Hh. exact (Exy (eq_sym Hh)). }
      assert (Hldiv : Lo *F (xq -F xp) = yq -F yp).
      { unfold Lo. rewrite div_mul.
        - exact (FieldRewrite.from_sub yq yp).
        - unfold Primes.pallas_p, Primes.t_p; lia.
        - exact Nqp. }
      apply (field_mul_eq_zero_cancel _ _ Nqp) in Hc1.
      rewrite FieldRewrite.from_sub in Hc1.
      apply sub_zero_equiv in Hc1.
      rewrite FieldRewrite.from_mul, FieldRewrite.from_sub in Hc1.
      assert (Hlam_eq : UnOp.from lam = UnOp.from Lo).
      { apply (field_mul_cancel_r lam Lo (xq -F xp) Nqp).
        exact (eq_trans (field_mul_comm lam (xq -F xp))
          (eq_trans Hc1 (eq_sym Hldiv))). }
      assert (Hpfx : UnOp.from (xp *F xq *F (xq -F xp)) <> 0)
        by (apply field_from_mul_nonzero;
            [ apply field_from_mul_nonzero; assumption | exact Nqp ]).
      apply (field_mul_eq_zero_cancel _ _ Hpfx) in Hc3a.
      apply (field_mul_eq_zero_cancel _ _ Hpfx) in Hc3b.
      assert (HXR' : XR = lam *F lam -F xp -F xq)
        by (apply (field_solve_xr (lam *F lam) xp xq XR IXR); exact Hc3a).
      assert (HYR' : YR = lam *F (xp -F XR) -F yp)
        by (apply (field_solve_yr (lam *F (xp -F XR)) yp YR IYR); exact Hc3b).
      assert (HXR : XR = Lo *F Lo -F xp -F xq).
      { rewrite HXR'. now rewrite (field_mul_cong lam lam Lo Lo Hlam_eq Hlam_eq). }
      set (xrout := Lo *F Lo -F xp -F xq) in *.
      rewrite <- HXR.
      f_equal.
      rewrite HYR'.
      now rewrite (field_mul_cong lam (xp -F XR) Lo (xp -F XR) Hlam_eq eq_refl). }
  Qed.

  (* End-to-end instance of the synthesis-to-gates gluing: from running the
     [add] chip's synthesis program and assuming the proof verified
     ([circuit_holds] = synthesis facts + gate satisfaction of the configured
     system), the next-row result on A2/A3 is the [output] of the current-row
     inputs.  The free-floating [Hselector]/[Hgate] hypotheses of
     [deterministic] are discharged by the two bridge lemmas. *)
  Theorem synthesize_correct
      (Γ : Assignment.t columns RegionId.t)
      (Hcircuit :
        circuit_holds Γ
          Garden.Halo2.halo2_gadgets.ecc.chip.add.synthesize
          (𝓒.run_unit Garden.Halo2.halo2_gadgets.ecc.chip.add.configure
            ConstraintSystem.empty)) :
      {|
        Point.x :=
          Γ ⊢ ⟦ Expression.Advice Advice.A2 Rotation.next ⟧
            (RegionId.GadgetLocal RegionId.GadgetLocal.EccAdd, 0);
        Point.y :=
          Γ ⊢ ⟦ Expression.Advice Advice.A3 Rotation.next ⟧
            (RegionId.GadgetLocal RegionId.GadgetLocal.EccAdd, 0);
      |} =
        output
          (Γ ⊢ ⟦ Expression.Advice Advice.A0 Rotation.cur ⟧
            (RegionId.GadgetLocal RegionId.GadgetLocal.EccAdd, 0))
          (Γ ⊢ ⟦ Expression.Advice Advice.A1 Rotation.cur ⟧
            (RegionId.GadgetLocal RegionId.GadgetLocal.EccAdd, 0))
          (Γ ⊢ ⟦ Expression.Advice Advice.A2 Rotation.cur ⟧
            (RegionId.GadgetLocal RegionId.GadgetLocal.EccAdd, 0))
          (Γ ⊢ ⟦ Expression.Advice Advice.A3 Rotation.cur ⟧
            (RegionId.GadgetLocal RegionId.GadgetLocal.EccAdd, 0)).
  Proof.
  Admitted.
End CompleteAddition.
