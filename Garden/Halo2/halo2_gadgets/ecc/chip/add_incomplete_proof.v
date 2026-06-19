Require Import Garden.Halo2.main.
Require Import Garden.Halo2.proof.
Require Garden.Halo2.halo2_gadgets.ecc.chip.add_incomplete.
Require Import Garden.Halo2.halo2_gadgets.utilities_proof.
Require Import Garden.Orchard.columns.
Require Import Garden.Field.Field.
Require Import Garden.Field.FieldLemmas.
Require Import Garden.Field.FieldDiv.
Require Import Garden.Plonky3.M.

#[local] Existing Instance Primes.PallasPIsPrime.

Global Open Scope Z_scope.

Module IncompleteAddition.
  (* Incomplete point addition of [(x_p, y_p)] and [(x_q, y_q)], valid when
     [x_p <> x_q]. The result is the unique point determined by the two
     constraints of [incomplete_addition_gate]:
       lambda = (y_p - y_q) / (x_p - x_q)   (field division)
       x_r    = lambda^2 - x_p - x_q
       y_r    = lambda * (x_p - x_r) - y_p. *)
  Definition output {p : Z} `{Prime p}
      (x_p y_p x_q y_q : Z)
      : Point.t :=
    let lambda := BinOp.div (y_p -F y_q) (x_p -F x_q) in
    let x_r := square lambda -F x_p -F x_q in
    {|
      Point.x := x_r;
      Point.y := lambda *F (x_p -F x_r) -F y_p;
    |}.

  (* The next-row result point [(x_r, y_r)] read off advice columns A2/A3 is
     uniquely determined by the current-row inputs [(x_p, y_p)] on A0/A1 and
     [(x_q, y_q)] on A2/A3, given distinct x-coordinates [x_p <> x_q] (the gate
     is degenerate at [x_p = x_q], leaving the next-row cells free). *)
  Theorem deterministic
      {RegionId : Set} (Γ : Assignment.t columns RegionId) (region : RegionId) (row : Z)
      (Hselector : Γ ⊢ ⟦ Selector.QAddIncomplete ⟧ (region, row) <> 0)
      (Hx_distinct :
        Γ ⊢ ⟦ Expression.Advice Advice.A0 Rotation.cur ⟧ (region, row) <>
        Γ ⊢ ⟦ Expression.Advice Advice.A2 Rotation.cur ⟧ (region, row))
      (Hgate :
        Γ ⊢ ⟦ Garden.Halo2.halo2_gadgets.ecc.chip.add_incomplete
            .incomplete_addition_gate ⟧ (region, row)) :
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
    (* [Hx_distinct] gives [x_p -F x_q <> 0], so the field-division law
       ([BinOp.div x y *F y = x] for [y <> 0], from [Garden.Field.FieldDiv])
       determines [lambda]; the two gate constraints then pin [(x_r, y_r)]. *)
    unfold output, square.
    with_strategy opaque [BinOp.add BinOp.sub BinOp.mul BinOp.div UnOp.from]
      cbn in *.
    set (rc := rotated_row row Rotation.cur) in *.
    set (rn := rotated_row row Rotation.next) in *.
    set (xp := UnOp.from (Γ.(Assignment.advice) Advice.A0 region rc)) in *.
    set (yp := UnOp.from (Γ.(Assignment.advice) Advice.A1 region rc)) in *.
    set (xq := UnOp.from (Γ.(Assignment.advice) Advice.A2 region rc)) in *.
    set (yq := UnOp.from (Γ.(Assignment.advice) Advice.A3 region rc)) in *.
    set (XR := UnOp.from (Γ.(Assignment.advice) Advice.A2 region rn)) in *.
    set (YR := UnOp.from (Γ.(Assignment.advice) Advice.A3 region rn)) in *.
    destruct Hgate as (Hc1 & Hc2).
    specialize (Hc1 Hselector).
    specialize (Hc2 Hselector).
    set (N := yp -F yq) in *.
    set (d := xp -F xq) in *.
    set (L := BinOp.div N d) in *.
    assert (Hxp : UnOp.from xp = xp) by (unfold xp; apply FieldRewrite.from_from).
    assert (Hxq : UnOp.from xq = xq) by (unfold xq; apply FieldRewrite.from_from).
    (* The distinct x-coordinates give a nonzero divisor [d = x_p - x_q]. *)
    assert (Hd : UnOp.from d <> 0).
    { unfold d. rewrite FieldRewrite.from_sub. intro Hc.
      rewrite sub_zero_equiv in Hc. rewrite Hxp, Hxq in Hc.
      exact (Hx_distinct Hc). }
    assert (Hdd : UnOp.from (d *F d) <> 0)
      by (apply field_from_mul_nonzero; exact Hd).
    (* The field-division law pins the gradient: [lambda * d = y_p - y_q]. *)
    assert (Hlam : L *F d = N).
    { unfold L. rewrite div_mul.
      - unfold N, BinOp.sub. rewrite Zmod_mod. reflexivity.
      - unfold Primes.pallas_p, Primes.t_p. lia.
      - exact Hd. }
    (* Reduce the two gate polynomials to plain field equalities. *)
    apply sub_zero_equiv in Hc1.
    rewrite !FieldRewrite.from_mul in Hc1.
    apply sub_zero_equiv in Hc2.
    rewrite !FieldRewrite.from_mul in Hc2.
    (* x-coordinate: cancel the [d^2] factor against the secant constraint. *)
    assert (Hx_eq : UnOp.from (XR +F xq +F xp) = UnOp.from (L *F L)).
    { apply (field_mul_cancel_r _ _ (d *F d) Hdd).
      rewrite <- field_mul_assoc.
      rewrite <- (field_mul_swap_inner L d L d).
      rewrite !Hlam. exact Hc1. }
    assert (Hxr : XR = L *F L -F xp -F xq).
    { clear Hc1 Hc2 Hlam Hdd Hd. field_solve. }
    set (xrout := L *F L -F xp -F xq) in *.
    rewrite Hxr.
    (* y-coordinate: cancel the [d] factor against the line constraint. *)
    assert (Hy_eq : UnOp.from (YR +F yq) = UnOp.from (L *F (xq -F XR))).
    { apply (field_mul_cancel_r _ _ d Hd).
      transitivity (N *F (xq -F XR)).
      - exact Hc2.
      - rewrite <- Hlam, !field_mul_assoc, (field_mul_comm d (xq -F XR)).
        reflexivity. }
    assert (Hlam' : L *F xp -F L *F xq = N).
    { rewrite <- field_mul_sub_distr. exact Hlam. }
    rewrite Hxr in Hy_eq.
    rewrite field_mul_sub_distr in Hy_eq.
    unfold N in Hlam'.
    f_equal.
    rewrite field_mul_sub_distr.
    clear Hc1 Hc2 Hlam Hx_eq Hdd Hd Hxr.
    field_solve.
  Qed.
End IncompleteAddition.
