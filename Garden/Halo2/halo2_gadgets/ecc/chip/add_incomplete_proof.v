Require Import Garden.Halo2.main.
Require Import Garden.Halo2.proof.
Require Garden.Halo2.halo2_gadgets.ecc.chip.add_incomplete.
Require Import Garden.Halo2.halo2_gadgets.utilities_proof.
Require Import Garden.Orchard.columns.
Require Import Garden.Field.Field.
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
      (ρ : Evaluation.t columns)
      (Hselector : ⟦ Selector.QAddIncomplete ⟧ ρ <> 0)
      (Hx_distinct :
        ⟦ Expression.Advice Advice.A0 Rotation.cur ⟧ ρ <>
        ⟦ Expression.Advice Advice.A2 Rotation.cur ⟧ ρ)
      (Hgate :
        ⟦ Garden.Halo2.halo2_gadgets.ecc.chip.add_incomplete
            .incomplete_addition_gate ⟧ ρ) :
      {|
        Point.x := ⟦ Expression.Advice Advice.A2 Rotation.next ⟧ ρ;
        Point.y := ⟦ Expression.Advice Advice.A3 Rotation.next ⟧ ρ;
      |} =
        output
          (⟦ Expression.Advice Advice.A0 Rotation.cur ⟧ ρ)
          (⟦ Expression.Advice Advice.A1 Rotation.cur ⟧ ρ)
          (⟦ Expression.Advice Advice.A2 Rotation.cur ⟧ ρ)
          (⟦ Expression.Advice Advice.A3 Rotation.cur ⟧ ρ).
  Proof.
    (* [Hx_distinct] gives [x_p -F x_q <> 0], so the field-division law
       ([BinOp.div x y *F y = x] for [y <> 0], from [Garden.Field.FieldDiv])
       determines [lambda]; the two gate constraints then pin [(x_r, y_r)]. *)
  Admitted.
End IncompleteAddition.
