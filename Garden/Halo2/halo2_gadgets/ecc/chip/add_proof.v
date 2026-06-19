Require Import Garden.Halo2.main.
Require Import Garden.Halo2.proof.
Require Garden.Halo2.halo2_gadgets.ecc.chip.add.
Require Import Garden.Halo2.halo2_gadgets.utilities_proof.
Require Import Garden.Orchard.columns.
Require Import Garden.Field.Field.
Require Import Garden.Plonky3.M.

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
      (ρ : Evaluation.t columns)
      (Hselector : ⟦ Selector.QEccAdd ⟧ ρ <> 0)
      (Hgate :
        ⟦ Garden.Halo2.halo2_gadgets.ecc.chip.add
            .complete_addition_gate ⟧ ρ) :
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
    (* Per branch: the field-division law ([BinOp.div x y *F y = x] for
       [y <> 0], from [Garden.Field.FieldDiv]) determines [lambda] in the
       generic/doubling case, and the exceptional cases are read directly off
       the gate constraints. *)
  Admitted.
End CompleteAddition.
