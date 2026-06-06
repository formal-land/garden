Require Import Garden.Halo2.main.
Require Import Garden.Halo2.Gadgets.Ecc.chip.common.
Require Garden.Halo2.Gadgets.Utilities.
Require Garden.Halo2.Gadgets.Ecc.chip.constants.

Import ListNotations.
Global Open Scope pstring_scope.
Global Open Scope Z_scope.

Definition x_r
    (x_a x_p lambda_1 : Advice.t)
    (rotation : Rotation.t)
    : Expression.t columns :=
  let x_a := Expression.Advice x_a rotation in
  let x_p := Expression.Advice x_p rotation in
  let lambda_1 := Expression.Advice lambda_1 rotation in
  Garden.Halo2.Gadgets.Utilities.square lambda_1 -E x_a -E x_p.

Definition y_a
    (x_a x_p lambda_1 lambda_2 : Advice.t)
    (rotation : Rotation.t)
    : Expression.t columns :=
  let x_a_expr := Expression.Advice x_a rotation in
  let lambda_1_expr := Expression.Advice lambda_1 rotation in
  let lambda_2_expr := Expression.Advice lambda_2 rotation in
  ((lambda_1_expr +E lambda_2_expr)
    *E (x_a_expr -E x_r x_a x_p lambda_1 rotation))
    *Z Garden.Halo2.Gadgets.Ecc.chip.constants.two_inv.

Definition for_loop
    (z x_a x_p y_p lambda_1 lambda_2 : Advice.t)
    (y_a_next : Expression.t columns)
    : Constraints.t columns :=
  let z_cur := Expression.Advice z Rotation.cur in
  let z_prev := Expression.Advice z Rotation.prev in
  let x_a_cur := Expression.Advice x_a Rotation.cur in
  let x_a_next := Expression.Advice x_a Rotation.next in
  let x_p_cur := Expression.Advice x_p Rotation.cur in
  let y_p_cur := Expression.Advice y_p Rotation.cur in
  let lambda1_cur := Expression.Advice lambda_1 Rotation.cur in
  let lambda2_cur := Expression.Advice lambda_2 Rotation.cur in
  let y_a_cur := y_a x_a x_p lambda_1 lambda_2 Rotation.cur in
  let k := z_cur -E (z_prev *Z 2) in
  let bool_check := Garden.Halo2.Gadgets.Utilities.bool_check k in
  let gradient_1 :=
    lambda1_cur *E (x_a_cur -E x_p_cur)
      -E y_a_cur
      +E ((k *Z 2 -E Expression.Constant 1) *E y_p_cur) in
  let secant_line :=
    Garden.Halo2.Gadgets.Utilities.square lambda2_cur
      -E x_a_next
      -E x_r x_a x_p lambda_1 Rotation.cur
      -E x_a_cur in
  let gradient_2 :=
    lambda2_cur *E (x_a_cur -E x_a_next) -E y_a_cur -E y_a_next in
  [
    (Some "bool_check", bool_check);
    (Some "gradient_1", gradient_1);
    (Some "secant_line", secant_line);
    (Some "gradient_2", gradient_2)
  ].

Definition configure
    (meta : ConstraintSystem.t columns)
    (q_mul_1 q_mul_2 q_mul_3 : Selector.t)
    (z x_a x_p y_p lambda_1 lambda_2 : Advice.t)
    : ConstraintSystem.t columns :=
  let meta := ConstraintSystem.create_gate meta {|
    Gate.name := "q_mul_1 == 1 checks";
    Gate.constraints :=
      let y_a_next := y_a x_a x_p lambda_1 lambda_2 Rotation.next in
      let y_a_witnessed := Expression.Advice lambda_1 Rotation.cur in
      Constraints.with_selector q_mul_1 [
        (Some "init y_a", y_a_witnessed -E y_a_next)
      ];
  |} in
  let meta := ConstraintSystem.create_gate meta {|
    Gate.name := "q_mul_2 == 1 checks";
    Gate.constraints :=
      let y_a_next := y_a x_a x_p lambda_1 lambda_2 Rotation.next in
      let x_p_cur := Expression.Advice x_p Rotation.cur in
      let x_p_next := Expression.Advice x_p Rotation.next in
      let y_p_cur := Expression.Advice y_p Rotation.cur in
      let y_p_next := Expression.Advice y_p Rotation.next in
      let x_p_check := x_p_cur -E x_p_next in
      let y_p_check := y_p_cur -E y_p_next in
      Constraints.with_selector q_mul_2 (
        [
          (Some "x_p_check", x_p_check);
          (Some "y_p_check", y_p_check)
        ]
        ++ for_loop z x_a x_p y_p lambda_1 lambda_2 y_a_next);
  |} in
  let meta := ConstraintSystem.create_gate meta {|
    Gate.name := "q_mul_3 == 1 checks";
    Gate.constraints :=
      let y_a_final := Expression.Advice lambda_1 Rotation.next in
      Constraints.with_selector q_mul_3
        (for_loop z x_a x_p y_p lambda_1 lambda_2 y_a_final);
  |} in
  meta.
