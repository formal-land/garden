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
  Garden.Halo2.Gadgets.Utilities.square lambda_1 ➖ x_a ➖ x_p.

Definition y_a
    (x_a x_p lambda_1 lambda_2 : Advice.t)
    (rotation : Rotation.t)
    : Expression.t columns :=
  let x_a_expr := Expression.Advice x_a rotation in
  let lambda_1_expr := Expression.Advice lambda_1 rotation in
  let lambda_2_expr := Expression.Advice lambda_2 rotation in
  ((lambda_1_expr ➕ lambda_2_expr)
    ✖️ (x_a_expr ➖ x_r x_a x_p lambda_1 rotation))
    ● Garden.Halo2.Gadgets.Ecc.chip.constants.two_inv.

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
  let k := z_cur ➖ (z_prev ● 2) in
  let gradient_1 :=
    lambda1_cur ✖️ (x_a_cur ➖ x_p_cur)
      ➖ y_a_cur
      ➕ ((k ● 2 ➖ Expression.Constant 1) ✖️ y_p_cur) in
  let secant_line :=
    Garden.Halo2.Gadgets.Utilities.square lambda2_cur
      ➖ x_a_next
      ➖ x_r x_a x_p lambda_1 Rotation.cur
      ➖ x_a_cur in
  let gradient_2 :=
    lambda2_cur ✖️ (x_a_cur ➖ x_a_next) ➖ y_a_cur ➖ y_a_next in
  [
    (Some "bool_check", Constraint.Boolean k);
    (Some "gradient_1", Constraint.EqualZeroToPrecise gradient_1);
    (Some "secant_line", Constraint.EqualZeroToPrecise secant_line);
    (Some "gradient_2", Constraint.EqualZeroToPrecise gradient_2)
  ].

Definition q_mul_1_checks_gate
    (q_mul_1 : Selector.t)
    (x_a x_p lambda_1 lambda_2 : Advice.t)
    : Gate.t columns := {|
  Gate.name := "q_mul_1 == 1 checks";
  Gate.constraints :=
    let y_a_next := y_a x_a x_p lambda_1 lambda_2 Rotation.next in
    let y_a_witnessed := Expression.Advice lambda_1 Rotation.cur in
    Constraints.with_selector q_mul_1 [
      (Some "init y_a",
        Constraint.Equal y_a_witnessed y_a_next)
    ];
|}.

Definition q_mul_2_checks_gate
    (q_mul_2 : Selector.t)
    (z x_a x_p y_p lambda_1 lambda_2 : Advice.t)
    : Gate.t columns := {|
  Gate.name := "q_mul_2 == 1 checks";
  Gate.constraints :=
    let y_a_next := y_a x_a x_p lambda_1 lambda_2 Rotation.next in
    let x_p_cur := Expression.Advice x_p Rotation.cur in
    let x_p_next := Expression.Advice x_p Rotation.next in
    let y_p_cur := Expression.Advice y_p Rotation.cur in
    let y_p_next := Expression.Advice y_p Rotation.next in
    let x_p_check := x_p_cur ➖ x_p_next in
    let y_p_check := y_p_cur ➖ y_p_next in
    Constraints.with_selector q_mul_2 (
      [
        (Some "x_p_check", Constraint.Equal x_p_cur x_p_next);
        (Some "y_p_check", Constraint.Equal y_p_cur y_p_next)
      ]
      ++ for_loop z x_a x_p y_p lambda_1 lambda_2 y_a_next);
|}.

Definition q_mul_3_checks_gate
    (q_mul_3 : Selector.t)
    (z x_a x_p y_p lambda_1 lambda_2 : Advice.t)
    : Gate.t columns := {|
  Gate.name := "q_mul_3 == 1 checks";
  Gate.constraints :=
    let y_a_final := Expression.Advice lambda_1 Rotation.next in
    Constraints.with_selector q_mul_3
      (for_loop z x_a x_p y_p lambda_1 lambda_2 y_a_final);
|}.

Definition configure
    (q_mul_1 q_mul_2 q_mul_3 : Selector.t)
    (z x_a x_p y_p lambda_1 lambda_2 : Advice.t)
    : 𝓒 columns unit :=
  do🞵 𝓒.CreateGate (q_mul_1_checks_gate q_mul_1 x_a x_p lambda_1 lambda_2) in
  do🞵 𝓒.CreateGate (q_mul_2_checks_gate q_mul_2 z x_a x_p y_p lambda_1 lambda_2) in
  do🞵 𝓒.CreateGate (q_mul_3_checks_gate q_mul_3 z x_a x_p y_p lambda_1 lambda_2) in
  return🞵 tt.

Definition synthesize
    (q_mul_1 q_mul_2 q_mul_3 : Selector.t)
    : 𝓛 columns RegionId.t unit :=
  do🞵
    𝓛.AddRegion
      (RegionId.GadgetLocal RegionId.GadgetLocal.EccMulIncomplete1)
      "q_mul_1 == 1 checks" (fun _ =>
      𝓡.EnableSelector q_mul_1 0 "") in
  do🞵
    𝓛.AddRegion
      (RegionId.GadgetLocal RegionId.GadgetLocal.EccMulIncomplete2)
      "q_mul_2 == 1 checks" (fun _ =>
      𝓡.EnableSelector q_mul_2 0 "") in
  𝓛.AddRegion
    (RegionId.GadgetLocal RegionId.GadgetLocal.EccMulIncomplete3)
    "q_mul_3 == 1 checks" (fun _ =>
    𝓡.EnableSelector q_mul_3 0 "").
