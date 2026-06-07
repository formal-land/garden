Require Import Garden.Halo2.main.
Require Import Garden.Orchard.columns.
Require Garden.Halo2.Gadgets.Utilities.
Require Garden.Halo2.Gadgets.Ecc.chip.constants.

Import ListNotations.
Global Open Scope pstring_scope.
Global Open Scope Z_scope.

Definition sinsemilla_k : Z := 10.

Definition sinsemilla_s0_x : Z := 0.

Definition sinsemilla_s0_y : Z := 0.

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
  (lambda_1_expr +E lambda_2_expr)
    *E (x_a_expr -E x_r x_a x_p lambda_1 rotation).

Definition q_s3
    (q_sinsemilla2 : Fixed.t)
    : Expression.t columns :=
  let q_s2 := Expression.Fixed q_sinsemilla2 Rotation.cur in
  q_s2 *E (q_s2 -E Expression.Constant 1).

Definition configure_generator_table
    (meta : ConstraintSystem.t columns)
    (q_sinsemilla1 : Selector.t)
    (q_sinsemilla2 : Fixed.t)
    (x_a x_p bits lambda_1 lambda_2 : Advice.t)
    : ConstraintSystem.t columns :=
  let meta := ConstraintSystem.create_lookup meta {|
    LookupArgument.pairs :=
      let q_s1 := Expression.Selector q_sinsemilla1 in
      let q_s2 := Expression.Fixed q_sinsemilla2 Rotation.cur in
      let q_s3 := q_s3 q_sinsemilla2 in
      let q_run := q_s2 -E q_s3 in
      let z_cur := Expression.Advice bits Rotation.cur in
      let z_next := Expression.Advice bits Rotation.next in
      let word := z_cur -E (q_run *E z_next *Z (2 ^ sinsemilla_k)) in
      let x_p_expr := Expression.Advice x_p Rotation.cur in
      let lambda1 := Expression.Advice lambda_1 Rotation.cur in
      let x_a_expr := Expression.Advice x_a Rotation.cur in
      let y_p :=
        (y_a x_a x_p lambda_1 lambda_2 Rotation.cur
          *Z Garden.Halo2.Gadgets.Ecc.chip.constants.two_inv)
          -E (lambda1 *E (x_a_expr -E x_p_expr)) in
      let not_q_s1 := Expression.Constant 1 -E q_s1 in
      [
        (q_s1 *E word, Fixed.Lookup Lookup.TableIdx);
        (q_s1 *E x_p_expr +E not_q_s1 *E Expression.Constant sinsemilla_s0_x,
          Fixed.Lookup Lookup.TableX);
        (q_s1 *E y_p +E not_q_s1 *E Expression.Constant sinsemilla_s0_y,
          Fixed.Lookup Lookup.TableY)
      ];
  |} in
  meta.

Definition configure_instance
    (meta : ConstraintSystem.t columns)
    (q_sinsemilla1 q_sinsemilla4 : Selector.t)
    (q_sinsemilla2 fixed_y_q : Fixed.t)
    (x_a x_p bits lambda_1 lambda_2 : Advice.t)
    : ConstraintSystem.t columns :=
  let meta :=
    configure_generator_table
      meta
      q_sinsemilla1
      q_sinsemilla2
      x_a
      x_p
      bits
      lambda_1
      lambda_2 in
  let meta := ConstraintSystem.create_gate meta {|
    Gate.name := "Initial y_Q";
    Gate.constraints :=
      let y_q := Expression.Fixed fixed_y_q Rotation.cur in
      let y_a_cur := y_a x_a x_p lambda_1 lambda_2 Rotation.cur in
      Constraints.with_selector q_sinsemilla4 [
        (Some "init_y_q_check",
          Constraint.EqualZeroToPrecise (y_q *Z 2 -E y_a_cur))
      ];
  |} in
  let meta := ConstraintSystem.create_gate meta {|
    Gate.name := "Sinsemilla gate";
    Gate.constraints :=
      let q_s3 := q_s3 q_sinsemilla2 in
      let lambda_1_next := Expression.Advice lambda_1 Rotation.next in
      let lambda_2_cur := Expression.Advice lambda_2 Rotation.cur in
      let x_a_cur := Expression.Advice x_a Rotation.cur in
      let x_a_next := Expression.Advice x_a Rotation.next in
      let x_r_cur := x_r x_a x_p lambda_1 Rotation.cur in
      let y_a_cur := y_a x_a x_p lambda_1 lambda_2 Rotation.cur in
      let y_a_next := y_a x_a x_p lambda_1 lambda_2 Rotation.next in
      let secant_line :=
        Garden.Halo2.Gadgets.Utilities.square lambda_2_cur
          -E (x_a_next +E x_r_cur +E x_a_cur) in
      let lhs := lambda_2_cur *Z 4 *E (x_a_cur -E x_a_next) in
      let rhs :=
        (y_a_cur *Z 2)
          +E ((Expression.Constant 2 -E q_s3) *E y_a_next)
          +E (q_s3 *E Expression.Constant 2 *E lambda_1_next) in
      let y_check := lhs -E rhs in
      Constraints.with_selector q_sinsemilla1 [
        (Some "Secant line", Constraint.EqualZeroToPrecise secant_line);
        (Some "y check", Constraint.EqualZeroToPrecise y_check)
      ];
  |} in
  meta.

Definition configure_1
    (meta : ConstraintSystem.t columns)
    : ConstraintSystem.t columns :=
  configure_instance
    meta
    Selector.QSinsemilla1_1
    Selector.QSinsemilla4_1
    Fixed.QSinsemilla2_1
    Fixed.LagrangeCoeffs0
    Advice.A0
    Advice.A1
    Advice.A2
    Advice.A3
    Advice.A4.

Definition configure_2
    (meta : ConstraintSystem.t columns)
    : ConstraintSystem.t columns :=
  configure_instance
    meta
    Selector.QSinsemilla1_2
    Selector.QSinsemilla4_2
    Fixed.QSinsemilla2_2
    Fixed.LagrangeCoeffs1
    Advice.A5
    Advice.A6
    Advice.A7
    Advice.A8
    Advice.A9.
