Require Import Garden.Halo2.main.
Require Import Garden.Halo2.Gadgets.Ecc.chip.common.
Require Garden.Halo2.Gadgets.Utilities.

Import ListNotations.
Global Open Scope pstring_scope.
Global Open Scope Z_scope.

Definition configure
    (meta : ConstraintSystem.t columns)
    : ConstraintSystem.t columns :=
  let meta := ConstraintSystem.create_gate meta {|
    Gate.name := "complete addition";
    Gate.constraints :=
      let x_p := Expression.Advice Advice.A0 Rotation.cur in
      let y_p := Expression.Advice Advice.A1 Rotation.cur in
      let x_q := Expression.Advice Advice.A2 Rotation.cur in
      let y_q := Expression.Advice Advice.A3 Rotation.cur in
      let x_r := Expression.Advice Advice.A2 Rotation.next in
      let y_r := Expression.Advice Advice.A3 Rotation.next in
      let lambda := Expression.Advice Advice.A4 Rotation.cur in
      let alpha := Expression.Advice Advice.A5 Rotation.cur in
      let beta := Expression.Advice Advice.A6 Rotation.cur in
      let gamma := Expression.Advice Advice.A7 Rotation.cur in
      let delta := Expression.Advice Advice.A8 Rotation.cur in
      let x_q_minus_x_p := x_q -E x_p in
      let x_p_minus_x_r := x_p -E x_r in
      let y_q_plus_y_p := y_q +E y_p in
      let if_alpha := x_q_minus_x_p *E alpha in
      let if_beta := x_p *E beta in
      let if_gamma := x_q *E gamma in
      let if_delta := y_q_plus_y_p *E delta in
      let one := Expression.Constant 1 in
      let two := Expression.Constant 2 in
      let three := Expression.Constant 3 in
      let poly1 :=
        let y_q_minus_y_p := y_q -E y_p in
        let incomplete := x_q_minus_x_p *E lambda -E y_q_minus_y_p in
        x_q_minus_x_p *E incomplete in
      let poly2 :=
        let three_x_p_sq :=
          three *E Garden.Halo2.Gadgets.Utilities.square x_p in
        let two_y_p := two *E y_p in
        let tangent_line := two_y_p *E lambda -E three_x_p_sq in
        (one -E if_alpha) *E tangent_line in
      let nonexceptional_x_r :=
        Garden.Halo2.Gadgets.Utilities.square lambda -E x_p -E x_q -E x_r in
      let nonexceptional_y_r :=
        lambda *E x_p_minus_x_r -E y_p -E y_r in
      let poly3a :=
        x_p *E x_q *E x_q_minus_x_p *E nonexceptional_x_r in
      let poly3b :=
        x_p *E x_q *E x_q_minus_x_p *E nonexceptional_y_r in
      let poly3c :=
        x_p *E x_q *E y_q_plus_y_p *E nonexceptional_x_r in
      let poly3d :=
        x_p *E x_q *E y_q_plus_y_p *E nonexceptional_y_r in
      let poly4a := (one -E if_beta) *E (x_r -E x_q) in
      let poly4b := (one -E if_beta) *E (y_r -E y_q) in
      let poly5a := (one -E if_gamma) *E (x_r -E x_p) in
      let poly5b := (one -E if_gamma) *E (y_r -E y_p) in
      let poly6a := (one -E if_alpha -E if_delta) *E x_r in
      let poly6b := (one -E if_alpha -E if_delta) *E y_r in
      Constraints.with_selector Selector.QEccAdd [
        (Some "1", Constraint.EqualZeroToPrecise poly1);
        (Some "2", Constraint.EqualZeroToPrecise poly2);
        (Some "3a", Constraint.EqualZeroToPrecise poly3a);
        (Some "3b", Constraint.EqualZeroToPrecise poly3b);
        (Some "3c", Constraint.EqualZeroToPrecise poly3c);
        (Some "3d", Constraint.EqualZeroToPrecise poly3d);
        (Some "4a", Constraint.EqualZeroToPrecise poly4a);
        (Some "4b", Constraint.EqualZeroToPrecise poly4b);
        (Some "5a", Constraint.EqualZeroToPrecise poly5a);
        (Some "5b", Constraint.EqualZeroToPrecise poly5b);
        (Some "6a", Constraint.EqualZeroToPrecise poly6a);
        (Some "6b", Constraint.EqualZeroToPrecise poly6b)
      ];
  |} in
  meta.
