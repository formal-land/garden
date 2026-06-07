Require Import Garden.Halo2.main.
Require Import Garden.Orchard.columns.
Require Garden.Halo2.Gadgets.Utilities.
Require Garden.Halo2.Gadgets.Ecc.chip.constants.

Import ListNotations.
Global Open Scope pstring_scope.
Global Open Scope Z_scope.

Definition t_p_expr : Expression.t columns :=
  Expression.Constant Garden.Halo2.Gadgets.Ecc.chip.constants.t_p.

Definition configure_instance
    (meta : ConstraintSystem.t columns)
    (q_b q_d q_e q_g q_h
      q_gd q_pkd q_value q_rho q_psi q_y_canon : Selector.t)
    : ConstraintSystem.t columns :=
  let meta := ConstraintSystem.create_gate meta {|
    Gate.name := "NoteCommit MessagePiece b";
    Gate.constraints :=
      let b := Expression.Advice Advice.A6 Rotation.cur in
      let b_0 := Expression.Advice Advice.A7 Rotation.cur in
      let b_1 := Expression.Advice Advice.A8 Rotation.cur in
      let b_2 := Expression.Advice Advice.A7 Rotation.next in
      let b_3 := Expression.Advice Advice.A8 Rotation.next in
      let decomposition_check :=
        b -E (b_0 +E (b_1 *Z (2 ^ 4)) +E (b_2 *Z (2 ^ 5))
          +E (b_3 *Z (2 ^ 6))) in
      Constraints.with_selector q_b [
        (Some "bool_check b_1",
          Constraint.EqualZeroToPrecise
            (Garden.Halo2.Gadgets.Utilities.bool_check b_1));
        (Some "bool_check b_2",
          Constraint.EqualZeroToPrecise
            (Garden.Halo2.Gadgets.Utilities.bool_check b_2));
        (Some "decomposition", Constraint.EqualZeroToPrecise decomposition_check)
      ];
  |} in
  let meta := ConstraintSystem.create_gate meta {|
    Gate.name := "NoteCommit MessagePiece d";
    Gate.constraints :=
      let d := Expression.Advice Advice.A6 Rotation.cur in
      let d_0 := Expression.Advice Advice.A7 Rotation.cur in
      let d_1 := Expression.Advice Advice.A8 Rotation.cur in
      let d_2 := Expression.Advice Advice.A7 Rotation.next in
      let d_3 := Expression.Advice Advice.A8 Rotation.next in
      let decomposition_check :=
        d -E (d_0 +E (d_1 *Z 2) +E (d_2 *Z (2 ^ 2))
          +E (d_3 *Z (2 ^ 10))) in
      Constraints.with_selector q_d [
        (Some "bool_check d_0",
          Constraint.EqualZeroToPrecise
            (Garden.Halo2.Gadgets.Utilities.bool_check d_0));
        (Some "bool_check d_1",
          Constraint.EqualZeroToPrecise
            (Garden.Halo2.Gadgets.Utilities.bool_check d_1));
        (Some "decomposition", Constraint.EqualZeroToPrecise decomposition_check)
      ];
  |} in
  let meta := ConstraintSystem.create_gate meta {|
    Gate.name := "NoteCommit MessagePiece e";
    Gate.constraints :=
      let e := Expression.Advice Advice.A6 Rotation.cur in
      let e_0 := Expression.Advice Advice.A7 Rotation.cur in
      let e_1 := Expression.Advice Advice.A8 Rotation.cur in
      let decomposition_check := e -E (e_0 +E (e_1 *Z (2 ^ 6))) in
      Constraints.with_selector q_e [
        (Some "decomposition", Constraint.EqualZeroToPrecise decomposition_check)
      ];
  |} in
  let meta := ConstraintSystem.create_gate meta {|
    Gate.name := "NoteCommit MessagePiece g";
    Gate.constraints :=
      let g := Expression.Advice Advice.A6 Rotation.cur in
      let g_0 := Expression.Advice Advice.A7 Rotation.cur in
      let g_1 := Expression.Advice Advice.A6 Rotation.next in
      let g_2 := Expression.Advice Advice.A7 Rotation.next in
      let decomposition_check :=
        g -E (g_0 +E (g_1 *Z 2) +E (g_2 *Z (2 ^ 10))) in
      Constraints.with_selector q_g [
        (Some "bool_check g_0",
          Constraint.EqualZeroToPrecise
            (Garden.Halo2.Gadgets.Utilities.bool_check g_0));
        (Some "decomposition", Constraint.EqualZeroToPrecise decomposition_check)
      ];
  |} in
  let meta := ConstraintSystem.create_gate meta {|
    Gate.name := "NoteCommit MessagePiece h";
    Gate.constraints :=
      let h := Expression.Advice Advice.A6 Rotation.cur in
      let h_0 := Expression.Advice Advice.A7 Rotation.cur in
      let h_1 := Expression.Advice Advice.A8 Rotation.cur in
      let decomposition_check := h -E (h_0 +E (h_1 *Z (2 ^ 5))) in
      Constraints.with_selector q_h [
        (Some "bool_check h_1",
          Constraint.EqualZeroToPrecise
            (Garden.Halo2.Gadgets.Utilities.bool_check h_1));
        (Some "decomposition", Constraint.EqualZeroToPrecise decomposition_check)
      ];
  |} in
  let meta := ConstraintSystem.create_gate meta {|
    Gate.name := "NoteCommit input g_d";
    Gate.constraints :=
      let gd_x := Expression.Advice Advice.A6 Rotation.cur in
      let b_0 := Expression.Advice Advice.A7 Rotation.cur in
      let b_1 := Expression.Advice Advice.A7 Rotation.next in
      let a := Expression.Advice Advice.A8 Rotation.cur in
      let a_prime := Expression.Advice Advice.A8 Rotation.next in
      let z13_a := Expression.Advice Advice.A9 Rotation.cur in
      let z13_a_prime := Expression.Advice Advice.A9 Rotation.next in
      let decomposition_check :=
        a +E (b_0 *Z (2 ^ 250)) +E (b_1 *Z (2 ^ 254)) -E gd_x in
      let a_prime_check :=
        a +E Expression.Constant (2 ^ 130) -E t_p_expr -E a_prime in
      Constraints.with_selector q_gd [
        (Some "decomposition", Constraint.EqualZeroToPrecise decomposition_check);
        (Some "a_prime_check", Constraint.EqualZeroToPrecise a_prime_check);
        (Some "b_1 = 1 => b_0",
          Constraint.EqualZeroToPrecise (b_1 *E b_0));
        (Some "b_1 = 1 => z13_a",
          Constraint.EqualZeroToPrecise (b_1 *E z13_a));
        (Some "b_1 = 1 => z13_a_prime",
          Constraint.EqualZeroToPrecise (b_1 *E z13_a_prime))
      ];
  |} in
  let meta := ConstraintSystem.create_gate meta {|
    Gate.name := "NoteCommit input pk_d";
    Gate.constraints :=
      let pkd_x := Expression.Advice Advice.A6 Rotation.cur in
      let b_3 := Expression.Advice Advice.A7 Rotation.cur in
      let d_0 := Expression.Advice Advice.A7 Rotation.next in
      let c := Expression.Advice Advice.A8 Rotation.cur in
      let b3_c_prime := Expression.Advice Advice.A8 Rotation.next in
      let z13_c := Expression.Advice Advice.A9 Rotation.cur in
      let z14_b3_c_prime := Expression.Advice Advice.A9 Rotation.next in
      let decomposition_check :=
        b_3 +E (c *Z (2 ^ 4)) +E (d_0 *Z (2 ^ 254)) -E pkd_x in
      let b3_c_prime_check :=
        b_3 +E (c *Z (2 ^ 4)) +E Expression.Constant (2 ^ 140)
          -E t_p_expr -E b3_c_prime in
      Constraints.with_selector q_pkd [
        (Some "decomposition", Constraint.EqualZeroToPrecise decomposition_check);
        (Some "b3_c_prime_check",
          Constraint.EqualZeroToPrecise b3_c_prime_check);
        (Some "d_0 = 1 => z13_c",
          Constraint.EqualZeroToPrecise (d_0 *E z13_c));
        (Some "d_0 = 1 => z14_b3_c_prime",
          Constraint.EqualZeroToPrecise (d_0 *E z14_b3_c_prime))
      ];
  |} in
  let meta := ConstraintSystem.create_gate meta {|
    Gate.name := "NoteCommit input value";
    Gate.constraints :=
      let value := Expression.Advice Advice.A6 Rotation.cur in
      let d_2 := Expression.Advice Advice.A7 Rotation.cur in
      let z1_d := Expression.Advice Advice.A8 Rotation.cur in
      let e_0 := Expression.Advice Advice.A9 Rotation.cur in
      let value_check :=
        d_2 +E (z1_d *Z (2 ^ 8)) +E (e_0 *Z (2 ^ 58)) -E value in
      Constraints.with_selector q_value [
        (Some "value_check", Constraint.EqualZeroToPrecise value_check)
      ];
  |} in
  let meta := ConstraintSystem.create_gate meta {|
    Gate.name := "NoteCommit input rho";
    Gate.constraints :=
      let rho := Expression.Advice Advice.A6 Rotation.cur in
      let e_1 := Expression.Advice Advice.A7 Rotation.cur in
      let g_0 := Expression.Advice Advice.A7 Rotation.next in
      let f := Expression.Advice Advice.A8 Rotation.cur in
      let e1_f_prime := Expression.Advice Advice.A8 Rotation.next in
      let z13_f := Expression.Advice Advice.A9 Rotation.cur in
      let z14_e1_f_prime := Expression.Advice Advice.A9 Rotation.next in
      let decomposition_check :=
        e_1 +E (f *Z (2 ^ 4)) +E (g_0 *Z (2 ^ 254)) -E rho in
      let e1_f_prime_check :=
        e_1 +E (f *Z (2 ^ 4)) +E Expression.Constant (2 ^ 140)
          -E t_p_expr -E e1_f_prime in
      Constraints.with_selector q_rho [
        (Some "decomposition", Constraint.EqualZeroToPrecise decomposition_check);
        (Some "e1_f_prime_check",
          Constraint.EqualZeroToPrecise e1_f_prime_check);
        (Some "g_0 = 1 => z13_f",
          Constraint.EqualZeroToPrecise (g_0 *E z13_f));
        (Some "g_0 = 1 => z14_e1_f_prime",
          Constraint.EqualZeroToPrecise (g_0 *E z14_e1_f_prime))
      ];
  |} in
  let meta := ConstraintSystem.create_gate meta {|
    Gate.name := "NoteCommit input psi";
    Gate.constraints :=
      let psi := Expression.Advice Advice.A6 Rotation.cur in
      let h_0 := Expression.Advice Advice.A6 Rotation.next in
      let g_1 := Expression.Advice Advice.A7 Rotation.cur in
      let h_1 := Expression.Advice Advice.A7 Rotation.next in
      let z1_g := Expression.Advice Advice.A8 Rotation.cur in
      let g_2 := z1_g in
      let g1_g2_prime := Expression.Advice Advice.A8 Rotation.next in
      let z13_g := Expression.Advice Advice.A9 Rotation.cur in
      let z13_g1_g2_prime := Expression.Advice Advice.A9 Rotation.next in
      let decomposition_check :=
        g_1 +E (g_2 *Z (2 ^ 9)) +E (h_0 *Z (2 ^ 249))
          +E (h_1 *Z (2 ^ 254)) -E psi in
      let g1_g2_prime_check :=
        g_1 +E (g_2 *Z (2 ^ 9)) +E Expression.Constant (2 ^ 130)
          -E t_p_expr -E g1_g2_prime in
      Constraints.with_selector q_psi [
        (Some "decomposition", Constraint.EqualZeroToPrecise decomposition_check);
        (Some "g1_g2_prime_check",
          Constraint.EqualZeroToPrecise g1_g2_prime_check);
        (Some "h_1 = 1 => h_0",
          Constraint.EqualZeroToPrecise (h_1 *E h_0));
        (Some "h_1 = 1 => z13_g",
          Constraint.EqualZeroToPrecise (h_1 *E z13_g));
        (Some "h_1 = 1 => z13_g1_g2_prime",
          Constraint.EqualZeroToPrecise (h_1 *E z13_g1_g2_prime))
      ];
  |} in
  let meta := ConstraintSystem.create_gate meta {|
    Gate.name := "y coordinate checks";
    Gate.constraints :=
      let y := Expression.Advice Advice.A5 Rotation.cur in
      let lsb := Expression.Advice Advice.A6 Rotation.cur in
      let k_0 := Expression.Advice Advice.A7 Rotation.cur in
      let k_2 := Expression.Advice Advice.A8 Rotation.cur in
      let k_3 := Expression.Advice Advice.A9 Rotation.cur in
      let j := Expression.Advice Advice.A5 Rotation.next in
      let z1_j := Expression.Advice Advice.A6 Rotation.next in
      let z13_j := Expression.Advice Advice.A7 Rotation.next in
      let j_prime := Expression.Advice Advice.A8 Rotation.next in
      let z13_j_prime := Expression.Advice Advice.A9 Rotation.next in
      let k3_check := Garden.Halo2.Gadgets.Utilities.bool_check k_3 in
      let j_check := j -E (lsb +E (k_0 *Z 2) +E (z1_j *Z (2 ^ 10))) in
      let y_check :=
        y -E (j +E (k_2 *Z (2 ^ 250)) +E (k_3 *Z (2 ^ 254))) in
      let j_prime_check :=
        j +E Expression.Constant (2 ^ 130) -E t_p_expr -E j_prime in
      Constraints.with_selector q_y_canon [
        (Some "k3_check", Constraint.EqualZeroToPrecise k3_check);
        (Some "j_check", Constraint.EqualZeroToPrecise j_check);
        (Some "y_check", Constraint.EqualZeroToPrecise y_check);
        (Some "j_prime_check", Constraint.EqualZeroToPrecise j_prime_check);
        (Some "k_3 = 1 => k_2 = 0",
          Constraint.EqualZeroToPrecise (k_3 *E k_2));
        (Some "k_3 = 1 => z13_j = 0",
          Constraint.EqualZeroToPrecise (k_3 *E z13_j));
        (Some "k_3 = 1 => z13_j_prime = 0",
          Constraint.EqualZeroToPrecise (k_3 *E z13_j_prime))
      ];
  |} in
  meta.

Definition configure_old
    (meta : ConstraintSystem.t columns)
    : ConstraintSystem.t columns :=
  configure_instance
    meta
    Selector.QNoteCommitOldB
    Selector.QNoteCommitOldD
    Selector.QNoteCommitOldE
    Selector.QNoteCommitOldG
    Selector.QNoteCommitOldH
    Selector.QNoteCommitOldGd
    Selector.QNoteCommitOldPkd
    Selector.QNoteCommitOldValue
    Selector.QNoteCommitOldRho
    Selector.QNoteCommitOldPsi
    Selector.QNoteCommitOldYCanon.

Definition configure_new
    (meta : ConstraintSystem.t columns)
    : ConstraintSystem.t columns :=
  configure_instance
    meta
    Selector.QNoteCommitNewB
    Selector.QNoteCommitNewD
    Selector.QNoteCommitNewE
    Selector.QNoteCommitNewG
    Selector.QNoteCommitNewH
    Selector.QNoteCommitNewGd
    Selector.QNoteCommitNewPkd
    Selector.QNoteCommitNewValue
    Selector.QNoteCommitNewRho
    Selector.QNoteCommitNewPsi
    Selector.QNoteCommitNewYCanon.
