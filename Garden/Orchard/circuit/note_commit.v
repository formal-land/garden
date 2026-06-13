Require Import Garden.Halo2.main.
Require Import Garden.Halo2.Synthesis.
Require Import Garden.Orchard.columns.
Require Garden.Halo2.Gadgets.Utilities.
Require Garden.Halo2.Gadgets.Ecc.chip.constants.
Require Garden.Halo2.Gadgets.Sinsemilla.chip.
Require Garden.Orchard.FixedBases.NoteCommitR.

Import ListNotations.
Global Open Scope pstring_scope.
Global Open Scope Z_scope.

Definition note_commit_region
    (which : RegionId.NoteCommit.Which.t)
    (region : RegionId.NoteCommit.t) : RegionId.t :=
  RegionId.NoteCommit which region.

Definition note_commit_y_region
    (which : RegionId.NoteCommit.Which.t)
    (subject : RegionId.NoteCommit.YSubject.t)
    (region : RegionId.NoteCommit.YCanonicity.t) : RegionId.t :=
  note_commit_region which (RegionId.NoteCommit.YCanonicity subject region).

Module AssignedPoint.
  Record t : Set := {
    x : Cell.t columns RegionId.t;
    y : Cell.t columns RegionId.t;
  }.
End AssignedPoint.

Module FullFixedResult.
  Record t : Set := {
    acc : AssignedPoint.t;
    mul_b : AssignedPoint.t;
  }.
End FullFixedResult.

Module LookupResult.
  Record t : Set := {
    z_0 : Cell.t columns RegionId.t;
    z_1 : Cell.t columns RegionId.t;
    z_13 : Cell.t columns RegionId.t;
    z_end : Cell.t columns RegionId.t;
  }.
End LookupResult.

Definition fixed_base_row : Set :=
  list (Fixed.t * string * Z).

Fixpoint assign_fixed_row
    (offset : Z)
    (row : fixed_base_row)
    : 𝓡 columns RegionId.t unit :=
  match row with
  | [] => return🞵 tt
  | (column, annotation, value) :: row =>
      do🞵
        𝓡.AssignFixed annotation column offset value in
      assign_fixed_row offset row
  end.

Fixpoint assign_fixed_rows_with_selector
    (selector : Selector.t)
    (offset : Z)
    (rows : list fixed_base_row)
    : 𝓡 columns RegionId.t unit :=
  match rows with
  | [] => return🞵 tt
  | row :: rows =>
      do🞵 𝓡.EnableSelector selector offset "" in
      do🞵 assign_fixed_row offset row in
      assign_fixed_rows_with_selector selector (offset + 1) rows
  end.

Definition assign_mul_fixed_window
    (region : RegionId.t)
    (offset : Z)
    : 𝓡 columns RegionId.t AssignedPoint.t :=
  let x := Cell.advice region Advice.A0 offset in
  let y := Cell.advice region Advice.A1 offset in
  return🞵 {| AssignedPoint.x := x; AssignedPoint.y := y |}.

Definition assign_add_incomplete
    (region : RegionId.t)
    (offset : Z)
    (p q : AssignedPoint.t)
    : 𝓡 columns RegionId.t AssignedPoint.t :=
  do🞵 𝓡.EnableSelector Selector.QAddIncomplete offset "" in
  let x_p := Cell.advice region Advice.A0 offset in
  do🞵 𝓡.Copy x_p p.(AssignedPoint.x) in
  let y_p := Cell.advice region Advice.A1 offset in
  do🞵 𝓡.Copy y_p p.(AssignedPoint.y) in
  let x_q := Cell.advice region Advice.A2 offset in
  do🞵 𝓡.Copy x_q q.(AssignedPoint.x) in
  let y_q := Cell.advice region Advice.A3 offset in
  do🞵 𝓡.Copy y_q q.(AssignedPoint.y) in
  let x_r := Cell.advice region Advice.A2 (offset + 1) in
  let y_r := Cell.advice region Advice.A3 (offset + 1) in
  return🞵 {| AssignedPoint.x := x_r; AssignedPoint.y := y_r |}.

Fixpoint assign_incomplete_additions
    (region : RegionId.t)
    (offset : Z)
    (count : nat)
    (acc : AssignedPoint.t)
    : 𝓡 columns RegionId.t AssignedPoint.t :=
  match count with
  | O => return🞵 acc
  | S count =>
      let🞵 mul_b := assign_mul_fixed_window region offset in
      let🞵 acc := assign_add_incomplete region offset mul_b acc in
      assign_incomplete_additions region (offset + 1) count acc
  end.

Fixpoint assign_full_window_witnesses
    (offset : Z)
    (count : nat)
    : 𝓡 columns RegionId.t unit :=
  match count with
  | O => return🞵 tt
  | S count =>
      do🞵
        𝓡.EnableSelector Selector.QMulFixedFull offset "" in
      assign_full_window_witnesses (offset + 1) count
  end.

Definition assign_complete_add
    (region : RegionId.t)
    (p q : AssignedPoint.t)
    : 𝓡 columns RegionId.t AssignedPoint.t :=
  do🞵 𝓡.EnableSelector Selector.QEccAdd 0 "" in
  let x_p := Cell.advice region Advice.A0 0 in
  do🞵 𝓡.Copy x_p p.(AssignedPoint.x) in
  let y_p := Cell.advice region Advice.A1 0 in
  do🞵 𝓡.Copy y_p p.(AssignedPoint.y) in
  let x_q := Cell.advice region Advice.A2 0 in
  do🞵 𝓡.Copy x_q q.(AssignedPoint.x) in
  let y_q := Cell.advice region Advice.A3 0 in
  do🞵 𝓡.Copy y_q q.(AssignedPoint.y) in
  let x_r := Cell.advice region Advice.A2 1 in
  let y_r := Cell.advice region Advice.A3 1 in
  return🞵 {| AssignedPoint.x := x_r; AssignedPoint.y := y_r |}.

Definition synthesize_full_fixed_base_mul_note_commit_r_incomplete_region
    (region : RegionId.t)
    : 𝓛 columns RegionId.t FullFixedResult.t :=
  𝓛.AddRegion region "Full-width fixed-base mul (incomplete addition)" (fun region =>
    do🞵 assign_full_window_witnesses 0 85%nat in
    do🞵
      assign_fixed_rows_with_selector
        Selector.QMulFixedFull
        0
        Garden.Orchard.FixedBases.NoteCommitR.full_fixed_rows in
    let🞵 acc := assign_mul_fixed_window region 0 in
    let🞵 acc := assign_incomplete_additions region 1 83%nat acc in
    let🞵 mul_b := assign_mul_fixed_window region 84 in
    return🞵 {|
      FullFixedResult.acc := acc;
      FullFixedResult.mul_b := mul_b;
    |}).

Definition synthesize_full_fixed_base_mul_note_commit_r_last_region
    (region : RegionId.t)
    (result : FullFixedResult.t)
    : 𝓛 columns RegionId.t AssignedPoint.t :=
  𝓛.AddRegion region "Full-width fixed-base mul (last window, complete addition)" (fun region =>
    assign_complete_add
      region
      result.(FullFixedResult.mul_b)
      result.(FullFixedResult.acc)).

Definition synthesize_full_fixed_base_mul_note_commit_r
    (which : RegionId.NoteCommit.Which.t)
    : 𝓛 columns RegionId.t AssignedPoint.t :=
  let🞵 result :=
    synthesize_full_fixed_base_mul_note_commit_r_incomplete_region
      (note_commit_region which RegionId.NoteCommit.FixedBaseIncomplete) in
  synthesize_full_fixed_base_mul_note_commit_r_last_region
    (note_commit_region which RegionId.NoteCommit.FixedBaseLast)
    result.

Definition t_p_expr : Expression.t columns :=
  Expression.Constant Garden.Halo2.Gadgets.Ecc.chip.constants.t_p.

Definition q_note_commit_m_x : Z :=
  10629404576683096409262958701336170057000067777256141967953463442979689100381.

Definition q_note_commit_m_y : Z :=
  22898949290933268079297281211505753011910178734473470279111609228438645877859.

Definition message_piece_b_gate
    (q_b : Selector.t)
    : Gate.t columns := {|
  Gate.name := "NoteCommit MessagePiece b";
  Gate.constraints :=
    let b := Expression.Advice Advice.A6 Rotation.cur in
    let b_0 := Expression.Advice Advice.A7 Rotation.cur in
    let b_1 := Expression.Advice Advice.A8 Rotation.cur in
    let b_2 := Expression.Advice Advice.A7 Rotation.next in
    let b_3 := Expression.Advice Advice.A8 Rotation.next in
    let decomposition_check :=
      b ➖ (b_0 ➕ (b_1 ● (2 ^ 4)) ➕ (b_2 ● (2 ^ 5))
        ➕ (b_3 ● (2 ^ 6))) in
    Constraints.with_selector q_b [
      (Some "bool_check b_1", Constraint.Boolean b_1);
      (Some "bool_check b_2", Constraint.Boolean b_2);
      (Some "decomposition",
        Constraint.Equal
          b
          (b_0 ➕ (b_1 ● (2 ^ 4)) ➕ (b_2 ● (2 ^ 5))
            ➕ (b_3 ● (2 ^ 6))))
    ];
|}.

Definition message_piece_d_gate
    (q_d : Selector.t)
    : Gate.t columns := {|
  Gate.name := "NoteCommit MessagePiece d";
  Gate.constraints :=
    let d := Expression.Advice Advice.A6 Rotation.cur in
    let d_0 := Expression.Advice Advice.A7 Rotation.cur in
    let d_1 := Expression.Advice Advice.A8 Rotation.cur in
    let d_2 := Expression.Advice Advice.A7 Rotation.next in
    let d_3 := Expression.Advice Advice.A8 Rotation.next in
    let decomposition_check :=
      d ➖ (d_0 ➕ (d_1 ● 2) ➕ (d_2 ● (2 ^ 2))
        ➕ (d_3 ● (2 ^ 10))) in
    Constraints.with_selector q_d [
      (Some "bool_check d_0", Constraint.Boolean d_0);
      (Some "bool_check d_1", Constraint.Boolean d_1);
      (Some "decomposition",
        Constraint.Equal
          d
          (d_0 ➕ (d_1 ● 2) ➕ (d_2 ● (2 ^ 2))
            ➕ (d_3 ● (2 ^ 10))))
    ];
|}.

Definition message_piece_e_gate
    (q_e : Selector.t)
    : Gate.t columns := {|
  Gate.name := "NoteCommit MessagePiece e";
  Gate.constraints :=
    let e := Expression.Advice Advice.A6 Rotation.cur in
    let e_0 := Expression.Advice Advice.A7 Rotation.cur in
    let e_1 := Expression.Advice Advice.A8 Rotation.cur in
    let decomposition_check := e ➖ (e_0 ➕ (e_1 ● (2 ^ 6))) in
    Constraints.with_selector q_e [
      (Some "decomposition", Constraint.Equal e (e_0 ➕ (e_1 ● (2 ^ 6))))
    ];
|}.

Definition message_piece_g_gate
    (q_g : Selector.t)
    : Gate.t columns := {|
  Gate.name := "NoteCommit MessagePiece g";
  Gate.constraints :=
    let g := Expression.Advice Advice.A6 Rotation.cur in
    let g_0 := Expression.Advice Advice.A7 Rotation.cur in
    let g_1 := Expression.Advice Advice.A6 Rotation.next in
    let g_2 := Expression.Advice Advice.A7 Rotation.next in
    let decomposition_check :=
      g ➖ (g_0 ➕ (g_1 ● 2) ➕ (g_2 ● (2 ^ 10))) in
    Constraints.with_selector q_g [
      (Some "bool_check g_0", Constraint.Boolean g_0);
      (Some "decomposition",
        Constraint.Equal g (g_0 ➕ (g_1 ● 2) ➕ (g_2 ● (2 ^ 10))))
    ];
|}.

Definition message_piece_h_gate
    (q_h : Selector.t)
    : Gate.t columns := {|
  Gate.name := "NoteCommit MessagePiece h";
  Gate.constraints :=
    let h := Expression.Advice Advice.A6 Rotation.cur in
    let h_0 := Expression.Advice Advice.A7 Rotation.cur in
    let h_1 := Expression.Advice Advice.A8 Rotation.cur in
    let decomposition_check := h ➖ (h_0 ➕ (h_1 ● (2 ^ 5))) in
    Constraints.with_selector q_h [
      (Some "bool_check h_1", Constraint.Boolean h_1);
      (Some "decomposition", Constraint.Equal h (h_0 ➕ (h_1 ● (2 ^ 5))))
    ];
|}.

Definition input_g_d_gate
    (q_gd : Selector.t)
    : Gate.t columns := {|
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
      a ➕ (b_0 ● (2 ^ 250)) ➕ (b_1 ● (2 ^ 254)) ➖ gd_x in
    let a_prime_check :=
      a ➕ Expression.Constant (2 ^ 130) ➖ t_p_expr ➖ a_prime in
    Constraints.with_selector q_gd [
      (Some "decomposition",
        Constraint.Equal
          (a ➕ (b_0 ● (2 ^ 250)) ➕ (b_1 ● (2 ^ 254)))
          gd_x);
      (Some "a_prime_check",
        Constraint.Equal
          (a ➕ Expression.Constant (2 ^ 130) ➖ t_p_expr)
          a_prime);
      (Some "b_1 = 1 => b_0",
        Constraint.Either
          (Constraint.EqualZeroToPrecise b_1)
          (Constraint.EqualZeroToPrecise b_0));
      (Some "b_1 = 1 => z13_a",
        Constraint.Either
          (Constraint.EqualZeroToPrecise b_1)
          (Constraint.EqualZeroToPrecise z13_a));
      (Some "b_1 = 1 => z13_a_prime",
        Constraint.Either
          (Constraint.EqualZeroToPrecise b_1)
          (Constraint.EqualZeroToPrecise z13_a_prime))
    ];
|}.

Definition input_pk_d_gate
    (q_pkd : Selector.t)
    : Gate.t columns := {|
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
      b_3 ➕ (c ● (2 ^ 4)) ➕ (d_0 ● (2 ^ 254)) ➖ pkd_x in
    let b3_c_prime_check :=
      b_3 ➕ (c ● (2 ^ 4)) ➕ Expression.Constant (2 ^ 140)
        ➖ t_p_expr ➖ b3_c_prime in
    Constraints.with_selector q_pkd [
      (Some "decomposition",
        Constraint.Equal
          (b_3 ➕ (c ● (2 ^ 4)) ➕ (d_0 ● (2 ^ 254)))
          pkd_x);
      (Some "b3_c_prime_check",
        Constraint.Equal
          (b_3 ➕ (c ● (2 ^ 4)) ➕ Expression.Constant (2 ^ 140)
            ➖ t_p_expr)
          b3_c_prime);
      (Some "d_0 = 1 => z13_c",
        Constraint.Either
          (Constraint.EqualZeroToPrecise d_0)
          (Constraint.EqualZeroToPrecise z13_c));
      (Some "d_0 = 1 => z14_b3_c_prime",
        Constraint.Either
          (Constraint.EqualZeroToPrecise d_0)
          (Constraint.EqualZeroToPrecise z14_b3_c_prime))
    ];
|}.

Definition input_value_gate
    (q_value : Selector.t)
    : Gate.t columns := {|
  Gate.name := "NoteCommit input value";
  Gate.constraints :=
    let value := Expression.Advice Advice.A6 Rotation.cur in
    let d_2 := Expression.Advice Advice.A7 Rotation.cur in
    let z1_d := Expression.Advice Advice.A8 Rotation.cur in
    let e_0 := Expression.Advice Advice.A9 Rotation.cur in
    let value_check :=
      d_2 ➕ (z1_d ● (2 ^ 8)) ➕ (e_0 ● (2 ^ 58)) ➖ value in
    Constraints.with_selector q_value [
      (Some "value_check",
        Constraint.Equal (d_2 ➕ (z1_d ● (2 ^ 8)) ➕ (e_0 ● (2 ^ 58))) value)
    ];
|}.

Definition input_rho_gate
    (q_rho : Selector.t)
    : Gate.t columns := {|
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
      e_1 ➕ (f ● (2 ^ 4)) ➕ (g_0 ● (2 ^ 254)) ➖ rho in
    let e1_f_prime_check :=
      e_1 ➕ (f ● (2 ^ 4)) ➕ Expression.Constant (2 ^ 140)
        ➖ t_p_expr ➖ e1_f_prime in
    Constraints.with_selector q_rho [
      (Some "decomposition",
        Constraint.Equal
          (e_1 ➕ (f ● (2 ^ 4)) ➕ (g_0 ● (2 ^ 254)))
          rho);
      (Some "e1_f_prime_check",
        Constraint.Equal
          (e_1 ➕ (f ● (2 ^ 4)) ➕ Expression.Constant (2 ^ 140)
            ➖ t_p_expr)
          e1_f_prime);
      (Some "g_0 = 1 => z13_f",
        Constraint.Either
          (Constraint.EqualZeroToPrecise g_0)
          (Constraint.EqualZeroToPrecise z13_f));
      (Some "g_0 = 1 => z14_e1_f_prime",
        Constraint.Either
          (Constraint.EqualZeroToPrecise g_0)
          (Constraint.EqualZeroToPrecise z14_e1_f_prime))
    ];
|}.

Definition input_psi_gate
    (q_psi : Selector.t)
    : Gate.t columns := {|
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
      g_1 ➕ (g_2 ● (2 ^ 9)) ➕ (h_0 ● (2 ^ 249))
        ➕ (h_1 ● (2 ^ 254)) ➖ psi in
    let g1_g2_prime_check :=
      g_1 ➕ (g_2 ● (2 ^ 9)) ➕ Expression.Constant (2 ^ 130)
        ➖ t_p_expr ➖ g1_g2_prime in
    Constraints.with_selector q_psi [
      (Some "decomposition",
        Constraint.Equal
          (g_1 ➕ (g_2 ● (2 ^ 9)) ➕ (h_0 ● (2 ^ 249))
            ➕ (h_1 ● (2 ^ 254)))
          psi);
      (Some "g1_g2_prime_check",
        Constraint.Equal
          (g_1 ➕ (g_2 ● (2 ^ 9)) ➕ Expression.Constant (2 ^ 130)
            ➖ t_p_expr)
          g1_g2_prime);
      (Some "h_1 = 1 => h_0",
        Constraint.Either
          (Constraint.EqualZeroToPrecise h_1)
          (Constraint.EqualZeroToPrecise h_0));
      (Some "h_1 = 1 => z13_g",
        Constraint.Either
          (Constraint.EqualZeroToPrecise h_1)
          (Constraint.EqualZeroToPrecise z13_g));
      (Some "h_1 = 1 => z13_g1_g2_prime",
        Constraint.Either
          (Constraint.EqualZeroToPrecise h_1)
          (Constraint.EqualZeroToPrecise z13_g1_g2_prime))
    ];
|}.

Definition y_coordinate_checks_gate
    (q_y_canon : Selector.t)
    : Gate.t columns := {|
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
    let j_check := j ➖ (lsb ➕ (k_0 ● 2) ➕ (z1_j ● (2 ^ 10))) in
    let y_check :=
      y ➖ (j ➕ (k_2 ● (2 ^ 250)) ➕ (k_3 ● (2 ^ 254))) in
    let j_prime_check :=
      j ➕ Expression.Constant (2 ^ 130) ➖ t_p_expr ➖ j_prime in
    Constraints.with_selector q_y_canon [
      (Some "k3_check", Constraint.Boolean k_3);
      (Some "j_check",
        Constraint.Equal j (lsb ➕ (k_0 ● 2) ➕ (z1_j ● (2 ^ 10))));
      (Some "y_check",
        Constraint.Equal y (j ➕ (k_2 ● (2 ^ 250)) ➕ (k_3 ● (2 ^ 254))));
      (Some "j_prime_check",
        Constraint.Equal (j ➕ Expression.Constant (2 ^ 130) ➖ t_p_expr) j_prime);
      (Some "k_3 = 1 => k_2 = 0",
        Constraint.Either
          (Constraint.EqualZeroToPrecise k_3)
          (Constraint.EqualZeroToPrecise k_2));
      (Some "k_3 = 1 => z13_j = 0",
        Constraint.Either
          (Constraint.EqualZeroToPrecise k_3)
          (Constraint.EqualZeroToPrecise z13_j));
      (Some "k_3 = 1 => z13_j_prime = 0",
        Constraint.Either
          (Constraint.EqualZeroToPrecise k_3)
          (Constraint.EqualZeroToPrecise z13_j_prime))
    ];
|}.

Definition configure_instance_program
    (q_b q_d q_e q_g q_h
      q_gd q_pkd q_value q_rho q_psi q_y_canon : Selector.t)
    : 𝓒 columns unit :=
  do🞵 𝓒.CreateGate (message_piece_b_gate q_b) in
  do🞵 𝓒.CreateGate (message_piece_d_gate q_d) in
  do🞵 𝓒.CreateGate (message_piece_e_gate q_e) in
  do🞵 𝓒.CreateGate (message_piece_g_gate q_g) in
  do🞵 𝓒.CreateGate (message_piece_h_gate q_h) in
  do🞵 𝓒.CreateGate (input_g_d_gate q_gd) in
  do🞵 𝓒.CreateGate (input_pk_d_gate q_pkd) in
  do🞵 𝓒.CreateGate (input_value_gate q_value) in
  do🞵 𝓒.CreateGate (input_rho_gate q_rho) in
  do🞵 𝓒.CreateGate (input_psi_gate q_psi) in
  do🞵 𝓒.CreateGate (y_coordinate_checks_gate q_y_canon) in
  return🞵 tt.

Definition configure_instance
    (meta : ConstraintSystem.t columns)
    (q_b q_d q_e q_g q_h
      q_gd q_pkd q_value q_rho q_psi q_y_canon : Selector.t)
    : ConstraintSystem.t columns :=
  𝓒.run_unit
    (configure_instance_program
      q_b
      q_d
      q_e
      q_g
      q_h
      q_gd
      q_pkd
      q_value
      q_rho
      q_psi
      q_y_canon)
    meta.

Definition configure_old_program : 𝓒 columns unit :=
  configure_instance_program
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

Definition configure_old
    (meta : ConstraintSystem.t columns)
    : ConstraintSystem.t columns :=
  𝓒.run_unit configure_old_program meta.

Definition configure_new_program : 𝓒 columns unit :=
  configure_instance_program
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

Definition configure_new
    (meta : ConstraintSystem.t columns)
    : ConstraintSystem.t columns :=
  𝓒.run_unit configure_new_program meta.

Definition witness_message_piece
    (region : RegionId.t)
    (column : Advice.t)
    (name : string)
    : 𝓛 columns RegionId.t (Cell.t columns RegionId.t) :=
  𝓛.InNamespace name (
    𝓛.AddRegion region "witness message piece" (fun region =>
      return🞵 (Cell.advice region column 0))).

Definition synthesize_short_range
    (region : RegionId.t)
    (namespace region_name : string)
    : 𝓛 columns RegionId.t (Cell.t columns RegionId.t) :=
  𝓛.InNamespace namespace (
    𝓛.AddRegion region region_name (fun region =>
      let element := Cell.advice region Advice.A9 0 in
      do🞵 𝓡.EnableSelector Selector.QLookup 0 "" in
      do🞵 𝓡.EnableSelector Selector.QLookup 1 "" in
      do🞵 𝓡.EnableSelector Selector.QBitshift 1 "" in
      return🞵 element)).

Fixpoint enable_lookup_running_rows
    (offset : Z)
    (count : nat)
    : 𝓡 columns RegionId.t unit :=
  match count with
  | O => return🞵 tt
  | S count =>
      do🞵 𝓡.EnableSelector Selector.QLookup offset "" in
      do🞵 𝓡.EnableSelector Selector.QRunning offset "" in
      enable_lookup_running_rows (offset + 1) count
  end.

Definition synthesize_running_lookup
    (region : RegionId.t)
    (namespace : string)
    (count : nat)
    : 𝓛 columns RegionId.t LookupResult.t :=
  𝓛.InNamespace namespace (
    𝓛.AddRegion region "Witness element" (fun region =>
      let z_0 := Cell.advice region Advice.A9 0 in
      let z_1 := Cell.advice region Advice.A9 1 in
      let z_13 := Cell.advice region Advice.A9 13 in
      do🞵 enable_lookup_running_rows 0 count in
      let z_end := Cell.advice region Advice.A9 (Z.of_nat count) in
      return🞵 {|
        LookupResult.z_0 := z_0;
        LookupResult.z_1 := z_1;
        LookupResult.z_13 := z_13;
        LookupResult.z_end := z_end;
      |})).

Definition synthesize_y_canonicity
    (which : RegionId.NoteCommit.Which.t)
    (subject : RegionId.NoteCommit.YSubject.t)
    (namespace : string)
    (q_y_canon : Selector.t)
    (y : Cell.t columns RegionId.t)
    : 𝓛 columns RegionId.t (Cell.t columns RegionId.t) :=
  𝓛.InNamespace namespace (
    let🞵 k_0 :=
      synthesize_short_range
        (note_commit_y_region
          which
          subject
          RegionId.NoteCommit.YCanonicity.RangeK0)
        "k_0"
        "Range check 9 bits" in
    let🞵 k_2 :=
      synthesize_short_range
        (note_commit_y_region
          which
          subject
          RegionId.NoteCommit.YCanonicity.RangeK2)
        "k_2"
        "Range check 4 bits" in
    let🞵 j_lookup :=
      synthesize_running_lookup
        (note_commit_y_region
          which
          subject
          RegionId.NoteCommit.YCanonicity.JLookup)
        "Decompose j = LSB + (2)k_0 + (2^10)k_1"
        25%nat in
    let🞵 j_prime_lookup :=
      𝓛.InNamespace "j_prime = j + 2^130 - t_P" (
        synthesize_running_lookup
          (note_commit_y_region
            which
            subject
            RegionId.NoteCommit.YCanonicity.JPrimeLookup)
          "Decompose low 130 bits of (a + 2^130 - t_P)"
          13%nat) in
    𝓛.AddRegion
      (note_commit_y_region which subject RegionId.NoteCommit.YCanonicity.Gate)
      "y canonicity" (fun region =>
      do🞵 𝓡.EnableSelector q_y_canon 0 "" in
      let y_bit := Cell.advice region Advice.A6 0 in
      let y_target := Cell.advice region Advice.A5 0 in
      do🞵 𝓡.Copy y_target y in
      let k_0_target := Cell.advice region Advice.A7 0 in
      do🞵 𝓡.Copy k_0_target k_0 in
      let k_2_target := Cell.advice region Advice.A8 0 in
      do🞵 𝓡.Copy k_2_target k_2 in
      let j_0_target := Cell.advice region Advice.A5 1 in
      do🞵 𝓡.Copy j_0_target j_lookup.(LookupResult.z_0) in
      let j_1_target := Cell.advice region Advice.A6 1 in
      do🞵 𝓡.Copy j_1_target j_lookup.(LookupResult.z_1) in
      let j_13_target := Cell.advice region Advice.A7 1 in
      do🞵 𝓡.Copy j_13_target j_lookup.(LookupResult.z_13) in
      let j_prime_0_target := Cell.advice region Advice.A8 1 in
      do🞵
        𝓡.Copy j_prime_0_target j_prime_lookup.(LookupResult.z_0) in
      let j_prime_13_target := Cell.advice region Advice.A9 1 in
      do🞵
        𝓡.Copy j_prime_13_target j_prime_lookup.(LookupResult.z_end) in
      return🞵 y_bit)).

Definition synthesize_instance
    (which : RegionId.NoteCommit.Which.t)
    (q_b q_d q_e q_g q_h
      q_gd q_pkd q_value q_rho q_psi q_y_canon : Selector.t)
    (use_second_sinsemilla : bool)
    (g_d_x g_d_y pk_d_x pk_d_y value rho psi : Cell.t columns RegionId.t)
    : 𝓛 columns RegionId.t AssignedPoint.t :=
  let piece_column :=
    if use_second_sinsemilla then Advice.A7 else Advice.A6 in
  let bits_column :=
    if use_second_sinsemilla then Advice.A7 else Advice.A2 in
  let rho_column :=
    if use_second_sinsemilla then Advice.A2 else Advice.A0 in
  let🞵 a :=
    witness_message_piece
      (note_commit_region which RegionId.NoteCommit.WitnessA)
      piece_column
      "a" in
  let🞵 b_0 :=
    synthesize_short_range
      (note_commit_region which RegionId.NoteCommit.RangeB0)
      "b_0"
      "Range check 4 bits" in
  let🞵 b_3 :=
    synthesize_short_range
      (note_commit_region which RegionId.NoteCommit.RangeB3)
      "b_3"
      "Range check 4 bits" in
  let🞵 b :=
    witness_message_piece
      (note_commit_region which RegionId.NoteCommit.WitnessB)
      piece_column
      "b" in
  let🞵 c :=
    witness_message_piece
      (note_commit_region which RegionId.NoteCommit.WitnessC)
      piece_column
      "c" in
  let🞵 d_2 :=
    synthesize_short_range
      (note_commit_region which RegionId.NoteCommit.RangeD2)
      "d_2"
      "Range check 8 bits" in
  let🞵 d :=
    witness_message_piece
      (note_commit_region which RegionId.NoteCommit.WitnessD)
      piece_column
      "d" in
  let🞵 e_0 :=
    synthesize_short_range
      (note_commit_region which RegionId.NoteCommit.RangeE0)
      "e_0"
      "Range check 6 bits" in
  let🞵 e_1 :=
    synthesize_short_range
      (note_commit_region which RegionId.NoteCommit.RangeE1)
      "e_1"
      "Range check 4 bits" in
  let🞵 e :=
    witness_message_piece
      (note_commit_region which RegionId.NoteCommit.WitnessE)
      piece_column
      "e" in
  let🞵 f :=
    witness_message_piece
      (note_commit_region which RegionId.NoteCommit.WitnessF)
      piece_column
      "f" in
  let🞵 g_1 :=
    synthesize_short_range
      (note_commit_region which RegionId.NoteCommit.RangeG1)
      "g_1"
      "Range check 9 bits" in
  let🞵 g :=
    witness_message_piece
      (note_commit_region which RegionId.NoteCommit.WitnessG)
      piece_column
      "g" in
  let🞵 h_0 :=
    synthesize_short_range
      (note_commit_region which RegionId.NoteCommit.RangeH0)
      "h_0"
      "Range check 5 bits" in
  let🞵 h :=
    witness_message_piece
      (note_commit_region which RegionId.NoteCommit.WitnessH)
      piece_column
      "h" in
  let🞵 b_2 :=
    synthesize_y_canonicity
      which
      RegionId.NoteCommit.YSubject.GD
      "y(g_d) decomposition"
      q_y_canon
      g_d_y in
  let🞵 d_1 :=
    synthesize_y_canonicity
      which
      RegionId.NoteCommit.YSubject.PkD
      "y(pk_d) decomposition"
      q_y_canon
      pk_d_y in
  let🞵 '(cm, hash) :=
    𝓛.InNamespace "Process NoteCommit inputs" (
      let🞵 blind :=
        𝓛.InNamespace "[r] R" (
          𝓛.InNamespace "fixed-base mul of NoteCommitR" (
            synthesize_full_fixed_base_mul_note_commit_r which)) in
      let🞵 m_hash :=
        𝓛.InNamespace "M" (
          (if use_second_sinsemilla
           then Garden.Halo2.Gadgets.Sinsemilla.chip.synthesize_hash_to_point_note_commit_2
           else Garden.Halo2.Gadgets.Sinsemilla.chip.synthesize_hash_to_point_note_commit)
            (note_commit_region which RegionId.NoteCommit.HashToPoint)
            q_note_commit_m_x
            q_note_commit_m_y
            a
            b
            c
            d
            e
            f
            g
            h) in
      let m := {|
        AssignedPoint.x :=
          m_hash.(Garden.Halo2.Gadgets.Sinsemilla.chip.HashResult.x);
        AssignedPoint.y :=
          m_hash.(Garden.Halo2.Gadgets.Sinsemilla.chip.HashResult.y);
      |} in
      let🞵 cm :=
        𝓛.InNamespace "M + [r] R" (
          𝓛.AddRegion
            (note_commit_region which RegionId.NoteCommit.CompletePointAdd)
            "complete point addition" (fun region =>
            assign_complete_add region m blind)) in
      return🞵 (cm, m_hash)) in
  let🞵 x_gd_lookup :=
    𝓛.InNamespace "x(g_d) canonicity" (
      synthesize_running_lookup
        (note_commit_region which RegionId.NoteCommit.XGDLookup)
        "Decompose low 130 bits of (a + 2^130 - t_P)"
        13%nat) in
  let🞵 x_pkd_lookup :=
    𝓛.InNamespace "x(pk_d) canonicity" (
      synthesize_running_lookup
        (note_commit_region which RegionId.NoteCommit.XPKDLookup)
        "Decompose low 140 bits of (b_3 + 2^4 c + 2^140 - t_P)"
        14%nat) in
  let🞵 rho_lookup :=
    𝓛.InNamespace "rho canonicity" (
      synthesize_running_lookup
        (note_commit_region which RegionId.NoteCommit.RhoLookup)
        "Decompose low 140 bits of (e_1 + 2^4 f + 2^140 - t_P)"
        14%nat) in
  let🞵 psi_lookup :=
    𝓛.InNamespace "psi canonicity" (
      synthesize_running_lookup
        (note_commit_region which RegionId.NoteCommit.PsiLookup)
        "Decompose low 130 bits of (g_1 + (2^9)g_2 + 2^130 - t_P)"
        13%nat) in
  let🞵 b_1 :=
    𝓛.AddRegion
      (note_commit_region which RegionId.NoteCommit.MessagePieceB)
      "NoteCommit MessagePiece b" (fun region =>
      do🞵 𝓡.EnableSelector q_b 0 "" in
      let b_target := Cell.advice region Advice.A6 0 in
      do🞵 𝓡.Copy b_target b in
      let b_0_target := Cell.advice region Advice.A7 0 in
      do🞵 𝓡.Copy b_0_target b_0 in
      let b_1 := Cell.advice region Advice.A8 0 in
      let b_2_target := Cell.advice region Advice.A7 1 in
      do🞵 𝓡.Copy b_2_target b_2 in
      let b_3_target := Cell.advice region Advice.A8 1 in
      do🞵 𝓡.Copy b_3_target b_3 in
      return🞵 b_1) in
  let🞵 d_0 :=
    𝓛.AddRegion
      (note_commit_region which RegionId.NoteCommit.MessagePieceD)
      "NoteCommit MessagePiece d" (fun region =>
      do🞵 𝓡.EnableSelector q_d 0 "" in
      let d_target := Cell.advice region Advice.A6 0 in
      do🞵 𝓡.Copy d_target d in
      let d_0 := Cell.advice region Advice.A7 0 in
      let d_1_target := Cell.advice region Advice.A8 0 in
      do🞵 𝓡.Copy d_1_target d_1 in
      let d_2_target := Cell.advice region Advice.A7 1 in
      do🞵 𝓡.Copy d_2_target d_2 in
      let d_3_target := Cell.advice region Advice.A8 1 in
      do🞵
        𝓡.Copy
          d_3_target
          hash.(Garden.Halo2.Gadgets.Sinsemilla.chip.HashResult.z1_d) in
      return🞵 d_0) in
  do🞵
    𝓛.AddRegion
      (note_commit_region which RegionId.NoteCommit.MessagePieceE)
      "NoteCommit MessagePiece e" (fun region =>
      do🞵 𝓡.EnableSelector q_e 0 "" in
      let e_target := Cell.advice region Advice.A6 0 in
      do🞵 𝓡.Copy e_target e in
      let e_0_target := Cell.advice region Advice.A7 0 in
      do🞵 𝓡.Copy e_0_target e_0 in
      let e_1_target := Cell.advice region Advice.A8 0 in
      do🞵 𝓡.Copy e_1_target e_1 in
      return🞵 tt) in
  let🞵 g_0 :=
    𝓛.AddRegion
      (note_commit_region which RegionId.NoteCommit.MessagePieceG)
      "NoteCommit MessagePiece g" (fun region =>
      do🞵 𝓡.EnableSelector q_g 0 "" in
      let g_target := Cell.advice region Advice.A6 0 in
      do🞵 𝓡.Copy g_target g in
      let g_0 := Cell.advice region Advice.A7 0 in
      let g_1_target := Cell.advice region Advice.A6 1 in
      do🞵 𝓡.Copy g_1_target g_1 in
      let g_2_target := Cell.advice region Advice.A7 1 in
      do🞵
        𝓡.Copy
          g_2_target
          hash.(Garden.Halo2.Gadgets.Sinsemilla.chip.HashResult.z1_g) in
      return🞵 g_0) in
  let🞵 h_1 :=
    𝓛.AddRegion
      (note_commit_region which RegionId.NoteCommit.MessagePieceH)
      "NoteCommit MessagePiece h" (fun region =>
      do🞵 𝓡.EnableSelector q_h 0 "" in
      let h_target := Cell.advice region Advice.A6 0 in
      do🞵 𝓡.Copy h_target h in
      let h_0_target := Cell.advice region Advice.A7 0 in
      do🞵 𝓡.Copy h_0_target h_0 in
      let h_1 := Cell.advice region Advice.A8 0 in
      return🞵 h_1) in
  do🞵
    𝓛.AddRegion
      (note_commit_region which RegionId.NoteCommit.InputGD)
      "NoteCommit input g_d" (fun region =>
      let gd_x_target := Cell.advice region Advice.A6 0 in
      do🞵 𝓡.Copy gd_x_target g_d_x in
      let b_0_target := Cell.advice region Advice.A7 0 in
      do🞵 𝓡.Copy b_0_target b_0 in
      let b_1_target := Cell.advice region Advice.A7 1 in
      do🞵 𝓡.Copy b_1_target b_1 in
      let a_target := Cell.advice region Advice.A8 0 in
      do🞵 𝓡.Copy a_target a in
      let a_prime_target := Cell.advice region Advice.A8 1 in
      do🞵
        𝓡.Copy a_prime_target x_gd_lookup.(LookupResult.z_0) in
      let z13_a_target := Cell.advice region Advice.A9 0 in
      do🞵
        𝓡.Copy
          z13_a_target
          hash.(Garden.Halo2.Gadgets.Sinsemilla.chip.HashResult.z13_a) in
      let z13_a_prime_target := Cell.advice region Advice.A9 1 in
      do🞵
        𝓡.Copy z13_a_prime_target x_gd_lookup.(LookupResult.z_end) in
      𝓡.EnableSelector q_gd 0 "") in
  do🞵
    𝓛.AddRegion
      (note_commit_region which RegionId.NoteCommit.InputPkD)
      "NoteCommit input pk_d" (fun region =>
      let pkd_x_target := Cell.advice region Advice.A6 0 in
      do🞵 𝓡.Copy pkd_x_target pk_d_x in
      let b_3_target := Cell.advice region Advice.A7 0 in
      do🞵 𝓡.Copy b_3_target b_3 in
      let d_0_target := Cell.advice region Advice.A7 1 in
      do🞵 𝓡.Copy d_0_target d_0 in
      let c_target := Cell.advice region Advice.A8 0 in
      do🞵 𝓡.Copy c_target c in
      let b3_c_prime_target := Cell.advice region Advice.A8 1 in
      do🞵
        𝓡.Copy b3_c_prime_target x_pkd_lookup.(LookupResult.z_0) in
      let z13_c_target := Cell.advice region Advice.A9 0 in
      do🞵
        𝓡.Copy
          z13_c_target
          hash.(Garden.Halo2.Gadgets.Sinsemilla.chip.HashResult.z13_c) in
      let z14_b3_c_prime_target := Cell.advice region Advice.A9 1 in
      do🞵
        𝓡.Copy z14_b3_c_prime_target x_pkd_lookup.(LookupResult.z_end) in
      𝓡.EnableSelector q_pkd 0 "") in
  do🞵
    𝓛.AddRegion
      (note_commit_region which RegionId.NoteCommit.InputValue)
      "NoteCommit input value" (fun region =>
      let value_target := Cell.advice region Advice.A6 0 in
      do🞵 𝓡.Copy value_target value in
      let d_2_target := Cell.advice region Advice.A7 0 in
      do🞵 𝓡.Copy d_2_target d_2 in
      let d3_target := Cell.advice region Advice.A8 0 in
      do🞵
        𝓡.Copy
          d3_target
          hash.(Garden.Halo2.Gadgets.Sinsemilla.chip.HashResult.z1_d) in
      let e_0_target := Cell.advice region Advice.A9 0 in
      do🞵 𝓡.Copy e_0_target e_0 in
      𝓡.EnableSelector q_value 0 "") in
  do🞵
    𝓛.AddRegion
      (note_commit_region which RegionId.NoteCommit.InputRho)
      "NoteCommit input rho" (fun region =>
      let rho_target := Cell.advice region Advice.A6 0 in
      do🞵 𝓡.Copy rho_target rho in
      let e_1_target := Cell.advice region Advice.A7 0 in
      do🞵 𝓡.Copy e_1_target e_1 in
      let g_0_target := Cell.advice region Advice.A7 1 in
      do🞵 𝓡.Copy g_0_target g_0 in
      let f_target := Cell.advice region Advice.A8 0 in
      do🞵 𝓡.Copy f_target f in
      let e1_f_prime_target := Cell.advice region Advice.A8 1 in
      do🞵
        𝓡.Copy e1_f_prime_target rho_lookup.(LookupResult.z_0) in
      let z13_f_target := Cell.advice region Advice.A9 0 in
      do🞵
        𝓡.Copy
          z13_f_target
          hash.(Garden.Halo2.Gadgets.Sinsemilla.chip.HashResult.z13_f) in
      let z14_e1_f_prime_target := Cell.advice region Advice.A9 1 in
      do🞵
        𝓡.Copy z14_e1_f_prime_target rho_lookup.(LookupResult.z_end) in
      𝓡.EnableSelector q_rho 0 "") in
  do🞵
    𝓛.AddRegion
      (note_commit_region which RegionId.NoteCommit.InputPsi)
      "NoteCommit input psi" (fun region =>
      let psi_target := Cell.advice region Advice.A6 0 in
      do🞵 𝓡.Copy psi_target psi in
      let h_0_target := Cell.advice region Advice.A6 1 in
      do🞵 𝓡.Copy h_0_target h_0 in
      let g_1_target := Cell.advice region Advice.A7 0 in
      do🞵 𝓡.Copy g_1_target g_1 in
      let h_1_target := Cell.advice region Advice.A7 1 in
      do🞵 𝓡.Copy h_1_target h_1 in
      let g_2_target := Cell.advice region Advice.A8 0 in
      do🞵
        𝓡.Copy
          g_2_target
          hash.(Garden.Halo2.Gadgets.Sinsemilla.chip.HashResult.z1_g) in
      let g1_g2_prime_target := Cell.advice region Advice.A8 1 in
      do🞵
        𝓡.Copy g1_g2_prime_target psi_lookup.(LookupResult.z_0) in
      let z13_g_target := Cell.advice region Advice.A9 0 in
      do🞵
        𝓡.Copy
          z13_g_target
          hash.(Garden.Halo2.Gadgets.Sinsemilla.chip.HashResult.z13_g) in
      let z13_g1_g2_prime_target := Cell.advice region Advice.A9 1 in
      do🞵
        𝓡.Copy z13_g1_g2_prime_target psi_lookup.(LookupResult.z_end) in
      𝓡.EnableSelector q_psi 0 "") in
  return🞵 cm.

Definition synthesize_old
    (g_d_x g_d_y pk_d_x pk_d_y value rho psi : Cell.t columns RegionId.t)
    : 𝓛 columns RegionId.t AssignedPoint.t :=
  synthesize_instance
    RegionId.NoteCommit.Which.Old
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
    Selector.QNoteCommitOldYCanon
    false
    g_d_x
    g_d_y
    pk_d_x
    pk_d_y
    value
    rho
    psi.

Definition synthesize_new
    (g_d_x g_d_y pk_d_x pk_d_y value rho psi : Cell.t columns RegionId.t)
    : 𝓛 columns RegionId.t AssignedPoint.t :=
  synthesize_instance
    RegionId.NoteCommit.Which.New
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
    Selector.QNoteCommitNewYCanon
    true
    g_d_x
    g_d_y
    pk_d_x
    pk_d_y
    value
    rho
    psi.
