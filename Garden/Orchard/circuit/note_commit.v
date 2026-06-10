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
      let🞵 _ :=
        ℛ.AssignFixed annotation column offset value in
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
      let🞵 _ := ℛ.EnableSelector selector offset "" in
      let🞵 _ := assign_fixed_row offset row in
      assign_fixed_rows_with_selector selector (offset + 1) rows
  end.

Definition assign_mul_fixed_window
    (offset : Z)
    : 𝓡 columns RegionId.t AssignedPoint.t :=
  let🞵 x :=
    ℛ.AssignAdvice "mul_b_x" Advice.A0 offset 0 in
  let🞵 y :=
    ℛ.AssignAdvice "mul_b_y" Advice.A1 offset 0 in
  let🞵 _ :=
    ℛ.AssignAdvice "u" Advice.A5 offset 0 in
  return🞵 {| AssignedPoint.x := x; AssignedPoint.y := y |}.

Definition assign_add_incomplete
    (offset : Z)
    (p q : AssignedPoint.t)
    : 𝓡 columns RegionId.t AssignedPoint.t :=
  let🞵 _ := ℛ.EnableSelector Selector.QAddIncomplete offset "" in
  let🞵 _ :=
    copy_advice "x_p" p.(AssignedPoint.x) Advice.A0 offset 0 in
  let🞵 _ :=
    copy_advice "y_p" p.(AssignedPoint.y) Advice.A1 offset 0 in
  let🞵 _ :=
    copy_advice "x_q" q.(AssignedPoint.x) Advice.A2 offset 0 in
  let🞵 _ :=
    copy_advice "y_q" q.(AssignedPoint.y) Advice.A3 offset 0 in
  let🞵 x_r :=
    ℛ.AssignAdvice "x_r" Advice.A2 (offset + 1) 0 in
  let🞵 y_r :=
    ℛ.AssignAdvice "y_r" Advice.A3 (offset + 1) 0 in
  return🞵 {| AssignedPoint.x := x_r; AssignedPoint.y := y_r |}.

Fixpoint assign_incomplete_additions
    (offset : Z)
    (count : nat)
    (acc : AssignedPoint.t)
    : 𝓡 columns RegionId.t AssignedPoint.t :=
  match count with
  | O => return🞵 acc
  | S count =>
      let🞵 mul_b := assign_mul_fixed_window offset in
      let🞵 acc := assign_add_incomplete offset mul_b acc in
      assign_incomplete_additions (offset + 1) count acc
  end.

Fixpoint assign_full_window_witnesses
    (offset : Z)
    (count : nat)
    : 𝓡 columns RegionId.t unit :=
  match count with
  | O => return🞵 tt
  | S count =>
      let🞵 _ :=
        ℛ.EnableSelector Selector.QMulFixedFull offset "" in
      let🞵 _ := ℛ.AssignAdvice "k" Advice.A4 offset 0 in
      assign_full_window_witnesses (offset + 1) count
  end.

Definition assign_complete_add
    (p q : AssignedPoint.t)
    : 𝓡 columns RegionId.t AssignedPoint.t :=
  let🞵 _ := ℛ.EnableSelector Selector.QEccAdd 0 "" in
  let🞵 _ :=
    copy_advice "x_p" p.(AssignedPoint.x) Advice.A0 0 0 in
  let🞵 _ :=
    copy_advice "y_p" p.(AssignedPoint.y) Advice.A1 0 0 in
  let🞵 _ :=
    copy_advice "x_q" q.(AssignedPoint.x) Advice.A2 0 0 in
  let🞵 _ :=
    copy_advice "y_q" q.(AssignedPoint.y) Advice.A3 0 0 in
  let🞵 _ := ℛ.AssignAdvice "alpha" Advice.A5 0 0 in
  let🞵 _ := ℛ.AssignAdvice "beta" Advice.A6 0 0 in
  let🞵 _ := ℛ.AssignAdvice "gamma" Advice.A7 0 0 in
  let🞵 _ := ℛ.AssignAdvice "delta" Advice.A8 0 0 in
  let🞵 _ := ℛ.AssignAdvice "lambda" Advice.A4 0 0 in
  let🞵 x_r := ℛ.AssignAdvice "x_r" Advice.A2 1 0 in
  let🞵 y_r := ℛ.AssignAdvice "y_r" Advice.A3 1 0 in
  return🞵 {| AssignedPoint.x := x_r; AssignedPoint.y := y_r |}.

Definition synthesize_full_fixed_base_mul_note_commit_r_incomplete_region
    (region : RegionId.t)
    : 𝓛 columns RegionId.t FullFixedResult.t :=
  ℒ.AddRegion region "Full-width fixed-base mul (incomplete addition)" (
    let🞵 _ := assign_full_window_witnesses 0 85%nat in
    let🞵 _ :=
      assign_fixed_rows_with_selector
        Selector.QMulFixedFull
        0
        Garden.Orchard.FixedBases.NoteCommitR.full_fixed_rows in
    let🞵 acc := assign_mul_fixed_window 0 in
    let🞵 acc := assign_incomplete_additions 1 83%nat acc in
    let🞵 mul_b := assign_mul_fixed_window 84 in
    return🞵 {|
      FullFixedResult.acc := acc;
      FullFixedResult.mul_b := mul_b;
    |}).

Definition synthesize_full_fixed_base_mul_note_commit_r_last_region
    (region : RegionId.t)
    (result : FullFixedResult.t)
    : 𝓛 columns RegionId.t AssignedPoint.t :=
  ℒ.AddRegion region "Full-width fixed-base mul (last window, complete addition)" (
    assign_complete_add
      result.(FullFixedResult.mul_b)
      result.(FullFixedResult.acc)).

Definition synthesize_full_fixed_base_mul_note_commit_r
    (first_region_index : Z)
    : 𝓛 columns RegionId.t AssignedPoint.t :=
  let🞵 result :=
    synthesize_full_fixed_base_mul_note_commit_r_incomplete_region
      (RegionId.of_index first_region_index) in
  synthesize_full_fixed_base_mul_note_commit_r_last_region
    (RegionId.of_index (first_region_index + 1))
    result.

Definition t_p_expr : Expression.t columns :=
  Expression.Constant Garden.Halo2.Gadgets.Ecc.chip.constants.t_p.

Definition q_note_commit_m_x : Z :=
  10629404576683096409262958701336170057000067777256141967953463442979689100381.

Definition q_note_commit_m_y : Z :=
  22898949290933268079297281211505753011910178734473470279111609228438645877859.

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
        b ➖ (b_0 ➕ (b_1 ● (2 ^ 4)) ➕ (b_2 ● (2 ^ 5))
          ➕ (b_3 ● (2 ^ 6))) in
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
        d ➖ (d_0 ➕ (d_1 ● 2) ➕ (d_2 ● (2 ^ 2))
          ➕ (d_3 ● (2 ^ 10))) in
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
      let decomposition_check := e ➖ (e_0 ➕ (e_1 ● (2 ^ 6))) in
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
        g ➖ (g_0 ➕ (g_1 ● 2) ➕ (g_2 ● (2 ^ 10))) in
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
      let decomposition_check := h ➖ (h_0 ➕ (h_1 ● (2 ^ 5))) in
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
        a ➕ (b_0 ● (2 ^ 250)) ➕ (b_1 ● (2 ^ 254)) ➖ gd_x in
      let a_prime_check :=
        a ➕ Expression.Constant (2 ^ 130) ➖ t_p_expr ➖ a_prime in
      Constraints.with_selector q_gd [
        (Some "decomposition", Constraint.EqualZeroToPrecise decomposition_check);
        (Some "a_prime_check", Constraint.EqualZeroToPrecise a_prime_check);
        (Some "b_1 = 1 => b_0",
          Constraint.EqualZeroToPrecise (b_1 ✖️ b_0));
        (Some "b_1 = 1 => z13_a",
          Constraint.EqualZeroToPrecise (b_1 ✖️ z13_a));
        (Some "b_1 = 1 => z13_a_prime",
          Constraint.EqualZeroToPrecise (b_1 ✖️ z13_a_prime))
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
        b_3 ➕ (c ● (2 ^ 4)) ➕ (d_0 ● (2 ^ 254)) ➖ pkd_x in
      let b3_c_prime_check :=
        b_3 ➕ (c ● (2 ^ 4)) ➕ Expression.Constant (2 ^ 140)
          ➖ t_p_expr ➖ b3_c_prime in
      Constraints.with_selector q_pkd [
        (Some "decomposition", Constraint.EqualZeroToPrecise decomposition_check);
        (Some "b3_c_prime_check",
          Constraint.EqualZeroToPrecise b3_c_prime_check);
        (Some "d_0 = 1 => z13_c",
          Constraint.EqualZeroToPrecise (d_0 ✖️ z13_c));
        (Some "d_0 = 1 => z14_b3_c_prime",
          Constraint.EqualZeroToPrecise (d_0 ✖️ z14_b3_c_prime))
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
        d_2 ➕ (z1_d ● (2 ^ 8)) ➕ (e_0 ● (2 ^ 58)) ➖ value in
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
        e_1 ➕ (f ● (2 ^ 4)) ➕ (g_0 ● (2 ^ 254)) ➖ rho in
      let e1_f_prime_check :=
        e_1 ➕ (f ● (2 ^ 4)) ➕ Expression.Constant (2 ^ 140)
          ➖ t_p_expr ➖ e1_f_prime in
      Constraints.with_selector q_rho [
        (Some "decomposition", Constraint.EqualZeroToPrecise decomposition_check);
        (Some "e1_f_prime_check",
          Constraint.EqualZeroToPrecise e1_f_prime_check);
        (Some "g_0 = 1 => z13_f",
          Constraint.EqualZeroToPrecise (g_0 ✖️ z13_f));
        (Some "g_0 = 1 => z14_e1_f_prime",
          Constraint.EqualZeroToPrecise (g_0 ✖️ z14_e1_f_prime))
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
        g_1 ➕ (g_2 ● (2 ^ 9)) ➕ (h_0 ● (2 ^ 249))
          ➕ (h_1 ● (2 ^ 254)) ➖ psi in
      let g1_g2_prime_check :=
        g_1 ➕ (g_2 ● (2 ^ 9)) ➕ Expression.Constant (2 ^ 130)
          ➖ t_p_expr ➖ g1_g2_prime in
      Constraints.with_selector q_psi [
        (Some "decomposition", Constraint.EqualZeroToPrecise decomposition_check);
        (Some "g1_g2_prime_check",
          Constraint.EqualZeroToPrecise g1_g2_prime_check);
        (Some "h_1 = 1 => h_0",
          Constraint.EqualZeroToPrecise (h_1 ✖️ h_0));
        (Some "h_1 = 1 => z13_g",
          Constraint.EqualZeroToPrecise (h_1 ✖️ z13_g));
        (Some "h_1 = 1 => z13_g1_g2_prime",
          Constraint.EqualZeroToPrecise (h_1 ✖️ z13_g1_g2_prime))
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
      let j_check := j ➖ (lsb ➕ (k_0 ● 2) ➕ (z1_j ● (2 ^ 10))) in
      let y_check :=
        y ➖ (j ➕ (k_2 ● (2 ^ 250)) ➕ (k_3 ● (2 ^ 254))) in
      let j_prime_check :=
        j ➕ Expression.Constant (2 ^ 130) ➖ t_p_expr ➖ j_prime in
      Constraints.with_selector q_y_canon [
        (Some "k3_check", Constraint.EqualZeroToPrecise k3_check);
        (Some "j_check", Constraint.EqualZeroToPrecise j_check);
        (Some "y_check", Constraint.EqualZeroToPrecise y_check);
        (Some "j_prime_check", Constraint.EqualZeroToPrecise j_prime_check);
        (Some "k_3 = 1 => k_2 = 0",
          Constraint.EqualZeroToPrecise (k_3 ✖️ k_2));
        (Some "k_3 = 1 => z13_j = 0",
          Constraint.EqualZeroToPrecise (k_3 ✖️ z13_j));
        (Some "k_3 = 1 => z13_j_prime = 0",
          Constraint.EqualZeroToPrecise (k_3 ✖️ z13_j_prime))
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

Definition witness_message_piece
    (region : RegionId.t)
    (column : Advice.t)
    (name : string)
    : 𝓛 columns RegionId.t (Cell.t columns RegionId.t) :=
  ℒ.InNamespace name (
    ℒ.AddRegion region "witness message piece" (
      ℛ.AssignAdvice "witness message piece" column 0 0)).

Definition synthesize_short_range
    (region : RegionId.t)
    (namespace region_name : string)
    : 𝓛 columns RegionId.t (Cell.t columns RegionId.t) :=
  ℒ.InNamespace namespace (
    ℒ.AddRegion region region_name (
      let🞵 element :=
        ℛ.AssignAdvice "Witness element" Advice.A9 0 0 in
      let🞵 _ := ℛ.EnableSelector Selector.QLookup 0 "" in
      let🞵 _ := ℛ.EnableSelector Selector.QLookup 1 "" in
      let🞵 _ := ℛ.EnableSelector Selector.QBitshift 1 "" in
      return🞵 element)).

Fixpoint enable_lookup_running_rows
    (offset : Z)
    (count : nat)
    : 𝓡 columns RegionId.t unit :=
  match count with
  | O => return🞵 tt
  | S count =>
      let🞵 _ := ℛ.EnableSelector Selector.QLookup offset "" in
      let🞵 _ := ℛ.EnableSelector Selector.QRunning offset "" in
      let🞵 _ := ℛ.AssignAdvice "z" Advice.A9 offset 0 in
      enable_lookup_running_rows (offset + 1) count
  end.

Definition synthesize_running_lookup
    (region : RegionId.t)
    (namespace : string)
    (count : nat)
    : 𝓛 columns RegionId.t LookupResult.t :=
  ℒ.InNamespace namespace (
    ℒ.AddRegion region "Witness element" (
      let🞵 z_0 := ℛ.AssignAdvice "z_0" Advice.A9 0 0 in
      let🞵 z_1 := ℛ.AssignAdvice "z_1" Advice.A9 1 0 in
      let🞵 z_13 := ℛ.AssignAdvice "z_13" Advice.A9 13 0 in
      let🞵 _ := enable_lookup_running_rows 0 count in
      let🞵 z_end :=
        ℛ.AssignAdvice
          "z_end"
          Advice.A9
          (Z.of_nat count)
          0 in
      return🞵 {|
        LookupResult.z_0 := z_0;
        LookupResult.z_1 := z_1;
        LookupResult.z_13 := z_13;
        LookupResult.z_end := z_end;
      |})).

Definition copy_advice_column
    (source_column target_column : Advice.t)
    (source_offset target_offset : Z)
    : 𝓡 columns RegionId.t (Cell.t columns RegionId.t) :=
  let🞵 source :=
    ℛ.AssignAdvice "source" source_column source_offset 0 in
  copy_advice "copy" source target_column target_offset 0.

Definition synthesize_y_canonicity
    (first_region_index : Z)
    (namespace : string)
    (q_y_canon : Selector.t)
    (y : Cell.t columns RegionId.t)
    : 𝓛 columns RegionId.t (Cell.t columns RegionId.t) :=
  ℒ.InNamespace namespace (
    let🞵 k_0 :=
      synthesize_short_range
        (RegionId.of_index first_region_index)
        "k_0"
        "Range check 9 bits" in
    let🞵 k_2 :=
      synthesize_short_range
        (RegionId.of_index (first_region_index + 1))
        "k_2"
        "Range check 4 bits" in
    let🞵 j_lookup :=
      synthesize_running_lookup
        (RegionId.of_index (first_region_index + 2))
        "Decompose j = LSB + (2)k_0 + (2^10)k_1"
        25%nat in
    let🞵 j_prime_lookup :=
      ℒ.InNamespace "j_prime = j + 2^130 - t_P" (
        synthesize_running_lookup
          (RegionId.of_index (first_region_index + 3))
          "Decompose low 130 bits of (a + 2^130 - t_P)"
          13%nat) in
    ℒ.AddRegion
      (RegionId.of_index (first_region_index + 4))
      "y canonicity" (
      let🞵 _ := ℛ.EnableSelector q_y_canon 0 "" in
      let🞵 y_bit := ℛ.AssignAdvice "y_bit" Advice.A6 0 0 in
      let🞵 _ := copy_advice "y" y Advice.A5 0 0 in
      let🞵 _ := copy_advice "k_0" k_0 Advice.A7 0 0 in
      let🞵 _ := copy_advice "k_2" k_2 Advice.A8 0 0 in
      let🞵 _ :=
        copy_advice "j_0" j_lookup.(LookupResult.z_0) Advice.A5 1 0 in
      let🞵 _ :=
        copy_advice "j_1" j_lookup.(LookupResult.z_1) Advice.A6 1 0 in
      let🞵 _ :=
        copy_advice "j_13" j_lookup.(LookupResult.z_13) Advice.A7 1 0 in
      let🞵 _ :=
        copy_advice
          "j_prime_0"
          j_prime_lookup.(LookupResult.z_0)
          Advice.A8
          1
          0 in
      let🞵 _ :=
        copy_advice
          "j_prime_13"
          j_prime_lookup.(LookupResult.z_end)
          Advice.A9
          1
          0 in
      return🞵 y_bit)).

Definition synthesize_instance
    (first_region_index : Z)
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
    witness_message_piece (RegionId.of_index first_region_index) piece_column "a" in
  let🞵 b_0 :=
    synthesize_short_range
      (RegionId.of_index (first_region_index + 1))
      "b_0"
      "Range check 4 bits" in
  let🞵 b_3 :=
    synthesize_short_range
      (RegionId.of_index (first_region_index + 2))
      "b_3"
      "Range check 4 bits" in
  let🞵 b :=
    witness_message_piece
      (RegionId.of_index (first_region_index + 3))
      piece_column
      "b" in
  let🞵 c :=
    witness_message_piece
      (RegionId.of_index (first_region_index + 4))
      piece_column
      "c" in
  let🞵 d_2 :=
    synthesize_short_range
      (RegionId.of_index (first_region_index + 5))
      "d_2"
      "Range check 8 bits" in
  let🞵 d :=
    witness_message_piece
      (RegionId.of_index (first_region_index + 6))
      piece_column
      "d" in
  let🞵 e_0 :=
    synthesize_short_range
      (RegionId.of_index (first_region_index + 7))
      "e_0"
      "Range check 6 bits" in
  let🞵 e_1 :=
    synthesize_short_range
      (RegionId.of_index (first_region_index + 8))
      "e_1"
      "Range check 4 bits" in
  let🞵 e :=
    witness_message_piece
      (RegionId.of_index (first_region_index + 9))
      piece_column
      "e" in
  let🞵 f :=
    witness_message_piece
      (RegionId.of_index (first_region_index + 10))
      piece_column
      "f" in
  let🞵 g_1 :=
    synthesize_short_range
      (RegionId.of_index (first_region_index + 11))
      "g_1"
      "Range check 9 bits" in
  let🞵 g :=
    witness_message_piece
      (RegionId.of_index (first_region_index + 12))
      piece_column
      "g" in
  let🞵 h_0 :=
    synthesize_short_range
      (RegionId.of_index (first_region_index + 13))
      "h_0"
      "Range check 5 bits" in
  let🞵 h :=
    witness_message_piece
      (RegionId.of_index (first_region_index + 14))
      piece_column
      "h" in
  let🞵 b_2 :=
    synthesize_y_canonicity
      (first_region_index + 15)
      "y(g_d) decomposition"
      q_y_canon
      g_d_y in
  let🞵 d_1 :=
    synthesize_y_canonicity
      (first_region_index + 20)
      "y(pk_d) decomposition"
      q_y_canon
      pk_d_y in
  let🞵 '(cm, hash) :=
    ℒ.InNamespace "Process NoteCommit inputs" (
      let🞵 blind :=
        ℒ.InNamespace "[r] R" (
          ℒ.InNamespace "fixed-base mul of NoteCommitR" (
            synthesize_full_fixed_base_mul_note_commit_r
              (first_region_index + 25))) in
      let🞵 m_hash :=
        ℒ.InNamespace "M" (
          (if use_second_sinsemilla
           then Garden.Halo2.Gadgets.Sinsemilla.chip.synthesize_hash_to_point_note_commit_2
           else Garden.Halo2.Gadgets.Sinsemilla.chip.synthesize_hash_to_point_note_commit)
            (RegionId.of_index (first_region_index + 27))
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
        ℒ.InNamespace "M + [r] R" (
          ℒ.AddRegion
            (RegionId.of_index (first_region_index + 28))
            "complete point addition" (
            assign_complete_add m blind)) in
      return🞵 (cm, m_hash)) in
  let🞵 x_gd_lookup :=
    ℒ.InNamespace "x(g_d) canonicity" (
      synthesize_running_lookup
        (RegionId.of_index (first_region_index + 29))
        "Decompose low 130 bits of (a + 2^130 - t_P)"
        13%nat) in
  let🞵 x_pkd_lookup :=
    ℒ.InNamespace "x(pk_d) canonicity" (
      synthesize_running_lookup
        (RegionId.of_index (first_region_index + 30))
        "Decompose low 140 bits of (b_3 + 2^4 c + 2^140 - t_P)"
        14%nat) in
  let🞵 rho_lookup :=
    ℒ.InNamespace "rho canonicity" (
      synthesize_running_lookup
        (RegionId.of_index (first_region_index + 31))
        "Decompose low 140 bits of (e_1 + 2^4 f + 2^140 - t_P)"
        14%nat) in
  let🞵 psi_lookup :=
    ℒ.InNamespace "psi canonicity" (
      synthesize_running_lookup
        (RegionId.of_index (first_region_index + 32))
        "Decompose low 130 bits of (g_1 + (2^9)g_2 + 2^130 - t_P)"
        13%nat) in
  let🞵 b_1 :=
    ℒ.AddRegion
      (RegionId.of_index (first_region_index + 33))
      "NoteCommit MessagePiece b" (
      let🞵 _ := ℛ.EnableSelector q_b 0 "" in
      let🞵 _ := copy_advice "b" b Advice.A6 0 0 in
      let🞵 _ := copy_advice "b_0" b_0 Advice.A7 0 0 in
      let🞵 b_1 := ℛ.AssignAdvice "b_1" Advice.A8 0 0 in
      let🞵 _ := copy_advice "b_2" b_2 Advice.A7 1 0 in
      let🞵 _ := copy_advice "b_3" b_3 Advice.A8 1 0 in
      return🞵 b_1) in
  let🞵 d_0 :=
    ℒ.AddRegion
      (RegionId.of_index (first_region_index + 34))
      "NoteCommit MessagePiece d" (
      let🞵 _ := ℛ.EnableSelector q_d 0 "" in
      let🞵 _ := copy_advice "d" d Advice.A6 0 0 in
      let🞵 d_0 := ℛ.AssignAdvice "d_0" Advice.A7 0 0 in
      let🞵 _ := copy_advice "d_1" d_1 Advice.A8 0 0 in
      let🞵 _ := copy_advice "d_2" d_2 Advice.A7 1 0 in
      let🞵 _ :=
        copy_advice
          "d_3"
          hash.(Garden.Halo2.Gadgets.Sinsemilla.chip.HashResult.z1_d)
          Advice.A8
          1
          0 in
      return🞵 d_0) in
  let🞵 _ :=
    ℒ.AddRegion
      (RegionId.of_index (first_region_index + 35))
      "NoteCommit MessagePiece e" (
      let🞵 _ := ℛ.EnableSelector q_e 0 "" in
      let🞵 _ := copy_advice "e" e Advice.A6 0 0 in
      let🞵 _ := copy_advice "e_0" e_0 Advice.A7 0 0 in
      let🞵 _ := copy_advice "e_1" e_1 Advice.A8 0 0 in
      return🞵 tt) in
  let🞵 g_0 :=
    ℒ.AddRegion
      (RegionId.of_index (first_region_index + 36))
      "NoteCommit MessagePiece g" (
      let🞵 _ := ℛ.EnableSelector q_g 0 "" in
      let🞵 _ := copy_advice "g" g Advice.A6 0 0 in
      let🞵 g_0 := ℛ.AssignAdvice "g_0" Advice.A7 0 0 in
      let🞵 _ := copy_advice "g_1" g_1 Advice.A6 1 0 in
      let🞵 _ :=
        copy_advice
          "g_2"
          hash.(Garden.Halo2.Gadgets.Sinsemilla.chip.HashResult.z1_g)
          Advice.A7
          1
          0 in
      return🞵 g_0) in
  let🞵 h_1 :=
    ℒ.AddRegion
      (RegionId.of_index (first_region_index + 37))
      "NoteCommit MessagePiece h" (
      let🞵 _ := ℛ.EnableSelector q_h 0 "" in
      let🞵 _ := copy_advice "h" h Advice.A6 0 0 in
      let🞵 _ := copy_advice "h_0" h_0 Advice.A7 0 0 in
      let🞵 h_1 := ℛ.AssignAdvice "h_1" Advice.A8 0 0 in
      return🞵 h_1) in
  let🞵 _ :=
    ℒ.AddRegion
      (RegionId.of_index (first_region_index + 38))
      "NoteCommit input g_d" (
      let🞵 _ := copy_advice "gd_x" g_d_x Advice.A6 0 0 in
      let🞵 _ := copy_advice "b_0" b_0 Advice.A7 0 0 in
      let🞵 _ := copy_advice "b_1" b_1 Advice.A7 1 0 in
      let🞵 _ := copy_advice "a" a Advice.A8 0 0 in
      let🞵 _ :=
        copy_advice "a_prime" x_gd_lookup.(LookupResult.z_0) Advice.A8 1 0 in
      let🞵 _ :=
        copy_advice
          "z13_a"
          hash.(Garden.Halo2.Gadgets.Sinsemilla.chip.HashResult.z13_a)
          Advice.A9
          0
          0 in
      let🞵 _ :=
        copy_advice
          "z13_a_prime"
          x_gd_lookup.(LookupResult.z_end)
          Advice.A9
          1
          0 in
      ℛ.EnableSelector q_gd 0 "") in
  let🞵 _ :=
    ℒ.AddRegion
      (RegionId.of_index (first_region_index + 39))
      "NoteCommit input pk_d" (
      let🞵 _ := copy_advice "pkd_x" pk_d_x Advice.A6 0 0 in
      let🞵 _ := copy_advice "b_3" b_3 Advice.A7 0 0 in
      let🞵 _ := copy_advice "d_0" d_0 Advice.A7 1 0 in
      let🞵 _ := copy_advice "c" c Advice.A8 0 0 in
      let🞵 _ :=
        copy_advice "b3_c_prime" x_pkd_lookup.(LookupResult.z_0) Advice.A8 1 0 in
      let🞵 _ :=
        copy_advice
          "z13_c"
          hash.(Garden.Halo2.Gadgets.Sinsemilla.chip.HashResult.z13_c)
          Advice.A9
          0
          0 in
      let🞵 _ :=
        copy_advice
          "z14_b3_c_prime"
          x_pkd_lookup.(LookupResult.z_end)
          Advice.A9
          1
          0 in
      ℛ.EnableSelector q_pkd 0 "") in
  let🞵 _ :=
    ℒ.AddRegion
      (RegionId.of_index (first_region_index + 40))
      "NoteCommit input value" (
      let🞵 _ := copy_advice "value" value Advice.A6 0 0 in
      let🞵 _ := copy_advice "d_2" d_2 Advice.A7 0 0 in
      let🞵 _ :=
        copy_advice
          "d3"
          hash.(Garden.Halo2.Gadgets.Sinsemilla.chip.HashResult.z1_d)
          Advice.A8
          0
          0 in
      let🞵 _ := copy_advice "e_0" e_0 Advice.A9 0 0 in
      ℛ.EnableSelector q_value 0 "") in
  let🞵 _ :=
    ℒ.AddRegion
      (RegionId.of_index (first_region_index + 41))
      "NoteCommit input rho" (
      let🞵 _ := copy_advice "rho" rho Advice.A6 0 0 in
      let🞵 _ := copy_advice "e_1" e_1 Advice.A7 0 0 in
      let🞵 _ := copy_advice "g_0" g_0 Advice.A7 1 0 in
      let🞵 _ := copy_advice "f" f Advice.A8 0 0 in
      let🞵 _ :=
        copy_advice "e1_f_prime" rho_lookup.(LookupResult.z_0) Advice.A8 1 0 in
      let🞵 _ :=
        copy_advice
          "z13_f"
          hash.(Garden.Halo2.Gadgets.Sinsemilla.chip.HashResult.z13_f)
          Advice.A9
          0
          0 in
      let🞵 _ :=
        copy_advice
          "z14_e1_f_prime"
          rho_lookup.(LookupResult.z_end)
          Advice.A9
          1
          0 in
      ℛ.EnableSelector q_rho 0 "") in
  let🞵 _ :=
    ℒ.AddRegion
      (RegionId.of_index (first_region_index + 42))
      "NoteCommit input psi" (
      let🞵 _ := copy_advice "psi" psi Advice.A6 0 0 in
      let🞵 _ := copy_advice "h_0" h_0 Advice.A6 1 0 in
      let🞵 _ := copy_advice "g_1" g_1 Advice.A7 0 0 in
      let🞵 _ := copy_advice "h_1" h_1 Advice.A7 1 0 in
      let🞵 _ :=
        copy_advice
          "g_2"
          hash.(Garden.Halo2.Gadgets.Sinsemilla.chip.HashResult.z1_g)
          Advice.A8
          0
          0 in
      let🞵 _ :=
        copy_advice "g1_g2_prime" psi_lookup.(LookupResult.z_0) Advice.A8 1 0 in
      let🞵 _ :=
        copy_advice
          "z13_g"
          hash.(Garden.Halo2.Gadgets.Sinsemilla.chip.HashResult.z13_g)
          Advice.A9
          0
          0 in
      let🞵 _ :=
        copy_advice
          "z13_g1_g2_prime"
          psi_lookup.(LookupResult.z_end)
          Advice.A9
          1
          0 in
      ℛ.EnableSelector q_psi 0 "") in
  return🞵 cm.

Definition synthesize_old
    (g_d_x g_d_y pk_d_x pk_d_y value rho psi : Cell.t columns RegionId.t)
    : 𝓛 columns RegionId.t AssignedPoint.t :=
  synthesize_instance
    303
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
    350
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
