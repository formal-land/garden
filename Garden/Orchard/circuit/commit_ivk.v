Require Import Garden.Halo2.main.
Require Import Garden.Halo2.Synthesis.
Require Import Garden.Orchard.columns.
Require Garden.Halo2.Gadgets.Utilities.
Require Garden.Halo2.Gadgets.Ecc.chip.constants.
Require Garden.Halo2.Gadgets.Sinsemilla.chip.
Require Garden.Orchard.FixedBases.CommitIvkR.

Import ListNotations.
Global Open Scope pstring_scope.
Global Open Scope Z_scope.

Definition configure
    (meta : ConstraintSystem.t columns)
    : ConstraintSystem.t columns :=
  let meta := ConstraintSystem.create_gate meta {|
    Gate.name := "CommitIvk canonicity check";
    Gate.constraints :=
      let ak := Expression.Advice Advice.A0 Rotation.cur in
      let nk := Expression.Advice Advice.A0 Rotation.next in
      let a := Expression.Advice Advice.A1 Rotation.cur in
      let b_whole := Expression.Advice Advice.A2 Rotation.cur in
      let c := Expression.Advice Advice.A1 Rotation.next in
      let d_whole := Expression.Advice Advice.A2 Rotation.next in
      let b_0 := Expression.Advice Advice.A3 Rotation.cur in
      let b_1 := Expression.Advice Advice.A4 Rotation.cur in
      let b_2 := Expression.Advice Advice.A5 Rotation.cur in
      let d_0 := Expression.Advice Advice.A3 Rotation.next in
      let d_1 := Expression.Advice Advice.A4 Rotation.next in
      let b_decomposition_check :=
        b_whole ➖ (b_0 ➕ (b_1 ● (2 ^ 4)) ➕ (b_2 ● (2 ^ 5))) in
      let d_decomposition_check :=
        d_whole ➖ (d_0 ➕ (d_1 ● (2 ^ 9))) in
      let b1_bool_check := Garden.Halo2.Gadgets.Utilities.bool_check b_1 in
      let d1_bool_check := Garden.Halo2.Gadgets.Utilities.bool_check d_1 in
      let ak_decomposition_check :=
        a ➕ (b_0 ● (2 ^ 250)) ➕ (b_1 ● (2 ^ 254)) ➖ ak in
      let nk_decomposition_check :=
        b_2 ➕ (c ● (2 ^ 5)) ➕ (d_0 ● (2 ^ 245))
          ➕ (d_1 ● (2 ^ 254)) ➖ nk in
      let z13_a := Expression.Advice Advice.A6 Rotation.cur in
      let a_prime := Expression.Advice Advice.A7 Rotation.cur in
      let z13_a_prime := Expression.Advice Advice.A8 Rotation.cur in
      let b0_canon_check := b_1 ✖️ b_0 in
      let z13_a_check := b_1 ✖️ z13_a in
      let a_prime_check :=
        a ➕ Expression.Constant (2 ^ 130)
          ➖ Expression.Constant Garden.Halo2.Gadgets.Ecc.chip.constants.t_p
          ➖ a_prime in
      let z13_a_prime := b_1 ✖️ z13_a_prime in
      let z13_c := Expression.Advice Advice.A6 Rotation.next in
      let b2_c_prime := Expression.Advice Advice.A7 Rotation.next in
      let z14_b2_c_prime := Expression.Advice Advice.A8 Rotation.next in
      let c0_canon_check := d_1 ✖️ d_0 in
      let z13_c_check := d_1 ✖️ z13_c in
      let b2_c_prime_check :=
        b_2 ➕ (c ● (2 ^ 5)) ➕ Expression.Constant (2 ^ 140)
          ➖ Expression.Constant Garden.Halo2.Gadgets.Ecc.chip.constants.t_p
          ➖ b2_c_prime in
      let z14_b2_c_prime := d_1 ✖️ z14_b2_c_prime in
      Constraints.with_selector Selector.QCommitIvk [
        (Some "b1_bool_check", Constraint.EqualZeroToPrecise b1_bool_check);
        (Some "d1_bool_check", Constraint.EqualZeroToPrecise d1_bool_check);
        (Some "b_decomposition_check",
          Constraint.EqualZeroToPrecise b_decomposition_check);
        (Some "d_decomposition_check",
          Constraint.EqualZeroToPrecise d_decomposition_check);
        (Some "ak_decomposition_check",
          Constraint.EqualZeroToPrecise ak_decomposition_check);
        (Some "nk_decomposition_check",
          Constraint.EqualZeroToPrecise nk_decomposition_check);
        (Some "b0_canon_check", Constraint.EqualZeroToPrecise b0_canon_check);
        (Some "z13_a_check", Constraint.EqualZeroToPrecise z13_a_check);
        (Some "a_prime_check", Constraint.EqualZeroToPrecise a_prime_check);
        (Some "z13_a_prime", Constraint.EqualZeroToPrecise z13_a_prime);
        (Some "c0_canon_check", Constraint.EqualZeroToPrecise c0_canon_check);
        (Some "z13_c_check", Constraint.EqualZeroToPrecise z13_c_check);
        (Some "b2_c_prime_check",
          Constraint.EqualZeroToPrecise b2_c_prime_check);
        (Some "z14_b2_c_prime",
          Constraint.EqualZeroToPrecise z14_b2_c_prime)
      ];
  |} in
  meta.

Module AssignedPoint.
  Record t : Set := {
    x : Cell.t columns;
    y : Cell.t columns;
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
    z_0 : Cell.t columns;
    z_end : Cell.t columns;
  }.
End LookupResult.

Definition fixed_base_row : Set :=
  list (Fixed.t * string * Z).

Fixpoint assign_fixed_row
    (offset : Z)
    (row : fixed_base_row)
    : Region.t columns unit :=
  match row with
  | [] => return_ℛ tt
  | (column, annotation, value) :: row =>
      let_ℛ _ :=
        Region.assign_fixed annotation column offset (Value.Known value) in
      assign_fixed_row offset row
  end.

Fixpoint assign_fixed_rows_with_selector
    (selector : Selector.t)
    (offset : Z)
    (rows : list fixed_base_row)
    : Region.t columns unit :=
  match rows with
  | [] => return_ℛ tt
  | row :: rows =>
      let_ℛ _ := Region.enable_selector selector offset "" in
      let_ℛ _ := assign_fixed_row offset row in
      assign_fixed_rows_with_selector selector (offset + 1) rows
  end.

Definition assign_mul_fixed_window
    (offset : Z)
    : Region.t columns AssignedPoint.t :=
  let_ℛ x :=
    Region.assign_advice "mul_b_x" Advice.A0 offset Value.Unknown in
  let_ℛ y :=
    Region.assign_advice "mul_b_y" Advice.A1 offset Value.Unknown in
  let_ℛ _ :=
    Region.assign_advice "u" Advice.A5 offset Value.Unknown in
  return_ℛ {| AssignedPoint.x := x; AssignedPoint.y := y |}.

Definition assign_add_incomplete
    (offset : Z)
    (p q : AssignedPoint.t)
    : Region.t columns AssignedPoint.t :=
  let_ℛ _ := Region.enable_selector Selector.QAddIncomplete offset "" in
  let_ℛ _ :=
    Region.copy_advice "x_p" p.(AssignedPoint.x) Advice.A0 offset Value.Unknown in
  let_ℛ _ :=
    Region.copy_advice "y_p" p.(AssignedPoint.y) Advice.A1 offset Value.Unknown in
  let_ℛ _ :=
    Region.copy_advice "x_q" q.(AssignedPoint.x) Advice.A2 offset Value.Unknown in
  let_ℛ _ :=
    Region.copy_advice "y_q" q.(AssignedPoint.y) Advice.A3 offset Value.Unknown in
  let_ℛ x_r :=
    Region.assign_advice "x_r" Advice.A2 (offset + 1) Value.Unknown in
  let_ℛ y_r :=
    Region.assign_advice "y_r" Advice.A3 (offset + 1) Value.Unknown in
  return_ℛ {| AssignedPoint.x := x_r; AssignedPoint.y := y_r |}.

Fixpoint assign_incomplete_additions
    (offset : Z)
    (count : nat)
    (acc : AssignedPoint.t)
    : Region.t columns AssignedPoint.t :=
  match count with
  | O => return_ℛ acc
  | S count =>
      let_ℛ mul_b := assign_mul_fixed_window offset in
      let_ℛ acc := assign_add_incomplete offset mul_b acc in
      assign_incomplete_additions (offset + 1) count acc
  end.

Fixpoint assign_full_window_witnesses
    (offset : Z)
    (count : nat)
    : Region.t columns unit :=
  match count with
  | O => return_ℛ tt
  | S count =>
      let_ℛ _ :=
        Region.enable_selector Selector.QMulFixedFull offset "" in
      let_ℛ _ := Region.assign_advice "k" Advice.A4 offset Value.Unknown in
      assign_full_window_witnesses (offset + 1) count
  end.

Definition assign_complete_add
    (p q : AssignedPoint.t)
    : Region.t columns AssignedPoint.t :=
  let_ℛ _ := Region.enable_selector Selector.QEccAdd 0 "" in
  let_ℛ _ :=
    Region.copy_advice "x_p" p.(AssignedPoint.x) Advice.A0 0 Value.Unknown in
  let_ℛ _ :=
    Region.copy_advice "y_p" p.(AssignedPoint.y) Advice.A1 0 Value.Unknown in
  let_ℛ _ :=
    Region.copy_advice "x_q" q.(AssignedPoint.x) Advice.A2 0 Value.Unknown in
  let_ℛ _ :=
    Region.copy_advice "y_q" q.(AssignedPoint.y) Advice.A3 0 Value.Unknown in
  let_ℛ _ := Region.assign_advice "alpha" Advice.A5 0 Value.Unknown in
  let_ℛ _ := Region.assign_advice "beta" Advice.A6 0 Value.Unknown in
  let_ℛ _ := Region.assign_advice "gamma" Advice.A7 0 Value.Unknown in
  let_ℛ _ := Region.assign_advice "delta" Advice.A8 0 Value.Unknown in
  let_ℛ _ := Region.assign_advice "lambda" Advice.A4 0 Value.Unknown in
  let_ℛ x_r := Region.assign_advice "x_r" Advice.A2 1 Value.Unknown in
  let_ℛ y_r := Region.assign_advice "y_r" Advice.A3 1 Value.Unknown in
  return_ℛ {| AssignedPoint.x := x_r; AssignedPoint.y := y_r |}.

Definition synthesize_full_fixed_base_mul_incomplete_region
    : Layouter.t columns FullFixedResult.t :=
  Layouter.assign_region "Full-width fixed-base mul (incomplete addition)" (
    let_ℛ _ := assign_full_window_witnesses 0 85%nat in
    let_ℛ _ :=
      assign_fixed_rows_with_selector
        Selector.QMulFixedFull
        0
        Garden.Orchard.FixedBases.CommitIvkR.full_fixed_rows in
    let_ℛ acc := assign_mul_fixed_window 0 in
    let_ℛ acc := assign_incomplete_additions 1 83%nat acc in
    let_ℛ mul_b := assign_mul_fixed_window 84 in
    return_ℛ {|
      FullFixedResult.acc := acc;
      FullFixedResult.mul_b := mul_b;
    |}).

Definition synthesize_full_fixed_base_mul_last_region
    (result : FullFixedResult.t)
    : Layouter.t columns AssignedPoint.t :=
  Layouter.assign_region "Full-width fixed-base mul (last window, complete addition)" (
    assign_complete_add
      result.(FullFixedResult.mul_b)
      result.(FullFixedResult.acc)).

Definition synthesize_full_fixed_base_mul_commit_ivk_r
    : Layouter.t columns AssignedPoint.t :=
  let_ℒ result := synthesize_full_fixed_base_mul_incomplete_region in
  synthesize_full_fixed_base_mul_last_region result.

Definition q_commit_ivk_m_x : Z :=
  2593820817260930114322133467408868473290945477826616247349533151445648376562.

Definition q_commit_ivk_m_y : Z :=
  12214744946019415453501880094709511126888074367290315326445800415816181472958.

Definition witness_message_piece
    (name : string)
    : Layouter.t columns (Cell.t columns) :=
  Layouter.namespace name (
    Layouter.assign_region "witness message piece" (
      Region.assign_advice "witness message piece" Advice.A6 0 Value.Unknown)).

Definition synthesize_range_check
    (namespace region_name : string)
    : Layouter.t columns (Cell.t columns) :=
  Layouter.namespace namespace (
    Layouter.assign_region region_name (
      let_ℛ element :=
        Region.assign_advice "Witness element" Advice.A9 0 Value.Unknown in
      let_ℛ _ := Region.enable_selector Selector.QLookup 0 "" in
      let_ℛ _ := Region.enable_selector Selector.QLookup 1 "" in
      let_ℛ _ := Region.enable_selector Selector.QBitshift 1 "" in
      return_ℛ element)).

Fixpoint enable_lookup_running_rows
    (offset : Z)
    (count : nat)
    : Region.t columns unit :=
  match count with
  | O => return_ℛ tt
  | S count =>
      let_ℛ _ := Region.enable_selector Selector.QLookup offset "" in
      let_ℛ _ := Region.enable_selector Selector.QRunning offset "" in
      let_ℛ _ := Region.assign_advice "z" Advice.A9 offset Value.Unknown in
      enable_lookup_running_rows (offset + 1) count
  end.

Definition synthesize_running_lookup
    (namespace region_namespace : string)
    (count : nat)
    : Layouter.t columns LookupResult.t :=
  Layouter.namespace namespace (
    Layouter.namespace region_namespace (
      Layouter.assign_region "Witness element" (
        let_ℛ z_0 :=
          Region.assign_advice "z_0" Advice.A9 0 Value.Unknown in
        let_ℛ _ := enable_lookup_running_rows 0 count in
        let_ℛ z_end :=
          Region.assign_advice
            "z_end"
            Advice.A9
            (Z.of_nat count)
            Value.Unknown in
        return_ℛ {|
          LookupResult.z_0 := z_0;
          LookupResult.z_end := z_end;
        |}))).

Definition assign_cells_used_in_canonicity_gate
    (ak nk : Cell.t columns)
    (a b c d : Cell.t columns)
    (b_0 b_2 d_0 : Cell.t columns)
    (hash : Garden.Halo2.Gadgets.Sinsemilla.chip.HashResult.t)
    (ak_lookup nk_lookup : LookupResult.t)
    : Layouter.t columns unit :=
  Layouter.namespace "Assign cells used in canonicity gate" (
    Layouter.assign_region "Assign cells used in canonicity gate" (
      let_ℛ _ := Region.enable_selector Selector.QCommitIvk 0 "" in
      let_ℛ _ := Region.copy_advice "ak" ak Advice.A0 0 Value.Unknown in
      let_ℛ _ := Region.copy_advice "a" a Advice.A1 0 Value.Unknown in
      let_ℛ _ := Region.copy_advice "b" b Advice.A2 0 Value.Unknown in
      let_ℛ _ := Region.copy_advice "b_0" b_0 Advice.A3 0 Value.Unknown in
      let_ℛ _ := Region.assign_advice "Witness b_1" Advice.A4 0 Value.Unknown in
      let_ℛ _ := Region.copy_advice "b_2" b_2 Advice.A5 0 Value.Unknown in
      let_ℛ _ :=
        Region.copy_advice
          "z13_a"
          hash.(Garden.Halo2.Gadgets.Sinsemilla.chip.HashResult.z13_a)
          Advice.A6
          0
          Value.Unknown in
      let_ℛ _ :=
        Region.copy_advice
          "a_prime"
          ak_lookup.(LookupResult.z_0)
          Advice.A7
          0
          Value.Unknown in
      let_ℛ _ :=
        Region.copy_advice
          "z13_a_prime"
          ak_lookup.(LookupResult.z_end)
          Advice.A8
          0
          Value.Unknown in
      let_ℛ _ := Region.copy_advice "nk" nk Advice.A0 1 Value.Unknown in
      let_ℛ _ := Region.copy_advice "c" c Advice.A1 1 Value.Unknown in
      let_ℛ _ := Region.copy_advice "d" d Advice.A2 1 Value.Unknown in
      let_ℛ _ := Region.copy_advice "d_0" d_0 Advice.A3 1 Value.Unknown in
      let_ℛ _ := Region.assign_advice "Witness d_1" Advice.A4 1 Value.Unknown in
      let_ℛ _ :=
        Region.copy_advice
          "z13_c"
          hash.(Garden.Halo2.Gadgets.Sinsemilla.chip.HashResult.z13_c)
          Advice.A6
          1
          Value.Unknown in
      let_ℛ _ :=
        Region.copy_advice
          "b2_c_prime"
          nk_lookup.(LookupResult.z_0)
          Advice.A7
          1
          Value.Unknown in
      let_ℛ _ :=
        Region.copy_advice
          "z14_b2_c_prime"
          nk_lookup.(LookupResult.z_end)
          Advice.A8
          1
          Value.Unknown in
      return_ℛ tt)).

Definition synthesize
    (ak nk : Cell.t columns)
    : Layouter.t columns unit :=
  let_ℒ a := witness_message_piece "a" in
  let_ℒ b_0 := synthesize_range_check "b_0" "Range check 4 bits" in
  let_ℒ b_2 := synthesize_range_check "b_2" "Range check 5 bits" in
  let_ℒ b := witness_message_piece "b = b_0 || b_1 || b_2" in
  let_ℒ c := witness_message_piece "c" in
  let_ℒ d_0 := synthesize_range_check "d_0" "Range check 9 bits" in
  let_ℒ d := witness_message_piece "d = d_0 || d_1" in
  let_ℒ hash :=
    Layouter.namespace "Hash ak||nk" (
    Layouter.namespace "commit" (
      let_ℒ blind :=
        Layouter.namespace "[r] R" (
          Layouter.namespace "fixed-base mul of CommitIvkR" (
            synthesize_full_fixed_base_mul_commit_ivk_r)) in
      let_ℒ m_hash :=
        Layouter.namespace "M" (
          Garden.Halo2.Gadgets.Sinsemilla.chip.synthesize_hash_to_point_commit_ivk
            q_commit_ivk_m_x
            q_commit_ivk_m_y
            a
            b
            c
            d) in
      let m := {|
        AssignedPoint.x :=
          m_hash.(Garden.Halo2.Gadgets.Sinsemilla.chip.HashResult.x);
        AssignedPoint.y :=
          m_hash.(Garden.Halo2.Gadgets.Sinsemilla.chip.HashResult.y);
      |} in
      let_ℒ _ :=
        Layouter.namespace "M + [r] R" (
          Layouter.assign_region "complete point addition" (
            assign_complete_add m blind)) in
      return_ℒ m_hash)) in
  let_ℒ ak_lookup :=
    synthesize_running_lookup
      "ak canonicity"
      "Decompose low 130 bits of (a + 2^130 - t_P)"
      13%nat in
  let_ℒ nk_lookup :=
    synthesize_running_lookup
      "nk canonicity"
      "Decompose low 140 bits of (b_2 + c * 2^5 + 2^140 - t_P)"
      14%nat in
  assign_cells_used_in_canonicity_gate
    ak
    nk
    a
    b
    c
    d
    b_0
    b_2
    d_0
    hash
    ak_lookup
    nk_lookup.
