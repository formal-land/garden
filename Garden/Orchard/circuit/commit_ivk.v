Require Import Garden.Halo2.main.
Require Import Garden.Halo2.Synthesis.
Require Import Garden.Orchard.columns.
Require Garden.Halo2.halo2_gadgets.utilities.
Require Garden.Halo2.halo2_gadgets.ecc.chip.constants.
Require Garden.Halo2.halo2_gadgets.sinsemilla.chip.
Require Garden.Orchard.constants.fixed_bases.commit_ivk_r.

Import ListNotations.
Global Open Scope pstring_scope.
Global Open Scope Z_scope.

Definition commit_ivk_region (region : RegionId.CommitIvk.t) : RegionId.t :=
  RegionId.CommitIvk region.

Definition commit_ivk_canonicity_check_gate : Gate.t columns := {|
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
        ➖ Expression.Constant Garden.Halo2.halo2_gadgets.ecc.chip.constants.t_p
        ➖ a_prime in
    let z13_c := Expression.Advice Advice.A6 Rotation.next in
    let b2_c_prime := Expression.Advice Advice.A7 Rotation.next in
    let z14_b2_c_prime := Expression.Advice Advice.A8 Rotation.next in
    let c0_canon_check := d_1 ✖️ d_0 in
    let z13_c_check := d_1 ✖️ z13_c in
    let b2_c_prime_check :=
      b_2 ➕ (c ● (2 ^ 5)) ➕ Expression.Constant (2 ^ 140)
        ➖ Expression.Constant Garden.Halo2.halo2_gadgets.ecc.chip.constants.t_p
        ➖ b2_c_prime in
    Constraints.with_selector Selector.QCommitIvk [
      (Some "b1_bool_check", Constraint.Boolean b_1);
      (Some "d1_bool_check", Constraint.Boolean d_1);
      (Some "b_decomposition_check",
        Constraint.Equal
          b_whole
          (b_0 ➕ (b_1 ● (2 ^ 4)) ➕ (b_2 ● (2 ^ 5))));
      (Some "d_decomposition_check",
        Constraint.Equal d_whole (d_0 ➕ (d_1 ● (2 ^ 9))));
      (Some "ak_decomposition_check",
        Constraint.Equal
          (a ➕ (b_0 ● (2 ^ 250)) ➕ (b_1 ● (2 ^ 254)))
          ak);
      (Some "nk_decomposition_check",
        Constraint.Equal
          (b_2 ➕ (c ● (2 ^ 5)) ➕ (d_0 ● (2 ^ 245))
            ➕ (d_1 ● (2 ^ 254)))
          nk);
      (Some "b0_canon_check",
        Constraint.Either
          (Constraint.EqualZeroToPrecise b_1)
          (Constraint.EqualZeroToPrecise b_0));
      (Some "z13_a_check",
        Constraint.Either
          (Constraint.EqualZeroToPrecise b_1)
          (Constraint.EqualZeroToPrecise z13_a));
      (Some "a_prime_check",
        Constraint.Equal
          (a ➕ Expression.Constant (2 ^ 130)
            ➖ Expression.Constant Garden.Halo2.halo2_gadgets.ecc.chip.constants.t_p)
          a_prime);
      (Some "z13_a_prime",
        Constraint.Either
          (Constraint.EqualZeroToPrecise b_1)
          (Constraint.EqualZeroToPrecise z13_a_prime));
      (Some "c0_canon_check",
        Constraint.Either
          (Constraint.EqualZeroToPrecise d_1)
          (Constraint.EqualZeroToPrecise d_0));
      (Some "z13_c_check",
        Constraint.Either
          (Constraint.EqualZeroToPrecise d_1)
          (Constraint.EqualZeroToPrecise z13_c));
      (Some "b2_c_prime_check",
        Constraint.Equal
          (b_2 ➕ (c ● (2 ^ 5)) ➕ Expression.Constant (2 ^ 140)
            ➖ Expression.Constant Garden.Halo2.halo2_gadgets.ecc.chip.constants.t_p)
          b2_c_prime);
      (Some "z14_b2_c_prime",
        Constraint.Either
          (Constraint.EqualZeroToPrecise d_1)
          (Constraint.EqualZeroToPrecise z14_b2_c_prime))
    ];
|}.

Definition configure : 𝓒 columns unit :=
  do🞵 𝓒.CreateGate commit_ivk_canonicity_check_gate in
  return🞵 tt.

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

Definition synth_full_mul_incomplete
    (region : RegionId.t)
    : 𝓛 columns RegionId.t FullFixedResult.t :=
  𝓛.AddRegion region "Full-width fixed-base mul (incomplete addition)" (fun region =>
    do🞵 assign_full_window_witnesses 0 85%nat in
    do🞵
      assign_fixed_rows_with_selector
        Selector.QMulFixedFull
        0
        Garden.Orchard.constants.fixed_bases.commit_ivk_r.full_fixed_rows in
    let🞵 acc := assign_mul_fixed_window region 0 in
    let🞵 acc := assign_incomplete_additions region 1 83%nat acc in
    let🞵 mul_b := assign_mul_fixed_window region 84 in
    return🞵 {|
      FullFixedResult.acc := acc;
      FullFixedResult.mul_b := mul_b;
    |}).

Definition synthesize_full_fixed_base_mul_last_region
    (region : RegionId.t)
    (result : FullFixedResult.t)
    : 𝓛 columns RegionId.t AssignedPoint.t :=
  𝓛.AddRegion region "Full-width fixed-base mul (last window, complete addition)" (fun region =>
    assign_complete_add
      region
      result.(FullFixedResult.mul_b)
      result.(FullFixedResult.acc)).

Definition synthesize_full_fixed_base_mul_commit_ivk_r
    : 𝓛 columns RegionId.t AssignedPoint.t :=
  let🞵 result :=
    synth_full_mul_incomplete
      (commit_ivk_region RegionId.CommitIvk.FixedBaseIncomplete) in
  synthesize_full_fixed_base_mul_last_region
    (commit_ivk_region RegionId.CommitIvk.FixedBaseLast)
    result.

Definition q_commit_ivk_m_x : Z :=
  2593820817260930114322133467408868473290945477826616247349533151445648376562.

Definition q_commit_ivk_m_y : Z :=
  12214744946019415453501880094709511126888074367290315326445800415816181472958.

Definition witness_message_piece
    (region : RegionId.t)
    (name : string)
    : 𝓛 columns RegionId.t (Cell.t columns RegionId.t) :=
  𝓛.InNamespace name (
    𝓛.AddRegion region "witness message piece" (fun region =>
      return🞵 (Cell.advice region Advice.A6 0))).

Definition synthesize_range_check
    (region : RegionId.t)
    (namespace region_name : string)
    (inv_two_pow_s : Z)
    : 𝓛 columns RegionId.t (Cell.t columns RegionId.t) :=
  𝓛.InNamespace namespace (
    𝓛.AddRegion region region_name (fun region =>
      let element := Cell.advice region Advice.A9 0 in
      do🞵 𝓡.EnableSelector Selector.QLookup 0 "" in
      do🞵 𝓡.EnableSelector Selector.QLookup 1 "" in
      do🞵 𝓡.EnableSelector Selector.QBitshift 1 "" in
      do🞵
        𝓡.ConstrainConstant (Cell.advice region Advice.A9 2) inv_two_pow_s in
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
    (namespace region_namespace : string)
    (count : nat)
    : 𝓛 columns RegionId.t LookupResult.t :=
  𝓛.InNamespace namespace (
    𝓛.InNamespace region_namespace (
      𝓛.AddRegion region "Witness element" (fun region =>
        let z_0 := Cell.advice region Advice.A9 0 in
        do🞵 enable_lookup_running_rows 0 count in
        let z_end := Cell.advice region Advice.A9 (Z.of_nat count) in
        return🞵 {|
          LookupResult.z_0 := z_0;
          LookupResult.z_end := z_end;
        |}))).

Definition assign_cells_used_in_canonicity_gate
    (region : RegionId.t)
    (ak nk : Cell.t columns RegionId.t)
    (a b c d : Cell.t columns RegionId.t)
    (b_0 b_2 d_0 : Cell.t columns RegionId.t)
    (hash : Garden.Halo2.halo2_gadgets.sinsemilla.chip.CommitIvkHashResult.t)
    (ak_lookup nk_lookup : LookupResult.t)
    : 𝓛 columns RegionId.t unit :=
  𝓛.InNamespace "Assign cells used in canonicity gate" (
    𝓛.AddRegion region "Assign cells used in canonicity gate" (fun region =>
      do🞵 𝓡.EnableSelector Selector.QCommitIvk 0 "" in
      let ak_target := Cell.advice region Advice.A0 0 in
      do🞵 𝓡.Copy ak_target ak in
      let a_target := Cell.advice region Advice.A1 0 in
      do🞵 𝓡.Copy a_target a in
      let b_target := Cell.advice region Advice.A2 0 in
      do🞵 𝓡.Copy b_target b in
      let b_0_target := Cell.advice region Advice.A3 0 in
      do🞵 𝓡.Copy b_0_target b_0 in
      let b_2_target := Cell.advice region Advice.A5 0 in
      do🞵 𝓡.Copy b_2_target b_2 in
      let z13_a_target := Cell.advice region Advice.A6 0 in
      do🞵
        𝓡.Copy
          z13_a_target
          hash.(Garden.Halo2.halo2_gadgets.sinsemilla.chip.CommitIvkHashResult.z13_a) in
      let a_prime_target := Cell.advice region Advice.A7 0 in
      do🞵
        𝓡.Copy a_prime_target ak_lookup.(LookupResult.z_0) in
      let z13_a_prime_target := Cell.advice region Advice.A8 0 in
      do🞵
        𝓡.Copy z13_a_prime_target ak_lookup.(LookupResult.z_end) in
      let nk_target := Cell.advice region Advice.A0 1 in
      do🞵 𝓡.Copy nk_target nk in
      let c_target := Cell.advice region Advice.A1 1 in
      do🞵 𝓡.Copy c_target c in
      let d_target := Cell.advice region Advice.A2 1 in
      do🞵 𝓡.Copy d_target d in
      let d_0_target := Cell.advice region Advice.A3 1 in
      do🞵 𝓡.Copy d_0_target d_0 in
      let z13_c_target := Cell.advice region Advice.A6 1 in
      do🞵
        𝓡.Copy
          z13_c_target
          hash.(Garden.Halo2.halo2_gadgets.sinsemilla.chip.CommitIvkHashResult.z13_c) in
      let b2_c_prime_target := Cell.advice region Advice.A7 1 in
      do🞵
        𝓡.Copy b2_c_prime_target nk_lookup.(LookupResult.z_0) in
      let z14_b2_c_prime_target := Cell.advice region Advice.A8 1 in
      do🞵
        𝓡.Copy z14_b2_c_prime_target nk_lookup.(LookupResult.z_end) in
      return🞵 tt)).

Definition synthesize
    (ak nk : Cell.t columns RegionId.t)
    : 𝓛 columns RegionId.t AssignedPoint.t :=
  let🞵 a := witness_message_piece (commit_ivk_region RegionId.CommitIvk.WitnessA) "a" in
  let🞵 b_0 :=
    synthesize_range_check
      (commit_ivk_region RegionId.CommitIvk.RangeB0)
      "b_0"
      "Range check 4 bits"
      Garden.Halo2.halo2_gadgets.ecc.chip.constants.inv_two_pow_4 in
  let🞵 b_2 :=
    synthesize_range_check
      (commit_ivk_region RegionId.CommitIvk.RangeB2)
      "b_2"
      "Range check 5 bits"
      Garden.Halo2.halo2_gadgets.ecc.chip.constants.inv_two_pow_5 in
  let🞵 b :=
    witness_message_piece
      (commit_ivk_region RegionId.CommitIvk.WitnessB)
      "b = b_0 || b_1 || b_2" in
  let🞵 c := witness_message_piece (commit_ivk_region RegionId.CommitIvk.WitnessC) "c" in
  let🞵 d_0 :=
    synthesize_range_check
      (commit_ivk_region RegionId.CommitIvk.RangeD0)
      "d_0"
      "Range check 9 bits"
      Garden.Halo2.halo2_gadgets.ecc.chip.constants.inv_two_pow_9 in
  let🞵 d :=
    witness_message_piece
      (commit_ivk_region RegionId.CommitIvk.WitnessD)
      "d = d_0 || d_1" in
  let🞵 hash :=
    𝓛.InNamespace "Hash ak||nk" (
    𝓛.InNamespace "commit" (
      let🞵 blind :=
        𝓛.InNamespace "[r] R" (
          𝓛.InNamespace "fixed-base mul of CommitIvkR" (
            synthesize_full_fixed_base_mul_commit_ivk_r)) in
      let🞵 m_hash :=
        𝓛.InNamespace "M" (
          Garden.Halo2.halo2_gadgets.sinsemilla.chip.synthesize_hash_to_point_commit_ivk
            (commit_ivk_region RegionId.CommitIvk.HashToPoint)
            q_commit_ivk_m_x
            q_commit_ivk_m_y
            a
            b
            c
            d) in
      let m := {|
        AssignedPoint.x :=
          m_hash.(Garden.Halo2.halo2_gadgets.sinsemilla.chip.CommitIvkHashResult.x);
        AssignedPoint.y :=
          m_hash.(Garden.Halo2.halo2_gadgets.sinsemilla.chip.CommitIvkHashResult.y);
      |} in
      let🞵 ivk :=
        𝓛.InNamespace "M + [r] R" (
          𝓛.AddRegion
            (commit_ivk_region RegionId.CommitIvk.CompletePointAdd)
            "complete point addition" (fun region =>
            assign_complete_add region m blind)) in
      return🞵 (m_hash, ivk))) in
  let🞵 ak_lookup :=
    synthesize_running_lookup
      (commit_ivk_region RegionId.CommitIvk.AkLookup)
      "ak canonicity"
      "Decompose low 130 bits of (a + 2^130 - t_P)"
      13%nat in
  let🞵 nk_lookup :=
    synthesize_running_lookup
      (commit_ivk_region RegionId.CommitIvk.NkLookup)
      "nk canonicity"
      "Decompose low 140 bits of (b_2 + c * 2^5 + 2^140 - t_P)"
      14%nat in
  do🞵
  assign_cells_used_in_canonicity_gate
    (commit_ivk_region RegionId.CommitIvk.CanonicityGate)
    ak
    nk
    a
    b
    c
    d
    b_0
    b_2
    d_0
    (fst hash)
    ak_lookup
    nk_lookup in
  return🞵 (snd hash).
