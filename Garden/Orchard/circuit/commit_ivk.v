Require Import Garden.Halo2.main.
Require Import Garden.Halo2.Synthesis.
Require Import Garden.Orchard.columns.
Require Garden.Halo2.Gadgets.Utilities.
Require Garden.Halo2.Gadgets.Ecc.chip.constants.

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

Definition synthesize
    : Layouter.t columns unit :=
  Layouter.assign_region "CommitIvk canonicity check" (
    Region.enable_selector Selector.QCommitIvk 0 "").
