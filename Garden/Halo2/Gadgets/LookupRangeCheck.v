Require Import Garden.Halo2.main.

Import ListNotations.
Global Open Scope pstring_scope.
Global Open Scope Z_scope.

Definition configure {columns : Columns.t}
    (k : Z)
    (meta : ConstraintSystem.t columns)
    (q_lookup q_running q_bitshift : columns.(Columns.Selector))
    (running_sum : columns.(Columns.Advice))
    (table_idx : columns.(Columns.Fixed))
    : ConstraintSystem.t columns :=
  let two_pow_k := 2 ^ k in
  let meta := ConstraintSystem.create_lookup meta {|
    LookupArgument.pairs :=
      let q_lookup := Expression.Selector q_lookup in
      let q_running := Expression.Selector q_running in
      let z_cur := Expression.Advice running_sum Rotation.cur in
      let one := Expression.Constant 1 in
      let running_sum_lookup :=
        let z_next := Expression.Advice running_sum Rotation.next in
        let running_sum_word := z_cur ➖ (z_next ● two_pow_k) in
        q_running ✖️ running_sum_word in
      let short_lookup :=
        let short_word := z_cur in
        let q_short := one ➖ q_running in
        q_short ✖️ short_word in
      [
        (q_lookup ✖️ (running_sum_lookup ➕ short_lookup), table_idx)
      ];
  |} in
  let meta := ConstraintSystem.create_gate meta {|
    Gate.name := "Short lookup bitshift";
    Gate.constraints :=
      let word := Expression.Advice running_sum Rotation.prev in
      let shifted_word := Expression.Advice running_sum Rotation.cur in
      let inv_two_pow_s := Expression.Advice running_sum Rotation.next in
      Constraints.with_selector q_bitshift [
        (None,
          Constraint.EqualZeroToPrecise
            (word ● two_pow_k ✖️ inv_two_pow_s ➖ shifted_word))
      ];
  |} in
  meta.
