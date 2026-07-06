Require Import Garden.Halo2.main.
Require Import Garden.Halo2.Synthesis.

Import ListNotations.
Global Open Scope pstring_scope.
Global Open Scope Z_scope.

Definition short_lookup_bitshift_gate {columns : Columns.t}
    (k : Z)
    (q_bitshift : columns.(Columns.Selector))
    (running_sum : columns.(Columns.Advice))
    : Gate.t columns := {|
  Gate.name := "Short lookup bitshift";
  Gate.constraints :=
    let two_pow_k := 2 ^ k in
    let word := Expression.Advice running_sum Rotation.prev in
    let shifted_word := Expression.Advice running_sum Rotation.cur in
    let inv_two_pow_s := Expression.Advice running_sum Rotation.next in
    Constraints.with_selector q_bitshift [
      (None,
        Constraint.Equal
          (word ● two_pow_k ✖️ inv_two_pow_s)
          shifted_word)
    ];
|}.

Definition configure {columns : Columns.t}
    (k : Z)
    (q_lookup q_running q_bitshift : columns.(Columns.Selector))
    (running_sum : columns.(Columns.Advice))
    (table_idx : columns.(Columns.Lookup))
    : 𝓒 columns unit :=
  let two_pow_k := 2 ^ k in
  do🞵 𝓒.CreateLookup {|
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
  do🞵 𝓒.CreateGate (short_lookup_bitshift_gate k q_bitshift running_sum) in
  return🞵 tt.

Definition synthesize {columns : Columns.t} {RegionId : Set}
    : 𝓛 columns RegionId unit :=
  return🞵 tt.

Definition synthesize_short {columns : Columns.t} {RegionId : Set}
    (region : RegionId)
    (name : string)
    (q_lookup q_bitshift : columns.(Columns.Selector))
    (running_sum : columns.(Columns.Advice))
    (inv_two_pow_s : Z)
    : 𝓛 columns RegionId (Cell.t columns RegionId) :=
  𝓛.AddRegion region name (fun region =>
    let element := Cell.advice region running_sum 0 in
    do🞵 𝓡.EnableSelector q_lookup 0 "" in
    do🞵 𝓡.EnableSelector q_lookup 1 "" in
    do🞵 𝓡.EnableSelector q_bitshift 1 "" in
    do🞵
      𝓡.ConstrainConstant
        (Cell.advice region running_sum 2)
        inv_two_pow_s in
    return🞵 element).
