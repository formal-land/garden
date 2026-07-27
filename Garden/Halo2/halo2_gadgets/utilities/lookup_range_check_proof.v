Require Import Garden.Halo2.main.
Require Import Garden.Halo2.Synthesis.
Require Import Garden.Halo2.proof.
Require Import Garden.Halo2.lemmas.
Require Garden.Halo2.halo2_gadgets.utilities.lookup_range_check.
Require Import Garden.Field.Field.
Require Import Garden.Plonky3.M.

Import ListNotations.
Global Open Scope Z_scope.

Module ShortLookupBitshift.
  Record t : Set := {
    shifted_word : Z;
  }.

  Definition output {p : Z} `{Prime p}
      (k word inv_two_pow_s : Z)
      : t := {|
    shifted_word := word *F UnOp.from (2 ^ k) *F inv_two_pow_s;
  |}.
End ShortLookupBitshift.

(* Soundness of the [lookup_range_check] table argument (the range-table
   analogue of the Sinsemilla [GeneratorTable.sound]): the [table_idx] column
   holds the row indexes [0 .. nb_table_rows - 1], so an active lookup pins the
   queried word to that interval.  The chip does not load the table itself: in
   the Orchard circuit the [table_idx] contents come from the single
   generator-table load ([load_generator_table]'s first entry is the index
   column), mirroring the Rust circuit where [SinsemillaChip::load] provides
   the shared table and [LookupRangeCheckConfig::load] is never called.  The
   loaded-as-identity fact is therefore a hypothesis here ([Hloaded]),
   discharged at circuit level by [GeneratorTable.loaded] at
   [Lookup.TableIdx]. *)
Module RangeTable.
  Section WithParameters.
    Context {columns : Columns.t} {RegionId : Set} {p : Z} `{Prime p}.

    (* The lookup argument created by [lookup_range_check.configure
       k q_lookup q_running q_bitshift running_sum table_idx]. *)
    Definition argument
        (k : Z)
        (q_lookup q_running : columns.(Columns.Selector))
        (running_sum : columns.(Columns.Advice))
        (table_idx : columns.(Columns.Lookup))
        : LookupArgument.t columns := {|
      LookupArgument.pairs :=
        let two_pow_k := 2 ^ k in
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
    |}.

    (* [configure] emits exactly [argument] as its single lookup. *)
    Lemma configure_lookups_eq
        (k : Z)
        (q_lookup q_running q_bitshift : columns.(Columns.Selector))
        (running_sum : columns.(Columns.Advice))
        (table_idx : columns.(Columns.Lookup)) :
      (𝓒.run_unit
        (Garden.Halo2.halo2_gadgets.utilities.lookup_range_check.configure
          k q_lookup q_running q_bitshift running_sum table_idx)
        ConstraintSystem.empty).(ConstraintSystem.lookups) =
      [argument k q_lookup q_running running_sum table_idx].
    Proof.
      reflexivity.
    Qed.

    (* A [LookupTableLoaded] fact whose values are the index sequence pins the
       table column to the identity on the loaded range. *)
    Lemma loaded_index_table
        (Γ : Assignment.t columns RegionId)
        (table_idx : columns.(Columns.Lookup))
        (n : Z) (default_value : Z)
        (Hfact :
          interpret_fact Γ
            (Fact.LookupTableLoaded table_idx
              (List.map Z.of_nat (List.seq 0%nat (Z.to_nat n)))
              default_value))
        (i : Z) (Hi : 0 <= i < n) :
      Γ.(Assignment.lookup) table_idx i = i.
    Proof.
      cbn [interpret_fact] in Hfact.
      rewrite Hfact by lia.
      unfold value_at_row.
      rewrite nth_map_seq by (apply Z2Nat.inj_lt; lia).
      apply Z2Nat.id; lia.
    Qed.

    (* Soundness of the running-sum branch: on a row with [q_lookup] and
       [q_running] both enabled, the running-sum word
       [z_cur - 2^k * z_next] lies in [0, nb_table_rows).  Instantiated at
       [nb_table_rows = 2^k] this is the ten-bit word range. *)
    Theorem word_sound
        (Γ : Assignment.t columns RegionId)
        (k : Z)
        (q_lookup q_running : columns.(Columns.Selector))
        (running_sum : columns.(Columns.Advice))
        (table_idx : columns.(Columns.Lookup))
        (nb_table_rows : Z)
        (region : RegionId) (row : Z)
        (Hloaded :
          forall i, 0 <= i < nb_table_rows ->
          Γ.(Assignment.lookup) table_idx i = i)
        (Hsel_lookup : Γ.(Assignment.selector) q_lookup region row = 1)
        (Hsel_running : Γ.(Assignment.selector) q_running region row = 1)
        (Hlookup :
          eval_lookup_argument Γ (region, row) nb_table_rows
            (argument k q_lookup q_running running_sum table_idx)) :
      0 <=
        (Γ ⊢ ⟦ Expression.Advice running_sum Rotation.cur ⟧ (region, row)) -F
          (Γ ⊢ ⟦ Expression.Advice running_sum Rotation.next ⟧ (region, row)) *F
          UnOp.from (2 ^ k) <
        nb_table_rows.
    Proof.
      with_strategy opaque [BinOp.add BinOp.sub BinOp.mul UnOp.from]
        cbn in Hlookup.
      destruct Hlookup as (table_row & Hbound & Hpairs).
      unfold argument in Hpairs.
      cbn [LookupArgument.pairs] in Hpairs.
      rewrite Forall_cons_iff in Hpairs.
      destruct Hpairs as [Hpair _].
      with_strategy opaque [BinOp.add BinOp.sub BinOp.mul UnOp.from]
        cbn in Hpair.
      rewrite Hsel_lookup, Hsel_running in Hpair.
      rewrite (Hloaded table_row Hbound) in Hpair.
      assert (Hsub11 : BinOp.sub 1 1 = 0).
      { unfold BinOp.sub. now rewrite Z.sub_diag, Zmod_0_l. }
      rewrite FieldRewrite.from_one in Hpair.
      setoid_rewrite Hsub11 in Hpair.
      setoid_rewrite FieldRewrite.add_zero_right in Hpair.
      repeat setoid_rewrite FieldRewrite.mul_one_left in Hpair.
      repeat setoid_rewrite FieldRewrite.from_from in Hpair.
      repeat setoid_rewrite FieldRewrite.from_sub in Hpair.
      with_strategy opaque [BinOp.add BinOp.sub BinOp.mul UnOp.from] cbn.
      unfold BinOp.sub, BinOp.mul, BinOp.add, UnOp.from in Hpair |- *.
      rewrite Hpair.
      exact Hbound.
    Qed.

    (* Soundness of the short (bitshifted) branch: on a row with [q_lookup]
       enabled and [q_running] disabled, the current cell itself lies in
       [0, nb_table_rows).  The relational fact model only ever pins selectors
       on ([Fact.SelectorOn]), so the [q_running = 0] hypothesis is not
       derivable from circuit synthesis facts; consumers carry it as a named
       short-lookup honesty hypothesis. *)
    Theorem short_word_sound
        (Γ : Assignment.t columns RegionId)
        (k : Z)
        (q_lookup q_running : columns.(Columns.Selector))
        (running_sum : columns.(Columns.Advice))
        (table_idx : columns.(Columns.Lookup))
        (nb_table_rows : Z)
        (region : RegionId) (row : Z)
        (Hloaded :
          forall i, 0 <= i < nb_table_rows ->
          Γ.(Assignment.lookup) table_idx i = i)
        (Hsel_lookup : Γ.(Assignment.selector) q_lookup region row = 1)
        (Hsel_running : Γ.(Assignment.selector) q_running region row = 0)
        (Hlookup :
          eval_lookup_argument Γ (region, row) nb_table_rows
            (argument k q_lookup q_running running_sum table_idx)) :
      0 <=
        (Γ ⊢ ⟦ Expression.Advice running_sum Rotation.cur ⟧ (region, row)) <
        nb_table_rows.
    Proof.
      with_strategy opaque [BinOp.add BinOp.sub BinOp.mul UnOp.from]
        cbn in Hlookup.
      destruct Hlookup as (table_row & Hbound & Hpairs).
      unfold argument in Hpairs.
      cbn [LookupArgument.pairs] in Hpairs.
      rewrite Forall_cons_iff in Hpairs.
      destruct Hpairs as [Hpair _].
      with_strategy opaque [BinOp.add BinOp.sub BinOp.mul UnOp.from]
        cbn in Hpair.
      rewrite Hsel_lookup, Hsel_running in Hpair.
      rewrite (Hloaded table_row Hbound) in Hpair.
      assert (Hcollapse : forall w z : Z,
          UnOp.from 1 *F
            (UnOp.from 0 *F w +F (UnOp.from 1 -F UnOp.from 0) *F UnOp.from z) =
          UnOp.from z)
        by (intros; mod_ring_solve).
      rewrite Hcollapse in Hpair.
      with_strategy opaque [BinOp.add BinOp.sub BinOp.mul UnOp.from] cbn.
      rewrite Hpair.
      exact Hbound.
    Qed.
  End WithParameters.
End RangeTable.
