Require Import Garden.Plonky3.M.
Require Import Garden.Plonky3.MExpr.
Require Import Garden.OpenVM.primitives.bitwise_op_lookup.
Require Import Garden.OpenVM.primitives.encoder.
Require Import Garden.OpenVM.primitives.utils.
Require Import Garden.OpenVM.Sha256.columns.
Require Import Garden.OpenVM.Sha256.utils.

(* We hardcode this value *)
Definition row_idx_encoder: Encoder.t := {|
  Encoder.var_cnt := 5;
  Encoder.flag_cnt := 18;
  Encoder.max_flag_degree := 2;
  Encoder.pts := [
    [0; 0; 0; 0; 0];
    [0; 0; 0; 0; 1];
    [0; 0; 0; 0; 2];
    [0; 0; 0; 1; 0];
    [0; 0; 0; 1; 1];
    [0; 0; 0; 2; 0];
    [0; 0; 1; 0; 0];
    [0; 0; 1; 0; 1];
    [0; 0; 1; 1; 0];
    [0; 0; 2; 0; 0];
    [0; 1; 0; 0; 0];
    [0; 1; 0; 0; 1];
    [0; 1; 0; 1; 0];
    [0; 1; 1; 0; 0];
    [0; 2; 0; 0; 0];
    [1; 0; 0; 0; 0];
    [1; 0; 0; 0; 1];
    [1; 0; 0; 1; 0];
    [1; 0; 1; 0; 0];
    [1; 1; 0; 0; 0];
    [2; 0; 0; 0; 0]
  ];
  Encoder.reserve_invalid := false;
|}.

(*
pub struct Sha256Air {
    pub bitwise_lookup_bus: BitwiseOperationLookupBus,
    pub row_idx_encoder: Encoder,
    bus: PermutationCheckBus,
}
*)
Module Sha256Air.
  Record t : Set := {
    bitwise_lookup_bus : BitwiseOperationLookupBus.t;
    row_idx_encoder : Encoder.t;
    bus : Z;
  }.
End Sha256Air.

(*
fn eval_row<AB: InteractionBuilder>(&self, builder: &mut AB, start_col: usize)
where
    AB: LoggingAirBuilder,
{
    builder.log_in_constraints("eval_row");
    let main = builder.main();
    let local = main.row_slice(0);

    // Doesn't matter which column struct we use here as we are only interested in the common
    // columns
    let local_cols: &Sha256DigestCols<AB::Var> =
        local[start_col..start_col + SHA256_DIGEST_WIDTH].borrow();
    let flags = &local_cols.flags;
    builder.log_in_constraints("eval_row::flags");
    builder.assert_bool(flags.is_round_row);
    builder.assert_bool(flags.is_first_4_rows);
    builder.assert_bool(flags.is_digest_row);
    builder.assert_bool(flags.is_round_row + flags.is_digest_row);
    builder.assert_bool(flags.is_last_block);

    // Constrain a, e, being composed of bits: we make sure a and e are always in the same place
    // in the trace matrix Note: this has to be true for every row, even padding rows
    builder.log_in_constraints("eval_row::hash");
    for i in 0..SHA256_ROUNDS_PER_ROW {
        for j in 0..SHA256_WORD_BITS {
            builder.assert_bool(local_cols.hash.a[i][j]);
            builder.assert_bool(local_cols.hash.e[i][j]);
        }
    }
}
*)
Definition eval_row (start_col : Z) (local_cols : Sha256DigestCols.t Var.t) : MExpr.t unit :=
  msg! "eval_row" in
  let flags := local_cols.(Sha256DigestCols.flags) in
  msg! "eval_row::flags" in
  let! _ := MExpr.assert_bool (Expr.Var flags.(Sha256FlagsCols.is_round_row)) in
  let! _ := MExpr.assert_bool (Expr.Var flags.(Sha256FlagsCols.is_first_4_rows)) in
  let! _ := MExpr.assert_bool (Expr.Var flags.(Sha256FlagsCols.is_digest_row)) in
  let! _ := MExpr.assert_bool (
    Expr.Add
      (Expr.Var flags.(Sha256FlagsCols.is_round_row))
      (Expr.Var flags.(Sha256FlagsCols.is_digest_row))
  ) in
  let! _ := MExpr.assert_bool (Expr.Var flags.(Sha256FlagsCols.is_last_block)) in
  msg! "eval_row::hash" in
  let! _ := for_in_zero_to_n SHA256_ROUNDS_PER_ROW (fun i =>
    for_in_zero_to_n SHA256_WORD_BITS (fun j =>
      let! _ := MExpr.assert_bool (Expr.Var local_cols.(Sha256DigestCols.hash).(Sha256WorkVarsCols.a).[i].[j]) in
      let! _ := MExpr.assert_bool (Expr.Var local_cols.(Sha256DigestCols.hash).(Sha256WorkVarsCols.e).[i].[j]) in
      MExpr.pure tt
    )
  ) in
  MExpr.pure tt.

Definition print_eval_row : string :=
  let start_col := 0 in
  let local_cols : Sha256DigestCols.t Var.t :=
    MGenerate.eval MGenerate.generate in
  ToRocq.cats [
    ToRocq.endl;
    ToRocq.to_rocq (eval_row start_col local_cols) 0;
    ToRocq.endl
  ].

(*
fn eval_message_schedule<AB: InteractionBuilder>(
    &self,
    builder: &mut AB,
    local: &Sha256RoundCols<AB::Var>,
    next: &Sha256RoundCols<AB::Var>,
)
*)
Definition eval_message_schedule
    (local_cols next_cols : Sha256RoundCols.t Var.t) :
    MExpr.t unit :=
  msg! "eval_message_schedule" in
  (*
    let w = [local.message_schedule.w, next.message_schedule.w].concat();
  *)
  let w := Array.concat
    local_cols.(Sha256RoundCols.message_schedule).(Sha256MessageScheduleCols.w)
    next_cols.(Sha256RoundCols.message_schedule).(Sha256MessageScheduleCols.w)
  in

  (*
    for i in 0..SHA256_ROUNDS_PER_ROW - 1 {
        // here we constrain the w_3 of the i_th word of the next row
        // w_3 of next is w[i+4-3] = w[i+1]
        let w_3 = w[i + 1].map(|x| x.into());
        let expected_w_3 = next.schedule_helper.w_3[i];
        for j in 0..SHA256_WORD_U16S {
            let w_3_limb = compose::<AB::Expr>(&w_3[j * 16..(j + 1) * 16], 1);
            builder
                .when(local.flags.is_round_row)
                .assert_eq(w_3_limb, expected_w_3[j].into());
        }
    }
  *)
  msg! "eval_message_schedule::first_loop" in
  let! _ := for_in_zero_to_n (SHA256_ROUNDS_PER_ROW - 1) (fun i =>
    let w_3 := Array.get w (i + 1) in
    let expected_w_3 := next_cols.(Sha256RoundCols.schedule_helper).(Sha256MessageHelperCols.w_3).[i] in
    MExpr.for_in_zero_to_n SHA256_WORD_U16S (fun j =>
      let w_3_limb := utils.compose (Array.slice_range (Array.map Expr.Var w_3) (j * 16) ((j + 1) * 16)) 1 in
      let! _ :=
        MExpr.when local_cols.(Sha256RoundCols.flags).(Sha256FlagsCols.is_round_row) (
        MExpr.assert_eq w_3_limb expected_w_3.[j]
      ) in
      MExpr.pure tt
    )
  ) in

  (*
    for i in 0..SHA256_ROUNDS_PER_ROW {
        // w_idx
        let w_idx = w[i].map(|x| x.into());
        // sig_0(w_{idx+1})
        let sig_w = small_sig0_field::<AB::Expr>(&w[i + 1]);
        for j in 0..SHA256_WORD_U16S {
            let w_idx_limb = compose::<AB::Expr>(&w_idx[j * 16..(j + 1) * 16], 1);
            let sig_w_limb = compose::<AB::Expr>(&sig_w[j * 16..(j + 1) * 16], 1);

            // We would like to constrain this only on rows 0..16, but we can't do a conditional
            // check because the degree is already 3. So we must fill in
            // `intermed_4` with dummy values on rows 0 and 16 to ensure the constraint holds on
            // these rows.
            builder.when_transition().assert_eq(
                next.schedule_helper.intermed_4[i][j],
                w_idx_limb + sig_w_limb,
            );
        }
    }
  *)
  msg! "eval_message_schedule::second_loop" in
  let! _ :=
    MExpr.for_in_zero_to_n SHA256_ROUNDS_PER_ROW (fun i =>
      let w_idx := w.[i] in
      let sig_w := utils.small_sig0_field (Array.map Expr.Var w.[i + 1]) in
      MExpr.for_in_zero_to_n SHA256_WORD_U16S (fun j =>
        let w_idx_limb := utils.compose (Array.slice_range (Array.map Expr.Var w_idx) (j * 16) ((j + 1) * 16)) 1 in
        let sig_w_limb := utils.compose (Array.slice_range sig_w (j * 16) ((j + 1) * 16)) 1 in
        let! _ :=
          MExpr.when Expr.IsTransition (
            MExpr.assert_eq
              next_cols.(Sha256RoundCols.schedule_helper).(Sha256MessageHelperCols.intermed_4).[i].[j]
              (w_idx_limb +E sig_w_limb)
          ) in
        MExpr.pure tt
      )
    ) in

  (*
    for i in 0..SHA256_ROUNDS_PER_ROW {
        // Note, here by w_{t} we mean the i_th word of the `next` row
        // w_{t-7}
        let w_7 = if i < 3 {
            local.schedule_helper.w_3[i].map(|x| x.into())
        } else {
            let w_3 = w[i - 3].map(|x| x.into());
            array::from_fn(|j| compose::<AB::Expr>(&w_3[j * 16..(j + 1) * 16], 1))
        };
        // sig_0(w_{t-15}) + w_{t-16}
        let intermed_16 = local.schedule_helper.intermed_12[i].map(|x| x.into());

        let carries = array::from_fn(|j| {
            next.message_schedule.carry_or_buffer[i][j * 2]
                + AB::Expr::TWO * next.message_schedule.carry_or_buffer[i][j * 2 + 1]
        });

        // Constrain `W_{idx} = sig_1(W_{idx-2}) + W_{idx-7} + sig_0(W_{idx-15}) + W_{idx-16}`
        // We would like to constrain this only on rows 4..16, but we can't do a conditional
        // check because the degree of sum is already 3 So we must fill in
        // `intermed_12` with dummy values on rows 0..3 and 15 and 16 to ensure the constraint
        // holds on rows 0..4 and 16. Note that the dummy value goes in the previous
        // row to make the current row's constraint hold.
        constraint_word_addition(
            // Note: here we can't do a conditional check because the degree of sum is already
            // 3
            &mut builder.when_transition(),
            &[&small_sig1_field::<AB::Expr>(&w[i + 2])],
            &[&w_7, &intermed_16],
            &w[i + 4],
            &carries,
        );

        for j in 0..SHA256_WORD_U16S {
            // When on rows 4..16 message schedule carries should be 0 or 1
            let is_row_4_15 = next.flags.is_round_row - next.flags.is_first_4_rows;
            builder
                .when(is_row_4_15.clone())
                .assert_bool(next.message_schedule.carry_or_buffer[i][j * 2]);
            builder
                .when(is_row_4_15)
                .assert_bool(next.message_schedule.carry_or_buffer[i][j * 2 + 1]);
        }
        // Constrain w being composed of bits
        for j in 0..SHA256_WORD_BITS {
            builder
                .when(next.flags.is_round_row)
                .assert_bool(next.message_schedule.w[i][j]);
        }
    }
  *)
  msg! "eval_message_schedule::third_loop" in
  let! _ :=
    MExpr.for_in_zero_to_n SHA256_ROUNDS_PER_ROW (fun i =>
      let w_7 :=
        if i <? 3 then
          Array.map Expr.Var local_cols.(Sha256RoundCols.schedule_helper).(Sha256MessageHelperCols.w_3).[i]
        else
          let w_3 := w.[i - 3] in
          {| Array.get j := utils.compose (Array.slice_range (Array.map Expr.Var w_3) (j * 16) ((j + 1) * 16)) 1 |}
      in
      let intermed_16 := local_cols.(Sha256RoundCols.schedule_helper).(Sha256MessageHelperCols.intermed_12).[i] in
      let carries := {| Array.get j :=
        next_cols.(Sha256RoundCols.message_schedule).(Sha256MessageScheduleCols.carry_or_buffer).[i].[j * 2] +E
        (Expr.TWO *E next_cols.(Sha256RoundCols.message_schedule).(Sha256MessageScheduleCols.carry_or_buffer).[i].[j * 2 + 1])
      |} in
      let! _ :=
        MExpr.when Expr.IsTransition (
        utils.constrain_word_addition
          [utils.small_sig1_field (Array.map Expr.Var w.[i + 2])]
          [w_7; Array.map Expr.Var intermed_16]
          (Array.map Expr.Var w.[i + 4])
          carries
        ) in
      let! _ :=
        MExpr.for_in_zero_to_n SHA256_WORD_U16S (fun j =>
          let is_row_4_15 :=
            next_cols.(Sha256RoundCols.flags).(Sha256FlagsCols.is_round_row) -E
            next_cols.(Sha256RoundCols.flags).(Sha256FlagsCols.is_first_4_rows) in
          let! _ :=
            MExpr.when is_row_4_15 (
            MExpr.assert_bool (next_cols.(Sha256RoundCols.message_schedule).(Sha256MessageScheduleCols.carry_or_buffer).[i].[j * 2])
          ) in
          let! _ :=
            MExpr.when is_row_4_15 (
            MExpr.assert_bool (next_cols.(Sha256RoundCols.message_schedule).(Sha256MessageScheduleCols.carry_or_buffer).[i].[j * 2 + 1])
          ) in
          MExpr.pure tt
        ) in
      let! _ :=
        MExpr.for_in_zero_to_n SHA256_WORD_BITS (fun j =>
          MExpr.when next_cols.(Sha256RoundCols.flags).(Sha256FlagsCols.is_round_row) (
          MExpr.assert_bool (next_cols.(Sha256RoundCols.message_schedule).(Sha256MessageScheduleCols.w).[i].[j])
        )
      ) in
      MExpr.pure tt
    ) in
  MExpr.pure tt.

(*
fn eval_work_vars<AB: InteractionBuilder>(
    &self,
    builder: &mut AB,
    local: &Sha256RoundCols<AB::Var>,
    next: &Sha256RoundCols<AB::Var>,
)
*)
Definition eval_work_vars
    (self : Sha256Air.t)
    (local_cols next_cols : Sha256RoundCols.t Var.t) :
    MExpr.t unit :=
  msg! "eval_work_vars" in
  (*
    let a = [local.work_vars.a, next.work_vars.a].concat();
    let e = [local.work_vars.e, next.work_vars.e].concat();
    for i in 0..SHA256_ROUNDS_PER_ROW {
        for j in 0..SHA256_WORD_U16S {
            // Although we need carry_a <= 6 and carry_e <= 5, constraining carry_a, carry_e in
            // [0, 2^8) is enough to prevent overflow and ensure the soundness
            // of the addition we want to check
            self.bitwise_lookup_bus
                .send_range(local.work_vars.carry_a[i][j], local.work_vars.carry_e[i][j])
                .eval(builder, local.flags.is_round_row);
        }
  *)
  msg! "eval_work_vars::first_loop" in
  let a := Array.concat
    local_cols.(Sha256RoundCols.work_vars).(Sha256WorkVarsCols.a)
    next_cols.(Sha256RoundCols.work_vars).(Sha256WorkVarsCols.a)
  in
  let e := Array.concat
    local_cols.(Sha256RoundCols.work_vars).(Sha256WorkVarsCols.e)
    next_cols.(Sha256RoundCols.work_vars).(Sha256WorkVarsCols.e) in
  let! _ :=
    MExpr.for_in_zero_to_n SHA256_ROUNDS_PER_ROW (fun i =>
      MExpr.for_in_zero_to_n SHA256_WORD_U16S (fun j =>
        let interaction :=
          Impl_BitwiseOperationLookupBus.send_range
            self.(Sha256Air.bitwise_lookup_bus)
            (local_cols.(Sha256RoundCols.work_vars).(Sha256WorkVarsCols.carry_a).[i].[j])
            (local_cols.(Sha256RoundCols.work_vars).(Sha256WorkVarsCols.carry_e).[i].[j]) in
        Impl_BitwiseOperationLookupBusInteraction.eval
          interaction
          local_cols.(Sha256RoundCols.flags).(Sha256FlagsCols.is_round_row)
      )
    ) in
  MExpr.pure tt.

(*
fn eval_digest_row<AB: InteractionBuilder>(
    &self,
    builder: &mut AB,
    local: &Sha256RoundCols<AB::Var>,
    next: &Sha256DigestCols<AB::Var>,
)
*)
Definition eval_digest_row
    (local_cols : Sha256RoundCols.t Var.t)
    (next_cols : Sha256DigestCols.t Var.t) :
    MExpr.t unit :=
  msg! "eval_digest_row" in
  (*
    for i in 0..SHA256_ROUNDS_PER_ROW {
        let a = next.hash.a[i].map(|x| x.into());
        let e = next.hash.e[i].map(|x| x.into());
        for j in 0..SHA256_WORD_U16S {
            let a_limb = compose::<AB::Expr>(&a[j * 16..(j + 1) * 16], 1);
            let e_limb = compose::<AB::Expr>(&e[j * 16..(j + 1) * 16], 1);

            // If it is a padding row or the last row of a message, the `hash` should be the
            // [SHA256_H]
            builder
                .when(
                    next.flags.is_padding_row()
                        + next.flags.is_last_block * next.flags.is_digest_row,
                )
                .assert_eq(
                    a_limb,
                    AB::Expr::from_canonical_u32(
                        u32_into_limbs::<2>(SHA256_H[SHA256_ROUNDS_PER_ROW - i - 1])[j],
                    ),
                );

            builder
                .when(
                    next.flags.is_padding_row()
                        + next.flags.is_last_block * next.flags.is_digest_row,
                )
                .assert_eq(
                    e_limb,
                    AB::Expr::from_canonical_u32(
                        u32_into_limbs::<2>(SHA256_H[SHA256_ROUNDS_PER_ROW - i + 3])[j],
                    ),
                );
        }
    }
  *)
  msg! "eval_digest_row::first_loop" in
  let! _ :=
    MExpr.for_in_zero_to_n SHA256_ROUNDS_PER_ROW (fun i =>
      let a := next_cols.(Sha256DigestCols.hash).(Sha256WorkVarsCols.a).[i] in
      let e := next_cols.(Sha256DigestCols.hash).(Sha256WorkVarsCols.e).[i] in
      MExpr.for_in_zero_to_n SHA256_WORD_U16S (fun j =>
        let a_limb := utils.compose (Array.slice_range (Array.map Expr.Var a) (j * 16) ((j + 1) * 16)) 1 in
        let e_limb := utils.compose (Array.slice_range (Array.map Expr.Var e) (j * 16) ((j + 1) * 16)) 1 in
        let! _ :=
          MExpr.when (
            Impl_Sha256FlagsCols.is_padding_row next_cols.(Sha256DigestCols.flags)
            +E next_cols.(Sha256DigestCols.flags).(Sha256FlagsCols.is_last_block)
            *E next_cols.(Sha256DigestCols.flags).(Sha256FlagsCols.is_digest_row)
          ) (
            MExpr.assert_eq
              a_limb
              (Expr.from_canonical_u32 (utils.u32_into_limbs 2 SHA256_H.[SHA256_ROUNDS_PER_ROW - i - 1]).[j])
          ) in
        let! _ :=
          MExpr.when (
            Impl_Sha256FlagsCols.is_padding_row next_cols.(Sha256DigestCols.flags)
            +E next_cols.(Sha256DigestCols.flags).(Sha256FlagsCols.is_last_block)
            *E next_cols.(Sha256DigestCols.flags).(Sha256FlagsCols.is_digest_row)
          ) (
            MExpr.assert_eq
              e_limb
              (Expr.from_canonical_u32 (utils.u32_into_limbs 2 SHA256_H.[SHA256_ROUNDS_PER_ROW - i + 3]).[j])
          ) in
        MExpr.pure tt
      )
    ) in

  (*
    for i in 0..SHA256_ROUNDS_PER_ROW {
        let prev_a = next.hash.a[i].map(|x| x.into());
        let prev_e = next.hash.e[i].map(|x| x.into());
        let cur_a = next.final_hash[SHA256_ROUNDS_PER_ROW - i - 1].map(|x| x.into());

        let cur_e = next.final_hash[SHA256_ROUNDS_PER_ROW - i + 3].map(|x| x.into());
        for j in 0..SHA256_WORD_U8S {
            let prev_a_limb = compose::<AB::Expr>(&prev_a[j * 8..(j + 1) * 8], 1);
            let prev_e_limb = compose::<AB::Expr>(&prev_e[j * 8..(j + 1) * 8], 1);

            builder
                .when(not(next.flags.is_last_block) * next.flags.is_digest_row)
                .assert_eq(prev_a_limb, cur_a[j].clone());

            builder
                .when(not(next.flags.is_last_block) * next.flags.is_digest_row)
                .assert_eq(prev_e_limb, cur_e[j].clone());
        }
    }
    *)
  msg! "eval_digest_row::second_loop" in
  let! _ :=
    MExpr.for_in_zero_to_n SHA256_ROUNDS_PER_ROW (fun i =>
      let prev_a := next_cols.(Sha256DigestCols.hash).(Sha256WorkVarsCols.a).[i] in
      let prev_e := next_cols.(Sha256DigestCols.hash).(Sha256WorkVarsCols.e).[i] in
      let cur_a := next_cols.(Sha256DigestCols.final_hash).[SHA256_ROUNDS_PER_ROW - i - 1] in
      let cur_e := next_cols.(Sha256DigestCols.final_hash).[SHA256_ROUNDS_PER_ROW - i + 3] in
      MExpr.for_in_zero_to_n SHA256_WORD_U8S (fun j =>
        let prev_a_limb := utils.compose (Array.slice_range (Array.map Expr.Var prev_a) (j * 8) ((j + 1) * 8)) 1 in
        let prev_e_limb := utils.compose (Array.slice_range (Array.map Expr.Var prev_e) (j * 8) ((j + 1) * 8)) 1 in
        let! _ :=
          MExpr.when (
            Expr.not next_cols.(Sha256DigestCols.flags).(Sha256FlagsCols.is_last_block) *E
            next_cols.(Sha256DigestCols.flags).(Sha256FlagsCols.is_digest_row)
        ) (
          MExpr.assert_eq
            prev_a_limb
            (Array.map Expr.Var cur_a).[j]
        ) in
        let! _ :=
          MExpr.when (
            Expr.not next_cols.(Sha256DigestCols.flags).(Sha256FlagsCols.is_last_block) *E
            next_cols.(Sha256DigestCols.flags).(Sha256FlagsCols.is_digest_row)
        ) (
          MExpr.assert_eq
            prev_e_limb
            (Array.map Expr.Var cur_e).[j]
        ) in
        MExpr.pure tt
      )
    ) in

  (*
    for i in 0..SHA256_HASH_WORDS {
        let mut carry = AB::Expr::ZERO;
        for j in 0..SHA256_WORD_U16S {
            let work_var_limb = if i < SHA256_ROUNDS_PER_ROW {
                compose::<AB::Expr>(
                    &local.work_vars.a[SHA256_ROUNDS_PER_ROW - 1 - i][j * 16..(j + 1) * 16],
                    1,
                )
            } else {
                compose::<AB::Expr>(
                    &local.work_vars.e[SHA256_ROUNDS_PER_ROW + 3 - i][j * 16..(j + 1) * 16],
                    1,
                )
            };
            let final_hash_limb =
                compose::<AB::Expr>(&next.final_hash[i][j * 2..(j + 1) * 2], 8);

            carry = AB::Expr::from(AB::F::from_canonical_u32(1 << 16).inverse())
                * (next.prev_hash[i][j] + work_var_limb + carry - final_hash_limb);
            builder
                .when(next.flags.is_digest_row)
                .assert_bool(carry.clone());
        }
        // constrain the final hash limbs two at a time since we can do two checks per
        // interaction
        for chunk in next.final_hash[i].chunks(2) {
            self.bitwise_lookup_bus
                .send_range(chunk[0], chunk[1])
                .eval(builder, next.flags.is_digest_row);
        }
    }
  *)
  msg! "eval_digest_row::third_loop" in
  let! _ :=
    MExpr.for_in_zero_to_n SHA256_HASH_WORDS (fun i =>
      let carry : Expr.t := Expr.ZERO in
      let! _ :=
        List.fold_left (fun carry j =>
          let j := Z.of_nat j in
          let work_var_limb :=
            if i <? SHA256_ROUNDS_PER_ROW then
              utils.compose (Array.slice_range (Array.map Expr.Var local_cols.(Sha256RoundCols.work_vars).(Sha256WorkVarsCols.a).[SHA256_ROUNDS_PER_ROW - i - 1]) (j * 16) ((j + 1) * 16)) 1
            else
              utils.compose (Array.slice_range (Array.map Expr.Var local_cols.(Sha256RoundCols.work_vars).(Sha256WorkVarsCols.e).[SHA256_ROUNDS_PER_ROW + 3 - i]) (j * 16) ((j + 1) * 16)) 1 in
          let final_hash_limb :=
            utils.compose (Array.slice_range (Array.map Expr.Var next_cols.(Sha256DigestCols.final_hash).[i]) (j * 2) ((j + 1) * 2)) 8 in
          let carry :=
            (* TODO: have the expression with the inverse *)
            (* Expr.Constant (Field.inverse (Field.from_canonical_u32 (2 ^ 16))) *E *)
            Expr.constant 18446462594437939201 *E
            (next_cols.(Sha256DigestCols.prev_hash).[i].[j] +E work_var_limb +E carry -E final_hash_limb) in
          let! _ :=
            MExpr.when (next_cols.(Sha256DigestCols.flags).(Sha256FlagsCols.is_digest_row)) (
            MExpr.assert_bool carry
          ) in
          MExpr.pure carry
        )
        carry
        (List.seq 0 (Z.to_nat SHA256_WORD_U16S)) in
      let! _ :=
        let chunks :=
          Array.to_list next_cols.(Sha256DigestCols.final_hash).[i] in
        MExpr.List.iter (fun j =>
          (* TODO interaction *)
          MExpr.pure tt
        ) chunks in
      MExpr.pure tt
    ) in
  MExpr.pure tt.

(* fn eval_transitions<AB: InteractionBuilder>(&self, builder: &mut AB, start_col: usize) *)
Definition eval_transitions
    (self : Sha256Air.t)
    (start_col : Z)
    (round_local_cols round_next_cols : Sha256RoundCols.t Var.t)
    (digest_local_cols digest_next_cols : Sha256DigestCols.t Var.t) :
    MExpr.t unit :=
  (*
    let main = builder.main();
    let local = main.row_slice(0);
    let next = main.row_slice(1);

    // Doesn't matter what column structs we use here
    let local_cols: &Sha256RoundCols<AB::Var> =
        local[start_col..start_col + SHA256_ROUND_WIDTH].borrow();
    let next_cols: &Sha256RoundCols<AB::Var> =
        next[start_col..start_col + SHA256_ROUND_WIDTH].borrow();

    let local_is_padding_row = local_cols.flags.is_padding_row();
    // Note that there will always be a padding row in the trace since the unpadded height is a
    // multiple of 17. So the next row is padding iff the current block is the last
    // block in the trace.
    let next_is_padding_row = next_cols.flags.is_padding_row();
  *)
  msg! "eval_transitions" in
  let local_cols := round_local_cols in
  let next_cols := round_next_cols in
  let local_is_padding_row := Impl_Sha256FlagsCols.is_padding_row local_cols.(Sha256RoundCols.flags) in
  let next_is_padding_row := Impl_Sha256FlagsCols.is_padding_row next_cols.(Sha256RoundCols.flags) in

  (*
    // We check that the very last block has `is_last_block` set to true, which guarantees that
    // there is at least one complete message. If other digest rows have `is_last_block` set to
    // true, then the trace will be interpreted as containing multiple messages.
    builder
        .when(next_is_padding_row.clone())
        .when(local_cols.flags.is_digest_row)
        .assert_one(local_cols.flags.is_last_block);
    // If we are in a round row, the next row cannot be a padding row
    builder
        .when(local_cols.flags.is_round_row)
        .assert_zero(next_is_padding_row.clone());
    // The first row must be a round row
    builder
        .when_first_row()
        .assert_one(local_cols.flags.is_round_row);
    // If we are in a padding row, the next row must also be a padding row
    builder
        .when_transition()
        .when(local_is_padding_row.clone())
        .assert_one(next_is_padding_row.clone());
    // If we are in a digest row, the next row cannot be a digest row
    builder
        .when(local_cols.flags.is_digest_row)
        .assert_zero(next_cols.flags.is_digest_row);
  *)
  msg! "eval_transitions::first_block" in
  let! _ :=
    MExpr.when next_is_padding_row (
    MExpr.when local_cols.(Sha256RoundCols.flags).(Sha256FlagsCols.is_digest_row) (
    MExpr.assert_one local_cols.(Sha256RoundCols.flags).(Sha256FlagsCols.is_last_block)
    )) in
  let! _ :=
    MExpr.when local_cols.(Sha256RoundCols.flags).(Sha256FlagsCols.is_round_row) (
    MExpr.assert_zero next_is_padding_row
    ) in
  let! _ :=
    MExpr.when Expr.IsFirstRow (
    MExpr.assert_one local_cols.(Sha256RoundCols.flags).(Sha256FlagsCols.is_round_row)
    ) in
  let! _ :=
    MExpr.when Expr.IsTransition (
    MExpr.when local_is_padding_row (
    MExpr.assert_one next_is_padding_row
    )) in
  let! _ :=
    MExpr.when local_cols.(Sha256RoundCols.flags).(Sha256FlagsCols.is_digest_row) (
    MExpr.assert_zero next_cols.(Sha256RoundCols.flags).(Sha256FlagsCols.is_digest_row)
    ) in

  (*
    // Constrain how much the row index changes by
    // round->round: 1
    // round->digest: 1
    // digest->round: -16
    // digest->padding: 1
    // padding->padding: 0
    // Other transitions are not allowed by the above constraints
    let delta = local_cols.flags.is_round_row * AB::Expr::ONE
        + local_cols.flags.is_digest_row
            * next_cols.flags.is_round_row
            * AB::Expr::from_canonical_u32(16)
            * AB::Expr::NEG_ONE
        + local_cols.flags.is_digest_row * next_is_padding_row.clone() * AB::Expr::ONE;
  *)
  let delta : Expr.t :=
    local_cols.(Sha256RoundCols.flags).(Sha256FlagsCols.is_round_row) *E Expr.ONE
      +E local_cols.(Sha256RoundCols.flags).(Sha256FlagsCols.is_digest_row)
        *E next_cols.(Sha256RoundCols.flags).(Sha256FlagsCols.is_round_row)
        *E Expr.from_canonical_u32 16
        *E Expr.NEG_ONE
      +E local_cols.(Sha256RoundCols.flags).(Sha256FlagsCols.is_digest_row)
        *E next_is_padding_row
        *E Expr.ONE in

  (*
    // Constrain the global block index
    // We set the global block index to 0 for padding rows
    // Starting with 1 so it is not the same as the padding rows

    // Global block index is 1 on first row
    builder
        .when_first_row()
        .assert_one(local_cols.flags.global_block_idx);
  *)
  msg! "eval_transitions::second_block" in
  let! _ :=
    MExpr.when Expr.IsFirstRow (
    MExpr.assert_one local_cols.(Sha256RoundCols.flags).(Sha256FlagsCols.global_block_idx)
    ) in

  (*
    // Global block index is constant on all rows in a block
    builder.when(local_cols.flags.is_round_row).assert_eq(
        local_cols.flags.global_block_idx,
        next_cols.flags.global_block_idx,
    );
    // Global block index increases by 1 between blocks
    builder
        .when_transition()
        .when(local_cols.flags.is_digest_row)
        .when(next_cols.flags.is_round_row)
        .assert_eq(
            local_cols.flags.global_block_idx + AB::Expr::ONE,
            next_cols.flags.global_block_idx,
        );
    // Global block index is 0 on padding rows
    builder
        .when(local_is_padding_row.clone())
        .assert_zero(local_cols.flags.global_block_idx);
  *)
  let! _ :=
    MExpr.when local_cols.(Sha256RoundCols.flags).(Sha256FlagsCols.is_round_row) (
    MExpr.assert_eq local_cols.(Sha256RoundCols.flags).(Sha256FlagsCols.global_block_idx)
      next_cols.(Sha256RoundCols.flags).(Sha256FlagsCols.global_block_idx)
    ) in
  let! _ :=
    MExpr.when Expr.IsTransition (
    MExpr.when local_cols.(Sha256RoundCols.flags).(Sha256FlagsCols.is_digest_row) (
    MExpr.when next_cols.(Sha256RoundCols.flags).(Sha256FlagsCols.is_round_row) (
    MExpr.assert_eq
      (Expr.Add local_cols.(Sha256RoundCols.flags).(Sha256FlagsCols.global_block_idx) Expr.ONE)
      next_cols.(Sha256RoundCols.flags).(Sha256FlagsCols.global_block_idx)
    ))) in
  let! _ :=
    MExpr.when local_is_padding_row (
    MExpr.assert_zero local_cols.(Sha256RoundCols.flags).(Sha256FlagsCols.global_block_idx)
    ) in

  (*
    // Constrain the local block index
    // We set the local block index to 0 for padding rows

    // Local block index is constant on all rows in a block
    // and its value on padding rows is equal to its value on the first block
    builder.when(not(local_cols.flags.is_digest_row)).assert_eq(
        local_cols.flags.local_block_idx,
        next_cols.flags.local_block_idx,
    );
    // Local block index increases by 1 between blocks in the same message
    builder
        .when(local_cols.flags.is_digest_row)
        .when(not(local_cols.flags.is_last_block))
        .assert_eq(
            local_cols.flags.local_block_idx + AB::Expr::ONE,
            next_cols.flags.local_block_idx,
        );
    // Local block index is 0 on padding rows
    // Combined with the above, this means that the local block index is 0 in the first block
    builder
        .when(local_cols.flags.is_digest_row)
        .when(local_cols.flags.is_last_block)
        .assert_zero(next_cols.flags.local_block_idx);
    *)
  msg! "eval_transitions::third_block" in
  let! _ :=
    MExpr.when (Expr.not local_cols.(Sha256RoundCols.flags).(Sha256FlagsCols.is_digest_row)) (
    MExpr.assert_eq
      local_cols.(Sha256RoundCols.flags).(Sha256FlagsCols.local_block_idx)
      next_cols.(Sha256RoundCols.flags).(Sha256FlagsCols.local_block_idx)
    ) in
  let! _ :=
    MExpr.when local_cols.(Sha256RoundCols.flags).(Sha256FlagsCols.is_digest_row) (
    MExpr.when (Expr.not local_cols.(Sha256RoundCols.flags).(Sha256FlagsCols.is_last_block)) (
    MExpr.assert_eq
      (local_cols.(Sha256RoundCols.flags).(Sha256FlagsCols.local_block_idx) +E Expr.ONE)
      next_cols.(Sha256RoundCols.flags).(Sha256FlagsCols.local_block_idx)
    )) in
  let! _ :=
    MExpr.when local_cols.(Sha256RoundCols.flags).(Sha256FlagsCols.is_digest_row) (
    MExpr.when local_cols.(Sha256RoundCols.flags).(Sha256FlagsCols.is_last_block) (
    MExpr.assert_zero next_cols.(Sha256RoundCols.flags).(Sha256FlagsCols.local_block_idx)
    )) in

  (* self.eval_message_schedule::<AB>(builder, local_cols, next_cols); *)
  let! _ := eval_message_schedule local_cols next_cols in
  (* self.eval_work_vars::<AB>(builder, local_cols, next_cols); *)
  let! _ := eval_work_vars self local_cols next_cols in
  (*
    let next_cols: &Sha256DigestCols<AB::Var> =
        next[start_col..start_col + SHA256_DIGEST_WIDTH].borrow();
  *)
  let next_cols := digest_next_cols in
  (* self.eval_digest_row(builder, local_cols, next_cols); *)
  let! _ := eval_digest_row local_cols next_cols in
  (*
    let local_cols: &Sha256DigestCols<AB::Var> =
        local[start_col..start_col + SHA256_DIGEST_WIDTH].borrow();
  *)
  let local_cols := digest_local_cols in
  (* self.eval_prev_hash::<AB>(builder, local_cols, next_is_padding_row); *)
  (* let! _ := eval_prev_hash local_cols next_is_padding_row in *)
  MExpr.pure tt.

(*
fn eval<'a>(&'a self, builder: &'a mut AB, start_col: Self::AirContext<'a>)
where
    <AB as AirBuilder>::Var: 'a,
    <AB as AirBuilder>::Expr: 'a,
{
    self.eval_row(builder, start_col);
    self.eval_transitions(builder, start_col);
}
*)
Definition eval
    (self : Sha256Air.t)
    (start_col : Z)
    (round_local_cols round_next_cols : Sha256RoundCols.t Var.t)
    (digest_local_cols digest_next_cols : Sha256DigestCols.t Var.t) :
    MExpr.t unit :=
  let! _ := eval_row start_col digest_local_cols in
  let! _ :=
    eval_transitions self start_col
      round_local_cols round_next_cols
      digest_local_cols digest_next_cols in
  MExpr.pure tt.

Definition print_eval : string :=
  let self : Sha256Air.t := {|
    Sha256Air.bitwise_lookup_bus := {|
      BitwiseOperationLookupBus.inner := {|
        LookupBus.index := 8000;
      |};
    |};
    Sha256Air.row_idx_encoder := row_idx_encoder;
    Sha256Air.bus := 8001;
  |} in
  let start_col := 0 in
  let '(round_local_cols, round_next_cols) :=
    MGenerate.eval [[ (
      MGenerate.generate (A := Sha256RoundCols.t Var.t) (||),
      MGenerate.generate (A := Sha256RoundCols.t Var.t) (||)
    ) ]] in
  (* Because the "round" version is longer than the "digest" one *)
  let digest_local_cols :=
    MGenerate.eval [[
      MGenerate.generate (A := Sha256DigestCols.t Var.t) (||)
    ]] in
  let '(_, digest_next_cols) :=
    MGenerate.eval [[ (
      MGenerate.generate (A := Sha256RoundCols.t Var.t) (||),
      MGenerate.generate (A := Sha256DigestCols.t Var.t) (||)
    ) ]] in
  ToRocq.cats [
    ToRocq.endl;
    ToRocq.to_rocq (eval self start_col round_local_cols round_next_cols digest_local_cols digest_next_cols) 0;
    ToRocq.endl
  ].

Compute print_eval.
