Require Import Garden.Plonky3.M.
Require Import Garden.Plonky3.MExpr.
Require Import Garden.OpenVM.Sha256.columns.
Require Import Garden.OpenVM.Sha256.utils.

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
    MGenerateVar.eval MGenerateVar.generate in
  ToRocq.cats [
    ToRocq.endl;
    ToRocq.to_rocq (eval_row start_col local_cols) 0;
    ToRocq.endl
  ].

Compute print_eval_row.
