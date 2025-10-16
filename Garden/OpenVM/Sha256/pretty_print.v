Require Import Garden.Plonky3.M.
Require Import Garden.Plonky3.MExpr.
Require Import Garden.OpenVM.primitives.bitwise_op_lookup.
Require Import Garden.OpenVM.Sha256.air_expr.
Require Import Garden.OpenVM.Sha256.columns.

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
  PrettyPrint.cats [
    PrettyPrint.endl;
    PrettyPrint.to_string (eval self start_col round_local_cols round_next_cols digest_local_cols digest_next_cols) 0;
    PrettyPrint.endl
  ].

Compute print_eval.
