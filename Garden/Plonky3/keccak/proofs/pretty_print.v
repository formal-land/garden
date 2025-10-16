Require Import Plonky3.M.
Require Import Plonky3.MExpr.
Require Import Plonky3.keccak.proofs.air_local.
Require Import Plonky3.keccak.columns.

(* We do not care about the prime we use, but it is needed to have one for the printing. *)
Parameter p : Z.
Instance IsPrime : Prime p.
Admitted.

Definition local_next : KeccakCols.t * KeccakCols.t :=
  MGenerate.eval MGenerate.generate.

Definition SQUARE_SIZE : Z := 5.

Compute PrettyPrint.cats [
  PrettyPrint.endl;
  "Trace 🐾"; PrettyPrint.endl;
  PrettyPrint.to_string
    ltac:(OfShallow.to_mexpr_trace (snd (
      M.to_trace (
        eval_local
          SQUARE_SIZE
          (fst local_next)
          (snd local_next)
          OfShallow.IsFirstRow
          OfShallow.IsTransition
      )
    )))
    2;
  PrettyPrint.endl;
  "Result 🛍️"; PrettyPrint.endl;
  "  tt";
  PrettyPrint.endl
].
