(** * Plonk verifying-key surface used by [verify_proof]

    Transcription of the verify-time fields of
    [halo2_proofs/src/plonk.rs] and [plonk/error.rs], specialized to
    Vesta. Gate polynomials are the post-compression query-indexed
    expressions the verifier evaluates at the opened cells. *)

Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Lists.List.
Require Import Garden.Rust.primitives.
Require Import Garden.Halo2.halo2_proofs.pasta.
Require Import Garden.Halo2.halo2_proofs.transcript.
Require Import Garden.Halo2.halo2_proofs.poly.domain.
Require Import Garden.Halo2.halo2_proofs.poly.commitment.

Import List.ListNotations.
Global Open Scope Z_scope.

Module Error.
  Inductive t : Set :=
  | Synthesis
  | InvalidInstances
  | ConstraintSystemFailure
  | BoundsFailure
  | Opening
  | Transcript (e : TranscriptError.t)
  | InstanceTooLarge
  | NotEnoughRowsAvailable (current_k : u32).

  Definition of_transcript (e : TranscriptError.t) : t := Transcript e.
End Error.

Module ColumnType.
  Inductive t : Set :=
  | Advice | Fixed | Instance.
End ColumnType.

Module Column.
  Record t : Set := {
    column_type : ColumnType.t;
    index : usize;
  }.
End Column.

Module Rotation.
  Definition t : Set := Z.
  Definition cur : t := 0.
  Definition prev : t := -1.
  Definition next : t := 1.
End Rotation.

Module Query.
  Record t : Set := {
    column : Column.t;
    rot : Rotation.t;
    index : usize;
  }.
End Query.

(** Query-indexed gate expression, after selector compression. *)
Module Expression.

  Inductive t : Set :=
  | Constant (value : Z)
  | Fixed (index : usize)
  | Advice (index : usize)
  | Instance (index : usize)
  | Negated (e : t)
  | Sum (a b : t)
  | Product (a b : t)
  | Scaled (e : t) (scale : Z).

  Fixpoint evaluate (e : t)
      (fixed_evals advice_evals instance_evals : list Z) : Z :=
    match e with
    | Constant value => Fp.from value
    | Fixed i => Vec.nth (A := Z) fixed_evals i
    | Advice i => Vec.nth (A := Z) advice_evals i
    | Instance i => Vec.nth (A := Z) instance_evals i
    | Negated e => Fp.opp (evaluate e fixed_evals advice_evals instance_evals)
    | Sum a b =>
      evaluate a fixed_evals advice_evals instance_evals
        +s evaluate b fixed_evals advice_evals instance_evals
    | Product a b =>
      evaluate a fixed_evals advice_evals instance_evals
        *s evaluate b fixed_evals advice_evals instance_evals
    | Scaled e scale =>
      evaluate e fixed_evals advice_evals instance_evals
        *s Fp.from scale
    end.
End Expression.

Module LookupArgument.
  Record t : Set := {
    input_expressions : list Expression.t;
    table_expressions : list Expression.t;
  }.
End LookupArgument.

Module PermutationArgument.
  Record t : Set := {
    columns : list Column.t;
  }.
End PermutationArgument.

Module PermutationVK.
  Record t : Set := {
    commitments : list VestaCurve.point;
  }.
End PermutationVK.

Module ConstraintSystem.
  Record t : Set := {
    num_instance_columns : usize;
    num_advice_columns : usize;
    instance_queries : list (Column.t * Rotation.t);
    advice_queries : list (Column.t * Rotation.t);
    fixed_queries : list (Column.t * Rotation.t);
    gates : list (list Expression.t);
    lookups : list LookupArgument.t;
    permutation : PermutationArgument.t;
    blinding_factors : usize;
    degree : usize;
  }.

  Definition get_any_query_index (cs : t) (column : Column.t) : usize :=
    let queries :=
      match column.(Column.column_type) with
      | ColumnType.Advice => cs.(advice_queries)
      | ColumnType.Fixed => cs.(fixed_queries)
      | ColumnType.Instance => cs.(instance_queries)
      end in
    usize_of (Z.of_nat
      (fst (List.fold_left (fun '(found, i) '(col, rot) =>
        if Nat.eqb (Integer.to_nat col.(Column.index)) (Integer.to_nat column.(Column.index))
             && Z.eqb rot Rotation.cur
             && match col.(Column.column_type), column.(Column.column_type) with
                | ColumnType.Advice, ColumnType.Advice
                | ColumnType.Fixed, ColumnType.Fixed
                | ColumnType.Instance, ColumnType.Instance => true
                | _, _ => false
                end
        then (i, S i)
        else (found, S i)) queries (0%nat, 0%nat)))).
End ConstraintSystem.

Module VerifyingKey.
  Record t : Set := {
    domain : EvaluationDomain.t;
    fixed_commitments : list VestaCurve.point;
    permutation : PermutationVK.t;
    cs : ConstraintSystem.t;
    cs_degree : usize;
    transcript_repr : Z;
  }.

  Definition hash_into (vk : t) (tr : Blake2bRead.t) : Blake2bRead.t :=
    Blake2bRead.common_scalar tr vk.(transcript_repr).
End VerifyingKey.
