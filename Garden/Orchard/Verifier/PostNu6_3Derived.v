(** * Audited derivation of Post-NU6.3 verifier expression data

    This proof-side module preserves the path from Garden's formal Orchard
    configure program and selector compression to the verifier's gate and
    lookup expression trees.  Runtime verifier modules deliberately do not
    import it; [PostNu6_3Materialization.v] compares these derived values with
    the compact literals used for evaluation and extraction. *)

From Stdlib Require Import ZArith Lists.List.
Require Import Garden.Halo2.main.
Require Import Garden.Halo2.serialize.
Require Import Garden.Halo2.plonkish.main.
Require Import Garden.Halo2.Verifier.Plonk.
Require Import Garden.Halo2.Verifier.Lookup.
Require Import Garden.Orchard.compiled.check.
Require Import Garden.Orchard.compiled.configuration.
Require Import Garden.Orchard.Verifier.PostNu6_3.

Import ListNotations.
Import Plonkish.
Local Open Scope Z_scope.

Module OrchardPostNu63Derived.
  Module P := PlonkVerifier.

  Definition expression_query_of_pair
      (kind : P.column_kind) (query : Z * Z) : P.query_spec :=
    let queries :=
      match kind with
      | P.Advice => OrchardPostNu63.advice_query_pairs
      | P.Fixed => OrchardPostNu63.fixed_query_pairs
      | P.Instance => OrchardPostNu63.instance_query_pairs
      end in
    {| P.query_column := {|
         P.column_type := kind;
         (** Expression evaluation vectors are indexed by query registration
             position, not by physical column number. *)
         P.column_index :=
           match OrchardPostNu63.query_index_from query queries 0 with
           | Some index => index
           | None => List.length queries
           end
       |};
       P.query_rotation := snd query |}.

  Fixpoint compiled_expression
      (expression : Expression.t Configure.indexed_columns) : P.expression :=
    match expression with
    | Expression.Constant value => P.Constant value
    | Expression.Selector selector => P.Selector (Z.to_nat selector)
    | Expression.Fixed column rotation =>
        P.Query (expression_query_of_pair P.Fixed
          (column, rotation.(Rotation.offset)))
    | Expression.Advice column rotation =>
        P.Query (expression_query_of_pair P.Advice
          (column, rotation.(Rotation.offset)))
    | Expression.Instance_ column rotation =>
        P.Query (expression_query_of_pair P.Instance
          (column, rotation.(Rotation.offset)))
    | Expression.Negated inner => P.Negated (compiled_expression inner)
    | Expression.Sum lhs rhs =>
        P.Sum (compiled_expression lhs) (compiled_expression rhs)
    | Expression.Product lhs rhs =>
        P.Product (compiled_expression lhs) (compiled_expression rhs)
    | Expression.Scaled inner factor =>
        P.Scaled (compiled_expression inner) factor
    end.

  Definition compiled := OrchardCompiledCheck.compiled.

  Definition compiled_lookups :
      list (LookupArgument.t Configure.indexed_columns) :=
    compiled.(CompiledSystem.lookups).

  Definition lookup_table_expression (lookup_column : Z) : P.expression :=
    P.Query (expression_query_of_pair P.Fixed
      (OrchardConfigure.lookup_fixed_column lookup_column, 0)).

  Definition lookup_description
      (argument : LookupArgument.t Configure.indexed_columns) :
      LookupVerifier.argument := {|
    LookupVerifier.input_expressions := map (fun pair =>
      compiled_expression (fst pair)) argument.(LookupArgument.pairs);
    LookupVerifier.table_expressions := map (fun pair =>
      lookup_table_expression (snd pair)) argument.(LookupArgument.pairs)
  |}.

  Definition lookup_descriptions : list LookupVerifier.argument :=
    map lookup_description compiled_lookups.

  Definition gate_polynomials : list (list P.expression) :=
    map (fun expression => [compiled_expression expression])
      compiled.(CompiledSystem.gates).
End OrchardPostNu63Derived.
