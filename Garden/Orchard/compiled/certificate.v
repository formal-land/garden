(** * Closed provenance certificate for the compiled Orchard constraint system

    [OrchardConfigure] interprets the allocation and builder operations in
    Garden's formal configure program.  [OrchardCompiledCheck.compiled] then
    applies selector compression using that derived metadata.  The deployed
    description in [compiled/pinned.v] occurs only on the right-hand side of
    the equalities below: it is the target whose provenance is established,
    not an input to compilation. *)

Require Import Garden.Halo2.main.
Require Import Garden.Halo2.plonkish.main.
Require Import Garden.Halo2.serialize.
Require Import Garden.Orchard.compiled.configuration.
Require Import Garden.Orchard.compiled.pinned.
Require Import Garden.Orchard.compiled.check.

Import Plonkish.

Module OrchardCompiledCertificate.

Record certificate : Prop := {
  configure_state_valid :
    OrchardConfigure.state.(Metadata.State.valid) = true;
  configure_counts :
    OrchardConfigure.base_fixed_columns =
        OrchardCompiledPinned.base_fixed_columns /\
    OrchardConfigure.num_advice_columns =
        OrchardCompiledPinned.num_advice_columns /\
    OrchardConfigure.num_instance_columns =
        OrchardCompiledPinned.num_instance_columns /\
    OrchardConfigure.num_selectors = OrchardCompiledPinned.num_selectors;
  compiled_gate_polynomials :
    OrchardCompiledCheck.zll_eqb
      (List.map OrchardCompiledCheck.gate_fp
        OrchardCompiledCheck.compiled.(CompiledSystem.gates))
      OrchardCompiledPinned.gate_fps = true;
  compiled_gate_count :
    Nat.eqb
      (List.length OrchardCompiledCheck.compiled.(CompiledSystem.gates))
      OrchardCompiledPinned.num_gates = true;
  compiled_combination_count :
    andb
      (Nat.eqb
        (List.length
          OrchardCompiledCheck.compiled.(CompiledSystem.combination_columns))
        OrchardCompiledPinned.num_combinations)
      (Z.eqb
        (OrchardConfigure.base_fixed_columns +
          Z.of_nat
            (List.length
              OrchardCompiledCheck.compiled.(CompiledSystem.combination_columns)))
        OrchardCompiledPinned.num_fixed_columns) = true;
  compiled_combination_columns :
    OrchardCompiledCheck.compiled.(CompiledSystem.combination_columns) =
      OrchardCompiledCheck.combination_columns_cache;
  compiled_combination_assignment_count :
    List.length
      OrchardCompiledCheck.compiled
        .(CompiledSystem.combination_assignments) = 15%nat;
  selector_assignment_coverage :
    List.forallb
      (fun selector =>
        List.existsb
          (fun assignment =>
            Z.eqb assignment.(SelectorAssignment.selector) (Z.of_nat selector))
          OrchardCompiledCheck.compiled.(CompiledSystem.selector_assignments))
      (List.seq 0 (Z.to_nat OrchardConfigure.num_selectors)) = true;
  selectors_fully_compiled :
    CompiledSystem.selector_free_b OrchardCompiledCheck.compiled = true;
  advice_query_order :
    OrchardCompiledCheck.compiled.(CompiledSystem.advice_queries) =
      OrchardCompiledPinned.advice_queries;
  fixed_query_order :
    OrchardCompiledCheck.compiled.(CompiledSystem.fixed_queries) =
      OrchardCompiledPinned.fixed_queries;
  instance_query_order :
    OrchardCompiledCheck.compiled.(CompiledSystem.instance_queries) =
      OrchardCompiledPinned.instance_queries;
  permutation_column_order :
    OrchardCompiledCheck.compiled.(CompiledSystem.permutation_columns) =
      OrchardCompiledPinned.permutation_columns;
  configured_constants :
    OrchardCompiledCheck.compiled.(CompiledSystem.constants) =
      OrchardCompiledPinned.constants;
  configured_minimum_degree : OrchardConfigure.minimum_degree = None;
  compiled_lookup_inputs :
    OrchardCompiledCheck.zlll_eqb
      (List.map
        (fun lookup : LookupArgument.t Configure.indexed_columns =>
          List.map
            (fun pair => OrchardCompiledCheck.gate_fp (fst pair))
            lookup.(LookupArgument.pairs))
        OrchardCompiledCheck.compiled.(CompiledSystem.lookups))
      OrchardCompiledPinned.lookup_input_fps = true;
  compiled_lookup_tables :
    OrchardCompiledCheck.zlll_eqb
      OrchardCompiledCheck.model_lookup_table_fps
      OrchardCompiledPinned.lookup_table_fps = true;
  synthesis_constant_columns :
    OrchardCompiledCheck.zlist_eqb OrchardCompiledCheck.constants_columns
      OrchardCompiledPinned.constants = true;
  synthesis_copies_configured :
    List.forallb
      (fun column =>
        List.existsb (OrchardCompiledCheck.pair_eqb column)
          OrchardCompiledCheck.derived_permutation_codes)
      OrchardCompiledCheck.copy_columns = true;
}.

Theorem certified : certificate.
Proof.
  constructor.
  - exact OrchardConfigure.state_valid.
  - exact OrchardCompiledCheck.configure_counts_match.
  - exact OrchardCompiledCheck.gate_polynomials_match.
  - exact OrchardCompiledCheck.gate_count_match.
  - exact OrchardCompiledCheck.combination_count_match.
  - exact OrchardCompiledCheck.combination_columns_match.
  - exact OrchardCompiledCheck.combination_assignments_count_match.
  - exact OrchardCompiledCheck.selector_assignments_cover.
  - exact OrchardCompiledCheck.compiled_selector_free.
  - exact OrchardCompiledCheck.advice_queries_match.
  - exact OrchardCompiledCheck.fixed_queries_match.
  - exact OrchardCompiledCheck.instance_queries_match.
  - exact OrchardCompiledCheck.permutation_columns_match.
  - exact OrchardCompiledCheck.configure_constants_match.
  - exact OrchardCompiledCheck.minimum_degree_match.
  - exact OrchardCompiledCheck.lookup_inputs_match.
  - exact OrchardCompiledCheck.lookup_tables_match.
  - exact OrchardCompiledCheck.constants_column_match.
  - exact OrchardCompiledCheck.copy_columns_in_permutation.
Qed.

End OrchardCompiledCertificate.
