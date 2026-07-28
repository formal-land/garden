# Halo2 chip model: what it captures and where it is sketchy

This note describes how the Rocq semantics in `proof.v` relates to how real
Rust Halo2 chips behave, so that readers know what the gadget proofs actually
establish and what they assume away.

## The two interpreters

The synthesis syntax (`Synthesis.v`) is a free monad with a layouter layer
`𝓛` and a region layer `𝓡`. It has two interpreters:

- **Operational** — `serialize.v` (`V1.eval_layouter`/`eval_region`). Takes a
  floor-planner placement `region_start : RegionId -> Z` and lowers every
  region offset to an absolute, shared row `region_start region + offset`
  (`serialize.v:319`, `serialize.v:328`), emitting `Raw.Event`s. This mirrors
  what Rust's `Layouter`/`MockProver` actually do.
- **Relational** — `proof.v`. Rather than a single interpreter, the syntax is
  consumed by paired fixpoints: `region_value`/`layouter_value` (`proof.v:236`,
  `proof.v:271`) compute the program's result, and `region_facts`/
  `layouter_facts` (`proof.v:253`, `proof.v:290`) reify the established facts as
  data, turned into a `Prop` by `interpret_facts` (`proof.v:364`). All keep
  `RegionId` abstract and never apply `region_start`.

The gadget theorems (e.g. `CompleteAddition.deterministic`) use the relational
interpreter's gate layer only. This document is about that relational model.

## What the model gets right

- **Gate polynomial evaluation** (`eval_expression`, `proof.v:90-137`):
  constants, fixed/advice/instance reads at a rotation, and
  sum/product/negation/scaling are all modeled correctly. Rotation as an
  additive row offset (`rotated_row`, `proof.v:58-62`) is correct for
  region-local reasoning.
- **Selector-gated constraints** (`Constraint.Select`, `proof.v:144`):
  `eval_selector ≠ 0 → constraint`, matching Halo2's "constraint is multiplied
  by its selector" — gates bind only on enabled rows.
- **Copy constraints** (`Copy` reified as `Fact.CellsEqual` and interpreted as
  `eval_cell l = eval_cell r`, `proof.v:268`/`proof.v:353`, with `eval_cell` at
  `proof.v:212-231`): a faithful relational abstraction of the permutation
  argument. Because `Cell.t` carries its own `region` (`Synthesis.v:22-27`),
  cross-region wiring is expressible, and it is the one place inter-region
  linking is modeled — correctly, as value equality.
- **Fixed assignment and selector enabling** as reified pinning facts
  (`Fact.FixedIs → … = value`, `Fact.SelectorOn → … = 1`, interpreted at
  `proof.v:349-352`): faithful. Lookup-table loading is reified the same way
  (`Fact.LookupTableLoaded`, `proof.v:45`), pinning each table column to its
  `value_at_row` — see [Tying lookups to the loaded
  table](#tying-lookups-to-the-loaded-table-initlookuptables).
- **Layouter-level constant pinning** (`𝓡.ConstrainConstant`, reified as
  `Fact.CellIsConstant → eval_cell Γ cell = value`) — see [The constants
  mechanism](#the-constants-mechanism-constrain_constant).

## Defensible idealizations

- **Regions as independent integer address spaces.** `AddRegion` evaluates the
  body at abstract `(region, offset)` and never resolves `region_start`
  (`proof.v:280`, `proof.v:300`). This bakes in Halo2's usage discipline —
  gates only read cells in their own region, and the planner leaves enough
  room — as an axiom. It is sound for per-region gate proofs, but it abstracts
  the floor planner away entirely. The model therefore **cannot express region
  overlap, nor a rotation escaping a region's allocated rows** into a
  neighbor's data. The two interpreters are not proven consistent (no theorem
  relates the relational facts to the operational events).
- **Region-scoped advice and fixed columns.** Acceptable: gates are
  region-local, and the only legitimate cross-region advice link is a copy
  constraint, which is modeled.

## Where it gets sketchy

1. **Instance columns are global public inputs.** `Assignment.instance_` has
   type `Instance_ -> Z -> Z` (`proof.v:14`): instance columns are addressed
   by an absolute row alone, not region-scoped, matching real Halo2 and
   `serialize.v`'s region-less `Cell.instance_raw` lowering
   (`serialize.v:450`). (The record field, the `Expression.Instance_` case,
   and `ConstrainInstance` all address an instance column by absolute row
   alone, so two regions constraining the same instance column and row read
   the same abstract cell.) One residual
   idealization remains, shared with advice/fixed: a gate that queries an
   instance column uses the region-local gate row rather than an absolute
   row. This is benign for the audited chips, which reference instance only
   via `constrain_instance`, not in gates.

2. **Lookups have a `Prop` value model.** `Assignment.t` carries a global
   `lookup : Columns.Lookup -> Z -> Z` table (addressed by an absolute
   `table_row`, like `instance_`), and `eval_lookup_argument` asserts that, at
   a `(region, row)`, the tuple of queried expressions equals some row of that
   table, with the witness bounded by `nb_table_rows` — the bound is what
   gives a lookup its range-check role, since only genuine table rows satisfy
   it. `satisfies_lookups` conjoins this over every `(region, row)` and every
   `ConstraintSystem.lookups` entry, and is folded into `Satisfies` /
   `circuit_holds`. `nb_table_rows` and the table contents are not free
   inputs: both are derived from the program's `InitLookupTables` — see
   [Tying lookups to the loaded
   table](#tying-lookups-to-the-loaded-table-initlookuptables). `serialize.v`
   fills the same tables with concrete fixed assignments
   (`serialize.v:413-420`); the two interpreters remain unproven-consistent.
   `GeneratorTable.sound` (`sinsemilla/chip_proof.v`) is the first end-to-end
   instance: on an active `q_sinsemilla1` row the three padded slots collapse
   to the bare `word`/`x_p`/`y_p` field values, so the lookup pins the
   witnessed point to the `SINSEMILLA_S` generator for the message word. The
   range-check chip's `LookupArgument` is consumed too: `RangeTable`
   (`utilities/lookup_range_check_proof.v`) proves `configure_lookups_eq`
   (`lookup_range_check.configure` emits exactly `RangeTable.argument`),
   `loaded_index_table` (a `LookupTableLoaded` fact with index-sequence
   values pins the table column to the identity on `[0, n)`), `word_sound`
   (on a `q_lookup = 1`, `q_running = 1` row the running-sum word
   `z_cur -F z_next *F 2^k` lies in `[0, nb_table_rows)`) and
   `short_word_sound` (the `q_running = 0` form, which must carry its
   selector-off hypothesis explicitly — the fact model records only
   `SelectorOn` points). The `Lookup.TableIdx` index column it checks
   against is loaded as the first entry of `load_generator_table`
   (`sinsemilla/chip.v`), mirroring Rust, where `SinsemillaChip::load`
   provides the shared table and `LookupRangeCheckConfig::load` is never
   called by the Orchard circuit. Circuit-level consumers: the variable-base
   mul overflow decomposition
   (`Orchard/circuit_proof/ownership/var_base_overflow.v`, via
   `RangeTable.word_sound` with `GeneratorTable.loaded` at
   `Lookup.TableIdx`) and the `α_0'` canonicity lookup
   (`Orchard/circuit_proof/base_field_canonicity.v`,
   `alpha_lookup_word_range`, same pattern). **On this branch the idealized
   membership semantics remains a modeling choice.** The polynomial layer
   that closes this `Prop` model's loop from above lives on
   `valerii-huhnin@compilation-correctness`, not here: there `lookup_sound` /
   `lookup_complete` (`Halo2/plonkish/lookup_poly.v`) prove the
   set-membership reading of `eval_lookup_argument` equivalent, for all
   θ, β, γ, to the five lookup grand-product rules the deployed verifier
   checks on the cyclic domain, with the tables-as-fixed-prefix coherence
   discharged as a `vm_compute` certificate on the pinned instance
   (`Orchard/circuit_compiled_algebraic.v`). Neither `Halo2/plonkish/` nor
   `Orchard/circuit_compiled*.v` is part of this branch's build.

3. **No cyclic domain, no usable-row distinction.** Rows are plain integers
   and `rotated_row = row + offset` (`proof.v:58-62`); there is no `nb_rows`
   and no `row mod nb_rows` wrap. Real Halo2 rows live in `Z / 2^k Z` with
   cyclic rotations, and the last `blinding_factors + 1` rows are unusable.
   The model allows negative and unbounded rows and has no notion that gates
   must not be enabled on blinding rows, so a "valid assignment" here is
   strictly more permissive than a real circuit.

4. **The synthesis-to-gates gluing (`circuit_holds`).** The specification
   that an assignment satisfies the configured constraint system lives in
   `proof.v`:
   - `satisfies_gates` — gate satisfaction, `forall (region, row), eval_gates
     …`: the simplest faithful reading of "the prover checks every row";
     because each gate constraint is selector-guarded it is vacuous off the
     enabled rows. Quantifying over each region's actual extent instead is a
     refinement that belongs with the finite-domain work (item 3).
   - `Satisfies` = `satisfies_gates /\ satisfies_lookups` (item 2).
   - `circuit_holds Γ program system` = `interpret_facts Γ (layouter_facts
     program) /\ Satisfies Γ (layouter_table_rows program) system` — what a
     successful proof of a chip gives: the synthesis-time facts plus
     constraint satisfaction, with the lookup-table size read off the
     program.
   - The value and facts of a program are computed by separate fixpoints
     (`region_value`/`layouter_value`, `region_facts`/`layouter_facts`); the
     facts are reified as data (`Fact.t`) and interpreted into `Prop` by
     `interpret_facts`, because `𝓡`/`𝓛` are non-small inductives and admit no
     `Prop`-valued recursion.
   - Bridges discharge the `Hselector`/`Hgate` hypotheses of the gate lemmas:
     `enabled_nonzero` (an enabled selector evaluates nonzero) and
     `satisfies_gates_single` / `eval_gates_In` / `satisfies_gates_at`
     (extract a gate of a one- or multi-gate system).

   `CompleteAddition.synthesize_correct` (`add_proof.v`) is the template
   instance: from `circuit_holds` over the `add` chip's `synthesize` program
   and `configure` system, the next-row result is the `output` of the
   current-row inputs — `deterministic` as a corollary of *running the
   program*, not of free hypotheses. Chip-level `synthesize_correct` theorems
   are proved (`Qed`) along the same template for the determinism-bearing
   gadgets (ECC `add`, `add_incomplete`, `mul/incomplete`, `mul/overflow`,
   `mul_fixed`/`full_width`/`short`; Poseidon full/partial/pad-and-add;
   Sinsemilla round and initial-y_Q; Merkle decomposition), each next to its
   proved gate `deterministic`; chips whose `synthesize`/`configure` take an
   abstract sub-program (Merkle's `cond_swap`) project past the opaque prefix
   of the facts/gates lists rather than reducing them. The whole-circuit
   Orchard action theorems (`OrchardAction.satisfies_specification`,
   `OrchardAction.deterministic` in
   `Garden/Orchard/circuit_proof/main.v`) build on this gluing; see
   `docs/orchard-soundness-proof.md` where present. The **completeness**
   direction — an honestly synthesized Γ satisfies `circuit_holds` — is now
   supplied generically by `Complete.circuit_holds_intro` (`Halo2/complete.v`)
   and instantiated for the add chip and, constructively, for the whole Orchard
   circuit; see
   [`orchard-completeness-proof.md`](orchard-completeness-proof.md) for the
   theorem surface and [Open gaps](#open-gaps) for what is proved and what
   remains.

## Tying lookups to the loaded table (`InitLookupTables`)

The lookup model (item 2) needs two things the synthesis program already
fixes: the table contents — `Γ.(Assignment.lookup) : Columns.Lookup -> Z -> Z`
(`proof.v:15`) — and the table size — `nb_table_rows`, the bound on the
witnessed row in `eval_lookup_argument` (`proof.v:441`). Leaving them as free
inputs was a soundness trust hole (the range-check guarantee was only as
strong as the out-of-band promise that the caller plugged in the real size
and table) and a hard blocker for completeness (one cannot even state
"construct each witness `table_row < nb_table_rows`" while both are free).
Both are derived from the program:

- `InitLookupTables name entries` (`Synthesis.v:128`) carries, per
  `LookupTableColumn`, `values : list Z` and `default_value`; the generator
  table loads `values := map sinsemilla_s_x generator_table_indexes` (length
  `2 ^ sinsemilla_k = 1024`) padded with `default_value := sinsemilla_s0_x`.
- The relational interpreter consumes it: `value_at_row` (`proof.v:68`)
  mirrors `serialize.v`'s fill (the `row`-th entry of `values`, else
  `default_value`); `Fact.LookupTableLoaded column values default_value`
  (`proof.v:45`) is emitted by `layouter_facts` for each entry (`proof.v:306`)
  and interpreted as `forall row, 0 <= row -> Γ.(Assignment.lookup) column row
  = value_at_row row values default_value` — exactly the rows a replay of the
  serializer's events (which write rows `>= 0` only) can establish; a
  `layouter_table_rows` fixpoint (`proof.v:319`) returns the loaded row
  count, so `circuit_holds` computes `nb_table_rows` from the program
  (`proof.v:489`) — a program with no table (e.g. `add`) gets `0`.
- The operational interpreter uses the same data: `serialize.v` emits the
  per-row fixed assignments plus a fill carrying `length values` and
  `default_value` (`fill_lookup_entries`, `serialize.v:399-409`).
- `GeneratorTable.sound` (`sinsemilla/chip_proof.v`) takes the synthesis
  facts of running `load_generator_table` instead of a free `Htable`;
  `GeneratorTable.loaded` derives that the carried table agrees with the
  concrete model on `[0, 2 ^ sinsemilla_k)`, and
  `GeneratorTable.table_rows_eq` reduces the program-derived bound to
  `2 ^ sinsemilla_k`. Only the Pallas primality certificate remains as an
  axiom.

One known refinement remains:

- Faithfully, a lookup table is not a separate `Assignment.lookup` address
  space: it is ordinary fixed columns occupying `[0, nb_table_rows) ⊆
  [0, nb_rows)`, with the `default_value` padding coinciding with the
  unusable/blinding rows — concretely, `sinsemilla_s0_x` is exactly the
  `(1 - q_s1) ● sinsemilla_s0_x` padding term in `generator_table_argument`.
  Making `nb_table_rows`, the fill default, and the gate padding mutually
  coherent is finite-domain bookkeeping deferred with the cyclic-domain gap
  (item 3).

## The constants mechanism: `constrain_constant`

Halo2 pins cells to public constants at the layouter level:
`ConstraintSystem::enable_constant` designates an equality-enabled fixed
*constants column*, and `region.constrain_constant(cell, c)` writes `c` into
a fresh cell of that column plus a permutation copy to `cell`
(`assign_advice_from_constant` is assign-plus-pin in one call) — to the
verifier exactly as strong as a gate `cell = c`.

The DSL models this. `𝓡.ConstrainConstant (cell, value)` (with the
translation-prelude alias `assign_advice_from_constant`) is reified as
`Fact.CellIsConstant cell value` and interpreted as `eval_cell Γ cell = value`
— raw-value pinning, so `value` must be a reduced literal in `[0, p)`.
`V1.eval_region` emits no raw event for the op: the V1 floor planner
materializes constants as a trailing block after all regions, and that block
is replayed verbatim from the Rust-generated table
(`circuit_synthesis_constants.v`).

Emission covers every site the action circuit exercises — 166 bindings across
nine sites; two further sites are unexercised and documented, not emitted —
and the standalone certificate
`Garden/Orchard/circuit_synthesis_constants_check.v` proves by `vm_compute`
that the program's `ConstrainConstant` ops, resolved through the serializer's
placement, equal the replay table as a multiset of (absolute cell, value)
pairs: a Rust-independent check the JSON parity comparison structurally
cannot provide. The full analysis — the gap as originally found, the
root-cause trace, the per-site table, and the validation gates — is in
[`constrain-constant-fix.md`](constrain-constant-fix.md).

## Field-element wrap and base-field scalar canonicity

Cell values in the relational model are plain `Z`, and every constraint is
interpreted with the mod-p field operations (`UnOp.from`/`BinOp.*`,
`Field/Field.v`), so modular wrap-around of field *values* is inherent and
faithful in `Holds Γ` — the model neither ignores nor idealizes it. (Do not
confuse this with the *row-domain* wrap of item 3 — cyclic rotations over
`Z/2^k Z` — which is genuinely unmodeled but unrelated to scalars.)

The wrap is why the two fixed-base scalar legs differ. The running-sum
telescoping holds mod p:

```
z_0 = Σ_{i<W} 8^i·w_i + 8^W·z_W   (mod p)
```

For the short leg (`W = 22`, 66 bits ≪ 254) the word bounds force the
identity over ℤ — a wrap is arithmetically impossible, so `z_W = 0` plus
ranges pin the `w_i` to the scalar's base-8 digits. For the base-field leg
(`W = 85`, `8⁸⁵ = 2²⁵⁵ > p ≈ 2²⁵⁴`) a shift by exactly `p` fits inside the
digit space: one field element `α` (with `α < 2²⁵⁵ − p`) has *two* valid
255-bit digit strings, for `α` and `α + p`. The ambiguity is semantically
real: the folded multiple is `[k]·NullifierK` with `k` read mod `q ≠ p`, so
the two strings give different NF_OLD points. The model correctly exhibits
the attack the real circuit has to (and does) exclude.

Upstream excludes the non-canonical string with a dedicated sub-circuit
(`base_field_elem.rs`, constraint group
`https://p.z.cash/halo2-0.1:ecc-fixed-mul-base-canonicity`): a `canon_checks`
gate over the pieces `α_0'`, `α_1`, `α_2` with running-sum probes
`z_13`/`z_43`/`z_44`/`z_84`, plus lookup range checks, all under strict
(`z_85 = 0`) decomposition. All of it is translated: the canonicity gate
(`Selector.QMulFixedBaseField`, `ecc/chip/mul_fixed/base_field_elem.v`); the
`"Canonicity checks"` region (`circuit.v` `synthesize_canonicity_checks`);
the `α_0'` lookup region (`synthesize_alpha_lookup`); and the strict tail
`z_85 = 0` via the constants mechanism above.

The proof layer discharges this route end-to-end where the whole-circuit
Orchard development is present: the gate/region/lookup extraction in
`circuit_proof/base_field_canonicity.v` (culminating in the 85-window digit
match `nullifier_k_window_digit`), the generic circuit-free reconstruction
core in `Field/BaseEightReconstruct.v` (two integers below `p` that are
congruent mod `p` are equal), and the `nullifier_k` scalar-value and
`nf_old` legs (`circuit_proof/us_free/nullifier_k.v`,
`circuit_proof/nullifier_k/out.v`). One spec-level consequence:
`OrchardSpec.nullifier`'s scalar is the *reduced* base-field sum `+F` — with
an unreduced ℤ-sum the digit ambiguity above genuinely refutes the
circuit↔spec equality, because the circuit witnesses the canonical digit
string of the reduced scalar.

## The operational bridge

The relational ↔ operational consistency gap is closed — see
`docs/operational-soundness.md` for the full account. The generic bridge
(`Halo2/realize/main.v` + `realize/value.v`/`realize/constraints.v`/
`realize/facts.v`/`realize/sound.v`) replays the `serialize.v` event stream
into a flat grid (`apply_events`, failing on any conflicting rewrite) and
proves `operational_sound`: replay success plus acceptance by the ideal
checker `mock_prover_accepts` (gates and lookups of the indexed, flattened
system at every absolute row; `Raw.Event.Copy` permutation obligations read
off the events) yields `circuit_holds` of the realized assignment, under the
decidable system hypotheses `instance_free` (no `Expression.Instance_` in
gates/lookups) and `flattening_ok` (no `Constraint.Range _ 0`);
`operational_complete` is the converse given an inhabitant of `RegionId`.
The floor planner's trailing constants block enters `operational_sound` as
an explicit extra event input with the `constants_materialized`
correspondence (vacuous for `ConstrainConstant`-free chips,
`operational_sound_no_tail`). The layout idealizations are thereby a
per-placement computation (replay success, by `vm_compute`) rather than
trusted hypotheses. Both instantiation layers are proved:

- `Halo2/realize/disjoint.v` — placement-generic sufficient conditions:
  `replay_is_ok` equals the decidable `conflict_free` verdict at every
  initial grid (`replay_is_ok_conflict_free`), and
  `layouter_replay_succeeds` / `layouter_with_tail_replay_succeeds` derive
  replay success from per-block single-assignment (`block_ok`,
  placement-independent) plus pairwise block compatibility
  (`blocks_compatible_all`: disjoint region row intervals under
  `region_start`; column-disjoint table and constants blocks) — per-region
  reasoning plus interval disjointness in place of one whole-stream
  quadratic replay.
- `Orchard/circuit_operational.v` — the whole-circuit Orchard
  instantiation: `orchard_operational_sound` discharges every decidable
  premise of `operational_sound` by `vm_compute` certificates on the
  19,617-event stream (replay success on symbolic witness planes,
  `instance_free`/`flattening_ok`, and the `constants_materialized`
  coverage of the concrete constants tail), so the `Holds` hypothesis of
  the Orchard action surface follows from mock acceptance of the
  serialized circuit alone; `orchard_action_statement_operational`
  composes with `action_statement`.

## Open gaps

- **Completeness of `circuit_holds`.** The gluing (item 4) was originally used
  in the soundness direction only. The dual — an honestly synthesized Γ
  *satisfies* `circuit_holds` — is now addressed (full account in
  [`orchard-completeness-proof.md`](orchard-completeness-proof.md)). The
  well-formedness
  fact the model did not track — selectors are 0 except where the synthesis
  program enables them — is now supplied as the selector plane of the
  `honest_planes` predicate (the enabled-point indicator), which makes
  `satisfies_gates` (quantified over all `(region, row)`) vacuous off the
  enabled points. On that basis:
  - `Complete.circuit_holds_intro` (`Halo2/complete.v`, `Qed`, clean audit)
    reduces `circuit_holds` to finite per-enabled-point gate/lookup/witness
    obligations plus three `vm_compute` Boolean checkers.
  - `CompleteAdditionCompleteness.completeness` (`ecc/chip/add_complete.v`,
    `Qed`, clean audit) is the add-chip instance.
  - `OrchardCompletenessInstance.orchard_completeness_instance`
    (`Orchard/circuit_completeness/instance/cert.v`, `Qed`, clean audit) is
    the constructive whole-circuit concrete instance
    (`Holds (honest_assignment test_input)` plus read-back for one concrete
    valid input): all 4,858 enabled gate points and all 2,964 witness facts
    are machine-verified by `vm_compute`.

  - `OrchardCompletenessAssembly.orchard_completeness`
    (`Orchard/circuit_completeness/forward/assembly.v`, `Qed`) is the
    universally quantified completeness theorem
    `OrchardHonestAssignment.orchard_completeness_statement` — every valid,
    nondegenerate honest input yields a satisfying Γ that reads back to the
    input. It composes, through `forward/api.v`'s
    `completeness_statement_of_families`, the whole-circuit gate side
    (`gates_all : family_gates_ok all_families`, a total case analysis over
    the 56 gate selectors into the per-family `forward/` lanes), the lookup
    side (`lookups_forward_ok`), the read-back (`read_back_forward`) and the
    witness-fact side (`witness_facts_ok`).

  Remaining: nothing. `orchard_completeness`'s assumption audit is exactly the
  repo baseline, so the universal whole-circuit completeness claim is
  unconditional, and the concrete instance is a special case of it. The last
  leaf, the 97 witness facts whose two cell addresses the generator fills
  through *different* derivations
  of one value, closed as the five group files of
  `forward/witness/`. There is no `Admitted`, `Axiom` or `admit` anywhere
  under `Garden/Orchard/` or `Garden/Halo2/` (per-file account in
  [`orchard-completeness-proof.md`](orchard-completeness-proof.md)).

  - `OrchardOperationalAgreement.orchard_operational_complete`
    (`Orchard/circuit_completeness/operational/main.v`, `Qed`, clean audit)
    carries that statement across the event-replay bridge (item 6): with the
    advice and instance planes chosen from the honest generator, the replayed
    grid of the serialized Orchard stream is accepted by the ideal
    `mock_prover_accepts` checker, for every valid, nondegenerate input. The
    relational-model idealization is therefore no longer load-bearing in the
    completeness direction either.

  Completeness is a non-vacuity result in both readings: it says the honest
  witness is accepted, not that nothing else is, and the operational layer
  inherits the ideal checker's own limits (all integer rows rather than the
  `2^k` cyclic domain, blinding rows unmodelled). The model idealizations
  listed elsewhere in this file remain in force.
- **Cyclic-domain refinement** (item 3) — *open on this branch; partially
  discharged on `valerii-huhnin@compilation-correctness`.* There the finite
  domain exists one layer below the relational model: `Halo2/plonkish/main.v`'s
  `Domain` carries `n = 2^k` rows, `usable_rows = n - (blinding_factors + 1)`,
  and the `l_0`/`l_last`/`l_blind` row predicates, and `compile_correct` /
  `plonkish_of_mock_prover` (`Halo2/plonkish/`) connect it upward:
  compiled-gate satisfaction on the cyclic domain ↔ selector-gated
  satisfaction on usable rows, and `mock_prover_accepts` ↔ compiled-plonkish
  satisfaction restricted to `[0, n)`, with the blinding-row vacuity and the
  finite-domain layout as computable side conditions (`finite_domain_ok_b`),
  instantiated on the concrete Orchard domain (k = 11, n = 2048) in
  `Orchard/circuit_compiled.v`. None of that is part of this branch's build,
  where the relational model is the bottom of the stack below
  `Halo2/realize/`.
  What remains even there: the relational `proof.v` model *itself* still uses
  plain integer rows (`rotated_row = row + offset`, no `row mod nb_rows` wrap,
  no `nb_rows`), and `satisfies_gates` still quantifies over all
  `(region, row)` rather than each region's actual extent; folding the finite
  domain back into the relational reading — and the
  tables-as-fixed-column-prefixes coherence of the lookup-table work (the
  refinement noted at the end of [Tying lookups to the loaded
  table](#tying-lookups-to-the-loaded-table-initlookuptables)) — is still
  open.
- **Selector-off closure for short lookups** (item 2). The range-check
  chip's `LookupArgument` is now consumed (`RangeTable.word_sound` /
  `short_word_sound`, used by the var-base-mul overflow and base-field
  canonicity lookups — see item 2), but the short-lookup form needs an
  explicit `q_running = 0` hypothesis because the fact model asserts only
  the `SelectorOn` points. The default-0 selector model — the same
  well-formedness fact as the completeness gap above — now exists in the
  completeness direction as the `honest_planes` selector plane (the
  enabled-point indicator, 0 off the enabled points), consumed by
  `Complete.circuit_holds_intro`. It is not yet propagated back into the
  soundness lemmas: the short-lookup form still carries its `q_running = 0`
  hypothesis explicitly, and folding the default-0 model into the soundness
  side (so the named short-lookup witness-honesty conditions discharge
  automatically) remains open.

## Bottom line

For per-region gate determinism and soundness arguments, the model is
faithful and the gadget proofs are legitimate. As a model of a whole Rust
Halo2 chip it is not yet fully faithful: it idealizes the floor planner into
independent per-region coordinate spaces and drops the cyclic/blinding-row
structure. Within the relational model, the layouter-level constants
mechanism is modeled and validated, lookups have a `Prop` value model tied to
the loaded table with a first end-to-end soundness proof
(`GeneratorTable.sound`), and the synthesis-to-gates predicate
(`circuit_holds`) glues the synthesis layer to the gate layer for the
determinism-bearing gadgets. On top of this model, the whole-circuit Orchard
action determinism development — see `docs/orchard-soundness-proof.md`
where present — carries two residual named witness-honesty hypotheses
(`merkle_witness_ok`, `note_commit_witness_ok`): short-lookup range facts
that the relational selector model leaves free at `q_running = 0` rows, and
Sinsemilla incomplete-add nondegeneracy. The faithful operational counterpart
in `serialize.v` is connected to the relational model by the generic
event-replay bridge (`operational_sound`/`operational_complete`,
`Halo2/realize/sound.v`), instantiated on the whole Orchard action circuit
with its concrete placement and constants tail
(`Orchard/circuit_operational.v`), so the action surface's `Holds`
hypothesis follows from mock-prover acceptance of the serialized circuit;
the remaining open gaps above are the exact trust boundary.
