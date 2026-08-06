# The Orchard compilation-correctness layer: what keygen does, and why the Rocq circuit is the Rust one

Companion to [`orchard-soundness-proof.md`](orchard-soundness-proof.md) (the
Action statement) and [`orchard-completeness-proof.md`](orchard-completeness-proof.md)
(honest witnesses are accepted). Those two document *what is proved about the
circuit*. This one documents the layer underneath them: the modelled Halo 2
**keygen**, which turns the configured circuit into the plonkish system a
verifier actually checks, and the certificates that identify that system with
the deployed Orchard verifying key.

Two questions motivate it, and each gets its own section below.

1. **What do the theorems say about Orchard and Halo 2, and what does this
   layer add to that claim?** Short answer: it moves the hypothesis of the
   Action statement off the idealized relational model and onto the objects
   the deployed verifier operates on — a compiled system on the real cyclic
   2048-row domain, then polynomial identities over that domain. See
   [What this proves about Orchard and Halo 2](#what-this-proves-about-orchard-and-halo-2).
2. **Why should anyone believe the circuit in Rocq is the circuit in Rust?**
   Short answer: not because the translation was verified — it was not — but
   because the modelled keygen is bracketed at both ends. Its *inputs* (the
   configure system and the 19,679-event synthesis trace) are compared with
   the Rust implementation as JSON, and its *output* reproduces the deployed
   verifying key's description byte for byte. See
   [Why the Rocq circuit is the Rust circuit](#why-the-rocq-circuit-is-the-rust-circuit),
   and in particular
   [The refinement from the JSON comparison to the vk](#the-refinement-from-the-json-comparison-to-the-vk).

## Where the layer sits

The refinement ladder, top to bottom:

| | Layer | Object | Where |
|---|---|---|---|
| | Action statement | § 4.18.4 conditions on read-back inputs | `Orchard/circuit_proof/` |
| | Relational satisfaction | `circuit_holds` over `Assignment.t` | `Halo2/proof.v` |
| L3 | Operational replay | `mock_prover_accepts` over a raw event grid | `Halo2/realize/` |
| **L2** | **Compiled plonkish** | **`CompiledSystem.t` on the cyclic domain** | **`Halo2/plonkish/`, `Orchard/compiled/`** |
| **L1** | **Polynomial identities** | **vanishing quotient + grand products** | **`Halo2/plonkish/algebraic.v`** |
| L0 | Proof system | commitments, IPA, Fiat–Shamir | named hypotheses only |

The L-numbering is the one used in
[`operational-soundness.md`](operational-soundness.md). L2 and L1 are this
document. L3 and the two unnumbered rows above it are the companions; L0 is
recorded as named hypotheses in `Halo2/plonkish/boundary.v` and is *not*
proved.

## What keygen actually does

`Halo2/plonkish/main.v` models the compilation step over the indexed
constraint system of `serialize.v`. It is a port, not an invention: the
selector packing follows `halo2_proofs/src/plonk/circuit/compress_selectors.rs`
(`process`) and its caller `ConstraintSystem::compress_selectors`, and the
permutation follows `halo2_proofs/src/plonk/permutation/keygen.rs`
(`Assembly::copy`). Concrete Orchard figures below are computed from the
model, then compared with the deployed description.

### Configure metadata

Gates and lookups are not all that Halo 2's `configure` method records. The
builder also retains allocation counts, selector kinds, first-query order,
equality-enabled columns, constants columns, and an optional minimum degree.
Those fields affect `vk.pinned()` even when they do not affect the relational
meaning of a gate.

`Halo2/main.v` therefore gives the free configure language a typed metadata
operation. `Orchard/configure_metadata.v` supplies an explicit formal trace
of those operations in Orchard's builder order, and
`Orchard/compiled/configuration.v` interprets it with the same ordered
deduplication as `ConstraintSystem`. This trace is not reconstructed from the
gate/lookup AST alone: its parity with Rust's builder operations is the
external configure-JSON check described below. It is nevertheless distinct
from the deployed VK targets and is the actual compiler input used by the
kernel-checked provenance theorem. The resulting state is checked as valid
and derives:

- 14 pre-compression fixed columns, 10 advice columns, one instance column,
  and 56 selectors;
- complex selectors `QLookup`, `QRunning`, `QSinsemilla1_1`, and
  `QSinsemilla1_2` (numeric selectors `[2; 3; 25; 29]`), with all other
  selectors simple;
- lookup-table fixed columns 0, 1, and 2;
- equality-enabled columns in exact order: instance 0, advice 0 through 9,
  then fixed 3, 8, 9, and 10;
- constants `[3]`; and
- `minimum_degree = None`.

`Compile.compile_from_metadata` consumes this derived state. The deployed
literals in `compiled/pinned.v` are comparison targets, not arguments to the
compiler.

### The cyclic domain

`Domain.t` fixes `k` and derives `n = 2^k`, rotation as addition mod `n`, and
the row predicates `l_0` / `l_last` / `l_blind`. Rows split as

```
[0, usable_rows)      the circuit          usable_rows = n − (blinding_factors + 1)
 usable_rows          the spare l_last row
(usable_rows, n)      blinding rows
```

For Orchard: the deployment selects `k = 11`, hence `n = 2048`;
`blinding_factors = 5` and `usable_rows = 2042`, so rows 2042 through 2047
carry no circuit content. `blinding_factors` is itself derived, as in Rust:
the maximum number of distinct rotations at which one advice column is
queried (at least 3), plus one multiopen evaluation, plus one spare.

This is the first place the model stops idealizing. The relational layer (L4)
quantifies gates over ℤ with regions as independent address spaces; from L2
down, everything lives on the finite wrap-around domain with the blinding tail
reserved, which is what the verifier sees.

### Selector compression

Halo 2 does not keep one fixed column per selector. `Compress.process` sorts
the selectors into two classes:

- **degree-0 selectors** — complex ones, or ones appearing in no gate — each
  get their own plain 0/1 fixed column;
- **simple selectors** — packed greedily into shared *combination* columns
  under a degree budget, one column holding several mutually
  row-disjoint selectors, each identified by a 1-based *assigned root*.

A packed selector `s` with root `v` in a combination of length `L`, queried
through `q`, is substituted out of every gate by its **indicator polynomial**

```
q · ∏ { (r − q) : r ∈ [1, L], r ≠ v }
```

which is a nonzero constant where the column reads `v`, and `0` where it reads
`0` or any other member's root. The compiled gates then contain no
`Expression.Selector` leaf at all — `CompiledSystem.selector_free_b`.

Orchard: **56 selectors**, whose kinds come from the configure trace. The
four complex selectors `[2; 3; 25; 29]` take a column each, while the **52**
simple selectors are packed into the remaining 11, giving **15 combination
columns** in total. Thus the configure-derived 14 base fixed columns become
**29** after compression. Gate count: **193**. System degree: **9**.

The correctness statement is deliberately *allocation-independent*: no theorem
mentions which combination column a selector landed in. The hypotheses
constrain the compiled output as a whole (the grid agrees with the combination
values; each assignment's expression tracks its selector's activations), and
hold for any packing. Only the parity certificates pin the concrete Rust
choices — which is what makes them meaningful rather than circular.

### The permutation σ

Equality constraints are `Copy` obligations in the event stream.
`Sigma.sigma_of_copies` closes them into an explicit permutation of the
equality-enabled cell set, by weighted union with an explicit cycle-relabeling
walk — the port of `Assembly::copy`. Orchard replays **19,679 events**, of
which **3,004** are copies, over **15 permutation columns** × 2048 rows.

The construction maintains an invariant (`assembly_inv`) recording that the
result is an injective self-map of the cell domain, constant on orbits. Grid
invariance under σ is then equivalent to all the copy equalities holding:
`sigma_correct`.

### Lookup input substitution

Lookup inputs mention selectors too, so compilation substitutes them the same
way. `Halo2/plonkish/lookup_compile.v` proves the substitution
value-preserving, so acceptance's lookup conjunct can be read on either the
indexed selector-carrying system or the compiled one
(`plonkish_accepts_compiled_iff`). Orchard has **3** lookup arguments over a
1024-row table.

### Query tables

Halo 2 assigns a `query_index` on the first registration of each distinct
column/rotation pair, so equality as sets is insufficient. The configure
metadata interpreter retains that order exactly. Orchard's 25 advice queries
are

```text
(A0,0), ..., (A9,0),
(A9,+1), (A9,-1), (A2,+1), (A3,+1), (A4,+1), (A5,+1),
(A0,+1), (A1,+1), (A7,+1), (A8,+1),
(A6,-1), (A1,-1), (A6,+1), (A7,-1), (A8,-1)
```

The 14 base fixed queries are

```text
(3,0), (0,0), (11,0), (4,0), (5,0), (6,0), (7,0),
(8,0), (9,0), (10,0), (12,0), (1,0), (2,0), (13,0)
```

and selector compression appends `(14,0)` through `(28,0)`, for **29 fixed
queries** total. The single instance query is `(0,0)`. The three query
certificates now prove sequence equality with the deployed keygen order, and
the printer resolves every leaf's `query_index` against these derived lists.

### Evaluation-domain presentation fields

`Orchard/vk/setup.v` executes the relevant `EvaluationDomain::new` sizing and
root schedules. The configured minimum degree is unset, the compiled system
degree is 9, and the selected `k` is 11; the least fitting extended-domain
exponent is therefore 14. The certificate checks both that exponent 14 fits
`2^11 * (9 - 1)` coefficients and that exponent 13 does not. It derives
`omega` by the two Rust repeated-squaring loops from the Pasta root of unity,
and renders the base/scalar modulus strings from Garden's Vesta field
definitions. The deployed domain and modulus literals are equality targets,
not printer inputs. The optimized commitment layer retains checked
`PolyDomain.omega`, `VkMsm.omega_inv`, and `VkMsm.n_inv` caches for feasible
reduction. The full certificate explicitly proves that the latter two are
inverses of the setup-derived root and domain size; it also exposes the Pasta
generator schedule for the permutation-label `delta`.

## The correctness theorems

- **`compile_correct`** (`plonkish/compile.v`) — for a grid whose selector
  planes are boolean and `0` off the program-enabled points, the compiled gate
  polynomials vanish on every row of `[0, n)` **exactly when** the original
  selector-gated gates hold on the usable-row prefix. Two families carry it:
  indicator-polynomial evaluation (on/off/other-root), and blinding-row
  vacuity — off the usable rows every selector is disabled and every
  combination column reads `0`, so both sides vanish there.
  `compile_correct_domain` restates the original side over the full domain.
- **`sigma_correct`** (`plonkish/sigma.v`) — grid invariance under the closed
  assembly ↔ every copy obligation holds.
- **`plonkish_of_mock_prover`** (`plonkish/mock.v`) — acceptance by the ideal
  all-integer-rows checker ↔ satisfaction restricted to `[0, n)`, under the
  decidable `finite_domain_ok_b` layout checks.

All three are **equivalences**, which is why both directions compose. At the
whole circuit (`Orchard/compiled/main.v`), `orchard_compiled_accepts` bundles
the three conjuncts — compiled gates vanish on the installed grid, the lookup
arguments hold on every domain row, the grid is σ-invariant — and

```coq
Theorem orchard_compiled_sound    : replayed grid -> orchard_compiled_accepts g -> mock_prover_accepts …
Theorem orchard_compiled_complete : replayed grid -> mock_prover_accepts … -> orchard_compiled_accepts g
```

close the L3 ↔ L2 arrow in both directions. `Orchard/compiled/algebraic.v`
does the same for L2 ↔ L1 (`orchard_algebraic_sound` /
`orchard_algebraic_complete`), and `orchard_algebraic_action_statement` runs
the whole ladder down to the § 4.18.4 surface.

Every decidable premise on the concrete instance is a `vm_compute`
certificate: the activation bound, selector vacuity, the per-assignment
indicator check (sharded four ways — the whole scan costs ≈ 78 s), the
finite-domain layout bundle, the σ-construction success, and the resolvability
of every copy cell.

## What this proves about Orchard and Halo 2

The Action statement (`orchard_action_statement`) has always had the shape
*"if the circuit is satisfied, the witnessed values satisfy § 4.18.4"*. The
question is what "satisfied" means, and that is what this layer changes.

**Before.** `Holds Γ` — satisfaction of the *relational* model, in which
regions are independent integer address spaces, gates are quantified over ℤ
rather than a wrap-around domain, and blinding rows do not exist. A reader
could reasonably ask whether a real Halo 2 verifier accepting a proof has
anything to do with that predicate.

**Now.** The same conclusion follows from `orchard_algebraic_accepts_regular`:
the vanishing quotient for the 193 compiled gate polynomials, the four
permutation product rules against the σ of the actual copy obligations, and
the five lookup rules — over the cyclic 2048-row domain, on the compiled
system, with selectors compressed exactly as keygen compresses them. Those are
the identities the deployed verifier checks. The chain

```
algebraic acceptance → compiled satisfaction → mock_prover_accepts
                     → circuit_holds → § 4.18.4 Action statement
```

is machine-checked end to end, with no axioms beyond `PrimString.string` and
impredicative `Set`.

**Both directions hold**, which matters for how much the claim is worth. A
soundness theorem whose hypothesis is unsatisfiable proves nothing;
`orchard_honest_algebraic_accepts_ex` exhibits an honest witness satisfying
the L1 acceptance predicate outright, so the hypothesis is inhabited. See
[`orchard-completeness-proof.md`](orchard-completeness-proof.md) for the
domain of "honest" and for why the permutation conjunct is read at *regular*
challenges (at the excluded ones the running-product recurrence divides by
zero, so no prover has a product column there either).

**What it does not add.** L0 is untouched. That a verifier accepting a Halo 2
*proof* implies the identities hold at the challenge point is a property of
the commitment scheme and the transcript, not of the circuit. The residual
content is named — not axiomatized — in `plonkish/boundary.v` as `IPABinding`,
`MultiopenReduction` and `FiatShamirChallengeGood`, together with the in-model
part that *is* proved: by the counting lemmas of `plonkish/counting.v`,
acceptance at a single challenge tuple outside three cardinality-bounded bad
sets already yields the full satisfaction triple
(`algebraic_sound_at_challenge`). Cryptographic soundness of Sinsemilla,
Poseidon and the commitments remains outside, as recorded in
[`orchard-soundness-proof.md`](orchard-soundness-proof.md).

## Why the Rocq circuit is the Rust circuit

This is the faithfulness question, and it deserves a blunt answer first.

**The translation is not verified.** The Orchard chips and gadgets were
transcribed from Rust into Rocq by hand, following the conventions in
[`halo2-translation.md`](halo2-translation.md). Nothing machine-checks that
transcription against the Rust source, and no theorem in the development
could: the Rust source is not an object the proof assistant can see.

What the development provides instead is **translation validation**, at *both
ends of the compiler*. Two independent comparisons against the Rust
implementation bracket the modelled keygen:

- at the **input** end, a structural JSON comparison of the configure-time
  constraint system and the synthesis event trace;
- at the **output** end, a byte-exact comparison of the compiled verifying-key
  description.

The two are not alternatives, and they are not the same check at different
resolutions. They cover complementary objects, they are checked by different
means, and a `Qed` lemma joins them. That chain is the subject of the next
subsection; the certificates themselves follow it.

### The refinement from the JSON comparison to the vk

The chain has three links:

```
Rust configure  ≟  model configure + metadata ──┐
    (structural JSON diff)                      │
                                                ├─ compile_from_metadata ─> compiled system
Rust synthesis  ≟  synthesize_events ──────────┘                         │
    (exact JSON event stream)                                             │ vk/print.v
                                                                          ▼
                                      printed vk.pinned()  ≟  circuit_description_post_nu6_3
                                                           (T1, byte-exact, in-kernel)
```

**Link 1 — the JSON comparison pins the compiler's inputs.** Halo 2 keygen
consumes exactly two things from the circuit: the configure-time constraint
system, and the synthesis trace (from which the selector activations and the
copy obligations are read). Both are exported from the Rocq model by OCaml
extraction (`Orchard/circuit_synthesis_json_extract.v`, kept out of the build
by `blacklist.txt` and run through `make orchard-json-from-model`) and
compared against snapshots the Rust side emits from two ignored Orchard tests:

| | Rocq object | Rust snapshot | Result |
|---|---|---|---|
| configure relation | `model_configure` — 55 gates, 3 lookups | `circuit_configure_generated_from_implementation.json` | structural JSON comparison |
| configure keygen metadata | `model_configure_metadata` | `action_circuit.highlevel.json` plus `circuit_selector_compression_generated_from_implementation.json` | counts, selector kinds, lookup allocations, ordered queries, equality columns, constants, and minimum degree |
| synthesis | `model_synthesis_events` — 19,679 events | `circuit_synthesis_generated_from_implementation.json` | exact event-stream comparison |

Run by `make orchard-configure-json-compare` and
`make orchard-synthesis-json-compare`, whose comparators
(`scripts/compare_orchard_*.py`) normalize the configure formatting. The
metadata comparison reconstructs the Rust-side view from the high-level
configure snapshot and selector-compression assignments; it is deliberately
separate from the in-kernel certificate described below.

**Link 2 — the exported objects are the compiler's inputs, in the kernel.**
This is what makes the two ends one chain rather than two unrelated tests. The
objects the extraction exports are the objects the compilation stack compiles:

- `orchard_indexed_system`, the system `Compile.compile_from_metadata` is
  applied to, is
  `Configure.to_indexed Index.indices (𝓒.run_unit circuit.configure
  ConstraintSystem.empty)` — syntactically the extraction's `model_configure`;
- `OrchardConfigure.state` is
  `𝓒.run_metadata_unit … circuit.configure Metadata.State.empty` — exactly
  the extraction's `model_configure_metadata`; and
- `orchard_events`, the stream the selector activations and copies are read
  off, is `orchard_synthesis_events ++ orchard_constants_events` (19,315 +
  364), and `orchard_events_synthesize_events` — a `Qed` lemma in
  `circuit_operational.v` — proves it equal to
  `circuit.synthesize_events Index.indices`, the extraction's
  `model_synthesis_events`.

So the JSON evidence attaches to the very terms the rest of this document
reasons about; it is not evidence about a parallel artifact.

**Link 3 — T1 pins the compiler's output**, byte for byte, as described under
[The byte-level anchor](#the-byte-level-anchor) below.

**Why both links are needed.** Neither end subsumes the other:

- the configure comparison covers the builder metadata, but it remains an
  external translation-validation check; the in-kernel configure interpreter
  and vk certificates are what prevent those values from being silently
  passed through from the deployed target;
- the vk describes the constraint system only. `vk.pinned()` says nothing
  about *synthesis*, so no amount of byte-parity there can witness that the
  Rocq circuit writes the cells the Rust circuit writes. The 19,679-event
  synthesis snapshot is the only direct evidence of that, and it is exact.

**Trust status differs sharply between the two ends, and the difference
matters.** T1 is a kernel-checked conversion. The JSON comparison is *not*
kernel-checked: it trusts the OCaml extraction, the hand-written driver
(`scripts/orchard_synthesis_json.ml`), the Rust generators and the Python
comparators, none of which appear in any `Print Assumptions` output. Both
comparisons must be rerun after changes to the configure or synthesis model;
the documentation does not treat a `.vos` build as evidence that they pass.

The two ends also differ in how they age. The vk certificates are `.vo`
proofs, so they cannot fall silently out of date: a circuit change that would
invalidate them breaks the build. The JSON snapshots are committed artifacts,
so they carry evidence only as of the last time they were regenerated —
`make orchard-json-from-model` followed by the two compare targets is what
re-establishes them after any change to the Rocq circuit.

The in-kernel counterpart on the synthesis side, which *is* audited, is
narrower: `Orchard/circuit_synthesis_layout.v` imports the Rust-generated V1
floor-planner region starts as Rocq literals, and the replay and placement
certificates (`orchard_replay_ok` and the `circuit_operational` machinery)
check the model against them. That pins the *placement*; the equality of the
event traces themselves rests on the JSON diff.

### The component certificates

`Orchard/compiled/certificate.v` packages the closed checks on
`Compile.compile_from_metadata` applied to Garden's own
`orchard_indexed_system`. The deployed data in `compiled/pinned.v` appears
only on the right-hand side:

- `configure_state_valid` and `configure_counts_match` check the typed
  allocation trace and its 14 fixed / 10 advice / 1 instance / 56 selector
  counts;
- `gate_polynomials_match` checks all **193** compiled polynomials, including
  selector-indicator factors, while `gate_count_match`,
  `combination_count_match`, `selector_assignments_cover`, and
  `compiled_selector_free` check the packing shape and complete selector
  elimination;
- `advice_queries_match`, `fixed_queries_match`, and
  `instance_queries_match` prove **exact sequence equality** for all 25 / 29 /
  1 query entries, hence determine every printed `query_index`;
- `permutation_columns_match` proves equality of the complete ordered
  configure-derived list — instance 0, advice 0 through 9, fixed 3, 8, 9,
  and 10 — rather than inferring only the subset used by synthesis copies;
- `configure_constants_match` and `minimum_degree_match` derive `[3]` and
  `None`; the independent `constants_column_match` and
  `copy_columns_in_permutation` checks connect those configure choices with
  the concrete synthesis stream; and
- `lookup_inputs_match` and `lookup_tables_match` check the three compiled
  lookup arguments, including allocation of their table columns.

There is no longer a permutation/constants pass-through boundary. Fixed
columns 8, 9, and 10 illustrate why the configure trace is necessary: they
are equality-enabled even though synthesis never copies them, so the event
stream alone could establish only inclusion.

The compact gate checker still fingerprints a top-level product as its factor
sequence, which is sufficient for polynomial parity. Separately, the formal
constraint AST now has a precise either-zero node whose serialization is the
deployed left-associated product tree. `vk/print.v` prints the compiled gates
directly — no `rotate_top` or printer-only reassociation — and the byte-level
T1 check below establishes exact AST presentation parity.

### The byte-level anchor

The component certificates compare against *transcribed literals*, which
leaves the transcription itself as trusted input. `Orchard/vk/` removes that:

- **T1, `vk_pinned_dump_parity`** — a verified in-model printer, run over the
  metadata-derived compiled system, setup/domain computation, and an explicit
  commitment-coordinate input, reproduces
  `orchard/src/circuit_data/circuit_description_post_nu6_3` — the
  `format!("{:#?}\n", vk.pinned())` dump the Orchard test suite asserts
  against the deployed key — **byte for byte, all 1,285,701 bytes**. Since the
  non-commitment bytes are *produced from the configure and setup
  computations*, this certifies the exact gate AST, ordered query tables,
  permutation columns, lookup arguments, constants, counts, moduli, and
  domain values as presented bytes. The generated full certificate
  instantiates this printer with 44 explicit MSM-coordinate witnesses and
  proves both that they equal the deployed point literals and, transitively,
  that they denote the mathematical `commit_lagrange` results. The emitter
  and independent Python oracle recompute those witness literals, but that
  generator-level independence is outside the kernel trust path.
- **T2, `transcript_repr_spec`** — the verifying key's Fiat–Shamir binding
  scalar computed in-model: BLAKE2b-512, personalized `"Halo2-Verify-Key"`,
  over `le64(len s) ‖ s` for the compact rendering `s` of the same printer,
  reduced into the Pallas base field. This is the value the deployed verifier
  absorbs before any proof data, binding every challenge to the pinned
  description.

So the trust chain for faithfulness reads:

```
Rocq circuit --compile--> printed description  ==  circuit_description_post_nu6_3  ==  Post-NU6.3 vk
                          \____________ T1, machine-checked _____________/   \__ Orchard's own test __/
```

We discharge the first link. The second is asserted by the Orchard repository's
test suite, not by us.

### What the anchor reaches, and what it does not

**Reaches.** The certificates cover every field that feeds `vk.pinned()`, with
the following provenance split:

- **Configure- and compiler-derived fields:** all column and selector counts,
  selector kinds and compression assignments, the exact gate AST and lookup
  expressions, ordered query tables, complete permutation-column order,
  constants, and `minimum_degree`. A hand-translation error in a gate, query,
  equality enable, or allocation changes the derived description and breaks a
  certificate or T1.
- **Setup-derived fields:** `extended_k`, `omega`, and both modulus strings are
  computed from the chosen Vesta curve, `k = 11`, and compiled degree 9. The
  setup certificate connects the lightweight domain calculation to the actual
  compiled system degree.
- **Commitment coordinates with mathematical provenance:** the 29 fixed and
  15 permutation coordinate witnesses are emitted from the recomputed MSM
  results, assembled as
  `OrchardVkProvenance.derived_commitment_coordinates`, and checked equal to
  the deployed literals in `vk/data.v`. In addition,
  `OrchardVkProvenance.orchard_vk_commit_lagrange_refined` proves
  `OrchardVkAbstract.certificate` with no theorem premises. Its fields
  establish `VkMsm.params_well_formed` and, at every valid index, equality
  between `VkMsm.commit_lagrange` applied to
  `VkCommitmentColumns.fixed_values` or
  `VkCommitmentColumns.permutation_values` and the corresponding
  `VkPinnedSpec` point. `VkMsmRefinement.assemble_halves_commit_lagrange_sound`
  and `VkCommitmentRefinement.certificate_abstract_sound` connect the
  optimized inverse FFT, split Jacobian Pippenger MSM, and default blind
  `[1]w` to those equalities.
  `VkCommitmentColumnsCorrect.fixed_values_compiled_grid` identifies the fixed
  inputs with the compiled grid after `with_combinations` for every successful
  Orchard event replay. The permutation inputs use
  `OrchardCompiled.orchard_sigma`, which `OrchardCompiled.orchard_sigma_eq`
  derives from the copy obligations over the configure-derived complete
  permutation list. The generated
  `orchard_vk_commitments_derived` package bundles the fixed-column replay,
  domain, sigma, SRS, and executable commitment certificates. The separate
  `orchard_vk_commit_lagrange_refined` theorem consumes the latter four
  certificate families to prove `OrchardVkAbstract.certificate`; the fixed
  replay result is part of the provenance graph and is explicitly packaged in
  the full public certificate (together with synthesis/compiled-domain
  usable-row equality), although it is not a field of the narrower abstract
  commitment record. See
  [`orchard-vk-provenance.md`](orchard-vk-provenance.md).
  The generated `orchard_vk_fully_derived` theorem combines this record with
  setup, compiled-system, T1, and T2 certificates in
  `OrchardVkFullAbstract.certificate`. Its T1 and T2 statements use the
  printer instantiated with `derived_commitment_coordinates`, not a printer
  definition whose commitment inputs are fixed to `VkPinnedData`; T2 prefixes
  the actual computed compact-rendering length. The independent Python
  recomputation of the emitted coordinates remains a diagnostic outside the
  kernel, while the kernel theorem connects each explicit witness to
  `commit_lagrange` transitively through the deployed equality target.

**Does not reach:**

- **The witness side.** `vk.pinned()` describes the constraint system, not
  synthesis. That the Rocq synthesis writes the cells the Rust one writes is
  carried by the other end of the chain — the byte-identical 19,679-event
  synthesis snapshot of
  [the JSON link](#the-refinement-from-the-json-comparison-to-the-vk), which
  is *not* kernel-checked — together with the in-kernel event-replay bridge of
  [`operational-soundness.md`](operational-soundness.md) over the imported
  floor-planner placement.
- **An independent protocol specification selecting this configuration.** The
  configure trace now derives the complete fixed and permutation column
  choices and order. What remains a modeling choice is Garden's formal
  Orchard circuit itself, together with Vesta and `k = 11`. Equality of that
  formal configure/synthesis program with Rust is translation validation by
  the external JSON comparisons, not a theorem about Rust semantics.
- **Anything the dump omits.** Two circuits agreeing on `vk.pinned()` agree on
  everything a verifier is configured by, but the dump is a description, not a
  denotation — it is evidence of agreement, not a proof of it.

## Assumption audit

`Print Assumptions` must run against full `.vo` builds. The named results have
the following profiles:

- Most circuit and compilation theorems report `PrimString.string : Set` and
  impredicative `Set`. Several plonkish lemmas are closed under the global
  context.
- T1 additionally reports `PrimString.make` and `PrimString.cat`. T2 reports
  twelve primitive-interface assumptions in total: `PrimString.string` plus
  eleven `PrimString` / `PrimInt63` operations, including the BLAKE2b word
  arithmetic.
- `OrchardVkProvenance.orchard_vk_commit_lagrange_refined`, after
  `make -C Garden orchard-vk-provenance`, reports 48 Rocq primitive-interface
  declarations from Corelib and Stdlib:
  `PrimString.string`; `PrimInt63.int`, 17 primitive operations and 19
  `Uint63Axioms` laws; and `PrimArray.array`, four primitive operations and
  five `ArrayAxioms` laws. The explicit provenance target is required because
  ordinary `make -C Garden` omits the generated certificate modules.

The last profile is Rocq's primitive integer and array interface used by the
five-word Montgomery arithmetic and linearly threaded arrays. It contains no
Garden-specific axiom. The theorem has no premises: `VkMsm.params_well_formed`
and all 44 equalities in `OrchardVkAbstract.certificate` are discharged by the
sharded closed computational certificates (currently using
`vm_cast_no_check`). Generated coefficients, SRS witnesses,
projective partial sums, and domain tables are data inside those closed
propositions, not logical premises of the aggregate theorem.

The generated `orchard_vk_fully_derived` theorem is also premise-free and
adds the hand-written setup, configure/compilation, T1, and T2 records to that
commitment result. After the complete four-worker `.vo` provenance replay on
2026-08-05, `Print Assumptions
OrchardVkProvenance.orchard_vk_fully_derived` reported 52 standard
Rocq/Corelib/Stdlib primitive-interface declarations: the 48 commitment
interfaces itemized above plus `PrimString.make`, `PrimString.length`,
`PrimString.get`, and `PrimString.cat`, together with the configured
impredicative `Set`. It introduced no Garden-specific or classical axiom. A
`.vos` development build would not establish this audit.

The L0 names `IPABinding`, `MultiopenReduction`, and
`FiatShamirChallengeGood` are definitions taken as explicit premises where
used, so they do not appear in `Print Assumptions`. There is no `Admitted`,
`Axiom`, or `admit` declaration under `Garden/Halo2/` or `Garden/Orchard/`.
