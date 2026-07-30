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
(`Assembly::copy`). Concrete Orchard figures below are `vm_compute`d from the
model, not quoted.

### The cyclic domain

`Domain.t` fixes `k` and derives `n = 2^k`, rotation as addition mod `n`, and
the row predicates `l_0` / `l_last` / `l_blind`. Rows split as

```
[0, usable_rows)      the circuit          usable_rows = n − (blinding_factors + 1)
 usable_rows          the spare l_last row
(usable_rows, n)      blinding rows
```

For Orchard: `k = 11`, `n = 2048`, `blinding_factors = 5`, `usable_rows = 2042`,
so rows 2042 through 2047 carry no circuit content. `blinding_factors` is
itself derived, as in Rust: the maximum number of distinct rotations at which
one advice column is queried (at least 3), plus one multiopen evaluation, plus
one spare.

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

Orchard: **56 selectors**, of which **4** take a column each — the complex
ones, `[2; 3; 25; 29]`, which `process` sees as degree-0 — and **52** are
packed into the remaining 11, giving **15 combination columns** in total, so
14 base fixed columns become **29** after compression. Gate count: **193**.
System degree: **9**.

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

`Queries.t` collects the rotations at which each column is read: Orchard ends
with **25 advice / 29 fixed / 1 instance** queries. The model collects them in
gate order and the deployed keygen in configure order, so the parity
certificate compares them as *sets* plus length, not as sequences.

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
   Rust configure   ≟   model_configure ─────────┐
        (structural JSON diff)                   │
                                                 ├─ Compile.compile ─> compiled system
   Rust synthesis   ≟   synthesize_events ───────┘          │
        (byte-identical JSON)                               │  vk/print.v
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
| configure | `model_configure` — 55 gates, 3 lookups | `circuit_configure_generated_from_implementation.json` | **structurally identical**; the files differ in whitespace only (121,960 vs 118,360 bytes), and compare equal as JSON |
| synthesis | `model_synthesis_events` — 19,679 events | `circuit_synthesis_generated_from_implementation.json` | **byte-identical**, 2,477,271 bytes each |

Run by `make orchard-configure-json-compare` and
`make orchard-synthesis-json-compare`, whose comparators
(`scripts/compare_orchard_*.py`) normalize the configure formatting. The
configure JSON deliberately carries *only* gates and lookups — no query
tables, permutation columns, constants column or minimum degree.

**Link 2 — the exported objects are the compiler's inputs, in the kernel.**
This is what makes the two ends one chain rather than two unrelated tests. The
objects the extraction exports are the objects the compilation stack compiles:

- `orchard_indexed_system`, the system `Compile.compile` is applied to, is
  `Configure.to_indexed Index.indices (𝓒.run_unit circuit.configure
  ConstraintSystem.empty)` — syntactically the extraction's `model_configure`;
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

- the configure JSON omits the metadata Halo 2 derives — query tables, the
  permutation and constants columns, `minimum_degree`, the domain constants —
  which is what the vk end addresses (with the pass-through caveat recorded
  under [The component certificates](#the-component-certificates));
- the vk describes the constraint system only. `vk.pinned()` says nothing
  about *synthesis*, so no amount of byte-parity there can witness that the
  Rocq circuit writes the cells the Rust circuit writes. The 19,679-event
  synthesis snapshot is the only direct evidence of that, and it is exact.

**Trust status differs sharply between the two ends, and the difference
matters.** T1 is a kernel-checked conversion. The JSON comparison is *not*
kernel-checked: it trusts the OCaml extraction, the hand-written driver
(`scripts/orchard_synthesis_json.ml`), the Rust generators and the Python
comparators, none of which appear in any `Print Assumptions` output. Both
comparisons pass on the committed snapshots as of this writing.

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

`Orchard/compiled/check.v` proves twelve `vm_compute` certificates comparing
`Compile.compile` applied to the model's own `orchard_indexed_system` against
`compiled/pinned.v`, transcribed from the deployed key:

- `gate_polynomials_match` — all **193** compiled gate polynomials, *including
  the selector-indicator factors*. This is the strongest of the twelve: since
  the indicators encode which combination column and which root each selector
  received, matching them pins the entire 56-selector → column assignment
  wherever a selector occurs;
- `gate_count_match` (193), `combination_count_match` (15, hence 29 fixed
  columns), `selector_assignments_cover` (all 56 selectors assigned),
  `compiled_selector_free` (no selector survives in a gate);
- `advice_queries_match` / `fixed_queries_match` / `instance_queries_match`
  (25 / 29 / 1, as set equality plus length);
- `lookup_inputs_match` / `lookup_tables_match` — the three lookup arguments,
  input and table expressions pairwise;
- `constants_column_match` — the constants columns *derived from the event
  stream* (the distinct fixed columns the floor planner's constants tail
  writes) equal the pinned `[3]`;
- `copy_columns_in_permutation` — every column carrying an equality copy in
  the stream is among the pinned permutation columns. **Inclusion, not
  equality**: fixed columns 8, 9 and 10 are equality-enabled but never copied
  by synthesis, so the full 15-column list cannot be recovered from the
  stream.

**Two fields are pass-through, and the source says so.** The model's
`ConstraintSystem.t` does not carry the permutation column list or the
constants column, so `Compile.compile` is *given* them from the pinned
description. Those two fields of `compiled` are therefore not parity evidence
— comparing them against the pinned data would be circular. What covers them
instead are the two stream-derived cross-checks just listed: an equality for
the constants column, and only an inclusion for the permutation columns.

Comparison is by expression fingerprint: the top-level product chain flattened
into factors, each serialized preorder. The flattening absorbs a product
re-association between the model's gate builder and the deployed one (it
affects two gates); every other node — rotations and canonical field constants
included — is compared exactly.

### The byte-level anchor

The twelve certificates compare against *transcribed literals*, which leaves
the transcription itself as trusted input. `Orchard/vk/` removes that:

- **T1, `vk_pinned_dump_parity`** — a verified in-model printer, run over the
  compiled system and the pinned literals, reproduces
  `orchard/src/circuit_data/circuit_description_post_nu6_3` — the
  `format!("{:#?}\n", vk.pinned())` dump the Orchard test suite asserts
  against the deployed key — **byte for byte, all 1,285,701 bytes**. Since the
  printed bytes are *produced from the model's compiled system*, this certifies
  the gate polynomials, query tables, permutation columns, lookup arguments,
  constants column and domain constants as bytes, and simultaneously retires
  the offline-transcription trust in the literal files.
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

**Reaches.** Anything that feeds `vk.pinned()` — but the certificate is only
as strong as the provenance of what is printed, and that splits in two:

- **Computed by the model, hence genuine parity evidence**: every gate
  polynomial, the selector compression (through the indicator factors), the
  query tables, the lookup argument expressions, and the constants column. A
  hand-translation error in a gate — a wrong rotation, a dropped term, a
  swapped constant — changes a gate polynomial and therefore changes the dump.
- **Pinned literals passed through the printer**: the permutation column
  list, the 44 commitment coordinate pairs, the moduli strings, `extended_k`
  and `minimum_degree`. For these, T1 certifies that the transcription into
  `vk/data.v` is faithful to the dump — worth having, since it retires the
  offline-transcription trust — but it is not evidence that the model would
  *derive* the same values.

**Does not reach:**

- **The witness side.** `vk.pinned()` describes the constraint system, not
  synthesis. That the Rocq synthesis writes the cells the Rust one writes is
  carried by the other end of the chain — the byte-identical 19,679-event
  synthesis snapshot of
  [the JSON link](#the-refinement-from-the-json-comparison-to-the-vk), which
  is *not* kernel-checked — together with the in-kernel event-replay bridge of
  [`operational-soundness.md`](operational-soundness.md) over the imported
  floor-planner placement.
- **Fixed-column contents.** The dump carries the 44 commitment coordinate
  pairs (29 fixed columns + 15 permutation columns) as *values*, and T1 pins
  those values. It does not verify that they are the multi-scalar
  multiplications of the model's own fixed columns; recomputing them from the
  column contents is not done on this branch.
- **Anything the dump omits.** Two circuits agreeing on `vk.pinned()` agree on
  everything a verifier is configured by, but the dump is a description, not a
  denotation — it is evidence of agreement, not a proof of it.

## Assumption audit

`Print Assumptions` on every theorem named here, against a full `.vo` build,
reports exactly `PrimString.string : Set` plus the impredicative `Set` the
development is compiled with — with two documented exceptions in
`Orchard/vk/`, where the byte-level certificates additionally use kernel
primitives: T1 adds `PrimString.make` and `PrimString.cat`, and T2 reports
twelve axioms in total (`PrimString.string` plus eleven `PrimString` /
`PrimInt63` operations, the BLAKE2b word arithmetic among them). Several
plonkish lemmas are cleaner still, closed under the global context with no
axioms at all. There is no `Admitted`, `Axiom` or `admit` under
`Garden/Halo2/` or `Garden/Orchard/`.

The named L0 hypotheses (`IPABinding`, `MultiopenReduction`,
`FiatShamirChallengeGood`) are `Definition`s taken as explicit premises where
used, so they correctly do *not* appear in any audit.
