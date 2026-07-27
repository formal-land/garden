# The lookup-table fill and the blinding rows

Record of a faithfulness gap in the replay model's lookup-table fill: the
model filled a table's fixed column with its default value to the bottom of
the column, while deployed Halo 2 keygen stops at the usable rows and leaves
the `l_last` and blinding rows at `0`. This note states the gap, its cause,
why every existing theorem was blind to it, and the fix.

## The gap

A lookup table is loaded into fixed columns. After the layouter assigns the
table's real entries, the remaining rows are filled with the column's default
value so that a disabled lookup's padding tuple is still a genuine table row.
The model emitted that fill with no upper bound, so rows
`usable_rows .. n − 1` held `default_value`. Deployed keygen leaves them `0`.

For the Orchard circuit `n = 2048` and `blinding_factors = 5`, so
`usable_rows = 2042` (`Orchard/circuit.v`, `orchard_usable_rows`) and the
divergent rows are `2042 .. 2047` — the `l_last` row plus the five blinding
rows.

The gap is invisible on the `TableIdx` column, whose default is `0` and whose
over-fill therefore coincides with keygen's zeros. It is visible on the two
Sinsemilla generator-table columns `TableX` and `TableY`, whose defaults are
the coordinates of table row 0.

## Cause

`fill_lookup_entries` (`Halo2/serialize.v`) emitted, per table column, a
`FillFromRow` event carrying only a start row, and the realizer
`RawGrid.fill_fixed` (`Halo2/realize/main.v`) wrote the value at every row
`r` with `from_row <= r` — the extent was `[from_row, ∞)`. The model had a
faithful analog of the reference `fill_from_row` that dropped one bound.

## Reference implementation

The deployed keygen (pinned `halo2`, `plonk/keygen.rs`,
`circuit/floor_planner/single_pass.rs`) makes the intent explicit:

- fixed columns start all-zero, and table columns are fixed columns;
- the usable range excludes the tail:
  `usable_rows: 0..params.n - (cs.blinding_factors() + 1)`;
- the default fill is bounded by it —
  `for row in self.usable_rows.clone().skip(from_row)` — so the loop runs
  over `[first_unused, usable_rows)` and never reaches the tail;
- the commitment is taken over all `n` rows, with that zero tail included.

The tail is Halo 2's zero-knowledge device: the last `blinding_factors` rows
of *advice* columns are randomized so the witness commitments hide the
witness, and the extra `l_last` row is reserved by the permutation argument.
Public fixed, selector and table columns have nothing to hide and are left at
`0`. The Zcash protocol specification does not pin this down — §5.4.10.3
delegates verifying-key and parameter generation to the halo2 library — so
keygen's stored column is the ground truth.

## Why the theorems were blind to it

The divergent rows are unconstrained: no gate, copy or lookup argument reads
them. A relational or operational satisfaction theorem quantifies over the
constraints, so it cannot observe a value that no constraint mentions. The
gap only becomes observable once an artifact hashes *every* row of a fixed
column, which is what a verifying-key commitment does.

The unbounded extent had also become load-bearing in the other direction.
`mock_prover_accepts` quantifies each lookup argument over all rows, and the
equivalence with the domain-restricted reading is discharged by observing
that on an all-zero-selector row — which includes the blinding rows — the
padding tuple equals table row 0 and the fill guarantees the column holds
that same default there. Under the unbounded fill the blinding-row padding
was free.

## The fix

The bound is restored at the source, so the replay grid itself is
keygen-faithful:

- `Raw.Event.FillFromRow` carries a `to_row`, threaded from
  `init_lookup_table_events` and `eval_layouter` with
  `orchard_usable_rows = 2042`;
- `RawGrid.fill_fixed`, the `Fill` log record and the three conflict
  predicates use the half-open extent `[from_row, to_row)`;
- the fill lemmas of `Halo2/realize/facts.v` and the conflict machinery of
  `realize/disjoint.v` and `realize/sound.v` are restated and re-proved for
  it.

The relational side is tightened to match. `Fact.LookupTableLoaded` pins only
the assigned rows `[0, length values)` rather than every non-negative row;
the default band and the zero tail are captured operationally by the
fill-replay lemmas instead. This *weakens* the fact, so the completeness
surface needs only the matching destructuring in `Halo2/complete.v`, and the
Sinsemilla generator-table lemma `GeneratorTable.loaded` discharges the new
upper bound from the table length `2^sinsemilla_k`.

## Validation

`Orchard.circuit.synthesize` is unchanged, so the enabled points and witness
facts the completeness certificates range over are unaffected.
`orchard_completeness`, `orchard_completeness_instance` and
`orchard_operational_sound` audit at the repository baseline
(`PrimString.string : Set` plus impredicative `Set`), with no `Admitted` or
`Axiom` under `Garden/Orchard/` or `Garden/Halo2/`.

The residual model caveat is unchanged and recorded in
[`chip-model-caveats.md`](chip-model-caveats.md): the checker still
quantifies over all integer rows rather than the `2^k` cyclic domain, and
blinding rows are not otherwise modelled.
