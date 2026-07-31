# Ironwood–Garden Orchard Action specification alignment

This track compares the high-level Orchard Action semantic relation and total
output function. It does not claim a direct equivalence of Halo2 polynomial
constraints.

## Canonical standalone source

The source of record is
`ironwood/Zcash/Circuits/Action/IronwoodGardenActionBridge/ActionGarden.lean`.
It imports only Lean's `Init.Prelude` and defines:

```lean
abbrev Z := Int
```

All base and scalar operations use explicit Pallas moduli. Points are integer
coordinate pairs with `(0, 0)` as the identity sentinel. Poseidon,
Sinsemilla, message packing, Merkle evaluation, validity, and outputs are
concrete definitions.

The public records and functions intentionally mirror Garden:

```text
Params
ActionInputs
FullActionInputs
validActionInputs
orchardAction
```

`FullActionInputs` adds the old-note randomness and three validity flags to
the protocol-facing `ActionInputs`. Merkle paths store explicit
`(layer, sibling, isRight)` triples.

There is one standalone Action specification. The file contains no legacy
`Core…` records or alternate NU6.2 semantics.

## Lean-side Ironwood boundary

`ironwood/Zcash/Circuits/Action/IronwoodGardenActionBridge/ActionGardenBridge.lean`
supplies record adapters and proves the field/integer, Pallas, Poseidon,
Sinsemilla, packing, Merkle, and output correspondences used by the Ironwood
witness theorem. A `ProofCore` namespace remains local to that
Ironwood-dependent proof file; it is proof decomposition, not a second public
specification and is not part of the Lean-to-Rocq translation.

It also audits the standalone literals against Ironwood's deployed data:

```lean
orchardPoseidonRoundConstants_deployed
orchardSinsemillaGenerators_deployed
orchardPoseidonRoundConstant_deployed
orchardSinsemillaGenerator_deployed
orchardNoteCommitQ_deployed
orchardCommitIvkQ_deployed
orchardMerkleCrhQ_deployed
orchardSpendAuthG_deployed
orchardValueCommitVG_deployed
orchardValueCommitRG_deployed
orchardNullifierKG_deployed
orchardNoteCommitRG_deployed
orchardCommitIvkRG_deployed
```

The exact public input theorem is:

```lean
validActionInputs_iff_exists_proverAssumptionsPost
```

In full, it characterizes

```lean
ActionGarden.validActionInputs ActionGarden.orchardParams (fullInput wit)
```

by the existence of an `ActionData` with the same `fullInput` satisfying
Ironwood's `ProverAssumptionsPost`. The existentially quantified completion
fills the five erased fixed-base window arrays and five stored output fields.
A same-`ActionData` iff would incorrectly constrain data which the standalone
predicate cannot observe.

The output theorem remains separate:

```lean
proverAssumptionsPost_implies_gardenOrchardAction_output
```

It proves equality of all five outputs produced by the standalone function and
the integer encodings of the outputs fixed by Ironwood's post-synthesis
assumptions.

## Generated Lean-to-Rocq boundary

There is no hand-maintained Rocq body mirror. A Lean frontend parses and
elaborates one immutable source snapshot without `.olean` reuse, then emits a
schema-versioned syntax representation. A closed, fail-closed Rocq emitter
resolves and translates every supported declaration body, including the
target-side primitive-array storage; no `.v.in` semantic template remains.

The translator consumes all 119 declarations in source order and emits:

- `Garden/Orchard/IronwoodGardenActionBridge/action_garden_constants.v`,
  containing primitive arrays for 64 Poseidon rows and 1,024 Sinsemilla points;
- `Garden/Orchard/IronwoodGardenActionBridge/action_garden_generated.v`,
  containing the generated flattened declarations;
- `ironwood/Zcash/Circuits/Action/IronwoodGardenActionBridge/ActionGarden.lean-rocq.diff`,
  the complete review diff.

Both generated files carry the exact Lean SHA-256. The checker rejects stale
files, unsupported Lean constructs, proof shortcuts, extra imports, unresolved
names, unconsumed syntax, and declaration-order drift. Ordinary declaration
bodies and the two large constant tables are translated from the parsed
source, so changing a body changes the corresponding Rocq output or fails
before any output is written; updating only the stamped hash cannot make a
stale translation pass.

The translation preserves the established `ActionGardenZ_*` names and record
selectors while making its representation lowerings explicit: `Point` and
`State3` use generated data records, the large tables use primitive arrays,
and path triples use Garden's left-nested Rocq product layout.

Primitive-array lookup preserves the source's signed-index semantics:
negative `Z` indices become zero and oversized indices return the declared
fallback, without `uint63` wraparound.

## Five-file Garden proof

Only these files remain in the bridge directory:

1. `action_garden_constants.v`: generated primitive-array constants;
2. `action_garden_generated.v`: generated standalone declarations;
3. `action_garden_bridge.v`: integer/field, point, Sinsemilla, and fixed-base
   representation facts;
4. `action_garden_poseidon_bridge.v`: the isolated Poseidon correspondence;
5. `action_garden_equivalence.v`: adapters and the direct native comparison.

Splitting out constants and Poseidon is operational: it keeps the large
literal module and the symbolic 109-round permutation out of ordinary proof
reduction. The deleted `action_core_*` files and
`action_garden_public_equivalence.v` represented the previous Core/NU6.2
route and are no longer part of the argument.

`action_garden_equivalence.v` proves the total-function theorem:

```coq
ActionGardenEquivalence.orchard_action_output_eq
```

For every standalone parameter and input record, translating the result of
`ActionGardenZ_orchardAction` equals applying Garden's native
`OrchardProtocolSpec.orchard_action_spec` to the translated parameters and
input. This theorem is unconditional.

The concrete parameter theorem

```coq
ActionGardenEquivalence.orchard_params_eq
```

identifies the three standalone domain points with the constants used by the
current Garden circuit.

The proof makes each implementation seam explicit:

- explicit integer modulo versus Garden field operations;
- literal points versus `Point.t`/Pallas representations;
- all-`Z` scalar multiplication versus group multiplication modulo
  `pallas_q`;
- Fermat inversion versus Garden's extended-Euclid inverse;
- explicit Merkle layers and their canonicality predicate;
- total incomplete addition plus a separate honest-branch predicate;
- primitive-array constants versus Garden's named constants.

## Direct Post-NU6.3 circuit composition

Garden and Ironwood now describe the same Post-NU6.3 Action version. No
alternate semantic relation is needed. The bridge composes the unconditional
function equality with Garden's existing circuit theorem:

```coq
ActionGardenEquivalence.orchard_action_output_of_action_statement
ActionGardenEquivalence.native_valid_action_inputs_of_action_statement
```

The first theorem rewrites the native circuit output directly to the
translated Ironwood function. The second exposes the native
`OrchardValidActionInputs.ValidActionInputs Γ` conclusion of the same
Post-NU6.3 `action_statement`.

This input result intentionally retains Garden's assignment-indexed shape.
The native predicate reads values through several `Γ`-indexed readers,
including ownership witnesses that are not fields of
`OrchardSpec.ActionInputs`. Consequently, there is no honest bijection
between that record and standalone `FullActionInputs`, and this branch does
not introduce a duplicate record-level Garden predicate merely to state an
iff. The exact record-level Ironwood characterization is instead proved in
Lean by `validActionInputs_iff_exists_proverAssumptionsPost`.

All bridge theorems are closed with no admission. A `Print Assumptions` audit
reports only Rocq's primitive array/`uint63`/string interfaces and functional
extensionality already used by Garden, with no bridge-specific axiom.

## Reproduction

From `ironwood`:

```sh
TMPDIR=/home/fedora/Zcash/tmp/action-garden \
python3 Zcash/Circuits/Action/IronwoodGardenActionBridge/lean_to_rocq.py \
  Zcash/Circuits/Action/IronwoodGardenActionBridge/ActionGarden.lean \
  ../garden/Garden/Orchard/IronwoodGardenActionBridge/action_garden_generated.v \
  --diff Zcash/Circuits/Action/IronwoodGardenActionBridge/ActionGarden.lean-rocq.diff

TMPDIR=/home/fedora/Zcash/tmp/action-garden \
python3 Zcash/Circuits/Action/IronwoodGardenActionBridge/lean_to_rocq.py \
  Zcash/Circuits/Action/IronwoodGardenActionBridge/ActionGarden.lean \
  ../garden/Garden/Orchard/IronwoodGardenActionBridge/action_garden_generated.v \
  --diff Zcash/Circuits/Action/IronwoodGardenActionBridge/ActionGarden.lean-rocq.diff \
  --check
```

From `garden`, build the final file; the generated dependency graph checks all
five bridge files. Up to four jobs are safe for this target:

```sh
TMPDIR=/home/fedora/Zcash/tmp/action-garden \
make -C Garden -j4 \
  Orchard/IronwoodGardenActionBridge/action_garden_equivalence.vo
```
