# Orchard

Formal verification of the [Zcash Orchard Action circuit](https://zips.z.cash/protocol/protocol.pdf) in [Rocq](https://rocq-prover.org/), built on the Garden Halo 2 framework.

The verification covers all three core circuit properties:

- **Functional correctness** — a satisfying assignment's seven public outputs equal the §4.18.4 output functions applied to the genuine inputs (`circuit_proof/main.v`: `OrchardAction.satisfies_specification`).
- **Determinism** — two satisfying assignments that agree on the genuine inputs agree on every public output (`circuit_proof/main.v`: `OrchardAction.deterministic`).
- **Completeness** — the honest witness generator always produces a satisfying assignment (`circuit_completeness/`).

It also includes a transaction-level **value-balance** proof and a **Pedersen-binding reduction** for the `bundle/` layer.

## Directory structure

| Path | Contents |
|---|---|
| `circuit.v` | Top-level circuit configuration and synthesis in the Garden Halo 2 monad. |
| `columns.v` | Column-set definition (advice, fixed, instance, selectors). |
| `regions.v` | Region-identifier enumeration. |
| `protocol_spec.v` | The protocol-faithful specification (`OrchardProtocolSpec`), aligned to §4.18.4 of the Zcash protocol. |
| `circuit/` | Gadget definitions: addition chip, note-commit, commit-ivk, etc. |
| `circuit_proof/` | Functional-correctness and determinism proofs, from per-gadget lemmas up to the two-theorem surface in `main.v`. |
| `circuit_completeness/` | Completeness proof: forward witness generation (`forward/`), the operational soundness grid (`operational/`), and the generated instances (`instance/`). |
| `bundle/` | Transaction-level balance theorems (`main.v`), Pedersen-binding reduction (`binding_reduction.v`), and the bundle vocabulary (`spec.v`). |
| `Pallas/` | Rocq proofs about the Pallas curve generators used by Orchard: coordinates, group orders, and group-hash provenance. |
| `constants/` | Fixed-base Lagrange table constants for the six Orchard generators (SpendAuthG, ValueCommitV, ValueCommitR, NullifierK, NoteCommitR, CommitIvkR). |
| `vk/` | Verification-key serialisation helpers and the pinned transcript representation. |
| `compiled/` | JSON snapshots of the circuit configuration and synthesis, generated from both the implementation and the Rocq model, used to check parity. |
| `Snapshots/` | Raw algebraic data captured from the live Orchard circuit. |

## Proof architecture

```
protocol_spec.v           (OrchardProtocolSpec — §4.18.4 output functions)
        ▲
        │  protocol_equiv.v  (protocol_mul/ per-base bridges)
        │
circuit_proof/internal_spec.v  (OrchardCircuitSpec — windowed Lagrange tables)
        ▲
        │  per-output bridge lemmas
        │  (value_commit_v/, value_commit_r/, nullifier_k/, note_commit/,
        │   commit_ivk_r/, spend_auth_g/, old_note/, ladder/, us_free/, …)
        │
circuit_proof/main.v      (OrchardAction.satisfies_specification
                           OrchardAction.deterministic)
        ▲
bundle/main.v             (transaction balance: homomorphic sum, binding reduction)
```

The circuit-level proofs stay on top of the Garden Halo 2 monad (`Garden/Halo2/`); they never touch raw constraint polynomials directly.

## Entry points

- **Functional correctness / determinism**: `circuit_proof/main.v`
- **Completeness**: `circuit_completeness/main.v`
- **Transaction balance**: `bundle/main.v`
- **Protocol specification**: `protocol_spec.v`
- **Pallas generator facts**: `Pallas/Generators.v`, `Pallas/GeneratorsOrder.v`

## Interactive visualizations

Three generated views are published from this repository:

- [Orchard Verification Journey](https://formal-land.github.io/garden/) — an animated, guided account of how the proof developed.
- [Orchard Verification Atlas](https://formal-land.github.io/garden/proof-map.html) — an interactive map of proof dependencies, evidence, assumptions, and remaining boundaries.
- [Orchard Circuit Explorer](https://formal-land.github.io/garden/circuit.html) — an interactive view of the high-level Rocq circuit, from functional components down to free-monad regions, gates, and source definitions.
- [Orchard Circuit Grid](https://formal-land.github.io/garden/circuit-grid.html) — a parity-backed row-and-column view of the V1 circuit placement.

See [BUILD.md](../../docs/BUILD.md#orchard-verification-visualization) for local viewing and development commands.
