# Agent Documentation Map

Use this file as the stable entry point. Keep detailed, changing guidance in
`docs/`, and update this map when adding or moving documentation.

## Core Docs

- `docs/BUILD.md`: local setup, dependency installation, and Rocq build commands.
- `docs/halo2-translation.md`: conventions for translating Halo2 and Orchard
  Rust circuits into Garden/Rocq.
- `docs/halo2-proof.md`: proof-facing Halo2 semantics, Poseidon determinism
  proof patterns, and tactic/performance notes.

## Code Pointers

- `Garden/Halo2/main.v`: shared Halo2 DSL for columns, expressions, gates,
  lookups, and constraint systems.
- `Garden/Halo2/Synthesis.v`: shared high-level Halo2 synthesis DSL and raw
  V1 event types used by Orchard synthesis translations.
- `Garden/Halo2/proof.v`: proof-facing semantics for Halo2 expressions, gates,
  and semantic constraints.
- `Garden/Orchard/columns.v`: absolute Orchard column constructors used by the
  Orchard-specialized translation, plus the shared Orchard column-index map.
- `Garden/Orchard/circuit.v`: top-level Orchard configure translation.
- `Garden/Orchard/circuit_generated.v`: generated numeric-index Orchard
  configure snapshot emitted by the Rust generator in Orchard/Halo2.
- `Garden/Orchard/circuit_generated_proof.v`: comparison bridge from absolute
  Orchard columns to generated numeric indices; keep it free of gadget-specific
  expression rewrites.
- `Garden/Orchard/circuit_synthesis_generated.v`: generated full V1 synthesis
  event trace; intentionally excluded from the normal Garden build.

## Maintenance Rules

- Put new agent-facing documentation in `docs/`, not beside the Rocq code,
  unless it is a short local README for a specific subtree.
- Treat documentation as part of the change: when code changes introduce or
  revise conventions, proof workflow, tactics, build commands, or known proof
  status, update the relevant `docs/` file in the same turn.
- Update `docs/halo2-translation.md` whenever the Halo2/Rocq DSL or translation
  style changes.
- Update `docs/halo2-proof.md` whenever proof statements, semantics, tactics,
  or Poseidon proof status changes.
- Update this map whenever a documentation file is added, renamed, or removed.
