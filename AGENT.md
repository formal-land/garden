# Agent Documentation Map

Use this file as the stable entry point. Keep detailed, changing guidance in
`docs/`, and update this map when adding or moving documentation.

## Core Docs

- `docs/BUILD.md`: local setup, dependency installation, and Rocq build commands.
- `docs/halo2-translation.md`: conventions for translating Halo2 and Orchard
  Rust circuits into Garden/Rocq.

## Code Pointers

- `Garden/Halo2/main.v`: shared Halo2 DSL for columns, expressions, gates,
  lookups, and constraint systems.
- `Garden/Halo2/proof.v`: proof-facing semantics for Halo2 expressions, gates,
  and semantic constraints.
- `Garden/Orchard/columns.v`: absolute Orchard column constructors used by the
  Orchard-specialized translation.
- `Garden/Orchard/circuit.v`: top-level Orchard configure translation.

## Maintenance Rules

- Put new agent-facing documentation in `docs/`, not beside the Rocq code,
  unless it is a short local README for a specific subtree.
- Update `docs/halo2-translation.md` whenever the Halo2/Rocq DSL or translation
  style changes.
- Update this map whenever a documentation file is added, renamed, or removed.
