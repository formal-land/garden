# Agent Documentation Map

Use this file as the stable entry point. Keep detailed, changing guidance in
`docs/`, and update this map when adding or moving documentation.

## Core Docs

- `docs/BUILD.md`: local setup, dependency installation, and Rocq build commands.
- `docs/halo2-translation.md`: conventions for translating Halo2 and Orchard
  Rust circuits into Garden/Rocq.
- `docs/halo2-proof.md`: proof-facing Halo2 semantics, Poseidon determinism
  proof patterns, and tactic/performance notes.

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
