# Agent Documentation Map

Use this file as the stable entry point. Keep detailed, changing guidance in
`docs/`, and update this map when adding or moving documentation.

## Core Docs

- `docs/BUILD.md`: local setup, dependency installation, and Rocq build commands.
- `docs/halo2-translation.md`: conventions for translating Halo2 and Orchard
  Rust circuits into Garden/Rocq.
- `docs/halo2-proof.md`: proof-facing Halo2 semantics, Poseidon determinism
  proof patterns, and tactic/performance notes.
- `docs/chip-model-caveats.md`: what the relational `proof.v` model captures and
  idealizes, and the synthesis-to-gates gluing (`circuit_holds`).
- `docs/operational-soundness.md`: the relational ↔ operational bridge — the
  `serialize.v` event replay (`RawGrid`/`apply_events`/`realize`), the ideal
  `mock_prover_accepts` checker, `operational_sound`/`operational_complete`,
  the placement-generic replay-success conditions (`realize/disjoint.v`),
  the whole-circuit Orchard instantiation with its `vm_compute` certificates
  (`circuit_operational.v`), and the assurance upgrade this delivers for the
  Action-statement surface.
- `docs/constrain-constant-fix.md`: record of the constants-mechanism gap
  — the dropped `constrain_constant` sites, the level-mismatch cause (floor
  planner vs region API, and the parity splice that hid it), and the fix with
  its validation gates.
- `docs/orchard-soundness-proof.md`: the Orchard Action-statement theorem
  — the exact `action_statement`/`satisfies_specification`/`deterministic`
  statements, each hypothesis and its motivation (including the
  witness-honesty side conditions), what the conclusion does and does not
  ensure, the inherited model caveats, and the assumption audit.
- `docs/orchard-balance-proof.md`: the transaction-level balance theorems
  built on the Action statement — `balanced_or_dlog` and `no_inflation`,
  the Pedersen-binding-as-reduction design (with the explicit computable
  discrete-log witness), the three-step proof, and the two computational
  boundaries (`SignatureKnowledge`, discrete-log hardness).
- `docs/compile-performance.md`: READ BEFORE touching heavy `vm_compute`
  certificates or investigating slow compiles — the common pitfalls
  (checker-lemma shape, leaf closures, table literals, memory limits), the
  `-vos`/`-vok` fast dev loop, and the current cost map of the certificate
  leaves.

Personal or not-yet-committed documentation is indexed in `CLAUDE.local.md`
(gitignored), which loads alongside this file.

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

## Proof iteration workflow

Pick the cheapest feedback loop for the scale of the change:

- **Single proof:** use the **Rocq MCP** (interactive goal state, run/undo tactics
  against a live document) instead of a `coqc` round-trip. It shows the goal after
  each tactic, so you fix a proof without recompiling the file. (If the MCP tools
  are not available in a worktree, its config may be missing/needs a restart; fall
  back to the `-vos`/`-vok` loop below.)
- **A file plus its dependencies:** use Rocq's interface compilation so heavy
  `Qed`/`vm_compute` proofs are NOT re-run. From `Garden/`:
  - build the edited file's dependency closure as `.vos` (interface only — skips
    every opaque `Qed` proof body, including expensive `vm_compute` certificates):
    `make -f CoqMakefile <path>/<file>.vos -j "$(nproc)"`;
  - then kernel-check just the file you are editing against those `.vos`
    interfaces: `opam exec -- coqc -vos -impredicative-set -R . Garden -w
    -stdlib-vector <path>/<file>.v` followed by the same command with `-vok`. The
    `-vok` pass runs and checks THIS file's proofs while loading dependencies as
    trusted `.vos` interfaces (so the slow certificates never run).
- **Final check only:** run a full `make -C Garden` (building every `.vo`, which
  executes the certificate `vm_compute`s) as the last step, and as the basis for
  any `Print Assumptions` audit. `.vos`/`-vok`-against-`.vos` trusts the skipped
  dependency proofs, so it is a development accelerator only — never report a
  result as proved on `.vos` alone.

When a specific file, definition, or tactic compiles too slowly (a heavy
`vm_compute`, a pathological `rewrite`/`f_equal`, etc.), record it in
`docs/compile-performance.md` — the file, the definition/tactic, the wall-clock
cost, and any mitigation — so the slow spots stay tracked in one place.
