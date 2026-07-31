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
  Action-statement surface. It continues down the refinement ladder with the
  compiled plonkish layer (`Halo2/plonkish/`, `Orchard/compiled/` — selector
  compression, the permutation σ, and the pinned-vk parity certificates), the
  polynomial-identity layer over the cyclic domain, and the random-challenge
  counting layer with its named proof-system boundary hypotheses
  (`plonkish/boundary.v`) and the byte-level `vk.pinned()` anchor
  (`Orchard/vk/`).
- `docs/constrain-constant-fix.md`: record of the constants-mechanism gap
  — the dropped `constrain_constant` sites, the level-mismatch cause (floor
  planner vs region API, and the parity splice that hid it), and the fix with
  its validation gates.
- `docs/realize-overfill-fix.md`: record of the lookup-table fill gap — the
  unbounded table default fill against keygen's `usable_rows` cap, why the
  divergent `l_last` and blinding rows were invisible to every constraint
  theorem, the reference `fill_from_row` as ground truth, and the fix
  (half-open `FillFromRow` extent, the matching `LookupTableLoaded`
  tightening) with its validation.
- `docs/orchard-soundness-proof.md`: the Orchard Action-statement theorem
  — the exact `action_statement`/`satisfies_specification`/`deterministic`
  statements, each hypothesis and its motivation (including the
  witness-honesty side conditions), what the conclusion does and does not
  ensure, the inherited model caveats, and the assumption audit.
- `docs/orchard-completeness-proof.md`: the companion theorem in the other
  direction — honest witnesses are accepted (`orchard_completeness`), the
  `valid`/`nondegenerate` domain, the generic gluing lemma
  `Complete.circuit_holds_intro` and the `honest_planes` selector condition,
  the Orchard witness generator and its concrete instance, the per-family
  forward obligations of `circuit_completeness/forward/`, the operational
  layer carrying the result to the ideal `mock_prover_accepts` checker
  (`orchard_operational_complete`) via the placed re-derivation, and the
  continuation down the refinement ladder to the compiled plonkish layer
  (`orchard_compiled_complete`) and the polynomial-identity layer
  (`orchard_honest_algebraic_accepts`, `circuit_completeness/algebraic.v`),
  where soundness and completeness meet at the regular-challenge predicate
  `algebraic_accepts_regular`.
- `docs/orchard-compilation-correctness.md`: the companion to the two
  theorem documents, covering the layer beneath them — the modelled Halo2
  keygen (cyclic domain and blinding tail, selector compression by
  indicator polynomials, the permutation σ closed from the copies, lookup
  input substitution, query tables), the three equivalences that close the
  L3 ↔ L2 ↔ L1 arrows, what the layer adds to the assurance claim, and the
  translation-validation argument for the Rocq circuit being the Rust one:
  the modelled keygen bracketed at both ends — the structural JSON
  comparison of its inputs (`Orchard/Snapshots/`, out-of-kernel), the `Qed`
  identification of those exported objects with the terms the stack
  compiles, and the byte-level `vk.pinned()` anchor plus the Fiat–Shamir
  binding scalar on its output — with an explicit account of which end
  covers what, which fields are pass-through rather than evidence, and
  what neither reaches.
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
- `docs/ironwood-garden-action-bridge.md`: the checked Lean-to-Rocq Action
  translation, deployed-constant audits, and the direct refinement from
  Garden's native PostNU6.3 Action statement.
- `web/orchard-verification/`: the Orchard Verification Journey, Atlas,
  Circuit Explorer, and Circuit Grid source, tests, and data-generation hooks.
  The ignored raw structure snapshot, `public/data/` website data, and `dist/`
  production bundle are regenerated and validated through
  `.github/workflows/rocq.yml`. Pages releases are produced locally by
  `scripts/publish_orchard_pages.sh` and stored only on the dedicated
  `gh-pages` branch; build, validation, and publishing commands are documented
  in `docs/BUILD.md`.

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
- Treat `Garden/Orchard/Snapshots/circuit_structure_generated_from_model.json`,
  `web/orchard-verification/public/data/`, and `dist/` as ephemeral generated
  output: edit the source or evidence model, run its checks and build, and
  never commit those artifacts to the source branch. GitHub Actions regenerates
  and validates the raw and derived website data. The local Pages publisher
  puts only the validated static bundle on the force-replaced `gh-pages`
  deployment branch.

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
