# Compile-time performance: heavy `vm_compute` certificates

The Orchard fixed-base proof carries finite certificates whose correctness is
a single large `vm_compute` closed with `Qed`, over the concrete Pallas
modulus. This file records the rules that keep those costs out of the
development loop, the current cost profile of a full build, and a short
history of the big cost cliffs. Read the dev-loop and pitfall sections before
working anywhere near the certificate files.

## Fast dev loop: `-vos` / `-vok`

`-vos` compiles a file but **skips every opaque (`Qed`) proof** — no tactics
run, so no `vm_compute` executes; only each lemma's *statement* is recorded
as a trusted skeleton. An interface build of the whole tree is therefore
fast, and downstream files can be checked against their dependencies' `.vos`.

The generated `CoqMakefile` (from `rocq makefile`) exposes the standard
targets:

```sh
cd Garden
make -f CoqMakefile vos -j "$(nproc)"   # all .vos, skips the heavy vm_computes
make -f CoqMakefile vok -j "$(nproc)"   # then check the skipped proofs (still pays them)
```

To iterate on one proof (e.g. in `circuit_proof/ladder/main.v`) without
paying the table `vm_compute`, build the deps as `.vos` and check just that
file's opaque proofs:

```sh
make -f CoqMakefile vos -j "$(nproc)"
rocq compile -vok -impredicative-set -R . Garden -w -stdlib-vector \
  Orchard/circuit_proof/ladder/main.v   # checks THIS file vs .vos deps
```

**Honesty constraint.** `.vos`/`-vok`-against-`.vos` trusts the skipped
dependency proofs. It is a development accelerator only. Any "closed /
axiom-free" claim, and every `Print Assumptions` audit, must run on a full
`.vo` build (`make all`) that actually executes the certificate
`vm_compute`s. Treat `-vos` as "compiles and type-checks", not "verified".
Cautionary tale: `circuit_proof/ladder/main.v`'s `full_window_correct`/E2
`Qed`s were authored and only ever compiled `-vos`, so they sat unverified
until their first `-vok` (2026-07-02). Under the forward-progress policy,
building on such not-yet-checked `Qed`s is allowed — but they must stay
tracked, and every claim still requires the full-`.vo` audit.

## Rules and pitfalls

### State checker lemmas as the raw `forallb` term

Never state a certificate's checker lemma through a named boolean constant.
With `Definition nonres_check : bool := …` and `Lemma nonres_check_true :
nonres_check = true`, the per-entry extraction (`pose proof (forallb_entry …
nonres_check_true …)`) needs the conversion `nonres_check ≡ List.forallb …`,
and the conversion oracle runs the whole checker on the *lazy* machine —
≈ 77 s at elaboration plus ≈ 77 s again at `Qed`, where the VM does the same
computation in 1.6 s. Stating the lemma directly as `List.forallb … = true`
makes the extraction type-check syntactically, with no conversion at all.
All fifteen certificates (x-coordinate, window-sign, and discriminant, five
bases each) use the raw `forallb` shape; keep that shape for new
certificates.

### Keep certificates in leaf files with lean `Require` closures

Each heavy `vm_compute` lives in a leaf file whose `Require` closure contains
none of the files under proof iteration, so iterating never re-pays it. The
table leaves (`circuit_proof/<base>/table.v`) Require only
`EllipticCurve/Weierstrass.v` and `EllipticCurve/Pallas.v` — NOT `Sqrt.v`,
`window_disc.v`, `fixed_window_canonical.v`, or
`circuit_proof/fixed_base/main.v`. They are re-paid only when
`Weierstrass.v`/`Pallas.v`, the `Field/` layer, or the `Halo2`/`M.v` spine
(reached through `Pallas.v`'s Requires) change.

The parametric octupling builders live in `Orchard/circuit_proof/table_defs.v`
(module `FixedBaseTableDefs`; the same lean closure plus
`Field/ListLemmas.v`), while the certificate scaffolding — whose
`Sqrt`/`Halo2.lemmas` dependencies are exactly the utility files that get
edited — is deliberately separate in `Orchard/circuit_proof/cert_defs.v`, so
edits there do not re-trigger the heavy table leaves. The shared discriminant
checker/extraction scaffolding is parameterized once in
`ecc/chip/window_disc.v`. History shows why the split matters: certificate
files that sat downstream of the iteration surface once re-paid the whole
octupling chain on every edit (see History).

### Memoise tables as pasted literals and gate on literal size

`full_table_reduced` in each table leaf is an *actual literal* (85×8
`Weierstrass.Affine` points, generated offline), with
`full_table_reduced_eq : full_table = full_table_reduced` as the single heavy
`Qed`. An alias (`:= full_table`) is not memoisation: `Opaque` does not
affect `vm_compute`, so every consumer certificate would re-evaluate the
whole octupling chain.

Gate any generated table leaf on size *before* compiling it: file within
0.5–1.5× of the per-window-scaled template (~126 KB / 85 windows), plain
decimal coordinates below `pallas_p`. Provenance (2026-07-06): a generated
`circuit_proof/value_commit_r/table.v` whose literal had ~53 KB lines (vs the
template's 1.4 KB) made its `full_table_reduced_eq` `vm_compute` peak at
~100 GiB, and the kernel OOM killer killed the entire session scope, three
times across 2026-07-04/06. Root cause: the offline generator script omitted
`Require Import Stdlib.ZArith.ZArith.`, which registers the `Z` Number
Notation; without it the printer falls back to fully-qualified
`BinNums.Zpos (BinNums.xI …)` constructor trees, ~30–40× the character count
of the decimal form. Any scratch generator that prints
`Z`/`Weierstrass.Affine` coordinates for pasting needs that Require even if
its other Requires transitively pull in `BinNums`/`Z` — the Number Notation
registration is not re-exported by files that only use `Z` internally.
(Known-good outlier: `circuit_proof/value_commit_v/table.v` has
long-line-but-valid formatting — 30 KB max line, correct total size.)

### Witness generation is untrusted: dump, compute outside, paste

The checkers verify every pasted witness, so witnesses can come from
anywhere; reserve in-Rocq `vm_compute` for the trusted checks themselves. The
soundness gate is preserved: e.g. were any window discriminant a square,
`disc / pallas_b` would be a non-residue, no witness root could exist, and
the checker computes `false` — the `Qed` fails rather than lies. Recipe for
the discriminant roots: (1) dump the discriminants once from Rocq
(`Eval vm_compute in` over `window_disc` per table, plus `Primes.pallas_p`
and `pallas_b` — ~74 s, polynomial evaluation only); (2) compute the roots
with Python's native `pow`/Tonelli–Shanks — 1.4 s for all 2 908 entries —
asserting per entry that the discriminant is a non-residue and
`pallas_b·r² ≡ disc (mod p)`; (3) paste and let the checkers verify. Use the
same dump-compute-paste shape for any witness regeneration (discriminant or
window-sign tables).

If a sweep must run inside Rocq, shard it from the start: single-process
680-entry `field_sqrt` sweeps for window-sign `root_table`s failed to finish
within 43–52 minutes on two different bases. Split the 85 windows into 17
scratch files of 5 (`List.seq (5*i) 5` in place of `List.seq 0 85`), run
them as parallel background `rocq compile` jobs, and concatenate the printed
`list (list Z)` results in window order (~10 min under load, well under a
minute on an idle machine). Two adjacent traps: the table-leaf octupling
dump (`Eval vm_compute in full_table`, ~100 s) and the root-table
`field_sqrt` sweep are different `Eval`s with very different costs — a cheap
dump says nothing about the sweep; and the assembled outer `list (list Z)`
literal needs its own opening bracket before the first window row
(`[ [<row0>]; [<row1>]; …]`, matching the template literal in
`circuit_proof/spend_auth_g/sign_cert.v`) or the paste fails with
`Syntax error: '.' expected`.

### Run concrete checks on the VM, once

Close concrete modular-arithmetic checks with `vm_compute; reflexivity`,
never `cbv; reflexivity`: the lazy machine runs the computation at tactic
time AND again at `Qed` (a ~253-step square-and-multiply check cost ~26 s
that way; the VM makes both runs milliseconds). For certificate `Qed`s, use
`vm_cast_no_check (@eq_refl bool true)` so the VM conversion runs once (at
kernel check), not twice (tactic + kernel).

### OOM containment: cap `rocqworker`, never `ulimit -v`

The opam switch's `rocqworker` is wrapped by a shim
(`~/.opam/garden-rocq-9.0.1/lib/rocq-runtime/rocqworker`, real binary at
`rocqworker.real`) that runs every compile worker in a transient systemd user
scope with `MemoryMax=32G`, so a runaway `vm_compute` dies alone instead of
letting the kernel OOM killer take out the whole session. Do NOT use
`ulimit -v` instead: OCaml 5 reserves huge *virtual* mappings by design, and
`ulimit -v` kills every compile with "Not enough heap memory".

### Bisect hangs and slow files with `-time`

`coqc -time` prints each completed sentence, so a hung sentence is the first
one missing from the log (a *failing* sentence still gets a `-time` line, so
also check for an `Error` after it). Beware that a `coqc` OOM kill inside
`cmd 2>&1 | tail` looks like a clean run — bash prints `Killed` outside the
pipe; always check the exit status (137) and the output stamp (`.vok`/`.vo`
mtime).

### `Strategy opaque` before conversion-heavy composition

Composing lemmas whose types mention `is_square`, `field_sqrt`, `modpow`, or
`fixed_window_point_canonical` over the concrete Pallas modulus with
up-to-conversion tactics (`exact`, `apply`, `transitivity`, `rewrite`) can
hang for tens of minutes at `Qed`/kernel-check time: to compare such terms,
the kernel unfolds `is_square` to `… modpow _ ((p-1)/2) …`, and with the
concrete `(p-1)/2 ≈ 2²⁵³` the `modpow_pos` recursion squares its accumulator
~253 times, doubling the symbolic term size each step — exponential blowup
even when the base is abstract. Before the composing proof, set

```coq
Strategy opaque
  [is_square modpow modpow_pos field_sqrt fixed_window_point_canonical].
```

(the names must be resolvable in the file's scope — `Require Import` the
modules or qualify them). This turned a ~30-min `-vok` of
`circuit_proof/ladder/main.v` into ~2 min. Set the `Strategy` in any proof
that matches these constants up to conversion — conversion matching, not
just `vm_compute`, triggers the blowup.

### Never normalize Poseidon round chains

Each unfolded Poseidon round references the previous state three times, so
the 36-level normal form has `3^36` nodes: proving
`fold_rows permutation_rows s = Poseidon.permute s` by
`cbv … delta [… row_transition …]` OOM-kills `coqc` (>100 GB in ~60 s,
SIGKILL 137) — `cbv`'s in-memory sharing does not save the conversion check,
and the tactic dies first. Instead peel the fold row-by-row
(`rewrite !fold_rows_cons` + `!row_transition_full`/`!row_transition_partial`),
keeping `Poseidon.apply_full`/`apply_partial` folded so each consumes its
state argument exactly once, and end in `reflexivity` —
`Orchard/circuit_proof/poseidon.v` `-vok`s in seconds this way.

The same blowup reappears through *unification*: with primitive projections
(`Global Set Primitive Projections` in `Plonky3/M.v`), closing a goal with
`exact (f_equal State.x0 Hchain)` against `(Poseidon.permute {…}).(State.x0)`
compares a `Proj` node with a constant applied as an `App`, and unification
falls back to normalizing the shared `permute` argument — the same `3^36`
chain (>23 min before being killed). Never let unification compare a
projection-of-`permute` against a constant-applied-to-`permute`:
`rewrite <- Hchain` first, so the `permute` application is gone from the
goal, then `reflexivity`.

### Never hand unification sides that differ under a big fold

Never give unification an equation whose sides differ *underneath* a
`sinsemilla_hash_to_point` application — or any big symbolic fold
(`fixed_scalar_mul`, `merkle_root`). As soon as one argument pair fails
evarconv's syntactic check, unification whnf-normalises the applications:
the hash fold unfolds its 109 incomplete-add steps, each duplicating the
symbolic accumulator inside `mod_inverse` terms, and comparing the two
differently-shared graphs blows up — a monolithic `reflexivity` on
`out_cmx_spec_eq` (`circuit_proof/note_commit/cmx.v`) ran >45 min before
being killed (2026-07-07). Instead split: a projection lemma over *variable*
inputs (both sides unfold to the identical application, so no fold is ever
forced), one-delta lemmas, and per-field reader lemmas, assembled with
syntactic `rewrite`s so the final `reflexivity` compares literally identical
terms; the file compiles in ~1 s that way.

### Scope `lia`/`nia` with `clear -` in div/mod-heavy contexts

Micromega cost is a function of the whole context, not the goal: `lia`'s
zify preprocesses every hypothesis, each `Z.div`/`Z.mod` occurrence expands
into its euclidean axiomatization, and the search explodes. In `Field/Div.v`
a trivial fuel-exhaustion `lia` sat >30 minutes at 99% CPU; the same `lia`
scoped to the one needed hypothesis (`clear -Hfuel; lia`) takes 0.001 s. In
any proof whose context accumulates several `Z.div`/`Z.mod`/product
hypotheses, scope every `lia`/`nia`/`by lia` side-condition with `clear -…`.
Prefer spelling out a single nonlinear step (`Z.div_le_lower_bound` +
`Z.mul_le_mono_nonneg_l`, then `lia`) over `nia` — its witness search can
fail even in a minimized context.

### Never duplicate an instance-bearing module — alias it

The repo once had two verbatim copies of the `Primes` module
(`Garden.Field.Field.Primes` and `Garden.Plonky3.M.Primes`), and files
resolved the ambient `#[local] Existing Instance Primes.PallasPIsPrime` to
*different* copies depending on their imports. The two instance constants
contain distinct opaque primality proofs, so unification can never equate
them directly; its only semantic escape is unfolding the phantom-instance
functions (`is_square` → `modpow` at the concrete 2²⁵³ exponent) — which
hung the first kernel check of `circuit_proof/ladder/main.v` for >78 min
(root-caused 2026-07-02). Fix: `Garden/Plonky3/M.v` defines
`Module Primes := Garden.Field.Field.Primes.` — a module *alias*, so both
spellings are literally the same constants and instances everywhere. The
reconciliation had also been a hidden drag on every cross-instance
`apply`/`exact` in the file.

### Stale `.vos`/`.vok` placeholders and unstable dependency graphs

A plain (non-`-vos`) `rocq compile` leaves 0-byte `.vos`/`.vok` placeholder
files alongside the real `.vo`; a *different* file compiled with `-vos` that
`Require`s the leaf loads those placeholders (not the real `.vo`) and can
spuriously report "inconsistent assumptions over library …". Delete them
(`rm -f *.vos *.vok`, keep the `.vo`) once the leaf's real proof is done.
Relatedly (observed 2026-07-06), a long real compile can report inconsistent
assumptions against a dependency some concurrent process transiently rebuilt
mid-compile. Recompile once the dependency graph is stable — `md5sum` the
direct-dependency `.vo`s immediately before and after; if they match, the
result is trustworthy.

### Ring identities: `mod_ring_solve`, not `field_solve`

For pure mod-p polynomial identities use `mod_ring_solve`
(`Garden/Halo2/lemmas.v`), reserving `field_solve` for genuine linear
arithmetic; see `docs/halo2-proof.md` for the rule and its mechanism.

## Current costs (measured 2026-07-06)

Full clean build: ≈ 1 570 s CPU over 275 files, ≈ 212 s ideal wall. The wall
clock is set by the Sinsemilla chain — `sinsemilla_s` (59 s) → `chip_proof`
(18 s) → `hash_to_point_round_proof` (105 s) → `circuit_proof/merkle.v`
(25 s) — with the fixed-base chain ~60 s shorter. Heavy leaves:

- Fixed-base table leaves (`circuit_proof/<base>/table.v`): ~79 s ∥ 80 s ∥
  80 s ∥ 20 s in parallel (value_commit_v is the cheap one); the
  note_commit_r leaf lands in the ~100 s band.
- `sinsemilla/hash_to_point_round_final_proof.v`: 96 s, parallel with the
  round proof; `hash_to_point_proof.v` (shared definitions) 3 s;
  `hash_to_point_fold_proof.v` 1.5 s.
- `circuit_proof/fixed_base/main.v`: 78 s.
- The `order_<base>.v` ladder-certificate leaves: 16 s each
  (value_commit_v 30 s), `make -j` parallel.
- Discriminant certificates (`circuit_proof/<base>/disc_cert.v`): ≈ 92 s CPU
  total across the five self-contained files (≈ 21 s per 85-window family,
  6 s for the 22-window value_commit_v).
- x-coordinate certificates ≈ 7 s each; window-sign certificates ≈ 9–10 s
  each.
- `circuit_proof/main.v` 0.9 s; everything else seconds.

Remaining single-file levers: the `hash_to_point_round_proof` round proof
and the `sinsemilla_s` table literal, the two largest links in the chain
above. The round proof's cost is two 58-s
`with_strategy opaque […] cbn` normalizations plus ~36 s of `field_solve`s;
an untried whitelist `cbn [names]` over the gate-eval chain would likely
help, but do NOT retry swapping the `cbn` for `lazy` — `lazy` inlines the
`Z.add` fixpoint at stuck symbolic applications (`row + 1`), breaking every
later rewrite pattern; `cbn`'s refolding is load-bearing there.

## History: the big cost cliffs

**Table alias → pasted literal (2026-07-02).** `full_table_reduced` was
originally an alias of `full_table`, and the spend_auth_g x-coordinate and
window-sign certificate files sat downstream of `Field/Sqrt.v`,
`ecc/chip/window_disc.v`, and `ecc/chip/fixed_window_canonical.v` — exactly
the files under iteration — so every edit re-evaluated the whole octupling
chain twice (≈ 13–20 min per certificate). That stalled consumer integration
and briefly led to both checker `Qed`s being Admitted as "plumbing", letting
a full `make` go green without verifying either certificate (resolved the
same day). Moving the table to a pasted literal in a lean leaf cut both
certificates to seconds, leaving the one heavy one-time `Qed` in the leaf.
The same first kernel check also exposed the duplicate-`Primes` instance
wall (see the pitfall above).

**Egcd switch (2026-07-06).** `mod_inverse` switched from Fermat
exponentiation to extended Euclid, collapsing every inversion-dominated
`vm_compute`: the table-leaf checks fell from ≈ 23 min each to the band in
the cost table above, `Orchard/Pallas/Generators.v`'s six `[q]·G` order
ladders from ≈ 30 min to 87 s, the `order_<base>.v` leaves from ≈ 5 min
each to their current cost. The first full clean rebuild after the switch:
313 files, ≈ 9 800 s CPU, ≈ 16 min wall — of which the Euler-criterion
discriminant shards were ≈ 8 100 s CPU (~83% of the build; `modpow`-bound,
no inversion, so egcd did not help them). The switch also surfaced
`Field/Div.v`'s unscoped-`lia` stall (see the pitfall above).

**Euler → witness route, and shard retirement (2026-07-06).** The
discriminant certificates (`is_square (window_disc …) = false`, ~2 900
entries across the five fixed-base tables) stopped running Euler's criterion
per entry (a ~253-squaring `modpow`, ≈ 2.9 s each, ≈ 230 s per 10-window
shard). Each family now carries a pasted `nonres_root_table` — per entry a
root `r` of `disc / pallas_b` — and one checker verifying
`disc = pallas_b *F (r *F r)` and `r <> 0`: one field multiplication per
entry (3–7 s per former shard, 238 s CPU total). The exported lemma
statements stayed byte-identical, so consumers and `Print Assumptions
OrchardAction.deterministic` were untouched. With the per-entry cost gone,
the 50-file band sharding cost more in per-file `Require` loading than the
checks themselves and was retired to one self-contained `disc_cert.v` per
family (current figure above).

**Critical-path pass (2026-07-06).** With the discriminant block retired,
wall clock was set by the dependency critical path, funnelling through
`ecc/chip/spec.v`. Per-sentence profiling fixed: `spec.v` 148 s → 27 s (a
`cbv; reflexivity` modexp check and three ring identities proved with
`field_solve` — see the VM and `mod_ring_solve` rules above);
`Generators.v` down to ~2 s (the ladder certificates moved to the parallel
`order_<base>.v` leaves, the derived order facts to
`Orchard/Pallas/GeneratorsOrder.v`, consumed by
`circuit_proof/ladder/main.v`); `sinsemilla/hash_to_point_proof.v` 204 s
serial → ~110 s parallel via the four-way file split; and the octupling
builders moved to `table_defs.v` so the table leaves stopped serializing
behind the spend_auth_g leaf. Net: 438 s ideal wall at the egcd baseline
down to the current figure above.
