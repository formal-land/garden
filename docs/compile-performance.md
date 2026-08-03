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

**Adding, moving or renaming a `.v` file rebuilds the whole tree — but only
through the top-level `%.vo` route.** `Garden/`'s top-level `Makefile`
computes `VFILES` by `find`, regenerates `CoqMakefile` whenever that set
changes, and declares `%.vo: CoqMakefile %.v` — so asking the *top-level*
makefile for any `.vo` (`make Orchard/foo.vo`) after the file set changed
finds it older than the regenerated makefile and rebuilds it, and the same
holds for deleting `CoqMakefile` by hand. `make` / `make all` does **not**
take that route: it regenerates `CoqMakefile` and then delegates to
`make -f CoqMakefile all`, whose own rule is `$(VOFILES): %.vo: %.v |
$(VDFILE)` — no makefile prerequisite — so an added file costs only itself
and its dependents (verified 2026-08-03: adding four leaves and running
`make -j32` reported `Nothing to be done for 'real-all'` once the new files
had been compiled directly). Batch file moves into a single change anyway,
and never request an individual `.vo` from the top-level makefile after
changing the file set; editing a file *in place* always costs only its own
dependents.

**Honesty constraint.** `.vos`/`-vok`-against-`.vos` trusts the skipped
dependency proofs. It is a development accelerator only. Any "closed /
axiom-free" claim, and every `Print Assumptions` audit, must run on a full
`.vo` build (`make all`) that actually executes the certificate
`vm_compute`s. Treat `-vos` as "compiles and type-checks", not "verified".
Cautionary tale: `circuit_proof/ladder/main.v`'s `full_window_correct`
`Qed`s were authored and only ever compiled `-vos`, so they sat unverified
until their first `-vok` (2026-07-02). Under the forward-progress policy,
building on such not-yet-checked `Qed`s is allowed — but they must stay
tracked, and every claim still requires the full-`.vo` audit.

## Rules and pitfalls

The rules below are branch-independent. A few cite worked examples from the
vk-commitment MSM and Vesta/SRS layers, which are not in this worktree — they
live on `valerii-huhnin@msm-stretch`. The lesson still applies; only the
example is elsewhere.

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

### Shard large literal tables across files — single-file elaboration is superlinear

Elaboration cost of successive literal-table `Definition`s in one file grows
with file position, even though the definitions are independent.  Measured
2026-07-23 on sixteen 128-entry shards of 7-tuples with four ~77-digit
literals each: identical successive shard definitions cost
2.6 / 4.1 / 10.4 / 14.5 s in one file — the 700 KB whole-table file ran
> 6 minutes without finishing where 16 × 2.6 s was expected.  Splitting the
tables one-per-file, assembled by a constants-only aggregator, resets the
cost: ≈ 2.5 s per file, fully parallel.  Independently, an applicative
entry constructor (`E i ws0 r0 ws1 r1 x y`, each argument checked against a
fixed expected type) elaborates ≈ 2× cheaper than the nested tuple notation
`(i, ws0, …, y)` for the same 128-entry table (5.2 s → 2.6 s) — prefer it
for any new wide-tuple table.

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

**Composing as a term is not an escape when the composed step is a record
projection.** Elsewhere this file recommends `eq_trans`/`eq_sym`/`f_equal`
term composition over `rewrite` around heavy constants; that advice stops at
`f_equal <primitive projection>`. Measured 2026-08-03 in
`Orchard/circuit_proof/note_commit_bot.v`: closing a `cmx` bridge by
`exact (eq_trans … (eq_trans (f_equal OrchardSpec.out_cmx (eq_sym Hspec)) …))`
did not terminate (killed at 600 s wall clock, every other sentence of the
file at 0.000 s under `-time`). `Primitive Projections` is set globally in
`Plonky3/M.v`, so `f_equal proj H` hands unification a `Proj` node against a
projection *application* and it falls back to normalizing the shared
`orchard_action_spec` argument — the 109-step Sinsemilla fold. Rewriting the
record equality **inside the hypothesis** first (`rewrite Hspec in Hcmx`,
then the projection lemma, then `exact (eq_sym Hcmx)`) makes the same step
0.000 s. Same family, from `merkle_bot.v` the same day:
`exact (f_equal Point.x Hpoint)` against a goal spelling
`EccSpec.extract_x (sinsemilla_hash_to_point …)` ran > 100 s before being
killed; `unfold EccSpec.extract_x; rewrite <- Hpoint; cbn [Point.x];
reflexivity` — i.e. remove the fold application from the goal before any
conversion — is instant.

One ordering trap around the same fix: after `with_strategy opaque
[UnOp.from] cbn` on a goal, `rewrite H` for a hypothesis `H` mentioning the
same `UnOp.from` term fails with "found no subterm" — the two spellings
print identically, but `cbn` has normalized the implicit `Prime` instance
argument. Do every hypothesis rewrite *before* the `cbn`, and use
`setoid_rewrite` for facts reached through the ring morphisms.

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

### Never `match` on a concrete heavy computation — project through combinators

Elaborating a `match` whose scrutinee is a *constant that unfolds to a big
computation* sends that computation to the lazy machine at pretyping time,
before any tactic runs. In `Halo2/halo2_poseidon/p128pow5t3_provenance.v`,
`Definition derived_round_constants := match derived with Some (rc, _) => rc
| None => [] end` — where `derived` is the whole Grain/MDS generation
pipeline applied to concrete parameters — stalled `rocq compile` at 99% CPU
for >12 minutes (killed), on both the plain and the `-vos` build; even a
flat `match derived with Some _ => true | None => false end` hangs, while
the same `match` on a `None`-bodied constant of the identical type is
instant. Deceptive symptom under `-vos`/`-time`: every sentence logs
`0. secs` and the stall appears after the last sentence. Fix: never place
the concrete constant in scrutinee position — route projections through
combinators whose own `match` is on a bound variable
(`option_get [] (option_map fst derived)`), leaving the pipeline unreduced
until a checker's `vm_compute` (which runs it in milliseconds after a ~5 s
one-time bytecode compilation of the closure).

### Never reference a deep spec-constant chain inside a `Fixpoint` body

A `Fixpoint` whose body mentions a constant that unfolds into a deep
definition chain (observed with `SinsemillaSpec.merkle_layer`, which reaches
the whole hash/generator/table chain) stalls compilation for *minutes* in
end-of-file processing — under `-vos` and `-time`, every sentence logs
`0. secs` and the stall appears after the last sentence, the same deceptive
symptom as the match-scrutinee pitfall.  Measured on
`circuit_completeness/instance/defs.v` (2026-07-15): a 32-iteration Merkle
fixpoint referencing `merkle_layer` directly cost ≈ 8 min of end-of-file
CPU; the identical logic as a *higher-order* fixpoint over abstract
`step`/`check` function parameters, instantiated by a plain `Definition`
(`chain_nondeg_go` / `merkle_nondeg_b`), compiles in ≈ 1 s.  Plain
(non-recursive) definitions referencing the same constants are unaffected.
When a recursive checker needs a heavy spec function, abstract it as a
function parameter and instantiate outside the fixpoint.

### Per-cell witness generators must not recompute region prefixes per read

`vm_compute` shares no work between two applications of the same function:
an `Assignment.t` whose advice plane recomputes region-level derivations at
every cell read makes whole-circuit `vm_compute` certificates infeasible.
Measured on the completeness instance
(`Orchard/circuit_completeness/instance/cert.v`, 2026-07-14), with the raw
VM cost constants — one 255-bit modular multiplication ≈ 7 ms (Z is the
binary inductive, so a multiply is ~65 k constructor operations), one
incomplete point addition (one egcd inversion + a few multiplies) ≈ 48 ms,
one `field_sqrt` (Tonelli–Shanks, modpow-bound) ≈ 9–14 s, one `Pallas.mul`
at a 255-bit scalar ≈ 20 s — the per-read costs of the current
`circuit_completeness/advice_*` sub-generators are: any Merkle hash-region
cell ≈ 10 s (the leaf recomputes `cm_old`, a 109-word Sinsemilla hash) plus
≈ 5 s per layer index (the running node re-folds all previous layers); any
`A5` cell of a fixed-base leg ≈ 1 161 s (a `List.nth` into
`canonical_us_for` forces all 85 `field_sqrt`s); any variable-base-mul
accumulator cell ≈ 20 s (one full `Pallas.mul`); the Orchard-checks
`A4`/`A5` cells ≈ 161 s each (`anchor_root`, the 32-layer Merkle fold).
Summed over the 4 862 enabled selector points × their gate reads this is
days of VM time.

The implemented architecture
(`Orchard/circuit_completeness/generator/tables.v`, 2026-07-15): every
region-level
derivation is hoisted into one record (`OrchardCompletenessTables.t`) built
by `tables_of w` — the per-layer Sinsemilla accumulator rows built linearly
(two field inversions per round, mirroring `IncompleteAddition.output`'s
reduced chord formulas so the values are bit-identical to the spec fold),
the six fixed-base legs, the Poseidon schedule, and the scalar multiples —
and `honest_assignment` binds `tables_of w` in a `let` outside the per-cell
lambdas.  Since global constants are evaluated once per `vm_compute` run
and closure environments are built strictly, one run forces the record once
(≈ 3–4 min for the whole circuit at the test input) and every cell read is
a list lookup; the whole 4 862-point truth table evaluates in ≈ 9.5 min.
The `field_sqrt` wall disappeared without pasted literals: the fixed-base
square-root witnesses are read from the window-sign certificates' pasted
`root_table`s (`circuit_proof/<base>/sign_cert.v`, one root per
(window, digit) with `root² = fw_z + y`) instead of `canonical_us_for` —
`y = u² − z` is identical for either root, so every consumer value is
unchanged.  One residual rule for the builders themselves: the VM is
call-by-value, so never pass a heavy derivation as a plain argument to a
per-cell helper inside them.

**A hoisted record is built once per *file*, not once per `Qed`.**  Earlier
revisions of this section claimed the opposite — that every certificate
`Qed` re-pays the record build, so heavy `Qed`s should be spread thinly
across files.  That is wrong, and it was expensive: it is the reason the
instance certificates were split across five leaves, each rebuilding the
same record.  Measured directly (2026-07-27, three `vm_cast_no_check`
certificates over reads of `Γtest` in one file): **311.6 s, 0 s, 0 s**.
`Γtest` is a global constant, and the VM caches an evaluated global for the
whole compilation unit, kernel conversions included.  The rule is therefore
the reverse of what was written here: **put every certificate that shares a
heavy global in the same file** — see `instance/certs.v`, where merging four
leaves cut the group from 1 900 s to 751 s.  Certificates that do *not*
touch that global belong elsewhere, so they still compile in parallel
(`instance/domain.v`, `instance/read.v`).

The counter-pressure is wall clock: merging minimises CPU but concentrates
the critical path into one file.  Merge by *what a file computes*, then
split only if the merged file dominates the build.

### Fold a chained quantity once; never certify its members independently

The sharing rule applies to range checkers, not just to advice planes, and
its strongest form is structural: when the quantity a range quantifies over
satisfies a recurrence, certify the fold, not the members.  Measured on the
variable-base nondegeneracy range of the completeness instance (2026-07-27,
`circuit_completeness/instance/`).

The clause needs, for each of the 251 incomplete bit indices, three
non-degeneracy facts about the ladder accumulator `mul_acc w (S i)`.  Spelled
per index it costs one `Pallas.mul` over a `256 − i`-bit scalar each — four
sharded leaves, ≈ 90 min of VM time between them.  But `mul_acc w i` is one
double-and-add step from `mul_acc w (S i)`, so one linear fold
(`mul_chain_go`: two group additions and one incomplete addition per index)
computes every accumulator in the chain.  The whole clause became a **49 s**
`vm_cast_no_check` in `instance/domain.v` and the four leaves were deleted.

What makes the fold provable without circularity is which addition it runs
on.  `forward/ecc_add.v`'s `ladder_go_snd` threads the *incomplete* chip
addition and therefore carries a nondegeneracy hypothesis — the very thing
being certified.  `VarBaseDefs.double_add_step_multiple` states the same step
on the **complete group law** `Pallas.add`, where it holds given only
`Pallas.reduced`/`Pallas.on_curve` of the base point.  So the chain induction
is unconditional and the incomplete-addition conjuncts are *checked* at each
step rather than assumed.  Reach for the complete-law lemma whenever a fold
must be justified before its exceptional cases are known to be excluded.

Two lessons the same change left behind, both general:

- **A per-index checker must take the derived values, not the witness
  record.**  `vm_compute` shares no work between two applications of the same
  function, so `mul_step_b w i` — which reaches the scalar through
  `mul_scalar w`, hence `ivk w`, a `Commit^ivk` hash, twice per index —
  recomputed that hash at every index.  One `ivk test_input` costs 28.3 s on
  its first evaluation (bytecode compilation plus global forcing) and **4.9 s
  marginally**, against 10.1 s for a whole step at index 250 and 27.2 s at
  index 10: 9.8 s of every index, ≈ 41 min of the ≈ 90 min.  Passing the
  scalar and base points as arguments so the VM builds the `forallb` closure
  with the hash already a value cut the four ranges to 11.4 / 11.2 / 10.9 /
  9.4 min — before the fold removed them entirely.  Where a range genuinely
  has no recurrence to exploit, this hoisting is the whole remedy.
- **A delta-identical bridge lemma can still diverge.**  Bridging the
  record-indexed and value-indexed spellings holds by delta alone, yet
  `reflexivity` does not terminate (> 10 min at 2.4 GB and climbing): the
  checker is boolean, so whnf of either side forces the guard of
  `mul_step_point`, hence `mul_scalar w`, hence `ivk w`, whose body unfolds
  the whole symbolic `Commit^ivk` chain at a *variable* input.  Prop-level
  spellings are safe — `Point.x acc <> 0` against its counterpart stays
  congruent through `eq`, `Point.x`, `repr` and `Pallas.mul`, never reaching
  a match — but every boolean- or match-headed spelling diverges, including
  the `mul_step_nondegenerate` conclusion (its `mul_step_point` guard).
  `Strategy opaque [ivk]` makes all of them instant: both sides get stuck at
  the same atom and the comparison is structural.  Keep the setting
  `Local` — `forward/ecc_add.v` and `forward/var_base_ladder.v` unfold `ivk`
  and must not inherit it.

Sizing note, still worth having if a range ever needs sharding again: the
step at index `i` multiplies by a `256 − i`-bit scalar, so per-index cost
falls roughly linearly with the index and equal-length shards leave the
lowest one setting the wall clock by itself (31 min against 15 min for the
highest).  Fitting `cost(i) ≈ 1.2 + 0.066·(256 − i)` seconds against the two
measured ends balanced the four shards to 9.4–11.4 min.  Size parallel
shards by cost, never by member count.

### Certify each side of an equation against a literal, not against the other

A certificate whose two sides are *both* computed pays for one of them
twice. `vm_cast_no_check (@eq_refl T (rhs))` against the goal `lhs = rhs`
puts `rhs` on both sides of the checked cast, and the VM re-evaluates it
rather than noticing the syntactic match. Measured on the completeness
read-back (2026-07-27, `read_action_inputs Γtest = inputs_of test_input`):
the reader side costs 294 s and the specification side 207 s on their own,
yet the certificate took **864 s** — the 363 s gap is the second evaluation
of `inputs_of test_input`.

Pin the common value as a literal and certify each side against it, then
compose:

```coq
Lemma reader_lit : read_action_inputs Γtest = test_action_inputs. (* certs.v *)
Lemma spec_lit   : inputs_of test_input   = test_action_inputs. (* read.v  *)
Lemma ok : read_action_inputs Γtest = inputs_of test_input :=
  eq_trans reader_lit (eq_sym spec_lit).                        (* cert.v  *)
```

Each cast now compares one computed side against a literal, so nothing is
evaluated twice, the composition step evaluates nothing at all, and — since
the two sides share no subcomputation — the halves land in different files
and compile in parallel. The literal is dumped once with
`Eval vm_compute in`, and it is verified rather than trusted: both
certificates would fail if it were wrong. Here it is 5.8 KB and the
read-back fell from 972 s to 259 s.

The same reasoning applies to the *inputs* of a certificate: bind a value
that several fields need once, in a `let`, instead of letting each field
recompute it. `inputs_of` reached `cm_old w` three times — directly, through
`leaf w`, and through `anchor_root w` — at ≈ 10.6 s marginal each; giving
`anchor_of_leaf` the leaf as a parameter and binding `cm`/`lf` once removed
two of them. Beware measuring such a value's cost by a single
`Eval vm_compute`: the first evaluation also forces the Sinsemilla tables
and other globals, which made `cm_old` look like 34.3 s rather than 10.6 s.

### Pre-reduce both sides before `reflexivity` against the hoisted advice plane

A bare `reflexivity` between a generator dispatch applied to the hoisted
record and a hand-spelled cell value — e.g.
`advice_t w (tables_of w) A9 (Nullifier AlphaLookup) row =
running_lookup_advice (alpha_z0 w) 13 A9 row` — can diverge (> 30 s
timeout; observed 2026-07-21 in
`circuit_completeness/forward/lookups_witness.v`): when the head constants
differ, unification's alternating unfolding can force
`t_nullifier_scalar (tables_of w)` past the projection, normalizing the
symbolic Poseidon round chain (the `3^36` trap) on the lazy machine.  The
same holds for evar-driven forms — `eexists; reflexivity` against a
`tables_of` projection sat minutes in evarconv.  Fix (the `cell_refl`
tactic there): `cbn` on exactly the dispatch constants
(`advice_t`/`advice_nullifier_t`/`merkle_advice_t`/`advice_ecc_t`/
`mul_advice_of`), `unfold` the leaf readers and the site value
definitions, then `reflexivity` — both sides become syntactically
identical stuck terms and the compare is instant; and state
`tables_of`-projection equations with an explicit right-hand side
(`t_layers_eq`/`t_leaf`), never through an evar.

### Keep context-scanning tactics off heavy-constant hypotheses

Two members of the same family, both observed in `Orchard/compiled/main.v`
(2026-07-17), where the context carries hypotheses mentioning the concrete
19,679-event stream (`orchard_events`) or the compiled system
(`OrchardCompiledCheck.compiled`):

- **Bare `discriminate` whnf-normalizes every hypothesis type** while looking
  for an equality to refute.  With `Hin : List.In event orchard_events` in
  context, that whnf unfolds `In` and forces the whole synthesis
  serialization on the *lazy* machine — the proof sat ≥ 10 minutes at 3 GB
  where the VM replays the same stream in seconds.  Always target the
  hypothesis: `discriminate Hcheck` (whose type is a small boolean match)
  instead of `discriminate`/`try discriminate`.
- **Never let the unifier prove `compiled = Compile.compile …` by
  conversion.**  Passing `eq_refl` for `compile_correct`'s `Hcompiled` on the
  concrete instance makes evarconv unfold the *applied* side and evaluate the
  whole selector packing lazily (same ≥ 8-minute, 3 GB stall).  State the
  equation once as its own lemma closed with `vm_cast_no_check (@eq_refl
  CompiledSystem.t OrchardCompiledCheck.compiled)` (`orchard_compiled_eq`,
  1.5 s on the VM) and pass that lemma.

### Pin the implicit modulus when applying `Prime`-generic lemmas

Applying a `{p} `{Prime p}`-generic lemma to a concrete goal that does not
itself pin `p` lets typeclass resolution enumerate every `Primes.*IsPrime`
instance for the undetermined `?p`, and each wrong candidate makes evarconv
unfold and lazily normalize whatever computable structure the goal carries
before backtracking.  Observed in `Halo2/plonkish/poly_domain.v`
(2026-07-17): `apply (Poly.w_pows_NoDupP omega k)` on the goal
`Poly.NoDupP (p := Primes.pallas_p) omega_pows` sat ≥ 6 minutes at 98 % CPU
— each failed `Prime ?p` candidate forced a lazy normalization of the
2048-element `w_pows` power enumeration (2048 modular multiplications at
254-bit width per candidate) — while the same `apply` with
`(p := Primes.pallas_p)` given explicitly is instant.  Goals whose statement
already mentions an annotated occurrence (e.g. `Fpow (p := …)`) pin `?p`
through unification before resolution and do not stall.  Rule: pass
`(p := …)` explicitly whenever the only `p`-determining argument of an
`apply`/`rewrite` is a heavy computable structure.

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

### Reverse long accumulator lists with `rev_append`, never `List.rev`

Stdlib's `List.rev` is the quadratic definition (`rev l' ++ [x]` per cell);
on a 10^5-element list it dominates everything around it.  Measured in
`Orchard/vk/print.v` (2026-07-20): the pinned-vk printer emits
~112k string fragments onto a reversed accumulator in ~6 s of VM time, and
`List.rev` of that accumulator alone cost ~95 s (≈ 6·10^9 cons cells) —
switching to the linear `List.rev_append l []` made the reversal free and
cut the whole printer run to ~2 s.  The same applies to any
`vm_compute`-heavy fold that accumulates a long list in reverse order.
(`PrimString.cat` itself is cheap — a balanced pairwise join of ~10^5
fragments totalling 1.3 MB is well under a second.)

### Keep unification, `fold`, and `lia` away from heavy computable constants

Three members of one family, all observed while proving the `transcript_repr`
pipeline theorem (`Orchard/vk/transcript_repr.v`, 2026-07-20), where the goal
mentions constants whose bodies unfold into the 285 KB compact-rendering byte
list or its 2,228-block decomposition:

- **Tactic-time unification (`reflexivity`, `change A with B`) between two
  spellings of such a constant** — e.g. the goal
  `le64 ++ pstring_bytes s = le64 ++ vk_pinned_compact_bytes`, where the two
  byte-list terms are delta-convertible — diverges into a pointwise lazy
  comparison of the underlying lists (≈ 9 min; each element forced through a
  unary-`nat` `Z.of_nat` index, so the comparison is quadratic).  Make the
  two sides *syntactically identical* before `reflexivity`: `unfold` the
  younger constant (pure delta on named occurrences, no conversion check),
  never `change`/`reflexivity` across the delta step.
- **`fold heavy_constant` diverges outright**: `fold` first normalizes the
  constant's body with the tactic-level reduction machinery, which forces
  the whole block computation on the lazy machine.  State the definitional
  equation as its own lemma (`Lemma c_def : body = c. Proof. unfold c.
  reflexivity. Qed.` — delta only, instant) and `rewrite c_def` instead.
- **`lia` facts whose atoms are projections of heavy constants** (here
  `557 < length t2_blocks` derived from a `vm_compute`d length equation and
  `skipn_length`) pass at tactic time but **diverge at `Qed`** when the
  kernel re-checks the micromega proof with the heavy terms in checked
  positions.  Restate the needed comparison as a boolean `vm_compute`
  certificate (`(557 <? length t2_blocks)%nat = true`, closed with
  `vm_cast_no_check`) and consume it through `Nat.ltb_lt` — the kernel then
  checks one VM equality instead of a micromega chain over the atoms.

Related VM-cost trap in the same file: an index function that converts a
unary `nat` per element (`pstring_bytes`'s `Z.of_nat` per index) is
quadratic over a 285 k-element string — thread a `Z` (or machine-int) index
through a fuel fixpoint instead, and prove it pointwise equal to the
`nat`-indexed spec (the `Z`-indexed variant needs no `Uint63Axioms`).

### `Z.pow` at a concrete exponent must never reach any reduction engine

`(base ^ 1024) mod p` evaluates `Z.pow` by iterated multiplication into
the unreduced 260 kbit integer before the outer `mod` — on the VM and on
the lazy machine alike, and the lazy machine is reached by more than
tactics: `change`, a goal-side `rewrite` whose occurrence search unifies
its pattern against the pow subterm, and the `Qed`-time conversion of a
cast all forced it (observed 2026-07-24 on a root-of-unity half-power
certificate: three different >7-minute stalls).  Certify the power
through the square-and-multiply `modpow` (`vm_cast_no_check`, ~1 s),
transfer to the `Z.pow` spelling by rewriting `modpow_correct` *in the
hypothesis* (never in a goal that contains the pow term) followed by
`unfold Fpow, UnOp.from in H; exact H`, and wrap the transfer lemma in
`Strategy opaque [Z.pow Z.pow_pos]`.

### The completeness `forward/` gate-obligation files: reducing spec terms

`Orchard/circuit_completeness/forward/{ecc_add,fixed_base,canonicity,
sinsemilla,var_base_ladder}.v` (the per-family gate obligations) were
written by an interrupted run and initially blacklisted as "not yet
kernel-checked" — four hung, one errored (measured 2026-07-24 against a full
`.vo` tree).  They now kernel-check clean (0 Admitted, baseline
`PrimString.string` + impredicative Set) and are un-blacklisted (2026-07-25):
`ecc_add` 27 s (was ~490 s), `fixed_base` 149 s, `sinsemilla` 39 s,
`canonicity` / `var_base_ladder` comparable.  The shared cause was the one
this section warns about: a proof let a reduction engine touch the
generator's spec terms.

Measured full `.vo` costs of the `forward/` files (2026-07-25 for the family
files, 2026-07-26 for `read_back`, `assembly` and `witness/`, on an otherwise
idle 32-core machine, real time):
`fixed_base` 149 s, `poseidon` 119 s (1.1 GB peak), `running_sums` 75 s
(2.8 GB peak — the largest resident set in the directory), `canonicity` 73 s,
`lookups_witness` 45 s, `sinsemilla` 40 s, `ecc_add` 27 s,
`fixed_base_certs` 83 s, `var_base_ladder` 13 s, `residual` 3 s,
`read_back` 2 s, `assembly` 2 s, `api` 1 s; and the five `witness/` group
files, all cheap: `fixed_legs` 6 s, `bits_column` 2 s, `slice_bounds` 2 s,
`chain_outputs` 2 s, `var_base` 2 s.
`lookups_witness` grew from 37 s to 45 s when `nt_open` became the
concatenation of the five `witness/` fact lists: the `nt_cover` scan now
unfolds those definitions across module boundaries. That is the whole cost of
the regrouping, and it is why splitting the residue into separate files was
affordable — each group carries its own facts and proofs, and the joining
file pays only the re-run of one order-insensitive `existsb` scan.
`poseidon` and `running_sums` are dominated by their per-row case analyses
(36 permutation rows; the range-check/telescoping row lemmas), not by any
certificate — like the rest of the directory they contain no
input-dependent `vm_compute`.

Auditing the whole completeness surface is a *load* cost, not a proof cost:
a scratch
file that `Require`s the thirteen `forward/` modules plus `instance/cert.v`
and runs the ~37 `Print Assumptions` takes 56 s against a full `.vo` tree
(2026-07-26), essentially all of it loading the closure. Batch the audit into
one file rather than one `coqc` run per theorem. `Print Assumptions` prints
its blocks back to back with no name echo, so interleave a delimiter (a
`Check` of a marker, or split on the trailing `Theory:` line) before
attributing a block to a theorem — an off-by-one there silently misreports
which theorem carries a leaf.

Packaging a family obligation on top of that algebra re-pays the
enabled-point scan and the guarded-body inventory once per file:
`canonicity.v` went 8 s → 73 s when its `family_gates_ok [38; 39; 40]`
assembly landed (2026-07-25) — the 23 per-selector `guarded sel = <bodies>`
certificates and the 1,711-point `shard_classify` scan, plus the load of the
three sibling lanes it dispatches into.  All of it is input-independent
(facts, enabled points, selector membership — never a `Γ` advice
evaluation), so the file stays off the heavy-certificate cost map.  Note
that requiring a sibling forward file imports its persistent `Strategy
opaque` set: `ecc_add.v` exports `[BinOp.div mod_inverse
CompleteAddition.output]` and `[Pallas.mul Weierstrass.mul]`, which makes
`unfold` on those constants fail in the requiring file.  Re-enable them with
a scoped `Strategy transparent … / Strategy opaque …` pair around the
coordinate-projection lemmas that need them, rather than dropping the
opacity for the whole file.

- `canonicity.v` `padd_coords` (line 976): `unfold EccSpec.point_add,
  CompleteAddition.output` then `destruct (Point.x P =? 0); [cbn; auto |]`
  puts `cbn` on the unfolded complete-addition output, whose field division
  is a Fermat inverse `Z.pow _ (pallas_p − 2)` (exponent ≈ 2^254).
  Confirmed non-terminating — 99% CPU / ~1 GB and climbing, no `-time`
  progress past that sentence in > 2 min.  The same `unfold …point_add,
  CompleteAddition.output` sites are in `ecc_add.v` (≈ 427–462) and
  `var_base_ladder.v` (758).
- The Poseidon `3^36` chain (see "Never normalize Poseidon round chains"):
  `canonicity.v` `t_nf_spec_eq` (line 1081) proves `t_nf_spec (tables_of w)
  = <expr naming the 36th state of `pose_states_of w`>` by bare
  `reflexivity`; `sinsemilla.v` carries seven `pose_states_of` references in
  the same shape.
- `var_base_ladder.v` (line 950) does not hang — it *fails* after ≈ 196 s:
  `mod_ring_zero` on a gradient goal carrying a `BinOp.div` reports "not a
  valid ring equation" (the `mod_ring_solve`-not-ring trap below).

Resolution (statement-preserving; the techniques that worked):

- Persistent `Strategy opaque [BinOp.div mod_inverse CompleteAddition.output]`
  — NOT `with_strategy`, which speeds the tactic but leaves the `Qed`
  re-check slow — so the Fermat inverse (`mod_inverse` runs `mod_inv_loop`
  at concrete fuel ≈ 512) is never forced at tactic *or* kernel-check time.
  This alone took `ecc_add`'s `hash_go_snd` 45 s → 0.05 s.
- `#[local] Opaque poseidon_state pose_states_of` (and
  `Poseidon.poseidon_hash2`) to keep the 3^36 round chain folded; where a
  shallow projection must stay transparent, place the `Opaque` after it.
- Generic point-add projection lemmas `padd_x` / `padd_y` proved by
  `reflexivity` over *variable* points (the inverse never appears), applied
  by `rewrite` instead of letting `reflexivity` / `change` normalize a
  coordinate — this turned a 158 s `change` cheap in `sinsemilla.v`.
- `Opaque` on the ladder / table accumulators (`vb_columns`, `rr_mid`) so
  residual conversions match as stuck atoms.
- `cbn [tables_of <projections>]; reflexivity` (the `cell_refl` shape of
  `forward/lookups_witness.v`) for the `tables_of`-projection cell
  equalities, and `cbn [Z.eqb Pos.eqb]` — not just `Z.eqb` — so
  `mod_ring_solve` / `mod_ring_zero` sees a valid ring equation on a
  positive-literal boolean (var_base_ladder line 950).

Clearing the hangs also surfaced genuine proof bugs the hangs had masked
(a `List.nth_indep` called without its index, a wrong-occurrence `rewrite`,
an `f_equal` that already closed the goal so the trailing `lia` hit "No such
goal", a mis-ordered `unfold`); those were fixed with no weakened statements.

Two more members of the same family, from the variable-base ladder rows of
`forward/var_base_ladder.v` (2026-07-25):

- **State the gate bodies over abstract row values, never over the
  generator's projections.**  `mod_ring_zero` on a secant-line goal whose
  atoms were `sr_l1 (vstep …)` / `Point.x (macc …)` projections failed after
  its `setoid_rewrite` pass had delta-expanded them (the projections whnf to
  `BinOp.div`, which the occurrence search unfolds to `_ mod p`), leaving a
  goal in `mod_inverse` terms that is no longer a ring equation.  Fix: prove
  each gate body as a lemma universally quantified over plain `Z` row values
  (`q_mul_1_gate` / `q_mul_2_gate` / `q_mul_3_gate`), with the cell readings
  and the chord identities as hypotheses; the instance layer then supplies
  the generator's values by `refine` without any reduction.  This is the
  `generalize`-before-`setoid_rewrite` rule below, applied at the statement
  level instead of inside the proof.
- **Never let `f_equal`/`reflexivity` bridge two spellings of a row index.**
  `rewrite <- (hi_row w 254 …); f_equal` on
  `hi_at tb 2 = hi_at tb (256 − Z.of_nat 254)` does not stop at the index:
  `f_equal` tries `reflexivity` first, which unfolds `hi_at` to a `List.nth`
  and forces the 125-step ladder fold at a symbolic input — no termination
  (killed at 10 min).  Parameterize the row-reading lemmas by the row
  (`hi_row`/`lo_row` take `r` with `Hr : r = 256 − Z.of_nat m`), and thread
  the neighbouring rows as explicit parameters (`prow`/`nrow` with
  `prow = row − 1`, `nrow = row + 1`) so every instantiation is syntactic.
  With that, the whole family obligation costs ≈ 2.5 s on top of the file's
  previous 10 s.

### `split` on an equality goal is `eq_refl` — never enumerate facts with `repeat split`

`interpret_facts Γ [f₁; …; fₙ]` is a right-nested conjunction whose leaves
are equalities, so `repeat split` does not stop at the conjunctions: `eq`
has one constructor, and `split` on a leaf `a = b` is `apply eq_refl`, i.e.
a full conversion check between the two cell readings.  On the 888-fact
witness-fact enumeration of `circuit_completeness/forward/lookups_witness.v`
(2026-07-26) that conversion unfolds the hoisted record — `Strategy opaque`
only *delays* delta, the kernel still unfolds as a last resort — so the four
blinding-leg copies cost ≈ 10.7 s each and the Merkle-chain group (whose
sides are *not* convertible) did not terminate in 10 minutes.  Split with
`repeat apply conj` instead (it fails on a non-conjunction, leaving the leaf
to the intended tactic) and close the trailing `True` with `exact I`: the
same enumeration then costs ≈ 6 s in total.

Two companions from the same enumeration:

- **Keep the per-fact tactic away from bare `cbn` once a hand lemma has
  rewritten one side.**  With the goal `Point.x (t_cm_old (tables_of w)) =
  Γ.(advice) A0 (WitnessInput CmOld) 0`, a bare `cbn` ran > 6 min; stating
  the cell reading as its own `reflexivity` lemma (`cmold_read`) and closing
  by `rewrite` is instant.  Bare `cbn` is safe only where *both* sides are
  advice dispatches at concrete addresses (the 723-fact mechanical group,
  ≈ 0.06 s per 46-fact chunk).
- **Pin the fact list as a literal and certify coverage, not equality.**
  The list is reached by `List.forallb (fun f => existsb (fact_beq f) …)`
  over the reified `witness_facts` (one `vm_cast_no_check`, 0.4 s), so the
  pinned list may be regrouped by proof shape without re-running the scan;
  `fact_beq` needs no completeness proof, only `fact_beq f g = true → f = g`.
  The 294 KB of literal `Definition`s elaborate in ≈ 0.03 s per 46-fact
  chunk — the literal-table superlinearity above does not appear at this
  entry size.

### Compose replay/stream equalities as terms — never `rewrite` at the event stream

`rewrite (replay_is_ok_conflict_free orchard_events _) in Hok`, on the
hypothesis `replay_is_ok orchard_events (initial_grid _ _) = true`, costs
**445 s** in one tactic (measured 2026-07-27,
`circuit_completeness/operational/main.v`). The wildcard grid argument makes
`rewrite` unify through evarconv, which whnf-normalizes the 19,679-event
stream and the initial grid on the lazy machine; the same fact composed as a
term is instant:

```coq
Lemma orchard_conflict_free : conflict_free orchard_events = true.
Proof.
  exact (eq_trans
    (eq_sym (replay_is_ok_conflict_free orchard_events
      (initial_grid (fun _ _ : Z => 0) (fun _ _ : Z => 0))))
    (orchard_replay_ok (fun _ _ : Z => 0) (fun _ _ : Z => 0))).
Qed.
```

Same family: `destruct (conflict_free orchard_synthesis_events)` sends the
whole conflict scan (quadratic in the 15,067 writes) to the lazy machine —
project with `Bool.andb_true_iff` instead of case-splitting the boolean. This
is the general rule of the "unification / `fold` / `lia` vs heavy constants"
and "never `match` on a concrete heavy computation" sections, at the
event-stream layer: the replay stream, the fact list and the configured
system are all heavy computable constants, so every equation about them must
be `eq_trans`/`eq_sym`/`proj` composition, never `rewrite`, `destruct`,
`change` or `fold`.

Two related traps recorded from the same file set (2026-07-26/27):

- **`region_start_of` is a linear scan** of the 395-entry placement list
  (`circuit_synthesis_layout.v` `region_start_of_list` over `region_starts`,
  after a `region_index_of` traversal of the nested `RegionId`). Calling it in the
  inner loop of a per-point scan is quadratic-times-linear: a 4,862 × 4,862
  certificate that recomputed it did not finish in 12 minutes, and fell to
  31.8 s once absolute rows were precomputed once into a global.
- **`Complete.enabled_memb` / `fixed_lookup` / `table_lookup` re-extract from
  the fact list on every call.** With `facts` spelled as the *application*
  `layouter_facts circuit.synthesize`, the VM re-runs the whole
  14,813-fact synthesis reification per call. Hoist `enabled` / the fixed
  writes / the table entries into global `Definition`s and scan those.

### Generalize every compound atom before stripping `mod`s with `setoid_rewrite`

The `Zdiv.eqm` toolkit strips the guarding `mod` of each `BinOp`/`UnOp` by
`setoid_rewrite` through the ring morphisms.  Its occurrence search reduces
the terms it traverses, so any *constant* left in the goal is delta-expanded
and then evaluated: `constants.two_inv` (`(pallas_p + 1) / 2`, over
`pallas_p = 2 ^ 254 + t_p`) turned the Sinsemilla generator-table ordinate
goal into a 15 kB iterated product of `2`s in 36 s, and a second pass did not
terminate within 120 s (measured 2026-07-25 on
`circuit_completeness/forward/lookups_witness.v`, `sins_row`) — the `Z.pow`
trap above, reached through rewriting rather than a reduction tactic.  The
same search descends into a folded gradient (`rr_l1 A G`, a `BinOp.div`) and
forces the field inverse.

Rule: before the strip, replace every compound subterm and every named
constant by a variable — `revert` the fact hypotheses, then
`generalize <term>; intro x` for each of the chord gradients, the point
coordinates, the derived point's coordinates and the numeric constants, and
re-`intro` the facts.  The goal becomes a polynomial over variables, the
strip is instant, and the closing step is one `eqm_of_diff` with an explicit
linear combination plus `ring`.  This is the same discipline
`forward/sinsemilla.v` applies with `generalize (rr_l1 A G); intro l1` in
`mid_x_eqm`; `lookups_witness.v` extends it to the constants.  Cost of the
resulting file: 30 s (was 13 s before the five Sinsemilla site leaves, whose
per-row fixed-plane `vm_compute` certificates over 32 layers × 52 rows add
≈ 5 s).

### Concrete-fuel divide-and-conquer fixpoints explode under unification

`fft 11 w v` (the radix-2 inverse-NTT, two recursive calls per level)
with the concrete depth 11 and a symbolic list doubles at every
unfolding: any tactic whose unification touches the term — `apply
in_map_iff in H`, `f_equal` between mismatched sides, `rewrite` pattern
search — diverges (>7 min).  `Strategy opaque [fft]` protects kernel
conversion but NOT tactic unification: additionally state every consumer
lemma over an *abstract* list and instantiate at the concrete term with
pure `exact`-terms (`eq_trans`/`f_equal`/`eq_ind_r` compositions), so the
only checks are syntactic.  The same discipline carries into the leaf
assembly: a replayed-column certificate
is stated as the raw `option_map` term and consumed by an `eq_trans` of
`f_equal`s — an `injection`/`rewrite`-based version sat >10 min, and a
`rewrite` against a goal containing an applied never-computable spec
would lazily evaluate that spec, which must not happen.

### Instantiate curve-law wrappers with fully applied terms

`apply (GroupOrderCosets.mul_on_curve …)` against an `on_curve`
goal stalls in evarconv (>5 min) where the fully applied `exact` term is
instant; curve-instance group-law wrappers should be `exact`-style
one-liners for this reason.  When such a wrapper is itself applied by later proofs
the unification stays within one definitional layer and does not stall.

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

### Regenerate `_CoqProject` after any branch switch that deletes `.v` files

`_CoqProject` and `CoqMakefile` are generated (both gitignored) by the
`CoqMakefile: $(VFILES)` rule in `Garden/Makefile`, which re-runs only when a
prerequisite is *newer* than the target. A deletion is invisible to that test:
the file simply drops out of `$(VFILES)`, nothing is newer, and the stale
`_CoqProject` keeps listing sources that no longer exist. `make` then stops
before compiling anything, naming a missing *source*:

```
make: *** No rule to make target 'EllipticCurve/GroupOrderTight.v', needed by '.CoqMakefile.d'.  Stop.
```

which reads like a broken dependency rather than a stale artifact. Force the
regeneration — `rm -f CoqMakefile CoqMakefile.conf _CoqProject && make
CoqMakefile` — and confirm the entry count matches the tree
(`grep -c '^\./' _CoqProject` against `find . -name '*.v' | wc -l`, modulo
`blacklist.txt`). This bites on every branch switch that removes files, so it
is worth doing unconditionally after one; adding or editing files is safe,
since those do update the timestamp.

### Ring identities: `mod_ring_solve`, not `field_solve`

For pure mod-p polynomial identities use `mod_ring_solve`
(`Garden/Halo2/lemmas.v`), reserving `field_solve` for genuine linear
arithmetic; see `docs/halo2-proof.md` for the rule and its mechanism.

## Current costs

Full clean build (`make clean`, then `make -j32`, measured 2026-07-27 on an
otherwise idle 32-core machine): **1 089 s wall over 399 files**, with the
per-file times summing to 7 529 s. The wall clock is not set by a dependency
chain but by a single file: `instance/certs.v` alone is 792 s, i.e. 73 % of
the build, and everything else fits around it. Next are `instance/domain.v`
(593 s) and then, well behind, `instance/read.v` (259 s) and the eight
Sinsemilla provenance shards (≈ 257 s each, fully parallel).

Measure a build total with `make clean` first: without it `make` recompiles
only the changed cone, and a 26-file incremental rebuild reports a "build
time" that has nothing to do with the tree. Note also that `/usr/bin/time`'s
CPU figure for `make` undercounts, because the `rocqworker` shim runs each
worker in its own transient systemd scope; sum the per-file `TIMED=1` times
instead.

That figure was measured over the 399 files of
`valerii-huhnin@orchard-completeness`, so it excludes the 24 compiled-plonkish,
pinned-vk and transcript-repr files this branch adds; those are listed
individually among the heavy leaves below, and the whole-branch total has not
been re-measured since they landed. The vk-commitment MSM and Vesta SRS layers
are not on this branch at all — they live on `valerii-huhnin@msm-stretch`, and
their entries are kept in a separate section at the end only because the
pitfalls above cite them as worked examples.
The 2026-07-06 figure (≈ 1 570 s CPU over 275 files,
≈ 212 s ideal wall, wall clock set by the Sinsemilla chain `sinsemilla_s` →
`chip_proof` → `hash_to_point_round_proof` → `circuit_proof/merkle.v`)
predates the completeness-instance layer entirely. Heavy leaves:

- The short-lookup closure leaves (2026-08-03), all cheap:
  `Orchard/circuit_proof/lookup_closure.v` 4.0 s,
  `lookup_closure_old_note.v` 1.7 s, `lookup_closure_ivk.v` 1.6 s,
  `Orchard/circuit_adversarial.v` 1.0 s. Each site inventory is four raw
  `List.forallb … = true` certificates closed with `vm_cast_no_check`, and
  their whole cost is forcing the two heavy globals *once per file*: the
  19,679-event `orchard_events` (≈ 0.5 s, in the `q_running`-absence scan)
  and the 14,817-fact `layouter_facts circuit.synthesize` (≈ 0.1–0.2 s, in
  the fact-presence scan). The eleven / eleven / three sites themselves add
  ≈ 0.01 s of checking. Splitting the three families across files therefore
  costs ≈ 0.7 s of duplicated forcing each against the merge-by-heavy-global
  rule above — paid to keep the three families in separate files;
  merging them is a pure move of definitions and certificates. No
  sharding is needed at this scale. `circuit_adversarial.v` computes
  nothing: it is term composition only.
- The exceptional-branch (⊥-disjunctive Action statement) leaves
  (2026-08-03), also cheap: `Orchard/circuit_proof/protocol_spec_bot.v` and
  `adversarial_api.v` ≈ 1 s each (pure list/`Z` algebra and statements),
  `note_commit_bot.v` 1.1 s, `ownership_bot.v` 7.5 s (the two duplicated
  ~120-line half-ladder navigations of the ladder-nondegeneracy
  derivation),
  `merkle_bot.v` 8.0 s (the 64 Merkle `b1`/`b2` `ShortSite` certificates
  cost < 2.5 s of it; the rest is the duplicated per-layer region
  navigation), `circuit_proof/adversarial.v` 2.5 s and the extended
  `circuit_adversarial.v` 2.8 s — both term composition plus the five
  `QWitnessPointNonId` layouter-fact navigations. None carries an
  input-dependent `vm_compute`. The whole incremental cone of the change
  (the `valid_action_inputs.v` comment update plus the `cv_net_value.v` /
  `bundle/` weakening, hence `circuit_operational`, `compiled/*`, `vk/*`,
  the operational-completeness leaves and the closure files) was 151 s wall
  / 363 s CPU on a 32-core machine — the low end of the 350–400 s CPU
  estimate for a touch of that cone.
- `Orchard/circuit_operational.v` (2026-07-14): 17.8 s / 1.66 GB peak —
  dominated by `orchard_replay_ok`, a single `vm_cast_no_check` VM run of
  `replay_is_ok` on the 19,679-event Orchard stream (12.3 s before the
  post-NU6.3 update; the conflict check is quadratic in the 15,067 write
  events); the other three
  `vm_compute` certificates (`constants_materialized` coverage,
  `instance_free`, `flattening_ok`) are < 0.5 s each, and
  `orchard_operational_sound` pays ≈ 4.5 s of delta conversion at
  `exact`+Qed. The block conditions of `Halo2/realize/disjoint.v` are the
  placement-generic alternative if the whole-stream replay certificate
  ever becomes too heavy.
- `Orchard/compiled/main.v` (2026-07-17): ≈ 92 s / 3.3 GB peak — the
  per-assignment indicator certificate dominates: checking every selector
  assignment's expression against its activation vector on all 2048 domain
  rows through `combination_view` costs ≈ 78 s in one scan, so it is sharded
  into four 14-assignment `forallb` windows (25 / 13 / 20 / 21 s,
  reassembled by `forallb_chunk4`); the σ-construction certificate
  (`orchard_sigma_some`, union-find closure of the 3 004 copies over
  15 × 2048 cells) is 3.3 s, the first certificate pays the ≈ 3.5 s
  `compiled` global build (shared by every later `vm_compute` sentence in
  the file), `orchard_compiled_eq` is 1.5 s, and everything else —
  `finite_domain_ok_b` included — is < 0.2 s.
- `Orchard/compiled/check.v` (2026-07-17): ≈ 4.7 s — the twelve
  pinned-vk parity certificates against
  `circuit_description_post_nu6_3`, each a
  `vm_cast_no_check` of an `eq_refl` comparing a projection of
  `OrchardCompiledCheck.compiled` (the compiled Orchard system) with the
  pinned literal; the first sentence pays the one-time `compiled` global
  build shared by the rest. `compiled/pinned.v` (the pinned literal
  data) is ≈ 1.1 s; the five
  `Halo2/plonkish/{main,compile,mock,sigma,orbit}.v` proof-layer files
  are each < 1 s (generic theorems, no concrete-instance `vm_compute`).
- `Orchard/compiled/algebraic.v`: ≈ 21 s / 1.3 GB — the L1
  side-condition certificates: the σ-mapping scans and boundary fixed
  points, the `delta` order/small-power checks (one 222-bit `fast_pow`),
  the lookup replacement-exactness scan over the domain rows, and the
  event-stream value/fill scans, each a `vm_cast_no_check`; the first
  certificate pays the shared `compiled`/σ global builds.  The
  `coset_lbl_inj` proof keeps every `lia` scoped with `clear -` — the
  unscoped form cost ≈ 4.5 min across six calls (18–76 s each) in the
  hypothesis context carrying the `Fpow`-heavy coset equations.
- The `transcript_repr` T1 leaves: `Orchard/vk/parity.v` ≈ 6.5 s —
  the byte-parity certificate (`vm_cast_no_check` of a primitive-string
  equality between the printed pretty rendering and the 1.3 MB imported
  dump) plus the compact-length certificate; the first pays the shared
  `compiled` + printer global builds (the printer itself is ≈ 2 s after
  the `rev_append` fix — see the `List.rev` pitfall above).
  `vk/bytes.v` (the 20 sharded PrimString dump literals),
  `vk/data.v`, and `vk/print.v` are ≈ 1 s each.
- `Orchard/vk/transcript_repr.v` (T2, the Fiat–Shamir binding scalar):
  ≈ 33 s — the input-length and block-count certificates pay the one-time
  VM build of the 285,142-byte hash input and its 2,228-block split
  (≈ 9 s + 5 s, shared by the later sentences of the file); the four
  state-threading shard certificates (557-block BLAKE2b ranges between
  pinned 8-word chain values) are ≈ 2.5 s each; the final-block digest
  and `mod pallas_p` certificate is sub-second; the generic
  `compress_blocks_chunk` lemma pays one ≈ 8 s `lia` in its base case.
  See the "unification/`fold`/`lia` vs heavy constants" pitfall above —
  the naive proof of the same theorem costs > 20 min across three
  divergent sentences.
- The R4 counting/boundary leaves (2026-07-20):
  `Halo2/plonkish/counting.v` ≈ 11 s / 1.26 GB — no concrete-instance
  `vm_compute` (the per-family counting theorems, bad-set cardinality
  bounds, and constructive case corollaries are all generic over an
  arbitrary repetition-free challenge list, at impredicative `Set` only);
  the cost is proof-checking the `roots_le_pdeg`-based root-count and
  matching arguments plus the plonkish dependency load. `boundary.v`
  ≈ 0.6 s (the two composed single-challenge corollaries and the named
  `IPABinding`/`MultiopenReduction`/`FiatShamirChallengeGood` `Definition`s
  — no certificate). Neither is on any other file's `Require` path (both
  are R4 endpoints), so they are never re-paid while iterating elsewhere.
- The completeness-instance certificate leaves (remeasured 2026-07-17, over
  the hoisted `tables.v` record — which now also carries the variable-base
  ladder record of `tables_vb.v`, one linear double-and-add fold with two
  field inversions per bit; every run pays the ≈ 4 min record build once,
  then per-cell lookups; the seven leaves are mutually independent and
  compile fully parallel, ≈ 16 min wall on a free machine, set by
  `instance/read.v`):
  file totals remeasured 2026-07-27 inside the 32-way parallel clean build,
  so they run a little above their isolated cost:
  `instance/certs.v` — every certificate whose subject is `Γtest`: the
  enabled-point shards of all region families, the 3 004 copy/constant
  witness facts, and the reader side of the read-back. 791.6 s, of which the
  one-and-only `tables_of` record build is the bulk; the second and later
  certificates in the file cost no measurable time. This is now the critical
  path of the whole build (73 % of its wall clock);
  `instance/domain.v` (`valid_b`, the linear Merkle/Sinsemilla
  nondegeneracy clauses, and the variable-base ladder chain) 593.5 s, of
  which `test_input_valid_b` is ≈ 330 s, `mul_chain_cert` 49 s,
  `merkle_nondeg_cert` 47 s and `nc_new_nondeg_cert` 45 s;
  `instance/read.v` (the specification side of the read-back: the 32-layer
  Merkle fold of `anchor_of_leaf` plus the commitments) 258.9 s;
  `instance/cert.v` 1.5 s, and `instance/defs.v`, `generator/tables.v`,
  `generator/tables_vb.v`, `generator/tables_nc.v` and
  `generator/honest_assignment.v` (definitions only) ≈ 2 s each.
  Two earlier arrangements are worth recording. The variable-base
  nondegeneracy clause was four sharded leaves (`instance/mul_{a..d}.v`, one
  `Pallas.mul` per bit index, ≈ 90 min of CPU and 31 min of wall between
  them); it is now the 49 s `mul_chain_cert` — see the chained-quantity
  pitfall. And the `Γtest` certificates were five leaves
  (`shards_merkle` 556 s, `shards_blocked` 512 s, `shards_misc` 456 s,
  `witness` 376 s, `read` 972 s) each rebuilding the record; merging them
  took the group from 3 442 s to 1 534 s.
- The operational-completeness leaves
  (`Orchard/circuit_completeness/operational/`, measured 2026-07-27 on a
  shared 32-core host, full `.vo`): `certs.v` 70 s — nine
  `vm_cast_no_check` certificates, all input-independent, of which the
  restricted region-uniqueness scan is 32 s, the gate-queried fixed-cell
  scan 19 s, the 155,861-cell advice inversion 7 s, the enable-placement
  scan 5 s and the lookup-queried fixed-cell scan 5 s (the rest
  sub-second); `concrete.v` (the self-contained concrete instance, with its
  own copy of
  the certificate layer) 53 s / 1.3 GB; `main.v` 5 s (no certificate — the
  join is projections and hand-lemma rewrites, plus the two
  `conflict_free` term compositions); and the three generic layers
  `replay_planes.v` / `agreement_congruences.v` / `placed_intro.v` under
  0.7 s each (no `vm_compute`, no concrete data, so they never appear on
  this cost map and iterating on them is free). The certificate layer is
  input-independent by construction, so the concrete and universal rungs
  share it and neither pays a `tables_of` record build.
- `Orchard/circuit_completeness/generator/certificates.v`: ≈ 8.7 s total — three
  `vm_cast_no_check` certificates over `layouter_facts circuit.synthesize`
  (14,813 facts, built by the VM in ≈ 0.07 s). The
  `no_conflicting_writes` certificate dominates at ≈ 7.9 s: a first-match
  scan quadratic in the 6,948 fixed writes. The `selector_guarded`
  (configured system only) and `lookup_defaults_ok` (three lookup
  arguments against table row 0) certificates and the
  `layouter_table_rows = 1024` fact are each < 0.05 s. Single-process
  `vm_compute` stays under 1 GB, so no `native_compute` or region-family
  sharding is needed; shard `no_conflicting_writes` by top-level
  `RegionId` constructor if the fixed-write count grows.
- Fixed-base table leaves (`circuit_proof/<base>/table.v`): ~79 s ∥ 80 s ∥
  80 s ∥ 20 s in parallel (value_commit_v is the cheap one); the
  note_commit_r leaf lands in the ~100 s band; the commit_ivk_r leaf
  measured 81 s / 742 MB peak (2026-07-09).
- The commit_ivk_r certificate leaves (2026-07-09): `disc_cert.v` 19 s,
  `sign_cert.v` 7.3 s, `x_cert.v` 6.5 s,
  `protocol_mul/commit_ivk_r.v` 0.8 s — all inside the per-family bands
  below.
- The ownership variable-base-mul leaves (2026-07-09):
  `circuit_proof/ownership/var_base_incomplete.v` ~30 s — dominated by two
  symbolic-row `field_solve`s (the `q_mul_2`/`q_mul_3` secant conjuncts)
  plus six gate-membership ltac `In`-proofs; `var_base_mul.v` ~21 s;
  `var_base_overflow.v` ~10 s; `var_base_complete.v` ~6 s.
- `sinsemilla/hash_to_point_round_final_proof.v`: 96 s, parallel with the
  round proof; `hash_to_point_proof.v` (shared definitions) 3 s;
  `hash_to_point_fold_proof.v` 1.5 s.
- `circuit_proof/fixed_base/main.v`: 78 s.
- The `order_<base>.v` certificate leaves: < 1 s each — instances of
  `PallasOrder.pallas_mul_q_on_curve` at the generator's
  `reduced`/`on_curve` facts (2026-07-10; formerly 16 s ladder
  certificates each, value_commit_v 30 s). The only remaining `[q]·G`
  ladder is `Pallas.placeholder_order` (`EllipticCurve/Pallas.v`), the
  bootstrap certificate the general theorem itself consumes — it cannot
  be replaced by instantiation without circularity.
- Discriminant certificates (`circuit_proof/<base>/disc_cert.v`): ≈ 92 s CPU
  total across the five self-contained files (≈ 21 s per 85-window family,
  6 s for the 22-window value_commit_v).
- x-coordinate certificates ≈ 7 s each; window-sign certificates ≈ 9–10 s
  each.
- `circuit_proof/main.v` ~1 s; everything else seconds.
- The Poseidon constants-provenance pair (2026-07-10):
  `halo2_poseidon/grain.v` (executable Grain/MDS transcription, no proofs)
  < 1 s; `halo2_poseidon/p128pow5t3_provenance.v` ~6 s — 5.3 s in the first
  checker's `vm_compute` (one-time bytecode compilation of the pipeline
  closure), the remaining four checkers milliseconds each (see the
  match-scrutinee pitfall above for the elaboration trap this file dodges).
- The `GroupHash^P` chain (2026-07-10): `GroupHash/blake2b.v` and `xmd.v`
  < 1 s each (their `vm_compute` reference vectors included), `sswu.v` ~5 s
  (the transcription-check `vm_compute`s over the iso-Pallas constants),
  `group_hash.v` < 1 s; the checker leaves
  `Orchard/Pallas/generators_provenance.v` ~9 s (six points) and
  `q_points_provenance.v` ~5 s (three points) — one raw-`forallb`
  `vm_compute` each, recomputing BLAKE2b/XMD and the witnessed SSWU +
  `iso_map` per point with pasted offline square-root witnesses
  (`scripts/generate_grouphash_witnesses.py`), never an in-kernel
  `field_sqrt`.
- The Sinsemilla S-table provenance shards (2026-07-10):
  `Halo2/halo2_gadgets/sinsemilla/provenance/shard_{0..7}.v` — ~196 s each
  (`sinsemilla_s_shard_N_check`, a 128-point raw-`forallb` `vm_compute`
  over the same witnessed `GroupHash^P` recomputation, ~1.5 s per point;
  witnesses pasted from `scripts/generate_sinsemilla_witnesses.py`; the
  companion index lemma's `vm_compute` is negligible). The eight leaves are
  mutually independent and off every other file's `Require` path (only
  `provenance/main.v`, < 2 s, consumes them), so they run fully parallel:
  ~200 s wall on eight cores, never re-paid while iterating elsewhere.
  Sharding finer was declined — per-leaf memory is small (< 1 GiB) and the
  cost is pure per-point CPU, so more shards only add `Require` overhead.

Remaining single-file levers: the `hash_to_point_round_proof` round proof
and the `sinsemilla_s` table literal, the two largest links in the chain
above. The round proof's cost is two 58-s
`with_strategy opaque […] cbn` normalizations plus ~36 s of `field_solve`s;
an untried whitelist `cbn [names]` over the gate-eval chain would likely
help, but do NOT retry swapping the `cbn` for `lazy` — `lazy` inlines the
`Z.add` fixpoint at stuck symbolic applications (`row + 1`), breaking every
later rewrite pattern; `cbn`'s refolding is load-bearing there.


### Leaves of the vk-commitment MSM and Vesta SRS layers (not on this branch)

The entries below measure files that live on `valerii-huhnin@msm-stretch`
and are **not** present in this worktree, so they contribute nothing to the
build figure above. They are kept here because the pitfalls elsewhere in this
file cite them as worked examples; re-measure them against that branch before
relying on the numbers.

- The vk-commitment MSM layer, on `valerii-huhnin@msm-stretch` (2026-07-24;
  machinery + the fixed-column-0 calibration certificate):
  `EllipticCurve/GroupOrderTight.v` ≈ 8 s (the three-coset order theorem
  and the ladder-distribution point algebra, all symbolic);
  `EllipticCurve/VestaOrder.v` ≈ 115 s — dominated by the
  [pallas_p]-fold `placeholder_order` ladder (`vm_cast_no_check`, ~100 s)
  plus the Euler-criterion cube certificate (~1.3 s);
  `Orchard/vk_msm.v` ≈ 14 s (95 `Qed`, no concrete-instance heavy
  `vm_compute`; the largest sentence is `fft_spec`'s `Qed` at ~19 s under
  a cold elaborator, ~7 s warm);
  `Orchard/vk_msm_data_fixed0.v` ≈ 19 s (2 × 2048 pasted literals + two
  checkpoint points);
  `Orchard/vk_msm_calibrate.v` ≈ 110 s — the replayed-column certificate
  (≈ 17 s before the post-NU6.3 update: the 19,679-event replay + 2048
  installed-plane reads), the
  inverse-NTT coefficient certificate (≈ 82 s: 11-level radix-2 FFT,
  ~22.5 k modular multiplications), the sub-second range/length/
  blind-and-compare certificates, and the term-style assembly theorem;
  `Orchard/vk_msm_calibrate_{a,b}.v`: MEASURED_SHARD — one half-range
  1024-base Pippenger `vm_compute` each (32 windows of 8 bits,
  255 filter-buckets, suffix-sum aggregation; ≈ 49 k affine point
  operations at ≈ 57 ms each), mutually independent, ≈ 0.7 GB peak.
  The 44-commitment fan-out runs two such leaves per commitment fully
  parallel; under route (b) every column is a dense 2048-scalar MSM, so
  the per-commitment cost is uniform.

- The Vesta SRS provenance shards, on `valerii-huhnin@msm-stretch`
  (2026-07-23):
  `Orchard/vk_srs_cert_{0..15}.v` — ≈ 295 s CPU each
  (`vk_srs_shard_N_check`, a 128-point raw-`forallb` `vm_compute` over the
  witnessed `GroupHashVesta` recomputation — BLAKE2b XMD, witnessed SSWU
  onto iso-Vesta, iso-curve addition, `iso_map` — ≈ 2.3 s per point under
  16-way parallel load; witnesses pasted from
  `scripts/generate_vk_srs_witnesses.py`, never an in-kernel `field_sqrt`).
  The sixteen leaves are mutually independent and only
  `Orchard/vk_srs_cert.v` (≈ 70 s: the 2049-point on-curve/reducedness scan,
  the single-point `w` certificate, the index scan, and list-plumbing
  assembly — all `Qed`) consumes them: ≈ 5.2 min wall for all 16 on 32
  cores, never re-paid while iterating elsewhere.  Supporting leaves:
  `GroupHash/sswu_vesta.v` ≈ 14 s (two Euler-criterion nonsquare checks, the
  λ-provenance `modpow`, and the pinned SSWU test vectors),
  `GroupHash/group_hash_vesta.v` ≈ 8 s (the pinned Vesta `hash_to_curve`
  reference vector), the sixteen `Orchard/vk_srs_data_*.v` literal files
  ≈ 2.5 s each (see the literal-table sharding pitfall above),
  `EllipticCurve/Vesta.v` and `Orchard/vk_srs_entry.v` < 1 s.

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
ladders from ≈ 30 min to 87 s, the `order_<base>.v` ladder certificates
from ≈ 5 min each to 16 s (value_commit_v 30 s) — later retired to the
sub-second instantiations in the cost table above. The first full clean
rebuild after the switch:
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
statements stayed byte-identical, so consumers and `Print Assumptions` on
the whole-circuit determinism theorem were untouched. With the per-entry
cost gone, the 50-file band sharding cost more in per-file `Require` loading
than the checks themselves and was retired to one self-contained
`disc_cert.v` per
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
