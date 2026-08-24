# Installation and Build Tutorial

This document provides an introduction to how to build the `garden` project for development. 

Before starting, make sure you have `Rust` and `opam` installed.

The Orchard verification visualization is a separate frontend and requires
[Node.js 22](https://nodejs.org/) and npm. The website data is generated from
the Rocq structure and parity snapshots rather than committed.

## Setting Up Dependency Submodules

Fetch the implementation repositories recursively, and fetch the Rocq Rust
model without its translator fixtures and nested implementation repositories:
```sh
git submodule update --init --recursive \
  third-party/Plonky3 \
  third-party/brevis \
  third-party/circom \
  third-party/circomlib \
  third-party/halo2 \
  third-party/orchard
git submodule update --init third-party/rocq-of-rust
```

Garden compiles the minimal MIT-licensed Rocq source closure directly from
`third-party/rocq-of-rust/RocqOfRust`. The rocq-of-rust nested submodules are
not build inputs and remain uninitialized.

## Install Opam Environment

In order to install dependencies and build the Rocq part of the project, run the following commands for the proper `ocaml` environment.

Create a new opam switch:

```sh
opam switch create garden-rocq-9.0.1 ocaml-base-compiler.5.2.0
```

Update shell environment to use the new switch:
```sh
eval $(opam env --switch=garden-rocq-9.0.1)
```

Add the repository with Rocq packages:
```sh
opam repo add rocq-released https://rocq-prover.org/opam/released
opam update
```

If you don't have a local Rust environment pre-installed:
```sh
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y
source "$HOME/.cargo/env"
```

Then we install the dependency files in the Rocq program:
```sh
opam install -y --deps-only Garden/rocq-garden.opam
rocq -v
```

## Rocq CI Dependency Image

CI prebuilds the dependencies from `Garden/rocq-garden.opam` in
`ghcr.io/formal-land/garden-rocq-ci:rocq-9.0.1`. The image publication
workflow runs after relevant changes reach `main`, and it can also be started
manually. Each build publishes the stable Rocq-version tag and a
commit-specific `sha-<commit>` tag. BuildKit's GitHub Actions cache speeds up
subsequent image rebuilds.

The first publication uses a strict two-stage rollout:

1. Merge the Dockerfile and publication workflow while Rocq CI still uses the
   upstream `rocq/rocq-prover` image.
2. Wait for the `Rocq dependency image` workflow to finish.
3. In the GitHub package settings for `garden-rocq-ci`, change the package
   visibility to **Public**.
4. Verify anonymous access:

   ```sh
   docker manifest inspect ghcr.io/formal-land/garden-rocq-ci:rocq-9.0.1
   ```

5. Only after that command succeeds, change `custom_image` in
   `.github/workflows/rocq.yml` to
   `ghcr.io/formal-land/garden-rocq-ci:rocq-9.0.1`.

Keep `opam install -y --deps-only Garden/rocq-garden.opam` in the Rocq
workflow after switching images. It is normally a fast consistency check, and
it installs any dependency delta introduced by a pull request before the image
is rebuilt from `main`.

## Setting Up Circom

We start from the main repository.

Going into the `third-party/circom` folder:
```sh
cd third-party
cd circom
```

Build `circom` via `cargo`:
```sh
cargo install --path circom
```

Getting back to the main repository:
```sh
cd ../..
```

Then we aim to translate the `Circom` library:
```sh
cd third-party/circomlib
```

We first translate each Circom circuit to JSON.
```sh
find . -name '*.circom' -execdir circom {} \;
```

After that we get back to the main repository:
```sh
cd ../..
```

Then we translate the JSON files to Coq
```sh
python scripts/rocq_of_circom_ci.py
```


## Compile Rocq Project

Finally, we compile the Rocq project.
```sh
cd Garden
make
cd ..
```

To compile one Rocq file directly, run from `garden/Garden` and keep the same
logical load path:

```sh
opam exec -- coqc -impredicative-set -R . Garden Halo2/halo2_gadgets/poseidon/pow5_proof.v
```

The current Halo2/Orchard proof work is checked with `-impredicative-set`.

To regenerate the checked constraint snapshots:

```sh
cd Garden
make snapshot
cd ..
```

To regenerate and verify the Orchard Rust implementation snapshots from the
pinned `third-party/halo2` and `third-party/orchard` submodules:

```sh
git submodule update --init --recursive third-party/halo2 third-party/orchard
scripts/check_orchard_implementation_snapshots.sh
```

The script keeps Rust build artifacts and temporary files under
`third-party/orchard/target`. It checks the high-level Orchard JSON together
with Garden's configure, synthesis, and selector-compression snapshots. The
Rocq synthesis layout is intentionally not overwritten: Garden extends that
file with typed `RegionId` mappings used by the proofs.

It also checks Orchard's Post-NU6.3 pinned verifying-key description against
the Rust keygen and runs `scripts/generate_vk_pinned.py --check`. That generator
keeps the Rocq dump shards, commitment literals, BLAKE2b checkpoint states, and
Fiat–Shamir binding scalar synchronized with
`circuit_description_post_nu6_3`. To regenerate those Rocq artifacts directly:

```sh
cd Garden
make orchard-vk-pinned
make orchard-vk-pinned-check
cd ..
```

## Orchard proof-verifier fixtures

The Post-NU6.3 proof-verifier corpus lives at
`Garden/Orchard/Verifier/Snapshots/post_nu6_3.json`. Its Rust producer invokes
the public pinned `orchard::Proof::verify` path on deterministic restricted and
unrestricted one-action proofs, a restricted two-action proof, and mutations
covering every transcript-read block, canonical decoding, instance binding,
multiopen, and IPA. The JSON contains raw proof bytes and exactly ten canonical
little-endian public scalars per action.

The fixture producer pins and requires the
`x86_64-unknown-linux-gnu` Rust target with a 64-bit `usize`; it exits instead of
writing a corpus on another target. The corpus contains exactly 40 authored
cases, and its authored semantic manifest contains 44 verifier/read-schedule
branch IDs. The producer and translator require exactly 40 cases and exactly
44 unique IDs, and check that every ID names at least one case. These counts
describe the maintained test inventory, not measured Rust source-line, branch,
or instruction coverage. The corpus has four `verified` and 36 `rejected`
outcomes; it has no panic case.

Regenerate the JSON, its Rocq fixture module, and the compact verifier runtime
data with:

```sh
cd Garden
make orchard-verifier-snapshots
make orchard-verifier-runtime-data
cd ..
```

The runtime-data generator consumes Orchard's pinned
`circuit_description_post_nu6_3.json` and materializes only the 193 compiled
gates and three lookup arguments needed during verification.
`PostNu6_3Materialization.v` proves those literals equal to the independently
derived Garden circuit values, so the Python generator is not an unchecked
equivalence boundary.

The Rust freshness check uses the crate's lockfile, validates that the index
gitlinks and clean initialized submodules match the recorded commits, and then
builds the deterministic proofs; it can take several minutes. Final verifier
acceptance runs both Rust release and debug freshness, the ordinary Rocq tests,
and the extracted all-case replay:

```sh
cd Garden
make orchard-verifier-snapshots-check
make orchard-verifier-snapshots-debug-check
make orchard-verifier-tests
cd ..
```

`orchard-verifier-snapshots-check` is the locked Rust release-mode freshness
check; `orchard-verifier-snapshots-debug-check` repeats it in debug mode. The
two modes must produce identical proof bytes and outcomes. The named verifier
target reads the checked-in corpus and does not itself run the Rust prover. It
checks the generated Rocq fixture module, the compact runtime data, the
runtime-data materialization theorem, the verifier unit tests, Replay, the
fixed-SRS assurance modules, and the extracted all-40 behavioral comparison.

The 64-bit OCaml runtime preflight must pass before extraction. The replay
build target also depends on this check, but running it explicitly gives a
clear diagnostic before generating or compiling OCaml.

The replay, report normalization, fixture preparation, and verifier remain
ordinary Rocq definitions. A valid case exceeded 120 seconds under
`vm_compute`, and this Rocq build has native reduction disabled, so exhaustive
behavioral replay uses a small OCaml extraction harness instead. The harness
maps both `nat` and `Z` to unbounded Zarith integers
(`ExtrOcamlNatBigInt`/`ExtrOcamlZBigInt`) and uses Rocq's standard Int63 and
persistent-array runtime mappings. Thus snapshot indices, proof-list lengths,
and other logical `nat`/`Z` values are unbounded; the optimized field and MSM
kernels deliberately use `Uint63` words and primitive-array indices on a
64-bit OCaml runtime. `make orchard-verifier-replay-build` checks that runtime
width as part of the build. The execution-test trusted computing base includes
Rocq extraction, the explicit rocq-of-rust type-metadata erasures, Zarith, the
Int63, PArray, and PrimString runtime mappings, the OCaml compiler and runtime,
and the handwritten replay driver. It is not a kernel theorem or a general
extracted-verifier API.

At the Rust-shaped boundary, wire bytes use the rocq-of-rust integer carrier
with exact checked and wrapping `u8` operations, and the pinned Rust producer
fixes `usize` to 64 bits. Verifier scalar and base-field operations are reduced
modulo the corresponding Pasta moduli. Reader offsets, lengths, and fixture IDs
are logical Rocq naturals; they agree with Rust `usize` for every physically
realizable 64-bit slice in this corpus, but the public Rocq list API does not
carry a separate proposition that its length is at most `usize::MAX`.

`make orchard-verifier-replay-build` typechecks the Rocq entry point, extracts
it, and compiles and links the ignored executable. The exact all-case command
is:

```sh
cd Garden
make orchard-verifier-replay-extracted
```

It exits nonzero unless all 40 recorded outcomes match, including treating
`BackendUnavailable` as a mismatch. It remains a standalone target for
localized reruns and is also a dependency of `orchard-verifier-tests`, so CI
cannot accept a successful extraction or link without the `--all` execution.

The verifier keeps a Rust-shaped MSM for auditability, while its fixed-SRS
evaluation path has a proved refinement to that reference MSM under the stated
point-well-formedness and checked-SRS premises. The replay module normalizes
the Rocq report and compares it with each recorded Rust outcome.

The concrete fixed-SRS premises come from generated provenance certificate
shards. Some of those shards use `vm_cast_no_check` to discharge very large
closed computations. That use does not appear as an axiom in `Print
Assumptions`, so an empty assumptions report does not remove this trusted
computation step from the assurance boundary.

Orchard's typed `Instance` API makes malformed instance encodings unreachable
in the Rust producer; separate executable Rocq examples exercise Garden's
untyped invalid-byte, invalid-width, noncanonical-scalar, and non-boolean-flag
boundaries.

The differential corpus is behavioral evidence for the pinned implementation;
it does not assert a proof of Rust-to-Rocq equivalence or Halo2 soundness. In
addition to the extracted-execution trust boundary above, the differential
oracle trusts the pinned Rust toolchain and Orchard/Halo2 sources, the fixture
producer, Serde serialization, and the Python JSON-to-Rocq translator. The
separate runtime-data materialization theorem checks that the generated gate
and lookup literals equal Garden's independently derived circuit values.

## Orchard Verification Visualization

The source for the Orchard Verification Journey, Atlas, Circuit Explorer, and
Circuit Grid lives in `web/orchard-verification`. The production bundle is
generated in the ignored `web/orchard-verification/dist` directory. It is
validated in CI and published at
`https://formal-land.github.io/garden/orchard/` from the dedicated `gh-pages`
branch. Generated website files must not be committed to the source branch.

On a fresh checkout, first generate the ignored raw structure snapshot using
the Rocq environment described above:

```sh
cd Garden
make orchard-structure-json-from-model
cd ..
```

Then install the pinned frontend dependencies and start the development server
from the repository root:

```sh
cd web/orchard-verification
npm ci
npm run dev
```

The `predev` hook regenerates the ignored website data in `public/data` before
Vite starts. `npm run build` does the same through its `prebuild` hook before
writing the ignored production bundle to `dist`. Run `npm run generate:data`
directly when only the derived JSON needs refreshing.

Open the URL printed by Vite for the Journey. Add `/proof-map.html` for the
Atlas, `/circuit.html` for the generated high-level Rocq circuit explorer, or
`/circuit-grid.html` for the parity-backed circuit layout grid.

The Circuit Explorer loads its generated JSON from `public/data`. When the Rocq
circuit or free-monad evaluator changes, first refresh the tracked raw
structure snapshot from `Garden/`:

```sh
cd Garden
make orchard-structure-json-from-model
cd ..
```

Once the raw structure snapshot exists locally, changes limited to source
mapping, the functional-flow manifest, or the frontend do not require another
Rocq build; `npm run generate:data` is sufficient.

The Circuit Grid combines the parsed-equal Rocq-model and Rust-implementation
configure/synthesis snapshots with the source-enriched Circuit Explorer
artifact. Regenerate it only after exact parity succeeds:

```sh
cd Garden
make orchard-configure-json-compare
make orchard-synthesis-json-compare
cd ..
npm --prefix web/orchard-verification run generate:data
python3 -m unittest scripts.tests.test_generate_orchard_circuit_grid
```

The generated `garden.halo2.circuit-grid.v1` data records V1 placement,
selector activations, fixed assignments, fill ranges, and copy endpoints. It
does not contain witness values or omitted ordinary advice assignments; its
metadata states those coverage limits explicitly.

The generation step requires the Rocq/OCaml environment described above. It
does not modify or build the sibling Halo2 and Orchard repositories.

Before committing a change, run the type checks and component tests, build the
production bundle, and run the browser tests:

```sh
npm run check
npm run build
npx playwright install chromium
npm run test:e2e
```

In CI, the Rocq job regenerates the raw structure and passes it to the website
job as a short-lived Actions artifact. The website job regenerates its derived
data and installs Chromium together with its system dependencies. Pull
requests and pushes to `main` run all validation without publishing, so a slow
Rocq job cannot block an independent Pages release.

To validate and publish the current committed revision from a developer
machine, run this command from a clean worktree:

```sh
./scripts/publish_orchard_pages.sh
```

The command regenerates the raw and derived circuit data, installs the pinned
frontend dependencies, runs the Python, TypeScript, component, and Playwright
checks, and builds the production bundle. It then creates a temporary,
parentless deployment commit containing `dist` under `orchard/`, root redirect
pages for the previous URLs, and `.nojekyll`, then force-pushes it with a lease
to `origin/gh-pages`. The source branch is never switched, and each release
leaves only one reachable deployment commit.

The publishing machine needs the Rocq/OCaml, Python, Node.js 22, npm, and
Playwright prerequisites described above, configured Git author information,
and push access to `origin`. In the GitHub repository settings, configure Pages
to **Deploy from a branch**, select `gh-pages`, and select `/(root)`. This is a
one-time setting; subsequent authenticated developer pushes publish the
prebuilt static files without waiting for the Rocq CI job.

To inspect the production bundle locally after `npm run build`, serve it from
the repository root:

```sh
python3 -m http.server 4173 --directory web/orchard-verification/dist
```

Then open `http://localhost:4173/` for the Journey,
`http://localhost:4173/proof-map.html` for the Atlas, or
`http://localhost:4173/circuit.html` for the Circuit Explorer, or
`http://localhost:4173/circuit-grid.html` for the Circuit Grid. Do not open the
HTML files directly with a `file:` URL; an HTTP server matches the way their
relative assets and circuit JSON are deployed.

## If Using VsRocq

Install the language server for the Rocq VS Code extension.
```sh
opam install vsrocq-language-server
```

Install `ocamlformat` as needed.
