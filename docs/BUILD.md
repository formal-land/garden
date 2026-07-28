# Installation and Build Tutorial

This document provides an introduction to how to build the `garden` project for development. 

Before starting, make sure you have `Rust` and `opam` installed.

The Orchard verification visualization is a separate frontend and requires
[Node.js 22](https://nodejs.org/) and npm. The website data is generated from
the Rocq structure and parity snapshots rather than committed.

## Setting Up Dependency Submodules

Fetch the necessary codes from submodule repositories:
```sh
git submodule update --init --recursive
```

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

## Orchard Verification Visualization

The source for the Orchard Verification Journey, Atlas, Circuit Explorer, and
Circuit Grid lives in `web/orchard-verification`. The production bundle is
generated in the ignored `web/orchard-verification/dist` directory. It is
validated in CI and published from the dedicated `gh-pages` branch. Generated
website files must not be committed to the source branch.

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
parentless deployment commit containing only `dist` plus `.nojekyll` and
force-pushes it with a lease to `origin/gh-pages`. The source branch is never
switched, and each release leaves only one reachable deployment commit.

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
