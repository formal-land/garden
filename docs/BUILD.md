# Installation and Build Tutorial

This document provides an introduction to how to build the `garden` project for development. 

Before starting, make sure you have `Rust` and `opam` installed.

The Orchard verification visualization is a separate frontend and requires
[Node.js 22](https://nodejs.org/) and npm. Its checked-in Rocq structure and
parity snapshots let the website data regenerate without the Rocq toolchain.

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
uploaded directly to GitHub Pages by CI and must not be committed.

Install the pinned dependencies and start the development server from the
repository root:

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

Changes limited to source mapping, the functional-flow manifest, or the
frontend do not require Rocq; `npm run generate:data` is sufficient.

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

In CI, Playwright installs Chromium together with its system dependencies.
Pull requests regenerate the website data and run all validation without
publishing. A successful build on `main` uploads `dist` as a GitHub Pages
artifact and deploys it.

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
