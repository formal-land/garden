# Installation and Build Tutorial

This document provides an introduction to how to build the `garden` project for development. 

Before starting, make sure you have `Rust` and `opam` installed.

The Orchard verification visualization is a separate frontend and requires
[Node.js 22](https://nodejs.org/) and npm. It does not require the Rocq toolchain
unless you are also changing or checking the proofs.

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

The source for the Orchard Verification Journey and Atlas lives in
`web/orchard-verification`. Its production bundle is committed in
`docs/orchard-verification` so the experience can be served as static files
without Node.js or a runtime network connection.

Install the pinned dependencies and start the development server from the
repository root:

```sh
cd web/orchard-verification
npm ci
npm run dev
```

Open the URL printed by Vite for the Journey. Add `/proof-map.html` for the
Atlas.

Before committing a change, run the type checks and component tests, rebuild
the committed bundle, and run the browser tests:

```sh
npm run check
npm run build
npx playwright install chromium
npm run test:e2e
git diff --exit-code -- ../../docs/orchard-verification
```

The final command is expected to succeed after the regenerated bundle has been
staged or committed. In CI, Playwright installs Chromium together with its
system dependencies.

To inspect only the committed production files, serve them from the repository
root:

```sh
python3 -m http.server 4173 --directory docs/orchard-verification
```

Then open `http://localhost:4173/` for the Journey or
`http://localhost:4173/proof-map.html` for the Atlas. Do not open the HTML files
directly with a `file:` URL; an HTTP server matches the way their relative
assets are deployed.

## If Using VsRocq

Install the language server for the Rocq VS Code extension.
```sh
opam install vsrocq-language-server
```

Install `ocamlformat` as needed.
