# Installation and Build Tutorial

This document provides an introduction to how to build the `garden` project for development. 

Before starting, make sure you have `Rust` and `opam` installed.

## Setting Up Dependency Submodules

Fetch the necessary codes from submodule repositories:
```sh
git submodule update --init --recursive
```

## Install Opam Environment

In order to install dependencies and build the Coq part of the project, run the following commands for the proper `ocaml` environment.

Create a new opam switch:

```sh
opam switch create garden --packages=ocaml-variants.4.14.0+options,ocaml-option-flambda
```

Update shell environment to use the new switch:
```sh
eval $(opam env --switch=garden)
```

Add the repository with Coq packages:
```sh
opam repo add coq-released https://coq.inria.fr/opam/released
```

If you don't have a local Rust environment pre-installed:
```sh
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y
source "$HOME/.cargo/env"
```

Then we install the dependency files in the Coq program
```sh
opam install -y --deps-only Garden/coq-garden.opam
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
python scripts/coq_of_circom_ci.py
```


## Compile Coq Project

Finally, we compile the Coq project.
```sh
cd Garden
make
cd ..
```