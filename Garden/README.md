# Garden — Rocq Source

This directory contains the [Rocq](https://rocq-prover.org/) formal verification library for zero-knowledge circuits.

## Structure

| Directory / File | Description |
|---|---|
| `Brevis/` | Formalization of [Brevis](https://brevis.network/) circuits |
| `Circom/` | Formalization of [Circom](https://github.com/iden3/circom) circuits and Circomlib gadgets |
| `EllipticCurve/` | Elliptic-curve primitives over the Pallas curve |
| `Field/` | Finite-field arithmetic lemmas (Fermat, square roots, primality, …) |
| `GroupHash/` | Group-hash (Sinsemilla / Pedersen) formalization |
| `Halo2/` | Halo 2 proof-system model — relational circuit semantics, serialization / deserialization, plonkish compilation layer, and the operational-soundness bridge |
| `LLZK/` | Formalization of the [LLZK](https://github.com/Veridise/llzk-lib) language and example verified translations |
| `OpenVM/` | Formal verification of [OpenVM](https://github.com/openvm-org/openvm) chips (BranchEq, Sha256) |
| `Orchard/` | Full formal verification of the [Orchard](https://github.com/zcash/orchard) Action circuit: soundness, completeness, compilation correctness, balance, and operational proofs |
| `Plonky3/` | Formal verification of [Plonky3](https://github.com/Plonky3/Plonky3) AIR circuits (Keccak, Blake3) |
| `RecordUpdate.v` | Utility for record-field updates |

Each subdirectory typically contains:

- A monad or language model (`M.v`) defining the circuit semantics;
- Constraint / column definitions (`columns.v`, `air.v`, …);
- Snapshot files (`.snapshot`) generated from the real implementation to keep the formal model in sync;
- A `proofs/` subfolder with the main verification theorems.

## Build

From this directory run:

```sh
make
```

This generates `_CoqProject` and a `CoqMakefile`, then compiles all `.v` files.  See [`docs/BUILD.md`](../docs/BUILD.md) for full dependency installation and build instructions, and [`docs/compile-performance.md`](../docs/compile-performance.md) before touching heavy `vm_compute` certificates.
