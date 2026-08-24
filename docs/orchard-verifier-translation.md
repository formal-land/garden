# Orchard verifier transcription

Executable Rocq transcription of the deployed Orchard Halo 2 verifier:
`orchard::Proof::verify` calling `halo2_proofs::plonk::verify_proof` over
Vesta. The translation is handwritten, following the Rust module structure.
It is not the automatic THIR `rocq-of-rust` pipeline, and it does not prove
equivalence to the algebraic layer in `Halo2/plonkish/`.

The named L0 hypotheses in [`Halo2/plonkish/boundary.v`](../Garden/Halo2/plonkish/boundary.v)
(`IPABinding`, `MultiopenReduction`, `FiatShamirChallengeGood`) remain named
hypotheses. This transcription is the algorithm those hypotheses talk about.

## Primitive types

[`Garden/Rust/primitives.v`](../Garden/Rust/primitives.v) is the single local
copy of the rocq-of-rust data types used here, stripped of `Link`/`φ`/`Value`:

- `IntegerKind` / `Integer.t` and the `u8`/`u32`/`u64`/`usize` aliases
  (`RocqOfRust/M.v`, `RocqOfRust/links/M.v`)
- nested-pair `Array.t` (`RocqOfRust/core/links/array.v`)
- `Result.t` (`Ok`/`Err`)
- `Vec.t A := list A`
- `Lens.t` for `&mut` focuses (`get`/`set`/`compose`/`modify`)

`usize`/`isize` are 64-bit. Field elements stay as `Z` residues in
`Garden.Field.Field`. `&T` is `T`; `&mut T` is state-passing (`A → R * A`)
or a lens into a larger state. Rust `for` loops are recursive functions on
lists or a `nat` fuel.

## File map

Rust path under `third-party/halo2/halo2_proofs/src/` maps to
`Garden/Halo2/halo2_proofs/`. Matching `.rs` snapshots sit beside the `.v`
files (review only; not part of the Rocq build).

| Rocq | Rust |
|---|---|
| `Garden/Rust/primitives.v` | (rocq-of-rust primitives, one file) |
| `halo2_proofs/pasta.v` | pasta_curves `to_repr` / `from_repr` / `from_uniform_bytes`, Vesta compress |
| `halo2_proofs/transcript.v` | `transcript.rs` (`Blake2bRead`, `Challenge255`) |
| `halo2_proofs/arithmetic.v` | `arithmetic.rs` (`eval_polynomial`, `lagrange_interpolate`, `best_multiexp`) |
| `halo2_proofs/poly/domain.v` | `poly/domain.rs` (`rotate_omega`, `l_i_range`) |
| `halo2_proofs/poly/commitment.v` | `poly/commitment.rs`, `commitment/msm.rs` |
| `halo2_proofs/poly/commitment/verifier.v` | `poly/commitment/verifier.rs` (IPA) |
| `halo2_proofs/poly/multiopen.v` | `poly/multiopen.rs`, `multiopen/verifier.rs` |
| `halo2_proofs/plonk.v` | `plonk.rs`, `plonk/error.rs` (verify-time VK) |
| `halo2_proofs/plonk/verifier.v` | `plonk/verifier.rs` |
| `halo2_proofs/plonk/vanishing/verifier.v` | `plonk/vanishing/verifier.rs` |
| `halo2_proofs/plonk/permutation/verifier.v` | `plonk/permutation/verifier.rs` |
| `halo2_proofs/plonk/lookup/verifier.v` | `plonk/lookup/verifier.rs` |
| `Garden/Orchard/verifier.v` | `orchard/src/circuit.rs` (`Proof::verify`, instance encoding) |
| `Garden/Orchard/verifier/tests.v` | cheap `vm_compute` checks |

Specialization: `C = vesta::Affine`, `E = Challenge255`, `T = Blake2bRead`,
`V = SingleVerifier`. No `BatchVerifier`.

Submodule pins: `third-party/halo2` `cca1dd70c5ac76daa7d9773eb9a26e33ceea9a6a`,
`third-party/orchard` `05d899241b7a907d9c47dc5d3d7b3aa1361d785c`.

## What is reused

- BLAKE2b: `Garden.GroupHash.blake2b` (personalization `Halo2-Transcript` here;
  `Halo2-Verify-Key` stays in `Orchard/vk/transcript_repr.v`)
- Pasta moduli: the primes of `Garden.Field.Field.Primes`, implemented as
  `Z` reduction in `halo2_proofs/pasta.v` so the verifier tree does not
  pull fiat-crypto / Coqprime. The affine group law is \(y^2 = x^3 + 5\)
  over \(F_{pallas_q}\), the same curve as `EllipticCurve.Vesta`.
- VK binding scalar and compiled CS: `Orchard/vk/`, `Orchard/compiled/` (not
  rebuilt by this transcription; `verify_proof` takes a Rocq `VerifyingKey`)

## Tests

Default-suite checks (`Garden/Orchard/verifier/tests.v` and per-module
`*Tests` modules):

- wrapping integers, array replace, vec lens
- Pasta `to_repr`/`from_repr`/`from_uniform_bytes`
- transcript buffer underrun
- IPA `compute_b` / `compute_s`
- Orchard wrapper rejects `disableCrossAddress = 1` under a FixedPostNu6_2 key
- `verify_proof` rejects a wrong instance-column count

Orchard already ships serialized proofs that `Proof::verify` accepts
(`third-party/orchard/src/circuit_data/circuit_proof_test_case_*.bin`). Replaying
one through the full IPA+MSM at `k = 11` is the same cost class as VK
provenance and is not part of the ordinary `make` leaf.

## Out of scope

- Automatic `rocq-of-rust` THIR translation or vendoring `RocqOfRust/`
- Proving the transcription equivalent to `algebraic_accepts`
- Discharging `IPABinding` / `MultiopenReduction` / `FiatShamirChallengeGood`
- `BatchVerifier` / `create_proof`
- Re-translating the Action circuit
