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
| `halo2_proofs/from_compiled.v` | (Garden: `CompiledSystem.t` → query-indexed CS / VK) |
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
  rebuilt by this transcription; `verify_proof` takes a Rocq `VerifyingKey`).
  `halo2_proofs/from_compiled.v` fills that VK's constraint-system fields
  from a `CompiledSystem.t`; commitments, domain, and the transcript
  binding scalar remain parameters.

## Tests

Default-suite checks (`Garden/Orchard/verifier/tests.v` and per-module
`*Tests` modules):

- wrapping integers, array replace, vec lens
- Pasta `to_repr`/`from_repr`/`from_uniform_bytes`
- transcript buffer underrun
- IPA `compute_b` / `compute_s`
- Orchard wrapper rejects `disableCrossAddress = 1` under a FixedPostNu6_2 key
- `verify_proof` rejects a wrong instance-column count
- `from_compiled`: `query_index` first-match and missing; `reindex` evaluation
  of a two-leaf sum against `cell_evals`

Orchard already ships serialized proofs that `Proof::verify` accepts
(`third-party/orchard/src/circuit_data/circuit_proof_test_case_*.bin`). Replaying
one through the full IPA+MSM at `k = 11` is the same cost class as VK
provenance and is not part of the ordinary `make` leaf.

## Compiled-system glue

[`Garden/Halo2/halo2_proofs/from_compiled.v`](../Garden/Halo2/halo2_proofs/from_compiled.v)
rebuilds the transcribed verifier's `ConstraintSystem` from an L2
`CompiledSystem.t` (`Halo2/plonkish/main.v`):

- `query_index` is the first-match position of `(column, rotation offset)`
  in a query table, the same resolution [`Orchard/vk/print.v`](../Garden/Orchard/vk/print.v)
  uses as `index_of_go`.
- `reindex` replaces each `Advice` / `Fixed` / `Instance_` leaf by that
  query index. Selector leaves (absent from a compressed system) become
  `Constant 0`.
- `constraint_system_of` fills instance/advice counts, the three query
  tables, singleton gate-polynomial lists (the flattening
  `gate_expressions` in `plonk/verifier.rs` performs), lookup input/table
  expressions (table side: current-rotation fixed query of
  `lookup_as_fixed`), permutation columns, `blinding_factors`, and
  `degree`.
- `vk_of_orchard` installs that CS and `cs_degree`, and takes the
  evaluation domain, fixed commitments, permutation commitments, and
  transcript binding scalar as parameters.

`reindex_preserves_eval` is the row-evaluation agreement: on a
selector-free expression whose leaves sit in the query tables, the
verifier's `Expression.evaluate` against the three `cell_evals` lists
(each query `(col, rot)` read at `row + rot` and reduced into
`F_{pallas_p}`) equals `eval_at_row`. That row evaluator is the residue
arithmetic of `eval_expression` in [`Halo2/proof.v`](../Garden/Halo2/proof.v)
at `p = pallas_p` (`UnOp.from` = `Fp.from`, `BinOp.add` = `Fp.add`, and
the matching `mul` / `opp`). The file depends only on the verifier Pasta
stack, not on `Field.Field`.

Lookup table columns are Garden `Lookup` indices. Halo 2 stores them as
`TableColumn` (a fixed column); `lookup_as_fixed` is that map. For Orchard
it is the identity, certified by
`OrchardConfigure.lookup_fixed_columns_eq` in
[`compiled/configuration.v`](../Garden/Orchard/compiled/configuration.v).

## Out of scope

- Automatic `rocq-of-rust` THIR translation or vendoring `RocqOfRust/`
- Proving `verify_proof = Ok` implies `algebraic_accepts` /
  `algebraic_accepts_at`
- Discharging `IPABinding` / `MultiopenReduction` / `FiatShamirChallengeGood`
- `BatchVerifier` / `create_proof`
- Re-translating the Action circuit
