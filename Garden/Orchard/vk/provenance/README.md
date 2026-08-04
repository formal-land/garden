# Orchard verifying-key commitment provenance

This directory derives the 29 fixed-column and 15 permutation-column
commitments printed in the deployed Post-NU6.3 Orchard verifying key. The
executable model mirrors the Halo 2 keygen equation

```text
commit_lagrange(Params::new(11), column_evaluations, Blind::default())
  = pinned verifying-key point
```

for every one of the 44 columns. Generated literals are witnesses, not
assumptions: small Rocq leaves recompute and check each stage before
`generated/certificates/Main.v` bundles the results.  Its closed
`orchard_vk_commit_lagrange_refined` theorem has type
`OrchardVkAbstract.certificate`: all 44 deployed points are equal to the
library-level group/polynomial `commit_lagrange` specification, and the
`Params::new(11)` premise of that specification is discharged.

## What is checked

The certificate graph covers the following chain.

1. `ModelColumns.v` replays Garden's own synthesis events into a flat
   primitive-array fixed plane and installs the selector-combination columns
   emitted by `Compile.compile`. `ModelColumnsCorrect.v` connects that fast
   evaluator to the ordinary `RawGrid`/`with_combinations` semantics.
2. `Sigma.v` checks each packed generated permutation column against
   `OrchardCompiled.orchard_sigma` and evaluates its
   `delta^column * omega^row` labels. This part inherits the existing pinned
   `permutation_columns` list and ordering; it derives the commitments
   conditional on that configuration, rather than independently deriving
   the full list from copied cells.
3. `Domain.v` checks the bit-reversal table, inverse-root recurrence,
   `omega` and `delta` power tables, and the inverse of 2048 against the
   domain constants already used by the compiled-system proof.
4. `FFT.v` performs the 2048-point inverse FFT.  A calibration leaf proves
   that its decoded output is exactly the generated standard scalar vector.
5. `Srs.v` enforces the exact `Params::new(11)` message schedule, canonical
   Montgomery coordinates, and the hash-to-field and SSWU witness equations
   for every base, including `w` and `u`, in 64-point shards. A generic
   square-root-independence theorem connects every accepted witness to the
   canonical `GroupHashVesta.group_hash` definition.
6. `Jacobian.v` performs a width-8 Pippenger MSM.  The low and high 128-bit
   halves compile independently and each proves an ordinary Rocq equality to
   an exact generated Jacobian representative.  `AssemblyCheck.v` shifts the
   high half by 128 bits, adds the default blinding generator `w`, and checks
   the deployed affine point.
7. `DomainRefinement.v`, `JacobianRefinement.v`, and `MsmRefinement.v` prove
   the semantic refinement of those optimized primitive operations.  The
   inverse FFT is identified with `VkMsm.intt`; every window, bucket update,
   doubling, addition, and split-MSM recombination is transported to the
   abstract Vesta group; and `VkMsm.commit_lagrange_intt` connects that MSM
   with the mathematical group inverse FFT used by Halo 2.

`Checks.commitment_certificate_sound` rewrites the two exact half-MSM
equalities into the assembly check. `CommitmentRefinement.v` then composes
the calibration, SRS, primitive-arithmetic, and pinned-coordinate refinements.
Thus the aggregate establishes the actual executable committed point and its
equality to the abstract `commit_lagrange`, rather than merely checking two
unrelated affine witnesses.

## Representation and parallelism

Field elements use five little-endian radix-`2^63` words.  Montgomery
addition and multiplication use Rocq's primitive `uint63` instructions;
2048-element vectors and 255 Pippenger buckets use primitive arrays whose
latest version is threaded linearly through every loop.

The proof graph deliberately has separate leaves for:

- each inverse FFT;
- each low and high MSM half;
- each final assembly;
- each 64-point SRS shard;
- each sigma column; and
- each domain table.

The default is conservative because several Rocq workers can consume much
more memory than their source size suggests:

```sh
make -C Garden orchard-vk-provenance
```

A memory-rich 32-core builder can expose 32-way parallelism for generated
data and cheap record-packaging leaves with:

```sh
make -C Garden orchard-vk-provenance VK_PROVENANCE_JOBS=32
```

The memory-heavy phases remain independently capped. Builders that have
measured sufficient headroom can raise, for example,
`VK_PROVENANCE_SRS_JOBS`, `VK_PROVENANCE_CALIBRATION_JOBS`, or
`VK_PROVENANCE_MSM_JOBS`; after observed OOMs their defaults are one worker.

The sigma mapping is split into 15 primitive-word shards.  A previous
monolithic representation as 30,720 pairs of `nat` exhausted memory during
elaboration; packing `(column,row)` as `column * 2048 + row` avoids that
Peano-term blow-up.

To run the independent Python diagnostic or regenerate every untrusted
witness:

```sh
make -C Garden orchard-vk-provenance-oracle-check
make -C Garden orchard-vk-provenance-witnesses
```

The Python implementation uses only the standard library and independently
reproduces all 44 pinned points, but it is not in the trusted proof path.

## Proof and trust boundary

The closed certificates use `vm_compute`; this Rocq installation was built
without the native compiler, so `native_compute` falls back to the same VM.
The executable arithmetic contains no project-specific `Axiom` or
`Admitted`. Its logical refinement layer proves the primitive multiply/add
carry equations, the five-word CIOS sweep, and modular correctness of
five-limb Montgomery multiplication for a canonical operand. The certificates
ultimately rely on Rocq's standard `PrimInt63` and `PrimArray` primitives.

The refinement chain is complete up to the library-level mathematical
`commit_lagrange`: it proves field canonicality, inverse-FFT semantics,
Jacobian group-law semantics, Pippenger semantics, the mandatory default
blind `[1]w`, and equality with every pinned coordinate. Generated `.v`
sources are ignored build artifacts and can be reproduced exactly by the
emitter; their small closed facts are checked by Rocq's kernel when built.

This theorem does not prove cryptographic verifier soundness, knowledge
soundness, or extractability. It also intentionally treats Garden's compiled
Orchard column configuration and pinned VK coordinate list as the objects
whose compilation provenance is being established; those protocol-level
choices are not independently re-specified here.
