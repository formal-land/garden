# Orchard verifying-key provenance

Garden derives every field of the deployed Post-NU6.3 Orchard
`vk.pinned()` description from its formal circuit, its explicit formal
configure-metadata trace, and the selected deployment parameters, then
compares the result with the deployed description. Equality of that metadata
trace with the Rust builder remains an external JSON translation-validation
check. The compiler, setup, and MSM computations do not consume the deployed
VK literals; those literals occur only as right-hand-side equality targets.
The public end-to-end result is the premise-free generated theorem

```coq
OrchardVkProvenance.orchard_vk_fully_derived :
  OrchardVkFullAbstract.certificate
```

Its two main VK-field claims are kept separate for review:

- `OrchardVkFullAbstract.non_commitment_certificate` is parameterized by an
  explicit commitment-coordinate view and covers setup/domain values, the
  configured and compiled constraint system, exact Debug-dump parity (T1),
  and the compact transcript representation (T2).
- `OrchardVkAbstract.certificate`, exposed separately by
  `orchard_vk_commit_lagrange_refined`, proves the 29 fixed-column and 15
  permutation-column commitment equations.

The aggregate additionally carries the fixed-grid replay, usable-row
equality, checked inverse-domain caches, permutation-label schedule, and the
coordinate bridge that instantiates T1 and T2 with the derived commitments.

The literals in `vk/data.v` and `compiled/pinned.v` are right-hand-side
equality targets. They are not fed into the compiler, setup computation, or
the full certificate's explicit printer input. Optimized domain and
commitment code does use efficient checked caches such as `PolyDomain.omega`;
the public certificate explicitly connects their inverse-root and inverse-size
witnesses to the setup-derived domain.

## Configure and compilation provenance

`Orchard/configure_metadata.v` gives an explicit typed formal trace of the
keygen-relevant builder operations and installs it in the same free configure
program that creates Garden's gates and lookups. The ordinary gate/lookup
interpreter ignores this metadata node;
`Orchard/compiled/configuration.v` interprets it with ordered deduplication
and derives:

- 14 fixed columns before compression, 10 advice columns, one instance
  column, and 56 selectors;
- selector kind for every selector: `QLookup`, `QRunning`,
  `QSinsemilla1_1`, and `QSinsemilla1_2` are complex, and the other 52 are
  simple;
- the first-registration order of all advice, fixed, and instance queries;
- the complete equality-enabled column order: instance 0, advice 0 through
  9, then fixed 3, 8, 9, and 10;
- lookup-table allocation to fixed columns 0, 1, and 2;
- the constants list `[3]`; and
- an unset minimum degree (`None`).

`Compile.compile_from_metadata` uses those values rather than fields copied
from `compiled/pinned.v`. Selector compression derives 15 combination
columns, hence 29 fixed columns after compression. The closed
`OrchardCompiledCertificate.certificate` checks the compression shape and
selector-assignment coverage, then compares the resulting 193 compiled gates,
exact ordered query tables, permutation columns, lookups, constants, counts,
and minimum degree with the deployed targets.

The gate AST printed by `vk/print.v` is the compiled AST itself. The precise
either-zero constraint constructor preserves Rust's left-associated product
tree for the two curve checks, so there is no printer-only rotation or
reassociation patch. T1 therefore checks the actual derived expression tree,
including query indices, against the deployed Debug dump byte for byte.

## Setup and domain provenance

The chosen Vesta curve and `Params::new(11)` exponent are deployment inputs.
From them, and from the compiled system's derived degree 9 with minimum degree
unset, `Orchard/vk/setup.v` and `setup_compiled.v` derive:

- `k = 11` and a 2,048-row domain;
- `extended_k = 14` as the first exponent whose domain holds
  `2^11 * (9 - 1)` coefficients;
- `omega` by the two repeated-squaring loops of Halo 2's
  `EvaluationDomain::new`, starting from the Pasta root of unity; and
- the printed base- and scalar-field modulus strings from the Vesta field
  definitions.

The cached domain and string literals are again equality witnesses. The
certificate checks both that exponent 14 fits and that its predecessor does
not. The full certificate also states that the FFT's cached `omega_inv` is an
inverse of this derived `omega`, that `n_inv` is the inverse of the derived
domain size, and that the permutation-label `delta` is obtained from the
Pasta generator/two-adicity schedule.

## Commitment provenance

For every one of the 44 columns, the executable model checks the Halo 2
key-generation equation

```text
commit_lagrange(Params::new(11), column_evaluations, Blind::default())
  = deployed verifying-key point
```

The commitment graph covers this chain:

1. `ModelColumns.v` replays Garden's synthesis events into the fixed plane and
   installs the selector-combination columns emitted by the metadata-driven
   compiler. `ModelColumnsCorrect.v` connects the primitive-array evaluator
   to `RawGrid`/`with_combinations` semantics.
2. `Sigma.v` checks the 15 permutation evaluation vectors against
   `OrchardCompiled.orchard_sigma`. Their complete column order comes from the
   formal configure trace, not from the deployed commitment list.
3. `Domain.v` checks bit reversal, inverse-root and power tables, `omega`,
   `delta`, and the inverse of 2048.
4. `FFT.v` evaluates the 2,048-point inverse FFT and checks each result against
   its generated scalar-vector witness.
5. `Srs.v` checks every base in the exact `Params::new(11)` hash-to-curve
   message schedule, including `w` and `u`, and connects accepted SSWU
   witnesses to `GroupHashVesta.group_hash`.
6. `Jacobian.v` evaluates a width-8 Pippenger MSM in low and high 128-bit
   halves. `AssemblyCheck.v` shifts the high half, recombines it, adds the
   mandatory default blind `[1]w`, and checks the deployed affine point.
7. `DomainRefinement.v`, `JacobianRefinement.v`, `MsmRefinement.v`, and
   `CommitmentRefinement.v` prove that these primitive computations denote
   the ordinary field, Vesta group, inverse-FFT, and
   `VkMsm.commit_lagrange` definitions.

Thus the deployed coordinate pairs are checked outputs of the mathematical
commitment computation, not unrelated affine witnesses.

The optimized replay keeps the computational leaves tractable without
changing that chain. The expensive post-hash SRS field equations, inversions,
point reconstruction, and curve-membership checks evaluate over five-limb
Montgomery words in 64-point shards, while the BLAKE2b-XMD hash-to-field stage
stays on `Z` bytes. A generic
square-root-independence theorem connects accepted SSWU witnesses to the
canonical group hash. FFT calibration leaves connect decoded primitive-array
outputs to ordinary scalar vectors, and the independently compiled low and
high Pippenger halves each expose an exact Jacobian representative before
assembly.

The emitter also records its independently recomputed affine result for each
MSM in the existing per-column data module. That independence is a generator
and oracle reproducibility property outside the kernel. Inside Rocq,
`VkCommitmentsCertificate` assembles the 44 emitted witnesses into a printer
coordinate view and checks that view against the deployed right-hand side;
the commitment refinement separately proves `commit_lagrange` equals that
same right-hand side. `OrchardVkFullAbstract.coordinate_certificate` combines
the two equalities and therefore connects every entry of the explicit view to
mathematical `commit_lagrange`.
Consequently the T1 and T2 fields of `orchard_vk_fully_derived` are stated for
the printer instantiated with the recomputed view; the pinned coordinate lists
are substitution targets, not hidden computational inputs to that printer.

## Representation, generation, and memory

Field elements use five little-endian radix-`2^63` limbs. Montgomery
arithmetic uses primitive `uint63` operations, while 2,048-element vectors
and 255 Pippenger buckets use linearly threaded primitive arrays. The proof
graph is sharded by inverse FFT, low/high MSM half, final assembly, 64-point
SRS range, sigma column, and domain table.

Generated `.v` sources are deterministic, ignored build artifacts. Ordinary
`make -C Garden` builds the hand-written refinement layer, the 129 generated
data modules, and the full kernel replay of 278 generated certificate modules
(229 computational leaves and 49 aggregate or packaging modules). The
explicit target below performs the same replay in phases with per-group
worker caps for memory-constrained builders:

```sh
make -C Garden orchard-vk-provenance
```

The last generated aggregate contains both
`orchard_vk_commit_lagrange_refined` and `orchard_vk_fully_derived`; a default
build kernel-checks both. PR CI runs the default build together with the
deterministic-source-generation check and the independent all-44-point
oracle.

The default job limits are deliberately conservative. SRS, inverse-FFT,
Pippenger, and assembly workers retain much more memory than their source
sizes suggest, and concurrent heavy workers have caused OOM kills. On a
measured memory-rich builder, cheap generated-data and packaging work can be
raised to 32 workers with

```sh
make -C Garden orchard-vk-provenance VK_PROVENANCE_JOBS=32
```

The heavy groups remain separately capped by
`VK_PROVENANCE_SRS_JOBS`, `VK_PROVENANCE_CALIBRATION_JOBS`,
`VK_PROVENANCE_MSM_JOBS`, and `VK_PROVENANCE_ASSEMBLY_JOBS`; raise them only
after measuring available memory.

Generation and the independent diagnostic can be run separately:

```sh
make -C Garden orchard-vk-provenance-generated-check
make -C Garden orchard-vk-provenance-oracle-check
make -C Garden orchard-vk-provenance-witnesses
```

The standard-library-only Python oracle independently reproduces the 44
points, but neither it nor the emitter is in the theorem's trusted path.
Rocq checks the emitted values as witnesses.

## Trust boundary

The closed computational leaves use `vm_cast_no_check`: the kernel checks
the cast's source and target types by VM conversion. The refinement layer has
no project-specific `Axiom` or `Admitted`; it relies on Rocq's standard
`PrimString`, `PrimInt63`, `PrimArray`, VM-conversion, and associated
primitive laws.

The theorem establishes provenance relative to four explicit modeling and
deployment choices: Garden's formal Orchard circuit, its formal configure
metadata trace, Vesta, and `k = 11`.
The deployed Debug dump and its 44 points are equality targets, while T1 and
T2 connect the printer instantiated with explicit emitted MSM-coordinate
witnesses to the target bytes and transcript value; the T2 statement prefixes
the actual computed compact-string length rather than a cached numeric length.
The public certificate also carries the fixed-column replay/compiled-grid
certificate and the equality between the synthesis usable-row bound and the
compiled domain's usable-row count.
The external JSON comparisons connect Garden's configure and synthesis
traces to the Rust implementation, including configure metadata, with
selector kinds reconstructed from the implementation's selector-compression
snapshot. That translation-validation step trusts extraction, the Rust
snapshot producers, and the Python comparator; it is outside Rocq's kernel.

This work does not prove cryptographic verifier soundness, polynomial-
commitment binding, Fiat–Shamir security, knowledge soundness, or
extractability. Nor does it independently justify the protocol's choice of
Vesta, `k = 11`, or this circuit: it proves what the selected formal inputs
compile to and that those results equal the deployed VK targets.
