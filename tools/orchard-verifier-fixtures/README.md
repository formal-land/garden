# Orchard verifier differential fixtures

This crate drives the original pinned Orchard `Proof::verify` implementation
and produces the neutral 40-case corpus at
`Garden/Orchard/Verifier/Snapshots/post_nu6_3.json`. It builds the
Post-NU6.3 proving and verifying keys once, creates deterministic one- and
two-action proofs, and applies mutations at the verifier's 32-byte transcript
read boundaries.

The JSON records:

- the exact Orchard, Halo2, and rocq-of-rust commits;
- the x86_64 / 64-bit-`usize` execution target;
- raw proof bytes and ten canonical little-endian public scalars per action;
- the proof mutation for each case and the original Rust outcome; and
- an exact 44-ID inventory of manually authored semantic annotations covering
  valid shapes, public-input binding, flag variants, canonical decoders, every
  proof-reading transition, multiopen, and the final IPA MSM.

The producer checks that the superproject index and initialized, clean
submodule checkouts all match the recorded Orchard, Halo2, and rocq-of-rust
commits before generating data. It requires `x86_64-unknown-linux-gnu` with a
64-bit `usize`.

From the repository root, regenerate the original-Rust snapshot with:

```sh
git submodule update --init --recursive third-party/halo2 third-party/orchard
git submodule update --init third-party/rocq-of-rust
cargo run --locked --release \
  --manifest-path tools/orchard-verifier-fixtures/Cargo.toml -- \
  --output Garden/Orchard/Verifier/Snapshots/post_nu6_3.json
tools/generate_orchard_verifier_snapshots.py
```

The freshness checks run the original verifier again and compare every byte,
input, result, and branch annotation:

```sh
cargo run --locked --manifest-path tools/orchard-verifier-fixtures/Cargo.toml -- \
  --check --output Garden/Orchard/Verifier/Snapshots/post_nu6_3.json
cargo run --locked --release \
  --manifest-path tools/orchard-verifier-fixtures/Cargo.toml -- \
  --check --output Garden/Orchard/Verifier/Snapshots/post_nu6_3.json
tools/generate_orchard_verifier_snapshots.py --check
python3 tools/generate_orchard_verifier_runtime_data.py \
  third-party/orchard/src/circuit_data/circuit_description_post_nu6_3.json \
  Garden/Orchard/Verifier/PostNu6_3Data.v --check
```

Debug and release must produce identical snapshots. This detects accidental
dependence on Rust debug-overflow panics while the Rocq integer facade models
each checked, wrapping, or saturating operation explicitly.

The per-case `covers` labels are manually authored scenario and read-phase
annotations. They are not measurements of executed Rust branches, source
lines, or instructions, and the inventory does not claim 100% implementation
coverage. It also does not claim a panic fixture: malformed public-instance
representations are excluded by Orchard's typed `Instance` boundary, while
Garden has separate executable Rocq tests for its untyped byte and scalar input
boundary.

The fixture comparison is behavioral evidence for this pinned corpus. It is
not a proof that the Rocq verifier is equivalent to Rust and is not a proof of
the cryptographic soundness of Halo2.

From `Garden/`, `make orchard-verifier-replay-build` typechecks and compiles the
exact extracted Rocq replay. `make orchard-verifier-replay-extracted` executes
all 40 cases and exits nonzero on any mismatch; CI runs this all-case target.
The exact 44-ID inventory is shared across those cases and has the semantic,
manually authored scope described above.
