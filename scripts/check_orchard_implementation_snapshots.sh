#!/usr/bin/env bash

set -euo pipefail

GARDEN_REPOSITORY="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
ORCHARD_REPOSITORY="${GARDEN_REPOSITORY}/third-party/orchard"
ORCHARD_BUILD="${ORCHARD_REPOSITORY}/target"
ORCHARD_SNAPSHOTS="${GARDEN_REPOSITORY}/Garden/Orchard/Snapshots"

mkdir -p "${ORCHARD_BUILD}/tmp"

export CARGO_TARGET_DIR="${ORCHARD_BUILD}"
export TMPDIR="${ORCHARD_BUILD}/tmp"
export ORCHARD_CIRCUIT_JSON_DUMP="${ORCHARD_REPOSITORY}/src/circuit_data/action_circuit.highlevel.json"
export ORCHARD_CIRCUIT_CONFIGURE_JSON_DUMP="${ORCHARD_SNAPSHOTS}/circuit_configure_generated_from_implementation.json"
export ORCHARD_CIRCUIT_SYNTHESIS_JSON_DUMP="${ORCHARD_SNAPSHOTS}/circuit_synthesis_generated_from_implementation.json"
export ORCHARD_CIRCUIT_SYNTHESIS_LAYOUT_ROCQ_DUMP="${ORCHARD_BUILD}/circuit_synthesis_layout.generated.v"
export ORCHARD_CIRCUIT_SELECTOR_COMPRESSION_JSON_DUMP="${ORCHARD_SNAPSHOTS}/circuit_selector_compression_generated_from_implementation.json"

cd "${ORCHARD_REPOSITORY}"

cargo test generate_action_circuit_highlevel_json -- --ignored --nocapture
cargo test generate_action_circuit_configure_json -- --ignored --nocapture
cargo test generate_action_circuit_synthesis_json -- --ignored --nocapture
cargo test generate_action_circuit_selector_compression_json -- --ignored --nocapture
cargo test round_trip_post_nu6_3 -- --nocapture

cd "${GARDEN_REPOSITORY}"

if test -n "$(git -C "${ORCHARD_REPOSITORY}" status --porcelain -- \
  src/circuit_data/action_circuit.highlevel.json)"; then
  git -C "${ORCHARD_REPOSITORY}" diff -- \
    src/circuit_data/action_circuit.highlevel.json
  echo "Orchard high-level circuit snapshot is stale." >&2
  exit 1
fi

if test -n "$(git status --porcelain -- \
  Garden/Orchard/Snapshots/circuit_configure_generated_from_implementation.json \
  Garden/Orchard/Snapshots/circuit_synthesis_generated_from_implementation.json \
  Garden/Orchard/Snapshots/circuit_selector_compression_generated_from_implementation.json)"; then
  git diff -- \
    Garden/Orchard/Snapshots/circuit_configure_generated_from_implementation.json \
    Garden/Orchard/Snapshots/circuit_synthesis_generated_from_implementation.json \
    Garden/Orchard/Snapshots/circuit_selector_compression_generated_from_implementation.json
  echo "Garden's Orchard implementation snapshots are stale." >&2
  exit 1
fi

python3 scripts/generate_vk_pinned.py --check
