.DEFAULT_GOAL := default

.PHONY: all clean clean-util distclean default
.PHONY: orchard-json-from-model orchard-configure-json-from-model orchard-configure-json-compare
.PHONY: orchard-synthesis-json-from-model orchard-synthesis-json-compare orchard-synthesis-json-compare-normalized
.PHONY: orchard-structure-json-from-model orchard-circuit-visualization-json orchard-circuit-visualization-check
.PHONY: orchard-circuit-grid-json orchard-circuit-grid-check orchard-circuit-grid-test
.PHONY: orchard-vk-pinned orchard-vk-pinned-check
.PHONY: orchard-verifier-snapshots orchard-verifier-snapshots-check
.PHONY: orchard-verifier-snapshots-debug-check orchard-verifier-snapshots-generated
.PHONY: orchard-verifier-snapshots-generated-check
.PHONY: orchard-verifier-runtime-data orchard-verifier-runtime-data-check
.PHONY: orchard-verifier-tests orchard-verifier-replay-build orchard-verifier-ocaml-runtime-check
.PHONY: orchard-verifier-replay-case0 orchard-verifier-replay-extracted

# The VK provenance graph is large and branch-specific, so its inventories,
# generator rules, job controls, and explicit build targets live separately.
include vk-provenance.mk

# Excluding the generated subtree here prevents parse-time discovery from
# depending on whether a developer happens to have generated it already.
VFILES := $(shell find -L . -path './$(VK_PROVENANCE_GENERATED_DIR)' -prune -o -name "*.v" -print | grep -v -f blacklist.txt | sort)

# Garden uses the computational integer core from rocq-of-rust.  Listing the
# exact MIT-licensed source closure here keeps the Rust translator, link plugin,
# generated translations, and nested upstream submodules outside the build.
ROCQ_OF_RUST_ROOT := ../third-party/rocq-of-rust/RocqOfRust
ROCQ_OF_RUST_VFILES := \
	$(ROCQ_OF_RUST_ROOT)/M.v \
	$(ROCQ_OF_RUST_ROOT)/RecordUpdate.v \
	$(ROCQ_OF_RUST_ROOT)/lib/lib.v \
	$(ROCQ_OF_RUST_ROOT)/RocqOfRust.v \
	$(ROCQ_OF_RUST_ROOT)/links/M.v
PROJECT_VFILES := $(VFILES) $(ROCQ_OF_RUST_VFILES)

# The ordinary project build covers every source the generated makefile
# knows: hand-written Rocq sources, generated literal-data modules, and the
# 278 generated provenance certificate modules.  `make orchard-vk-provenance`
# remains available as a phased replay with per-group worker caps for
# memory-constrained builders.

default: all

CoqMakefile: $(PROJECT_VFILES) blacklist.txt $(VK_PROVENANCE_STATE) $(VK_PROVENANCE_MANIFEST) $(VK_PROVENANCE_GENERATED_VFILES)
	echo "-R . Garden" > _CoqProject
	echo "-R $(ROCQ_OF_RUST_ROOT) RocqOfRust" >> _CoqProject
	echo "-docroot Garden" >> _CoqProject
	echo "-arg -impredicative-set -arg -w -arg -stdlib-vector" >> _CoqProject
	# The checked-in sources and generated manifest are deliberately separate.
	find -L . -path './$(VK_PROVENANCE_GENERATED_DIR)' -prune -o -name "*.v" -print | grep -v -f blacklist.txt | sort >> _CoqProject
	for source in $(ROCQ_OF_RUST_VFILES); do echo "$$source"; done >> _CoqProject
	cat $(VK_PROVENANCE_MANIFEST) >> _CoqProject
	rocq makefile -f _CoqProject -o $@

MAKECOQ := +$(MAKE) -f CoqMakefile

%.vo: CoqMakefile %.v
	$(MAKECOQ) $@

all: CoqMakefile
	$(MAKECOQ) all

ORCHARD_SYNTHESIS_JSON_BUILD := _build/orchard_synthesis_json
ORCHARD_SNAPSHOTS := Orchard/Snapshots
ORCHARD_CONFIGURE_MODEL_JSON := $(ORCHARD_SNAPSHOTS)/circuit_configure_generated_from_model.json
ORCHARD_CONFIGURE_IMPL_JSON := $(ORCHARD_SNAPSHOTS)/circuit_configure_generated_from_implementation.json
ORCHARD_CONFIGURE_HIGHLEVEL_IMPL_JSON := ../third-party/orchard/src/circuit_data/action_circuit.highlevel.json
ORCHARD_SELECTOR_COMPRESSION_IMPL_JSON := $(ORCHARD_SNAPSHOTS)/circuit_selector_compression_generated_from_implementation.json
ORCHARD_SYNTHESIS_MODEL_JSON := $(ORCHARD_SNAPSHOTS)/circuit_synthesis_generated_from_model.json
ORCHARD_SYNTHESIS_IMPL_JSON := $(ORCHARD_SNAPSHOTS)/circuit_synthesis_generated_from_implementation.json
ORCHARD_STRUCTURE_MODEL_JSON := $(ORCHARD_SNAPSHOTS)/circuit_structure_generated_from_model.json
ORCHARD_CIRCUIT_VISUALIZATION_JSON := ../web/orchard-verification/public/data/orchard-circuit-highlevel.v1.json
ORCHARD_CIRCUIT_VISUALIZATION_GENERATOR := ../scripts/generate_orchard_circuit_explorer.py
ORCHARD_CIRCUIT_GRID_JSON := ../web/orchard-verification/public/data/orchard-circuit-grid.v1.json
ORCHARD_CIRCUIT_GRID_GENERATOR := ../scripts/generate_orchard_circuit_grid.py
ORCHARD_SYNTHESIS_EXTRACT := Orchard/circuit_synthesis_json_extract.v
ORCHARD_SYNTHESIS_EXTRACTED_ML := $(ORCHARD_SYNTHESIS_JSON_BUILD)/orchard_synthesis_model.ml
ORCHARD_SYNTHESIS_EXTRACTED_MLI := $(ORCHARD_SYNTHESIS_JSON_BUILD)/orchard_synthesis_model.mli
ORCHARD_SYNTHESIS_MODEL_CMO := $(ORCHARD_SYNTHESIS_JSON_BUILD)/orchard_synthesis_model.cmo
ORCHARD_SYNTHESIS_DRIVER_CMO := $(ORCHARD_SYNTHESIS_JSON_BUILD)/orchard_synthesis_json_driver.cmo
ORCHARD_SYNTHESIS_EXE := $(ORCHARD_SYNTHESIS_JSON_BUILD)/orchard_synthesis_json

$(ORCHARD_SYNTHESIS_EXTRACTED_ML): $(VFILES) $(ORCHARD_SYNTHESIS_EXTRACT) CoqMakefile
	mkdir -p $(ORCHARD_SYNTHESIS_JSON_BUILD)
	rocq compile -impredicative-set -R . Garden $(ORCHARD_SYNTHESIS_EXTRACT)

$(ORCHARD_SYNTHESIS_MODEL_CMO): $(ORCHARD_SYNTHESIS_EXTRACTED_ML) $(ORCHARD_SYNTHESIS_EXTRACTED_MLI)
	ocamlfind ocamlc -package rocq-runtime.kernel,zarith \
	  -I $(ORCHARD_SYNTHESIS_JSON_BUILD) \
	  -c $(ORCHARD_SYNTHESIS_EXTRACTED_MLI)
	ocamlfind ocamlc -package rocq-runtime.kernel,zarith \
	  -I $(ORCHARD_SYNTHESIS_JSON_BUILD) \
	  -c $(ORCHARD_SYNTHESIS_EXTRACTED_ML)

$(ORCHARD_SYNTHESIS_DRIVER_CMO): $(ORCHARD_SYNTHESIS_MODEL_CMO) ../scripts/orchard_synthesis_json.ml
	ocamlfind ocamlc -package rocq-runtime.kernel,zarith \
	  -I $(ORCHARD_SYNTHESIS_JSON_BUILD) \
	  -c -o $@ ../scripts/orchard_synthesis_json.ml

$(ORCHARD_SYNTHESIS_EXE): $(ORCHARD_SYNTHESIS_MODEL_CMO) $(ORCHARD_SYNTHESIS_DRIVER_CMO)
	ocamlfind ocamlc -package rocq-runtime.kernel,zarith -linkpkg \
	  -I $(ORCHARD_SYNTHESIS_JSON_BUILD) \
	  $(ORCHARD_SYNTHESIS_MODEL_CMO) \
	  $(ORCHARD_SYNTHESIS_DRIVER_CMO) \
	  -o $@

orchard-json-from-model: $(ORCHARD_SYNTHESIS_EXE)
	mkdir -p $(ORCHARD_SNAPSHOTS)
	$(ORCHARD_SYNTHESIS_EXE) $(ORCHARD_CONFIGURE_MODEL_JSON) $(ORCHARD_SYNTHESIS_MODEL_JSON)

orchard-configure-json-from-model: orchard-json-from-model

orchard-synthesis-json-from-model: orchard-json-from-model

orchard-structure-json-from-model: $(ORCHARD_SYNTHESIS_EXE)
	mkdir -p $(ORCHARD_SNAPSHOTS)
	$(ORCHARD_SYNTHESIS_EXE) --structure $(ORCHARD_STRUCTURE_MODEL_JSON)

orchard-circuit-visualization-json: orchard-structure-json-from-model
	python3 $(ORCHARD_CIRCUIT_VISUALIZATION_GENERATOR) \
	  --input $(ORCHARD_STRUCTURE_MODEL_JSON) \
	  --output $(ORCHARD_CIRCUIT_VISUALIZATION_JSON)

orchard-circuit-visualization-check: orchard-structure-json-from-model
	python3 $(ORCHARD_CIRCUIT_VISUALIZATION_GENERATOR) \
	  --input $(ORCHARD_STRUCTURE_MODEL_JSON) \
	  --output $(ORCHARD_CIRCUIT_VISUALIZATION_JSON) \
	  --check

orchard-configure-json-compare: orchard-configure-json-from-model
	python3 ../scripts/compare_orchard_configure_json.py \
	  $(ORCHARD_CONFIGURE_MODEL_JSON) \
	  $(ORCHARD_CONFIGURE_IMPL_JSON) \
	  --implementation-highlevel $(ORCHARD_CONFIGURE_HIGHLEVEL_IMPL_JSON) \
	  --selector-compression $(ORCHARD_SELECTOR_COMPRESSION_IMPL_JSON)

orchard-synthesis-json-compare: orchard-synthesis-json-from-model
	python3 ../scripts/compare_orchard_synthesis_json.py \
	  $(ORCHARD_SYNTHESIS_MODEL_JSON) \
	  $(ORCHARD_SYNTHESIS_IMPL_JSON)

orchard-synthesis-json-compare-normalized: orchard-synthesis-json-from-model
	python3 ../scripts/compare_orchard_synthesis_json.py \
	  --normalize-rows \
	  $(ORCHARD_SYNTHESIS_MODEL_JSON) \
	  $(ORCHARD_SYNTHESIS_IMPL_JSON)

orchard-circuit-grid-json: orchard-configure-json-compare orchard-synthesis-json-compare orchard-circuit-visualization-json
	python3 $(ORCHARD_CIRCUIT_GRID_GENERATOR) \
	  --configure-model $(ORCHARD_CONFIGURE_MODEL_JSON) \
	  --configure-implementation $(ORCHARD_CONFIGURE_IMPL_JSON) \
	  --synthesis-model $(ORCHARD_SYNTHESIS_MODEL_JSON) \
	  --synthesis-implementation $(ORCHARD_SYNTHESIS_IMPL_JSON) \
	  --explorer $(ORCHARD_CIRCUIT_VISUALIZATION_JSON) \
	  --output $(ORCHARD_CIRCUIT_GRID_JSON)

orchard-circuit-grid-check: orchard-configure-json-compare orchard-synthesis-json-compare orchard-circuit-visualization-json
	python3 $(ORCHARD_CIRCUIT_GRID_GENERATOR) \
	  --configure-model $(ORCHARD_CONFIGURE_MODEL_JSON) \
	  --configure-implementation $(ORCHARD_CONFIGURE_IMPL_JSON) \
	  --synthesis-model $(ORCHARD_SYNTHESIS_MODEL_JSON) \
	  --synthesis-implementation $(ORCHARD_SYNTHESIS_IMPL_JSON) \
	  --explorer $(ORCHARD_CIRCUIT_VISUALIZATION_JSON) \
	  --output $(ORCHARD_CIRCUIT_GRID_JSON) \
	  --check

orchard-circuit-grid-test:
	python3 ../scripts/tests/test_generate_orchard_circuit_grid.py

orchard-vk-pinned:
	python3 ../scripts/generate_vk_pinned.py

orchard-vk-pinned-check:
	python3 ../scripts/generate_vk_pinned.py --check

ORCHARD_VERIFIER_SNAPSHOTS := Orchard/Verifier/Snapshots
ORCHARD_VERIFIER_JSON := $(ORCHARD_VERIFIER_SNAPSHOTS)/post_nu6_3.json
ORCHARD_VERIFIER_GENERATED := $(ORCHARD_VERIFIER_SNAPSHOTS)/Generated.v
ORCHARD_VERIFIER_GENERATOR := ../tools/generate_orchard_verifier_snapshots.py
ORCHARD_VERIFIER_RUST_MANIFEST := ../tools/orchard-verifier-fixtures/Cargo.toml
ORCHARD_VERIFIER_RUNTIME_SOURCE := ../third-party/orchard/src/circuit_data/circuit_description_post_nu6_3.json
ORCHARD_VERIFIER_RUNTIME_DATA := Orchard/Verifier/PostNu6_3Data.v
ORCHARD_VERIFIER_RUNTIME_GENERATOR := ../tools/generate_orchard_verifier_runtime_data.py
ORCHARD_VERIFIER_REPLAY_BUILD := _build/orchard_verifier_replay
ORCHARD_VERIFIER_REPLAY_EXTRACT := Orchard/Verifier/Snapshots/Extract.v
ORCHARD_VERIFIER_REPLAY_ML := $(ORCHARD_VERIFIER_REPLAY_BUILD)/orchard_verifier_replay.ml
ORCHARD_VERIFIER_REPLAY_MLI := $(ORCHARD_VERIFIER_REPLAY_BUILD)/orchard_verifier_replay.mli
ORCHARD_VERIFIER_REPLAY_CMX := $(ORCHARD_VERIFIER_REPLAY_BUILD)/orchard_verifier_replay.cmx
ORCHARD_VERIFIER_REPLAY_DRIVER_CMX := $(ORCHARD_VERIFIER_REPLAY_BUILD)/orchard_verifier_replay_driver.cmx
ORCHARD_VERIFIER_REPLAY_EXE := $(ORCHARD_VERIFIER_REPLAY_BUILD)/orchard_verifier_replay

orchard-verifier-snapshots:
	cargo run --locked --release --manifest-path $(ORCHARD_VERIFIER_RUST_MANIFEST) -- \
	  --output $(ORCHARD_VERIFIER_JSON)
	python3 $(ORCHARD_VERIFIER_GENERATOR) \
	  $(ORCHARD_VERIFIER_JSON) $(ORCHARD_VERIFIER_GENERATED)

orchard-verifier-snapshots-generated:
	python3 $(ORCHARD_VERIFIER_GENERATOR) \
	  $(ORCHARD_VERIFIER_JSON) $(ORCHARD_VERIFIER_GENERATED)

orchard-verifier-snapshots-generated-check:
	python3 $(ORCHARD_VERIFIER_GENERATOR) \
	  $(ORCHARD_VERIFIER_JSON) $(ORCHARD_VERIFIER_GENERATED) --check

orchard-verifier-snapshots-check:
	cargo run --locked --release --manifest-path $(ORCHARD_VERIFIER_RUST_MANIFEST) -- \
	  --check --output $(ORCHARD_VERIFIER_JSON)
	python3 $(ORCHARD_VERIFIER_GENERATOR) \
	  $(ORCHARD_VERIFIER_JSON) $(ORCHARD_VERIFIER_GENERATED) --check

orchard-verifier-snapshots-debug-check:
	cargo run --locked --manifest-path $(ORCHARD_VERIFIER_RUST_MANIFEST) -- \
	  --check --output $(ORCHARD_VERIFIER_JSON)

orchard-verifier-runtime-data:
	python3 $(ORCHARD_VERIFIER_RUNTIME_GENERATOR) \
	  $(ORCHARD_VERIFIER_RUNTIME_SOURCE) $(ORCHARD_VERIFIER_RUNTIME_DATA)

orchard-verifier-runtime-data-check:
	python3 $(ORCHARD_VERIFIER_RUNTIME_GENERATOR) \
	  $(ORCHARD_VERIFIER_RUNTIME_SOURCE) $(ORCHARD_VERIFIER_RUNTIME_DATA) --check

orchard-verifier-tests: \
	Halo2/Verifier/Tests.vo \
	Halo2/Verifier/CoreTests.vo \
	Halo2/Verifier/Eval/CommitmentTests.vo \
	Orchard/Verifier/Tests.vo \
	Orchard/Verifier/PostNu6_3Materialization.vo \
	Orchard/Verifier/Snapshots/Generated.vo \
	Orchard/Verifier/Snapshots/Replay.vo \
	Orchard/Verifier/Assurance.vo \
	Orchard/Verifier/InstanceCommitmentAssurance.vo \
	orchard-verifier-snapshots-generated-check \
	orchard-verifier-runtime-data-check \
	orchard-verifier-replay-extracted

$(ORCHARD_VERIFIER_REPLAY_ML) $(ORCHARD_VERIFIER_REPLAY_MLI) &: \
	$(ORCHARD_VERIFIER_REPLAY_EXTRACT) \
	Orchard/Verifier/Snapshots/Replay.vo CoqMakefile \
	| orchard-verifier-ocaml-runtime-check
	mkdir -p $(ORCHARD_VERIFIER_REPLAY_BUILD)
	rocq compile -impredicative-set \
	  -R . Garden -R $(ROCQ_OF_RUST_ROOT) RocqOfRust \
	  $(ORCHARD_VERIFIER_REPLAY_EXTRACT)
	test -s $(ORCHARD_VERIFIER_REPLAY_ML)
	test -s $(ORCHARD_VERIFIER_REPLAY_MLI)

$(ORCHARD_VERIFIER_REPLAY_CMX): $(ORCHARD_VERIFIER_REPLAY_ML) \
	$(ORCHARD_VERIFIER_REPLAY_MLI)
	ocamlfind ocamlopt -package rocq-runtime.kernel,zarith \
	  -I $(ORCHARD_VERIFIER_REPLAY_BUILD) \
	  -c $(ORCHARD_VERIFIER_REPLAY_MLI)
	ocamlfind ocamlopt -package rocq-runtime.kernel,zarith \
	  -I $(ORCHARD_VERIFIER_REPLAY_BUILD) \
	  -c $(ORCHARD_VERIFIER_REPLAY_ML)

$(ORCHARD_VERIFIER_REPLAY_DRIVER_CMX): $(ORCHARD_VERIFIER_REPLAY_CMX) \
	../scripts/orchard_verifier_replay.ml
	ocamlfind ocamlopt -package rocq-runtime.kernel,zarith,unix \
	  -I $(ORCHARD_VERIFIER_REPLAY_BUILD) \
	  -c -o $@ ../scripts/orchard_verifier_replay.ml

$(ORCHARD_VERIFIER_REPLAY_EXE): $(ORCHARD_VERIFIER_REPLAY_CMX) \
	$(ORCHARD_VERIFIER_REPLAY_DRIVER_CMX)
	ocamlfind ocamlopt -package rocq-runtime.kernel,zarith,unix -linkpkg \
	  -I $(ORCHARD_VERIFIER_REPLAY_BUILD) \
	  $(ORCHARD_VERIFIER_REPLAY_CMX) \
	  $(ORCHARD_VERIFIER_REPLAY_DRIVER_CMX) \
	  -o $@

orchard-verifier-ocaml-runtime-check:
	@test "$$(ocamlopt -config-var word_size)" = 64 || { \
	  echo "Orchard verifier replay requires a 64-bit OCaml runtime" >&2; \
	  exit 1; \
	}

orchard-verifier-replay-build: \
	orchard-verifier-ocaml-runtime-check \
	orchard-verifier-snapshots-generated-check \
	orchard-verifier-runtime-data-check \
	$(ORCHARD_VERIFIER_REPLAY_EXE)

orchard-verifier-replay-case0: orchard-verifier-replay-build
	$(ORCHARD_VERIFIER_REPLAY_EXE) --case0

# CI and [orchard-verifier-tests] use this exact all-40 behavioral replay.
# It exits nonzero for any Rust/Rocq mismatch; BackendUnavailable is always a
# mismatch rather than a successful parser-only result.
orchard-verifier-replay-extracted: orchard-verifier-replay-build
	$(ORCHARD_VERIFIER_REPLAY_EXE) --all

# Detect OS and set appropriate commands
UTILHEADNAME_S := $(shell uname -s)
ifeq ($(UTILHEADNAME_S),Darwin)
    HEAD_CMD = ghead
else
    HEAD_CMD = head
endif

snapshot:
	rocq compile -R . Garden OpenVM/BranchEq/pretty_print.v | tail -n +2 | $(HEAD_CMD) -n -2 > OpenVM/BranchEq/core_expr.snapshot
	rocq compile -R . Garden OpenVM/Sha256/pretty_print.v | tail -n +2 | $(HEAD_CMD) -n -2 > OpenVM/Sha256/air_expr.snapshot
	rocq compile -R . Garden Plonky3/keccak/pretty_print.v | tail -n +2 | $(HEAD_CMD) -n -2 > Plonky3/keccak/air.snapshot

clean-coq: CoqMakefile
	$(MAKECOQ) clean

clean-util:
	rm -f *CoqMakefile*

clean: clean-coq
	$(MAKE) clean-util # done separately to enforce order

distclean: clean
