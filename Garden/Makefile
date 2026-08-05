.PHONY: all clean clean-util distclean default
.PHONY: orchard-json-from-model orchard-configure-json-from-model orchard-configure-json-compare
.PHONY: orchard-synthesis-json-from-model orchard-synthesis-json-compare orchard-synthesis-json-compare-normalized
.PHONY: orchard-structure-json-from-model orchard-circuit-visualization-json orchard-circuit-visualization-check
.PHONY: orchard-circuit-grid-json orchard-circuit-grid-check orchard-circuit-grid-test
.PHONY: orchard-vk-pinned orchard-vk-pinned-check
.PHONY: orchard-vk-provenance orchard-vk-provenance-build orchard-vk-provenance-generate
.PHONY: orchard-vk-provenance-generated-check
.PHONY: orchard-vk-provenance-witnesses orchard-vk-provenance-oracle-check

# These sources are deterministic build artifacts. An exact inventory avoids
# wildcard discovery because they do not exist on a clean checkout until the
# generator has run.
VK_PROVENANCE_GENERATED_DIR := Orchard/vk/provenance/generated
VK_PROVENANCE_CERT_DIR := $(VK_PROVENANCE_GENERATED_DIR)/certificates
VK_PROVENANCE_MANIFEST := $(VK_PROVENANCE_GENERATED_DIR)/.manifest
VK_PROVENANCE_STATE := $(VK_PROVENANCE_GENERATED_DIR)/.state.json
VK_PROVENANCE_EMITTER := ../scripts/emit_vk_provenance.py
VK_PROVENANCE_ORACLE := ../scripts/generate_vk_provenance.py
VK_PROVENANCE_GENERATOR_INPUTS := \
	$(VK_PROVENANCE_EMITTER) \
	$(VK_PROVENANCE_ORACLE) \
	Orchard/Snapshots/circuit_synthesis_generated_from_model.json \
	Orchard/Snapshots/circuit_selector_compression_generated_from_implementation.json \
	Orchard/vk/data.v

VK_PROVENANCE_FIXED_INDICES := \
	00 01 02 03 04 05 06 07 08 09 10 11 12 13 14 \
	15 16 17 18 19 20 21 22 23 24 25 26 27 28
VK_PROVENANCE_PERMUTATION_INDICES := \
	00 01 02 03 04 05 06 07 08 09 10 11 12 13 14
VK_PROVENANCE_SRS_INDICES := \
	00 01 02 03 04 05 06 07 08 09 10 11 12 13 14 15 \
	16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31
VK_PROVENANCE_FIXED_PREFIXES := \
	$(addprefix Fixed,$(VK_PROVENANCE_FIXED_INDICES))
VK_PROVENANCE_PERMUTATION_PREFIXES := \
	$(addprefix Permutation,$(VK_PROVENANCE_PERMUTATION_INDICES))
VK_PROVENANCE_COLUMN_PREFIXES := \
	$(VK_PROVENANCE_FIXED_PREFIXES) $(VK_PROVENANCE_PERMUTATION_PREFIXES)

VK_PROVENANCE_GENERATED_DATA_VFILES := \
	$(VK_PROVENANCE_GENERATED_DIR)/DomainData.v \
	$(foreach prefix,$(VK_PROVENANCE_FIXED_PREFIXES),$(VK_PROVENANCE_GENERATED_DIR)/$(prefix)Data.v) \
	$(foreach prefix,$(VK_PROVENANCE_PERMUTATION_PREFIXES),$(VK_PROVENANCE_GENERATED_DIR)/$(prefix)Data.v) \
	$(foreach index,$(VK_PROVENANCE_PERMUTATION_INDICES),$(VK_PROVENANCE_GENERATED_DIR)/Sigma$(index)Data.v) \
	$(VK_PROVENANCE_GENERATED_DIR)/SigmaData.v \
	$(foreach index,$(VK_PROVENANCE_SRS_INDICES),$(VK_PROVENANCE_GENERATED_DIR)/SrsData$(index).v) \
	$(VK_PROVENANCE_GENERATED_DIR)/SrsExtraData.v \
	$(VK_PROVENANCE_GENERATED_DIR)/SrsAll.v \
	$(foreach index,$(VK_PROVENANCE_SRS_INDICES),$(VK_PROVENANCE_GENERATED_DIR)/SrsCoordinates$(index)Data.v) \
	$(VK_PROVENANCE_GENERATED_DIR)/SrsCoordinatesExtraData.v \
	$(VK_PROVENANCE_GENERATED_DIR)/SrsCoordinatesAll.v
VK_PROVENANCE_GENERATED_CERT_VFILES := \
	$(VK_PROVENANCE_CERT_DIR)/Domain.v \
	$(foreach name,BitReversal DeltaPowers InverseRoots NInverse OmegaPowers,$(VK_PROVENANCE_CERT_DIR)/Domain$(name).v) \
	$(VK_PROVENANCE_CERT_DIR)/Sigma.v \
	$(foreach index,$(VK_PROVENANCE_PERMUTATION_INDICES),$(VK_PROVENANCE_CERT_DIR)/Sigma$(index).v) \
	$(VK_PROVENANCE_CERT_DIR)/Srs.v \
	$(foreach index,$(VK_PROVENANCE_SRS_INDICES),$(VK_PROVENANCE_CERT_DIR)/Srs$(index).v) \
	$(VK_PROVENANCE_CERT_DIR)/SrsExtra.v \
	$(VK_PROVENANCE_CERT_DIR)/Commitments.v \
	$(foreach prefix,$(VK_PROVENANCE_COLUMN_PREFIXES),$(foreach suffix,.v Assembly.v Calibration.v High.v Low.v,$(VK_PROVENANCE_CERT_DIR)/$(prefix)$(suffix))) \
	$(VK_PROVENANCE_CERT_DIR)/Main.v
VK_PROVENANCE_GENERATED_VFILES := \
	$(VK_PROVENANCE_GENERATED_DATA_VFILES) \
	$(VK_PROVENANCE_GENERATED_CERT_VFILES)

# Excluding the generated subtree here prevents parse-time discovery from
# depending on whether a developer happens to have generated it already.
VFILES := $(shell find -L . -path './$(VK_PROVENANCE_GENERATED_DIR)' -prune -o -name "*.v" -print | grep -v -f blacklist.txt | sort)

# The ordinary project build checks every hand-written Rocq source and all
# generated literal-data modules.  The dedicated target below owns the 278
# generated provenance certificate modules; a complete kernel replay of those
# certificates is `make orchard-vk-provenance`.
DEFAULT_VOFILES := $(VFILES:.v=.vo) $(VK_PROVENANCE_GENERATED_DATA_VFILES:.v=.vo)

default: all

$(VK_PROVENANCE_STATE): $(VK_PROVENANCE_GENERATOR_INPUTS)
	python3 $(VK_PROVENANCE_EMITTER) --emit-all

$(VK_PROVENANCE_MANIFEST): | $(VK_PROVENANCE_STATE)
	python3 $(VK_PROVENANCE_EMITTER) --ensure

# The order-only metadata prerequisites avoid rebuilding all sources merely
# because the generation stamp is newer.  A missing source invokes the
# locked, idempotent ensure path and recreates the entire coherent set.
$(VK_PROVENANCE_GENERATED_VFILES): | $(VK_PROVENANCE_STATE) $(VK_PROVENANCE_MANIFEST)
	@test -f $@ || python3 $(VK_PROVENANCE_EMITTER) --ensure

CoqMakefile: $(VFILES) blacklist.txt $(VK_PROVENANCE_STATE) $(VK_PROVENANCE_MANIFEST) $(VK_PROVENANCE_GENERATED_VFILES)
	echo "-R . Garden" > _CoqProject
	echo "-arg -impredicative-set -arg -w -arg -stdlib-vector" >> _CoqProject
	# The checked-in sources and generated manifest are deliberately separate.
	find -L . -path './$(VK_PROVENANCE_GENERATED_DIR)' -prune -o -name "*.v" -print | grep -v -f blacklist.txt | sort >> _CoqProject
	cat $(VK_PROVENANCE_MANIFEST) >> _CoqProject
	rocq makefile -f _CoqProject -o $@

MAKECOQ := +$(MAKE) -f CoqMakefile

%.vo: CoqMakefile %.v
	$(MAKECOQ) $@

all: CoqMakefile
	$(MAKECOQ) $(DEFAULT_VOFILES)

ORCHARD_SYNTHESIS_JSON_BUILD := _build/orchard_synthesis_json
ORCHARD_SNAPSHOTS := Orchard/Snapshots
ORCHARD_CONFIGURE_MODEL_JSON := $(ORCHARD_SNAPSHOTS)/circuit_configure_generated_from_model.json
ORCHARD_CONFIGURE_IMPL_JSON := $(ORCHARD_SNAPSHOTS)/circuit_configure_generated_from_implementation.json
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
	  $(ORCHARD_CONFIGURE_IMPL_JSON)

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

# The provenance graph has plenty of parallelism, but its leaves have very
# different memory profiles.  In particular, SRS, inverse-FFT, Pippenger and
# assembly workers retain large generated terms. Those job groups default to
# one worker. Generated literals and record-packaging leaves are
# individually cheaper, but a production-size graph can retain enough
# elaborated terms for several simultaneous workers to exhaust memory.  The
# safe default is therefore one worker for every job group; builders with
# measured memory headroom can opt into fan-out one group at a time below.
VK_PROVENANCE_CORE_JOBS ?= 1
VK_PROVENANCE_DATA_JOBS ?= 1
VK_PROVENANCE_CHECK_JOBS ?= 1
VK_PROVENANCE_SRS_JOBS ?= 1
VK_PROVENANCE_CALIBRATION_JOBS ?= 1
VK_PROVENANCE_MSM_JOBS ?= 1
VK_PROVENANCE_ASSEMBLY_JOBS ?= 1
VK_PROVENANCE_CHEAP_JOBS ?= 1
VK_PROVENANCE_FINAL_JOBS ?= 1

# VK_PROVENANCE_JOBS is a compatibility alias for the generated-data and cheap
# record-construction job counts.  It does not affect any of the four
# memory-heavy job counts above.  A memory-rich
# 32-core builder can equivalently set
#
#   VK_PROVENANCE_DATA_JOBS=32 VK_PROVENANCE_CHEAP_JOBS=32
#
# without ever launching 32 SRS/FFT/MSM/assembly workers together.
ifneq ($(origin VK_PROVENANCE_JOBS),undefined)
VK_PROVENANCE_DATA_JOBS := $(VK_PROVENANCE_JOBS)
VK_PROVENANCE_CHEAP_JOBS := $(VK_PROVENANCE_JOBS)
endif

VK_PROVENANCE_DIR := Orchard/vk/provenance
VK_PROVENANCE_MAIN := $(VK_PROVENANCE_CERT_DIR)/Main.vo

# Implementation modules that do not depend on generated tables.
VK_PROVENANCE_CORE_VOS := \
	Prim63/ArrayLinear.vo \
	Prim63/Loop.vo \
	Prim63/Words.vo \
	Prim63/Montgomery.vo \
	Prim63/Pasta.vo \
	Prim63/Refinement.vo \
	Prim63/PastaRefinement.vo \
	Prim63/WindowRefinement.vo \
	EllipticCurve/GroupOrderTight.vo \
	EllipticCurve/Vesta.vo \
	EllipticCurve/VestaOrder.vo \
	GroupHash/sswu_vesta.vo \
	GroupHash/group_hash_vesta.vo \
	GroupHash/sswu_vesta_witness.vo \
	$(VK_PROVENANCE_DIR)/DataTypes.vo \
	$(VK_PROVENANCE_DIR)/Kinds.vo \
	$(VK_PROVENANCE_DIR)/Jacobian.vo \
	$(VK_PROVENANCE_DIR)/ArrayOfListRefinement.vo \
	$(VK_PROVENANCE_DIR)/JacobianRefinement.vo \
	$(VK_PROVENANCE_DIR)/ModelColumns.vo \
	$(VK_PROVENANCE_DIR)/CompressShape.vo \
	$(VK_PROVENANCE_DIR)/OrchardCombinationCount.vo \
	$(VK_PROVENANCE_DIR)/OrchardCompressShape.vo \
	$(VK_PROVENANCE_DIR)/ModelColumnsCorrect.vo \
	$(VK_PROVENANCE_DIR)/FFT.vo \
	$(VK_PROVENANCE_DIR)/Srs.vo \
	Orchard/vk_msm.vo

# Independent generated literals.  These are the only large fan-out
# for which a memory-rich builder should normally request roughly 32 workers.
VK_PROVENANCE_DATA_LEAF_VOS := \
	$(VK_PROVENANCE_GENERATED_DIR)/DomainData.vo \
	$(foreach index,$(VK_PROVENANCE_PERMUTATION_INDICES),$(VK_PROVENANCE_GENERATED_DIR)/Sigma$(index)Data.vo) \
	$(foreach index,$(VK_PROVENANCE_SRS_INDICES),$(VK_PROVENANCE_GENERATED_DIR)/SrsData$(index).vo) \
	$(VK_PROVENANCE_GENERATED_DIR)/SrsExtraData.vo \
	$(foreach index,$(VK_PROVENANCE_SRS_INDICES),$(VK_PROVENANCE_GENERATED_DIR)/SrsCoordinates$(index)Data.vo) \
	$(VK_PROVENANCE_GENERATED_DIR)/SrsCoordinatesExtraData.vo \
	$(foreach prefix,$(VK_PROVENANCE_FIXED_PREFIXES),$(VK_PROVENANCE_GENERATED_DIR)/$(prefix)Data.vo) \
	$(foreach prefix,$(VK_PROVENANCE_PERMUTATION_PREFIXES),$(VK_PROVENANCE_GENERATED_DIR)/$(prefix)Data.vo)

VK_PROVENANCE_DATA_AGGREGATE_VOS := \
	$(VK_PROVENANCE_GENERATED_DIR)/SigmaData.vo \
	$(VK_PROVENANCE_GENERATED_DIR)/SrsCoordinatesAll.vo

VK_PROVENANCE_CHECKER_VOS := \
	$(VK_PROVENANCE_DIR)/Domain.vo \
	$(VK_PROVENANCE_DIR)/Sigma.vo \
	$(VK_PROVENANCE_DIR)/SrsDataView.vo \
	$(VK_PROVENANCE_DIR)/FixedCalibration.vo \
	$(VK_PROVENANCE_DIR)/PermutationCalibration.vo \
	$(VK_PROVENANCE_DIR)/Calibration.vo \
	$(VK_PROVENANCE_DIR)/MsmChecks.vo \
	$(VK_PROVENANCE_DIR)/AssemblyCheck.vo \
	$(VK_PROVENANCE_DIR)/Checks.vo \
	$(VK_PROVENANCE_DIR)/ColumnValues.vo \
	$(VK_PROVENANCE_DIR)/ColumnValuesCorrect.vo \
	$(VK_PROVENANCE_DIR)/DomainPowerRefinement.vo \
	$(VK_PROVENANCE_DIR)/DomainRefinement.vo \
	$(VK_PROVENANCE_DIR)/SigmaRefinement.vo \
	$(VK_PROVENANCE_DIR)/PermutationValuesCorrect.vo \
	$(VK_PROVENANCE_DIR)/MsmRefinement.vo \
	$(VK_PROVENANCE_DIR)/PinnedSpec.vo \
	$(VK_PROVENANCE_DIR)/PinnedCorrect.vo \
	$(VK_PROVENANCE_DIR)/Abstract.vo \
	$(VK_PROVENANCE_DIR)/CommitmentRefinement.vo

# Closed domain/sigma checks are smaller than the cryptographic arithmetic
# leaves and default to a single worker because they replay sizeable
# model terms.
VK_PROVENANCE_DOMAIN_LEAF_VOS := \
	$(VK_PROVENANCE_CERT_DIR)/DomainBitReversal.vo \
	$(VK_PROVENANCE_CERT_DIR)/DomainInverseRoots.vo \
	$(VK_PROVENANCE_CERT_DIR)/DomainOmegaPowers.vo \
	$(VK_PROVENANCE_CERT_DIR)/DomainDeltaPowers.vo \
	$(VK_PROVENANCE_CERT_DIR)/DomainNInverse.vo
VK_PROVENANCE_SIGMA_LEAF_VOS := \
	$(foreach index,$(VK_PROVENANCE_PERMUTATION_INDICES),$(VK_PROVENANCE_CERT_DIR)/Sigma$(index).vo)

# Hash-to-curve/SRS checks.  Each shard is independent but heavy.
VK_PROVENANCE_SRS_LEAF_VOS := \
	$(foreach index,$(VK_PROVENANCE_SRS_INDICES),$(VK_PROVENANCE_CERT_DIR)/Srs$(index).vo) \
	$(VK_PROVENANCE_CERT_DIR)/SrsExtra.vo

# Inverse FFTs, the two Pippenger halves, and final point assembly.
VK_PROVENANCE_CALIBRATION_VOS := \
	$(foreach prefix,$(VK_PROVENANCE_COLUMN_PREFIXES),$(VK_PROVENANCE_CERT_DIR)/$(prefix)Calibration.vo)
VK_PROVENANCE_MSM_VOS := \
	$(foreach prefix,$(VK_PROVENANCE_COLUMN_PREFIXES),$(VK_PROVENANCE_CERT_DIR)/$(prefix)Low.vo) \
	$(foreach prefix,$(VK_PROVENANCE_COLUMN_PREFIXES),$(VK_PROVENANCE_CERT_DIR)/$(prefix)High.vo)
VK_PROVENANCE_ASSEMBLY_VOS := \
	$(foreach prefix,$(VK_PROVENANCE_COLUMN_PREFIXES),$(VK_PROVENANCE_CERT_DIR)/$(prefix)Assembly.vo)

# These per-column files only package already-checked leaves.  They may use
# the cheap fan-out, while the graph-wide aggregates are serialized.
VK_PROVENANCE_COLUMN_AGGREGATE_VOS := \
	$(foreach prefix,$(VK_PROVENANCE_COLUMN_PREFIXES),$(VK_PROVENANCE_CERT_DIR)/$(prefix).vo)
VK_PROVENANCE_FINAL_VOS := \
	$(VK_PROVENANCE_CERT_DIR)/Domain.vo \
	$(VK_PROVENANCE_CERT_DIR)/Sigma.vo \
	$(VK_PROVENANCE_CERT_DIR)/Srs.vo \
	$(VK_PROVENANCE_CERT_DIR)/Commitments.vo \
	$(VK_PROVENANCE_MAIN)

orchard-vk-provenance-generate: $(VK_PROVENANCE_STATE) $(VK_PROVENANCE_MANIFEST) $(VK_PROVENANCE_GENERATED_VFILES)
	python3 $(VK_PROVENANCE_EMITTER) --ensure

orchard-vk-provenance-generated-check:
	python3 $(VK_PROVENANCE_EMITTER) --check

# Recompute every untrusted witness (including Params::new(11), all inverse
# FFTs, and the split Pippenger results) before refreshing the small proof
# leaves.  This is intentionally separate from the normal proof build.
orchard-vk-provenance-witnesses:
	python3 $(VK_PROVENANCE_EMITTER) --emit-all

# An independent standard-library-only oracle.  The Rocq target below does
# not trust this run; it is useful as a fast end-to-end diagnostic.
orchard-vk-provenance-oracle-check:
	python3 ../scripts/generate_vk_provenance.py --verify

orchard-vk-provenance: orchard-vk-provenance-generate
	+$(MAKE) orchard-vk-provenance-build

# This private target is invoked only after the outer make has ensured that
# all generated sources exist, so its fixed target lists are valid on a clean
# checkout as well as in a developer's populated tree.
orchard-vk-provenance-build: CoqMakefile
	@echo "[vk provenance 1/4] core modules and generated data"
	+$(MAKE) -f CoqMakefile -j$(VK_PROVENANCE_CORE_JOBS) $(VK_PROVENANCE_CORE_VOS)
	+$(MAKE) -f CoqMakefile -j$(VK_PROVENANCE_DATA_JOBS) $(VK_PROVENANCE_DATA_LEAF_VOS)
	+$(MAKE) -f CoqMakefile -j$(VK_PROVENANCE_CORE_JOBS) $(VK_PROVENANCE_DATA_AGGREGATE_VOS) $(VK_PROVENANCE_CHECKER_VOS)
	+$(MAKE) -f CoqMakefile -j$(VK_PROVENANCE_CHECK_JOBS) $(VK_PROVENANCE_DOMAIN_LEAF_VOS) $(VK_PROVENANCE_SIGMA_LEAF_VOS)
	@echo "[vk provenance 2/4] SRS leaves"
	+$(MAKE) -f CoqMakefile -j$(VK_PROVENANCE_SRS_JOBS) $(VK_PROVENANCE_SRS_LEAF_VOS)
	@echo "[vk provenance 3/4] commitment calibration, MSM, and assembly leaves"
	+$(MAKE) -f CoqMakefile -j$(VK_PROVENANCE_CALIBRATION_JOBS) $(VK_PROVENANCE_CALIBRATION_VOS)
	+$(MAKE) -f CoqMakefile -j$(VK_PROVENANCE_MSM_JOBS) $(VK_PROVENANCE_MSM_VOS)
	+$(MAKE) -f CoqMakefile -j$(VK_PROVENANCE_ASSEMBLY_JOBS) $(VK_PROVENANCE_ASSEMBLY_VOS)
	+$(MAKE) -f CoqMakefile -j$(VK_PROVENANCE_CHEAP_JOBS) $(VK_PROVENANCE_COLUMN_AGGREGATE_VOS)
	@echo "[vk provenance 4/4] serialized aggregate certificates"
	+$(MAKE) -f CoqMakefile -j$(VK_PROVENANCE_FINAL_JOBS) $(VK_PROVENANCE_FINAL_VOS)

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
