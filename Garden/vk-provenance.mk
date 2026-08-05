# Orchard verifying-key provenance generation and explicit proof replay.

.PHONY: orchard-vk-provenance orchard-vk-provenance-build orchard-vk-provenance-generate
.PHONY: orchard-vk-provenance-generated-check
.PHONY: orchard-vk-provenance-witnesses orchard-vk-provenance-oracle-check

# These sources are deterministic build artifacts. An exact inventory avoids
# wildcard discovery because they do not exist on a clean checkout until the
# generator has run.
VK_PROVENANCE_DIR := Orchard/vk/provenance
VK_PROVENANCE_GENERATED_DIR := $(VK_PROVENANCE_DIR)/generated
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

$(VK_PROVENANCE_STATE): $(VK_PROVENANCE_GENERATOR_INPUTS)
	python3 $(VK_PROVENANCE_EMITTER) --emit-all

$(VK_PROVENANCE_MANIFEST): | $(VK_PROVENANCE_STATE)
	python3 $(VK_PROVENANCE_EMITTER) --ensure

# The order-only metadata prerequisites avoid rebuilding all sources merely
# because the generation stamp is newer. A missing source invokes the locked,
# idempotent ensure path and recreates the entire coherent set.
$(VK_PROVENANCE_GENERATED_VFILES): | $(VK_PROVENANCE_STATE) $(VK_PROVENANCE_MANIFEST)
	@test -f $@ || python3 $(VK_PROVENANCE_EMITTER) --ensure

# The provenance graph has plenty of parallelism, but its leaves have very
# different memory profiles. In particular, SRS, inverse-FFT, Pippenger and
# assembly workers retain large generated terms. The safe default is one
# worker for every job group; builders with measured memory headroom can opt
# into fan-out one group at a time.
VK_PROVENANCE_CORE_JOBS ?= 1
VK_PROVENANCE_DATA_JOBS ?= 1
VK_PROVENANCE_CHECK_JOBS ?= 1
VK_PROVENANCE_SRS_JOBS ?= 1
VK_PROVENANCE_CALIBRATION_JOBS ?= 1
VK_PROVENANCE_MSM_JOBS ?= 1
VK_PROVENANCE_ASSEMBLY_JOBS ?= 1
VK_PROVENANCE_CHEAP_JOBS ?= 1
VK_PROVENANCE_FINAL_JOBS ?= 1

# Compatibility alias for generated-data and cheap record-construction jobs.
# It deliberately does not affect the memory-heavy job groups.
ifneq ($(origin VK_PROVENANCE_JOBS),undefined)
VK_PROVENANCE_DATA_JOBS := $(VK_PROVENANCE_JOBS)
VK_PROVENANCE_CHEAP_JOBS := $(VK_PROVENANCE_JOBS)
endif

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

# Independent generated literals. These are the only large fan-out for which
# a memory-rich builder should normally request roughly 32 workers.
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
# leaves but still replay sizeable model terms.
VK_PROVENANCE_DOMAIN_LEAF_VOS := \
	$(VK_PROVENANCE_CERT_DIR)/DomainBitReversal.vo \
	$(VK_PROVENANCE_CERT_DIR)/DomainInverseRoots.vo \
	$(VK_PROVENANCE_CERT_DIR)/DomainOmegaPowers.vo \
	$(VK_PROVENANCE_CERT_DIR)/DomainDeltaPowers.vo \
	$(VK_PROVENANCE_CERT_DIR)/DomainNInverse.vo
VK_PROVENANCE_SIGMA_LEAF_VOS := \
	$(foreach index,$(VK_PROVENANCE_PERMUTATION_INDICES),$(VK_PROVENANCE_CERT_DIR)/Sigma$(index).vo)

# Hash-to-curve/SRS checks. Each shard is independent but heavy.
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

# These per-column files only package already-checked leaves. They may use the
# cheap fan-out, while the graph-wide aggregates are serialized.
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
# leaves. This is intentionally separate from the normal proof build.
orchard-vk-provenance-witnesses:
	python3 $(VK_PROVENANCE_EMITTER) --emit-all

# An independent standard-library-only oracle. The Rocq target below does not
# trust this run; it is useful as a fast end-to-end diagnostic.
orchard-vk-provenance-oracle-check:
	python3 $(VK_PROVENANCE_ORACLE) --verify

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
