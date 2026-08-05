.DEFAULT_GOAL := default

.PHONY: all clean clean-util distclean default
.PHONY: orchard-json-from-model orchard-configure-json-from-model orchard-configure-json-compare
.PHONY: orchard-synthesis-json-from-model orchard-synthesis-json-compare orchard-synthesis-json-compare-normalized
.PHONY: orchard-structure-json-from-model orchard-circuit-visualization-json orchard-circuit-visualization-check
.PHONY: orchard-circuit-grid-json orchard-circuit-grid-check orchard-circuit-grid-test
.PHONY: orchard-vk-pinned orchard-vk-pinned-check

# The VK provenance graph is large and branch-specific, so its inventories,
# generator rules, job controls, and explicit build targets live separately.
include vk-provenance.mk

# Excluding the generated subtree here prevents parse-time discovery from
# depending on whether a developer happens to have generated it already.
VFILES := $(shell find -L . -path './$(VK_PROVENANCE_GENERATED_DIR)' -prune -o -name "*.v" -print | grep -v -f blacklist.txt | sort)

# The ordinary project build checks every hand-written Rocq source and all
# generated literal-data modules.  The dedicated target below owns the 278
# generated provenance certificate modules; a complete kernel replay of those
# certificates is `make orchard-vk-provenance`.
DEFAULT_VOFILES := $(VFILES:.v=.vo) $(VK_PROVENANCE_GENERATED_DATA_VFILES:.v=.vo)

default: all

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
