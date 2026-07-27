.PHONY: all clean clean-util distclean default
.PHONY: orchard-json-from-model orchard-configure-json-from-model orchard-configure-json-compare
.PHONY: orchard-synthesis-json-from-model orchard-synthesis-json-compare orchard-synthesis-json-compare-normalized

VFILES := $(shell find -L . -name "*.v" | grep -v -f blacklist.txt | sort)

default: all

CoqMakefile: $(VFILES) blacklist.txt
	echo "-R . Garden" > _CoqProject
	echo "-arg -impredicative-set -arg -w -arg -stdlib-vector" >> _CoqProject
	# We copy & paste the command to find files as this variable is too long on command line
	find -L . -name "*.v" | grep -v -f blacklist.txt | sort >> _CoqProject
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
ORCHARD_SYNTHESIS_MODEL_JSON := $(ORCHARD_SNAPSHOTS)/circuit_synthesis_generated_from_model.json
ORCHARD_SYNTHESIS_IMPL_JSON := $(ORCHARD_SNAPSHOTS)/circuit_synthesis_generated_from_implementation.json
ORCHARD_SYNTHESIS_EXTRACT := Orchard/circuit_synthesis_json_extract.v
ORCHARD_SYNTHESIS_EXTRACTED_ML := $(ORCHARD_SYNTHESIS_JSON_BUILD)/orchard_synthesis_model.ml
ORCHARD_SYNTHESIS_EXTRACTED_MLI := $(ORCHARD_SYNTHESIS_JSON_BUILD)/orchard_synthesis_model.mli
ORCHARD_SYNTHESIS_MODEL_CMX := $(ORCHARD_SYNTHESIS_JSON_BUILD)/orchard_synthesis_model.cmx
ORCHARD_SYNTHESIS_DRIVER_CMX := $(ORCHARD_SYNTHESIS_JSON_BUILD)/orchard_synthesis_json_driver.cmx
ORCHARD_SYNTHESIS_EXE := $(ORCHARD_SYNTHESIS_JSON_BUILD)/orchard_synthesis_json

$(ORCHARD_SYNTHESIS_EXTRACTED_ML): $(VFILES) $(ORCHARD_SYNTHESIS_EXTRACT) CoqMakefile
	mkdir -p $(ORCHARD_SYNTHESIS_JSON_BUILD)
	rocq compile -impredicative-set -R . Garden $(ORCHARD_SYNTHESIS_EXTRACT)

$(ORCHARD_SYNTHESIS_MODEL_CMX): $(ORCHARD_SYNTHESIS_EXTRACTED_ML) $(ORCHARD_SYNTHESIS_EXTRACTED_MLI)
	ocamlfind ocamlopt -package rocq-runtime.kernel,zarith \
	  -I $(ORCHARD_SYNTHESIS_JSON_BUILD) \
	  -c $(ORCHARD_SYNTHESIS_EXTRACTED_MLI)
	ocamlfind ocamlopt -package rocq-runtime.kernel,zarith \
	  -I $(ORCHARD_SYNTHESIS_JSON_BUILD) \
	  -c $(ORCHARD_SYNTHESIS_EXTRACTED_ML)

$(ORCHARD_SYNTHESIS_DRIVER_CMX): $(ORCHARD_SYNTHESIS_MODEL_CMX) ../scripts/orchard_synthesis_json.ml
	ocamlfind ocamlopt -package rocq-runtime.kernel,zarith \
	  -I $(ORCHARD_SYNTHESIS_JSON_BUILD) \
	  -c -o $@ ../scripts/orchard_synthesis_json.ml

$(ORCHARD_SYNTHESIS_EXE): $(ORCHARD_SYNTHESIS_MODEL_CMX) $(ORCHARD_SYNTHESIS_DRIVER_CMX)
	ocamlfind ocamlopt -package rocq-runtime.kernel,zarith -linkpkg \
	  -I $(ORCHARD_SYNTHESIS_JSON_BUILD) \
	  $(ORCHARD_SYNTHESIS_MODEL_CMX) \
	  $(ORCHARD_SYNTHESIS_DRIVER_CMX) \
	  -o $@

orchard-json-from-model: $(ORCHARD_SYNTHESIS_EXE)
	mkdir -p $(ORCHARD_SNAPSHOTS)
	$(ORCHARD_SYNTHESIS_EXE) $(ORCHARD_CONFIGURE_MODEL_JSON) $(ORCHARD_SYNTHESIS_MODEL_JSON)

orchard-configure-json-from-model: orchard-json-from-model

orchard-synthesis-json-from-model: orchard-json-from-model

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
