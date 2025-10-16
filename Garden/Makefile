.PHONY: all clean clean-util distclean default

VFILES := $(shell find -L . -name "*.v" | grep -v -f blacklist.txt | sort)

default: all

CoqMakefile: $(VFILES) blacklist.txt
	echo "-R . Garden" > _CoqProject
	echo "-arg -impredicative-set -arg -w -arg -stdlib-vector" >> _CoqProject
	# We copy & paste the command to find files as this variable is too long on command line
	find -L . -name "*.v" | grep -v -f blacklist.txt | sort >> _CoqProject
	coq_makefile -f _CoqProject -o $@

MAKECOQ := +$(MAKE) -f CoqMakefile

%.vo: CoqMakefile %.v
	$(MAKECOQ) $@

all: CoqMakefile
	$(MAKECOQ) all
	$(MAKE) snapshot

# Detect OS and set appropriate commands
UTILHEADNAME_S := $(shell uname -s)
ifeq ($(UTILHEADNAME_S),Darwin)
    HEAD_CMD = ghead
else
    HEAD_CMD = head
endif

snapshot:
	coqc -R . Garden OpenVM/BranchEq/pretty_print.v | tail -n +2 | $(HEAD_CMD) -n -2 > OpenVM/BranchEq/core_expr.snapshot
	coqc -R . Garden OpenVM/Sha256/pretty_print.v | tail -n +2 | $(HEAD_CMD) -n -2 > OpenVM/Sha256/air_expr.snapshot
	coqc -R . Garden Plonky3/keccak/proofs/pretty_print.v | tail -n +2 | $(HEAD_CMD) -n -2 > Plonky3/keccak/proofs/air_local.snapshot

clean-coq: CoqMakefile
	$(MAKECOQ) clean

clean-util:
	rm -f *CoqMakefile*

clean: clean-coq
	$(MAKE) clean-util # done separately to enforce order

distclean: clean
