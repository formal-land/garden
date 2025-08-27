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

snapshot:
	coqc -R . Garden OpenVM/BranchEq/core_expr.v | tail -n +2 | sed -e '$d' -e '$d' > OpenVM/BranchEq/core_expr.snapshot

clean-coq: CoqMakefile
	$(MAKECOQ) clean

clean-util:
	rm -f *CoqMakefile*

clean: clean-coq
	$(MAKE) clean-util # done separately to enforce order

distclean: clean
