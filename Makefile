ROCQ ?= rocq
COQCHK ?= coqchk

.DEFAULT_GOAL := all

Makefile.coq: _CoqProject
	$(ROCQ) makefile -f _CoqProject -o Makefile.coq

-include Makefile.coq

.PHONY: check tests check-generated
check-generated:
	python3 scripts/generate_moves.py --check

check: all check-generated
	$(COQCHK) -silent -R . minirubik \
	  $(addprefix minirubik.,$(basename $(VFILES)))

tests: check
