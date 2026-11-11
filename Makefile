ROCQ ?= rocq

.PHONY: all check clean

all: RocqMakefile
	$(MAKE) -f RocqMakefile all

RocqMakefile: _CoqProject
	$(ROCQ) makefile --rocq-package weak-memory-local-reasoning -f _CoqProject -o RocqMakefile

check: all
	$(ROCQ) check -silent -Q theories WMLR WMLR.Audit

clean: RocqMakefile
	$(MAKE) -f RocqMakefile clean
