all: Makefile.coq
	+make -f Makefile.coq all

clean: Makefile.coq
	+make -f Makefile.coq clean
	rm -f Makefile.coq Makefile.coq.conf Makefile.coq.d

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

.PHONY: clean all
