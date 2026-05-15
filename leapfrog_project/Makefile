KNOWNTARGETS := Makefile.coq clightgen clean cleanall
KNOWNFILES   := Makefile _CoqProject

.DEFAULT_GOAL := invoke-coqmakefile

Makefile.coq Makefile.coq.conf: Makefile _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject -o Makefile.coq

invoke-coqmakefile: Makefile.coq.conf Makefile.coq
	$(MAKE) --no-print-directory -f Makefile.coq $(filter-out $(KNOWNTARGETS),$(MAKECMDGOALS))

clightgen:
	clightgen -normalize lfharm.c
	sed -i.bak -e 's/From Coq Require/From Stdlib Require/g' lfharm.v && rm -f lfharm.v.bak

clean cleanall:
	+[ ! -f Makefile.coq ] || $(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq Makefile.coq.conf .nia.cache .lia.cache

.PHONY: invoke-coqmakefile clightgen clean cleanall

$(KNOWNFILES):
	@true

%: invoke-coqmakefile
	@true
