VST_LOC=../../vst64
CC_LOC=../../CompCert64

COQFLAGS != cat $(VST_LOC)/_CoqProject-export

all: _CoqProject verif_lfharm.vo

_CoqProject: $(VST_LOC)/_CoqProject-export
	cp $< _CoqProject

lfharm.v: lfharm.c
	$(CC_LOC)/clightgen -normalize $<

verif_lfharm.vo: lfharm.vo lf_harm_float.vo lf_harm_lemmas.vo

lf_harm_lemmas.vo: lf_harm_lemmas.v lf_harm_float.vo

%.vo: %.v
	coqc $(COQFLAGS) -I . $<

