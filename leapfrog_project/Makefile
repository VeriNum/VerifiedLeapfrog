VST_LOC=../../vst64
CC_LOC=../../CompCert64
VCFLOAT_LOC=../../vcfloat/vcfloat

VST_Q != cat $(VST_LOC)/_CoqProject-export

COQFLAGS= -Q $(VCFLOAT_LOC) vcfloat $(VST_Q)

all: _CoqProject verif_lfharm.vo

_CoqProject: $(VST_LOC)/_CoqProject-export Makefile
	echo $(COQFLAGS) >_CoqProject

float_lib.vo: float_lib.v

lf_harm_float.vo: lf_harm_float.v float_lib.vo

lfharm.v: lfharm.c
	$(CC_LOC)/clightgen -normalize $<

verif_lfharm.vo: lfharm.vo lf_harm_float.vo lf_harm_lemmas.vo

lf_harm_lemmas.vo: lf_harm_lemmas.v lf_harm_float.vo

%.vo: %.v
	coqc $(COQFLAGS) -I . $<

