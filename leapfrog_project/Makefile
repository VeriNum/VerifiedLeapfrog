# VST_LOC=../../vst64
CC_LOC=../../CompCert64
VCFLOAT_LOC=../../vcfloat/vcfloat

ifdef VST_LOC
VST_Q != cat $(VST_LOC)/_CoqProject-export
endif 

COQFLAGS= -Q $(VCFLOAT_LOC) vcfloat $(VST_Q)

all: _CoqProject verif_lfharm.vo

_CoqProject: Makefile
	echo $(COQFLAGS) >_CoqProject

float_lib.vo: float_lib.v float_notations.vo

vcfloat.vo: vcfloat.v float_lib.vo

optimize.vo: optimize.v float_lib.vo vcfloat.vo

real_lemmas.vo: real_lemmas.v 

lf_harm_float.vo: lf_harm_float.v float_lib.vo

lf_harm_real.vo: lf_harm_real.v real_lemmas.vo

lf_harm_real_theorems.vo: lf_harm_real_theorems.v real_lemmas.vo lf_harm_real.vo 

lfharm.v: lfharm.c
	$(CC_LOC)/clightgen -normalize $<

verif_lfharm.vo: lfharm.vo lf_harm_float.vo lf_harm_lemmas.vo

lf_harm_lemmas.vo: lf_harm_lemmas.v lf_harm_float.vo lf_harm_real.vo vcfloat.vo optimize.vo real_lemmas.vo

lf_harm_theorems.vo: lf_harm_theorems.v lf_harm_float.vo lf_harm_real.vo vcfloat.vo optimize.vo real_lemmas.vo lf_harm_lemmas.vo  

%.vo: %.v
	coqc $(COQFLAGS) -I . $<

clean:
	rm -f *.vo *.vok *.vos *.glob lfharm.v _CoqProject
