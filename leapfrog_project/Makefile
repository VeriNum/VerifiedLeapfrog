# VST_LOC=../../vst64
CC_LOC=../../CompCert64
VCFLOAT_LOC=../../vcfloat/vcfloat

ifdef VST_LOC
VST_Q != cat $(VST_LOC)/_CoqProject-export
endif 

COQFLAGS= -Q $(VCFLOAT_LOC) vcfloat $(VST_Q)

all: _CoqProject main.vo

_CoqProject: Makefile
	echo $(COQFLAGS) >_CoqProject

float_lib.vo: float_lib.v

vcfloat.vo: vcfloat.v

real_lemmas.vo: real_lemmas.v 

lf_harm_float.vo: lf_harm_float.v

lf_harm_real.vo: lf_harm_real.v real_lemmas.vo

lf_harm_real_theorems.vo: lf_harm_real_theorems.v real_lemmas.vo lf_harm_real.vo 
main.vo: main.v verif_lfharm.vo lf_harm_float.vo lf_harm_theorems.vo


lfharm.v: lfharm.c
	$(CC_LOC)/clightgen -normalize $<

lf_harm_lemmas.vo: lf_harm_lemmas.v lf_harm_float.vo lf_harm_real.vo lf_harm_real_theorems.vo vcfloat.vo real_lemmas.vo

lf_harm_theorems.vo: lf_harm_theorems.v  lf_harm_float.vo lf_harm_real.vo lf_harm_real_theorems.vo vcfloat.vo real_lemmas.vo lf_harm_lemmas.vo 
verif_lfharm.vo: lfharm.vo lf_harm_float.vo lf_harm_lemmas.vo lf_harm_theorems.vo


%.vo: %.v
	coqc $(COQFLAGS) -I . $<

clean:
	rm -f *.vo *.vok *.vos *.glob 
