CC      = gcc
CCOMP  = ccomp
CFLAGS  = -g
RM      = rm -f


default: Diffcc

all: Diffgcc Diffcc

Diffgcc: lfharm_diff.c
	$(CC) -o gcc_lfharm_diff lfharm_diff.c


Diffcc: lfharm_diff.c
	$(CCOMP) -o compcc_lfharm_diff lfharm_diff.c -lm

clean:
	$(RM) gcc_lfharm_diff compcc_lfharm_diff

out_clean:
	$(RM) *.png *.txt

result: findbad
	./findbad 20 10000000 > result


findbad: findbad.c
	gcc -O2 findbad.c -o findbad
