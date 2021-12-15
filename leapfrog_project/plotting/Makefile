CC      = gcc
CCOMP  = ccomp
CFLAGS  = -g
RM      = rm -f


default: all

all: Diffgcc Diffcc

Diffgcc: lfharm_diff.c
	$(CC) -o gcc_lfharm_diff lfharm_diff.c


Diffcc: lfharm_diff.c
	$(CCOMP) -o compcc_lfharm_diff lfharm_diff.c

clean:
	$(RM) gcc_lfharm_diff compcc_lfharm_diff

out_clean:
	$(RM) *.png *.txt
