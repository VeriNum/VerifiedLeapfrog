# VerifiedLeapfrog

## Formally verified leapfrog integration of the simple harmonic oscillator

The Stormer-Verlet ("leapfrog") method is a numerical method for solving ordinary differential equations (ODEs). 

This repository contains Coq proofs for the formal verification of a C implementation of leapfrog integration of the simple harmonic oscillator. 

A dependency graph for our theorems in the [leapfrog_project](https://github.com/VeriNum/VerifiedLeapfrog/tree/main/leapfrog_project) directory can be found in the project [paper](https://github.com/VeriNum/VerifiedLeapfrog/blob/main/Paper.pdf) draft.

## Building

Tested on **Coq Platform 2025.08** (Rocq 9.0.1) with:

- coq-vcfloat 2.4.1
- coq-vst 2.16
- coq-compcert 3.17
- coq-flocq 4.2.1
- coq-interval 4.11.3
- coq-coquelicot 3.4.4

```sh
cd leapfrog_project
make clean && make
```

To regenerate the C-frontend file `lfharm.v` from `lfharm.c` (CompCert `clightgen`):

```sh
make clightgen
```
