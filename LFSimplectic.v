From Coq Require Import ZArith Reals Psatz.
From Coq Require Import Arith.Arith.
From Coquelicot Require Import Coquelicot.

Open Scope R_scope.

Definition leapfrog_step xn vn h F := 
    let x1  := xn + h*vn + 0.5*h^2*(F xn) in
    let v1  := vn + 0.5*h*(F xn + F x1) in
    pair x1 v1.


Fixpoint leapfrog x0 v0 h F (n:nat):=
    match n with 
    | 0 => pair x0 v0
    | S n' => 
        let xn := fst (leapfrog_step x0 v0 h F) in
        let vn := snd (leapfrog_step x0 v0 h F) in
        leapfrog xn vn h F (n')
    end.

Definition F (x:R) := -PI^2 * x.

Definition div_F (x:R) := Derive F x.

Lemma div_F_lemma:
  forall x,
  (div_F x = -PI^2). 
Proof.
intros. unfold div_F, F. apply is_derive_unique.
auto_derive. auto. nra.
Qed.

Definition dlfx (x v h: R) (F: R -> R) := 
  let dlfxdx := Derive (fun x => (fst (leapfrog_step x v h F)) ) x in
  let dlfxdv := Derive (fun v => (fst (leapfrog_step x v h F)) ) v in 
  pair dlfxdx dlfxdv.


Lemma dlfxdx_lemma (x v h: R):
  fst (dlfx x v h F) = 1 - 0.5 * h^2 * PI^2. 
Proof.
unfold dlfx, leapfrog_step, fst, F. apply is_derive_unique.
auto_derive. auto. nra.
Qed.

Lemma dlfxdv_lemma (x v h: R):
  snd (dlfx x v h F) = h. 
Proof.
unfold dlfx, leapfrog_step, fst, F. apply is_derive_unique.
auto_derive. auto. nra.
Qed.

Definition dlfv (x v h: R) (F: R -> R) := 
  let dlfvdv := Derive (fun v => (snd (leapfrog_step x v h F)) ) v in
  let dlfvdx := Derive (fun x => (snd (leapfrog_step x v h F)) ) x in 
  pair dlfvdv dlfvdx.

Lemma dlfvdv_lemma (x v h: R):
  fst (dlfv x v h F) = 1 - 0.5* h^2 * PI^2. 
Proof.
unfold dlfv, leapfrog_step, snd, F. apply is_derive_unique.
auto_derive. auto. nra.
Qed.

Lemma dlfvdx_lemma (x v h: R) (f: R -> R):
  f = F->
  snd (dlfv x v h f) = 0.5 * h * (0.5*h^2*PI^4 - 2*PI^2). 
Proof.
intros. replace f with F.
unfold dlfv, leapfrog_step, snd, F. apply is_derive_unique.
auto_derive. auto. nra.
Qed.

Definition jacobian (x v h: R) (f: R -> R) (S: R -> R -> R -> (R -> R) -> (R * R)) :=
  let dSx_dx := Derive (fun x => (fst (S x v h f)) ) x in
  let dSx_dv := Derive (fun v => (fst (S x v h f)) ) v in 
  let dSv_dv := Derive (fun v => (snd (S x v h f)) ) v in
  let dSv_dx := Derive (fun x => (snd (S x v h f)) ) x in
  pair (pair dSx_dx dSx_dv) (pair dSv_dx dSv_dv).

Definition is_symplectic_1D (J: (R*R)*(R*R)):=
    let S1 := fst(fst J ) in
    let S2 := snd(fst J) in
    let S3 := fst(snd J) in
    let S4 := snd(snd J) in 
    S1*S4 - S2*S3 = 1.

Lemma is_symplectic_LF : 
  forall x v h,
  is_symplectic_1D (jacobian x v h F leapfrog_step).
Proof.
intros; unfold is_symplectic_1D.
replace (fst (snd (jacobian x v h F leapfrog_step))) with (0.5 * h * (0.5*h^2*PI^4 - 2*PI^2)).
replace (snd (snd (jacobian x v h F leapfrog_step))) with (1 - 0.5 * h^2 * PI^2).
replace (fst (fst (jacobian x v h F leapfrog_step))) with (1 - 0.5 * h^2 * PI^2).
replace (snd (fst (jacobian x v h F leapfrog_step))) with h.
nra.
all: simpl; unfold F; symmetry; field_simplify; apply is_derive_unique; auto_derive; auto; nra. 
Qed.



