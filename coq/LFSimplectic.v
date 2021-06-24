From Coq Require Import ZArith Reals Psatz.
From Coq Require Import Arith.Arith.
From Coquelicot Require Import Coquelicot.
Require Import Leapfrog.Iterate.

Open Scope R_scope.

Section LeapfrogDefs.

(* You can factor out common parameters like this within a Section. *)

Variable h : R.
Variable F : R -> R.

Definition leapfrog_step (xv : R * R) : R * R :=
  let (x,v) := xv in
  let x' := x + h * v + 0.5 * h^2 * F x in
  let v' := v + 0.5 * h * (F x + F x') in
  (x', v').

(* This will prevent tactics like simpl from expanding leapfrog_step *)
Opaque leapfrog_step.

Fixpoint leapfrog (xv : R * R) (n : nat) : R * R :=
  match n with
  | 0 => xv
  | S n' =>
    let xv' := leapfrog_step xv in
    leapfrog xv' n'
  end.

Definition leapfrog_iter (xv : R * R) (n : nat) : R * R :=
  iterate _ leapfrog_step xv n.

Lemma leapfrog__leapfrog_iter:
  forall n xv,
    leapfrog_iter xv n = leapfrog xv n.
Proof.
  induction n.
  - reflexivity.
  - intros; simpl.
    rewrite IHn.
    reflexivity.
Qed.

End LeapfrogDefs.

(* After the Section is closed, the definitions will be expanded (somewhat
intelligently) to take those parameters. *)

Check leapfrog.
(* leapfrog : R -> (R -> R) -> R -> R -> nat -> R * R *)

Definition jacobian (x v: R) (S: R -> R -> R * R) : (R * R) * (R * R) :=
  let dSx_dx := Derive (fun x => fst (S x v)) x in
  let dSx_dv := Derive (fun v => fst (S x v)) v in
  let dSv_dv := Derive (fun v => snd (S x v)) v in
  let dSv_dx := Derive (fun x => snd (S x v)) x in
  ((dSx_dx, dSx_dv), (dSv_dx, dSv_dv)).

Definition is_symplectic_1D (J: (R*R)*(R*R)) :=
  let S1 := fst (fst J) in
  let S2 := snd (fst J) in
  let S3 := fst (snd J) in
  let S4 := snd (snd J) in
  S1*S4 - S2*S3 = 1.

Definition F (x:R) : R := -PI^2 * x.

Lemma is_symplectic_LF :
  forall x v h,
  is_symplectic_1D (jacobian x v (leapfrog_step h F)).
Proof.
intros; unfold is_symplectic_1D.
replace (fst (snd (jacobian x v (leapfrog_step h F))))
  with (0.5 * h * (0.5*h^2*PI^4 - 2*PI^2)).
replace (snd (snd (jacobian x v (leapfrog_step h F))))
  with (1 - 0.5 * h^2 * PI^2).
replace (fst (fst (jacobian x v (leapfrog_step h F))))
  with (1 - 0.5 * h^2 * PI^2).
replace (snd (fst (jacobian x v (leapfrog_step h F))))
  with h.
nra.
all:
  simpl; unfold F; symmetry; field_simplify;
  apply is_derive_unique; auto_derive; auto; nra.
Qed.


Definition div_F (x:R) := Derive F x.

Definition dlfx (x v h: R) (F: R -> R) :=
  let dlfxdx := Derive (fun x => (fst (leapfrog_step h F x v)) ) x in
  let dlfxdv := Derive (fun v => (fst (leapfrog_step h F x v)) ) v in
  (dlfxdx, dlfxdv).

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
  let dlfvdv := Derive (fun v => (snd (leapfrog_step h F x v))) v in
  let dlfvdx := Derive (fun x => (snd (leapfrog_step h F x v))) x in
  (dlfvdv,dlfvdx).

Lemma dlfvdv_lemma (x v h: R):
  fst (dlfv x v h F) = 1 - 0.5* h^2 * PI^2.
Proof.
unfold dlfv, leapfrog_step, snd, F. apply is_derive_unique.
auto_derive. auto. nra.
Qed.

Lemma dlfvdx_lemma (x v h: R) (f: R -> R):
  f = F ->
  snd (dlfv x v h f) = 0.5 * h * (0.5*h^2*PI^4 - 2*PI^2).
Proof.
intros. replace f with F.
unfold dlfv, leapfrog_step, snd, F. apply is_derive_unique.
auto_derive. auto. nra.
Qed.

Lemma div_F_lemma:
  forall x,
  (div_F x = -PI^2).
Proof.
intros. unfold div_F, F. apply is_derive_unique.
auto_derive. auto. nra.
Qed.
