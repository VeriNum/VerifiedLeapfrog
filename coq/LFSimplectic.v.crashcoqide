From Coq Require Import ZArith Reals Psatz.
From Coq Require Import Arith.Arith.
From Coquelicot Require Import Coquelicot.
From Leapfrog Require Import Iterate.

Open Scope R_scope.

Section LeapfrogDefs.

(* You can factor out common parameters like this within a Section. *)

Variable h : R.
Variable F : R -> R.

Definition leapfrog_step (x v : R) : R * R :=
  let x' := x + h * v + 0.5 * h^2 * F x in
  let v' := v + 0.5 * h * (F x + F x') in
  (x', v').

(* This will prevent tactics like simpl from expanding leapfrog_step. If you
want to switch back use Transparent *)
Opaque leapfrog_step.

Fixpoint leapfrog (x v : R) (n : nat) : R * R :=
  match n with
  | 0 => (x, v)
  | S n' =>
    let (x', v') := leapfrog_step x v in
    leapfrog x' v' n'
  end.

Definition leapfrog_iter (x v : R) (n : nat) : R * R :=
  iterate _ (uncurry leapfrog_step) (x, v) n.

Lemma leapfrog__leapfrog_iter:
  forall n x v,
    leapfrog_iter x v n = leapfrog x v n.
Proof.
  induction n.
  - reflexivity.
  - intros; simpl.
    destruct (leapfrog_step x v) eqn:Heq.
    rewrite <- IHn.
    unfold leapfrog_iter.
    rewrite <- Heq.
    constructor.
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

Definition F x := -PI^2 * x.

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

