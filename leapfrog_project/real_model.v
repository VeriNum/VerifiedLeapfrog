From Coq Require Import ZArith Reals Psatz.
From Coq Require Import Arith.Arith.
Require Import real_lemmas.
From Coquelicot Require Import Coquelicot.
Set Bullet Behavior "Strict Subproofs". 

Require Import IntervalFlocq3.Tactic.

Open Scope R_scope.


(* Time step*)
Definition h := 1 / 32.
Definition ω := 1.

Definition leapfrog_stepR (ic : R * R ) (h : R) : R * R :=
  let q := snd ic in let p := fst ic in 
  let q' := ( 1 - 0.5 * h^2*ω^2) * q + h * p  in 
  let p' := ( 1 - 0.5 * h^2*ω^2) * p - 0.5 * h * (2 - 0.5 * h^2*ω^2 ) * q in 
  (p', q').

(* assumes inputs of (p, w * q, w, n) *)
(* output q' will therefore be scaled appropriately *)
Fixpoint iternR (ic : R * R) (h : R) (n : nat): R * R:=
  match n with
  | 0%nat => ic
  | S n' =>
    let ic' := leapfrog_stepR ic h in
  iternR ic' h n'
end.

Lemma lfstepR_lfn:
  forall n ic h ,
  leapfrog_stepR (iternR ic h n) h = iternR (leapfrog_stepR ic h) h n.
Proof.
induction n. 
- auto.
- simpl. auto. 
Qed.

Lemma step_iternR:
  forall ic h n,
  iternR ic h (S n) = leapfrog_stepR (iternR ic h n) h.
Proof.
induction n.
- auto.
- intros. rewrite -> IHn. simpl. 
replace (leapfrog_stepR (iternR ic h0 n) h0) with (iternR (leapfrog_stepR ic h0) h0 n). destruct (leapfrog_stepR ic h0). 
all: symmetry; apply lfstepR_lfn. 
Qed.

Lemma one_stepR_p_alt2:
  forall ic1 ic2: R * R,
  forall h,
  (fst (leapfrog_stepR ic1 h) - fst (leapfrog_stepR ic2 h)) = 
  (1 - 0.5 * h ^ 2 * ω^2) * (fst ic1 - fst ic2) -  
   0.5 * h * (2 - 0.5 * h^2 * ω^2) * (snd ic1 - snd ic2).
Proof.
intros. destruct ic1 as [x1 v1]. destruct ic2 as [x2 v2].
unfold leapfrog_stepR, fst, snd; field_simplify. nra.
Qed.


Lemma one_stepR_q_alt2:
  forall ic1 ic2: R * R,
  forall h: R, 
  (snd (leapfrog_stepR ic1 h) - snd (leapfrog_stepR ic2 h)) = 
  (1 - 0.5 * h ^ 2 * ω^2) * (snd ic1 - snd ic2) +   h *(fst ic1 - fst ic2).
Proof.
intros. destruct ic1 as [x1 v1]. destruct ic2 as [x2 v2].
unfold leapfrog_stepR, fst, snd; field_simplify; nra.
Qed.



Lemma step_iternR_2 : 
  forall n : nat,
  forall x v h : R,
  (iternR (x,v) h (S n)) = leapfrog_stepR (iternR (x,v) h n) h.
Proof.
intros.
rewrite step_iternR.
unfold iternR. 
congruence.
Qed.

Lemma leapfrog_minus_args :
forall ic1 ic2 : (R * R),
forall h : R,
Rprod_minus (leapfrog_stepR ic1 h) (leapfrog_stepR ic2 h) = leapfrog_stepR (Rprod_minus ic1 ic2) h.
Proof.
intros.
destruct ic1; destruct ic2.
unfold leapfrog_stepR, Rprod_minus, fst ,snd.
f_equal; nra.
Qed.

Lemma leapfrog_plus_args :
forall ic1 ic2 : (R * R),
forall h : R,
Rprod_plus (leapfrog_stepR ic1 h) (leapfrog_stepR ic2 h) = leapfrog_stepR (Rprod_plus ic1 ic2) h.
Proof.
intros.
destruct ic1; destruct ic2.
unfold leapfrog_stepR, Rprod_plus, fst ,snd.
f_equal; nra.
Qed.




(*  TODO: the following need to be updated with new def of leapfrogR over p, q 
and moved into lf_harm_real_theorems *)

(*
Definition jacobian (x v: R) (S: R * R -> R * R) : (R * R) * (R * R) :=
  let dSx_dx := Derive (fun x => fst (S (x,v))) x in
  let dSx_dv := Derive (fun v => fst (S (x,v))) v in
  let dSv_dv := Derive (fun v => snd (S (x,v))) v in
  let dSv_dx := Derive (fun x => snd (S (x,v))) x in
  ((dSx_dx, dSx_dv), (dSv_dx, dSv_dv)).

Definition is_symplectic_1D (J: (R*R)*(R*R)) :=
  let S1 := fst (fst J) in
  let S2 := snd (fst J) in
  let S3 := fst (snd J) in
  let S4 := snd (snd J) in
  S1*S4 - S2*S3 = 1.


Lemma is_symplectic_LF :
  forall x v,
  is_symplectic_1D (jacobian x v (leapfrog_stepR )).
Proof.
intros; unfold is_symplectic_1D.
unfold jacobian.
unfold leapfrog_stepR, F; unfold fst, snd.
simpl;
repeat match goal with |- context [Derive (?f) ?var] =>
auto_derive_fun f; unfold F;
assert True as TR by auto;
let H := fresh "H" in
          intro H;
let H1 := fresh "H" in
pose proof (H var TR) as H1; clear TR; clear H ;
apply is_derive_unique in H1;  rewrite H1; clear H1
end.
unfold h.
field_simplify.
nra. 
Qed.

*)
Close Scope R_scope. 
