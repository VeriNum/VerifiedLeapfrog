(* This file defines a functional model for the C
   program.  *)

From Flocq Require Import Binary Bits Core.
From compcert.lib Require Import IEEE754_extra
 (* Coqlib Floats Zbits Integers*).

Require Import vcfloat.FPCore vcfloat.Reify vcfloat.Float_notations.
Set Bullet Behavior "Strict Subproofs". 

Local Open Scope float32_scope.

Section WITHNANS.
Context {NANS: Nans}.

(** A single step of integration can modeled as either 
(1) a transition matrix update to the vector (p,q) of momentum "p" and position "q", as
  given in "leapfrog_stepF"
-or-
(2) the "typical" velocity verlet scheme, as given in "leapfrog_stepF_ver" **)


(** Compute one time-step: given "ic" which is a pair of momentum "q" and position "p" ,
  calculate the new position and mometum after time "h" has elapsed. **)

Definition h := (1 / 32)%F32.   (* Time-step: 1/32 of a second *)


(* Linear forcing function *)
Definition F (x : ftype Tsingle) : ftype Tsingle := -x.


(* Single step of Verlet integration *)
Definition leapfrog_stepF (ic : ftype Tsingle * ftype Tsingle) : ftype Tsingle * ftype Tsingle :=
  let x  := fst ic in let v:= snd ic in 
  let x' := (x + h * v) + ((1/2) * (h * h)) * F x in
  let v' :=  v +  (1/2 * h) * (F x + F x') in 
  (x', v').


(** Iterations **)

(* Main *)
Fixpoint iternF (ic: ftype Tsingle * ftype Tsingle) (n : nat): ftype Tsingle * ftype Tsingle:=
  match n with
  | 0%nat => ic
  | S n' =>
    let ic' := leapfrog_stepF ic in
  iternF  ic' n'
end.


(** Lemmas **)


Lemma lfstep_lfn:
  forall n ic ,
  leapfrog_stepF (iternF ic n) = iternF (leapfrog_stepF ic) n.
Proof.
induction n. 
- auto.
- simpl. auto. 
Qed.


Lemma step_iternF:
  forall n ic ,
  iternF  ic (S n) = leapfrog_stepF (iternF ic n).
Proof.
induction n.
- auto.
- intros. rewrite -> IHn. simpl. 
replace (leapfrog_stepF (iternF _ _ )) with (iternF (leapfrog_stepF ic) n). 
  destruct (leapfrog_stepF ic). 
all: symmetry; apply lfstep_lfn. 
Qed.

End WITHNANS.


