(* This file defines a functional model for the C
   program.  *)

From Flocq Require Import Binary Bits Core.
From compcert.lib Require Import IEEE754_extra
 (* Coqlib Floats Zbits Integers*).

Require Import vcfloat.FPCore vcfloat.Reify vcfloat.Float_notations.

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


(* Single step of integration modeling a transition matrix update *)
Definition leapfrog_stepF (ic : ftype Tsingle * ftype Tsingle) : (ftype Tsingle * ftype Tsingle)  :=
  let p:= fst ic in let q:= snd ic in 
  let q' := (1 - ((1/2) * (h * h))) * q + (h * p) in
  let p' := (1 - ((1/2) * (h * h))) * p - ((1/2 * h) * (2 - ((1/2) * (h * h)))) * q  in 
  (p', q').



(* Linear forcing function *)
Definition F (x : ftype Tsingle) : ftype Tsingle := -x.



(* Single step of Verlet integration *)
Definition leapfrog_stepF_ver (ic : ftype Tsingle * ftype Tsingle) : ftype Tsingle * ftype Tsingle :=
  let x  := fst ic in let v:= snd ic in 
  let x' := (x + h * v) + ((1/2) * (h * h)) * F x in
  let v' :=  v +  (1/2 * h) * (F x + F x') in 
  (x', v').


(** Iterations **)

(* Main *)
Fixpoint leapfrogF (Step: (ftype Tsingle * ftype Tsingle) -> (ftype Tsingle * ftype Tsingle)) 
  (ic: ftype Tsingle * ftype Tsingle) (n : nat): ftype Tsingle * ftype Tsingle:=
  match n with
  | 0%nat => ic
  | S n' =>
    let ic' :=  Step ic in
  leapfrogF Step ic' n'
end.


Definition iternF (ic: ftype Tsingle * ftype Tsingle) (n:nat) :=  leapfrogF leapfrog_stepF ic n.

Definition iternF_ver (ic: ftype Tsingle * ftype Tsingle) (n:nat) :=  leapfrogF leapfrog_stepF_ver ic n.



(** Lemmas **)


Lemma lfstep_lfn:
  forall n ic ,
  leapfrog_stepF (leapfrogF leapfrog_stepF ic n) = leapfrogF leapfrog_stepF (leapfrog_stepF ic) n.
Proof.
induction n. 
- auto.
- simpl. auto. 
Qed.

Lemma lfn_eq_lfstep:
  forall n ic ,
  leapfrogF leapfrog_stepF ic (S n) = leapfrog_stepF (leapfrogF leapfrog_stepF ic n).
Proof.
induction n.
- auto.
- intros. rewrite -> IHn. simpl. 
replace (leapfrog_stepF (leapfrogF _ _ _ )) with (leapfrogF leapfrog_stepF (leapfrog_stepF ic) n). 
  destruct (leapfrog_stepF ic). 
all: symmetry; apply lfstep_lfn. 
Qed.

Lemma step_iternF : 
  forall n : nat,
  forall ic, 
  (iternF  ic (S n)) = leapfrog_stepF (iternF ic n ).
Proof.
intros; unfold iternF.
rewrite ?lfn_eq_lfstep; 
congruence.
Qed.


Lemma lfstep_lfn_ver:
  forall n ic ,
  leapfrog_stepF_ver (leapfrogF leapfrog_stepF_ver ic n) = leapfrogF leapfrog_stepF_ver (leapfrog_stepF_ver ic) n.
Proof.
induction n. 
- auto.
- simpl. auto. 
Qed.

Lemma lfn_eq_lfstep_ver:
  forall n ic ,
  leapfrogF leapfrog_stepF_ver ic (S n) = leapfrog_stepF_ver (leapfrogF leapfrog_stepF_ver ic n).
Proof.
induction n.
- auto.
- intros. rewrite -> IHn. simpl. 
replace (leapfrog_stepF_ver (leapfrogF _ _ _ )) with (leapfrogF leapfrog_stepF_ver (leapfrog_stepF_ver ic) n). 
  destruct (leapfrog_stepF_ver ic). 
all: symmetry; apply lfstep_lfn_ver. 
Qed.

Lemma step_iternF_ver : 
  forall n : nat,
  forall ic, 
  (iternF_ver  ic (S n)) = leapfrog_stepF_ver (iternF_ver ic n ).
Proof.
intros; unfold iternF_ver.
rewrite ?lfn_eq_lfstep_ver; 
congruence.
Qed.

End WITHNANS.


