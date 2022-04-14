From Coq Require Import ZArith Reals Psatz.
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

Definition h : ftype Tsingle := 1 / 32.   (* Time-step: 1/32 of a second *)
Definition ω : ftype Tsingle := 1.

(* Linear force function *)
Definition F_alt (x : ftype Tsingle) : ftype Tsingle := -((ω*ω)*x).
Definition F (x : ftype Tsingle) : ftype Tsingle := -x.
(* We will use F rather than F_alt in the floating-point functional model,
  because the C program omits the multiplication by 1.0*1.0.  
  You might think that (1.0*1.0)*x is the same as x, but we do
  not wish to use the identity (1.0*x=x)  _in the floats_;  we want
  to match exactly the computation that the C program does. *)

(* Single step of Verlet integration *)
Definition leapfrog_stepF (ic : ftype Tsingle * ftype Tsingle) : ftype Tsingle * ftype Tsingle :=
  let p  := fst ic in let q := snd ic in 
  let q' := (q + h * p) + (0.5 * (h * h)) * F q in
  let p' :=  p +  (0.5 * h) * (F q + F q') in 
  (p', q').


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

Lemma Ziter_itern:  (* Delete this lemma?  doesn't seem to be used. *)
  forall x v i,
  (Z.iter i leapfrog_stepF (x, v)) = iternF (x, v) (Z.to_nat i).
Proof.
intros.
destruct (Z_le_dec 0 i).
-
 pattern i at 1; rewrite <- (Z2Nat.id i)  by auto.
 clear.
 set (xv := (x,v)). clearbody xv.
revert xv; induction (Z.to_nat i); intros.
 + reflexivity.
 + rewrite inj_S. rewrite Zbits.Ziter_succ by lia. simpl iternF.
     rewrite IHn.
     apply lfstep_lfn.
-
  rewrite Zbits.Ziter_base by lia.
  destruct i; try lia. simpl. auto.
Qed.

(* The initial conditions of the momentum "p" and position "q" specified for the integration scheme*)
Definition p_init: ftype Tsingle :=  0%F32.
Definition q_init: ftype Tsingle :=  1%F32.

Definition iternF_is_finite : Prop :=
  forall n : nat,  ( n <= 100)%nat->
  (is_finite _ _  (fst(iternF (p_init,q_init)  n)) = true) /\
  (is_finite _ _  (snd(iternF (p_init,q_init)  n)) = true).

End WITHNANS.


