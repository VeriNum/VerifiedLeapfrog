(* This file defines a functional model for the C
   program.  *)

From Flocq Require Import Binary Bits Core.
From compcert.lib Require Import IEEE754_extra
 (* Coqlib Floats Zbits Integers*).

Require Import vcfloat.FPCore vcfloat.Reify vcfloat.Float_notations.

Local Open Scope float32_scope.

Section WITHNANS.
Context {NANS: Nans}.

(* Linear forcing function *)
Definition F (x : ftype Tsingle) : ftype Tsingle := -x.

(* Time step*)
Definition h := 1 / 32.
Definition half_h := 1 / 64.
Definition pow2_h := 1/1024.
Definition half_pow2_h := 1/2048.


(* Single step of integration*)
Definition leapfrog_stepF' ( ic : ftype Tsingle * ftype Tsingle) : ftype Tsingle * ftype Tsingle :=
  let x  := fst ic in let v:= snd ic in 
  let x' := x + h * v + half_pow2_h * F x in
  let v' :=  v +  half_h * (F x + F x')  in 
  (x', v').


(* Single step of integration*)
Definition leapfrog_stepF'' ( ic : ftype Tsingle * ftype Tsingle) : ftype Tsingle * ftype Tsingle :=
  let x  := fst ic in let v:= snd ic in 
  let x' := (x + h * v) + ((1/2) * (h * h)) * F x in
  let v' :=  v +  (1/2 * h) * (F x + F x') in 
  (x', v').


Lemma lf_funs_eq ( ic : ftype Tsingle * ftype Tsingle):
leapfrog_stepF' ic = leapfrog_stepF'' ic.
Proof.
unfold leapfrog_stepF', leapfrog_stepF'', F, half_pow2_h, h, half_h.
replace (1 / 2048) with (1 / 2 * (1 / 32 * (1 / 32))); auto.
replace (1 / 64) with (1 / 2 * (1 / 32)); auto.
all: apply B2R_inj; auto.
Qed.


(* Main *)
Fixpoint leapfrogF' ( ic : ftype Tsingle * ftype Tsingle) (n : nat) : ftype Tsingle * ftype Tsingle:=
  match n with
  | 0%nat => ic
  | S n' =>
    let  ic' := leapfrog_stepF' ic in
    leapfrogF' ic' n'
  end.

Definition leapfrog_stepF ic : ftype Tsingle * ftype Tsingle :=
  let p:= fst ic in let q:= snd ic in 
  let q' := (1 - half_pow2_h) * q + (h * p) in
  let p' := (1 - half_pow2_h) * p - (half_h * (2 - half_pow2_h)) * q  in 
  (p', q').

(* assumes inputs of (p, w * q, w, n) *)
(* output q' will therefore be scaled appropriately *)
Fixpoint leapfrogF (ic: ftype Tsingle * ftype Tsingle) (n : nat): ftype Tsingle * ftype Tsingle:=
  match n with
  | 0%nat => ic
  | S n' =>
    let ic' :=  leapfrog_stepF ic in
  leapfrogF ic' n'
end.


Lemma lfstep_lfn:
  forall n ic ,
  leapfrog_stepF (leapfrogF ic n) = leapfrogF (leapfrog_stepF ic) n.
Proof.
induction n. 
- auto.
- simpl. auto. 
Qed.

Lemma lfn_eq_lfstep:
  forall n ic ,
  leapfrogF ic (S n) = leapfrog_stepF (leapfrogF ic n).
Proof.
induction n.
- auto.
- intros. rewrite -> IHn. simpl. 
replace (leapfrog_stepF (leapfrogF ic n)) with (leapfrogF (leapfrog_stepF ic) n). destruct (leapfrog_stepF ic). 
all: symmetry; apply lfstep_lfn. 
Qed.


Definition iternF (ic: ftype Tsingle * ftype Tsingle) (n:nat) :=  leapfrogF ic n.


Lemma step_iternF : 
  forall n : nat,
  forall ic, 
  (iternF ic (S n)) = leapfrog_stepF (iternF ic n ).
Proof.
intros; unfold iternF; 
rewrite ?lfn_eq_lfstep; 
congruence.
Qed.

End WITHNANS.


