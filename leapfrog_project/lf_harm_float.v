(* This file defines a functional model for the C
   program.  *)

From Flocq Require Import Binary Bits Core.
From compcert.lib Require Import IEEE754_extra Coqlib Floats Zbits Integers.

Require Import float_lib.

Local Open Scope float32_scope.

(* Linear forcing function *)
Definition F (x : float32) : float32 := -x.

(* Time step*)
Definition h := 1 / 32.
Definition half_h := 1 / 64.
Definition pow2_h := 1/1024.
Definition half_pow2_h := 1/2048.


(* Single step of integration*)
Definition leapfrog_step' ( ic : float32 * float32) : float32 * float32 :=
  let x  := fst ic in let v:= snd ic in 
  let x' := x + h * v + half_pow2_h * F x in
  let v' :=  v +  half_h * (F x + F x')  in 
  (x', v').


(* Single step of integration*)
Definition leapfrog_step ( ic : float32 * float32) : float32 * float32 :=
  let x  := fst ic in let v:= snd ic in 
  let x' := (x + h * v) + ((1/2) * (h * h)) * F x in
  let v' :=  v +  (1/2 * h) * (F x + F x') in 
  (x', v').


Lemma lf_funs_eq ( ic : float32 * float32):
leapfrog_step' ic = leapfrog_step ic.
Proof.
unfold leapfrog_step', leapfrog_step, F, half_pow2_h, h, half_h.
replace (1 / 2048) with (1 / 2 * (1 / 32 * (1 / 32))); auto.
replace (1 / 64) with (1 / 2 * (1 / 32)); auto.
all: apply B2R_inj; auto.
Qed.


(* Main *)
Fixpoint leapfrog' ( ic : float32 * float32) (n : nat) : float32 * float32:=
  match n with
  | 0%nat => ic
  | S n' =>
    let  ic' := leapfrog_step' ic in
    leapfrog' ic' n'
  end.

Lemma lfstep_lfn:
  forall n ic ,
  leapfrog_step' (leapfrog' ic n) = leapfrog' (leapfrog_step' ic) n.
Proof.
induction n. 
- auto.
- simpl. auto. 
Qed.

Lemma lfn_eq_lfstep:
  forall n ic ,
  leapfrog' ic (S n) = leapfrog_step' (leapfrog' ic n).
Proof.
induction n.
- auto.
- intros. rewrite -> IHn. simpl. 
replace (leapfrog_step' (leapfrog' ic n)) with (leapfrog' (leapfrog_step' ic) n). destruct (leapfrog_step' ic). 
all: symmetry; apply lfstep_lfn. 
Qed.


Definition iternF  (n:nat) (x v :float32) :=  leapfrog' (x%F32, v%F32) n.


Lemma step_iternF : 
  forall n : nat,
  forall x v : float32,
  (iternF (S n) x v) = leapfrog_step' (iternF n x v).
Proof.
intros; unfold iternF; 
rewrite ?lfn_eq_lfstep; 
congruence.
Qed.
