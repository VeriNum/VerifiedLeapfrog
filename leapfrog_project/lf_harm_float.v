From Flocq Require Import Binary Bits Core.
From compcert.lib Require Import IEEE754_extra Coqlib Floats Zbits Integers.
Require Import float_lib.

Definition half := Float32.div 1 2.

(* Linear forcing function *)
Definition F (x : float32) : float32 := (- 1%F32 * x)%F32.

(* Time step*)
Definition h := Float32.div 1 32.

Opaque F h half.

(* Single step of the integrator*)
Definition leapfrog_step ( ic : float32 * float32) : float32 * float32 :=
  (let x  := fst ic in let v:= snd ic in 
  let x' := (x + h * v) + (h * h * F x)*half in
  let v' :=  v + (half*h*(F x + F x')) in 
  (x', v'))%F32.

(* Main *)
Fixpoint leapfrog ( ic : float32 * float32) (n : nat) : float32 * float32:=
  match n with
  | 0%nat => ic
  | S n' =>
    let  ic' := leapfrog_step ic in
    leapfrog ic' n'
  end.

Lemma lfstep_lfn:
  forall n ic ,
  leapfrog_step (leapfrog ic n) = leapfrog (leapfrog_step ic) n.
Proof.
induction n. 
- auto.
- simpl. auto. 
Qed.

Lemma lfn_eq_lfstep:
  forall n ic ,
  leapfrog ic (S n) = leapfrog_step (leapfrog ic n).
Proof.
induction n.
- auto.
- intros. rewrite -> IHn. simpl. 
replace (leapfrog_step (leapfrog ic n)) with (leapfrog (leapfrog_step ic) n). destruct (leapfrog_step ic). 
all: symmetry; apply lfstep_lfn. 
Qed.


