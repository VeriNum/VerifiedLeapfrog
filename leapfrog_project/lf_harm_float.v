From Flocq Require Import Binary Bits Core.
From compcert.lib Require Import IEEE754_extra Coqlib Floats Zbits Integers.

Definition float32_of_Z : Z -> float32 := BofZ 24 128 eq_refl eq_refl.
Definition float_of_Z : Z -> float := BofZ 53 1024 eq_refl eq_refl.

(* Linear forcing function *)
Definition F (x : float32) : float32 := 
   Float32.mul (Float32.neg (float32_of_Z 1)) x.

(* Time step*)
Definition h := Float32.div (float32_of_Z 1) (float32_of_Z 32).

(* Single step of the integrator*)
Definition leapfrog_step ( ic : float32 * float32) : float32 * float32 :=
  let x  := fst ic in let v:= snd ic in 
  let x1 := Float32.add x (Float32.mul h v) in 
  let x2 := Float32.div (Float32.mul (Float32.mul h h) (F x)) (float32_of_Z 2)  in
  let x' := Float32.add x1 x2 in
  let v1 := Float32.add (F x) (F x') in
  let v' := Float32.add v (Float32.div (Float32.mul h v1) (float32_of_Z 2)) in 
  (x', v').

(* Main *)
Fixpoint leapfrog ( ic : float32 * float32) (n : nat) : float32 * float32:=
  match n with
  | 0%nat => ic
  | S n' =>
    let  ic' := leapfrog_step ic in
    leapfrog ic' n'
  end.

Lemma lfstep_lf_comp:
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
all: symmetry; apply lfstep_lf_comp. 
Qed.







