From Flocq Require Core Binary.
Import Defs Raux FLT Generic_fmt Binary Ulp.
Require Import Psatz.
Require Import Recdef.

Require compcert.lib.Floats.

Section LeapfrogDefs.

Definition float := Floats.float32.

Definition binop_nan : forall x y : float, {x: float | is_nan _ _ x = true}
    := Floats.Float32.binop_nan.

Definition ms :=  (* mantissa bits *)
     ltac:(let t := eval compute in float in 
            match t with binary_float ?m ?e => let x := constr:(m) in apply x end).
Definition es :=  (* maximum exponent *)
    ltac:(let t := eval compute in float in 
            match t with binary_float ?m ?e => let x := constr:(e) in apply x end).

Definition float_of_Z : Z -> float := 
     IEEE754_extra.BofZ ms es eq_refl eq_refl.

Definition zero:= float_of_Z 0.

Variable F : float -> float.
Variable h : float.

Definition float_plus: float -> float -> float :=
   Bplus ms es eq_refl eq_refl binop_nan mode_NE.

Definition float_mult: float -> float -> float :=
   Bmult ms es eq_refl eq_refl binop_nan mode_NE.

Definition float_div: float -> float -> float :=
   Bdiv ms es eq_refl eq_refl binop_nan mode_NE.

Fixpoint float_pow (r:float) (n:nat) : float :=
  match n with
    | O => float_of_Z 1
    | S n => float_mult r (float_pow r n)
  end.

Definition leapfrog_step ( ic : float * float) : float * float :=
  let x  := fst ic in let v:= snd ic in 
  let x1 := float_plus x (float_mult h v) in 
  let x2 := float_div (float_mult (float_pow h 2) (F x)) (float_of_Z 2) in
  let x' := float_plus x1 x2 in
  let v1 := float_plus (F x) (F x') in
  let v' := float_plus v (float_div (float_mult h v1) (float_of_Z 2)) in 
  (x', v').

Fixpoint leapfrog ( ic : float * float) (n : nat) : float * float:=
  match n with
  | 0 => ic
  | S n' =>
    let  ic' := leapfrog_step ic in
    leapfrog ic' n'
  end.

Lemma leapfrog_correct_step1  (ic : float * float) :
  leapfrog ic 1 = leapfrog_step ic.
Proof.
auto.
Qed.

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

Lemma leapfrog_zero_ic :
  forall n ic ,
  ic = (zero,zero) ->
  leapfrog ic n = (zero, zero).
Proof.
intros. 
induction n.
- auto.
- assert (H1: leapfrog ic 0 = (zero, zero)) by (auto). 
assert (H2: leapfrog ic (S n) = leapfrog_step (leapfrog ic n)) by (apply lfn_eq_lfstep). 
assert (leapfrog ic (S n) = leapfrog ic n). auto. 
rewrite -> H1. rewrite -> IHn. unfold leapfrog_step, zero fst, snd. lia. 

End LeapfrogDefs.

Opaque leapfrog_step.


Lemma leapfrog_zero_IC (F: float -> float) (h x v: float) (n : nat) :
  x = zero  -> v = zero ->
  leapfrog F h x v n = (zero, zero).
Proof.
intros. 
induction n as [| n' IHn'].
- simple subst. auto.
- assert (H1: leapfrog F h x v (S n') = leapfrog_step F h (fst (leapfrog F h x v n')) (snd (leapfrog F h x v n'))).
unfold leapfrog. simpl. auto.
Qed.

