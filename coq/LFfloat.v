From Flocq Require Core Binary.
Import Defs Raux Binary.

Require Import Recdef.
Require compcert.lib.Floats.

Section LeapfrogDefs.

Definition float := Floats.float32.

Definition binop_nan : forall x y : float, {x: float | is_nan _ _ x = true}
    := Floats.Float32.binop_nan.

(*Start Defs. attributed to Appel, Bertot https://github.com/cverified/cbench-vst/blob/master/sqrt/float_lemmas.v*)
Definition ms :=  (* mantissa bits *)
     ltac:(let t := eval compute in float in 
            match t with binary_float ?m ?e => let x := constr:(m) in apply x end).
Definition es :=  (* maximum exponent *)
    ltac:(let t := eval compute in float in 
            match t with binary_float ?m ?e => let x := constr:(e) in apply x end).

Definition float_of_Z : Z -> float := 
     IEEE754_extra.BofZ ms es eq_refl eq_refl.
(*End Defs. attributed to Appel, Bertot*)

Definition zero:= float_of_Z 0.

Variable F : float -> float.
Variable h : float.

(*Start Defs. attributed to Appel, Bertot https://github.com/cverified/cbench-vst/blob/master/sqrt/float_lemmas.v*)
Definition float_plus: float -> float -> float :=
   Bplus ms es eq_refl eq_refl binop_nan mode_NE.

Definition float_mult: float -> float -> float :=
   Bmult ms es eq_refl eq_refl binop_nan mode_NE.

Definition float_div: float -> float -> float :=
   Bdiv ms es eq_refl eq_refl binop_nan mode_NE.
(*End Defs. attributed to Appel, Bertot*)

Fixpoint float_pow (f : float) (n : nat) : float :=
  match n with
    | O => float_of_Z 1
    | S n => float_mult f (float_pow f n)
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

End LeapfrogDefs.


