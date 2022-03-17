From Coq Require Import ZArith Reals Psatz.
From Coq Require Import Arith.Arith.
Require Import real_lemmas.
From Coquelicot Require Import Coquelicot.
Set Bullet Behavior "Strict Subproofs". 

Require Import Interval.Tactic.

Open Scope R_scope.


(* Time step*)
Definition h := 1 / 32.


Definition leapfrog_stepR (ic : R * R ): R * R :=
  let q := snd ic in let p := fst ic in 
  let q' := q + h * p - 0.5 * h^2  * q in 
  let p' := p - 0.5 * h^2 * p - 0.5 * h *  (2 - 0.5 * h^2 ) * q in 
  (p', q').

(* assumes inputs of (p, w * q, w, n) *)
(* output q' will therefore be scaled appropriately *)
Fixpoint leapfrogR  (ic : R * R) (n : nat): R * R:=
  match n with
  | 0%nat => ic
  | S n' =>
    let ic' := leapfrog_stepR ic in
  leapfrogR ic' n'
end.

Lemma lfstepR_lfn:
  forall n ic ,
  leapfrog_stepR (leapfrogR ic n) = leapfrogR (leapfrog_stepR ic) n.
Proof.
induction n. 
- auto.
- simpl. auto. 
Qed.

Lemma lfn_eq_lfstepR:
  forall n ic ,
  leapfrogR ic (S n) = leapfrog_stepR (leapfrogR ic n).
Proof.
induction n.
- auto.
- intros. rewrite -> IHn. simpl. 
replace (leapfrog_stepR (leapfrogR ic n)) with (leapfrogR (leapfrog_stepR ic) n). destruct (leapfrog_stepR ic). 
all: symmetry; apply lfstepR_lfn. 
Qed.



Lemma one_stepR_p_alt2:
  forall ic1 ic2: R * R,
  (fst (leapfrog_stepR ic1) - fst (leapfrog_stepR ic2)) = 
  (1 - 0.5 * h ^ 2) * (fst ic1 - fst ic2) -  
   0.5 * h * (2 - 0.5 * h^2) * (snd ic1 - snd ic2).
Proof.
intros. destruct ic1 as [x1 v1]. destruct ic2 as [x2 v2].
unfold leapfrog_stepR, fst, snd; field_simplify. nra.
Qed.


Lemma one_stepR_q_alt2:
  forall ic1 ic2: R * R,
  (snd (leapfrog_stepR ic1) - snd (leapfrog_stepR ic2)) = 
  (1 - 0.5 * h ^ 2) * (snd ic1 - snd ic2) +   h *(fst ic1 - fst ic2).
Proof.
intros. destruct ic1 as [x1 v1]. destruct ic2 as [x2 v2].
unfold leapfrog_stepR, fst, snd; field_simplify; nra.
Qed.


Definition iternR (ic :R * R) (n:nat) :=  leapfrogR ic n .

Lemma step_iternR : 
  forall n : nat,
  forall x v : R,
  (iternR (x,v) (S n)) = leapfrog_stepR (iternR (x,v) n).
Proof.
intros.
rewrite lfn_eq_lfstepR.
unfold iternR. 
congruence.
Qed.

Lemma leapfrog_minus_args :
forall ic1 ic2 : (R * R),
Rprod_minus (leapfrog_stepR ic1) (leapfrog_stepR ic2) = leapfrog_stepR (Rprod_minus ic1 ic2).
Proof.
intros.
destruct ic1; destruct ic2.
unfold leapfrog_stepR, Rprod_minus, fst ,snd.
f_equal; nra.
Qed.

Lemma leapfrog_plus_args :
forall ic1 ic2 : (R * R),
Rprod_plus (leapfrog_stepR ic1) (leapfrog_stepR ic2) = leapfrog_stepR (Rprod_plus ic1 ic2).
Proof.
intros.
destruct ic1; destruct ic2.
unfold leapfrog_stepR, Rprod_plus, fst ,snd.
f_equal; nra.
Qed.

(* Linear forcing function *)
Definition F (x w :R) : R := (- w^2 * x)%R.


Definition leapfrog_stepR' (ic : R * R) : R * R :=
  let x  := fst ic in let v:= snd ic in 
  let x' := (x + h * v) + 0.5 * h^2 * F x 1 in
  let v' :=  v +  0.5 * h * (F x 1 + F x' 1) in 
  (x', v').

Fixpoint leapfrogR' (x v : R) (n : nat): R * R:=
  match n with
  | 0%nat => (x,v)
  | S n' =>
    let x' := (x + h * v) + 0.5 * h^2 * F x 1 in
    let v' :=  v +  0.5 * h * (F x 1 + F x' 1) in 
    leapfrogR' x' v' n'
end.


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
