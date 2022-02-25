From Coq Require Import ZArith Reals Psatz.
From Coq Require Import Arith.Arith.
Require Import real_lemmas.
From Coquelicot Require Import Coquelicot.
Set Bullet Behavior "Strict Subproofs". 

Require Import Interval.Tactic.

Open Scope R_scope.

(* Linear forcing function *)
Definition F (x w :R) : R := (- w^2 * x)%R.


(* Time step*)
Definition h := 1 / 32.


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

(* assumes inputs of (p, w * q, w, n) *)
(* output q' will therefore be scaled appropriately *)
Fixpoint leapfrogR (p q w : R) (n : nat): R * R:=
  match n with
  | 0%nat => (p , q)
  | S n' =>
    let q' := q + h * w * p - 0.5 * h^2 * w^2 * q in
    let p' := p - 0.5 * h^2 * w^2 * p - 0.5 * h * w * (2 - 0.5 * h^2 * w^2) * q in 
  leapfrogR p' q' w n'
end.


Lemma one_stepR_q_alt2:
  forall p1 q1 p2 q2: R,
  forall w : R, 
   (snd (leapfrogR p1 (w * q1) w 1)  - snd (leapfrogR p2 (w * q2) w 1) ) = 
   (1 - 0.5 * w^2 * h ^ 2) * w * (q1-q2) +
    (h * w * (p1 - p2)).
Proof.
intros.
unfold leapfrogR, fst, snd. 
  field_simplify. nra.
Qed.


Lemma one_stepR_p_alt2:
  forall p1 q1 p2 q2: R,
  forall w : R, 
  (fst (leapfrogR p1 q1 w 1) - fst (leapfrogR  p2 q2 w 1) ) = 
  (1 - 0.5 * h ^ 2 * w^2) * (p1-p2) -  
   0.5 * h * w * (2 - 0.5 * h^2 * w^2) * (q1-q2).
Proof.
intros. 
unfold leapfrogR, fst, snd.
  field_simplify; nra.
Qed.

Lemma nsteps_lem:
  forall p q: R,
  forall w : R, 
  forall n: nat ,
(leapfrogR p q w (S n)) = (leapfrogR (fst (leapfrogR p q w n)) 
(snd ((leapfrogR p q w n))) w  1).
Proof.
intros. 
induction n.
+ simpl. f_equal.
+ simpl.  
Admitted.


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
