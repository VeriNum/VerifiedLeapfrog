From Coq Require Import ZArith Reals Psatz.
From Coq Require Import Arith.Arith.
From Coquelicot Require Import Coquelicot.


Open Scope R_scope.

(* Linear forcing function *)
Definition F (x :R) : R := (- 1 * x)%R.

(* Time step*)
Definition h := 1 / 32.

Definition leapfrog_stepR (ic : R * R) : R * R :=
  (let x  := fst ic in let v:= snd ic in 
  let x' := (x + h * v) + (h * h * F x) / 2 in
  let v' :=  v + (h*(F x + F x')/2) in 
  (x', v')).

Fixpoint leapfrogR ( ic : R * R ) (n : nat) : R * R:=
  match n with
  | 0%nat => ic
  | S n' =>
    let  ic' := leapfrog_stepR ic in
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

Lemma one_stepR_x:
  forall n: nat,
  forall ic : R * R,
  (fst (leapfrogR ic (S n))) - (fst (leapfrogR ic n)) = 
  h * (snd(leapfrogR ic n)) + 0.5 * h ^ 2 * (F (fst(leapfrogR ic n))).
Proof.
intros; induction n.
-unfold leapfrogR, leapfrog_stepR, fst, snd; nra.
-replace (leapfrogR ic (S(S n))) with (leapfrog_stepR (leapfrogR ic (S n))) by
(pose proof lfn_eq_lfstepR (S n) ic; auto).
unfold leapfrog_stepR. unfold fst at 1. field_simplify; nra.
Qed.

Lemma one_stepR_x_alt:
  forall ic : R * R,
  (fst (leapfrog_stepR ic) - (fst ic)) = 
  (- fst ic * h ^ 2 + 2 * h * snd ic) / 2.
Proof.
intros. destruct ic as [x v].
unfold leapfrogR, leapfrog_stepR, F, fst, snd; field_simplify; nra.
Qed.

Lemma one_stepR_x_alt2:
  forall ic1 ic2: R * R,
  (fst (leapfrog_stepR ic1) - fst (leapfrog_stepR ic2)) = 
  (1 - 0.5 * h ^ 2) * (fst ic1 - fst ic2) +  
    h *(snd ic1 - snd ic2).
Proof.
intros. destruct ic1 as [x1 v1]. destruct ic2 as [x2 v2].
unfold leapfrogR, leapfrog_stepR, F, fst, snd; field_simplify; nra.
Qed.

Lemma one_stepR_v_alt2:
  forall ic1 ic2: R * R,
  (snd (leapfrog_stepR ic1) - snd (leapfrog_stepR ic2)) = 
  (1 - 0.5 * h ^ 2) * (snd ic1 - snd ic2) -  
   0.5 * h * (2 - 0.5 * h^2) * (fst ic1 - fst ic2).
Proof.
intros. destruct ic1 as [x1 v1]. destruct ic2 as [x2 v2].
unfold leapfrogR, leapfrog_stepR, F, fst, snd; field_simplify; nra.
Qed.

Lemma one_stepR_xn:
  forall n : nat,
  forall ic1 ic2: R * R,
  (fst (leapfrogR ic1 (S n)) - fst (leapfrogR ic2 (S n))) = 
  (1 - 0.5 * h ^ 2) * (fst (leapfrogR ic1 n) - fst (leapfrogR ic2 n)) +  
   h *(snd (leapfrogR ic1 n) - snd (leapfrogR ic2 n)).
Proof.
intros. destruct ic1 as [x1 v1]. destruct ic2 as [x2 v2].
match goal with |- context [?a - ?b = ?c] => 
  let a' := constr:(fst (leapfrogR (x1, v1) n)) in
  let b' := constr:(fst (leapfrogR (x2, v2) n)) in
  replace (a - b) with  (a - a' - (b -b') + a' -b')
end.
repeat rewrite ?one_stepR_x; unfold F. all:  field_simplify; nra.
Qed.

Close Scope R_scope. 
