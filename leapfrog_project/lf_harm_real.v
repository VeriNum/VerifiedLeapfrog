From Coq Require Import ZArith Reals Psatz.
From Coq Require Import Arith.Arith.
Require Import real_lemmas.
From Coquelicot Require Import Coquelicot.
Set Bullet Behavior "Strict Subproofs". 

Require Import Interval.Tactic.

Open Scope R_scope.

(* Linear forcing function *)
Definition F (x :R) : R := (- x)%R.

(* Time step*)
Definition h := 1 / 32.

Definition leapfrog_stepR (ic : R * R) : R * R :=
  let x  := fst ic in let v:= snd ic in 
  let x' := (x + h * v) + ((1/2) * (h * h)) * F x in
  let v' :=  v +  (1/2 * h) * (F x + F x') in 
  (x', v').

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

Lemma one_stepR_v_alt:
  forall ic : R * R,
  (snd (leapfrog_stepR ic) - (snd ic)) = 
  (- 0.5 * h ^ 2) * (snd ic) -  
   0.5 * h * (2 - 0.5 * h^2) * (fst ic).
Proof.
intros. destruct ic as [x v].
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

Definition iternR (n:nat) (x v :R) :=  leapfrogR (x,v) n .

Lemma step_iternR : 
  forall n : nat,
  forall x v : R,
  (iternR (S n) x v) = leapfrog_stepR (iternR n x v).
Proof.
intros; unfold iternR; 
rewrite ?lfn_eq_lfstepR; 
congruence.
Qed.


(* start proofs of truncation error of the leapfrog method *)


(* We use the Taylor-Lagrange Theorem to determine the 
local truncation error of the leapfrog method. In particular,
the discrete solutions produced by the method differ from their
continous counterparts by (at most) the Taylor-Lagrange remainder
of order 3.*)
Theorem local_truncation_error:
forall x v: R -> R,
(forall n : nat,
forall t1 t2 t : R, t1 <= t <= t2 -> forall k : nat, (k <= S n)%nat -> ex_derive_n x k t) ->
(forall n : nat,
forall t1 t2 t : R, t1 <= t <= t2 -> forall k : nat, (k <= S n)%nat -> ex_derive_n v k t) ->
(forall t : R,
Derive_n x 1 t  = v t /\
Derive_n x 2 t = (fun y => F (x y)) t ) -> 
forall t0 : R,
exists t1 t2: R,
t0 < t1 < t0 + h /\
t0 < t2 < t0 + h /\
 (Rabs(x (t0 + h) - (fst(leapfrog_stepR (x t0,v t0)))) = 
    Rabs ((1 / INR (fact 3) * Derive_n x 3 t1) * h^3)) /\
 (Rabs(v (t0 + h) - (snd(leapfrog_stepR (x t0,v t0)))) = 
    Rabs((1 / INR (fact 3) * Derive_n v 3 t2 - (1/4) * (x t0)) * h^3)) . 
Proof.
intros.
assert (t0 < t0 + h) as LT by (unfold h; nra).
specialize (H 2%nat t0 (t0 +h)).
pose proof Taylor_Lagrange x 2 t0 (t0 + h) LT H. 
specialize (H0 2%nat t0 (t0 +h)).
pose proof Taylor_Lagrange v 2 t0 (t0 + h) LT H0.
destruct H2 as (t1 & A & B). 
destruct H3 as (t2 & C & D).
replace (t0 + h - t0) with h in * by nra.
pose proof (H1 t0) as HD.
exists t1, t2. 
repeat split; try apply A; try apply C.
+  
rewrite B. cbv [sum_f_R0].
destruct HD as (Hxd1 & Hxd2).
rewrite Hxd1, Hxd2. 
unfold Derive_n at 1.
repeat match goal with |-context[ (fact ?a)] =>
set (y:= fact a);
compute in y; subst y 
end.
repeat match goal with |-context[ (INR ?a)] =>
set (y:= INR a);
compute in y; subst y 
end.
unfold leapfrog_stepR, F, fst, snd.
match goal with |-context[ Rabs (?a) = Rabs (?b)] =>
field_simplify a;
field_simplify b
end.
f_equal.
nra.
+  
rewrite D. cbv [sum_f_R0].
replace (Derive_n v 2 t0) with 
(Derive_n (fun y : R => F (x y)) 1 t0). 
2: {
replace (Derive_n (fun y : R => F (x y)) 1 t0) with 
(Derive_n (Derive_n x 1) 2 t0 ).
(apply Derive_n_ext; apply H1).
replace (Derive_n (Derive_n x 1) 2 t0) with
(Derive_n (Derive_n x 2) 1 t0) by auto.
apply Derive_n_ext.
apply H1.
}

unfold F. rewrite Derive_n_opp.

replace (Derive_n v 1 t0) with 
(Derive_n x 2 t0) by (
replace (Derive_n x 2 t0) with
(Derive_n (Derive_n x 1) 1 t0) by auto;
apply Derive_n_ext; apply H1).

destruct HD as (Hxd1 & Hxd2).
rewrite Hxd2. rewrite Hxd1. unfold Derive_n at 1. 
repeat match goal with |-context[ (fact ?a)] =>
set (y:= fact a);
compute in y; subst y 
end.
repeat match goal with |-context[ (INR ?a)] =>
set (y:= INR a);
compute in y; subst y 
end.
unfold leapfrog_stepR, F, fst, snd.
match goal with |-context[ Rabs (?a) = Rabs (?b)] =>
field_simplify a;
field_simplify b
end.
f_equal.
nra.
Qed.


Lemma local_truncation_error_bounded: 
forall x v: R -> R,
(forall n : nat,
forall t1 t2 t : R, t1 <= t <= t2 -> forall k : nat, (k <= S n)%nat -> ex_derive_n x k t) ->
(forall n : nat,
forall t1 t2 t : R, t1 <= t <= t2 -> forall k : nat, (k <= S n)%nat -> ex_derive_n v k t) ->
(forall t : R,
-1 <= x t <= 1 /\
-1 <= v t <= 1 /\
Derive_n x 1 t  = v t /\
Derive_n x 2 t = (fun y => F (x y)) t ) -> 
forall t0 : R,
 (Rabs(x (t0 + h) - (fst(leapfrog_stepR (x t0,v t0)))) <= 
     ((1 / INR (fact 3)) * h^3)) /\
 (Rabs(v (t0 + h) - (snd(leapfrog_stepR (x t0,v t0)))) <= 
    ((1 / INR (fact 3) + (1/4)) * h^3)) . 
Proof.
intros.
assert (forall t : R,
Derive_n x 1 t = v t /\ Derive_n x 2 t = (fun y : R => F (x y)) t) as NLTE by
(intros; specialize (H1 t); apply H1). 
pose proof local_truncation_error x v H H0 NLTE t0 as LTE.
destruct LTE as (t1 & t2 & Ht1 & Ht2  & LTEx & LTEv).  


replace (Derive_n x 3 t1) with (- v t1) in LTEx. 
2: {
pose proof H1 t1 as H1t. destruct H1t as ( xbnd & vbnd & H1v & H1x).
rewrite <- H1v. 
rewrite <- Derive_n_opp.
replace (Derive_n x 3 t1) with 
(Derive_n (Derive_n x 2) 1 t1) by (unfold Derive_n; auto).
apply Derive_n_ext; intros. specialize (H1 t). destruct H1 as (Hvt & Hxt).
unfold F in Hxt. symmetry; apply Hxt. 
}


replace (Derive_n v 3 t2) with (x t2) in LTEv. 
2: {
pose proof H1 t2 as H1t. destruct H1t as ( xbnd & vbnd & H1v & H1x).
unfold F in H1x. pose proof Ropp_eq_compat (Derive_n x 2 t2) ( - x t2) H1x.
field_simplify in H2. rewrite <- H2.
rewrite <- Derive_n_opp.
replace (Derive_n v 3 t2) with 
(Derive_n (Derive_n v 1) 2 t2) by (unfold Derive_n; auto).
apply Derive_n_ext; intros. specialize (H1 t). 
destruct H1 as ( xbnd2 & vbnd2 & H1v2 & H1x2).
replace (Derive_n v 1 t) with (Derive_n x 2 t).
2:{ 
assert (forall t : R, Derive_n x 1 t = v t) as NLTEv by 
(intros tt;specialize (NLTE tt); apply NLTE). 
pose proof Derive_n_ext (Derive_n x 1) (v) 1 t NLTEv.
rewrite <- H1; subst; auto.
}
rewrite H1x2; unfold F; auto.
}

split.
+ rewrite LTEx.
repeat match goal with |-context[ (fact ?a)] =>
set (y:= fact a);
compute in y; subst y 
end. 
repeat match goal with |-context[ (INR ?a)] =>
set (y:= INR a);
compute in y; subst y 
end. 
rewrite Rmult_comm.
rewrite <- Rmult_assoc.
eapply Rle_trans.
apply Rabs_mult_le_l.
nra.
rewrite Rabs_Ropp.
specialize (H1 t1). destruct H1 as ( xbnd & vbnd & H1v & H1x).
assert (Rabs (v t1) <=1) as bndv by interval; apply bndv.
nra.
+rewrite LTEv.
repeat match goal with |-context[ (fact ?a)] =>
set (y:= fact a);
compute in y; subst y 
end. 
repeat match goal with |-context[ (INR ?a)] =>
set (y:= INR a);
compute in y; subst y 
end. 
rewrite Rmult_comm.
pose proof (H1 t2) as Ht2a. destruct Ht2a as ( xbnd & vbnd & H1v & H1x).
assert (-1 <= (x t2) <=1) as bndv by interval.
pose proof (H1 t0) as Ht2b. destruct Ht2b as ( xbnd2 & vbnd2 & H1v2 & H1x2).
assert (-1<= (x t0) <=1) as bndv2 by interval.
rewrite abs_mul; try nra.
rewrite Rmult_comm.
eapply Rmult_le_compat. 
apply Rabs_pos.
unfold h; nra.
eapply Rle_trans.
apply  Rabs_le_minus_mul; try nra; try interval.
simpl in bndv2; try interval.
nra.
apply Rle_refl.
Qed. 


Fixpoint delta_x (erx erv : R) (n : nat) { struct n } : R :=
  match n with 
  | 0%nat => erx
  | S n' => 
    (1 - 0.5 * h^2) * delta_x erx erv n' + h * delta_v erx erv n' + erx
  end
 with delta_v (erx erv : R) (m : nat) { struct m } : R :=
  match m with 
  | 0%nat => erv
  | S m' =>  
    (1 - 0.5 * h^2) * delta_v erx erv m' +  0.5 * h * (2 - 0.5 * h ^ 2) * delta_x  erx erv m' + erv
end 
.


Definition trunc_error_x := (1 / INR (fact 3)) * h^3.
Definition trunc_error_v := ((1 / INR (fact 3) + (1/4)) * h^3).


Lemma local_error_sum_aux :
forall x v: R -> R,
(forall n : nat,
forall t1 t2 t : R, t1 <= t <= t2 -> forall k : nat, (k <= S n)%nat -> ex_derive_n x k t) ->
(forall n : nat,
forall t1 t2 t : R, t1 <= t <= t2 -> forall k : nat, (k <= S n)%nat -> ex_derive_n v k t) ->
(forall t : R,
-1 <= x t <= 1 /\
-1 <= v t <= 1 /\
Derive_n x 1 t  = v t /\
Derive_n x 2 t = (fun y => F (x y)) t ) -> 
forall t0: R,
   Rabs(snd(leapfrog_stepR (x t0,v t0))) <=  
    trunc_error_v + Rabs(v (t0 + h)) /\
    Rabs(fst(leapfrog_stepR (x t0,v t0))) <= 
    trunc_error_x + Rabs(x (t0 + h))
 .
Proof.
intros.
pose proof local_truncation_error_bounded x v H H0 H1 t0.
split.
+ eapply Rcomplements.Rle_minus_l.
eapply Rle_trans.
apply Rabs_triang_inv.
unfold trunc_error_v. 
rewrite Rabs_minus_sym.
apply H2.
+ eapply Rcomplements.Rle_minus_l.
eapply Rle_trans.
apply Rabs_triang_inv.
unfold trunc_error_v. 
rewrite Rabs_minus_sym.
apply H2.
Qed.


Lemma local_truncation_error_sum :
forall x v: R -> R,
(forall n : nat,
forall t1 t2 t : R, t1 <= t <= t2 -> forall k : nat, (k <= S n)%nat -> ex_derive_n x k t) ->
(forall n : nat,
forall t1 t2 t : R, t1 <= t <= t2 -> forall k : nat, (k <= S n)%nat -> ex_derive_n v k t) ->
(forall t : R,
-1 <= x t <= 1 /\
-1 <= v t <= 1 /\
Derive_n x 1 t  = v t /\
Derive_n x 2 t = (fun y => F (x y)) t ) -> 
forall t0: R,
Rabs (v (t0 + h) + (snd(leapfrog_stepR (x t0,v t0)))) <=
    (trunc_error_v + 2) /\
Rabs (x (t0 + h) + (fst(leapfrog_stepR (x t0,v t0)))) <=
    (trunc_error_x + 2).
Proof.
intros.
pose proof local_error_sum_aux x v H H0 H1 t0.
split.
 + eapply Rle_trans.
apply Rabs_triang.
eapply Rle_trans.
apply Rplus_le_compat_l.
apply H2.
rewrite Rplus_comm.
eapply Rle_trans.
rewrite Rplus_assoc.
eapply Rplus_le_compat.
apply Rle_refl.
specialize (H1 (t0+h)). destruct H1 as (A & B & C & D).
match goal with |- context [?a <= ?b] =>
assert (a <= 2) as LE by interval with (i_prec 64);
apply LE
end.
nra.
+ eapply Rle_trans.
apply Rabs_triang.
eapply Rle_trans.
apply Rplus_le_compat_l.
apply H2.
rewrite Rplus_comm.
eapply Rle_trans.
rewrite Rplus_assoc.
eapply Rplus_le_compat.
apply Rle_refl.
specialize (H1 (t0+h)). destruct H1 as (A & B & C & D).
match goal with |- context [?a <= ?b] =>
assert (a <= 2) as LE by interval with (i_prec 64);
apply LE
end.
nra.
Qed.


Theorem global_truncation_error : 
forall x v: R -> R,
(forall n : nat,
forall t1 t2 t : R, t1 <= t <= t2 -> forall k : nat, (k <= S n)%nat -> ex_derive_n x k t) ->
(forall n : nat,
forall t1 t2 t : R, t1 <= t <= t2 -> forall k : nat, (k <= S n)%nat -> ex_derive_n v k t) ->
(forall t : R,
-1 <= x t <= 1 /\
-1 <= v t <= 1 /\
Derive_n x 1 t  = v t /\
Derive_n x 2 t = (fun y => F (x y)) t ) -> 
forall n : nat, 
forall t0: R,
 (Rabs(x (t0 + INR (S n) * h) - (fst(iternR (S n) (x t0) (v t0))))) <= 
    (delta_x trunc_error_x trunc_error_v n) /\
 (Rabs(v (t0 + INR (S n) * h) - (snd(iternR (S n) (x t0) (v t0))))) <= 
    (delta_v trunc_error_x trunc_error_v n).
Proof.
intros.
induction n.
+ simpl.
pose proof local_truncation_error_bounded x v H H0 H1 t0.
rewrite ?Rmult_1_l. unfold trunc_error_x, trunc_error_v.
apply H2.
+  set (m:= S n ).
rewrite ?step_iternR.
unfold m; clear m. 
rewrite ?S_INR. 
replace ((t0 + (INR n + 1 + 1) * h)) with
(t0 + (INR n+1)*h + h) by nra.
set (phi1:= leapfrog_stepR 
  ( x (t0 + (INR n+1)*h ), v (t0 + (INR n+1)*h ))).
set (phi2:=  leapfrog_stepR (iternR (S n) (x t0) (v t0))).
split.
-
match goal with |- context [Rabs(?x1 -?x3) <= ?c] =>
  replace (Rabs(x1 - x3)) with (Rabs(x1 - fst(phi1) + fst(phi1) - x3)) by
  (field_simplify (x1 - fst(phi1) + fst(phi1) - x3); nra);
  set (aa:= (x1-fst(phi1)));
  replace (Rminus (aa + fst(phi1)) x3) with (Rplus aa (fst(phi1)- x3)) by nra;
  set (bb:= (fst(phi1)-x3));
  try apply Rabs_triang_aux; unfold aa; unfold bb; clear aa bb
end.
eapply Rle_trans.
eapply Rplus_le_compat_r.
pose proof local_truncation_error_bounded x v H H0 H1 (t0 + (INR n + 1) * h).
unfold phi1.
destruct H2 as (A & B).
apply A.
eapply Rle_trans.
eapply Rplus_le_compat_l.
unfold phi1, phi2.
match goal with |- context [Rabs(?a - ?b)] =>
set (yy:= a - b)
end.
rewrite ?S_INR in IHn.
destruct (iternR (S n) (x t0) (v t0)) as (xsn,vsn).
subst yy.
rewrite one_stepR_x_alt2.
unfold fst, snd.
unfold fst, snd in IHn.
eapply Rle_trans.
eapply Rabs_triang.
eapply Rle_trans.
eapply Rplus_le_compat_r.
rewrite abs_mul.
eapply Rmult_le_compat_l; try (unfold h; nra).
apply IHn.
unfold h; nra.
eapply Rle_trans.
eapply Rplus_le_compat_l.
rewrite abs_mul.
eapply Rmult_le_compat_l; try (unfold h; nra).
apply IHn.
unfold h; nra.
apply Rle_refl.
unfold delta_x at 2.
fold delta_x. fold delta_v.
fold trunc_error_x; nra.
-
match goal with |- context [Rabs(?x1 -?x3) <= ?c] =>
  replace (Rabs(x1 - x3)) with (Rabs(x1 - snd(phi1) + snd(phi1) - x3)) by
  (field_simplify (x1 - snd(phi1) + snd(phi1) - x3); nra);
  set (aa:= (x1-snd(phi1)));
  replace (Rminus (aa + snd(phi1)) x3) with (Rplus aa (snd(phi1)- x3)) by nra;
  set (bb:= (snd(phi1)-x3));
  try apply Rabs_triang_aux; unfold aa; unfold bb; clear aa bb
end.
eapply Rle_trans.
eapply Rplus_le_compat_r.
pose proof local_truncation_error_bounded x v H H0 H1 (t0 + (INR n + 1) * h).
unfold phi1.
destruct H2 as (A & B).
apply B.
eapply Rle_trans.
eapply Rplus_le_compat_l.
unfold phi1, phi2.
match goal with |- context [Rabs(?a - ?b)] =>
set (yy:= a - b)
end.
rewrite ?S_INR in IHn.
destruct (iternR (S n) (x t0) (v t0)) as (xsn,vsn).
subst yy.
rewrite one_stepR_v_alt2.
unfold fst, snd.
unfold fst, snd in IHn.
eapply Rle_trans.
eapply Rabs_triang.
eapply Rle_trans.
eapply Rplus_le_compat_r.
rewrite abs_mul.
eapply Rmult_le_compat_l; try (unfold h; nra).
apply IHn.
unfold h; nra.
eapply Rle_trans.
eapply Rplus_le_compat_l.
rewrite Rabs_Ropp.
rewrite abs_mul.
eapply Rmult_le_compat_l; try (unfold h; nra).
apply IHn.
unfold h; nra.
apply Rle_refl.
unfold delta_v at 2.
fold delta_x. fold delta_v.
fold trunc_error_v; nra.
Qed.

(* start proofs of energy error of the leapfrog method *)


Definition H_osc (x v :R) : R := x^ 2 + v^2. 

Theorem local_energy_error : 
forall x v: R -> R,
(forall n : nat,
forall t1 t2 t : R, t1 <= t <= t2 -> forall k : nat, (k <= S n)%nat -> ex_derive_n x k t) ->
(forall n : nat,
forall t1 t2 t : R, t1 <= t <= t2 -> forall k : nat, (k <= S n)%nat -> ex_derive_n v k t) ->
(forall t : R,
-1 <= x t <= 1 /\
-1 <= v t <= 1 /\
Derive_n x 1 t  = v t /\
Derive_n x 2 t = (fun y => F (x y)) t ) -> 
forall t0: R,
  let xs := fst (leapfrog_stepR (x t0,v t0)) in
  let vs := snd (leapfrog_stepR (x t0,v t0)) in 
  let xr := x (t0 + h) in
  let vr := v (t0 + h) in 
    Rabs (H_osc xr vr - H_osc xs vs) <= 
(trunc_error_x^2 + trunc_error_v^2) + 2 * (trunc_error_v + trunc_error_x).
Proof.
intros.
unfold H_osc.
eapply Rle_trans.
+ apply Rabs_triang_aux4.
+ 
pose proof local_truncation_error_sum x v H H0 H1 t0. 
pose proof local_truncation_error_bounded x v H H0 H1 t0.
unfold xr, vr, xs, vs in *.
eapply Rle_trans.
apply Rplus_le_compat_r.
apply Rmult_le_compat_r.
apply Rabs_pos.
apply H2.
eapply Rle_trans.
apply Rplus_le_compat_r.
apply Rmult_le_compat_l.
unfold trunc_error_x, h. 
repeat match goal with|-context[ (fact ?a)] =>
set (y:= fact a);
compute in y; subst y 
end. 
repeat match goal with |-context[ (INR ?a)] =>
set (y:= INR a);
compute in y; subst y 
end. nra.
apply H3.
eapply Rle_trans.
apply Rplus_le_compat_l.
apply Rmult_le_compat_l.
apply Rabs_pos.
apply H3.
eapply Rle_trans.
apply Rplus_le_compat_l.
apply Rmult_le_compat_r.
unfold h. 
repeat match goal with|-context[ (fact ?a)] =>
set (y:= fact a);
compute in y; subst y 
end. 
repeat match goal with |-context[ (INR ?a)] =>
set (y:= INR a);
compute in y; subst y 
end. nra.
apply H2.
fold trunc_error_x.
fold trunc_error_v.
nra.
Qed.

Lemma global_truncation_error_sum_aux :
forall x v: R -> R,
(forall n : nat,
forall t1 t2 t : R, t1 <= t <= t2 -> forall k : nat, (k <= S n)%nat -> ex_derive_n x k t) ->
(forall n : nat,
forall t1 t2 t : R, t1 <= t <= t2 -> forall k : nat, (k <= S n)%nat -> ex_derive_n v k t) ->
(forall t : R,
-1 <= x t <= 1 /\
-1 <= v t <= 1 /\
Derive_n x 1 t  = v t /\
Derive_n x 2 t = (fun y => F (x y)) t ) -> 
forall n: nat,
forall t0: R,
   Rabs (fst(iternR (S n) (x t0) (v t0))) <= 
    (delta_x trunc_error_x trunc_error_v n) + Rabs(x (t0 + INR (S n) * h) ) /\
 Rabs (snd(iternR (S n) (x t0) (v t0))) <= 
    (delta_v trunc_error_x trunc_error_v n) + Rabs(v (t0 + INR (S n) * h) ).
Proof.
intros.
pose proof global_truncation_error x v H H0 H1 n t0 as GE.
split.
+ eapply Rcomplements.Rle_minus_l;
eapply Rle_trans.
apply Rabs_triang_inv. rewrite Rabs_minus_sym.
apply GE.
+ eapply Rcomplements.Rle_minus_l;
eapply Rle_trans.
apply Rabs_triang_inv. rewrite Rabs_minus_sym.
apply GE.
Qed.

Lemma global_truncation_error_sum :
forall x v: R -> R,
(forall n : nat,
forall t1 t2 t : R, t1 <= t <= t2 -> forall k : nat, (k <= S n)%nat -> ex_derive_n x k t) ->
(forall n : nat,
forall t1 t2 t : R, t1 <= t <= t2 -> forall k : nat, (k <= S n)%nat -> ex_derive_n v k t) ->
(forall t : R,
-1 <= x t <= 1 /\
-1 <= v t <= 1 /\
Derive_n x 1 t  = v t /\
Derive_n x 2 t = (fun y => F (x y)) t ) -> 
forall n: nat,
forall t0: R,
Rabs ( x (t0 + INR (S n) * h) +  (fst(iternR (S n) (x t0) (v t0)))) <= 
    ((delta_x trunc_error_x trunc_error_v n) + 2) /\
Rabs ( v (t0 + INR (S n) * h) +  (snd(iternR (S n) (x t0) (v t0)))) <= 
    ((delta_v trunc_error_x trunc_error_v n) + 2).
Proof.
intros.
pose proof global_truncation_error_sum_aux x v H H0 H1 n t0.
split.
+ eapply Rle_trans.
apply Rabs_triang.
eapply Rle_trans.
apply Rplus_le_compat_l.
apply H2.
rewrite Rplus_comm.
rewrite Rplus_assoc.
eapply Rle_trans.
eapply Rplus_le_compat.
apply Rle_refl.
specialize (H1 ((t0 + INR (S n) * h))). destruct H1 as (A & B & C & D).
match goal with |- context [?a <= ?b] =>
assert (a <= 2) as LE by interval with (i_prec 64);
apply LE
end.
nra.
+ eapply Rle_trans.
apply Rabs_triang.
eapply Rle_trans.
apply Rplus_le_compat_l.
apply H2.
rewrite Rplus_comm.
rewrite Rplus_assoc.
eapply Rle_trans.
eapply Rplus_le_compat.
apply Rle_refl.
specialize (H1 ((t0 + INR (S n) * h))). destruct H1 as (A & B & C & D).
match goal with |- context [?a <= ?b] =>
assert (a <= 2) as LE by interval with (i_prec 64);
apply LE
end.
nra.
Qed.

Lemma disc_deltas_pos (n : nat) : 
  0 <= delta_v trunc_error_x trunc_error_v n /\  0 <= delta_x trunc_error_x trunc_error_v n.
Proof.
induction n.
+ split.
-- unfold delta_v. unfold trunc_error_v. 
repeat match goal with|-context[ (fact ?a)] =>
set (y:= fact a);
compute in y; subst y 
end. 
repeat match goal with |-context[ (INR ?a)] =>
set (y:= INR a);
compute in y; subst y 
end; unfold h.
nra.
-- unfold delta_x. unfold trunc_error_x. 
repeat match goal with|-context[ (fact ?a)] =>
set (y:= fact a);
compute in y; subst y 
end. 
repeat match goal with |-context[ (INR ?a)] =>
set (y:= INR a);
compute in y; subst y 
end; unfold h.
nra.
+ destruct IHn as (IHnv & IHnx). split.
-- unfold delta_v.  fold delta_v. fold delta_x.
repeat apply Rle_plus; try  (unfold error_v; nra);
apply Rle_mult; try (unfold h; nra).
repeat match goal with|-context[ (fact ?a)] =>
set (y:= fact a);
compute in y; subst y 
end. 
repeat match goal with |-context[ (INR ?a)] =>
set (y:= INR a);
compute in y; subst y 
end; unfold h.
nra.
-- unfold delta_x.  fold delta_x. fold delta_v.
repeat apply Rle_plus; try  (unfold error_x; nra);
apply Rle_mult; try (unfold h; nra);
repeat match goal with|-context[ (fact ?a)] =>
set (y:= fact a);
compute in y; subst y 
end. 
repeat match goal with |-context[ (INR ?a)] =>
set (y:= INR a);
compute in y; subst y 
end; unfold h.
nra.
Qed.

Theorem global_energy_error : 
forall x v: R -> R,
(forall n : nat,
forall t1 t2 t : R, t1 <= t <= t2 -> forall k : nat, (k <= S n)%nat -> ex_derive_n x k t) ->
(forall n : nat,
forall t1 t2 t : R, t1 <= t <= t2 -> forall k : nat, (k <= S n)%nat -> ex_derive_n v k t) ->
(forall t : R,
-1 <= x t <= 1 /\
-1 <= v t <= 1 /\
Derive_n x 1 t  = v t /\
Derive_n x 2 t = (fun y => F (x y)) t ) -> 
forall n: nat, 
forall t0: R,
  let xs :=  fst(iternR (S n) (x t0) (v t0)) in
  let vs :=  snd(iternR (S n) (x t0) (v t0)) in 
  let xr := x (t0 + INR (S n) * h) in
  let vr := v (t0 + INR (S n) * h) in 
    Rabs (H_osc xr vr - H_osc xs vs) <= 
    ((2 + delta_x trunc_error_x trunc_error_v n) * (delta_x trunc_error_x trunc_error_v n) + 
      (2 + delta_v trunc_error_x trunc_error_v n) * (delta_v trunc_error_x trunc_error_v n)).
Proof.
intros.

unfold H_osc.
eapply Rle_trans.
eapply Rabs_triang_aux4.

pose proof (global_truncation_error_sum x v H H0 H1  n t0) as GEC. 
pose proof (global_truncation_error x v H H0 H1  n t0) as GE.

unfold xr, vr, xs ,vs.

eapply  Rle_trans.
eapply Rplus_le_compat_l.
eapply Rmult_le_compat_r. apply Rabs_pos.
apply GEC.

eapply  Rle_trans.
eapply Rplus_le_compat_l.
eapply Rmult_le_compat_l. 
eapply Rplus_le_le_0_compat. 
apply disc_deltas_pos.
nra.
apply GE.

eapply  Rle_trans.
eapply Rplus_le_compat_r.
eapply Rmult_le_compat_l. apply Rabs_pos.
apply GE.


eapply  Rle_trans.
eapply Rplus_le_compat_r.
eapply Rmult_le_compat_r. 
apply disc_deltas_pos.
apply GEC.

nra.
Qed.


(* start proof of symplecticity of the leapfrog method *)


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
repeat match goal with |- context [Derive (?f) ?var] =>
auto_derive_fun f; unfold F;
assert True as TR by auto;
let H := fresh "H" in
          intro H;
let H1 := fresh "H" in
pose proof (H var TR) as H1; clear TR; clear H;
apply is_derive_unique in H1; field_simplify in H1; rewrite H1; clear H1
end.
unfold h.
field_simplify.
nra. 
Qed.


Close Scope R_scope. 
