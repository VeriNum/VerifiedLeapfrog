From Coq Require Import ZArith Reals Psatz.
From Coq Require Import Arith.Arith.
Require Import real_lemmas real_model.
From Coquelicot Require Import Coquelicot.
Set Bullet Behavior "Strict Subproofs". 

Require Import IntervalFlocq3.Tactic.

Open Scope R_scope.


(* the function f is k times differentiable in the interval [a,b] *)
Definition k_differentiable f k a b:=
  forall x, a <= x <= b -> forall n:nat, (n<=k)%nat ->  ex_derive_n f n x
.

Definition smooth_fun (f: R -> R): Prop :=
  forall (x: R) (n: nat),  
  ex_derive_n f n x
.

Definition dUdq x ω := ω ^ 2 * x.

(* the continuous system of equations for the simple harmonic oscillator *) 
Definition Harmonic_oscillator_system (p q : R -> R) (ω t0 : R) :=
  smooth_fun p /\ smooth_fun q /\
  forall t: R, 
  Derive_n q 1 t  = p t /\  
  Derive_n p 1 t  = - dUdq (q t) ω /\ 
  ∥( p t , ω * q t )∥ = ∥( p t0, ω * q t0)∥ .

Lemma HOS_implies_k_diff:
  forall p q ω t0 t h, 
  Harmonic_oscillator_system p q ω t0 -> 
  k_differentiable p 4 t (t + h) /\
  k_differentiable q 3 t (t + h) .
Proof.
intros.
unfold Harmonic_oscillator_system in H.
destruct H as (C & D & _).
split; unfold smooth_fun in *; 
unfold k_differentiable in *; intros.
-apply C.
-apply D.
Qed.

(* relating derivatives of the continuous system for future rewrites *)
Lemma Harm_sys_derive_eq p q ω t0: 
  Harmonic_oscillator_system p q ω t0 -> 
  forall t,
  Derive_n q 2 t  = Derive_n p 1 t /\
  Derive_n q 3 t  = - ω^2 * p t /\
  Derive_n p 2 t  = Derive_n q 3 t /\ 
  Derive_n p 3 t  = ω^4 * q t /\
  Derive_n p 4 t  = ω^4 * p t.
Proof.
unfold Harmonic_oscillator_system; intros.
destruct H as (_ & _ & H).
pose proof (H t) as (A & B & C).

assert (forall t, Derive_n q 2 t  = Derive_n p 1 t).
- intros; replace (Derive_n q 2 t1) with
(Derive_n (Derive_n q 1) 1 t1) by auto.
apply Derive_n_ext; intros.
specialize (H t2); apply H; auto.
-

assert ((Derive_n (fun y : R => - dUdq (q y) ω) 1 t) = 
(Derive_n (Derive_n q 1) 2 t )).
+  
replace (Derive_n (Derive_n q 1) 2 t) with
(Derive_n (Derive_n q 2) 1 t) by auto.
symmetry.
apply Derive_n_ext. intros.
specialize (H0 t1). rewrite H0.
apply H.
+ split; auto; split. 
* replace (Derive_n q 3 t) with 
(Derive_n (fun y : R => - dUdq (q y) ω) 1 t).
rewrite <- A.
rewrite <- Ropp_mult_distr_l.
rewrite <- Derive_n_scal_l.
rewrite Derive_n_opp.
unfold dUdq; auto.
* split.
-- 
unfold dUdq in *.
 replace (Derive_n q 3 t) with 
(Derive_n (fun y : R => - dUdq (q y) ω) 1 t).


         rewrite  Coquelicot.Derive_nS. 
    replace (Derive q) with (Derive_n q 1); auto.
unfold dUdq.
         apply Derive_n_ext. apply H.
-- split.
++  

unfold dUdq in *.
replace ( ω ^ 4 * q t) with
        ( -ω ^ 2 *(-ω ^ 2 * q t)) by nra.
rewrite <- Ropp_mult_distr_l.
rewrite <- Ropp_mult_distr_l.
rewrite <- B.

         replace (Derive_n p 3 t) with (Derive_n (Derive_n p 2) 1 t) by auto.
rewrite  Ropp_mult_distr_l.
          rewrite <- Derive_n_scal_l.
         apply Derive_n_ext. 
intros.
destruct (H t1) as ( J & K).
rewrite <- J.
         replace (Derive_n p 2 t1) with (Derive_n (Derive_n p 1) 1 t1) by auto.
          rewrite <- Derive_n_scal_l.
         apply Derive_n_ext.
intros. specialize (H t2).  
rewrite <-  Ropp_mult_distr_l.
apply H.
    ++  rewrite <- A.
        replace (Derive_n p 4 t) with
        (Derive_n (Derive_n p 3) 1 t) by auto.
        rewrite <- Derive_n_scal_l.
        apply Derive_n_ext.
        intros.
        replace (ω ^ 4 * q t1) with 
        (- ω ^ 2 * Derive_n q 2 t1).
        rewrite <- Derive_n_scal_l.
        rewrite  Coquelicot.Derive_nS. 
        apply Derive_n_ext.
        intros.
        replace (- ω ^ 2 * q t2) with
        ( Derive_n q 2 t2).
        rewrite  Coquelicot.Derive_nS.
         replace (Derive p) with (Derive_n p 1); auto.
        apply Derive_n_ext.
        intros.
        specialize (H t3).
        symmetry; replace (Derive q t3) with (Derive_n q 1 t3) by auto.
        apply H.
        specialize (H0 t2).
        rewrite H0.  
        specialize (H t2).
rewrite <-  Ropp_mult_distr_l.
unfold dUdq in H; apply H.
        specialize (H t1).
unfold dUdq in H.
replace (ω ^ 4 * q t1) with 
        ( -ω ^ 2 *(-ω ^ 2 * q t1)) by nra.
destruct H as ( _ & K & _).
repeat rewrite <-  Ropp_mult_distr_l.
rewrite <- K.
f_equal. f_equal.
apply H0.
Qed.

Close Scope R_scope. 