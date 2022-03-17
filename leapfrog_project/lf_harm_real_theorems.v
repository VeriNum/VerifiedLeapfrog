From Coq Require Import ZArith Reals Psatz.
From Coq Require Import Arith.Arith.
Require Import real_lemmas lf_harm_real.
From Coquelicot Require Import Coquelicot.
Set Bullet Behavior "Strict Subproofs". 

Require Import Interval.Tactic.

Open Scope R_scope.

(* This file contains the real properties proofs for the 
leapfrog method *)




(* the function f is k times differentiable in the interval [a,b] *)
Definition k_differentiable f k a b:=
forall x,
a<= x <= b -> forall n:nat, (n<=k)%nat ->  ex_derive_n f n x.


Definition Harmonic_osc_system p q w t0:=
forall t,
Derive_n q 1 t  = p t /\
Derive_n q 2 t = (fun y => F (q y) w) t /\
Rprod_norm ( p t , w * q t ) <= Rprod_norm( p t0, w * q t0)
.


Lemma Harm_sys_derive_eq p q w t0: 
Harmonic_osc_system p q w t0-> 
forall t,
Derive_n q 3 t  = - w ^2 * p t /\
Derive_n p 2 t  = Derive_n q 3 t /\ 
Derive_n p 3 t  = w ^4 * q t /\
Derive_n p 4 t  = w^4 * p t.
Proof.
unfold Harmonic_osc_system .
intros.
pose proof (H t) as (A & B & C).
split.
+ replace (Derive_n q 3 t) with 
(Derive_n (fun y : R => F (q y) w) 1 t).
2: {
replace (Derive_n (fun y : R => F (q y) w) 1 t) with 
(Derive_n (Derive_n q 1) 2 t ).  
symmetry.
rewrite  Coquelicot.Derive_nS.
replace (Derive_n q 1) with (Derive q); auto.
replace (Derive_n (Derive_n q 1) 2 t) with
(Derive_n (Derive_n q 2) 1 t) by auto.
apply Derive_n_ext.
apply H.
}
unfold F. 
rewrite Derive_n_scal_l.
rewrite A; auto.
+ split. 
++ symmetry. 
rewrite  Coquelicot.Derive_nS.
replace (Derive q) with (Derive_n q 1); auto.
apply Derive_n_ext.
apply H.
++ split.
+++ unfold F in B. 
assert (Derive_n q 4 t =  - w^2 *  Derive_n q 2 t).
rewrite  Coquelicot.Derive_nS. 
rewrite  Coquelicot.Derive_nS.
rewrite <- Derive_n_scal_l.
apply Derive_n_ext. apply H.
rewrite B in H0; field_simplify in H0.
rewrite <- H0.
replace (Derive_n q 4 t) with (Derive_n (Derive_n q 1) 3 t); auto.
symmetry.
apply Derive_n_ext. apply H.
+++
rewrite <- A.
replace (Derive_n p 4 t) with
(Derive_n (Derive_n p 3) 1 t) by auto.
rewrite <- Derive_n_scal_l.
apply Derive_n_ext.
intros.
replace (w ^ 4 * q t1) with 
(- w ^ 2 * Derive_n q 2 t1).
rewrite <- Derive_n_scal_l.
rewrite  Coquelicot.Derive_nS. 
apply Derive_n_ext.
intros.
replace (- w ^ 2 * q t2) with
( Derive_n q 2 t2).
rewrite  Coquelicot.Derive_nS.
 replace (Derive p) with (Derive_n p 1); auto.
apply Derive_n_ext.
intros.
specialize (H t3).
symmetry; replace (Derive q t3) with (Derive_n q 1 t3) by auto.
apply H.
specialize (H t2).
destruct H as (_ & B1 & _).
rewrite B1. unfold F; auto.
specialize (H t1).
destruct H as (_ & B1 & _).
rewrite B1. unfold F; nra.
Qed.

(*
Lemma Harm_sys_norm_bound p q:
forall a b t1 t2 t3,
forall w,
0 < w ->
Harmonic_osc_system p q w-> 
0 <= a ->
0 <= b ->
Rprod_norm (a * Derive_n p 3 t2 - b* w ^ 4 * q(t3), a * w * Derive_n q 3 t1 ) <= 
sqrt 5 * (Rmax a b) * (w ^ 3) * Rprod_norm( p (0), w * q(0)).
Proof.
intros.
unfold Harmonic_osc_system in H.
pose proof Harm_sys_derive_eq p q w H0 t1 as (A & _ & _).
pose proof Harm_sys_derive_eq p q w H0 t2 as (_ & _ & C2).
rewrite A, C2. clear A C2.
pose proof (H0 t1) as A1; destruct A1 as (_ & _ &C).
pose proof (H0 t2) as A1; destruct A1 as (_ & _ &C2).
specialize (H0 t3). destruct H0 as (_ & _ & C3).
unfold Rprod_norm, fst, snd in *.
apply sqrt_le_0 in C, C2, C3; try nra.
assert (p t1 ^ 2  <= w ^2 * q 0 ^ 2 + p 0 ^ 2) by nra; 
  clear C.
assert (w ^2 * q t2 ^ 2 <= w ^2 * q 0 ^ 2 + p 0 ^ 2) by nra; 
  clear C2.
assert (w ^2 * q t3 ^ 2 <= w ^2 * q 0 ^ 2 + p 0 ^ 2) by nra; 
  clear C3.
replace ((a * (- w ^ 2 * p t1)) ^ 2) with 
  (a ^2 * w ^4 * (p t1) ^ 2)  by nra.
replace ( a * (w ^ 4 * q t2)) with ( a * w^3 * (w * q t2)) by nra.
replace (b * w ^ 4 * q t3) with (b * w^3 * (w * q t3)) by nra.
replace (a * w * (- w ^ 2 * p t1)) with ( - a * w ^3 * p t1) by nra.
replace ((- a * w ^ 3 * p t1)^ 2) with (a ^2 * (w ^ 3)^2 * (p t1) ^ 2) by nra.
eapply Rle_trans.
apply sqrt_le_1_alt. 
eapply Rplus_le_compat_l.
eapply Rmult_le_compat_l; try nra.
apply H0.
replace ((a * w ^ 3 * (w * q t2) - b * w ^ 3 * (w * q t3))  ^ 2) with
(a^2 * (w ^ 3) ^2 * (w ^2 * q t2 ^2) + b^2 * (w ^ 3) ^2 * (w ^2 * q t3 ^2) - 
  2 * a * b * (w^3)^2 * (w * q t2) * (w * q t3))
by nra.
eapply Rle_trans.
apply sqrt_le_1_alt. 
eapply Rplus_le_compat_r.
eapply Rplus_le_compat_r.
eapply Rplus_le_compat_r.
eapply Rmult_le_compat_l; try nra.
apply H3.
eapply Rle_trans.
apply sqrt_le_1_alt. 
eapply Rplus_le_compat_r.
eapply Rplus_le_compat_r.
eapply Rplus_le_compat_l.
eapply Rmult_le_compat_l; try nra.
apply H4.
eapply Rle_trans.
apply sqrt_le_1_alt. 
eapply Rplus_le_compat_r.
eapply Rplus_le_compat_l.
apply Rabs_maj2.
repeat rewrite Rabs_mult.
eapply Rle_trans.
apply sqrt_le_1_alt. 
eapply Rplus_le_compat_r.
eapply Rplus_le_compat_l.
rewrite Rmult_assoc.
eapply Rmult_le_compat_l. 
repeat rewrite <- Rabs_mult. apply Rabs_pos.
rewrite <- Rabs_mult. 
eapply Rmult_le_compat; try apply Rabs_pos.
rewrite <- Rabs_mult; try apply Rabs_pos.
replace (w ^ 2 * q t2 ^ 2) with ((w * q t2) ^ 2) in H3 by nra.
apply Rabs_pos_le in H3; try nra; auto.
repeat rewrite Rabs_sqr_le in H3.
apply sqrt_le_1_alt in H3.
rewrite sqrt_pow2 in H3; try (apply Rabs_pos).
apply H3.
rewrite <- Rabs_mult. 
replace (w ^ 2 * q t3 ^ 2) with ((w * q t3) ^ 2) in H4 by nra.
apply Rabs_pos_le in H4; try nra; auto.
repeat rewrite Rabs_sqr_le in H4.
apply sqrt_le_1_alt in H4.
rewrite sqrt_pow2 in H4; try (apply Rabs_pos).
apply H4.
set (c:= (w ^ 2 * q 0 ^ 2 + p 0 ^ 2)).
replace ((sqrt (Rabs c) * sqrt (Rabs c))) with
(Rabs c) by (rewrite sqrt_sqrt; try apply Rabs_pos; nra).
replace (  (a ^ 2 * (w ^ 3) ^ 2 * c + b ^ 2 * (w ^ 3) ^ 2 * c +
   Rabs 2 * Rabs a * Rabs b * Rabs ((w ^ 3) ^ 2) * Rabs c +
   a ^ 2 * (w ^ 3) ^ 2 * c))
with 
  (( 2* a ^ 2 + b^2) * (w ^ 3) ^ 2 * c +
   Rabs 2 * Rabs a * Rabs b * Rabs ((w ^ 3) ^ 2) * Rabs c) by nra.
eapply Rle_trans.
apply sqrt_le_1_alt. 
eapply Rplus_le_compat_l.
eapply Rmult_le_compat_r.
apply Rabs_pos.
rewrite Rmult_comm.
rewrite Rmult_assoc.
rewrite Rmult_comm.
rewrite Rmult_assoc.
rewrite Rmult_comm.
eapply Rmult_le_compat_r.
apply Rabs_pos.
eapply Rmult_le_compat_r; try apply Rabs_pos.
eapply Rmult_le_compat; try apply Rabs_pos.
rewrite Rabs_pos_eq; try nra.
apply (Rmax_l a b).
rewrite Rabs_pos_eq; try nra.
apply (Rmax_r a b).
eapply Rle_trans.
apply sqrt_le_1_alt. 
eapply Rplus_le_compat_r.
eapply Rmult_le_compat_r; try unfold c; try nra.
eapply Rmult_le_compat_r; try nra.
eapply Rplus_le_compat.
eapply Rmult_le_compat_l; try nra.
replace (a ^ 2) with (a*a) by nra.
eapply Rmult_le_compat; try nra.
apply (Rmax_l a b). apply (Rmax_l a b).
replace (b ^ 2) with (b*b) by nra.
eapply Rmult_le_compat; try nra.
apply (Rmax_r a b). apply (Rmax_r a b). 
replace (2 * (Rmax a b * Rmax a b) + Rmax a b * Rmax a b)
with (3 * Rmax a b ^ 2) by nra.
replace (
3 * Rmax a b ^ 2 * (w ^ 3) ^ 2 * c +
Rmax a b * Rmax a b * Rabs ((w ^ 3) ^ 2) * Rabs 2 * Rabs c)
with (5 * Rmax a b ^2 * ((w ^ 3) ^ 2) * c).
repeat rewrite sqrt_mult_alt; try nra. 
repeat rewrite sqrt_pow2; try (apply Rmax_pos; auto).
unfold c. 
apply Req_le.
f_equal. f_equal. nra. nra.
repeat rewrite Rabs_pos_eq; try nra; try unfold c; try nra.
Qed.
*)
Ltac unfold_factorials :=
try repeat match goal with|-context[ (fact ?a)] =>
set (y:= fact a);
compute in y; subst y 
end; 
try repeat match goal with |-context[ (INR ?a)] =>
set (y:= INR a);
compute in y; subst y 
end;
try nra
.


Lemma Harm_sys_norm_bound p q:
forall t0 t1 t2 t3,
forall w h,
0 < w ->
0 < h  /\ 0 <= h  * w <= 2->
Harmonic_osc_system p q w t0-> 
Rprod_norm (h^4 / INR (fact 4) * Derive_n p 4 t2 - h^3 / 12 * w ^ 4 * q t3, h^3 / INR (fact 3) * w * Derive_n q 3 t1 ) <= 
 (h * w) ^ 3 * Rprod_norm( p t0, w * q t0).
Proof.
intros.
unfold Harmonic_osc_system in H.
pose proof Harm_sys_derive_eq p q w t0 H1 t1 as (A & _ & _ & _).
pose proof Harm_sys_derive_eq p q w t0 H1 t2 as (_ & _ & _ & C2).
rewrite A, C2. clear A C2.
pose proof (H1 t1) as A1; destruct A1 as (_ & _ &C).
pose proof (H1 t2) as A1; destruct A1 as (_ & _ &C2).
specialize (H1 t3). destruct H1 as (_ & _ & C3).
unfold Rprod_norm, fst, snd in *. cbv [prod_norm fst snd].
apply sqrt_le_0 in C, C2, C3; try nra.
assert (p t1 ^ 2  <= w ^2 * q t0 ^ 2 + p t0 ^ 2) by nra; 
  clear C.
assert (p t2 ^ 2  <= w ^2 * q t0 ^ 2 + p t0 ^ 2) by nra; 
  clear C2.
assert (w ^2 * q t3 ^ 2 <= w ^2 * q t0 ^ 2 + p t0 ^ 2) by nra; 
  clear C3.
set (y:=w ^ 2 * q t0 ^ 2 + p t0 ^ 2) in *. 
match goal with |- context[(?a - ?aa) ^2 ] =>
replace ((a - aa) ^2) with
  (a^2 + aa^2 -2*a*aa) by nra
end.
match goal with |- context[sqrt(?a) <= ?b] =>
assert (a <= b^2)
end.
+
eapply Rle_trans.
eapply Rplus_le_compat_r.
eapply Rplus_le_compat_r.
eapply Rplus_le_compat_r.

replace ((h ^ 4 / INR (fact 4) * (w ^ 4 * p t2)) ^ 2)
with ((h ^ 4 / INR (fact 4))^2 * (w ^ 4)^2 * (p t2) ^ 2) by nra.
eapply Rmult_le_compat_l; try nra. apply H2.

eapply Rle_trans.
eapply Rplus_le_compat_r.
eapply Rplus_le_compat_r.
eapply Rplus_le_compat_l.

replace ((h ^ 3 / 12 * w ^ 4 * q t3) ^ 2) 
with ((h ^ 3 / 12)^2 * (w ^ 3)^2 * (w ^2 * q t3 ^ 2)) by nra.
eapply Rmult_le_compat_l; try nra. apply H3.

eapply Rle_trans.
eapply Rplus_le_compat_r.
eapply Rplus_le_compat_l.
eapply Rle_trans.
apply Rabs_maj2.
repeat rewrite Rabs_mult.

eapply Rmult_le_compat_l. 
repeat rewrite <- Rabs_mult. apply Rabs_pos.
rewrite Rmult_assoc.
eapply Rmult_le_compat_l. apply Rabs_pos.
replace (Rabs (w ^ 4) * Rabs (q t3)) with
(Rabs (w ^ 3) * Rabs (w * q t3)).
eapply Rmult_le_compat_l. apply Rabs_pos.

apply Rabs_pos_le in H3; try nra; auto.
replace (w ^ 2 * q t3 ^ 2) with
((w * q t3) ^ 2) in H3.
rewrite Rabs_sqr_le in H3.
apply sqrt_le_1_alt in H3.
rewrite sqrt_pow2 in H3; try (apply Rabs_pos).
apply H3. 
try nra.
repeat rewrite <- Rabs_mult. f_equal. nra.

eapply Rle_trans.
eapply Rplus_le_compat_r.
eapply Rplus_le_compat_l.
eapply Rmult_le_compat_r.
rewrite <- Rmult_assoc.
apply Rle_mult.
rewrite <- Rabs_mult. apply Rabs_pos.
apply sqrt_pos.
eapply Rmult_le_compat_l. apply Rabs_pos.
eapply Rmult_le_compat_l. apply Rabs_pos.
eapply Rmult_le_compat_l. apply Rabs_pos.
apply Rabs_pos_le in H2; try nra; auto.
rewrite Rabs_sqr_le in H2.
apply sqrt_le_1_alt in H2.
rewrite sqrt_pow2 in H2; try (apply Rabs_pos).
apply H2.


eapply Rle_trans.
eapply Rplus_le_compat_l.
replace ((h ^ 3 / INR (fact 3) * w * (- w ^ 2 * p t1)) ^ 2)
with ((h ^ 3 / INR (fact 3) )^2 * w^2 * (w ^ 2)^2 * (p t1) ^ 2) by nra.
eapply Rmult_le_compat_l. nra.
apply H1.

replace (Rabs 2 * (Rabs (h ^ 4 / INR (fact 4)) * (Rabs (w ^ 4) * sqrt (Rabs y))) *
(Rabs (h ^ 3 / 12) * (Rabs (w ^ 3) * sqrt (Rabs y)))) with
(2 * h ^ 4 / INR (fact 4) * w ^ 4 * h ^ 3 / 12 *  w ^ 3 * y).

assert (h ^ 3 / 12 * w ^ 3 <= h ^ 3 / INR (fact 3) * (w ^ 3)).
replace (INR (fact 3)) with (6) by (simpl;nra).
apply Rmult_le_compat_r; try nra.

assert (h ^ 4 / INR (fact 4) * w ^ 4 <= h ^ 3 / INR (fact 3) * (w ^ 3)).
replace (INR (fact 4)) with (24) by (simpl;nra).

replace (h ^ 4 / 24 * w ^ 4) with
((h * w)^3 * (h * w) * /24) by nra.
replace (h ^ 3 / INR (fact 3) * w ^ 3) with
((h * w) ^ 3 * 4 *  /24) by (simpl; nra).
apply Rmult_le_compat_r; try nra.
apply Rmult_le_compat_l; try nra.
apply pow_le. apply H0.

eapply Rle_trans.
apply Rplus_le_compat_r.
apply Rplus_le_compat_r.
eapply Rle_trans.
apply Rplus_le_compat_r.
apply Rmult_le_compat_r; try nra.
replace ((h ^ 4 / INR (fact 4)) ^ 2 * (w ^ 4) ^ 2)
with ((h ^ 4 / INR (fact 4) * (w ^ 4)) ^ 2) by nra.
apply pow_incr.
split. simpl. nra.
apply H5.
apply Rplus_le_compat_l.
apply Rmult_le_compat_r; try nra.
replace ((h ^ 3 / 12) ^ 2 * (w ^ 3) ^ 2)
with ((h ^ 3 / 12 * w ^ 3) ^ 2) by nra.
apply pow_incr.
split. apply Rle_mult; try nra.
apply H4.


eapply Rle_trans.
apply Rplus_le_compat_r.
apply Rplus_le_compat_l.
apply Rmult_le_compat_r; try nra.
eapply Rle_trans.
apply Rmult_le_compat_r; try nra.
apply Rmult_le_compat_r; try nra.
apply Rmult_le_compat_r; try nra.
replace (2 * h ^ 4 / INR (fact 4) * w ^ 4)
with (2 * (h ^ 4 / INR (fact 4) * w ^ 4)) by nra.
apply Rmult_le_compat_l; try nra. 
apply H5.
rewrite Rmult_assoc.
rewrite Rmult_assoc.
apply Rmult_le_compat_l.
repeat (apply Rle_mult; simpl; try nra).
rewrite <- Rmult_assoc.
apply H4.

match goal with |- context [?a <= ?b] =>
replace a with ( 5 * (h ^ 3 / INR (fact 3)) ^ 2 * (w ^ 3) ^ 2 * y);
replace b with  ((h ^3)^2 * (w ^ 3)^2 * (w^2 * q t0 ^2 + p t0 ^ 2))
end.
subst y.
apply Rmult_le_compat_r; try (simpl; nra).
rewrite Rpow_mult_distr.
rewrite pow2_sqrt. nra. nra.

replace ((h ^ 3 / INR (fact 3)) ^ 2 * w ^ 2 * (w ^ 2) ^ 2 * y)
with ((h ^ 3 / INR (fact 3)) ^ 2 * (w ^ 3) ^ 2 * y) by nra.
field_simplify. nra.
simpl; nra. simpl; nra.
field_simplify. 
rewrite pow2_sqrt. nra.

apply sqr_plus_pos.
symmetry.
rewrite <- Rmult_assoc.
rewrite <- Rmult_assoc.
rewrite <- Rmult_assoc.
rewrite <- Rmult_assoc.
rewrite <- Rabs_mult.
rewrite <- Rabs_mult.
rewrite Rmult_comm.
rewrite Rmult_assoc.
rewrite<- Rabs_mult.
rewrite Rmult_comm.
rewrite Rmult_assoc.
rewrite Rmult_assoc.
replace (sqrt (Rabs y) * (Rabs (h ^ 3 / 12 * w ^ 3) * sqrt (Rabs y))) with 
((Rabs y) * Rabs (h ^ 3 / 12 * w ^ 3)).
repeat rewrite<- Rabs_mult.
field_simplify.
match goal with |- context [Rabs ?a = ?b] =>
field_simplify a
end.
apply Rabs_pos_eq. 
repeat apply Rle_mult; try (simpl;nra).
simpl. nra.
simpl. nra.
symmetry.
rewrite Rmult_comm.
rewrite Rmult_assoc.
symmetry.
rewrite Rmult_comm.
f_equal.
symmetry. apply sqrt_def.
subst y.
apply Rabs_pos.
+
apply sqrt_le_1_alt in H4.
rewrite sqrt_pow2 in H4.
eapply Rle_trans.
apply H4. try nra.
repeat apply Rle_mult; try (simpl;nra).
apply sqrt_pos.
Qed.



Theorem local_truncation_error_aux:
forall p q: R -> R,
forall t0 tn: R,
(forall t1 t2: R,
Harmonic_osc_system p q 1 t0 /\
k_differentiable p 4 t1 t2 /\
k_differentiable q 3 t1 t2)  ->
exists t1 t2: R,
tn < t1 < tn + h /\
tn < t2 < tn + h /\
 q (tn + h) - snd(leapfrog_stepR (p tn, q tn)) = 
    h^3 / INR (fact 3) * Derive_n q 3 t1 /\
 p (tn + h) - fst(leapfrog_stepR (p tn,  q tn)) = 
    h^4 / INR (fact 4) * Derive_n p 4 t2 - h^3 / 12 * q tn . 
Proof.
intros.
assert (tn < tn + h) as LT by (unfold h; nra).
specialize (H  tn (tn +h)).
destruct H as (HSY & KP & KQ); unfold k_differentiable in *.
pose proof Taylor_Lagrange q 2 tn (tn + h) LT KQ as TLRq. 
pose proof Taylor_Lagrange p 3 tn (tn + h) LT KP as TLRp.
destruct TLRq as (t1 & A & B). 
destruct TLRp as (t2 & C & D).
replace (tn + h - tn) with h in * by nra.

pose proof Harm_sys_derive_eq p q 1 t0 HSY tn as (HD1 & HD2 & HD3 & HD4).

unfold Harmonic_osc_system in HSY.
exists t1, t2. 
repeat split; try apply A; try apply C.
+  
rewrite B. cbv [sum_f_R0].
specialize (HSY tn). destruct HSY as (Hxd1 & Hxd2 & _ ).
rewrite Hxd1, Hxd2. 
unfold Derive_n at 1. unfold F.
unfold leapfrog_stepR, fst, snd.
unfold_factorials. 
+  
rewrite D. cbv [sum_f_R0].
replace (Derive_n p 2 tn) with 
(Derive_n (fun y : R => F (q y) 1) 1 tn). 
2: {
replace (Derive_n (fun y : R => F (q y) 1) 1 tn) with 
(Derive_n (Derive_n q 1) 2 tn ). 
(apply Derive_n_ext; apply HSY).
replace (Derive_n (Derive_n q 1) 2 tn) with
(Derive_n (Derive_n q 2) 1 tn) by auto.
apply Derive_n_ext.
apply HSY.
}
unfold F. 
rewrite Derive_n_scal_l.
replace (Derive_n p 1 tn) with 
(Derive_n q 2 tn) by (
replace (Derive_n q 2 tn) with
(Derive_n (Derive_n q 1) 1 tn) by auto;
apply Derive_n_ext; apply HSY).
specialize (HSY tn). destruct HSY as (Hxd1 & Hxd2 & _).
rewrite Hxd2. rewrite Hxd1. unfold Derive_n at 1.
rewrite HD3. 
unfold leapfrog_stepR, F, fst, snd.
unfold_factorials.
Qed.


Theorem local_truncation_error_norm_aux:
forall p q: R -> R,
forall t0 tn: R,
(forall t1 t2: R,
Harmonic_osc_system p q 1 t0 /\
k_differentiable p 4 t1 t2 /\
k_differentiable q 3 t1 t2)  ->
exists t1 t2: R,
tn < t1 < tn + h /\
tn < t2 < tn + h /\
Rprod_norm (Rprod_minus (p (tn + h), q (tn + h)) 
  (leapfrog_stepR (p tn, q tn) ))
 <= Rprod_norm (h^4 / INR (fact 4) * Derive_n p 4 t2 - h^3 / 12 * q tn,
 h^3 / INR (fact 3) * Derive_n q 3 t1).
Proof.
intros.
pose proof local_truncation_error_aux p q t0 tn H as LTE.
destruct LTE as [t1 [t2 [A [B [ C D ] ] ] ]].
exists t1, t2.
split; auto.
split; auto.
unfold Rprod_norm, Rprod_minus.
unfold fst at 1 2. unfold snd at 1 2.
unfold fst at 2. unfold snd at 2.
rewrite C, D.
apply Req_le.
nra.
Qed.

Theorem local_truncation_error_norm:
forall p q: R -> R,
forall t0 tn,
(forall t1 t2: R,
Harmonic_osc_system p q 1 t0 /\
k_differentiable p 4 t1 t2 /\
k_differentiable q 3 t1 t2)  ->
Rprod_norm (Rprod_minus (p (tn + h), q (tn + h)) 
 (leapfrog_stepR (p tn, q tn) ))
 <=  h ^3 * Rprod_norm( p t0,  q t0).
Proof.
intros.
pose proof local_truncation_error_norm_aux 
  p q t0 tn H as (t1 & t2 & A & B & C).
eapply Rle_trans.
apply C.
specialize (H t1 t2) as (D & E).
eapply Rle_trans.
assert (0 < 1) by nra.
assert (0 < h /\ 0 <= h * 1 <= 2) by (unfold h; split; nra).
pose proof (Harm_sys_norm_bound p q t0 t1 t2 tn 1 h H H0 D).
rewrite pow1 in H1. 
repeat rewrite Rmult_1_r in H1.
apply H1. 
rewrite Rmult_1_l.
apply Req_le. auto. 
Qed.

(* the 2norm of the matrix A corresponding to the leapfrog 
map is equal to the largest singular values of A'A. 
In the future, we should derive this value in Coq. For now,
we just compute it by hand -- using sympy -- and define it. *)
Definition method_norm h w :=
  let b := (h * w)^2 in
  sqrt(2*b^3 + 2*b*sqrt(b*(b+4))*sqrt(b^2-4*b+16) + 64)/8.

Definition method_norm2 h w :=
  let b := (h * w)^2 in
  sqrt((2*b^3 + 2*b*sqrt(b*(b+4))*sqrt(b^2-4*b+16))/64 + 1).

Lemma method_norms_eq h w:
method_norm2 h w = method_norm h w.
Proof.
intros.
unfold method_norm, method_norm2.
replace (8) with (sqrt (8^2)).
rewrite <- sqrt_div_alt; try nra.
f_equal. nra.
rewrite <- sqrt_pow2; nra.
Qed.

Lemma method_norm2_sep_aux h w : 
method_norm2 h w = 1 ->
h  * w = 0.
Proof.
intros.
unfold method_norm2 in H.
rewrite <- sqrt_1 in H at 2.
apply sqrt_inj in H; try nra; auto.
rewrite Rplus_comm in H.
apply Rplus_0_r_uniq in H.
assert (2 * ((h * w) ^ 2) * ( (h * w)^4 + sqrt ((h * w) ^ 2 * ((h * w) ^ 2 + 4)) *
     sqrt (((h * w) ^ 2) ^ 2 - 4 * (h * w) ^ 2 + 16)) = 0) by nra.
clear H.
apply Rmult_integral in H0.
destruct H0.
+ apply Rmult_integral in H.
destruct H. lra.
replace ((h * w) ^ 2) with ((h*w) * (h*w)) in H by nra.
apply Rmult_integral in H; destruct H; auto.
+  apply Rplus_opp_r_uniq in H.
match goal with [H : sqrt ?a * sqrt ?b = ?c  |- _] => 
pose proof sqrt_pos a as Ha; pose proof sqrt_pos b as Hb;
pose proof Rle_mult (sqrt a) (sqrt b) Ha Hb;
clear Ha Hb;
assert (0 <= c) by nra
end.
apply Ropp_0_le_ge_contravar in H1.
rewrite Ropp_involutive in H1. 
apply Rge_le in H1.
assert (0 <= (h * w) ^ 4).
apply Private.IT1.IT.TM.TMI.ZEven_pow_le. 
  simpl. hnf. exists 2%Z. lia.
Admitted.

Lemma method_norm2_sep h w : 
0 < w -> 
0 < h ->
method_norm2 h w <> 1.
Proof.
intros.
hnf; intros.
pose proof method_norm2_sep_aux h w H1.
nra.
Qed.


Definition method_norm3 h w :=  (1 + h * w - 0.5 * h^2 * w^2).

(*
Axiom method_norm2_subordinate :  forall p1 q1 p2 q2 w h: R,
Rprod_norm (Rprod_minus 
  (leapfrogR p1 (w * q1) w h 1)  
  (leapfrogR p2 (w * q2) w h 1)) <= 
method_norm2 h w * Rprod_norm (Rprod_minus (p1, w * q1) (p2, w *q2)).


Lemma global_error_aux1: 
forall p1 q1 p2 q2 w h: R,
Rprod_norm (Rprod_minus 
  (leapfrogR p1 (w * q1) w h 1)  
  (leapfrogR p2 (w * q2) w h 1)) = 
Rprod_norm (leapfrogR 
    (fst(Rprod_minus (p1, (w * q1)) 
      (p2,(w * q2))))
    (snd(Rprod_minus (p1, (w * q1)) 
      (p2,(w * q2)))) w h 1).
Proof.
intros.
unfold Rprod_norm, Rprod_minus, leapfrogR, F, 
  fst, snd.  f_equal. 
nra.
Qed.
*)

Import Coq.Logic.FunctionalExtensionality.

Lemma sum_pow_mult_l:
  forall a : R,
  forall n : nat,
  a * sum_f 0 n (fun m => a ^ m ) = 
  sum_f 1 (S n) (fun m => a ^ m ).
Proof.
intros.
replace (a * sum_f 0 n (fun m => a ^ m ) )
with 
( sum_f 0 n (fun m => a ^ m * a )).
+ replace (fun m : nat => a ^ m * a) with 
(fun m : nat => a ^ (m+1)).
induction n.
++ unfold sum_f. simpl. nra.
++ set (yy:=sum_f 0 (S n) (fun m : nat => a ^ (m + 1))).
rewrite sum_f_n_Sm. rewrite <- IHn. subst yy.
rewrite sum_f_n_Sm. repeat f_equal. ring. 
apply Nat.le_0_l.
rewrite <- Nat.succ_le_mono.
apply Nat.le_0_l.
++ apply functional_extensionality.
intros. replace (x+1)%nat 
  with (S x) by ring.
simpl; nra.
+  induction n.
++ unfold sum_f. simpl. nra.
++  rewrite sum_f_n_Sm. rewrite IHn.
rewrite sum_f_n_Sm. field_simplify. nra. 
apply Nat.le_0_l. apply Nat.le_0_l.
Qed.

Lemma sum_pow_mult_r : 
  forall a : R,
  forall n : nat,
  sum_f 0 n (fun m => a ^ m ) * a = 
  sum_f 1 (S n) (fun m => a ^ m ).
Proof.
intros.
rewrite Rmult_comm.
apply sum_pow_mult_l.
Qed.

Lemma sum_pow_first :
  forall a : R,
  forall n : nat,
  sum_f 0 (S n) (fun m => a ^ m ) = 
  sum_f 1 (S n) (fun m => a ^ m ) + 1.
Proof.
intros.
induction n. 
+ unfold sum_f. simpl. nra.
+ 
match goal with |-context[?a = ?b]=>
set (yy:= a)
end.
rewrite sum_f_n_Sm.
rewrite Rplus_assoc.
rewrite Rplus_comm.
rewrite Rplus_comm in IHn.
rewrite Rplus_assoc.
rewrite <- IHn.
subst yy.
rewrite sum_f_n_Sm.
rewrite IHn.
field_simplify. nra.
apply Nat.le_0_l.
rewrite <- Nat.succ_le_mono.
apply Nat.le_0_l.
Qed.


Definition error_sum error n: R:=
 match n with 
  | 0 => 0
  | S n' => sum_f 0 n' (fun m => error ^ m )
end
.

Lemma error_sum_aux n (er: R):
  error_sum er n + er ^ n = error_sum er (S n).
Proof.
intros.
induction n. 
+  simpl. unfold sum_f. simpl. nra.
+ unfold error_sum.
rewrite sum_f_n_Sm; auto.
apply Nat.le_0_l.
Qed.

Lemma error_sum_aux2 er n:
  er * error_sum er n + 1  = error_sum er (S n).
Proof.
intros.
induction n. 
+  simpl. unfold sum_f. rewrite Rmult_0_r. simpl. nra.
+ unfold error_sum.
rewrite Rmult_comm.
rewrite sum_pow_mult_r.
rewrite sum_pow_first.
nra.
Qed.

Definition Rabs_prod A := (Rabs (fst A) , Rabs (snd A)).

Fixpoint Rprod_sum (f:nat -> R * R) (n:nat) : R * R :=
  match n with
    | O => f 0%nat
    | S i => Rprod_plus (Rprod_sum f i) (f (S i))
  end.

Definition Rprod_error (f:nat -> R * R) (n:nat) : R * R :=
  match n with
    | O => (0,0)
    | S i => Rprod_sum f i
  end.

Lemma Rprod_sum_Sn : 
forall n ic, 
Rprod_sum (fun m : nat => iternR ic m) (S n) = 
Rprod_plus(
Rprod_sum (fun m : nat => iternR ic m) n) (iternR ic (S n)).
Proof.
intros.
induction n.
+ simpl. auto.
+ unfold Rprod_sum.
fold Rprod_sum. auto.
Qed.


Lemma Rprod_error_Sn : 
forall n ic, 
Rprod_plus (Rprod_error (fun m : nat => iternR ic m) n)
  (iternR ic n ) = 
    (Rprod_error (fun m : nat => iternR ic m) (S n)).
Proof.
intros.
induction n.
+ destruct ic. unfold Rprod_error, iternR, 
  Rprod_sum, leapfrogR, leapfrog_stepR, Rprod_plus, fst, snd;
  f_equal; nra.
+ unfold Rprod_error. unfold Rprod_sum.
fold Rprod_sum. auto.
Qed. 

Lemma leapfrog_stepR_sum :
forall ic n,
Rprod_plus (leapfrog_stepR (Rprod_error (fun m : nat => iternR ic m) n)) ic = 
(Rprod_sum (fun m : nat => iternR ic m)  n).
Proof.
intros.
induction n.
+ destruct ic. unfold Rprod_error, iternR, Rprod_sum, leapfrogR, leapfrog_stepR, Rprod_plus, fst, snd.
f_equal; nra.
+ rewrite  <-  Rprod_error_Sn.
rewrite Rprod_sum_Sn.
rewrite <- IHn.
replace ((iternR ic (S n))) with
(leapfrog_stepR (iternR ic n)).
rewrite <- leapfrog_plus_args.
rewrite Rprod_plus_assoc.
rewrite Rprod_plus_assoc.
f_equal.
rewrite Rprod_plus_sym.
auto.
destruct ic.
rewrite step_iternR; auto.
Qed. 


Theorem global_truncation_error_sum_aux: 
forall p q: R -> R,
forall t0 : R,
(forall t1 t2: R,
Harmonic_osc_system p q 1 t0 /\
k_differentiable p 4 t1 t2 /\
k_differentiable q 3 t1 t2)  ->
forall n : nat, 
 Rprod_minus (p (t0 + INR n * h),  q (t0 + INR n * h)) 
(iternR (p t0, q t0) n)
= Rprod_error (fun m => (iternR (p t0, q t0) m)) n.
Proof.
intros. 
induction n.
+ unfold Rprod_sum, Rprod_minus. simpl. rewrite Rmult_0_l. 
rewrite Rplus_0_r. f_equal; nra.
+ rewrite step_iternR.
set (phi1:= leapfrog_stepR (p (t0 + INR  n * h), q (t0 + INR  n * h))) in *.
set (phi2:=  
leapfrog_stepR (iternR (p t0, q t0) n)).
match goal with |- context[ ?a = ?b] =>
  replace a with 
  (Rprod_plus (Rprod_minus (p (t0 + INR (S n) * h ),  q (t0 + INR (S n) * h)) phi1)
(Rprod_minus phi1 phi2)) by (unfold Rprod_minus, fst at 1, snd at 1; unfold fst at 4, snd at 4, Rprod_plus;
unfold fst at 1, fst at 2, snd at 1, snd at 2; f_equal; nra)
end.
subst phi1; subst phi2.
rewrite leapfrog_minus_args.
rewrite IHn.
pose proof leapfrog_stepR_sum (p t0, q t0) n.
replace (leapfrog_stepR
     (Rprod_error (fun m : nat => iternR (p t0, q t0) m)  n))
with 
(Rprod_minus (Rprod_sum 
  (fun m : nat => iternR (p t0, q t0) m) n) (p t0, q t0)).
unfold Rprod_error.
 


Admitted. 


Theorem global_truncation_error_sum : 
forall p q: R -> R,
forall t0 : R,
(forall t1 t2: R,
Harmonic_osc_system p q 1 t0 /\
k_differentiable p 4 t1 t2 /\
k_differentiable q 3 t1 t2)  ->
forall C : R,
(forall p0 q0 : R, 
forall m : nat, Rprod_norm(iternR (p0,q0) m) <= C *  Rprod_norm(p0,q0)) ->
forall n : nat, 
Rprod_norm (Rprod_minus (p (t0 + INR n * h),  q (t0 + INR  n * h)) 
(iternR (p t0, q t0) n))
 <=   h^3 * C ^2 * Rprod_norm(p t0,q t0) * INR n.
Proof.
intros. 
induction n.
+ simpl. 
rewrite Rmult_0_l. rewrite Rmult_0_r.
rewrite Rplus_0_r. unfold Rprod_minus, Rprod_norm, fst, snd.
repeat rewrite Rminus_eq_0. rewrite pow_i. rewrite Rplus_0_r.
rewrite sqrt_0. nra. lia.
+ rewrite step_iternR.
set (phi1:= leapfrog_stepR (p (t0 + INR  n * h), q (t0 + INR  n * h))) in *.
set (phi2:=  
leapfrog_stepR (iternR (p t0, q t0) n)).
eapply Rle_trans.
match goal with |- context[ ?a <= ?b] =>
  replace a with (Rprod_norm 
  (Rprod_plus (Rprod_minus (p (t0 + INR (S n) * h ),  q (t0 + INR (S n) * h)) phi1)
(Rprod_minus phi1 phi2))) by (symmetry; apply Rprod_norm_plus_minus_eq)
end.
apply Rprod_triang_ineq.
pose proof local_truncation_error_norm p q t0 (t0 + INR n * h) H.
fold phi1 in H1.
eapply Rle_trans.
eapply Rplus_le_compat_r.
rewrite S_INR.
replace (t0 + (INR n + 1) * h) with (t0 + INR n * h + h) by nra.
apply H1.
eapply Rle_trans.
eapply Rplus_le_compat_l.
subst phi1 phi2.
pose proof method_norm2_subordinate (p (t0 + INR ( n) * h)) ( q (t0 + INR n * h)) 
(fst(leapfrogR (p t0) (w * q t0) w h n)) 
(1/w *snd(leapfrogR (p t0) (w * q t0) w h n)) w h.
replace 
(w * (1 / w * snd (leapfrogR (p t0) (w * q t0) w h n)))
with 
(snd (leapfrogR (p t0) (w * q t0) w h n)) in H4.
apply H4.
field_simplify. nra.
nra.
eapply Rle_trans.
eapply Rplus_le_compat_l.
eapply Rmult_le_compat_l; try (unfold h;nra).

unfold method_norm2. apply sqrt_pos.

apply IHn. (*lemmas about sums*)
set 
  (aa:=sqrt 5 * 0.25 * w ^ 3 * 
  Rprod_norm (p 0, w * q 0) * h ^ 3).
rewrite <- error_sum_aux2.
nra.
Qed.

(* apparently this is already covered by Constant Coq.Reals.PartSum.tech3*)
Theorem geo_series_closed_form:
forall r k ,
r <> 1 ->
sum_f 0 k (fun m => r ^ m ) = (1-(r^(S k)))/(1-r).
Proof.
intros.
induction k.
+ unfold sum_f. simpl. field_simplify. nra. lra. 
+ rewrite sum_f_n_Sm .
++ rewrite IHk.
match goal with|- context [?a/?aa + ?b = _] =>
replace  b with 
((r ^ S k)*(1-r)/(1-r))
end.
field_simplify; try nra.
replace  (- r ^ S k * r) with
(- r ^ S (S k) ).
nra.
simpl. nra.
field_simplify; try nra.
++ apply Nat.le_0_l.
Qed.

Theorem global_truncation_error: 
forall p q: R -> R,
forall w h : R,
0 < w ->
0 < h ->
0 < h * w < 2 ->
(forall t1 t2: R,
Harmonic_osc_system p q w/\
k_differentiable p 4 t1 t2 /\
k_differentiable q 3 t1 t2)  ->
forall n : nat, 
forall t0 : R,
Rprod_norm (Rprod_minus (p (t0 + INR n * h), w * q (t0 + INR n * h)) 
(leapfrogR (p t0) (w * q t0) w h n))
 <= 
h ^ 3 * w ^ 3 * Rprod_norm( p (0), w * q(0)) * (1-(method_norm2 h w)^ n)/(1- (method_norm2 h w)).
Proof.
intros.
assert (method_norm2 h w <> 1).
+ apply method_norm2_sep; auto.
+ induction n.
++ unfold Rprod_minus, Rprod_norm. simpl.
rewrite Rmult_0_l. rewrite Rplus_0_r. 
repeat rewrite Rmult_1_r. 
replace (p t0 - p t0) with 0 by nra.
replace (w * q t0 - w * q t0) with 0 by nra.
field_simplify. rewrite Rmult_0_l. 
replace (0+0) with 0 by nra.
rewrite sqrt_0. nra. nra.
++  pose proof geo_series_closed_form (method_norm2 h w) n.
specialize (H4 H3); clear H3.
assert (BND: 0 <= h * w <= 2) by nra.
pose proof 
  global_truncation_error_sum p q w h H H0 BND H2 (S n) t0.
eapply Rle_trans. apply H3.
unfold error_sum.
rewrite H4. 
apply Req_le.
nra.
Qed.


Lemma binomial_approx_aux: 
forall n x t,
  0 <= t <= x ->
  forall k : nat, (k <= 2)%nat -> 
      ex_derive_n (fun x : R =>  (1 + x) ^ n) k t.
Proof.
intros.
set (g:= fun z : R => z ^ n).
pose proof ex_derive_n_comp_trans g k t 1.
pose proof ex_derive_n_pow k n (t+1).
subst g.
specialize (H1 H2).
simpl in H1.
assert (ex_derive_n (fun y : R => (y + 1) ^ n) k t 
= ex_derive_n (fun x0 : R => (1 + x0) ^ n) k t).
f_equal.
apply functional_extensionality. 
intros; rewrite Rplus_comm; auto.
rewrite <- H3; auto.
Qed.

Lemma ex_derive_n_sqrt k (t: R): 
0 < t ->
ex_derive_n sqrt k t.
Proof.
intros.
assert (ex_derive (Derive_n sqrt k) t).
apply ex_derive_Reals_1.
pose proof Coquelicot.is_derive_n_sqrt k t H.
apply is_derive_n_unique in H0.
Admitted.


Lemma binomial_approx_sqrt_aux: 
forall n x t,
  0 <= t <= x ->
  forall k : nat, (k <= 2)%nat -> 
      ex_derive_n (fun x : R =>  sqrt(1 + x) ^ n) k t.
Admitted.


Lemma t_exp_norm_A w n: 
  0 < w -> 
  let x:= ((method_norm2 h w) ^2 - 1) in   
  exists n1 n2,
  0 < n1 < x /\
  0 < n2 < x /\
  (method_norm2 h w )^n = 
  1 + 0.5 * INR n * x - (1/8) * x^2 * INR n * (INR n -2) * sqrt(1 +  n1)^(n-4) /\ 
  method_norm2 h w = 
  1 + 0.5 * x - (1/8) * x^2 * sqrt(1 +  n2)^3.
Proof. 
intros.

assert (0 <=
(2 * ((h * w) ^ 2) ^ 3 +
 2 * (h * w) ^ 2 * sqrt ((h * w) ^ 2 * ((h * w) ^ 2 + 4)) *
 sqrt (((h * w) ^ 2) ^ 2 - 4 * (h * w) ^ 2 + 16)) / 64 + 1).


apply Rle_plus; try nra.
repeat (apply Rle_mult; try nra). 
apply Rle_plus; try nra.
repeat (apply Rle_mult; try nra). 
apply sqrt_pos.
apply sqrt_pos.

assert (Hx: 0 < x).

+ unfold x, method_norm2.
match goal with |- context [0 < sqrt (?b/64 + 1)^2 - _] =>
assert (0 <= b)
end. 


apply Rle_plus; try nra.
repeat (apply Rle_mult; try nra). 
apply sqrt_pos.
apply sqrt_pos.
rewrite pow2_sqrt.
++ field_simplify. 
apply RIneq.Rdiv_lt_0_compat; try nra.
apply Rplus_lt_0_compat; try nra.
repeat (apply Rmult_lt_0_compat; try nra).
repeat (apply Rmult_lt_0_compat; try nra).
apply sqrt_lt_R0.
repeat (apply Rmult_lt_0_compat; try nra).
apply sqrt_lt_R0. nra. 
++ apply Rle_plus; try nra.
+ pose proof  binomial_approx_sqrt_aux n x as P. 
pose proof  binomial_approx_sqrt_aux 1 x as P1. 
pose proof Taylor_Lagrange (fun x => sqrt (1+x)^n ) 1 0  x Hx P 
  as (zeta & B & C).
simpl in P1. replace (fun x : R => sqrt (1 + x) * 1) 
  with (fun x : R => sqrt (1 + x)) in P1.
pose proof Taylor_Lagrange (fun x => sqrt (1+x) ) 1 0  x Hx P1
  as (zeta1 & B1 & C1).
exists zeta, zeta1.
repeat (split; try apply B; try apply B1).
replace ((method_norm2 h w)^n) with 
  ( sqrt(1+x)^n ). rewrite C. unfold sum_f_R0.
rewrite Rminus_0_r. simpl. Admitted.
 

Theorem global_error_linear3:
forall p q: R -> R,
forall w : R,
0< w ->
0< h -> 
0 < h * w < 2 ->
(forall t1 t2: R,
Harmonic_osc_system p q w/\
k_differentiable p 4 t1 t2 /\
k_differentiable q 3 t1 t2)  ->
forall n : nat,
forall t0 : R,
exists n1: R,
let x:= ((method_norm3 h w)^2 - 1) in 
  0 < n1 < x /\
Rprod_norm (Rprod_minus (p (t0 + INR n * h), w * q (t0 + INR n * h)) 
(leapfrogR (p t0, q t0) n)) <= 
(h ^ 3 * w ^ 3 * Rprod_norm( p (0), w * q(0))) *
((INR n * x + 0.5 * INR n * (INR (n -1)) * x^2 * (1 +  n1)^(n-2)) / x).
Proof.
intros.
pose proof t_exp_norm_A w n H H1.
destruct H3 as (n1 & A).
destruct A as (B & C).
replace (method_norm2 h w -1) with 
(h * w * (1 - 0.5 * h * w)) by (unfold method_norm2;
simpl; nra).
exists n1.
split. apply B.
eapply Rle_trans.
apply global_truncation_error; auto.
assert (1 - method_norm3 h w ^ n = - (INR n * (h * w * (1 - 0.5 * h * w)) +
    0.5 * INR n * INR (n - 1) * (h * w * (1 - 0.5 * h * w)) ^ 2 *
    (1 + n1) ^ (n - 2))).
rewrite C. field_simplify. nra.
assert ((1 - method_norm3 h w) = - (h * w * (1 - 0.5 * h * w))) by 
  (unfold method_norm3; field_simplify;nra).
set (aa:= h^3 * w ^ 3 * Rprod_norm (p 0, w * q 0)).

match goal with |- context[ aa * ?a / ?d <= _ ] =>
replace (aa * a / d) with ( aa * (a/d)) by nra
end. 
rewrite Rmult_assoc.
apply Rmult_le_compat_l.
unfold aa. 
apply Rle_mult; try nra; try apply Rnorm_pos.

rewrite H3; rewrite H4.
apply Req_le. 
match goal with |-context[-?a/-?b  = _] =>
replace (-a/-b) with (a/b) 
end.
field_simplify. nra.
repeat (split; try nra).
repeat (split; try nra).
apply Stdlib.Rdiv_eq_reg.
field_simplify. nra.
nra.
nra.
Qed.



Close Scope R_scope. 
