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


Definition Harmonic_osc_system p q w :=
forall t,
Derive_n q 1 t  = p t /\
Derive_n q 2 t = (fun y => F (q y) w) t /\
Rprod_norm ( p(t), w * q(t)) <= Rprod_norm( p (0), w * q(0))
.


Lemma Harm_sys_derive_eq p q w: 
Harmonic_osc_system p q w-> 
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
replace (w ^ 4 * q t0) with 
(- w ^ 2 * Derive_n q 2 t0).
rewrite <- Derive_n_scal_l.
rewrite  Coquelicot.Derive_nS. 
apply Derive_n_ext.
intros.
replace (- w ^ 2 * q t1) with
( Derive_n q 2 t1).
rewrite  Coquelicot.Derive_nS.
 replace (Derive p) with (Derive_n p 1); auto.
apply Derive_n_ext.
intros.
specialize (H t2).
symmetry; replace (Derive q t2) with (Derive_n q 1 t2) by auto.
apply H.
specialize (H t1).
destruct H as (_ & B1 & _).
rewrite B1. unfold F; auto.
specialize (H t0).
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
forall t1 t2 t3,
forall w,
0 < w ->
0<= h * w <= 2 ->
Harmonic_osc_system p q w-> 
Rprod_norm (h^4 / INR (fact 4) * Derive_n p 4 t2 - h^3 / 12 * w ^ 4 * q t3, h^3 / INR (fact 3) * w * Derive_n q 3 t1 ) <= 
 (h * w) ^ 3 * Rprod_norm( p (0), w * q(0)).
Proof.
intros.
unfold Harmonic_osc_system in H.
pose proof Harm_sys_derive_eq p q w H1 t1 as (A & _ & _ & _).
pose proof Harm_sys_derive_eq p q w H1 t2 as (_ & _ & _ & C2).
rewrite A, C2. clear A C2.
pose proof (H1 t1) as A1; destruct A1 as (_ & _ &C).
pose proof (H1 t2) as A1; destruct A1 as (_ & _ &C2).
specialize (H1 t3). destruct H1 as (_ & _ & C3).
unfold Rprod_norm, fst, snd in *.
apply sqrt_le_0 in C, C2, C3; try nra.
assert (p t1 ^ 2  <= w ^2 * q 0 ^ 2 + p 0 ^ 2) by nra; 
  clear C.
assert (p t2 ^ 2  <= w ^2 * q 0 ^ 2 + p 0 ^ 2) by nra; 
  clear C2.
assert (w ^2 * q t3 ^ 2 <= w ^2 * q 0 ^ 2 + p 0 ^ 2) by nra; 
  clear C3.
set (y:=w ^ 2 * q 0 ^ 2 + p 0 ^ 2) in *. 
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
split. unfold h. simpl. nra.
apply H5.
apply Rplus_le_compat_l.
apply Rmult_le_compat_r; try nra.
replace ((h ^ 3 / 12) ^ 2 * (w ^ 3) ^ 2)
with ((h ^ 3 / 12 * w ^ 3) ^ 2) by nra.
apply pow_incr.
split. unfold h. simpl. nra.
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
apply Rmult_le_compat_l; try (simpl; unfold h;nra).
rewrite <- Rmult_assoc.
apply H4.

match goal with |- context [?a <= ?b] =>
replace a with ( 5 * (h ^ 3 / INR (fact 3)) ^ 2 * (w ^ 3) ^ 2 * y);
replace b with  ((h ^3)^2 * (w ^ 3)^2 * (w^2 * q 0 ^2 + p 0 ^ 2))
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
forall w : R,
(forall t1 t2: R,
Harmonic_osc_system p q w/\
k_differentiable p 4 t1 t2 /\
k_differentiable q 3 t1 t2)  ->
forall t0 : R,
exists t1 t2: R,
t0 < t1 < t0 + h /\
t0 < t2 < t0 + h /\
 w * q (t0 + h) - snd(leapfrogR (p t0) (w * q t0) w 1) = 
    w * h^3 / INR (fact 3) * Derive_n q 3 t1 /\
 p (t0 + h) - fst(leapfrogR (p t0) (w * q t0) w 1) = 
    h^4 / INR (fact 4) * Derive_n p 4 t2 - h^3 / 12 * w^4 * q t0 . 
Proof.
intros.
assert (t0 < t0 + h) as LT by (unfold h; nra).
specialize (H  t0 (t0 +h)).
destruct H as (HSY & KP & KQ); unfold k_differentiable in *.
pose proof Taylor_Lagrange q 2 t0 (t0 + h) LT KQ as TLRq. 
pose proof Taylor_Lagrange p 3 t0 (t0 + h) LT KP as TLRp.
destruct TLRq as (t1 & A & B). 
destruct TLRp as (t2 & C & D).
replace (t0 + h - t0) with h in * by nra.

pose proof Harm_sys_derive_eq p q w HSY t0 as (HD1 & HD2 & HD3 & HD4).

unfold Harmonic_osc_system in HSY.
exists t1, t2. 
repeat split; try apply A; try apply C.
+  
rewrite B. cbv [sum_f_R0].
specialize (HSY t0). destruct HSY as (Hxd1 & Hxd2 & _ ).
rewrite Hxd1, Hxd2. 
unfold Derive_n at 1. unfold F.
unfold leapfrogR, fst, snd.
unfold_factorials. 
+  
rewrite D. cbv [sum_f_R0].
replace (Derive_n p 2 t0) with 
(Derive_n (fun y : R => F (q y) w) 1 t0). 
2: {
replace (Derive_n (fun y : R => F (q y) w) 1 t0) with 
(Derive_n (Derive_n q 1) 2 t0 ). 
(apply Derive_n_ext; apply HSY).
replace (Derive_n (Derive_n q 1) 2 t0) with
(Derive_n (Derive_n q 2) 1 t0) by auto.
apply Derive_n_ext.
apply HSY.
}
unfold F. 
rewrite Derive_n_scal_l.
replace (Derive_n p 1 t0) with 
(Derive_n q 2 t0) by (
replace (Derive_n q 2 t0) with
(Derive_n (Derive_n q 1) 1 t0) by auto;
apply Derive_n_ext; apply HSY).
specialize (HSY t0). destruct HSY as (Hxd1 & Hxd2 & _).
rewrite Hxd2. rewrite Hxd1. unfold Derive_n at 1.
rewrite HD3. 
unfold leapfrogR, F, fst, snd.
unfold_factorials.
Qed.


Theorem local_truncation_error_norm_aux:
forall p q: R -> R,
forall w : R,
(forall t1 t2: R,
Harmonic_osc_system p q w /\
k_differentiable p 4 t1 t2 /\
k_differentiable q 3 t1 t2)  ->
forall t0 : R,
exists t1 t2: R,
t0 < t1 < t0 + h /\
t0 < t2 < t0 + h /\
Rprod_norm (Rprod_minus (p (t0 + h), w * q (t0 + h)) 
  (leapfrogR (p t0) (w * q t0) w 1))
 <= Rprod_norm (h^4 / INR (fact 4) * Derive_n p 4 t2 - h^3 / 12 * w^4 * q t0,
 w * h^3 / INR (fact 3) * Derive_n q 3 t1).
Proof.
intros.
pose proof local_truncation_error_aux p q w H t0 as LTE.
destruct LTE as [t1 [t2 [A [B [ C D ] ] ] ]].
exists t1, t2.
split; auto.
split; auto.
unfold Rprod_norm, Rprod_minus.
unfold fst at 1 2. unfold snd at 1 2.
unfold fst at 2. unfold snd at 2.
rewrite C, D.
set (c:= ( w * h^3  / INR (fact 3) * Derive_n q 3 t1) ^ 2 +
   (h^4 / INR (fact 4) * Derive_n p 4 t2 - h^3 / 12 * w^4 * q t0) ^ 2).
apply Req_le.
nra.
Qed.

Theorem local_truncation_error_norm:
forall p q: R -> R,
forall w : R,
0 < w ->
0 <= h * w <= 2 ->
(forall t1 t2: R,
Harmonic_osc_system p q w /\
k_differentiable p 4 t1 t2 /\
k_differentiable q 3 t1 t2)  ->
forall t0 : R,
Rprod_norm (Rprod_minus (p (t0 + h), w * q (t0 + h)) 
 (leapfrogR (p t0) (w * q t0) w 1))
 <=  (h * w)^3 * Rprod_norm( p (0), w * q(0)).
Proof.
intros.
pose proof local_truncation_error_norm_aux 
  p q w H1 t0 as (t1 & t2 & A & B & C).
eapply Rle_trans.
apply C.
specialize (H1 t1 t2) as (D & E).
eapply Rle_trans.
replace (w * h ^ 3 / INR (fact 3) * Derive_n q 3 t1)
with (h ^ 3 / INR (fact 3) * w * Derive_n q 3 t1) by nra.
apply Harm_sys_norm_bound; try nra; auto. 
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



Definition method_norm3 h w :=  (1 + h * w - 0.5 * h^2 * w^2).


Lemma global_error_aux1: 
forall p1 q1 p2 q2 w: R,
Rprod_norm (Rprod_minus 
  (leapfrogR p1 (w * q1) w 1)  
  (leapfrogR p2 (w * q2) w 1)) = 
Rprod_norm (leapfrogR 
    (fst(Rprod_minus (p1, (w * q1)) 
      (p2,(w * q2))))
    (snd(Rprod_minus (p1, (w * q1)) 
      (p2,(w * q2)))) w 1).
Proof.
intros.
unfold Rprod_norm, Rprod_minus, leapfrogR, F, 
  fst, snd.  f_equal. 
nra.
Qed.


Lemma subordinate_norm3: 
forall p1 q1 p2 q2 w: R,
Rprod_norm (Rprod_minus 
  (leapfrogR p1 (w * q1) w 1)  
  (leapfrogR p2 (w * q2) w 1)) <= 
method_norm3 h w * Rprod_norm (Rprod_minus (p1, w * q1) (p2, w *q2)) . 
Proof.
intros.
rewrite global_error_aux1.
unfold Rprod_norm, method_norm. 
unfold Rprod_minus, leapfrogR, F, 
  fst, snd, method_norm3.
match goal with |- context[?a <= ?b * sqrt(?x)] =>
replace (b * sqrt x) with (sqrt(b^2 * x)) 
end.
apply sqrt_le_1_alt.
set (p:=(p1 - p2)).
set (q:=(w * q1 - w * q2) ).
Admitted.

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


Definition error_sum n h w: R:=
 match n with 
  | 0 => 0
  | S n' => sum_f 0 n' (fun m => (method_norm3 h w) ^ m )
end
.

Lemma error_sum_aux n h w:
  error_sum n h w + (method_norm3 h w)^n = error_sum (S n) h w.
Proof.
intros.
induction n. 
+  simpl. unfold sum_f. simpl. nra.
+ unfold error_sum.
rewrite sum_f_n_Sm; auto.
apply Nat.le_0_l.
Qed.

Lemma error_sum_aux2 n h w:
  method_norm3 h w * error_sum n h w + 1  = error_sum (S n) h w.
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


Theorem global_truncation_error_sum : 
forall p q: R -> R,
forall w : R,
0 < w ->
0 <= h * w <= 2 ->
(forall t1 t2: R,
Harmonic_osc_system p q w/\
k_differentiable p 4 t1 t2 /\
k_differentiable q 3 t1 t2)  ->
forall n : nat, 
forall t0 : R,
Rprod_norm (Rprod_minus (p (t0 + INR n * h), w * q (t0 + INR n * h)) 
(leapfrogR (p t0) (w * q t0) w n))
 <=   h^3 * w^3 * Rprod_norm( p 0, w * q 0) * error_sum n h w.
Proof.
intros.
induction n.
+ unfold Rprod_minus, Rprod_norm, leapfrogR, fst, snd, error_sum.
replace (t0 + INR 0 * h) with t0 by (simpl; nra).
rewrite Rmult_0_r.
match goal with |-context[sqrt ?a <= _] =>
replace a with 0 by nra
end.
rewrite sqrt_0; nra.
+ rewrite nsteps_lem.
set (phi1:= leapfrogR (p (t0 + INR ( n) * h)) (w * q (t0 + INR ( n) * h)) w 1) in *.
set (phi2:=  
leapfrogR (fst(leapfrogR (p t0) (w * q t0) w ( n))) 
  (snd (leapfrogR (p t0) (w * q t0) w ( n))) w 1).
eapply Rle_trans.
match goal with |- context[ ?a <= ?b] =>
  replace a with (Rprod_norm 
  (Rprod_plus (Rprod_minus (p (t0 + INR (S n) * h ), w  * q (t0 + INR (S n) * h)) phi1)
(Rprod_minus phi1 phi2))) by (symmetry; apply Rprod_norm_plus_minus_eq)
end.
apply Rprod_triang_ineq.
pose proof local_truncation_error_norm p q w H H0 H1 (t0 + INR n * h).
fold phi1 in H2.
eapply Rle_trans.
eapply Rplus_le_compat_r.
rewrite S_INR.
replace (t0 + (INR n + 1) * h) with (t0 + INR n * h + h) by nra.
apply H2.
eapply Rle_trans.
eapply Rplus_le_compat_l.
subst phi1 phi2.
pose proof subordinate_norm3 (p (t0 + INR ( n) * h)) ( q (t0 + INR ( n) * h)) 
(fst(leapfrogR (p t0) (w * q t0) w ( n))) 
(1/w *snd(leapfrogR (p t0) (w * q t0) w ( n))) w.
replace 
(w * (1 / w * snd (leapfrogR (p t0) (w * q t0) w ( n))))
with 
(snd (leapfrogR (p t0) (w * q t0) w ( n))) in H3.
apply H3.
field_simplify. nra.
nra.
eapply Rle_trans.
eapply Rplus_le_compat_l.
eapply Rmult_le_compat_l; try (unfold h;nra).

unfold method_norm3; nra.

apply IHn. (*lemmas about sums*)
set 
  (aa:=sqrt 5 * 0.25 * w ^ 3 * 
  Rprod_norm (p 0, w * q 0) * h ^ 3).
rewrite <- error_sum_aux2.
nra.
Qed.

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
forall w : R,
0 < w ->
0 < h * w < 2 ->
(forall t1 t2: R,
Harmonic_osc_system p q w/\
k_differentiable p 4 t1 t2 /\
k_differentiable q 3 t1 t2)  ->
forall n : nat, 
forall t0 : R,
Rprod_norm (Rprod_minus (p (t0 + INR n * h), w * q (t0 + INR n * h)) 
(leapfrogR (p t0) (w * q t0) w ( n)))
 <= 
h ^ 3 * w ^ 3 * Rprod_norm( p (0), w * q(0)) * (1-(method_norm3 h w)^ n)/(1- (method_norm3 h w)).
Proof.
intros.
assert (method_norm3 h w <> 1).
+ unfold method_norm3. nra.
+ induction n.
++ unfold Rprod_minus, Rprod_norm. simpl.
rewrite Rmult_0_l. rewrite Rplus_0_r. 
repeat rewrite Rmult_1_r. 
replace (p t0 - p t0) with 0 by nra.
replace (w * q t0 - w * q t0) with 0 by nra.
field_simplify. rewrite Rmult_0_l. 
replace (0+0) with 0 by nra.
rewrite sqrt_0. nra. nra.
++  pose proof geo_series_closed_form (method_norm3 h w) n.
specialize (H3 H2); clear H2.
assert (BND: 0 <= h * w <= 2) by nra.
pose proof 
  global_truncation_error_sum p q w H BND H1 (S n) t0.
eapply Rle_trans. apply H2.
unfold error_sum.
rewrite H3. 
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
Search (ex_derive_n).
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


Lemma t_exp_norm_A w n: 
  0 < w -> 
  0 < h * w < 2 ->
  let x:= h * w * (1 - 0.5 * h * w) in 
  exists n1,
  0 < n1 < x /\
  (method_norm3 h w )^n = 
  1 +  INR n * x + 0.5 * INR n * (INR (n -1)) * x^2 * (1 +  n1)^(n-2).
Proof. 
intros.
assert (Hx: 0 < x).
+ unfold x. nra.
+ pose proof  binomial_approx_aux n x as P. 
pose proof Taylor_Lagrange (fun x =>  (1+x)^n ) 1 0  x Hx P 
  as (zeta & B & C).
exists zeta.
repeat (split; try apply B).
replace ((method_norm3 h w)^n) with 
  ( (1+x)^n ). rewrite C. unfold sum_f_R0.
rewrite Rminus_0_r.
f_equal. f_equal.
simpl. field_simplify. 
rewrite Rplus_0_r.
apply pow1.
simpl. 
repeat match goal with |- context [Derive (?f) ?var] =>
auto_derive_fun f; unfold F;
assert True as TR by auto;
let H := fresh "H" in
          intro H;
let H1 := fresh "H" in
pose proof (H var TR) as H1; clear TR; clear H ;
apply is_derive_unique in H1;  rewrite H1; clear H1
end.
field_simplify.
rewrite Rplus_0_r.
rewrite pow1. nra.

unfold Derive_n.
replace ((fun x0 : R => Derive (fun x1 : R => (1 + x1) ^ n) x0))
with ((fun x0 : R => INR n * (1+x0)^Init.Nat.pred n)).
repeat match goal with |- context [Derive (?f) ?var] =>
auto_derive_fun f; unfold F;
assert True as TR by auto;
let H := fresh "H" in
          intro H;
let H1 := fresh "H" in
pose proof (H var TR) as H1; clear TR; clear H ;
apply is_derive_unique in H1;  rewrite H1; clear H1
end.
rewrite Rmult_1_l.
replace (Init.Nat.pred (Init.Nat.pred n)) with
(n - 2)%nat.
replace ((Init.Nat.pred n)) with (n-1)%nat.
simpl; nra.
lia.
lia.

apply functional_extensionality. intros.

repeat match goal with |- context [Derive (?f) ?var] =>
auto_derive_fun f; unfold F;
assert True as TR by auto;
let H := fresh "H" in
          intro H;
let H1 := fresh "H" in
pose proof (H var TR) as H1; clear TR; clear H ;
apply is_derive_unique in H1;  rewrite H1; clear H1
end.
rewrite Rmult_1_l.
auto.

unfold method_norm3, x. 
f_equal. nra.
Qed.
 

Theorem global_error_linear:
forall p q: R -> R,
forall w : R,
0< w ->
0 < h * w < 2 ->
(forall t1 t2: R,
Harmonic_osc_system p q w/\
k_differentiable p 4 t1 t2 /\
k_differentiable q 3 t1 t2)  ->
forall n : nat,
forall t0 : R,
exists n1: R,
let x:= ((method_norm3 h w) - 1) in 
  0 < n1 < x /\
Rprod_norm (Rprod_minus (p (t0 + INR n * h), w * q (t0 + INR n * h)) 
(leapfrogR (p t0) (w * q t0) w n)) <= 
(h ^ 3 * w ^ 3 * Rprod_norm( p (0), w * q(0))) *
((INR n * x + 0.5 * INR n * (INR (n -1)) * x^2 * (1 +  n1)^(n-2)) / 
(h * w * (1 - 0.5 * h * w))).
Proof.
intros.
pose proof t_exp_norm_A w n H H0.
destruct H2 as (n1 & A).
destruct A as (B & C).
replace (method_norm3 h w -1) with 
(h * w * (1 - 0.5 * h * w)) by (unfold method_norm3;
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

rewrite H2; rewrite H3.
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
