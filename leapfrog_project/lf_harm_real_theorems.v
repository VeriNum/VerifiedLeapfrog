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


Definition Rprod_minus (x y : R * R) : R * R :=
  (Rminus (fst x) (fst y), Rminus (snd x) (snd y)).

Definition Rprod_plus (x y : R * R) : R * R :=
  (Rplus (fst x) (fst y), Rplus (snd x) (snd y)).

Definition Rprod_norm (x : R * R) : R  :=
  sqrt ( (fst x) ^ 2 +  (snd x) ^ 2).

Lemma Rprod_triang_ineq x y: 
Rprod_norm ( Rprod_plus x y) <= Rprod_norm x + Rprod_norm y.
Proof.
destruct x, y.
unfold Rprod_plus, Rprod_norm, fst, snd.
assert ((r + r1) ^ 2 + (r0 + r2) ^ 2 <= 
  (sqrt (r ^ 2 + r0 ^ 2) + sqrt (r1 ^ 2 + r2 ^ 2))^2).
replace ((sqrt (r ^ 2 + r0 ^ 2) + sqrt (r1 ^ 2 + r2 ^ 2)) ^ 2)
with (r^2 + r0^2 + r1^2 + r2^2 + 2 * sqrt (r ^ 2 + r0 ^ 2)* sqrt (r1 ^ 2 + r2 ^ 2))
by 
(simpl; field_simplify; 
repeat rewrite pow2_sqrt; repeat nra).
simpl. field_simplify.
repeat rewrite Rplus_assoc.
apply Rplus_le_compat_l.
rewrite Rplus_comm.
repeat rewrite Rplus_assoc.
apply Rplus_le_compat_l.
apply Rplus_le_compat_l.
rewrite Rplus_comm.
repeat rewrite Rplus_assoc.
apply Rplus_le_compat_l.
repeat rewrite Rmult_assoc.
replace (2 * (r * r1) + 2 * (r0 * r2)) with
(2 * ((r * r1) + (r0 * r2))) by nra.
apply Rmult_le_compat_l; try nra.
repeat rewrite Rmult_1_r. 
apply sqrt_cauchy.
apply sqrt_le_1 in H.
rewrite sqrt_pow2 in H; auto.
apply sqrt_plus_pos.
apply sqr_plus_pos.  
rewrite <- Rsqr_pow2.
apply Rle_0_sqr.
Qed.

Lemma Rprod_norm_plus_minus_eq x y z:
Rprod_norm ( Rprod_minus x y) = Rprod_norm ( Rprod_plus (Rprod_minus x z) (Rprod_minus z y)).
Proof.
intros.
destruct x, y, z.
unfold Rprod_plus, Rprod_minus, Rprod_norm, fst, snd.
f_equal.
nra.
Qed.

Definition Harmonic_osc_system p q w :=
forall t,
Derive_n q 1 t  = p t /\
Derive_n q 2 t = (fun y => F (q y) w) t /\
Rprod_norm ( p(t), w * q(t)) <= Rprod_norm( p (0), w * q(0))
.

Lemma Rnorm_pos x:
0 <= Rprod_norm x.
Proof.
unfold Rprod_norm.
apply sqrt_pos.
Qed.

Lemma Harm_sys_derive_eq p q w: 
Harmonic_osc_system p q w-> 
forall t,
Derive_n q 3 t  = - w ^2 * p t /\
Derive_n p 2 t  = Derive_n q 3 t /\ 
Derive_n p 3 t  = w ^4 * q t.
Proof.
unfold Harmonic_osc_system .
intros.
specialize (H t) as (A & B & C).
split.
Admitted.


Lemma Harm_sys_norm_bound p q w:
forall a b t1 t2 t3,
Harmonic_osc_system p q w-> 
0 <= a ->
0 <= b ->
Rprod_norm (a * Derive_n p 3 t2 - b* w ^ 4 * q(t3), a * w * Derive_n q 3 t1 ) <= 
sqrt 5 * (Rmax a b) * (w ^ 3) * Rprod_norm( p (0), w * q(0)).
Proof.
intros.
unfold Harmonic_osc_system in H.
pose proof Harm_sys_derive_eq p q w H t1 as (A & _ & _).
pose proof Harm_sys_derive_eq p q w H t2 as (_ & _ & C2).
rewrite A, C2. clear A C2.
pose proof (H t1) as A1; destruct A1 as (_ & _ &C).
pose proof (H t2) as A1; destruct A1 as (_ & _ &C2).
specialize (H t3). destruct H as (_ & _ & C3).
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
apply H.
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
apply H2.
eapply Rle_trans.
apply sqrt_le_1_alt. 
eapply Rplus_le_compat_r.
eapply Rplus_le_compat_r.
eapply Rplus_le_compat_l.
eapply Rmult_le_compat_l; try nra.
apply H3.
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
replace (w ^ 2 * q t2 ^ 2) with ((w * q t2) ^ 2) in H2 by nra.
apply Rabs_pos_le in H2; try nra; auto.
repeat rewrite Rabs_sqr_le in H2.
apply sqrt_le_1_alt in H2.
rewrite sqrt_pow2 in H2; try (apply Rabs_pos).
apply H2.
rewrite <- Rabs_mult. 
replace (w ^ 2 * q t3 ^ 2) with ((w * q t3) ^ 2) in H3 by nra.
apply Rabs_pos_le in H3; try nra; auto.
repeat rewrite Rabs_sqr_le in H3.
apply sqrt_le_1_alt in H3.
rewrite sqrt_pow2 in H3; try (apply Rabs_pos).
apply H3.
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
f_equal. f_equal. nra.
admit. (* omega positive*) 
repeat rewrite Rabs_pos_eq; try nra; try unfold c; try nra.
Admitted.


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


Theorem local_truncation_error_aux:
forall p q: R -> R,
forall w : R,
(forall t1 t2: R,
Harmonic_osc_system p q w/\
k_differentiable p 3 t1 t2 /\
k_differentiable q 3 t1 t2)  ->
forall t0 : R,
exists t1 t2: R,
t0 < t1 < t0 + h /\
t0 < t2 < t0 + h /\
 ((w * q (t0 + h) - (snd(leapfrogR (p t0) (w * q t0) w 1))) = 
     (w * h^3 * (1 / INR (fact 3) * Derive_n q 3 t1))) /\
 ((p (t0 + h) - (fst(leapfrogR (p t0) (w * q t0) w 1))) = 
    ( h^3 * (1 / INR (fact 3) * Derive_n p 3 t2 - w^4 * (1/4) * (q t0)))) . 
Proof.
intros.
assert (t0 < t0 + h) as LT by (unfold h; nra).
specialize (H  t0 (t0 +h)).
destruct H as (HSY & KP & KQ); unfold k_differentiable in *.
pose proof Taylor_Lagrange q 2 t0 (t0 + h) LT KQ as TLRq. 
pose proof Taylor_Lagrange p 2 t0 (t0 + h) LT KP as TLRp.
destruct TLRq as (t1 & A & B). 
destruct TLRp as (t2 & C & D).
replace (t0 + h - t0) with h in * by nra.
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
unfold leapfrogR, F, fst, snd.
unfold_factorials.
Qed.


Theorem local_truncation_error_norm_aux:
forall p q: R -> R,
forall w : R,
(forall t1 t2: R,
Harmonic_osc_system p q w /\
k_differentiable p 3 t1 t2 /\
k_differentiable q 3 t1 t2)  ->
forall t0 : R,
exists t1 t2: R,
t0 < t1 < t0 + h /\
t0 < t2 < t0 + h /\
Rprod_norm (Rprod_minus (p (t0 + h), w * q (t0 + h)) 
  (leapfrogR (p t0) (w * q t0) w 1))
 <= Rprod_norm (
     ( (1 / INR (fact 3) * Derive_n p 3 t2 - 1 / 4 * w^4 * q t0)),
 w * (1 / INR (fact 3) * Derive_n q 3 t1)) * h^3.
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
set (c:=((w * 1 / INR (fact 3) * Derive_n q 3 t1) ^ 2 +
   (1 / INR (fact 3) * Derive_n p 3 t2 - w^4* 1 / 4 * q t0) ^ 2)).
match goal with |-context[sqrt(?a) <= ?b] => 
replace a with (c * h^6) by (unfold c; nra)
end. 
apply Req_le.
rewrite sqrt_mult_alt.
f_equal.
unfold c. 
f_equal; nra.
replace (h^6) with ((h^3)^2) by nra.
rewrite sqrt_pow2; nra.
unfold c. 
apply sqr_plus_pos.
Qed.

Theorem local_truncation_error_norm:
forall p q: R -> R,
forall w : R,
(forall t1 t2: R,
Harmonic_osc_system p q w /\
k_differentiable p 3 t1 t2 /\
k_differentiable q 3 t1 t2)  ->
forall t0 : R,
Rprod_norm (Rprod_minus (p (t0 + h), w * q (t0 + h)) 
 (leapfrogR (p t0) (w * q t0) w 1))
 <= 
sqrt 5 * 0.25 * w^3 * Rprod_norm( p (0), w * q(0)) * h^3.
Proof.
intros.
pose proof local_truncation_error_norm_aux 
  p q w H t0 as (t1 & t2 & A & B & C).
eapply Rle_trans.
apply C.
specialize (H t1 t2) as (H & H2).
apply Rmult_le_compat_r. try unfold h; try nra.
eapply Rle_trans.
replace (w * (1 / INR (fact 3) * Derive_n q 3 t1)) with 
  ((1 / INR (fact 3)) * w * Derive_n q 3 t1) by nra.
eapply Harm_sys_norm_bound; auto; unfold_factorials. 
replace (Rmax (1 / INR (fact 3)) (1 / 4))
with (1/4); try nra.
symmetry.
apply Rmax_right.
unfold_factorials.
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


Lemma global_error_aux: 
forall p1 q1 p2 q2 w: R,
Rprod_norm (Rprod_minus 
  (leapfrogR p1 (w * q1) w 1)  
  (leapfrogR p2 (w * q2) w 1)) <= 
method_norm h w * Rprod_norm (Rprod_minus (p1, w * q1) (p2, w *q2)) . 
Proof.
intros.
rewrite global_error_aux1.
unfold Rprod_norm, method_norm. 
unfold Rprod_minus, leapfrogR, F, 
  fst, snd, method_norm.
field_simplify.
rewrite <- sqrt_mult_alt.
match goal with |- context [?a <= sqrt(?b)/?c] =>
replace (sqrt(b)/c) with (sqrt(b/c^2)) by admit
end.
apply sqrt_le_1_alt.
assert ( h* w<= 1) by admit.
Admitted.



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
admit. admit. (* ! *)
++ admit.
+ 
induction n.
++ unfold sum_f. simpl. nra.
++  rewrite sum_f_n_Sm. rewrite IHn.
rewrite sum_f_n_Sm. field_simplify. nra. 
admit. admit. (* ! *)
Admitted.

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
admit.
admit.
Admitted.



Theorem global_truncation_error_sum : 
forall p q: R -> R,
forall w : R,
(forall t1 t2: R,
Harmonic_osc_system p q w/\
k_differentiable p 3 t1 t2 /\
k_differentiable q 3 t1 t2)  ->
forall n : nat, 
forall t0 : R,
Rprod_norm (Rprod_minus (p (t0 + INR (S n) * h), w * q (t0 + INR (S n) * h)) 
(leapfrogR (p t0) (w * q t0) w (S n)))
 <= 
(sqrt 5 * 0.25 * w^3 * Rprod_norm( p (0), w * q(0)) * h^3) * 
  sum_f 0 n (fun m => (method_norm h w) ^ m ).
Proof.
intros.
induction n.
+ 
replace (INR 1 * h) with h.
pose proof local_truncation_error_norm p q w H t0.
eapply Rle_trans.
apply H0.
apply Req_le. unfold sum_f; simpl; nra. admit.
+ set (yy:=(S n)).
rewrite ?S_INR. subst yy. rewrite nsteps_lem.
replace ((t0 + (INR (S n) + 1) * h)) with
(t0 + (INR (S n))*h + h) by nra.
set (phi1:= leapfrogR (p (t0 + INR (S n) * h)) (w * q (t0 + INR (S n) * h)) w 1) in *.
set (phi2:=  
leapfrogR (fst(leapfrogR (p t0) (w * q t0) w (S n))) 
  (snd (leapfrogR (p t0) (w * q t0) w (S n))) w 1).
eapply Rle_trans.
match goal with |- context[ ?a <= ?b] =>
  replace a with (Rprod_norm 
  (Rprod_plus (Rprod_minus (p (t0 + INR (S n) * h + h), w  * q (t0 + INR (S n) * h + h)) phi1)
(Rprod_minus phi1 phi2))) by (symmetry; apply Rprod_norm_plus_minus_eq)
end.
apply Rprod_triang_ineq.
pose proof local_truncation_error_norm p q w H (t0 + INR (S n) * h).
fold phi1 in H0.
eapply Rle_trans.
eapply Rplus_le_compat_r.
apply H0.
eapply Rle_trans.
eapply Rplus_le_compat_l.
subst phi1 phi2.
pose proof global_error_aux (p (t0 + INR (S n) * h)) ( q (t0 + INR (S n) * h)) 
(fst(leapfrogR (p t0) (w * q t0) w (S n))) 
(1/w *snd(leapfrogR (p t0) (w * q t0) w (S n))) w.
replace 
(w * (1 / w * snd (leapfrogR (p t0) (w * q t0) w (S n))))
with 
(snd (leapfrogR (p t0) (w * q t0) w (S n))) in H1.
apply H1.
field_simplify. nra.
admit (* w positive *). 
eapply Rle_trans.
eapply Rplus_le_compat_l.
eapply Rmult_le_compat_l; try (unfold h;nra).
admit. (*method norm positive *)
apply IHn. (*lemmas about sums*)
set 
  (aa:=sqrt 5 * 0.25 * w ^ 3 * 
  Rprod_norm (p 0, w * q 0) * h ^ 3).
rewrite Rmult_comm.
rewrite Rmult_assoc.
rewrite Rmult_comm.
rewrite sum_pow_mult_r.
rewrite sum_pow_first.
field_simplify.
nra.
Admitted.

Theorem geo_series_closed_form:
forall r k ,
r <> 1 ->
sum_f 0 k (fun m => r ^ m ) = (1-(r^(S k)))/(1-r).
Proof.
intros.
induction k.
+ unfold sum_f. simpl. field_simplify. nra. admit.
+ rewrite sum_f_n_Sm .
++ rewrite IHk.
match goal with|- context [?a/?aa + ?b = _] =>
replace  b with 
((r ^ S k)*(1-r)/(1-r))
end.
field_simplify; try nra.
replace  (- r ^ S k * r) with
(- r ^ S (S k) ) by admit.
nra.
field_simplify; try nra.
Admitted.

Theorem global_truncation_error: 
forall p q: R -> R,
forall w : R,
(forall t1 t2: R,
Harmonic_osc_system p q w/\
k_differentiable p 3 t1 t2 /\
k_differentiable q 3 t1 t2)  ->
forall n : nat, 
forall t0 : R,
Rprod_norm (Rprod_minus (p (t0 + INR n * h), w * q (t0 + INR n * h)) 
(leapfrogR (p t0) (w * q t0) w n))
 <= 
(sqrt 5 * 0.25 * w^3 * Rprod_norm( p (0), w * q(0)) * h^3) * 
  (1-(method_norm2 h w)^n)/(1- (method_norm2 h w)).
Proof.
intros.
pose proof geo_series_closed_form (method_norm2 h w) (n-1).
assert (method_norm2 h w <> 1) by admit.
specialize (H0 H1); clear H1.
replace 
(sqrt 5 * 0.25 * w ^ 3 * Rprod_norm (p 0, w * q 0) * h ^ 3 *
(1 - method_norm2 h w ^ n) / (1 - method_norm2 h w))
with (
sqrt 5 * 0.25 * w ^ 3 * Rprod_norm (p 0, w * q 0) * h ^ 3 *
(sum_f 0 (n-1) (fun m : nat => method_norm2 h w ^ m))).
rewrite method_norms_eq.
pose proof global_truncation_error_sum p q w H (n-1) t0.
replace ((S (n - 1))) with n in * by admit.
apply H1.
replace ((S (n - 1))) with n in * by admit.
rewrite H0. nra.
Admitted.


Theorem global_error_linear:
forall p q: R -> R,
forall w : R,
(forall t1 t2: R,
Harmonic_osc_system p q w/\
k_differentiable p 3 t1 t2 /\
k_differentiable q 3 t1 t2)  ->
forall n : nat,
let x:= ((method_norm h w) ^2 - 1) in 
INR n * x <= 1/10^2 -> 
(method_norm2 h w)^n = (1 + INR n/2 * x) ->
(method_norm2 h w)   = (1 + 1/2 * x) ->
forall t0 : R,
Rprod_norm (Rprod_minus (p (t0 + INR n * h), w * q (t0 + INR n * h)) 
(leapfrogR (p t0) (w * q t0) w n))
 <= 
(sqrt 5 * 0.25 * w^3 * Rprod_norm( p (0), w * q(0)) * h^3) * INR n.
Proof.
intros.
eapply Rle_trans.
apply global_truncation_error.
apply  H.
rewrite H1.
rewrite H2.
apply Req_le.
Admitted.


Close Scope R_scope. 
