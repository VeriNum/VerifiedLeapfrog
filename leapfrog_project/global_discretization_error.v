From Coq Require Import ZArith Reals Psatz.
From Coq Require Import Arith.Arith.
Require Import real_model real_lemmas 
  harmonic_oscillator_system local_discretization_error matrix_analysis.
From Coquelicot Require Import Coquelicot.
Set Bullet Behavior "Strict Subproofs". 

Require Import IntervalFlocq3.Tactic.


Theorem global_truncation_error_sum : 
  forall p q: R -> R,
  forall t0 T: R,
  Harmonic_oscillator_system p q 1 -> 
  forall n : nat, 
  let tn:= t0 + INR n * h  in 
  tn <= T -> 
  ∥ (p tn, q tn) - (iternR (p t0, q t0) h n)∥
    <= h^3 * ∥(p t0,  q t0)∥ * error_sum σb n.
Proof.
intros ? ? ? ? HSY; intros. 
induction n.
-
subst tn. 
rewrite Rmult_0_l. rewrite Rmult_0_r.
rewrite Rplus_0_r. unfold Rprod_minus, Rprod_norm, iternR, fst, snd.
repeat rewrite Rminus_eq_0. rewrite pow_i. rewrite Rplus_0_r.
rewrite sqrt_0. nra. lia.
-
rewrite step_iternR. 
cbv zeta in IHn.
subst tn.
rewrite S_INR in H.
assert (HSN: t0 + INR n * h <= T).
+
assert (t0 + INR n * h <= t0 + (INR n + 1) * h).
apply Rplus_le_compat_l.
unfold h; try nra.
eapply Rle_trans. apply H0. apply H.
+
specialize (IHn HSN).
set (phi1:= leapfrog_stepR h (p (t0 + INR  n * h), q (t0 + INR  n * h))) in *.
set (phi2:=  
leapfrog_stepR h (iternR (p t0, q t0) h n)).
eapply Rle_trans.
match goal with |- context[ ?a <= ?b] =>
  replace a with (Rprod_norm 
  (Rprod_plus (Rprod_minus (p (t0 + INR (S n) * h ),  q (t0 + INR (S n) * h)) phi1)
(Rprod_minus phi1 phi2))) by (symmetry; apply Rprod_norm_plus_minus_eq)
end.
apply Rprod_triang_ineq.
assert (HBND2: 0 < ω*h <= 4) by (unfold ω, h; nra).
field_simplify in H.
assert (t0 <= t0 + INR n * h).
apply Rle_minus_l_2.
rewrite Rminus_eq_0.
apply Rle_mult; try (unfold h ; nra). apply pos_INR.
clear H0.
pose proof local_truncation_error p q t0 (t0 + INR n * h) h HBND2 HSY as H0.
fold phi1 in H0.
eapply Rle_trans.
eapply Rplus_le_compat_r.
rewrite S_INR.
replace (t0 + (INR n + 1) * h) with (t0 + INR n * h + h) by nra.
apply H0; auto.
eapply Rle_trans.
eapply Rplus_le_compat_l.
subst phi1 phi2.
pose proof leapfrog_minus_args
(p (t0 + INR n * h), q (t0 + INR n * h))
(iternR (p t0, q t0) h n) h as H1.
rewrite H1.
pose proof (method_norm_bound) as H2.
apply H2; rewrite Rmult_1_l; auto. 
unfold fst at 1.
eapply Rle_trans.
eapply Rplus_le_compat_l.
eapply Rmult_le_compat_l; try (unfold σb; nra).
apply IHn. 
set 
  (aa:=h ^ 3 *  ∥ (p t0, q t0) ∥).
replace (aa + σb * (aa * error_sum (σb ^ n) n))
with 
(aa + aa * σb * error_sum (σb ^ n) n) by nra.
rewrite <- error_sum_aux2.
clearbody aa.
field_simplify.
apply Req_le.
nra.
Qed.

Close Scope R_scope. 
