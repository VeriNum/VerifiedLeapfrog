(* This file contains proofs of the floating point properties:
local and global error, finiteness *)

From vcfloat Require Import FPLang FPLangOpt RAux Rounding Reify Float_notations Automate.
Require Import Interval.Tactic.
Import Binary.
Import List ListNotations.
Set Bullet Behavior "Strict Subproofs".

Require Import lf_harm_float lf_harm_real real_lemmas lf_harm_real_theorems lf_harm_lemmas.


Open Scope R_scope.

Section WITHNANS.


Context {NANS: Nans}.

Import Interval.Tactic.

Print q'.


Lemma prove_roundoff_bound_q:
  forall q p : ftype Tsingle,
  prove_roundoff_bound leapfrog_bmap (leapfrog_vmap q p) q' 
    (/ 4068166).
Proof.
intros.
prove_roundoff_bound.
- abstract (prove_rndval; interval).
- prove_roundoff_bound2.
 match goal with |- Rabs ?a <= _ => field_simplify a end.
 interval.
Qed.

Lemma prove_roundoff_bound_p:
  forall q p : ftype Tsingle,
  prove_roundoff_bound leapfrog_bmap (leapfrog_vmap q p) p' 
   (/7662000).
Proof.
intros.
prove_roundoff_bound.
- abstract (prove_rndval; interval).
- prove_roundoff_bound2.
match goal with |- Rabs ?a <= _ => field_simplify a end.
interval.
Qed.


Lemma prove_roundoff_bound_q_implies:
  forall q p : ftype Tsingle,
  boundsmap_denote leapfrog_bmap (leapfrog_vmap q p)-> 
  Rabs (FT2R (fval (env_ (leapfrog_vmap q p)) q') - rval (env_ (leapfrog_vmap q p)) q') <= (/ 4068166)
.
Proof.
intros.
pose proof prove_roundoff_bound_q q p.
unfold prove_roundoff_bound in H0. 
specialize (H0 H).
unfold roundoff_error_bound in H0; auto. 
Qed.


Lemma prove_roundoff_bound_p_implies:
  forall q p : ftype Tsingle,
  boundsmap_denote leapfrog_bmap (leapfrog_vmap q p)-> 
  Rabs (FT2R (fval (env_ (leapfrog_vmap q p)) p') - rval (env_ (leapfrog_vmap q p)) p') <= (/7662000)
.
Proof.
intros.
pose proof prove_roundoff_bound_p q p.
unfold prove_roundoff_bound in H0. 
specialize (H0 H).
unfold roundoff_error_bound in H0; auto. 
Qed.


Lemma init_norm_eq :
  ∥  (FT2R p_init, FT2R q_init) ∥ = 1 . 
Proof.
intros.
replace 1 with (sqrt 1).
replace (FT2R q_init) with 1.
simpl. unfold Rprod_norm, fst, snd.
f_equal; nra.
unfold FT2R, q_init. 
unfold Rprod_norm, fst, snd.
 cbv [B2R]. simpl. cbv [Defs.F2R IZR IPR]. simpl;
field_simplify; nra.
apply sqrt_1.
Qed.


Hypothesis iternR_bnd:
  forall p q n,
  ∥iternR (p,q) h n∥ <= (sqrt 2 * ∥(p,q)∥).



Lemma init_norm_bound :
  forall n : nat,
  ∥ iternR (FT2R p_init, FT2R q_init) h n ∥ <= 1.5. 
Proof.
intros.
specialize (iternR_bnd (FT2R p_init) (FT2R q_init) n).
pose proof init_norm_eq.
rewrite H in iternR_bnd; clear H.
rewrite Rmult_1_r in iternR_bnd.
interval.
Qed.


Lemma roundoff_norm_bound:
  forall p q : ftype Tsingle,
  boundsmap_denote leapfrog_bmap (leapfrog_vmap q p)-> 
  let (pnf, qnf) := FT2R_prod_rev (fval (env_ (leapfrog_vmap q p)) q', fval (env_ (leapfrog_vmap q p)) p') in 
  let (pnr, qnr) := (rval (env_ (leapfrog_vmap q p)) p', rval (env_ (leapfrog_vmap q p)) q') in
  ∥ (pnf, qnf) .- (pnr, qnr)∥ <= ∥(/7662000, / 4068166)∥.
Proof.
intros.
unfold Rprod_minus, FT2R_prod_rev, Rprod_norm, fst, snd.
rewrite <- pow2_abs.
rewrite Rplus_comm.
rewrite <- pow2_abs.
pose proof prove_roundoff_bound_p_implies q p H.
pose proof prove_roundoff_bound_q_implies q p H.
apply sqrt_le_1_alt.
eapply Rle_trans.
apply Rplus_le_compat_r.
apply pow_incr.
split; try (apply Rabs_pos).
apply H1.
eapply Rle_trans. 
apply Rplus_le_compat_l.
apply pow_incr.
split; try (apply Rabs_pos).
apply H0.
nra.
Qed.



Lemma global_error : 
  boundsmap_denote leapfrog_bmap 
  (leapfrog_vmap q_init p_init) ->
  forall n : nat, 
  (n <= 200)%nat -> 
  let vmap_n := (leapfrog_vmap (fst(iternF (q_init,p_init) n)) (snd(iternF (q_init,p_init) n))) in
  let c:= (∥ (/ 7662000, / 4068166) ∥) in 
  let (pr0, qr0) := (FT2R p_init, FT2R q_init) in
  boundsmap_denote leapfrog_bmap vmap_n /\
  ∥(iternR (pr0, qr0) h n) .- FT2R_prod_rev (iternF (q_init,p_init) n) ∥ <= c * error_sum (1 + h) n.
  Proof.
intros.
induction n.
- unfold Rprod_minus. simpl. repeat rewrite Rminus_eq_0.
unfold Rprod_norm, fst, snd. repeat rewrite pow_ne_zero; try lia.
rewrite Rplus_0_r. rewrite sqrt_0.
split.  try nra.
  + apply H.
  + nra. 
- 
match goal with |- context [?A /\ ?B] =>
  assert B; try split; auto
end.
+ 
destruct IHn as (IHbmd & IHnorm); try lia.
rewrite step_iternF; rewrite step_iternR.
pose proof init_norm_bound n.
destruct (iternR (FT2R p_init, FT2R q_init) h n) as (pnr, qnr). 
destruct (iternF (q_init,p_init) n) as (qnf, pnf).
match goal with |- context[∥?a .- ?b∥ <=  _] =>
  let c := (constr:(leapfrog_stepR (FT2R_prod_rev (qnf, pnf)) h)) in
  replace (∥a .- b∥) with (∥ Rprod_plus (a .- c) (c .- b) ∥)
end.
eapply Rle_trans.
apply Rprod_triang_ineq.
rewrite leapfrog_minus_args.
eapply Rle_trans.
apply Rplus_le_compat_l.
assert (BNDn: (n<= 200)%nat) by lia.
assert (∥ Rprod_minus (pnr, qnr) (FT2R_prod_rev (qnf, pnf)) ∥ <=
      (∥ (/ 7662000, / 4068166) ∥) * error_sum (1 + h) n /\ ∥ (pnr, qnr) ∥ <= 1.5).
split; auto.
pose proof (roundoff_norm_bound pnf qnf IHbmd) as BND.
rewrite reflect_reify_p in BND.
rewrite reflect_reify_q in BND.
change (leapfrog_step_q qnf pnf, leapfrog_step_p qnf pnf) with 
  (leapfrog_stepF (qnf, pnf)) in BND.
rewrite rval_correct_q in BND. 
rewrite rval_correct_p in BND.
change ((fst (leapfrog_stepR (FT2R_prod (pnf, qnf)) h),
         snd (leapfrog_stepR (FT2R_prod (pnf, qnf)) h))) with 
(leapfrog_stepR (FT2R_prod (pnf, qnf)) h) in BND.
destruct (FT2R_prod_rev (leapfrog_stepF (qnf, pnf))). 
rewrite Rprod_minus_comm in BND. 
apply BND.  
destruct (Rprod_minus (pnr, qnr) (FT2R_prod_rev (qnf, pnf))).
assert (0 < h <= 2) as Hh by (unfold h; nra).
pose proof (method_norm_bounded r r0 h Hh) as BND.
eapply Rle_trans.
apply Rplus_le_compat_r.
apply BND. 
eapply Rle_trans.
apply Rplus_le_compat_r.
apply Rmult_le_compat_l; try (unfold h; nra).
assert (BNDn: (n<= 200)%nat) by lia.
apply IHnorm. 
replace ((1 + h) * (c * error_sum (1 + h) n) + c)
with
(c * ((1 + h) * (error_sum (1 + h) n) + 1)) by nra.
rewrite <- error_sum_aux2; unfold c; nra.
symmetry. apply Rprod_norm_plus_minus_eq.
+ destruct IHn as (IHbmd & IHnorm); try lia.
apply itern_implies_bmd; try lia; auto; split; auto.
pose proof init_norm_bound (S n); auto.
Qed. 



Theorem total_error: 
  forall pt qt: R -> R,
  forall n : nat, 
  (n <= 200)%nat ->
  let t0 := 0 in
  let tn := t0 + INR n * h in
  let w  := 1 in
  Harmonic_oscillator_system pt qt w t0 (FT2R p_init) (FT2R q_init) ->
  let c:= (∥ (/ 7662000, / 4068166) ∥) / h in 
  ∥ (pt tn, qt tn) .- (FT2R_prod_rev (iternF (q_init,p_init) n)) ∥ <=  (h^2  + c) * ((1 + h) ^ n - 1) .
Proof.
assert (BMD: boundsmap_denote leapfrog_bmap (leapfrog_vmap q_init p_init)) by
apply bmd_init.
intros ? ? ? ? ? ? ? Hsys ; simpl.
match goal with |- context[?A <= ?B] =>
replace A with
  (∥ ((pt (t0 + INR n * h), qt (t0 + INR n * h)) .- (iternR (FT2R p_init, FT2R q_init) h n)) .+
((iternR (FT2R p_init, FT2R q_init) h n) .- (FT2R_prod_rev (iternF (q_init,p_init) n))) ∥)
end.
assert (HSY: Harmonic_oscillator_system pt qt 1 t0 (FT2R p_init) (FT2R q_init)) by auto.
unfold Harmonic_oscillator_system in Hsys.
destruct Hsys as (A & B & C).
eapply Rle_trans.
apply Rprod_triang_ineq.
eapply Rle_trans.
apply Rplus_le_compat_l.
apply global_error; auto.
eapply Rle_trans.
apply Rplus_le_compat_r.
apply symmetry in A. apply symmetry in B.
rewrite A in *. rewrite B in *.
eapply global_truncation_error_aux; try unfold h; try nra; auto.
apply Rle_refl.
assert (hlow: 0 < h) by (unfold h; nra).
 pose proof error_sum_GS n h hlow as GS.
rewrite GS.
apply Req_le.
replace ((∥ (/ 7662000, / 4068166) ∥) * (((1 + h) ^ n - 1) / h))
with 
((∥ (/ 7662000, / 4068166) ∥) / h  * ((1 + h) ^ n - 1) ).
replace (∥ (pt t0, qt t0) ∥) with 1.
field_simplify; nra.
rewrite A. rewrite B.
symmetry.
apply init_norm_eq.
field_simplify; repeat nra.
field_simplify.
symmetry; apply Rprod_norm_plus_minus_eq.
Qed. 




Theorem iternF_is_finite:
  forall n : nat,  ( n <= 200)%nat->
  (is_finite _ _  (fst(iternF (q_init,p_init)  n)) = true) /\
  (is_finite _ _  (snd(iternF (q_init,p_init)  n)) = true).
Proof.
intros.
pose proof global_error bmd_init n H.
destruct H0 as (A & _).
 lazymatch goal with
 | H: boundsmap_denote _ _ |- _ =>
  apply boundsmap_denote_e in H;
  simpl Maps.PTree.elements in H;
  unfold list_forall in H
end.
destruct A as (A & B).
simpl in A. destruct A as (V1 & V2 & V3 & V4 & _).  
  inversion V3; subst. simpl in V4; auto.
simpl in B. destruct B as (U1 & U2 & U3 & U4 & _).  
  inversion U3; subst. simpl in U4; auto.
Qed.



End WITHNANS.