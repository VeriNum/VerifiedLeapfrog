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

Lemma prove_roundoff_bound_q:
  forall q p : ftype Tsingle,
  prove_roundoff_bound leapfrog_bmap (leapfrog_vmap q p) q' 
    (2.704*(1/10^6)).
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
   (1.436*(1/10^6)).
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
  Rabs (FT2R (fval (env_ (leapfrog_vmap q p)) q') 
           - rval (env_ (leapfrog_vmap q p)) q')
        <= (2.704*(1/10^6))
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
  Rabs (FT2R (fval (env_ (leapfrog_vmap q p)) p') - rval (env_ (leapfrog_vmap q p)) p') <= (1.436*(1/10^6))
.
Proof.
intros.
pose proof prove_roundoff_bound_p q p.
unfold prove_roundoff_bound in H0. 
specialize (H0 H).
unfold roundoff_error_bound in H0; auto. 
Qed.


Definition local_round_off :=  ∥(1.436*(1/10^6), 2.704*(1/10^6))∥.


Lemma itern_implies_bmd_aux1:
  forall pnf qnf : ftype Tsingle,
  forall pnr qnr : R,
  forall n,
  (n <= 100)%nat -> 
  ∥ Rprod_minus (pnr, qnr) (FT2R_prod (pnf, qnf)) ∥ <=  local_round_off * error_sum (1 + h) n 
  /\ ∥(pnr,qnr) ∥ <= 21.697 -> 
  Rabs (FT2R pnf)  <= 22 /\ Rabs ( FT2R qnf) <= 22.
Proof.
intros ? ? ? ? ? BNDn H. destruct H as (A & B).
assert (HYP1: ∥ Rprod_minus (pnr, qnr) (FT2R_prod (pnf, qnf)) ∥ <=
(local_round_off) * error_sum (1 + h) 100).
+ eapply Rle_trans.
2 :  { 
apply Rmult_le_compat_l; try (apply Rnorm_pos). 
eapply error_sum_le_trans. apply BNDn. unfold h; nra.
} apply A.
+ clear A. 
(* use the fact that (error_sum (1 + h) 200 = 15032.068779571218 *)
assert ( HYP2 :∥ Rprod_minus (pnr, qnr) (FT2R_prod (pnf, qnf)) ∥ <=
    local_round_off * 15033).
eapply Rle_trans.
apply HYP1.
apply Rmult_le_compat_l; try (apply Rnorm_pos).
apply error_sum_bound; try lia.
clear HYP1. 
assert (HYP3: (∥ (FT2R_prod (pnf, qnf))∥ - ∥ (pnr, qnr) ∥) <=local_round_off * 15033 ).
eapply Rle_trans.
apply Rprod_triang_inv.
rewrite Rprod_minus_comm.
apply HYP2.
apply Rle_minus_l_2 in HYP3. 
assert (HYP4: ∥ FT2R_prod (pnf, qnf) ∥ <= 21.697 + local_round_off * 15033).
eapply Rle_trans.
2: {apply Rplus_le_compat_r. apply B.
} apply HYP3. clear HYP2.
generalize HYP4.
match goal with |-context[Rprod_norm ?A <= ?a]=>
  interval_intro a upper; intros ?HYP; clear HYP;
match goal with [H: a <= ?B |- _] =>
set (valB:= B)
end
end. 
unfold Rprod_norm in HYP4. 
unfold FT2R_prod, fst ,snd in HYP4.
assert (HYP5: sqrt (FT2R pnf  ^ 2 + FT2R qnf ^ 2) <= sqrt (valB^2) ).
eapply Rle_trans. apply  HYP4.
rewrite sqrt_pow2; try nra; try (unfold valB; nra); apply H.
apply sqrt_le_0 in HYP5; try nra.
split. 
++ assert (FT2R pnf ^ 2 <= valB ^ 2) by nra.
apply sqrt_le in H0.
rewrite sqrt_pow2 in H0.
all: (try interval).
++ assert (FT2R qnf ^ 2 <= valB ^ 2) by nra.
apply sqrt_le in H0.
rewrite sqrt_pow2 in H0.
all: (try interval).
Qed.

Definition FT2R_prod_rev := fun A : ftype Tsingle * ftype Tsingle =>
(FT2R (snd A), FT2R (fst A)).

Lemma itern_implies_bmd:
  forall q0 p0: ftype Tsingle,
  forall n,
  (S n <= 100)%nat -> 
  boundsmap_denote leapfrog_bmap 
    (leapfrog_vmap (fst(iternF (q0,p0) n)) (snd(iternF (q0,p0) n))) ->
  ∥(iternR (FT2R p0, FT2R q0) h (S n)) - FT2R_prod_rev (iternF (q0,p0)  (S n)) ∥ <= 
  local_round_off * error_sum (1 + h) (S n)  /\
∥ (iternR (FT2R p0, FT2R q0) h  (S n))∥ <= 21.697 ->
   boundsmap_denote leapfrog_bmap (leapfrog_vmap (fst(iternF (q0,p0) (S n))) (snd(iternF (q0,p0) (S n)))).
Proof. 
intros ? ? ? BNDn BMD NORM.
pose proof (itern_implies_bmd_aux q0 p0 n BMD) as HFIN.
pose proof (itern_implies_bmd_aux1) as HBND.
unfold boundsmap_denote in *.
intros.
specialize (BMD i).
pose proof bmd_Sn_bnds_le i as ABSBND.
destruct (Maps.PTree.get i leapfrog_bmap).
-
specialize (ABSBND v eq_refl).
destruct v. 
simpl in ABSBND.
rewrite step_iternF in *.
destruct ((iternF (q0, p0) n)).
set (f1 := (fst (leapfrog_stepF (f, f0)))) in *.
set (f2:=(snd (leapfrog_stepF (f, f0)))) in *.
pose proof  (Maps.PTree.elements_correct
   (leapfrog_vmap f1 f2) i) as COR. 
pose proof  (Maps.PTree.elements_correct
   (leapfrog_vmap f f0) i) as COR2.
pose proof (leapfrog_vmap_i_aux f1 f2 f f0 i) as EX.
simpl in BMD. 
destruct (Maps.PTree.get i (leapfrog_vmap f1 f2));
destruct (Maps.PTree.get i (leapfrog_vmap f f0));
try contradiction.
+
specialize (COR2 s0 eq_refl).
inversion COR2; clear COR2.
*
inversion H; subst; clear H.
simpl in BMD.
specialize (COR s eq_refl).
inversion COR; clear COR.
--
inversion H; subst; clear H.
split; try ( apply BMD).
split. simpl. apply BMD.
split. apply HFIN.
destruct ((iternR (FT2R p0, FT2R q0) h (S n))).
specialize (HBND f2 f1 r r0 (S n) BNDn NORM). 
destruct ABSBND.
subst.
unfold projT2. 
destruct HBND.
apply Rabs_le_inv; auto.
--
simpl in H; destruct H; try contradiction.
inversion H; subst; clear H.
*
simpl in H; destruct H; try contradiction.
inversion H; subst; clear H.
simpl in BMD.
specialize (COR s eq_refl).
inversion COR; clear COR.
--
inversion H; subst; clear H.
--
inversion H; subst; clear H.
++ 
inversion H0; subst; clear H0.
split; try ( apply BMD).
split. simpl. apply BMD.
split. apply HFIN.
destruct ((iternR (FT2R p0, FT2R q0) h (S n))).
specialize (HBND f2 f1 r r0 (S n) BNDn NORM). 
destruct ABSBND.
subst.
unfold projT2. 
destruct HBND.
apply Rabs_le_inv; auto.
++ 
inversion H0; subst; clear H0.
+
specialize (EX s eq_refl).
destruct EX as (A & B & C); discriminate.
-
rewrite step_iternF in *.
destruct ((iternF (q0, p0) n)).
set (f1 := (fst (leapfrog_stepF (f, f0)))) in *.
set (f2 := (snd (leapfrog_stepF (f, f0)))) in *.
pose proof  (Maps.PTree.elements_correct
   (leapfrog_vmap f1 f2) i) as COR. 
pose proof  (Maps.PTree.elements_correct
   (leapfrog_vmap f f0) i) as COR2.
pose proof (leapfrog_vmap_i_aux f1 f2 f f0 i) as EX1.
pose proof (leapfrog_vmap_i_aux f f0 f1 f2 i) as EX2.
simpl in BMD. 
destruct (Maps.PTree.get i (leapfrog_vmap f1 f2));
destruct (Maps.PTree.get i (leapfrog_vmap f f0));
try contradiction.
*
specialize (EX2 s eq_refl).
destruct EX2 as (A & B & C); discriminate.
* auto.
Qed.

Lemma roundoff_norm_bound:
  forall p q : ftype Tsingle,
  boundsmap_denote leapfrog_bmap (leapfrog_vmap q p)-> 
  let (pnf, qnf) := FT2R_prod_rev (fval (env_ (leapfrog_vmap q p)) q', fval (env_ (leapfrog_vmap q p)) p') in 
  let (pnr, qnr) := (rval (env_ (leapfrog_vmap q p)) p', rval (env_ (leapfrog_vmap q p)) q') in
  ∥ (pnf, qnf) - (pnr, qnr)∥ <= local_round_off.
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
unfold fst, snd.
nra.
Qed.

Lemma global_error : 
  boundsmap_denote leapfrog_bmap 
  (leapfrog_vmap q_init p_init) ->
  forall n : nat, 
  (n <= 100)%nat -> 
  let vmap_n := (leapfrog_vmap (fst(iternF (q_init,p_init) n)) (snd(iternF (q_init,p_init) n))) in
  let c:= local_round_off in 
  let (pr0, qr0) := (FT2R p_init, FT2R q_init) in
  boundsmap_denote leapfrog_bmap vmap_n /\
  ∥(iternR (pr0, qr0) h n) - FT2R_prod_rev (iternF (q_init,p_init) n) ∥ 
     <= c * error_sum (1 + h) n.
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
assert (BNDn: (n<= 100)%nat) by lia.
pose proof iternR_bound n BNDn.
destruct (iternR (FT2R p_init, FT2R q_init) h n) as (pnr, qnr). 
destruct (iternF (q_init,p_init) n) as (qnf, pnf).
match goal with |- context[∥?a - ?b∥ <=  _] =>
  let c := (constr:(leapfrog_stepR (FT2R_prod_rev (qnf, pnf)) h)) in
  replace (∥a - b∥) with (∥ Rprod_plus (a - c) (c - b) ∥)
end.
eapply Rle_trans.
apply Rprod_triang_ineq.
rewrite leapfrog_minus_args.
eapply Rle_trans.
apply Rplus_le_compat_l.

assert (∥ Rprod_minus (pnr, qnr) (FT2R_prod_rev (qnf, pnf)) ∥ <=
     local_round_off * error_sum (1 + h) n /\ ∥ (pnr, qnr) ∥ <= 21.697).
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
assert (0 < ω*h <= 2) as Hh by (unfold h,ω; nra).
pose proof (method_norm_bounded r r0 h Hh) as BND.
eapply Rle_trans.
apply Rplus_le_compat_r.
apply BND. 
eapply Rle_trans.
apply Rplus_le_compat_r.
apply Rmult_le_compat_l; try (unfold h; nra).
apply IHnorm. 
fold c.
replace ((1 + h) * (c * error_sum (1 + h) n) + c)
with
(c * ((1 + h) * (error_sum (1 + h) n) + 1)) by nra.
rewrite <- error_sum_aux2; unfold c; nra.
symmetry. apply Rprod_norm_plus_minus_eq.
+ destruct IHn as (IHbmd & IHnorm); try lia.
apply itern_implies_bmd; try lia; auto; split; auto.
pose proof iternR_bound (S n); auto.
Qed. 



Theorem total_error: 
  forall pt qt: R -> R,
  forall n : nat, 
  (n <= 100)%nat ->
  let t0 := 0 in
  let tn := t0 + INR n * h in
  pt t0 = FT2R p_init ->
  qt t0 = FT2R q_init ->
  Harmonic_oscillator_system pt qt ω t0 ->
  let c:= local_round_off / h in 
  ∥ (pt tn, qt tn) - (FT2R_prod_rev (iternF (q_init,p_init) n)) ∥ 
     <=  (h^2  + c) * ((1 + h) ^ n - 1) .
Proof.
assert (BMD: boundsmap_denote leapfrog_bmap (leapfrog_vmap q_init p_init)) by
apply bmd_init.
intros ? ? ? ? ? ? Hp Hq Hsys ; simpl.
match goal with |- context[?A <= ?B] =>
replace A with
  (∥ ((pt (t0 + INR n * h)%R, qt (t0 + INR n * h)%R) - (iternR (FT2R p_init, FT2R q_init) h n)) +
((iternR (FT2R p_init, FT2R q_init) h n) - (FT2R_prod_rev (iternF (q_init,p_init) n))) ∥)
end.
assert (HSY: Harmonic_oscillator_system pt qt 1 t0) by auto.
unfold Harmonic_oscillator_system in Hsys.
rename Hsys into C.
eapply Rle_trans.
apply Rprod_triang_ineq.
eapply Rle_trans.
apply Rplus_le_compat_l.
apply global_error; auto.
eapply Rle_trans.
apply Rplus_le_compat_r.
rewrite <- Hp, <- Hq in *.
eapply global_truncation_error_aux; try unfold h,ω; try nra; auto.
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
symmetry.
rewrite Hp, Hq.
apply init_norm_eq.
field_simplify; repeat nra.
field_simplify.
symmetry; apply Rprod_norm_plus_minus_eq.
Qed. 

Definition total_error_100 (xv: ftype Tsingle * ftype Tsingle) :=
  forall pt qt: R -> R,
  let t0 := 0 in
  let n := 100%nat in 
  let tn := t0 + INR n * h in
  pt t0 = FT2R p_init ->
  qt t0 = FT2R q_init ->
  Harmonic_oscillator_system pt qt ω t0 ->
  ∥ (pt tn, qt tn) - (FT2R (snd xv), FT2R (fst xv)) ∥ <= 0.0223.

Corollary yes_total_error_100: 
          total_error_100 (iternF (q_init,p_init) 100).
Proof.
intros.
red; intros.
eapply Rle_trans.
apply total_error; auto.
clear.
unfold local_round_off, Rprod_norm, fst,snd,h.
interval.
Qed.

Theorem yes_iternF_is_finite: iternF_is_finite.
Proof.
hnf; intros.
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