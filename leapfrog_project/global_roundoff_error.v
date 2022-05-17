(* This file contains proofs of the floating point properties:
local and global error, finiteness *)

From vcfloat Require Import FPLang FPLangOpt RAux Rounding Reify Float_notations Automate.
Require Import IntervalFlocq3.Tactic.
Import Binary.
Import List ListNotations.
Set Bullet Behavior "Strict Subproofs".

Require Import float_model real_model real_lemmas vcfloat_lemmas harmonic_oscillator_system
  matrix_analysis local_discretization_error global_discretization_error
  local_roundoff_error.

Open Scope R_scope.

Section WITHNANS.

Context {NANS: Nans}.



Lemma init_norm_eq :
  ∥  (FT2R p_init, FT2R q_init) ∥ = 1 . 
Proof.
intros.
rewrite <- sqrt_1.
replace (FT2R q_init) with 1.
simpl. unfold Rprod_norm, fst, snd.
f_equal; nra.
unfold FT2R, q_init. 
 cbv [B2R]. simpl. cbv [Defs.F2R IZR IPR]. simpl;
field_simplify; nra.
Qed.

Lemma iternR_bound_init : 
  forall nf : nat, 
  ( nf <= N)%nat -> 
  ∥iternR (FT2R p_init, FT2R q_init) h nf∥ <=  1.003822.
Proof.
intros. 
eapply Rle_trans.
apply (iternR_bound_max_step (FT2R p_init) (FT2R q_init) nf H).
rewrite init_norm_eq.
rewrite Rmult_1_r.
apply Req_le; auto.
Qed.


Lemma error_sum_bound: 
  forall n,
  (n <= 1000)%nat -> 
  error_sum σb n <= 1002.
Proof.
intros.
eapply Rle_trans.
eapply error_sum_le_trans. 
  apply H. try unfold σb; nra.
assert (Hyph: σb <> 1 ) by (unfold σb ;nra).
pose proof geo_series_closed_form σb (999) Hyph.
unfold error_sum.
rewrite H0.
set (a:= 1000%nat).
replace ((1 - σb ^ a) / (1 - σb)) with ((
 σb ^ a- 1) /(σb -1)) by (unfold σb; nra). 
match goal with  |-context[?a /?b] =>
replace b with (0.000003814704543) by (unfold σb; nra)
end.
rewrite Rcomplements.Rle_div_l. 
subst a.
eapply Rle_trans.
match goal with |- context[?a <= _] =>
interval_intro a upper with (i_prec 128)
end.
apply H1.
all: interval.
Qed.

Lemma iterR_bound: 
  forall pt qt: R -> R,
  forall n : nat, 
  (n <= 1000)%nat ->
  let t0 := 0 in
  let tn := t0 + INR n * h in
  pt t0 = FT2R p_init -> 
  qt t0 = FT2R q_init ->
  Harmonic_oscillator_system ω pt qt ->
   ∥(pt tn, qt tn) - (iternR ((FT2R p_init), (FT2R q_init)) h n)∥ <= h ^ 3 * error_sum σb n -> 
  (forall m,
    (m <= n)%nat -> 
    ∥(iternR ((FT2R p_init), (FT2R q_init)) h m)∥ <= 1.0306).
Proof.
intros * ? * IC1 IC2. intros.
assert (0 < ω*h <= 2) as Hbnd by (unfold h,ω; nra).
pose proof global_truncation_error_sum pt qt t0 tn H0 m.
assert (t0 + INR m * h <= tn). 
  subst tn. apply Rplus_le_compat_l.
  apply Rmult_le_compat_r; try unfold h; try nra.
  apply le_INR; apply H2.
specialize (H3 H4).
rewrite  Rprod_minus_comm in H3.
eapply Rle_trans in H3.
2: apply Rprod_triang_inv.
assert (wpos: 0 < ω) by (unfold ω; nra).
assert (C := system_implies_cons_e' pt qt ω t0 (t0 + INR m * h) wpos H0).
unfold ω in *; repeat (rewrite Rmult_1_l in C).
rewrite C in H3.
rewrite IC1 in H3.
rewrite IC2 in H3.
rewrite init_norm_eq in H3.
rewrite Rmult_1_r in H3.
rewrite Rle_minus_l_2 in H3.
pose proof error_sum_bound.
assert (1 + h ^ 3 * error_sum σb m <= 
  1 + h ^ 3 * error_sum σb n).
  apply Rplus_le_compat_l.
  apply Rmult_le_compat_l.
  try unfold h; try nra.
  apply error_sum_le_trans.
  apply H2.
  unfold σb; nra.
eapply Rle_trans.
apply H3.
eapply Rle_trans.
apply H6.
specialize (H5 n H).
assert (1 + h ^ 3 * error_sum σb n <=
  1 + h ^ 3 * 1002).
apply Rplus_le_compat_l.
  apply Rmult_le_compat_l.
  try unfold h; try nra.
  apply H5.
eapply Rle_trans.
apply H7.
unfold h.
interval.
Qed.


Lemma itern_implies_bmd_aux1:
  forall pnf qnf : ftype Tsingle,
  forall pnr qnr : R,
  forall n,
  (n <= 1000)%nat -> 
  ∥ Rprod_minus (pnr, qnr) (FT2R_prod (pnf, qnf)) ∥ <=  local_round_off * error_sum σb n ->
  ∥(pnr,qnr) ∥ <= 1.003822 -> 
  Rabs (FT2R pnf)  <= 1.0041 /\ Rabs ( FT2R qnf) <= 1.0041.
Proof.
intros ? ? ? ? ? BNDn A B.
assert (HYP1: ∥ Rprod_minus (pnr, qnr) (FT2R_prod (pnf, qnf)) ∥ <=
(local_round_off) * error_sum σb 1000).
- 
eapply Rle_trans. 
apply A.
  apply Rmult_le_compat_l; try (apply Rnorm_pos).
  eapply error_sum_le_trans. apply BNDn. unfold σb; nra.
-
clear A. 
(* use the fact that (error_sum (1 + a) 1000 <= 1002 *)
assert ( HYP2 :∥ Rprod_minus (pnr, qnr) (FT2R_prod (pnf, qnf)) ∥ <=
    local_round_off * 1002). {
  eapply Rle_trans.
  apply HYP1.
  apply Rmult_le_compat_l; try (apply Rnorm_pos).
  apply error_sum_bound; try lia.
}
clear HYP1. 
assert (HYP3: (∥ (FT2R_prod (pnf, qnf))∥ - ∥ (pnr, qnr) ∥) <=local_round_off * 1002 ). {
  eapply Rle_trans.
  apply Rprod_triang_inv.
  rewrite Rprod_minus_comm.
  apply HYP2.
}
apply Rle_minus_l_2 in HYP3. 
assert (HYP4: ∥ FT2R_prod (pnf, qnf) ∥ <= 1.003822 + local_round_off * 1002). {
  eapply Rle_trans.
  apply HYP3.
 apply Rplus_le_compat_r. apply B.
} clear HYP2.
generalize HYP4.
match goal with |-context[Rprod_norm ?A <= ?a]=>
  interval_intro a upper ; intros ?HYP; clear HYP;  
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
+ 
assert (FT2R pnf ^ 2 <= valB ^ 2) by nra.
apply sqrt_le in H0.
rewrite sqrt_pow2 in H0.
all: (try interval).
+ 
assert (FT2R qnf ^ 2 <= valB ^ 2) by nra.
apply sqrt_le in H0.
rewrite sqrt_pow2 in H0.
all: (try interval).
Qed.

Lemma itern_implies_bmd:
  forall p q: ftype Tsingle,
  forall n,
  (S n <= 1000)%nat -> 
  boundsmap_denote leapfrog_bmap 
    (leapfrog_vmap (iternF float_model.h (p,q) n)) ->
  ∥(iternR (FT2R p, FT2R q) h (S n)) - FT2R_prod (iternF float_model.h (p,q)  (S n)) ∥ <= 
  local_round_off * error_sum σb (S n)  ->
 ∥ (iternR (FT2R p, FT2R q) h  (S n))∥ <= 1.003822 ->
   boundsmap_denote leapfrog_bmap (leapfrog_vmap (iternF float_model.h (p,q) (S n))).
Proof. 
intros ? ? ? BNDn BMD NORM1 NORM2.
apply boundsmap_denote_i.
2: repeat apply list_forall_cons; try apply list_forall_nil; simpl; auto.
destruct (BMD _p) as [_ [_ [_ Bp]]].
destruct (BMD _q) as [_ [_ [_ Bq]]].
destruct (itern_implies_bmd_aux _ _ BMD) as [FINp FINq].
clear BMD.
rewrite step_iternF in *.
destruct ((iternF float_model.h (p, q) n)) as [pn qn].
destruct (leapfrog_stepF float_model.h (pn, qn)) as [pn1 qn1].
simpl in Bp,Bq,FINp,FINq.
destruct ((iternR (FT2R p, FT2R q) h (S n))) as [pr qr].
destruct (itern_implies_bmd_aux1 pn1 qn1 pr qr _ BNDn NORM1 NORM2).
apply Rabs_le_inv in H.
apply Rabs_le_inv in H0.
repeat apply list_forall_cons; try apply list_forall_nil;
(eexists; split; [|split;[|split]]; try reflexivity; auto;
 simpl; nra; auto).
Qed.


Theorem global_roundoff_error : 
  boundsmap_denote leapfrog_bmap 
  (leapfrog_vmap pq_init) ->
  forall n : nat, 
  (n <= 1000)%nat -> 
  let vmap_n := (leapfrog_vmap (iternF float_model.h pq_init n)) in
  let c:= local_round_off in 
  let (pr0, qr0) := (FT2R p_init, FT2R q_init) in
  boundsmap_denote leapfrog_bmap vmap_n /\
  ∥(iternR (pr0, qr0) h n) - FT2R_prod (iternF float_model.h pq_init n) ∥ 
     <= c * error_sum  σb n.
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
assert (BNDn: (n<= 1000)%nat) by lia.
pose proof iternR_bound_max_step (FT2R p_init) (FT2R q_init) n BNDn.
rewrite init_norm_eq in H1.
rewrite Rmult_1_r in H1.
destruct (iternR (FT2R p_init, FT2R q_init) h n) as (pnr, qnr). 
destruct (iternF float_model.h pq_init n) as (pnf, qnf).
match goal with |- context[∥?a - ?b∥ <=  _] =>
  let c := (constr:(leapfrog_stepR h (FT2R_prod (pnf, qnf)))) in
  replace (∥a - b∥) with (∥ Rprod_plus (a - c) (c - b) ∥)
end.
eapply Rle_trans.
apply Rprod_triang_ineq.
rewrite leapfrog_minus_args.
eapply Rle_trans.
apply Rplus_le_compat_l.
assert (∥ Rprod_minus (pnr, qnr) (FT2R_prod (pnf, qnf)) ∥ <=
     local_round_off * error_sum σb n /\ ∥ (pnr, qnr) ∥ <= 1.003822).
split; auto.
rewrite Rprod_minus_comm. 
apply (local_roundoff_error (pnf,qnf) IHbmd).
destruct (Rprod_minus (pnr, qnr) (FT2R_prod (pnf, qnf))).
assert (0 < ω*h <= 2) as Hh by (unfold h,ω; nra).
pose proof (method_norm_bound r r0 ) as BND.
eapply Rle_trans.
apply Rplus_le_compat_r.
apply BND. 
eapply Rle_trans.
apply Rplus_le_compat_r.
apply Rmult_le_compat_l; try (unfold σb; nra).
apply IHnorm. 
fold c.
replace (σb * (c * error_sum σb n) + c)
with
(c * (σb * (error_sum σb n) + 1)) by nra.
rewrite <- error_sum_aux2; unfold c; nra.
symmetry. apply Rprod_norm_plus_minus_eq.
+ destruct IHn as (IHbmd & IHnorm); try lia.
apply itern_implies_bmd; try lia; auto.
pose proof iternR_bound_max_step (FT2R p_init) (FT2R q_init) (S n) H0. 
rewrite init_norm_eq in H2.
rewrite Rmult_1_r in H2.
auto.
Qed.

 
End WITHNANS.