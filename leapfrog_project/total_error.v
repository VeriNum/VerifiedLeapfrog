(* This file contains proofs of the floating point properties:
local and global error, finiteness *)

From vcfloat Require Import FPLang FPLangOpt RAux Rounding Reify Float_notations Automate.
Require Import Interval.Tactic.
Import Binary.
Import List ListNotations.
Set Bullet Behavior "Strict Subproofs".

Require Import float_model real_model real_lemmas vcfloat_lemmas
  matrix_analysis local_discretization_error global_discretization_error harmonic_oscillator_system
  local_roundoff_error global_roundoff_error.

Open Scope R_scope.

Section WITHNANS.

Context {NANS: Nans}.


Theorem total_error: 
  forall pt qt: R -> R,
  forall n : nat, 
  (n <= 1000)%nat ->
  let t0 := 0 in
  let tn := t0 + INR n * h in
  pt t0 = FT2R p_init ->
  qt t0 = FT2R q_init ->
  Harmonic_oscillator_system ω pt qt ->
  ∥ (pt tn, qt tn) - (FT2R_prod (iternF float_model.h (p_init,q_init) n)) ∥ 
     <=  (h^3  + local_round_off)/ (σb-1) * (σb ^ n - 1) .
Proof.
assert (BMD: boundsmap_denote leapfrog_bmap (leapfrog_vmap pq_init)) by
apply bmd_init.
intros ? ? ? ? ? ? Hp Hq Hsys ; simpl.
match goal with |- context[?A <= ?B] =>
replace A with
  (∥ ((pt (t0 + INR n * h)%R, qt (t0 + INR n * h)%R) - (iternR (FT2R p_init, FT2R q_init) h n)) +
((iternR (FT2R p_init, FT2R q_init) h n) - (FT2R_prod (iternF float_model.h (p_init,q_init) n))) ∥)
end.
assert (HSY: Harmonic_oscillator_system 1 pt qt) by auto.
unfold Harmonic_oscillator_system in Hsys.
rename Hsys into C.
eapply Rle_trans.
apply Rprod_triang_ineq.
eapply Rle_trans.
apply Rplus_le_compat_l.
apply global_roundoff_error; auto.
eapply Rle_trans.
apply Rplus_le_compat_r.
rewrite <- Hp, <- Hq in *.
eapply global_truncation_error_sum; try unfold h,ω; try nra; auto.
apply Rle_refl.
assert (hlow: 0 < 0.000003814704543) by (unfold h; nra).
 pose proof error_sum_GS n 0.000003814704543 hlow as GS.
replace (1 + _) with (σb) in GS.
rewrite GS.
apply Req_le.
replace (( local_round_off ) * (((σb ^ n - 1) /  (σb-1))))
with 
(( local_round_off ) /  (σb-1)  * (σb ^ n - 1) ).
replace (∥ (pt t0, qt t0) ∥) with 1.
field_simplify; unfold σb; nra.
symmetry.
rewrite Hp, Hq.
apply init_norm_eq.
field_simplify; repeat (unfold σb; nra).
unfold σb; nra.
symmetry; apply Rprod_norm_plus_minus_eq.
Qed. 

Definition accurate_harmonic_oscillator (pq: state) (n : nat) (acc: R) :=
  forall pt qt: R -> R,
  let t0 := 0 in
  let tn := t0 + INR n * h in
  pt t0 = FT2R p_init ->
  qt t0 = FT2R q_init ->
  Harmonic_oscillator_system  ω pt qt  ->
  ∥ (pt tn, qt tn) - (FT2R (fst pq), FT2R (snd pq)) ∥ <= acc.

Corollary yes_accurate_harmonic_oscillator : 
          accurate_harmonic_oscillator (iternF float_model.h (p_init,q_init) N) N 0.0308.
Proof.
intros.
red; intros.
eapply Rle_trans.
apply total_error; auto.
clear.
unfold local_round_off, Rprod_norm, fst,snd,h.
interval.
Qed.

End WITHNANS.