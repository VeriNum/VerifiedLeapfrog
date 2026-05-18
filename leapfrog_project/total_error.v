(* This file contains proofs of the floating point properties:
local and global error, finiteness *)

Require Import vcfloat.VCFloat.
Require Import Interval.Tactic.
Import Binary.
Import Stdlib.Lists.List ListNotations.
Set Bullet Behavior "Strict Subproofs".

Require Import float_model real_model real_lemmas vcfloat_lemmas
  matrix_analysis local_discretization_error global_discretization_error harmonic_oscillator_system
  local_roundoff_error global_roundoff_error.
Require Import backward_error_analysis.

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

(** ** BEA-tightened total error.

    Replaces the linear-in-n discretization bound
    [h^3 / (σb-1) * (σb^n - 1)] (essentially N*h^3 for our σb) with the
    BEA bound [2/1000] (constant in n, valid for n <= 1000). Combined
    via triangle inequality with the existing [global_roundoff_error]
    (≤ [local_round_off * error_sum σb n], bounded by ~3.3e-4 via
    [error_sum_bound]), the headline becomes [3/1000] — a ~10× tightening
    over the existing [0.0308]. *)

Theorem BEA_total_error :
  forall pt qt : R -> R, forall n : nat, (n <= 1000)%nat ->
  pt 0 = FT2R p_init ->
  qt 0 = FT2R q_init ->
  Harmonic_oscillator_system ω pt qt ->
  ∥ (pt (INR n * h), qt (INR n * h))
    - (FT2R_prod (iternF float_model.h (p_init, q_init) n)) ∥
     <= 3 / 1000.
Proof.
assert (BMD: boundsmap_denote leapfrog_bmap (leapfrog_vmap pq_init)) by apply bmd_init.
intros pt qt n Hn Hp Hq Hsys.
assert (Hp_init: FT2R p_init = 0) by (unfold FT2R, p_init; compute; lra).
assert (Hq_init: FT2R q_init = 1) by (unfold FT2R, q_init; compute; lra).
match goal with |- context[?A <= ?B] =>
replace A with
  (∥ ((pt (INR n * h)%R, qt (INR n * h)%R)
        - (iternR (FT2R p_init, FT2R q_init) h n))
    + ((iternR (FT2R p_init, FT2R q_init) h n)
        - (FT2R_prod (iternF float_model.h (p_init, q_init) n))) ∥)
end.
- eapply Rle_trans; [apply Rprod_triang_ineq |].
  apply Rle_trans with (2 / 1000 + local_round_off * error_sum σb n).
  + apply Rplus_le_compat.
    * (* BEA discretization bound *)
      rewrite Hp_init, Hq_init. unfold h.
      unfold Rprod_minus. cbn [fst snd].
      apply (BEA_truncation_bound pt qt n Hn).
      -- rewrite Hp. exact Hp_init.
      -- rewrite Hq. exact Hq_init.
      -- unfold ω in Hsys. exact Hsys.
    * (* Roundoff bound *)
      pose proof (global_roundoff_error BMD n Hn) as [_ Hr].
      exact Hr.
  + (* Numeric: local_round_off * error_sum σb n ≤ 1/1000, so total ≤ 3/1000 *)
    pose proof (error_sum_bound n Hn) as Hes.
    assert (Hlpos: 0 <= local_round_off)
      by (unfold local_round_off; interval).
    assert (Hesp: 0 <= error_sum σb n).
    { clear -BMD. induction n.
      - simpl. lra.
      - simpl. apply Rplus_le_le_0_compat; [lra|].
        apply Rmult_le_pos; [unfold σb; lra | exact IHn]. }
    apply Rle_trans with (2 / 1000 + local_round_off * 1002).
    * apply Rplus_le_compat_l.
      apply Rmult_le_compat_l; assumption.
    * unfold local_round_off. interval.
- symmetry; apply Rprod_norm_plus_minus_eq.
Qed.

Corollary BEA_yes_accurate_harmonic_oscillator :
  accurate_harmonic_oscillator
    (iternF float_model.h (p_init, q_init) N) N (3 / 1000).
Proof.
unfold accurate_harmonic_oscillator.
intros pt qt Hp Hq Hsys.
cbv zeta.
replace (0 + INR N * h) with (INR N * h) by ring.
apply BEA_total_error; auto.
Qed.

End WITHNANS.