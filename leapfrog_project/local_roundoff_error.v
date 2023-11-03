(* This file contains proofs of the floating point properties:
local and global error, finiteness *)

Require Import vcfloat.VCFloat.
Require Import Interval.Tactic.
Import Binary.
Import Coq.Lists.List ListNotations.
Set Bullet Behavior "Strict Subproofs".

Require Import float_model real_model real_lemmas vcfloat_lemmas matrix_analysis.

Open Scope R_scope.

Section WITHNANS.

Context {NANS: Nans}.

Lemma prove_roundoff_bound_q:
  forall pq : state,
  prove_roundoff_bound leapfrog_bmap (leapfrog_vmap pq) q' 
    (1.235*(1/10^7)).
Proof.
intros [p q].
prove_roundoff_bound.
- abstract (prove_rndval; interval).
- prove_roundoff_bound2.
 match goal with |- Rabs ?a <= _ => field_simplify a end.
interval.
Qed.

Lemma prove_roundoff_bound_p:
  forall pq : state,
  prove_roundoff_bound leapfrog_bmap (leapfrog_vmap pq) p' 
   (6.552*(1/10^8)).
Proof.
intros [p q].
prove_roundoff_bound.
- abstract (prove_rndval; interval).
- prove_roundoff_bound2.
match goal with |- Rabs ?a <= _ => field_simplify a end.
interval.
Qed.


Lemma prove_roundoff_bound_q_implies:
  forall pq : state,
  boundsmap_denote leapfrog_bmap (leapfrog_vmap pq)-> 
  Rabs (FT2R (fval (env_ (leapfrog_vmap pq)) q') 
           - rval (env_ (leapfrog_vmap pq)) q')
        <= (1.235*(1/10^7))
.
Proof.
intros.
apply (prove_roundoff_bound_q pq H).
Qed.

Lemma prove_roundoff_bound_p_implies:
  forall pq : state,
  boundsmap_denote leapfrog_bmap (leapfrog_vmap pq)-> 
  Rabs (FT2R (fval (env_ (leapfrog_vmap pq)) p')  
      - rval (env_ (leapfrog_vmap pq)) p') <= (6.552*(1/10^8))
.
Proof.
intros.
apply (prove_roundoff_bound_p pq H).
Qed.

Lemma itern_implies_bmd_aux:
  forall pq0 : state,
  forall n : nat,
  boundsmap_denote leapfrog_bmap 
  (leapfrog_vmap (iternF float_model.h pq0 n)) ->
  (is_finite _ _  (fst(iternF float_model.h pq0 (S n))) = true) /\
  (is_finite _ _  (snd(iternF float_model.h pq0 (S n))) = true).
Proof.
intros.
rewrite step_iternF.
destruct (iternF float_model.h pq0 n) as [p q]; clear pq0 n.
split.
-
destruct (prove_roundoff_bound_p _ H) as [? _]; clear H.
rewrite <- H0; clear H0.
simple apply f_equal.
simpl. reflexivity.
-
destruct (prove_roundoff_bound_q _ H) as [? _]; clear H.
rewrite <- H0; clear H0.
simple apply f_equal.
simpl. reflexivity.
Qed.

Definition local_round_off :=  ∥(1.235*(1/10^7) , 6.552*(1/10^8))∥.

Theorem local_roundoff_error':
  forall x : state,
  boundsmap_denote leapfrog_bmap (leapfrog_vmap x)-> 
  let env := env_ (leapfrog_vmap x) in
  let (pnf, qnf) := FT2R_prod (fval env p', fval env q') in 
  let (pnr, qnr) := (rval env p', rval env q') in
  ∥ (pnf, qnf) - (pnr, qnr)∥ <= local_round_off.
Proof.
intros.
unfold Rprod_minus, FT2R_prod, Rprod_norm, fst, snd.
rewrite <- pow2_abs.
rewrite Rplus_comm.
rewrite <- pow2_abs.
pose proof prove_roundoff_bound_p_implies x H.
pose proof prove_roundoff_bound_q_implies x H.
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

Theorem local_roundoff_error:
  forall x : state,
  boundsmap_denote leapfrog_bmap (leapfrog_vmap x) -> 
  ∥ FT2R_prod (leapfrog_stepF float_model.h x)  - leapfrog_stepR h (FT2R_prod x) ∥ 
    <= local_round_off.
Proof.
intros.
pose proof local_roundoff_error' x H.
cbv zeta in H0.
rewrite reflect_reify_pq in H0.
rewrite rval_correct_pq in H0.
apply H0.
Qed.

End WITHNANS.