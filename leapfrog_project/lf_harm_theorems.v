(* This file contains proofs of the floating point properties:
local and global error, finiteness *)

From Flocq Require Import Binary Bits Core.
From compcert.lib Require Import IEEE754_extra Coqlib Floats Zbits Integers.
Require Import vcfloat lf_harm_float lf_harm_real real_lemmas lf_harm_lemmas.
Set Bullet Behavior "Strict Subproofs". 

Import FPLangOpt. 
Import FPLang.
Import FPSolve.
Import Test.

Import Interval.Tactic.

(*

(* single step position error *)
Theorem one_step_error_x:
  forall x v : float32,
    boundsmap_denote lf_bmap_init (leapfrog_vmap x v)->
    (Rabs (Rminus (rval (leapfrog_env  x v) (optimize_div x')) 
   (B2R _ _ (fval (leapfrog_env  x v) (optimize_div x'))))) <=
         (1.25/(10^7)).
Proof.
intros.
(destruct (rndval_with_cond O (mempty  (Tsingle, Normal)) (optimize_div x')) 
  as [[r [si2 s]] p] eqn:rndval).
(assert (BND: 0 <= 0 <= 1) by nra).
pose proof 
  (rndval_with_cond_correct_optx_n x v 0%nat (Nat.le_0_l (1000)) 0 0 BND BND H r si2 s p rndval)
as rndval_result.
intro_absolute_error_bound Tsingle Normal H x v rndval_result.
Qed.

(* single step position error *)
Theorem one_step_error_v:
  forall x v : float32,
    boundsmap_denote lf_bmap_init (leapfrog_vmap x v)->
    (Rabs (Rminus (rval (leapfrog_env  x v) (optimize_div v')) 
   (B2R _ _ (fval (leapfrog_env  x v) (optimize_div v'))))) <=
       6.75/(10^8) .
Proof.
intros.
(destruct (rndval_with_cond O (mempty  (Tsingle, Normal)) (optimize_div v')) 
  as [[r [si2 s]] p] eqn:rndval).
(assert (BND: 0 <= 0 <= 1) by nra).
pose proof 
  (rndval_with_cond_correct_optv_n x v 0%nat (Nat.le_0_l (1000)) 0 0 BND BND H r si2 s p rndval)
as rndval_result.
intro_absolute_error_bound Tsingle Normal H x v rndval_result.
Qed.


Lemma local_error_x :
  forall x v : float32,
  forall x1 v1 : R,
    boundsmap_denote lf_bmap_init (leapfrog_vmap x v)->
  x1 = B2R _ _ x ->
  v1 = B2R _ _ v -> 
    (Rabs (Rminus (fst(leapfrog_stepR' (x1,v1))) 
    (B2R _ _ (leapfrog_stepx x v)))) <=  (1.25/(10^7)).
Proof.
intros.
replace (fst (leapfrog_stepR' (x1,v1))) with 
  (rval (leapfrog_env x v) (optimize_div x')).
 replace (B2R 24 128 (leapfrog_stepx x v)) with
  (B2R _ _(fval (leapfrog_env x v) (optimize_div x'))).
  - pose proof one_step_error_x x v H. apply H2.
  - rewrite <- env_fval_reify_correct_leapfrog_step_x; 
  (assert (BND: 0 <= 0 <= 1) by nra).
  pose proof optimize_div_correct' (leapfrog_env x v) x' 
  (leapfrog_stepx_not_nan_n x v 0%nat (Nat.le_0_l (1000)) 0 0 BND BND H);
revert H2;
generalize (fval (leapfrog_env x v) (optimize_div x'));
rewrite optimize_div_type; intros;
apply binary_float_eqb_eq in H2; subst; reflexivity.
- rewrite (@env_rval_reify_correct_leapfrog_stepx x v x1 v1); auto.
Qed.


Lemma local_error_v:
  forall x v : float32,
  forall x1 v1 : R,
    boundsmap_denote lf_bmap_init (leapfrog_vmap x v)->
  x1 = B2R _ _ x ->
  v1 = B2R _ _ v -> 
    (Rabs (Rminus (snd(leapfrog_stepR' (x1,v1))) 
    (B2R _ _ (leapfrog_stepv x v)))) <= 6.75/(10^8).
Proof.
intros. 
replace (snd (leapfrog_stepR' (x1,v1))) with 
  (rval (leapfrog_env x v) (optimize_div v')).
 replace (B2R 24 128 (leapfrog_stepv x v)) with
  (B2R _ _(fval (leapfrog_env x v) (optimize_div v'))).
  - pose proof one_step_error_v x v H. apply H2.
  - rewrite <- env_fval_reify_correct_leapfrog_step_v; 
  (assert (BND: 0 <= 0 <= 1) by nra).
  pose proof optimize_div_correct' (leapfrog_env x v) v' 
  (leapfrog_stepv_not_nan_n x v 0%nat (Nat.le_0_l (1000)) 0 0 BND BND H);
revert H2;
generalize (fval (leapfrog_env x v) (optimize_div v'));
rewrite optimize_div_type; intros;
apply binary_float_eqb_eq in H2; subst; reflexivity.
- rewrite (@env_rval_reify_correct_leapfrog_stepv x v x1 v1); auto.
Qed.



Lemma leapfrog_step_is_finite:
forall n: nat,
forall x  v : float32,
boundsmap_denote (lf_bmap_n n) (leapfrog_vmap (fst ( iternF n x v)) (snd ( iternF n x v))) ->
(n <= 1000)%nat ->
is_finite _ _ (fst ( iternF (S n) x v)) = true/\
is_finite _ _ (snd ( iternF (S n) x v)) = true.  
Proof.
Admitted.
*)


Lemma bounds_Sn: 
  forall x v : float32, 
  forall n: nat, 
    boundsmap_denote (lf_bmap_n n) 
      (leapfrog_vmap x v) -> 
    boundsmap_denote (lf_bmap_n (S n)) 
      (leapfrog_vmap (leapfrog_stepx x v) (leapfrog_stepv x v)).
Proof.
intros.
unfold boundsmap_denote in *.
intros.
specialize (H i).
pose proof bmd_Sn_bnds_le  n i.
pose proof bmd_Sn_vars_eq   n i.
destruct (Maps.PTree.get i (leapfrog_vmap x v)).
destruct (
Maps.PTree.get i (leapfrog_vmap (leapfrog_stepx x v) (leapfrog_stepv x v))).
+ destruct (Maps.PTree.get i (lf_bmap_n  n)); 
  try contradiction.
++ destruct (Maps.PTree.get i (lf_bmap_n (S n))).
+++ specialize (H0 v3 v2 eq_refl eq_refl).
specialize (H1 v3 v2  eq_refl eq_refl).
destruct v3; destruct v2. 
destruct H as (xp & A & B & C & D).
simpl in H0; simpl in H1. destruct H1. subst.
exists xp; repeat split; auto.
eapply Rle_trans. apply H0. apply D.
eapply Rle_trans. apply D. apply H0.
+++ destruct H2; destruct H2. exists v1; auto. discriminate; auto.
+ destruct (Maps.PTree.get i (lf_bmap_n   ( n))).
++  destruct v0; try contradiction.
++ destruct (Maps.PTree.get i (lf_bmap_n   (S n))); auto.
destruct H2; destruct H3. exists v0; auto. discriminate; auto.
Qed.


end.

Theorem global_error:
  forall x v : float32, 
  forall n: nat, 
  (n <= 1000)%nat ->
  forall x1 v1 : R,
  x1 = B2R _ _ x ->
  v1 = B2R _ _ v ->
    boundsmap_denote (lf_bmap_n n) 
      (leapfrog_vmap x v) /\
Rprod_norm (Rprod_minus (leapfrogR x1 v1 1 n) 
  ((B2R _ _ (fst(iternF n x v))), (B2R _ _ (snd(iternF n x v))))) <= 1
.
Proof.
induction n.
intros.
+ simpl. rewrite H0; rewrite H1.
split. 
++ admit.
++ unfold Rprod_minus; simpl. admit.
+ intros.
assert (Hn: (n <= 1000)%nat) by admit.
specialize (IHn Hn x1 v1 H0 H1) as (A & B).
rewrite step_iternF. rewrite nsteps_lem.
destruct (leapfrogR x1 v1 1 n) as (xnr, vnr). 
destruct (iternF n x v) as (xnf, vnf).
simpl in A, B.
split.
++ 
unfold boundsmap_denote in *.
intros; specialize (A i).
++
unfold fst at 1. unfold snd at 1.


end.


Proof.
Admitted.
*)
