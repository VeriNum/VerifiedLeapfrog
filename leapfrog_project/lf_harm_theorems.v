From Flocq Require Import Binary Bits Core.
From compcert.lib Require Import IEEE754_extra Coqlib Floats Zbits Integers.
Require Import vcfloat float_lib lf_harm_float lf_harm_real optimize real_lemmas lf_harm_lemmas.
Set Bullet Behavior "Strict Subproofs". 

Import FPLangOpt. 
Import FPLang.
Import FPSolve.
Import Test.

Import Interval.Tactic.

(* these defs are pulled from bounds proofs in lf_harm_lemmas *)
Definition error_v := (5079915575529842 / 75557863725914323419136)%R.
(* error_v = 6.723212283974809e-08 *)
Definition error_x := (4716905030025348 / 37778931862957161709568)%R.
(* error_x = 1.2485543654690345e-07*)
Definition one_step_sum_bnd_x := (4646536420130942 / 2251799813685248)%R.
Definition one_step_sum_bnd_v := (4646570650113373 / 2251799813685248)%R.


(* single step position error *)
Theorem one_step_error_x:
  forall x v : float32,
    boundsmap_denote (leapfrog_bmap ) (leapfrog_vmap x v)->
    Rle (Rabs (Rminus (rval (leapfrog_env  x v) (optimize_div x')) 
   (B2R _ _ (fval (leapfrog_env  x v) (optimize_div x'))))) 
         error_x.
Proof.
intros.
unfold error_x.
(destruct (rndval_with_cond O (mempty  (Tsingle, Normal)) (optimize_div x')) 
  as [[r [si2 s]] p] eqn:rndval).
pose proof (rndval_with_cond_correct_optx x v H r si2 s p rndval)
  as rndval_result. 
intro_absolute_error_bound Tsingle Normal H x v rndval_result.
Qed.


(* single step velocity error *)
Theorem one_step_error_v:
  forall x v : float32,
    boundsmap_denote leapfrog_bmap (leapfrog_vmap x v)->
    Rle (Rabs (Rminus (rval (leapfrog_env x v)  (optimize_div v')) 
    (B2R _ _ (fval (leapfrog_env x v) (optimize_div v'))))) 
         error_v.
Proof.
intros.
unfold error_v.
(destruct (rndval_with_cond O (mempty  (Tsingle, Normal)) (optimize_div v')) 
  as [[r [si2 s]] p] eqn:rndval).
pose proof (rndval_with_cond_correct_optv x v H r si2 s p rndval)
  as rndval_result. 
intro_absolute_error_bound Tsingle Normal H x v rndval_result.
Qed.


Lemma local_error_x :
  forall x v : float32,
  forall x1 v1 : R,
  boundsmap_denote leapfrog_bmap (leapfrog_vmap x v)->
  x1 = B2R _ _ x ->
  v1 = B2R _ _ v -> 
    Rle (Rabs (Rminus (fst(leapfrog_stepR (x1,v1))) 
    (B2R _ _ (leapfrog_stepx x v)))) 
    error_x.
Proof.
intros.
replace (fst (leapfrog_stepR (x1,v1))) with 
  (rval (leapfrog_env x v) (optimize_div x')).
+ replace (B2R 24 128 (leapfrog_stepx x v)) with
  (B2R _ _(fval (leapfrog_env x v) (optimize_div x'))).
  - pose proof one_step_error_x x v H; apply H2.
  - rewrite <- env_fval_reify_correct_leapfrog_step_x; 
  pose proof optimize_div_correct' (leapfrog_env x v) x' 
  (leapfrog_stepx_not_nan x v H);
revert H2;
generalize (fval (leapfrog_env x v) (optimize_div x'));
rewrite optimize_div_type; intros;
apply binary_float_eqb_eq in H2; subst; reflexivity.
+ rewrite (@env_rval_reify_correct_leapfrog_stepx x v x1 v1); auto.
Qed.


Lemma local_error_v:
  forall x v : float32,
  forall x1 v1 : R,
  boundsmap_denote leapfrog_bmap (leapfrog_vmap x v)->
  x1 = B2R _ _ x ->
  v1 = B2R _ _ v -> 
    Rle (Rabs (Rminus (snd(leapfrog_stepR (x1,v1))) 
    (B2R _ _ (leapfrog_stepv x v)))) 
    error_v.
Proof.
intros.
replace (snd (leapfrog_stepR (x1,v1))) with 
  (rval (leapfrog_env x v) (optimize_div v')).
+ replace (B2R 24 128 (leapfrog_stepv x v)) with
  (B2R _ _(fval (leapfrog_env x v) (optimize_div v'))).
  - pose proof one_step_error_v x v H. apply H2.
  - rewrite <- env_fval_reify_correct_leapfrog_step_v; 
  pose proof optimize_div_correct' (leapfrog_env x v) v' 
  (leapfrog_stepv_not_nan x v H);
revert H2;
generalize (fval (leapfrog_env x v) (optimize_div v'));
rewrite optimize_div_type; intros;
apply binary_float_eqb_eq in H2; subst; reflexivity.
+ rewrite (@env_rval_reify_correct_leapfrog_stepv x v x1 v1); auto.
Qed.



Theorem global_error:
  forall x v : float32, 
  (forall m: nat, 
  forall x' v' : float32, 
  (x',v') = (iternF m x%F32 v%F32) -> 
  boundsmap_denote leapfrog_bmap (leapfrog_vmap x' v')) ->
  forall n: nat, 
  forall x1 v1 : R,
  x1 = B2R _ _ x ->
  v1 = B2R _ _ v -> 
  Rle (Rabs (Rminus (fst(iternR (S n) x1%R v1%R)) (B2R _ _ (fst(iternF (S n) x%F32 v%F32))))) 
   (delta_x error_x error_v n) /\
  Rle (Rabs (Rminus (snd(iternR (S n) x1%R v1%R)) (B2R _ _ (snd(iternF (S n) x%F32 v%F32))))) 
   (delta_v error_x error_v n) .
Proof.
intros. 
induction n.
- unfold iternF ,iternR ,INR, leapfrogR, leapfrog', delta_x, delta_v.
pose proof H 0%nat x v as BMD; unfold iternF, leapfrog', leapfrog_step' in BMD.
pose proof BMD eq_refl.
split.
+ apply local_error_x; auto.
+ apply local_error_v; auto.
- set (m:= S n ).
rewrite ?step_iternR; rewrite ?step_iternF.
unfold m; clear m.
pose proof H (S n) 
  ((fst (iternF (S n) x v))) ((snd (iternF (S n) x v))); clear H. 
destruct (iternR (S n) x1 v1) as (xnr, vnr). 
destruct (iternF (S n) x v) as (xnf, vnf).
unfold fst, snd in H2; pose proof H2 eq_refl; clear H2.
unfold fst, snd in IHn. 
set (r_xnf:= B2R _ _ xnf ) in *; assert (r_xnf = B2R 24 128 xnf) by auto.
set (r_vnf:= B2R _ _ vnf) in *;  assert (r_vnf = B2R 24 128 vnf) by auto.
destruct IHn as (IHx & IHv); split.
(* x case *)
+ match goal with |- context [Rabs(?x1 -?x3) <= ?c] =>
  let x2:= constr:(fst(leapfrog_stepR (r_xnf, r_vnf))) in
  replace (Rabs(x1 - x3)) with (Rabs(x1 -x2 + x2 - x3)) by
  (field_simplify (x1 - x2 + x2 - x3); nra);
  set (aa:= (x1-x2));
  replace (Rminus (aa + x2) x3) with (Rplus aa (x2- x3)) by nra;
  set (bb:= (x2-x3));
  try apply Rabs_triang_aux; unfold aa; unfold bb; clear aa bb
end.
rewrite ?one_stepR_x_alt2.
apply Rabs_triang_aux2.
fold (leapfrog_stepx xnf vnf).
eapply Rle_trans.
eapply Rplus_le_compat_r.
eapply Rplus_le_compat_r.
unfold fst.
eapply Rabs_mult_le_l. field_simplify; try interval; nra.
apply IHx.
eapply Rle_trans.
eapply Rplus_le_compat_r.
eapply Rplus_le_compat_l.
unfold snd.
eapply Rabs_mult_le_l. field_simplify; try interval; nra.
apply IHv.
eapply Rle_trans.
eapply Rplus_le_compat_l.
apply local_error_x; auto.
replace (delta_x error_x error_v (S n)) with ((1 - 0.5 * h ^ 2) * delta_x  error_x error_v n +
      h * delta_v  error_x error_v n + error_x) by 
      (unfold delta_x; fold delta_x; fold delta_v; auto); nra.
+ match goal with |- context [Rabs(?x1 -?x3) <= ?c] =>
  let x2:= constr:(snd(leapfrog_stepR (r_xnf, r_vnf))) in
  replace (Rabs(x1 - x3)) with (Rabs(x1 -x2 + x2 - x3)) by
  (field_simplify (x1 - x2 + x2 - x3); nra);
  set (aa:= (x1-x2));
  replace (Rminus (aa + x2) x3) with (Rplus aa (x2- x3)) by nra;
  set (bb:= (x2-x3));
  try apply Rabs_triang_aux; unfold aa; unfold bb; clear aa bb
end.
rewrite ?one_stepR_v_alt2.
apply Rabs_triang_aux2.
fold (leapfrog_stepv xnf vnf).
eapply Rle_trans.
eapply Rplus_le_compat_r.
eapply Rplus_le_compat_r.
unfold snd.
eapply Rabs_mult_le_l. field_simplify; try interval; nra.
apply IHv.
eapply Rle_trans.
eapply Rplus_le_compat_r.
eapply Rplus_le_compat_l.
unfold fst.
rewrite Rabs_Ropp.
eapply Rabs_mult_le_l. field_simplify; try interval; nra.
apply IHx.
eapply Rle_trans.
eapply Rplus_le_compat_l.
apply local_error_v; auto.
replace (delta_v error_x error_v (S n)) with 
 ((1 - 0.5 * h ^ 2) * delta_v error_x error_v n + 0.5 * h * (2- 0.5 * h ^ 2 ) * delta_x error_x error_v n +
  error_v) by 
 (unfold delta_v; fold delta_v; fold delta_x; auto). nra.
Qed.


Lemma global_error_sum_v_aux :
forall x v : float32, 
  (forall m: nat, 
  forall x' v' : float32, 
  (x',v') = (iternF m x%F32 v%F32) -> 
  boundsmap_denote leapfrog_bmap (leapfrog_vmap x' v')) ->
  forall n: nat, 
  forall x1 v1 : R,
  x1 = B2R _ _ x ->
  v1 = B2R _ _ v -> 
   Rabs (snd(iternR (S n) x1%R v1%R)) <= 
    ((delta_v error_x error_v n) + Rabs (B2R 24 128 (snd (iternF (S n) x v))))%R.
Proof.
intros.
pose proof global_error x v H n x1 v1 H0 H1 as GE.
destruct GE as (GEx & GEv).
eapply Rcomplements.Rle_minus_l.
eapply Rle_trans.
apply Rabs_triang_inv.
auto.
Qed.

Lemma global_error_sum_x_aux :
forall x v : float32, 
  (forall m: nat, 
  forall x' v' : float32, 
  (x',v') = (iternF m x%F32 v%F32) -> 
  boundsmap_denote leapfrog_bmap (leapfrog_vmap x' v')) ->
  forall n: nat, 
  forall x1 v1 : R,
  x1 = B2R _ _ x ->
  v1 = B2R _ _ v -> 
   Rabs (fst(iternR (S n) x1%R v1%R)) <= 
    ((delta_x error_x error_v n) + Rabs (B2R 24 128 (fst (iternF (S n) x v))))%R.
Proof.
intros.
pose proof global_error x v H n x1 v1 H0 H1 as GE.
destruct GE as (GEx & GEv).
eapply Rcomplements.Rle_minus_l.
eapply Rle_trans.
apply Rabs_triang_inv.
auto.
Qed.

Lemma global_error_sum_v :
forall x v : float32, 
  (forall m: nat, 
  forall x' v' : float32, 
  (x',v') = (iternF m x%F32 v%F32) -> 
  boundsmap_denote leapfrog_bmap (leapfrog_vmap x' v')) ->
  forall n: nat, 
  forall x1 v1 : R,
  x1 = B2R _ _ x ->
  v1 = B2R _ _ v -> 
Rabs (snd(iternR (S n) x1%R v1%R) + (B2R 24 128 (snd (iternF (S n) x v)))) <= 
    ((delta_v error_x error_v n) + 2)%R.
Proof.
intros.
pose proof global_error_sum_v_aux x v H n x1 v1 H0 H1.
eapply Rle_trans.
apply Rabs_triang.
eapply Rle_trans.
apply Rplus_le_compat_r.
apply H2.
pose proof H (S n) as BMD. 
destruct (iternF (S n) x v).
specialize (BMD f f0 eq_refl).
simpl.
   apply boundsmap_denote_e in BMD; rewrite list_forall_Forall in BMD;
   prepare_assumptions_about_free_variables.
lf_rewrites.
rewrite Rplus_assoc.
eapply Rle_trans.
eapply Rplus_le_compat.
apply Rle_refl.
match goal with |- context [?a <= ?b] =>
assert (a <= 2) as LE by interval with (i_prec 64);
apply LE
end.
nra.
Qed.

Lemma global_error_sum_x :
forall x v : float32, 
  (forall m: nat, 
  forall x' v' : float32, 
  (x',v') = (iternF m x%F32 v%F32) -> 
  boundsmap_denote leapfrog_bmap (leapfrog_vmap x' v')) ->
  forall n: nat, 
  forall x1 v1 : R,
  x1 = B2R _ _ x ->
  v1 = B2R _ _ v -> 
Rabs (fst(iternR (S n) x1%R v1%R) + (B2R 24 128 (fst (iternF (S n) x v)))) <= 
    ((delta_x error_x error_v n) + 2)%R.
Proof.
intros.
pose proof global_error_sum_x_aux x v H n x1 v1 H0 H1.
eapply Rle_trans.
apply Rabs_triang.
eapply Rle_trans.
apply Rplus_le_compat_r.
apply H2.
pose proof H (S n) as BMD. 
destruct (iternF (S n) x v).
specialize (BMD f f0 eq_refl).
simpl.
   apply boundsmap_denote_e in BMD; rewrite list_forall_Forall in BMD;
   prepare_assumptions_about_free_variables.
lf_rewrites.
rewrite Rplus_assoc.
eapply Rle_trans.
eapply Rplus_le_compat.
apply Rle_refl.
match goal with |- context [?a <= ?b] =>
assert (a <= 2) as LE by interval with (i_prec 64);
apply LE
end.
nra.
Qed.

Lemma local_error_sum_x_aux :
  forall x v : float32,
  forall x1 v1 : R,
  boundsmap_denote leapfrog_bmap (leapfrog_vmap x v)->
  x1 = B2R _ _ x ->
  v1 = B2R _ _ v ->  
   Rabs (fst(leapfrog_stepR (x1,v1))) <= 
    (error_x + Rabs (B2R _ _ (leapfrog_stepx x v)))%R.
Proof.
intros.
pose proof local_error_x x v x1 v1 H H0 H1.
eapply Rcomplements.Rle_minus_l.
eapply Rle_trans.
apply Rabs_triang_inv.
auto.
Qed.


Lemma local_error_sum_v_aux :
  forall x v : float32,
  forall x1 v1 : R,
  boundsmap_denote leapfrog_bmap (leapfrog_vmap x v)->
  x1 = B2R _ _ x ->
  v1 = B2R _ _ v ->  
   Rabs (snd(leapfrog_stepR (x1,v1))) <= 
    (error_v + Rabs (B2R _ _ (leapfrog_stepv x v)))%R.
Proof.
intros.
pose proof local_error_v x v x1 v1 H H0 H1.
eapply Rcomplements.Rle_minus_l.
eapply Rle_trans.
apply Rabs_triang_inv.
auto.
Qed.

Lemma local_error_sum_v :
  forall x v : float32,
  forall x1 v1 : R,
  x1 = B2R _ _ x ->
  v1 = B2R _ _ v ->  
  (forall m: nat, 
  forall x' v' : float32, 
  (x',v') = (iternF m x%F32 v%F32) -> 
  boundsmap_denote leapfrog_bmap (leapfrog_vmap x' v')) ->
    Rle (Rabs (Rplus (snd(leapfrog_stepR (x1,v1))) 
    (B2R _ _ (leapfrog_stepv x v)))) 
    (error_v + 2)%R.
Proof.
intros.
pose proof H1 0%nat x v as BMD; unfold iternF, leapfrog' in BMD; 
  specialize (BMD eq_refl).
pose proof local_error_sum_v_aux x v x1 v1 BMD H H0.
eapply Rle_trans.
apply Rabs_triang.
eapply Rle_trans.
apply Rplus_le_compat_r.
apply H2.
pose proof (H1 1%nat) as BMD2; unfold iternF, leapfrog' in BMD2. 
unfold leapfrog_stepv. destruct (leapfrog_step' (x, v)); simpl. 
  specialize (BMD2 f f0 eq_refl).
   apply boundsmap_denote_e in BMD2; rewrite list_forall_Forall in BMD2;
   prepare_assumptions_about_free_variables.
lf_rewrites.
rewrite Rplus_assoc.
eapply Rle_trans.
eapply Rplus_le_compat.
apply Rle_refl.
match goal with |- context [?a <= ?b] =>
assert (a <= 2) as LE by interval with (i_prec 64);
apply LE
end.
nra.
Qed.

Lemma local_error_sum_x :
  forall x v : float32,
  forall x1 v1 : R,
  x1 = B2R _ _ x ->
  v1 = B2R _ _ v ->  
  (forall m: nat, 
  forall x' v' : float32, 
  (x',v') = (iternF m x%F32 v%F32) -> 
  boundsmap_denote leapfrog_bmap (leapfrog_vmap x' v')) ->
    Rle (Rabs (Rplus (fst(leapfrog_stepR (x1,v1))) 
    (B2R _ _ (leapfrog_stepx x v)))) 
    (error_x + 2)%R.
Proof.
intros.
pose proof H1 0%nat x v as BMD; unfold iternF, leapfrog' in BMD; 
  specialize (BMD eq_refl).
pose proof local_error_sum_x_aux x v x1 v1 BMD H H0.
eapply Rle_trans.
apply Rabs_triang.
eapply Rle_trans.
apply Rplus_le_compat_r.
apply H2.
pose proof (H1 1%nat) as BMD2; unfold iternF, leapfrog' in BMD2. 
unfold leapfrog_stepx. destruct (leapfrog_step' (x, v)); simpl. 
  specialize (BMD2 f f0 eq_refl).
   apply boundsmap_denote_e in BMD2; rewrite list_forall_Forall in BMD2;
   prepare_assumptions_about_free_variables.
lf_rewrites.
rewrite Rplus_assoc.
eapply Rle_trans.
eapply Rplus_le_compat.
apply Rle_refl.
match goal with |- context [?a <= ?b] =>
assert (a <= 2) as LE by interval with (i_prec 64);
apply LE
end.
nra.
Qed.

Definition H_osc (x v :R) : R := x^ 2 + v^2. 

Theorem local_energy_error: 
  forall x v : float32,
  forall x1 v1 : R,
  x1 = B2R _ _ x ->
  v1 = B2R _ _ v ->  
  (forall m: nat, 
  forall x' v' : float32, 
  (x',v') = (iternF m x%F32 v%F32) -> 
  boundsmap_denote leapfrog_bmap (leapfrog_vmap x' v')) ->
  let xf2r := B2R 24 128 (fst (leapfrog_step' (x,v))) in
  let vf2r := B2R 24 128 (snd (leapfrog_step' (x,v))) in 
  let xr := fst (leapfrog_stepR (x1,v1)) in
  let vr := snd (leapfrog_stepR (x1,v1)) in 
    Rabs (H_osc xr vr - H_osc xf2r vf2r) <= 
(error_x^2 + error_v^2) + 2 * (error_v + error_x).
(*3.84175139e-7*)
Proof.
intros.
unfold H_osc.
eapply Rle_trans.
+ apply Rabs_triang_aux4.
+ 
pose proof local_error_sum_x x v x1 v1 H H0 H1.
pose proof local_error_sum_v x v x1 v1 H H0 H1.
specialize (H1 0%nat x v). unfold iternF, leapfrog' in H1. 
  specialize (H1 eq_refl).
pose proof local_error_x x v x1 v1 H1 H H0.
pose proof local_error_v x v x1 v1 H1 H H0.
unfold xr, vr, xf2r, vf2r in *.
unfold leapfrog_stepx, leapfrog_stepv in *.
eapply Rle_trans.
apply Rplus_le_compat_r.
apply Rmult_le_compat_r.
apply Rabs_pos.
apply H2.
eapply Rle_trans.
apply Rplus_le_compat_r.
apply Rmult_le_compat_l.
unfold error_x; nra.
apply H4.
eapply Rle_trans.
apply Rplus_le_compat_l.
apply Rmult_le_compat_l.
apply Rabs_pos.
apply H5.
eapply Rle_trans.
apply Rplus_le_compat_l.
apply Rmult_le_compat_r.
unfold error_v; nra.
apply H3.
interval_intro (error_x ^ 2 + error_v ^ 2 + 2 * (error_v + error_x)).
nra.
Qed.

Lemma deltas_pos (n : nat) : 
  0 <= delta_v error_x error_v n /\  0 <= delta_x error_x error_v n.
Proof.
induction n.
+ split.
-- unfold delta_v. unfold error_v; nra.
-- unfold delta_x. unfold error_x; nra.
+ destruct IHn as (IHnv & IHnx). split.
-- unfold delta_v.  fold delta_v. fold delta_x.
repeat apply Rle_plus; try  (unfold error_v; nra);
apply Rle_mult; try (unfold h; nra).
-- unfold delta_x.  fold delta_x. fold delta_v.
repeat apply Rle_plus; try  (unfold error_x; nra);
apply Rle_mult; try (unfold h; nra).
Qed.



Theorem global_energy_error: 
  forall x v : float32,
(forall m: nat, 
  forall x' v' : float32, 
  (x',v') = (iternF m x%F32 v%F32) -> 
  boundsmap_denote leapfrog_bmap (leapfrog_vmap x' v')) ->
  forall n: nat, 
  forall x1 v1 : R,
  x1 = B2R _ _ x ->
  v1 = B2R _ _ v -> 
    let xf2r := B2R _ _ (fst(iternF ( S n) x%F32 v%F32)) in
    let vf2r := B2R _ _ (snd(iternF ( S n) x%F32 v%F32)) in
    let xr := fst(iternR (S n) x1%R v1%R) in
    let vr := snd(iternR (S n) x1%R v1%R) in
    Rabs (H_osc xr vr - H_osc xf2r vf2r) <=  
    ((2 + delta_x error_x error_v n) * (delta_x error_x error_v n) + 
      (2 + delta_v error_x error_v n) * (delta_v error_x error_v n)).
Proof.
intros. 

unfold H_osc.
eapply Rle_trans.
eapply Rabs_triang_aux4.

pose proof (global_error_sum_x x v H n x1 v1 H0 H1) as GECx. 
pose proof (global_error_sum_v x v H n x1 v1 H0 H1) as GECv. 
pose proof global_error x v H n x1 v1 H0 H1 as GE;
   destruct GE as (GEx & GEv).

unfold xr, vr, xf2r, vf2r.

eapply  Rle_trans.
eapply Rplus_le_compat_l.
eapply Rmult_le_compat_r. apply Rabs_pos.
apply GECv.

eapply  Rle_trans.
eapply Rplus_le_compat_l.
eapply Rmult_le_compat_l. 
eapply Rplus_le_le_0_compat. 
apply deltas_pos.
nra.
apply GEv.

eapply  Rle_trans.
eapply Rplus_le_compat_r.
eapply Rmult_le_compat_l. apply Rabs_pos.
apply GEx.


eapply  Rle_trans.
eapply Rplus_le_compat_r.
eapply Rmult_le_compat_r. 
apply deltas_pos.
apply GECx.

nra.
Qed.
