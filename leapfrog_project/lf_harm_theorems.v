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

Lemma iter_real_bnded_x_v: forall x v : float32, 
  (forall m: nat, 
  forall x' v' : float32, 
  (x',v') = (iternF m x%F32 v%F32) -> 
  boundsmap_denote leapfrog_bmap (leapfrog_vmap x' v')) ->
  forall x1 v1 : R,
  x1 = B2R _ _ x ->
  v1 = B2R _ _ v -> 
forall n : nat,
let bnd:= (1 + lf_harm_real.h - 1/2 * lf_harm_real.h^2) in
  Rabs (fst(iternR n x1%R v1%R)) <= 
powerRZ bnd (Z.of_nat n) /\
  Rabs (snd(iternR n x1%R v1%R)) <= 
powerRZ bnd (Z.of_nat n).
Proof.
intros.
induction n.
+ simpl.
pose proof H 0%nat x v. unfold iternF, leapfrog' in H2.
pose proof H2 eq_refl.
fvs_from_bndsmap_hyp H3;
lf_rewrites;
split.
all: (apply Rbasic_fun.Rabs_le; nra).
+ assert (bnd <> 0) as Hbnd by (unfold bnd, lf_harm_real.h; nra).
replace (Z.of_nat (S n)) with ( (Z.of_nat n + 1%Z)%Z) by lia. 
rewrite ?powerRZ_add; auto. rewrite ?powerRZ_1.
rewrite ?step_iternR.
destruct (iternR n x1 v1) as (xnr, vnr). 
unfold iternR, leapfrog_stepR, fst, snd, lf_harm_real.h, lf_harm_real.F in *.
match goal with |- Rabs(?a) <= _ /\ Rabs(?b) <= _ =>
field_simplify b ;
field_simplify a 
end.
split; destruct IHn.
- rewrite Rcomplements.Rabs_div; try nra.
rewrite Rcomplements.Rle_div_l; try (apply Rabs_pos_lt; nra).
eapply Rle_trans.
eapply Rabs_triang.
rewrite ?abs_mul; try interval; try nra.
eapply Rle_trans.
eapply Rplus_le_compat.
eapply Rmult_le_compat_l in H2. apply H2. nra.
eapply Rmult_le_compat_l in H3. apply H3. nra.
rewrite <- Rmult_plus_distr_r .
rewrite Rmult_comm.
rewrite Rmult_assoc.
eapply Rmult_le_compat_l. 
apply powerRZ_le; unfold bnd; nra.
unfold bnd; field_simplify. 
rewrite Rabs_pos_eq; nra.
- rewrite Rcomplements.Rabs_div; try nra.
rewrite Rcomplements.Rle_div_l; try (apply Rabs_pos_lt; nra).
eapply Rle_trans.
replace ((4192256 * vnr - 131040 * xnr) ) with
(4192256 * vnr + 131040 * -xnr) by nra. 
eapply Rabs_triang.
rewrite ?abs_mul; try interval; try nra.
eapply Rle_trans.
eapply Rplus_le_compat.
eapply Rmult_le_compat_l in H3. apply H3. nra. 
rewrite Rabs_Ropp. eapply Rmult_le_compat_l in H2. apply H2. nra.
rewrite <- Rmult_plus_distr_r .
replace (powerRZ bnd (Z.of_nat n) * bnd * Rabs 4194304) with
(powerRZ bnd (Z.of_nat n) * (bnd * Rabs 4194304)) by nra.
rewrite Rmult_comm.
eapply Rmult_le_compat_l.
apply powerRZ_le; unfold bnd; nra.
unfold bnd. field_simplify. interval.
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


Lemma local_error_v_2 :
  forall x v : float32,
  boundsmap_denote leapfrog_bmap (leapfrog_vmap x v)-> 
  Rabs (B2R _ _ (fval (leapfrog_env  x v) (optimize_div v')))
   <= error_v + Rabs (rval (leapfrog_env  x v) (optimize_div v'))  .
Proof.
intros.
pose proof one_step_error_v x v H.
apply Rabs_le_minus. 
match goal with |- context [ Rabs(?a - ?b) <= _ ] =>
replace (Rabs(a - b)) with (Rabs(b -a)) by (apply Rabs_minus_sym)
end.
apply one_step_error_v; auto. 
Qed.

Lemma global_error_x_aux : 
  forall x v : float32,
  forall x' v' x'' v'' a b : R,
  boundsmap_denote leapfrog_bmap (leapfrog_vmap x v)->
  x' = B2R _ _ x -> v' = B2R _ _ v ->
  Rabs(x'' - x') <= a -> Rabs(v'' - v') <= b ->
  Rabs( fst (leapfrog_stepR (x'',v'')) - B2R _ _ (fst (leapfrog_step' (x,v)) )) <=
  ((1 - 0.5 * (pow lf_harm_real.h 2)) * a + (lf_harm_real.h) * b + error_x). 
Proof. 
intros.
match goal with |- context [Rabs(?x1 -?x3) <= ?c] =>
  let x2:= constr:(fst(leapfrog_stepR (x',v'))) in
  replace (Rabs(x1 - x3)) with (Rabs(x1 -x2 + x2 - x3)) by
  (field_simplify (x1 - x2 + x2 - x3); nra);
  set (aa:= (x1-x2));
  replace (Rminus (aa + x2) x3) with (Rplus aa (x2- x3)) by nra;
  set (bb:= (x2-x3));
  try apply Rabs_triang_aux; unfold aa; unfold bb; clear aa bb
end.
rewrite ?one_stepR_x_alt2.
apply Rabs_triang_aux2.
fold (leapfrog_stepx x v).
apply Rabs_triang_aux3.
+ unfold fst, lf_harm_real.h. rewrite ?abs_mul; nra.
+ unfold snd, lf_harm_real.h. rewrite ?abs_mul; nra.
+ apply local_error_x; auto.
Qed.


Lemma global_error_v_aux : 
  forall x v : float32,
  forall x' v' x'' v'' a b : R,
  boundsmap_denote leapfrog_bmap (leapfrog_vmap x v)->
  x' = B2R _ _ x -> v' = B2R _ _ v ->
  Rabs(x'' - x') <= a -> Rabs(v'' - v') <= b ->
  Rabs( snd (leapfrog_stepR (x'',v'')) - B2R _ _ (snd (leapfrog_step' (x,v)) )) <=
  ((1 - 0.5 * (pow lf_harm_real.h 2)) * b + 
    (0.5 * (lf_harm_real.h) * (2 - 0.5 * (pow lf_harm_real.h 2 )) * a) + error_v). 
Proof. 
intros.
match goal with |- context [Rabs(?x1 -?x3) <= ?c] =>
  let x2:= constr:(snd(leapfrog_stepR (x',v'))) in
  replace (Rabs(x1 - x3)) with (Rabs(x1 -x2 + x2 - x3)) by
  (field_simplify (x1 - x2 + x2 - x3); nra);
  set (aa:= (x1-x2));
  replace (Rminus (aa + x2) x3) with (Rplus aa (x2- x3)) by nra;
  set (bb:= (x2-x3));
  try apply Rabs_triang_aux; unfold aa; unfold bb; clear aa bb
end.
rewrite ?one_stepR_v_alt2.
apply Rabs_triang_aux2.
fold (leapfrog_stepv x v).
apply Rabs_triang_aux3.
+ unfold snd, lf_harm_real.h; rewrite ?abs_mul; nra.
+ unfold fst, lf_harm_real.h; rewrite ?Rabs_Ropp; rewrite ?abs_mul; nra.
+ apply local_error_v; auto.
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
  INR n <= 0.5 * 1/lf_harm_real.h -> 
  Rle (Rabs (Rminus (fst(iternR n x1%R v1%R)) (B2R _ _ (fst(iternF n x%F32 v%F32))))) 
   (2*(pow lf_harm_real.h 3) * sqrt (INR n)) /\
  Rle (Rabs (Rminus (snd(iternR n x1%R v1%R)) (B2R _ _ (snd(iternF n x%F32 v%F32))))) 
  (2*(pow lf_harm_real.h 3) * sqrt (INR n)) .
Proof.
intros. 
replace (0.5 * 1 / lf_harm_real.h) with 
16 in H2 by (unfold lf_harm_real.h; nra).
induction n.
- unfold iternF ,iternR ,INR, leapfrog', leapfrogR, 
leapfrog_stepx,lf_harm_real.h.
unfold fst; unfold snd; subst.
replace (B2R 24 128 x - B2R 24 128 x) with 0 by nra;
replace (B2R 24 128 v - B2R 24 128 v) with 0 by nra.
split. all: (rewrite ?sqrt_0; interval).
- rewrite ?S_INR in H2.
apply Rminus_plus_le_minus in H2; field_simplify in H2.
assert (INR n <= 16) as Hn by nra.
pose proof IHn Hn; clear IHn Hn;
assert (INR n <= 15) as Hn by nra; clear H2.
rewrite ?step_iternR; rewrite ?step_iternF. 
try pose proof H n 
  ((fst (iternF n x v))) ((snd (iternF n x v))); clear H. 
destruct (iternR n x1 v1) as (xnr, vnr). 
destruct (iternF n x v) as (xnf, vnf).
unfold fst, snd in H2; pose proof H2 eq_refl; clear H2.
unfold fst, snd in H3. 
set (r_xnf:= B2R _ _ xnf ) in *; assert (r_xnf = B2R 24 128 xnf) by auto.
set (r_vnf:= B2R _ _ vnf) in *;  assert (r_vnf = B2R 24 128 vnf) by auto.
rewrite ?step_iternR; rewrite ?step_iternF. 
set (a:= 2 * lf_harm_real.h ^ 3 * sqrt (INR n)).
destruct H3 as (IHx & IHv); split.
(* x case *)
+ pose proof global_error_x_aux 
  xnf vnf r_xnf r_vnf xnr vnr a a H H2 H4 IHx IHv.
eapply Rle_trans. 
-- apply H3.
-- rewrite ?S_INR.
unfold error_x, a, lf_harm_real.h in *.
pose proof pos_INR n.
apply Rminus_le.
(* depth is necessary for sqrt? *)
try interval with  
(i_bisect (INR n), i_depth 15).
(* v case *)
+ pose proof global_error_v_aux 
  xnf vnf r_xnf r_vnf xnr vnr a a H H2 H4 IHx IHv.
eapply Rle_trans. 
-- apply H3.
-- rewrite ?S_INR.
unfold error_v, a, lf_harm_real.h in *.
pose proof pos_INR n.
apply Rminus_le.
(* depth is necessary for sqrt? *)
try interval with  
(i_bisect (INR n), i_depth 15).
Qed.


Definition global_error_val n := 
(2*(pow lf_harm_real.h 3) * sqrt (INR n))%R.


Definition iter_R_val := 
(1 + lf_harm_real.h - 1/2 * lf_harm_real.h^2).


Lemma global_error_corollary:
forall x v : float32, 
  (forall m: nat, 
  forall x' v' : float32, 
  (x',v') = (iternF m x%F32 v%F32) -> 
  boundsmap_denote leapfrog_bmap (leapfrog_vmap x' v')) ->
  forall n: nat, 
  forall x1 v1 : R,
  x1 = B2R _ _ x ->
  v1 = B2R _ _ v -> 
  INR n <= 0.5 * 1/lf_harm_real.h -> 
  Rabs (fst(iternR n x1%R v1%R) + B2R 24 128 (fst (iternF n x v))) <= 
 2 * Rabs (fst(iternR n x1%R v1%R)) + global_error_val n
 /\
  Rabs (snd(iternR n x1%R v1%R) + B2R 24 128 (snd (iternF n x v))) <= 
 2 * Rabs (snd(iternR n x1%R v1%R)) + global_error_val n.
Proof.
intros.
pose proof global_error x v H n x1 v1 H0 H1 H2.
destruct H3.
split.
+ eapply Rle_trans.
eapply Rabs_triang.
match goal with |- context [_ <= 2 * ?a + ?b ] =>
replace (2 *a + b) with (a + (a + b)) by nra 
end.
eapply  Rplus_le_compat_l .
rewrite Rplus_comm.
eapply Rabs_le_minus.
rewrite <- Rabs_Ropp.
rewrite Ropp_minus_distr.
apply H3.
+ eapply Rle_trans.
eapply Rabs_triang.
match goal with |- context [_ <= 2 * ?a + ?b ] =>
replace (2 *a + b) with (a + (a + b)) by nra 
end.
eapply  Rplus_le_compat_l .
rewrite Rplus_comm.
eapply Rabs_le_minus.
rewrite <- Rabs_Ropp.
rewrite Ropp_minus_distr.
apply H4.
Qed.


Definition H_osc (x v :R) : R := x^ 2 + v^2. 


Theorem local_energy_error: 
  forall x v : float32,
    boundsmap_denote (leapfrog_bmap ) (leapfrog_vmap x v)->
    let xf2r := (B2R _ _ (fval (leapfrog_env  x v) (optimize_div x'))) in
    let vf2r := (B2R _ _ (fval (leapfrog_env  x v) (optimize_div v'))) in
    let xr := rval (leapfrog_env  x v) (optimize_div x') in
    let vr := rval (leapfrog_env  x v) (optimize_div v') in
    Rabs (H_osc xr vr - H_osc xf2r vf2r) <= 
5737052551189115355431825195770061827073493817295873037556855259267072 /
     14474011154664524427946373126085988481658748083205070504932198000989141204992.
(*3.963692227320304e-07*)
Proof.
intros.
set (bmap:= leapfrog_bmap) in *.
hnf in bmap. simpl in bmap.
unfold H_osc.
eapply Rle_trans.
+ apply Rabs_triang_aux4.
+ 
pose proof one_step_error_x x v H.
pose proof one_step_error_v x v H.
pose proof one_step_sum_x x v H.
pose proof one_step_sum_v x v H.
unfold xr, vr, xf2r, vf2r in *.
match goal with 
  |- context [ Rabs (?a) * Rabs (?b) + Rabs (?c) *Rabs (?d) <= _] =>
pose proof Rabs_le_aux 
  a b c d 
  one_step_sum_bnd_x error_x one_step_sum_bnd_v error_v
  H2 H0 H3 H1
end.
unfold error_x, error_v, one_step_sum_bnd_v, one_step_sum_bnd_x in *.
field_simplify in H4.
nra. 
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
  INR n <= 0.5 * 1/lf_harm_real.h -> 
    let xf2r := B2R _ _ (fst(iternF n x%F32 v%F32)) in
    let vf2r := B2R _ _ (snd(iternF n x%F32 v%F32)) in
    let xr := fst(iternR n x1%R v1%R) in
    let vr := snd(iternR n x1%R v1%R) in
    
    Rabs (H_osc xr vr - H_osc xf2r vf2r) <= 
    (4 * powerRZ iter_R_val (Z.of_nat n) * global_error_val n +
2 * global_error_val n ^ 2)%R.
Proof.
intros. 

unfold H_osc.
eapply Rle_trans.
eapply Rabs_triang_aux4.

pose proof global_error_corollary x v H n x1 v1 H0 H1 H2; destruct H3.
pose proof global_error x v H n x1 v1 H0 H1 H2; destruct H5.

eapply  Rle_trans.
eapply Rplus_le_compat_l.
eapply Rmult_le_compat_r; try interval.
apply H4.

eapply  Rle_trans.
eapply Rplus_le_compat_l.
eapply Rmult_le_compat_l.
unfold global_error_val.
unfold lf_harm_real.h.  
eapply Rplus_le_le_0_compat. 
eapply Rmult_le_pos; try nra.
apply Rabs_pos. 
eapply Rmult_le_pos; try nra.
apply sqrt_positivity. 
apply pos_INR.
apply H6.

eapply  Rle_trans.
eapply Rplus_le_compat_r.
eapply Rmult_le_compat_l; try interval.
apply H5.

eapply  Rle_trans.
eapply Rplus_le_compat_r.
eapply Rmult_le_compat_r.
eapply Rmult_le_pos; unfold lf_harm_real.h; try nra.
apply sqrt_positivity. 
apply pos_INR.
apply H3.

pose proof H n.
destruct (iternF n x v). simpl in xf2r. simpl in vf2r.
pose proof H7 f f0 eq_refl.
pose proof iter_real_bnded_x_v x v H x1 v1 H0 H1 n.
destruct H9.
fold iter_R_val in *.

eapply  Rle_trans.
eapply Rplus_le_compat_r.
eapply Rmult_le_compat_r.
eapply Rmult_le_pos; try nra; try unfold lf_harm_real.h; try nra.  
apply sqrt_positivity. 
apply pos_INR.
eapply Rplus_le_compat_r.
eapply Rmult_le_compat_l; try nra.
apply H9.

eapply  Rle_trans.
eapply Rplus_le_compat_l.
eapply Rmult_le_compat_r.
eapply Rmult_le_pos; try nra; try unfold lf_harm_real.h; try nra.  
apply sqrt_positivity. 
apply pos_INR.
eapply Rplus_le_compat_r.
eapply Rmult_le_compat_l; try nra.
apply H10.

fold (global_error_val n).
field_simplify.
nra.
Qed.
