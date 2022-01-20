From Flocq Require Import Binary Bits Core.
From compcert.lib Require Import IEEE754_extra Coqlib Floats Zbits Integers.
Require Import vcfloat float_lib lf_harm_float lf_harm_real lf_harm_lemmas.
Set Bullet Behavior "Strict Subproofs". 

Import FPLangOpt. 
Import FPLang.
Import FPSolve.
Import Test.

Import Interval.Tactic.


Definition error_v := (5079915575529618 / 75557863725914323419136)%R.
(* error_v = 6.723212283974809e-08 *)
Definition error_x := (4716905030025237 / 37778931862957161709568)%R.
(* error_x = 1.2485543654690345e-07*)


(* single step position error *)
Theorem one_step_error_x:
  forall x v : float32,
    boundsmap_denote (leapfrog_bmap ) (leapfrog_vmap x v)->
    Rle (Rabs (Rminus (rval (leapfrog_env  x v) (optimize_div x')) 
   (B2R _ _ (fval (leapfrog_env  x v) (optimize_div x'))))) 
         error_x.
Proof.
intros.
set (bmap:= leapfrog_bmap) in *.
hnf in bmap. simpl in bmap.
match goal with |- context [ rval ?env ?e] =>
simplify_shift_div_opt e
end.
(*unfold x'.*)
match goal with |- context [ rval ?env ?e] =>
get_rndval_with_conds e
end.
(* introduce and prove validity conditions *)
(* for optmize_div x', there are 4 conditions *) 
+ get_conds2;
repeat (apply List.Forall_cons; try apply List.Forall_nil;
try solve_one_cond2; 
try interval).
+ match goal with |- context [ rval ?env ?e] =>
get_rndval_with_cond_correct e H0 H1 rndval s p;
set (ty:= type_of_expr e) in *;
simpl in ty;
cbv [Datatypes.id] in ty;   
repeat change (type_lub Tsingle Tsingle) with Tsingle in ty; 
unfold ty in *; clear ty
end.
(* Populate hyps with some bounds on x and v*)
fv_prepare_assumptions.
(* turn rndval rexp to flt with eps delt *)
rndval_replace.
subst si2 s r;
get_eps_delts.
clear correct rndval H0 H1 H2 H3 e m H7.
revert e0. reduce_abs_error. 
(* env rewrite *)
replace ((env_ (leapfrog_vmap val_x val_v))) 
  with (leapfrog_env 
  val_x val_v) in * by
(apply lf_env_eq; apply BMD).
(* var rewrites *)
replace (leapfrog_env val_x val_v Tsingle lf_harm_lemmas._x) with 
  val_x in * by 
  (cbv in Hval_x;inversion Hval_x; clear Hval_x; subst; auto).
replace (leapfrog_env 
  val_x val_v Tsingle lf_harm_lemmas._v) with val_v in * by 
(cbv in Hval_v;inversion Hval_v; clear Hval_v; subst; auto).
change (fprec Tsingle) with 24%Z in *; 
change (femax Tsingle) with 128%Z in *.

intros. rewrite <- e0; clear H e0.

match goal with |- context [Rabs (?v) <= _] =>
field_simplify v
end.

match goal with |- context [Rabs (?v) <= _] =>
interval_intro (Rabs v)
end.
unfold error_x;  nra.
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
set (bmap:= leapfrog_bmap) in *.
hnf in bmap. simpl in bmap.
match goal with |- context [ rval ?env ?e] =>
simplify_shift_div_opt e
end.
match goal with |- context [ rval ?env ?e] =>
get_rndval_with_conds e
end.
(* introduce and prove validity conditions *)
(* for optmize_div v', there are 7 conditions *) 
+ get_conds2;
 repeat (apply List.Forall_cons; try apply List.Forall_nil;
try solve_one_cond2; 
try interval).
+ match goal with |- context [ rval ?env ?e] =>
get_rndval_with_cond_correct e H0 H1 rndval s p;
set (ty:= type_of_expr e) in *;
simpl in ty;
cbv [Datatypes.id] in ty;   
repeat change (type_lub Tsingle Tsingle) with Tsingle in ty; 
unfold ty in *; clear ty
end.
(* Populate hyps with some bounds on x and v*)
fv_prepare_assumptions.
(* turn rndval rexp to flt with eps delt *)
rndval_replace.
subst si2 s r;
get_eps_delts.
clear correct rndval H0 H1 H2 H3 e m H7.
revert e0. reduce_abs_error. 
(* env rewrite *)
replace ((env_ (leapfrog_vmap val_x val_v))) 
  with (leapfrog_env 
  val_x val_v) in * by
(apply lf_env_eq; apply BMD).
(* var rewrites *)
replace (leapfrog_env val_x val_v Tsingle lf_harm_lemmas._x) with 
  val_x in * by 
  (cbv in Hval_x;inversion Hval_x; clear Hval_x; subst; auto).
replace (leapfrog_env 
  val_x val_v Tsingle lf_harm_lemmas._v) with val_v in * by 
(cbv in Hval_v;inversion Hval_v; clear Hval_v; subst; auto).
change (fprec Tsingle) with 24%Z in *; 
change (femax Tsingle) with 128%Z in *.

intros. rewrite <- e0; clear H e0.

match goal with |- context [Rabs (?v) <= _] =>
field_simplify (v)
end.

match goal with |- context [Rabs (?v) <= _] =>
interval_intro (Rabs v)
end.
unfold error_v; nra.
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

Definition RHamiltonian (x v : R): R := 
  0.5%R * (powerRZ v 2 + powerRZ x 2) . 
Definition FHamiltonian (x v : float32): float32:= 
  (half  * (v * v + x * x) )%F32.

Definition H_osc (x v :R) : R := x^ 2 + v^2. 

Lemma local_energy_error: 
  forall x v : float32,
    boundsmap_denote (leapfrog_bmap ) (leapfrog_vmap x v)->
    let xf2r := (B2R _ _ (fval (leapfrog_env  x v) (optimize_div x'))) in
    let vf2r := (B2R _ _ (fval (leapfrog_env  x v) (optimize_div v'))) in
    let xr := rval (leapfrog_env  x v) (optimize_div x') in
    let vr := rval (leapfrog_env  x v) (optimize_div v') in
    Rabs (H_osc xr vr - H_osc xf2r vf2r) <=  
(5737052551188771447961625990175617189626654515220295204472916317044736 /
     14474011154664524427946373126085988481658748083205070504932198000989141204992).
(* 3.96369223e-7 *)
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
  (4646536420130843 / 2251799813685248) error_x (4646570650113169 / 2251799813685248) error_v
  H2 H0 H3 H1
end.
unfold error_x, error_v in *.
field_simplify in H4.
nra. 
Qed.
