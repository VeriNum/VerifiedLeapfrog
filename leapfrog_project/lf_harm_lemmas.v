(** Test.v:  application demo of "ftype" usage-style of VCfloat.
 Copyright (C) 2021-2022 Andrew W. Appel and Ariel Kellison.
*)

From vcfloat Require Import FPLang FPLangOpt RAux Rounding Reify Float_notations Automate.
Require Import Interval.Tactic.
Import Binary.
Import List ListNotations.
Set Bullet Behavior "Strict Subproofs".

Require Import lf_harm_float lf_harm_real real_lemmas lf_harm_real_theorems.


Open Scope R_scope.

Section WITHNANS.


Context {NANS: Nans}.


Definition leapfrog_stepp p q  := fst (leapfrog_stepF (p,q)).
Definition leapfrog_stepq p q := snd (leapfrog_stepF (p,q)).



Definition _p : ident := 1%positive.  (* Variable name for position *)
Definition _q : ident := 2%positive.  (* Variable name for velocity *)



Definition p' := ltac:(let e' := 
  HO_reify_float_expr constr:([_p; _q]) leapfrog_stepp in exact e').
Definition q' := ltac:(let e' := 
  HO_reify_float_expr constr:([_p; _q]) leapfrog_stepq in exact e').



Definition leapfrog_vmap_list (p q : ftype Tsingle) := 
   [(_p, existT ftype _ p);(_q, existT ftype _ q)].


Definition leapfrog_vmap (p q : ftype Tsingle) : valmap :=
 ltac:(let z := compute_PTree (valmap_of_list (leapfrog_vmap_list p q)) in exact z).


Definition leapfrog_bmap_list : list varinfo := 
  [ Build_varinfo Tsingle _p (-2)  2 ;  Build_varinfo Tsingle _q (-2)  2 ].


Definition leapfrog_bmap : boundsmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list leapfrog_bmap_list) in exact z).


Lemma prove_roundoff_bound_q:
  forall p q : ftype Tsingle,
  prove_roundoff_bound leapfrog_bmap (leapfrog_vmap p q) q' 
    (/ 4068166).
Proof.
intros.
prove_roundoff_bound.
- abstract (prove_rndval; interval).
-
  prove_roundoff_bound2.
 match goal with |- Rabs ?a <= _ => field_simplify a end.
 interval.
Qed.

Lemma prove_roundoff_bound_p:
  forall p q : ftype Tsingle,
  prove_roundoff_bound leapfrog_bmap (leapfrog_vmap p q) p' 
   (/4065000).
Proof.
intros.
prove_roundoff_bound.
- abstract (prove_rndval; interval).
-
  prove_roundoff_bound2.

 match goal with |- Rabs ?a <= _ => field_simplify a end.
interval.
Qed.


Lemma prove_roundoff_bound_q_implies:
  forall p q : ftype Tsingle,
boundsmap_denote leapfrog_bmap (leapfrog_vmap p q)-> 
Rabs (FT2R (fval (env_ (leapfrog_vmap p q)) q') - rval (env_ (leapfrog_vmap p q)) q') <= (/ 4068166)
.
Proof.
intros.
pose proof prove_roundoff_bound_q p q.
unfold prove_roundoff_bound in H0. 
specialize (H0 H).
unfold roundoff_error_bound in H0; auto. 
Qed.

Lemma prove_roundoff_bound_p_implies:
  forall p q : ftype Tsingle,
boundsmap_denote leapfrog_bmap (leapfrog_vmap p q)-> 
Rabs (FT2R (fval (env_ (leapfrog_vmap p q)) p') - rval (env_ (leapfrog_vmap p q)) p') <= (/4065000)
.
Proof.
intros.
pose proof prove_roundoff_bound_p p q.
unfold prove_roundoff_bound in H0. 
specialize (H0 H).
unfold roundoff_error_bound in H0; auto. 
Qed.

Definition FT2R_prod (A: ftype Tsingle * ftype Tsingle)  := (FT2R (fst A), FT2R (snd A)).

Lemma roundoff_norm_bound:
 forall p q : ftype Tsingle,
boundsmap_denote leapfrog_bmap (leapfrog_vmap p q)-> 
let (pnf, qnf) := FT2R_prod (fval (env_ (leapfrog_vmap p q)) p', fval (env_ (leapfrog_vmap p q)) q') in 
let (pnr, qnr) := (rval (env_ (leapfrog_vmap p q)) p', rval (env_ (leapfrog_vmap p q)) q') in
∥ (pnf, qnf) .- (pnr, qnr)∥ <= ∥(/4065000, / 4068166)∥.
Proof.
intros.
unfold Rprod_minus, FT2R_prod, Rprod_norm, fst, snd.
rewrite <- pow2_abs.
rewrite Rplus_comm.
rewrite <- pow2_abs.
pose proof prove_roundoff_bound_p_implies p q H.
pose proof prove_roundoff_bound_q_implies p q H.
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


Hypothesis iternR_bnd:
  forall p q n,
  ∥iternR (p,q) h n∥ <= (sqrt 2 * ∥(p,q)∥).


Lemma error_sum_bound: 
  forall n,
  (n <= 200)%nat -> 
  error_sum (1 + h) n <= 15033.
Proof.
intros.
eapply Rle_trans.
eapply error_sum_le_trans. 
  apply H. try unfold h; try nra.
assert (Hyph: 1 + h <> 1 ) by (unfold h ;nra).
pose proof geo_series_closed_form (1 + h) 199 Hyph.
unfold error_sum; rewrite H0.
replace ((1 - (1 + h) ^ 200) / (1 - (1 + h))) with (  ((1 + h) ^ 200 - 1) /  h).
rewrite Rcomplements.Rle_div_l; try (unfold h; nra).
set (a:=(1 + h) ^ 200).
field_simplify; try nra. 
apply Stdlib.Rdiv_eq_reg; try nra.
Qed.


Lemma itern_implies_bmd_aux1:
  forall pnf qnf : ftype Tsingle,
  forall pnr qnr : R,
  forall n,
  (n <= 200)%nat -> 
  ∥ Rprod_minus (pnr, qnr) (FT2R_prod (pnf, qnf)) ∥ <=  ∥(/4065000, / 4068166)∥ * error_sum (1 + h) n 
  /\ ∥(pnr,qnr) ∥ <= 1.5 -> 
  Rabs (FT2R pnf)  <= 2 /\ Rabs ( FT2R qnf) <= 2.
Proof.
intros ? ? ? ? ? BNDn H. destruct H as (A & B).
assert (HYP1: ∥ Rprod_minus (pnr, qnr) (FT2R_prod (pnf, qnf)) ∥ <=
(∥ ( /4065000, / 4068166) ∥) * error_sum (1 + h) 200).
+ eapply Rle_trans.
2 :  { 
apply Rmult_le_compat_l; try (apply Rnorm_pos). 
eapply error_sum_le_trans. apply BNDn. unfold h; nra.
} apply A.
+ clear A. 
assert ( HYP2 :∥ Rprod_minus (pnr, qnr) (FT2R_prod (pnf, qnf)) ∥ <=
     (∥ (/4065000, / 4068166) ∥) * 15033).
eapply Rle_trans.
apply HYP1.
apply Rmult_le_compat_l; try (apply Rnorm_pos).
apply error_sum_bound; try lia.
clear HYP1. 
assert (HYP3: (∥ (FT2R_prod (pnf, qnf))∥ - ∥ (pnr, qnr) ∥) <= (∥ (/4065000, / 4068166) ∥) * 15033 ).
eapply Rle_trans.
apply Rprod_triang_inv.
apply HYP2.
apply Rle_minus_l_2 in HYP3. 
assert (HYP4: ∥ FT2R_prod (pnf, qnf) ∥ <= 1.5 + (∥ (/4065000, / 4068166) ∥) * 15033).
eapply Rle_trans.
2: {apply Rplus_le_compat_r. apply B.
} apply HYP3. clear HYP2.
generalize HYP4.
match goal with |-context[Rprod_norm ?A <= ?a]=>
  interval_intro a upper; intros ?HYP; clear HYP
end. 
unfold Rprod_norm in HYP4. 
unfold FT2R_prod, fst ,snd in HYP4.
assert (HYP5: sqrt (FT2R pnf  ^ 2 + FT2R qnf ^ 2) <= sqrt ((6778944017806265 / 4503599627370496)^2) ).
eapply Rle_trans. apply  HYP4.
rewrite sqrt_pow2; try nra. apply H.
apply sqrt_le_0 in HYP5; try nra.
split. 
++ assert (FT2R pnf ^ 2 <= (6778944017806265 / 4503599627370496) ^ 2) by nra.
apply sqrt_le in H0.
rewrite sqrt_pow2 in H0.
all: (try interval).
++ assert (FT2R qnf ^ 2 <= (6778944017806265 / 4503599627370496) ^ 2) by nra.
apply sqrt_le in H0.
rewrite sqrt_pow2 in H0.
all: (try interval).
Qed.


Lemma leapfrog_vmap_i_aux: 
forall p1 q1 p0 q0,
forall i,
forall v1 : {x : type & ftype x},
Maps.PTree.get i (leapfrog_vmap p0 q0) = Some v1 -> 
exists v2 : {x : type & ftype x},
Maps.PTree.get i (leapfrog_vmap p1 q1) = Some v2 /\ 
projT1 v1 = projT1 v2.
Proof.
intros.
apply Maps.PTree.elements_correct in H.
destruct H.
+ inversion H. subst. clear H.
exists (existT ftype Tsingle q1).
simpl. auto.
+ simpl in H. destruct H; try contradiction. 
inversion H.  clear H.
exists (existT ftype Tsingle p1).
simpl. auto.
Qed.




Lemma reflect_reify_q : forall p q, 
             fval (env_ (leapfrog_vmap p q)) q' = leapfrog_stepq p q.
Proof.
intros.
destruct true.  
- unfold q', leapfrog_stepq, leapfrog_stepF, F,  fst, snd, lf_harm_float.h, half_pow2_h.
Admitted.


Lemma reflect_reify_p : forall p q, fval (env_ (leapfrog_vmap p q)) p' = leapfrog_stepp p q.
Proof.
intros.
Admitted.

Lemma rval_correct_p : 
forall pnf qnf,
rval (env_ (leapfrog_vmap pnf qnf)) p' = fst (leapfrog_stepR (FT2R_prod (pnf,qnf)) h).
Proof.
Admitted.


Lemma rval_correct_q : 
forall pnf qnf,
rval (env_ (leapfrog_vmap pnf qnf)) q' = snd (leapfrog_stepR (FT2R_prod (pnf,qnf)) h).
Proof.
Admitted.


Lemma itern_implies_bmd_aux:
  forall p0 q0 : ftype Tsingle,
  forall n,
  boundsmap_denote leapfrog_bmap 
    (leapfrog_vmap (fst(iternF (p0,q0) n)) (snd(iternF (p0,q0) n))) ->
  (is_finite _ _  (fst(iternF (p0,q0) (S n))) = true) /\
(is_finite _ _  (snd(iternF (p0,q0) (S n))) = true).
Proof.
intros.
induction n. 
- split.
+ unfold iternF, leapfrogF.
replace (fst (leapfrog_stepF (p0, q0))) with
  (leapfrog_stepp p0 q0) by auto.
rewrite <- reflect_reify_p.
Admitted.



Lemma bmd_Sn_bnds_le : 
forall i,
forall v : varinfo,
Maps.PTree.get i leapfrog_bmap = Some v-> 
v.(var_lobound) = -2 /\ 
v.(var_hibound) = 2.
Proof.
intros.
apply Maps.PTree.elements_correct in H.
inversion H.
- inversion H0.
simpl; auto.
- inversion H0.
+  inversion H1. simpl; auto.
+ simpl in H1; try contradiction. 
Qed.



Lemma itern_implies_bmd:
  forall p0 q0 : ftype Tsingle,
  forall n,
  (S n <= 200)%nat -> 
  boundsmap_denote leapfrog_bmap 
    (leapfrog_vmap (fst(iternF (p0,q0) n)) (snd(iternF (p0,q0) n))) ->
  ∥(iternR (FT2R p0, FT2R q0) h (S n)) .- FT2R_prod (iternF (p0,q0)  (S n)) ∥ <= 
  (∥ (/4065000, / 4068166) ∥) * error_sum (1 + h) (S n)  /\
∥ (iternR (FT2R p0, FT2R q0) h  (S n))∥ <= 1.5 ->
   boundsmap_denote leapfrog_bmap (leapfrog_vmap (fst(iternF (p0,q0) (S n))) (snd(iternF (p0,q0) (S n)))).
Proof. 
intros ? ? ? BNDn BMD NORM.
pose proof (itern_implies_bmd_aux p0 q0 n BMD) as HFIN.
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
destruct ((iternF (p0, q0) n)).
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
specialize (HBND f1 f2 r r0 (S n) BNDn NORM). 
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
specialize (HBND f1 f2 r r0 (S n) BNDn NORM). 
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
destruct ((iternF (p0, q0) n)).
set (f1 := (fst (leapfrog_stepF (f, f0)))) in *.
set (f2:=(snd (leapfrog_stepF (f, f0)))) in *.
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


Definition p_init: ftype Tsingle :=  0%F32.
Definition q_init: ftype Tsingle :=  1%F32.

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


Lemma init_norm_bound :
forall n,
∥ iternR (FT2R p_init, FT2R q_init) h n ∥ <= 1.5. 
Proof.
intros.
specialize (iternR_bnd (FT2R p_init) (FT2R q_init) n).
pose proof init_norm_eq.
rewrite H in iternR_bnd; clear H.
rewrite Rmult_1_r in iternR_bnd.
interval.
Qed.

Lemma global_error : 
  boundsmap_denote leapfrog_bmap 
    (leapfrog_vmap p_init q_init) ->
  forall n : nat, 
  (n <= 200)%nat -> 
  boundsmap_denote leapfrog_bmap 
    (leapfrog_vmap (fst(iternF (p_init,q_init) n)) (snd(iternF (p_init,q_init) n))) /\
  ∥(iternR (FT2R p_init, FT2R q_init) h n) .- FT2R_prod (iternF (p_init,q_init) n) ∥ <= (∥ (/ 4065000, / 4068166) ∥) * error_sum (1 + h) n.
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
destruct (iternF (p_init,q_init) n) as (pnf, qnf).

match goal with |- context[∥?a .- ?b∥ <=  _] =>
  let c := (constr:(leapfrog_stepR (FT2R_prod (pnf, qnf)) h)) in
  replace (∥a .- b∥) with (∥ Rprod_plus (a .- c) (c .- b) ∥)
end.
eapply Rle_trans.
apply Rprod_triang_ineq.
rewrite leapfrog_minus_args.
eapply Rle_trans.
apply Rplus_le_compat_l.
assert (BNDn: (n<= 200)%nat) by lia.
assert (∥ Rprod_minus (pnr, qnr) (FT2R_prod (pnf, qnf)) ∥ <=
      (∥ (/ 4065000, / 4068166) ∥) * error_sum (1 + h) n /\ ∥ (pnr, qnr) ∥ <= 1.5).
split; auto.
pose proof (roundoff_norm_bound pnf qnf IHbmd) as BND.
rewrite reflect_reify_p in BND.
rewrite reflect_reify_q in BND.
change (leapfrog_stepp pnf qnf, leapfrog_stepq pnf qnf) with 
  (leapfrog_stepF (pnf, qnf)) in BND.
rewrite rval_correct_q in BND. 
rewrite rval_correct_p in BND.
change ((fst (leapfrog_stepR (FT2R_prod (pnf, qnf)) h),
         snd (leapfrog_stepR (FT2R_prod (pnf, qnf)) h))) with 
(leapfrog_stepR (FT2R_prod (pnf, qnf)) h) in BND.
destruct (FT2R_prod (leapfrog_stepF (pnf, qnf))). 
rewrite Rprod_minus_comm in BND. 
apply BND.  
destruct (Rprod_minus (pnr, qnr) (FT2R_prod (pnf, qnf))).
assert (0 < h < 2) as Hh by (unfold h; nra).
pose proof (method_norm_bounded r r0 h Hh) as BND.
eapply Rle_trans.
apply Rplus_le_compat_r.
apply BND. 
eapply Rle_trans.
apply Rplus_le_compat_r.
apply Rmult_le_compat_l; try (unfold h; nra).
assert (BNDn: (n<= 200)%nat) by lia.
apply IHnorm. 
set (aa:= (∥ (/ 4065000, / 4068166) ∥)). 
replace ((1 + h) * (aa * error_sum (1 + h) n) + aa)
with
(aa * ((1 + h) * (error_sum (1 + h) n) + 1)) by nra.
rewrite <- error_sum_aux2. nra.
symmetry. apply Rprod_norm_plus_minus_eq.
+ destruct IHn as (IHbmd & IHnorm); try lia.
apply itern_implies_bmd; try lia; auto; split; auto.
pose proof init_norm_bound (S n); auto.
Qed. 


Lemma leapfrog_vmap_init: 
forall i,
forall v1 : (sigT ftype),
Maps.PTree.get i (leapfrog_vmap p_init q_init) = Some v1 -> 
v1 = (existT ftype Tsingle q_init) \/
v1 = (existT ftype Tsingle p_init).
Proof. 
intros.
apply Maps.PTree.elements_correct in H.
destruct H.
- inversion H.
left; auto.
- inversion H.
+ inversion H0.
* right; auto.
+ inversion H0; auto.
Qed.



Lemma leapfrog_bmap_aux:
forall (i : positive) (v: varinfo),
       Maps.PTree.get i leapfrog_bmap = Some v -> 
       Maps.PTree.get i leapfrog_bmap = Maps.PTree.get _q leapfrog_bmap \/
       Maps.PTree.get i leapfrog_bmap = Maps.PTree.get _p leapfrog_bmap.
Proof.
intros.
apply Maps.PTree.elements_correct in H.
inversion H.
- 
inversion H0. left; auto.
- inversion H0.
inversion H1.
+ 
 right; auto.
+ simpl in H1; contradiction.
Qed.

Lemma leapfrog_bmap_aux1:
forall (i : positive) (v : varinfo),
       Maps.PTree.get i leapfrog_bmap = Some v ->
v.(var_name) = i. 
Proof.
intros.
apply Maps.PTree.elements_correct in H.
destruct H.
- inversion H. auto.
- inversion H; inversion H0; subst; auto.
Qed. 


Lemma bmd_vmap_bmap_iff : 
forall (i : positive)
(p q: ftype Tsingle),
(exists (v : varinfo),
       Maps.PTree.get i leapfrog_bmap = Some v) <->
(exists (v1 : sigT ftype),
       Maps.PTree.get i (leapfrog_vmap p q) = Some v1).
Proof.
intros.
split.
- intros.
destruct H.
apply Maps.PTree.elements_correct in H.
inversion H.
+ exists (existT ftype Tsingle q).
inversion H0.
subst.
cbv. auto.
+ exists (existT ftype Tsingle p).
inversion H0. inversion H1.
* 
cbv. auto.
*  simpl in H1; contradiction.
- intros.
destruct H.
apply Maps.PTree.elements_correct in H.
destruct H.
+ exists 
(    {|
      var_type := Tsingle;
      var_name := _q;
      var_lobound := (-2);
      var_hibound := 2
    |}).
inversion H; auto.
+ inversion H. 
* inversion H0.
exists 
(    {|
      var_type := Tsingle;
      var_name := _p;
      var_lobound := (-2);
      var_hibound := 2
    |}).
auto.
* inversion H0.
Qed.


Lemma bmd_init : 
  boundsmap_denote leapfrog_bmap (leapfrog_vmap p_init q_init) .
Proof.
intros.
unfold boundsmap_denote.
intros.
pose proof leapfrog_bmap_aux i as H1.
pose proof leapfrog_vmap_init i as H2.
pose proof bmd_vmap_bmap_iff i p_init q_init as H3.
pose proof leapfrog_bmap_aux1 i as H4.
destruct (Maps.PTree.get i leapfrog_bmap).
-
specialize (H1 v eq_refl).
destruct H1 as [H1|H1].
+  
symmetry in H1.
apply Maps.PTree.elements_correct in H1.
specialize (H4 v eq_refl).
inversion H1.
* 
inversion H.
destruct v.
inversion H5.
destruct H3 as (A & B). destruct A. 
exists ({|
      var_type := Tsingle; var_name := _q; var_lobound := -2; var_hibound := 2
    |}); subst; auto.
destruct (Maps.PTree.get i (leapfrog_vmap p_init q_init)); 
  try discriminate.
subst.
specialize (H2 s eq_refl).
-- destruct H2.
++ 
split; simpl; auto.
rewrite H2; repeat (split; simpl; auto; try interval).
++
split; simpl; auto.
rewrite H2; repeat (split; simpl; auto; try interval).
* 
simpl in H. destruct H; try contradiction.
-- destruct H3.
++ destruct v. inversion H.
+
symmetry in H1.
apply Maps.PTree.elements_correct in H1.
specialize (H4 v eq_refl).
inversion H1.
* inversion H; clear H.
* simpl in H. destruct H; try contradiction.

-- destruct H3.
++ destruct v. inversion H.

destruct H0.
exists ({|
      var_type := Tsingle; var_name := _p; var_lobound := -2; var_hibound := 2
    |});subst;auto.
destruct (Maps.PTree.get i (leapfrog_vmap p_init q_init)); 
  try discriminate.
subst.
specialize (H2 s eq_refl).
destruct H2.
**
split; simpl; auto.
rewrite H2. repeat (split; simpl; auto; try interval).
** split; simpl; auto.
rewrite H2. repeat (split; simpl; auto; try interval).

- destruct (Maps.PTree.get i (leapfrog_vmap p_init q_init)); auto.
destruct H3.
destruct H0; try discriminate.
exists s; auto.
Qed.

Theorem total_error: 
  forall pt qt: R -> R,
  forall n : nat, 
  (n <= 200)%nat ->
  let t0 := 0 in
  let tn := t0 + INR n * h in
  let w  := 1 in
  Harmonic_osc_system pt qt w t0 (FT2R p_init) (FT2R q_init) ->
  (forall t1 t2: R,
  k_differentiable pt 4 t1 t2 /\
  k_differentiable qt 3 t1 t2)  ->
  ∥ (pt tn, qt tn) .- (FT2R_prod (iternF (p_init,q_init) n)) ∥ <= 
  (h^2  + (∥ (/ 4065000, / 4068166) ∥) / h) * ((1 + h)^ n - 1) .
Proof.
assert (BMD: boundsmap_denote leapfrog_bmap (leapfrog_vmap p_init q_init)) by
apply bmd_init.
intros ? ? ? ? ? ? ? Hsys Kdiff.
match goal with |- context[?A <= ?B] =>
replace A with
  (∥ ((pt (t0 + INR n * h), qt (t0 + INR n * h)) .- (iternR (FT2R p_init, FT2R q_init) h n)) .+
((iternR (FT2R p_init, FT2R q_init) h n) .- (FT2R_prod (iternF (p_init,q_init) n))) ∥)
end.
assert (HSY: Harmonic_osc_system pt qt 1 t0 (FT2R p_init) (FT2R q_init)) by auto.
unfold Harmonic_osc_system in H0.
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
apply global_truncation_error_aux; try unfold h; try nra; auto.

assert (hlow: 0 < h) by (unfold h; nra).
 pose proof error_sum_GS n h hlow as GS.
rewrite GS.
apply Req_le.

replace ((∥ (/ 4065000, / 4068166) ∥) * (((1 + h) ^ n - 1) / h))
with 
((∥ (/ 4065000, / 4068166) ∥) / h  * ((1 + h) ^ n - 1) ).

replace (∥ (pt t0, qt t0) ∥) with 1.

field_simplify; nra.

rewrite A. rewrite B.
symmetry.
apply init_norm_eq.


field_simplify; repeat nra.

field_simplify.

symmetry; apply Rprod_norm_plus_minus_eq.

Qed. 

End WITHNANS.



