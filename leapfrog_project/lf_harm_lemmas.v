(** lf_harm_lemmas.v:  Definitions and lemmas for the round-off error analysis
  of a simple harmonic oscillator.
 Copyright (C) 2021-2022 Andrew W. Appel and Ariel Kellison.
*)

From vcfloat Require Import FPLang FPLangOpt RAux Rounding Reify Float_notations Automate.
Require Import IntervalFlocq3.Tactic.
Import Binary.
Import List ListNotations.
Set Bullet Behavior "Strict Subproofs".

Require Import lf_harm_float lf_harm_real real_lemmas lf_harm_real_theorems.


Open Scope R_scope.

Section WITHNANS.


Context {NANS: Nans}.


(** Calculate a new momentum, as a function of momentum p and position q *)
Definition leapfrog_step_p p q  := fst (leapfrog_stepF (p,q)).
(** Calculate a new posisition, as a function of momentum p and position q *)
Definition leapfrog_step_q p q  := snd (leapfrog_stepF (p,q)).


(** In deep-embedded (syntactic) expressons, variables are represented
  by "ident"ifiers, which are actually small positive numbers. *)
Definition _p : ident := 1%positive.  (* Variable name for momentum *)
Definition _q : ident := 2%positive.  (* Variable name for position *)

(** These two lines compute a deep-embedded "expr"ession from
  a shallow-embedded Coq expression.  *)
Definition p' := ltac:(let e' := 
  HO_reify_float_expr constr:([_p; _q]) leapfrog_step_p in exact e').
Definition q' := ltac:(let e' := 
  HO_reify_float_expr constr:([_p; _q]) leapfrog_step_q in exact e').


(** When interpreting deep-embedded expressions, "Var"iables will appear
  which are labeled by identifiers such as "_p" and "_q".  We want a
  "varmap" for looking up the values of those variables.  We'll compute
  that varmap in two stages. **)

(**  Step one, given values "p" and "q", 
  make an association list mapping _q to q, and _p to p,  each labeled
  by its floating-point type.  **)
Definition leapfrog_vmap_list (p q : ftype Tsingle) := 
   [(_p, existT ftype _ p);(_q, existT ftype _ q)].


(** Step two, build that into "varmap" data structure, taking care to
  compute it into a lookup-tree ___here___, not later in each place
  where we look something up. *)
Definition leapfrog_vmap (p q : ftype Tsingle) : valmap :=
 ltac:(let z := compute_PTree (valmap_of_list (leapfrog_vmap_list p q)) in exact z).



(**  Reification and reflection.   When you have a 
  deep-embedded "expr"ession, you can get back the shallow embedding
   by applying the "fval" function *)
Lemma reflect_reify_q : forall p q, 
  fval (env_ (leapfrog_vmap p q)) q' = leapfrog_step_q p q.
Proof.
intros.
unfold q'. 
reflexivity. 
Qed.

Lemma reflect_reify_p : forall p q, 
  fval (env_ (leapfrog_vmap p q)) p' = leapfrog_step_p p q.
Proof.
intros.
unfold p'.
reflexivity. 
Qed.


(** The main point of VCFloat is to prove bounds on the roundoff error of
  floating-point expressions.  Generally those bounds are provable only if
  the free variables of the expression (e.g., "p" and "q") are themselves 
  bounded in some way;  otherwise, the expression might overflow.
  A "boundsmap" is a mapping from identifier (such as "_p") to
  a "varinfo", which gives its (floating-point) and its lower and upper bound. *)


(** First we make an association list.  This one says that 
  -2.0 <= p <= 2.0   and   -2.0 <= q <= 2.0. Given that the energy, computed in real arithmetic
  using the leapfrog integration scheme, is upper bounded, we can guarantee that these 
  bounds hold for the position and momentum computed in floating-point arithmetic for 
  some number of iterations *)

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

Lemma iternR_bound : 
  forall n : nat, 
  ( n <=100)%nat -> 
  ∥iternR (FT2R p_init, FT2R q_init) h n∥ <= 21.697.
Proof.
intros.
eapply Rle_trans.
eapply method_bound_n; try unfold h,ω; try nra.
rewrite init_norm_eq.
rewrite Rmult_1_r.
eapply Rle_trans.
apply Rle_pow; try unfold h; try nra.
apply H.
interval.
Qed.

Definition leapfrog_bmap_list : list varinfo := 
  [ Build_varinfo Tsingle _p (-22)  22 ;  Build_varinfo Tsingle _q (-22)  22 ].


Definition leapfrog_bmap : boundsmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list leapfrog_bmap_list) in exact z).



Definition FT2R_prod (A: ftype Tsingle * ftype Tsingle)  := (FT2R (fst A), FT2R (snd A)).



Lemma rval_correct_q : 
forall pnf qnf,
rval (env_ (leapfrog_vmap pnf qnf)) q' = snd (leapfrog_stepR (FT2R_prod (pnf,qnf)) h).
Proof.
intros.
unfold_rval.
unfold leapfrog_stepR,FT2R_prod, fst,snd, h,ω. 
nra.
Qed.


(** Reification and reflection: get back the shallow embedding
   of the real functional model by applying the "rval" function *)
Lemma rval_correct_p : 
forall pnf qnf,
rval (env_ (leapfrog_vmap pnf qnf)) p' = fst (leapfrog_stepR (FT2R_prod (pnf,qnf)) h).
Proof.
intros.
unfold_rval.
field_simplify.
unfold leapfrog_stepR,FT2R_prod, fst,snd, h,ω.
nra.
Qed.





Lemma leapfrog_vmap_i_aux: 
  forall  p1 q1 p0 q0 ,
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



Lemma itern_implies_bmd_aux:
  forall p0 q0 : ftype Tsingle,
  forall n : nat,
  boundsmap_denote leapfrog_bmap 
  (leapfrog_vmap (fst(iternF (p0,q0) n)) (snd(iternF (p0,q0) n))) ->
  (is_finite _ _  (fst(iternF (p0,q0) (S n))) = true) /\
  (is_finite _ _  (snd(iternF (p0,q0) (S n))) = true).
Proof.
intros.
rewrite step_iternF.
destruct (iternF (p0,q0) n).
simpl in H.
change (snd (leapfrog_stepF (f0, f))) with
  (leapfrog_step_p f0 f ).
change (fst (leapfrog_stepF (f0, f))) with
  (leapfrog_step_q f0 f).
split.
-
replace ((fst (leapfrog_stepF (f, f0)))) with
(leapfrog_step_p f f0) by (unfold leapfrog_step_p; auto). 
rewrite <- reflect_reify_p.
assert (EV1: expr_valid p' = true) by auto.
pose proof rndval_with_cond_correct2 p' EV1
  leapfrog_bmap (leapfrog_vmap f f0) H.
(* this takes a moment to print *)
destruct H0 as (_ & _ & FIN & _ ); try apply FIN; auto.
(* this takes a moment to solve *)
solve_Forall_conds; interval.
-
replace ((snd (leapfrog_stepF (f, f0)))) with
(leapfrog_step_q f f0) by (unfold leapfrog_step_q; auto). 
rewrite <- reflect_reify_q.
assert (EV1: expr_valid q' = true) by auto.
pose proof rndval_with_cond_correct2 q' EV1
  leapfrog_bmap (leapfrog_vmap f f0) H.
destruct H0 as (_ & _ & FIN & _ ); try apply FIN; auto.
(* this takes a moment to solve *)
solve_Forall_conds; interval.
Qed.




Lemma bmd_Sn_bnds_le : 
forall i,
forall v : varinfo,
Maps.PTree.get i leapfrog_bmap = Some v-> 
v.(var_lobound) = -22 /\ 
v.(var_hibound) = 22.
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



Lemma leapfrog_vmap_init: 
forall i,
forall v1 : (sigT ftype),
Maps.PTree.get i (leapfrog_vmap q_init p_init) = Some v1 -> 
v1 = (existT ftype Tsingle q_init) \/
v1 = (existT ftype Tsingle p_init).
Proof. 
intros.
apply Maps.PTree.elements_correct in H.
destruct H.
- inversion H.
right; auto.
- inversion H.
+ inversion H0.
* left; auto.
+ inversion H0; auto.
Qed.



Lemma leapfrog_bmap_aux:
forall (i : positive) (v: varinfo),
       Maps.PTree.get i leapfrog_bmap = Some v -> 
       Maps.PTree.get i leapfrog_bmap = Maps.PTree.get _p leapfrog_bmap \/
       Maps.PTree.get i leapfrog_bmap = Maps.PTree.get _q leapfrog_bmap.
Proof.
intros.
apply Maps.PTree.elements_correct in H.
inversion H.
- 
inversion H0. right; auto.
- inversion H0.
inversion H1.
+ 
 left; auto.
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
subst. cbv. auto.
inversion H1.
- intros.
destruct H.
apply Maps.PTree.elements_correct in H.
destruct H.
+ exists 
(    {|
      var_type := Tsingle;
      var_name := _q;
      var_lobound := (-22);
      var_hibound := 22
    |}).
inversion H; auto.
+ inversion H. 
* inversion H0.
exists 
(    {|
      var_type := Tsingle;
      var_name := _p;
      var_lobound := (-22);
      var_hibound := 22
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
* inversion H; clear H.
* simpl in H. destruct H; try contradiction.
destruct H3.
destruct v. inversion H.
destruct H0.
--
exists ({|
      var_type := Tsingle; var_name := _p; var_lobound := -22; var_hibound := 22
    |});subst;auto.
--
destruct (Maps.PTree.get i (leapfrog_vmap q_init p_init)); 
  try discriminate.
++
subst.
specialize (H2 s eq_refl).
destruct H2.
** repeat (split; simpl; auto; try interval).
** repeat (split; simpl; auto; try interval).
++
subst.
simpl.
repeat (split; simpl; auto; try interval).
+
inversion H1.
specialize (H4 v eq_refl).
subst.
simpl.
repeat (split; simpl; auto; try interval).
-
destruct (Maps.PTree.get i (leapfrog_vmap p_init q_init)); auto.
destruct H3.
destruct H0; try discriminate.
exists s; auto.
Qed.

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

Lemma iterR_bound: 
  forall pt qt: R -> R,
  forall n : nat, 
  (n <= 200)%nat ->
  let t0 := 0 in
  let tn := t0 + INR n * h in
  pt t0 = FT2R p_init -> 
  qt t0 = FT2R q_init ->
  Harmonic_oscillator_system pt qt ω t0 ->
   ∥(pt tn, qt tn) - (iternR ((FT2R p_init), (FT2R q_init)) h n)∥ <= h ^ 3 * error_sum (1 + h) n -> 
  (forall m,
    (m <= n)%nat -> 
    ∥(iternR ((FT2R p_init), (FT2R q_init)) h m)∥ <= 1.5).
Proof.
intros * ? * IC1 IC2. intros.
assert (0 < ω*h <= 2) as Hbnd by (unfold h,ω; nra).
pose proof global_truncation_error_sum pt qt t0 tn h Hbnd H0 m.
assert (t0 + INR m * h <= tn). 
  subst tn. apply Rplus_le_compat_l.
  apply Rmult_le_compat_r; try unfold h; try nra.
  apply le_INR; apply H2.
specialize (H3 H4).
rewrite  Rprod_minus_comm in H3.
eapply Rle_trans in H3.
2: apply Rprod_triang_inv.
destruct H0 as (_ & _ & A).
specialize (A (t0 + INR m * h)).
destruct A as ( _ & _ & C).
unfold ω in *; repeat (rewrite Rmult_1_l in C).
rewrite C in H3.
rewrite IC1 in H3.
rewrite IC2 in H3.
rewrite init_norm_eq in H3.
rewrite Rmult_1_r in H3.
rewrite Rle_minus_l_2 in H3.
pose proof error_sum_bound.
assert (1 + h ^ 3 * error_sum (1 + h) m <= 
  1 + h ^ 3 * error_sum (1 + h) n).
  apply Rplus_le_compat_l.
  apply Rmult_le_compat_l.
  try unfold h; try nra.
  apply error_sum_le_trans.
  apply H2.
  unfold h; nra.
eapply Rle_trans.
apply H3.
eapply Rle_trans.
apply H5.
specialize (H0 n H).
assert (1 + h ^ 3 * error_sum (1 + h) n <=
  1 + h ^ 3 * 15033).
apply Rplus_le_compat_l.
  apply Rmult_le_compat_l.
  try unfold h; try nra.
  apply H0.
eapply Rle_trans.
apply H6.
unfold h.
interval.
Qed.

Lemma init_norm_bound :
  forall n : nat,
  (forall p q n,
  ∥iternR (p,q) h n∥ <= (sqrt 2 * ∥(p,q)∥)) ->
  ∥ iternR (FT2R p_init, FT2R q_init) h n ∥ <= 1.5. 
Proof.
intros.
pose proof init_norm_eq as Hnorm.
specialize (H (FT2R p_init) (FT2R q_init) n).
eapply Rle_trans.
apply H.
eapply Rle_trans.
apply Rmult_le_compat_l.
apply sqrt_pos.
apply Req_le.
apply Hnorm.
interval.
Qed.


End WITHNANS.



