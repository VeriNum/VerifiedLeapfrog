(** lf_harm_lemmas.v:  Definitions and lemmas for the round-off error analysis
  of a simple harmonic oscillator.
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


(* The initial conditions of the momentum "p" and position "q" specified for the integration scheme*)
Definition p_init: ftype Tsingle :=  0%F32.
Definition q_init: ftype Tsingle :=  1%F32.


(** Calculate a new momentum, as a function of momentum p and position q *)
Definition leapfrog_step_p q p  := snd (leapfrog_stepF_ver (q,p)).
(** Calculate a new posisition, as a function of momentum p and position q *)
Definition leapfrog_step_q q p  := fst (leapfrog_stepF_ver (q,p)).


(** In deep-embedded (syntactic) expressons, variables are represented
  by "ident"ifiers, which are actually small positive numbers. *)
Definition _p : ident := 1%positive.  (* Variable name for momentum *)
Definition _q : ident := 2%positive.  (* Variable name for position *)

(** These two lines compute a deep-embedded "expr"ession from
  a shallow-embedded Coq expression.  *)
Definition p' := ltac:(let e' := 
  HO_reify_float_expr constr:([_q; _p]) leapfrog_step_p in exact e').
Definition q' := ltac:(let e' := 
  HO_reify_float_expr constr:([_q; _p]) leapfrog_step_q in exact e').


(** When interpreting deep-embedded expressions, "Var"iables will appear
  which are labeled by identifiers such as "_p" and "_q".  We want a
  "varmap" for looking up the values of those variables.  We'll compute
  that varmap in two stages. **)

(**  Step one, given values "p" and "q", 
  make an association list mapping _q to q, and _p to p,  each labeled
  by its floating-point type.  **)
Definition leapfrog_vmap_list (q p : ftype Tsingle) := 
   [(_q, existT ftype _ q);(_p, existT ftype _ p)].


(** Step two, build that into "varmap" data structure, taking care to
  compute it into a lookup-tree ___here___, not later in each place
  where we look something up. *)
Definition leapfrog_vmap (q p : ftype Tsingle) : valmap :=
 ltac:(let z := compute_PTree (valmap_of_list (leapfrog_vmap_list q p)) in exact z).



(**  Reification and reflection.   When you have a 
  deep-embedded "expr"ession, you can get back the shallow embedding
   by applying the "fval" function *)
Lemma reflect_reify_q : forall q p, 
  fval (env_ (leapfrog_vmap q p)) q' = leapfrog_step_q q p.
Proof.
intros.
unfold q'. 
reflexivity. 
Qed.

Lemma reflect_reify_p : forall q p, 
  fval (env_ (leapfrog_vmap q p)) p' = leapfrog_step_p q p.
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

Definition leapfrog_bmap_list : list varinfo := 
  [ Build_varinfo Tsingle _q (-2)  2 ;  Build_varinfo Tsingle _p (-2)  2 ].


Definition leapfrog_bmap : boundsmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list leapfrog_bmap_list) in exact z).



Definition FT2R_prod (A: ftype Tsingle * ftype Tsingle)  := (FT2R (fst A), FT2R (snd A)).



Lemma rval_correct_q : 
forall qnf pnf,
rval (env_ (leapfrog_vmap qnf pnf)) q' = snd (leapfrog_stepR (FT2R_prod (pnf,qnf)) h).
Proof.
intros.
unfold_rval.
unfold leapfrog_stepR,FT2R_prod, fst,snd, h. 
nra.
Qed.


(** Reification and reflection: get back the shallow embedding
   of the real functional model by applying the "rval" function *)
Lemma rval_correct_p : 
forall pnf qnf,
rval (env_ (leapfrog_vmap qnf pnf)) p' = fst (leapfrog_stepR (FT2R_prod (pnf,qnf)) h).
Proof.
intros.
unfold_rval.
field_simplify.
unfold leapfrog_stepR,FT2R_prod, fst,snd, h.
nra.
Qed.





Lemma leapfrog_vmap_i_aux: 
  forall q1 p1 q0 p0,
  forall i,
  forall v1 : {x : type & ftype x},
  Maps.PTree.get i (leapfrog_vmap q0 p0) = Some v1 -> 
  exists v2 : {x : type & ftype x},
  Maps.PTree.get i (leapfrog_vmap q1 p1) = Some v2 /\ 
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
  forall q0 p0 : ftype Tsingle,
  forall n : nat,
  boundsmap_denote leapfrog_bmap 
  (leapfrog_vmap (fst(iternF_ver (q0,p0) n)) (snd(iternF_ver (q0,p0) n))) ->
  (is_finite _ _  (fst(iternF_ver (q0,p0) (S n))) = true) /\
  (is_finite _ _  (snd(iternF_ver (q0,p0) (S n))) = true).
Proof.
intros.
rewrite step_iternF_ver.
destruct (iternF_ver (q0,p0) n).
simpl in H.
change (snd (leapfrog_stepF_ver (f, f0))) with
  (leapfrog_step_p f f0).
change (fst (leapfrog_stepF_ver (f, f0))) with
  (leapfrog_step_q f f0).
split.
-
rewrite <- reflect_reify_q.
assert (EV1: expr_valid q' = true) by auto.
pose proof rndval_with_cond_correct2 q' EV1
  leapfrog_bmap (leapfrog_vmap f f0) H.
Time destruct H0 as (_ & _ & FIN & _ ); try apply FIN; auto.
(* this takes a moment to solve *)
Time solve_Forall_conds.
-
rewrite <- reflect_reify_p.
assert (EV1: expr_valid p' = true) by auto.
pose proof rndval_with_cond_correct2 p' EV1
  leapfrog_bmap (leapfrog_vmap f f0) H.
(* this takes a moment to print *)
Time destruct H0 as (_ & _ & FIN & _ ); try apply FIN; auto.
(* this takes a moment to solve *)
Time solve_Forall_conds.
Qed.




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
(q p: ftype Tsingle),
(exists (v : varinfo),
       Maps.PTree.get i leapfrog_bmap = Some v) <->
(exists (v1 : sigT ftype),
       Maps.PTree.get i (leapfrog_vmap q p) = Some v1).
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
  boundsmap_denote leapfrog_bmap (leapfrog_vmap q_init p_init) .
Proof.
intros.
unfold boundsmap_denote.
intros.
pose proof leapfrog_bmap_aux i as H1.
pose proof leapfrog_vmap_init i as H2.
pose proof bmd_vmap_bmap_iff i q_init p_init as H3.
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
destruct (Maps.PTree.get i (leapfrog_vmap q_init p_init)); 
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
destruct (Maps.PTree.get i (leapfrog_vmap q_init p_init)); 
  try discriminate.
subst.
specialize (H2 s eq_refl).
destruct H2.
**
split; simpl; auto.
rewrite H2. repeat (split; simpl; auto; try interval).
** split; simpl; auto.
rewrite H2. repeat (split; simpl; auto; try interval).

- destruct (Maps.PTree.get i (leapfrog_vmap q_init p_init)); auto.
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


Lemma itern_implies_bmd_aux1:
  forall pnf qnf : ftype Tsingle,
  forall pnr qnr : R,
  forall n,
  (n <= 200)%nat -> 
  ∥ Rprod_minus (pnr, qnr) (FT2R_prod (pnf, qnf)) ∥ <=  ∥(/7662000, / 4068166)∥ * error_sum (1 + h) n 
  /\ ∥(pnr,qnr) ∥ <= 1.5 -> 
  Rabs (FT2R pnf)  <= 2 /\ Rabs ( FT2R qnf) <= 2.
Proof.
intros ? ? ? ? ? BNDn H. destruct H as (A & B).
assert (HYP1: ∥ Rprod_minus (pnr, qnr) (FT2R_prod (pnf, qnf)) ∥ <=
(∥ ( /7662000, / 4068166) ∥) * error_sum (1 + h) 200).
+ eapply Rle_trans.
2 :  { 
apply Rmult_le_compat_l; try (apply Rnorm_pos). 
eapply error_sum_le_trans. apply BNDn. unfold h; nra.
} apply A.
+ clear A. 
(* use the fact that (error_sum (1 + h) 200 = 15032.068779571218 *)
assert ( HYP2 :∥ Rprod_minus (pnr, qnr) (FT2R_prod (pnf, qnf)) ∥ <=
     (∥ (/7662000, / 4068166) ∥) * 15033).
eapply Rle_trans.
apply HYP1.
apply Rmult_le_compat_l; try (apply Rnorm_pos).
apply error_sum_bound; try lia.
clear HYP1. 
assert (HYP3: (∥ (FT2R_prod (pnf, qnf))∥ - ∥ (pnr, qnr) ∥) <= (∥ (/7662000, / 4068166) ∥) * 15033 ).
eapply Rle_trans.
apply Rprod_triang_inv.
apply HYP2.
apply Rle_minus_l_2 in HYP3. 
assert (HYP4: ∥ FT2R_prod (pnf, qnf) ∥ <= 1.5 + (∥ (/7662000, / 4068166) ∥) * 15033).
eapply Rle_trans.
2: {apply Rplus_le_compat_r. apply B.
} apply HYP3. clear HYP2.
generalize HYP4.
match goal with |-context[Rprod_norm ?A <= ?a]=>
  interval_intro a upper; intros ?HYP; clear HYP;
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
++ assert (FT2R pnf ^ 2 <= valB ^ 2) by nra.
apply sqrt_le in H0.
rewrite sqrt_pow2 in H0.
all: (try interval).
++ assert (FT2R qnf ^ 2 <= valB ^ 2) by nra.
apply sqrt_le in H0.
rewrite sqrt_pow2 in H0.
all: (try interval).
Qed.


Definition FT2R_prod_rev := fun A : ftype Tsingle * ftype Tsingle =>
(FT2R (snd A), FT2R (fst A)).


Lemma itern_implies_bmd:
  forall q0 p0: ftype Tsingle,
  forall n,
  (S n <= 200)%nat -> 
  boundsmap_denote leapfrog_bmap 
    (leapfrog_vmap (fst(iternF_ver (q0,p0) n)) (snd(iternF_ver (q0,p0) n))) ->
  ∥(iternR (FT2R p0, FT2R q0) h (S n)) .- FT2R_prod_rev (iternF_ver (q0,p0)  (S n)) ∥ <= 
  (∥ (/7662000, / 4068166) ∥) * error_sum (1 + h) (S n)  /\
∥ (iternR (FT2R p0, FT2R q0) h  (S n))∥ <= 1.5 ->
   boundsmap_denote leapfrog_bmap (leapfrog_vmap (fst(iternF_ver (q0,p0) (S n))) (snd(iternF_ver (q0,p0) (S n)))).
Proof. 
intros ? ? ? BNDn BMD NORM.
pose proof (itern_implies_bmd_aux q0 p0 n BMD) as HFIN.
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
rewrite step_iternF_ver in *.
destruct ((iternF_ver (q0, p0) n)).
set (f1 := (fst (leapfrog_stepF_ver (f, f0)))) in *.
set (f2:=(snd (leapfrog_stepF_ver (f, f0)))) in *.
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
specialize (HBND f2 f1 r r0 (S n) BNDn NORM). 
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
specialize (HBND f2 f1 r r0 (S n) BNDn NORM). 
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
rewrite step_iternF_ver in *.
destruct ((iternF_ver (q0, p0) n)).
set (f1 := (fst (leapfrog_stepF_ver (f, f0)))) in *.
set (f2 := (snd (leapfrog_stepF_ver (f, f0)))) in *.
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




End WITHNANS.



