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

(** NANS:  Each different computer architecture supports the same IEEE-754
  floating-point standard, but with slightly different Not-a-number (NAN) behavior.
  That behavior is encapsulated in a Nans typeclass.  You can instantiate that
  appropriate for your own architecture; but all the demos in this file are
  independent of the Nans details, so we can leave it abstract, like this: *)
Context {NANS: Nans}.



Definition leapfrog_stepp p q  := fst (leapfrog_stepF (p,q)).
Definition leapfrog_stepq p q := snd (leapfrog_stepF (p,q)).

(** In deep-embedded (syntactic) expressons, variables are represented
  by "ident"ifiers, which are actually small positive numbers. *)
Definition _p : ident := 1%positive.  (* Variable name for position *)
Definition _q : ident := 2%positive.  (* Variable name for velocity *)

(** These two lines compute a deep-embedded "expr"ession from
  a shallow-embedded Coq expression.  *)
Definition p' := ltac:(let e' := 
  HO_reify_float_expr constr:([_p; _q]) leapfrog_stepp in exact e').
Definition q' := ltac:(let e' := 
  HO_reify_float_expr constr:([_p; _q]) leapfrog_stepq in exact e').



Definition leapfrog_vmap_list (p q : ftype Tsingle) := 
   [(_p, existT ftype _ p);(_p, existT ftype _ q)].


Definition leapfrog_vmap (p q : ftype Tsingle) : valmap :=
 ltac:(let z := compute_PTree (valmap_of_list (leapfrog_vmap_list p q)) in exact z).


Definition leapfrog_bmap_list : list varinfo := 
  [ Build_varinfo Tsingle _p (-2)  2 ;  Build_varinfo Tsingle _q (-2)  2 ].

(** Then we calculate an efficient lookup table, the "boundsmap". *)
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
    (/ 4190000).
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
Rabs (FT2R (fval (env_ (leapfrog_vmap p q)) p') - rval (env_ (leapfrog_vmap p q)) p') <= (/ 4190000)
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
∥ (pnf, qnf) .- (pnr, qnr)∥ <= ∥(/ 4190000, / 4068166)∥.
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


Lemma Rprod_minus_comm : 
forall a b,
∥ a .- b ∥ = ∥ b .- a ∥.
Proof.
intros. 
unfold Rprod_norm, Rprod_minus.
destruct a; destruct b; unfold fst, snd.
f_equal. simpl. nra.
Qed.

Lemma Rprod_triang_inv : 
forall a b : (R * R),
(∥ a ∥ - ∥ b ∥) <= ∥ b .- a ∥.
Proof.
Admitted.

Lemma error_sum_le_trans :
  forall m n,
  (n <= m)%nat ->  
  error_sum (1 + h) n <=
  error_sum (1 + h) m.
Proof.
intros.
Admitted. 

Lemma error_sum_bound: 
  forall n,
  (n <= 200)%nat -> 
  error_sum (1 + h) n <= 15033.
Proof.
intros.
eapply Rle_trans.
eapply error_sum_le_trans.
apply H.
assert (Hyph: 1 + h <> 1 ) by (unfold h ;nra).
pose proof geo_series_closed_form (1 + h) 199 Hyph.
unfold error_sum; rewrite H0.
replace ((1 - (1 + h) ^ 200) / (1 - (1 + h))) with (  ((1 + h) ^ 200 - 1) /  h).
rewrite Rcomplements.Rle_div_l; try (unfold h; nra).
set (a:=(1 + h) ^ 200).
field_simplify; try nra. 
apply Stdlib.Rdiv_eq_reg; try nra.
Qed.



Lemma itern_implies_bmd_aux:
  forall pnf qnf : ftype Tsingle,
  forall pnr qnr : R,
  forall n,
  (n <= 200)%nat -> 
  (* if we are given a bound on the norm of the difference between
      the discretized real and floating point solutions after n iterations, 
      derived from the recurrence of the errors *)
  ∥ Rprod_minus (pnr, qnr) (FT2R_prod (pnf, qnf)) ∥ <=  ∥(/ 4190000, / 4068166)∥ * error_sum (1 + h) n 
  (*  and if we are given a bound on the norm of the discretized real solutions *) 
  /\ ∥(pnr,qnr) ∥ <= 1.5 -> 
  (*  then the floating point solution remains reasonably bounded *)
  Rabs (FT2R pnf)  <= 2 /\ Rabs ( FT2R qnf) <= 2.
Proof.
intros ? ? ? ? ? BNDn H. destruct H as (A & B).
assert (HYP1: ∥ Rprod_minus (pnr, qnr) (FT2R_prod (pnf, qnf)) ∥ <=
(∥ (/ 4190000, / 4068166) ∥) * error_sum (1 + h) 200).
+ eapply Rle_trans.
2 :  { 
apply Rmult_le_compat_l; try (apply Rnorm_pos). 
eapply error_sum_le_trans. apply BNDn.
} apply A.
+ clear A. 
assert ( HYP2 :∥ Rprod_minus (pnr, qnr) (FT2R_prod (pnf, qnf)) ∥ <=
     (∥ (/ 4190000, / 4068166) ∥) * 15033).
eapply Rle_trans.
apply HYP1.
apply Rmult_le_compat_l; try (apply Rnorm_pos).
apply error_sum_bound; try lia.
clear HYP1. 
assert (HYP3: (∥ (FT2R_prod (pnf, qnf))∥ - ∥ (pnr, qnr) ∥) <= (∥ (/ 4190000, / 4068166) ∥) * 15033 ).
eapply Rle_trans.
apply Rprod_triang_inv.
apply HYP2.
apply Rle_minus_l_2 in HYP3. 
assert (HYP4: ∥ FT2R_prod (pnf, qnf) ∥ <= 1.5 + (∥ (/ 4190000, / 4068166) ∥) * 15033).
eapply Rle_trans.
2: {apply Rplus_le_compat_r. apply B.
} apply HYP3. clear HYP2.
generalize HYP4.
match goal with |-context[Rprod_norm ?A <= ?a]=>
  interval_intro a upper; intros ?HYP; clear HYP
end. 
unfold Rprod_norm in HYP4. 
unfold FT2R_prod, fst ,snd in HYP4.
assert (HYP5: sqrt (FT2R pnf  ^ 2 + FT2R qnf ^ 2) <= sqrt ((6778595201347263 / 4503599627370496)^2) ).
eapply Rle_trans. apply  HYP4.
rewrite sqrt_pow2; try nra. apply H.
apply sqrt_le_0 in HYP5; try nra.
split. 
++ assert (FT2R pnf ^ 2 <= (6778595201347263 / 4503599627370496) ^ 2) by nra.
apply sqrt_le in H0.
rewrite sqrt_pow2 in H0.
all: (try interval).
++ assert (FT2R qnf ^ 2 <= (6778595201347263 / 4503599627370496) ^ 2) by nra.
apply sqrt_le in H0.
rewrite sqrt_pow2 in H0.
all: (try interval).
Qed.


Lemma leapfrog_vmap_i_aux : 
forall p1 q1 p0 q0,
forall i,
forall v1 v2 : {x : type & ftype x},
Maps.PTree.get i (leapfrog_vmap p0 q0) = Some v1 -> 
Maps.PTree.get i (leapfrog_vmap p1 q1) = Some v2 -> 
projT1 v1 = projT1 v2.
Proof.
intros.
apply Maps.PTree.elements_correct in H.
destruct H.
+ inversion H. subst. clear H.
simpl in H0. inversion H0. auto.
+ simpl in H. destruct H; try contradiction.
Qed.


Lemma itern_implies_bmd:
  forall p0 q0 : ftype Tsingle,
  boundsmap_denote leapfrog_bmap (leapfrog_vmap p0 q0) -> 
  forall n,
  (n <= 200)%nat -> 
  let (pnf,qnf) := (iternF (p0,q0) n) in
  let (pnr,qnr) := (iternR (FT2R_prod (p0,q0)) h n) in
  (* if we are given a bound on the norm of the difference between
      the discretized real and floating point solutions after n iterations, 
      derived from the recurrence of the errors *)
  ∥ Rprod_minus (pnr, qnr) (FT2R_prod (pnf, qnf)) ∥ <=  ∥(/ 4190000, / 4068166)∥ * error_sum (1 + h) n 
  (*  and if we are given a bound on the norm of the discretized real solutions *) 
  /\ ∥(pnr,qnr) ∥ <= 1.5 -> 
  (*  then the floating point solution remains reasonably bounded *)
  boundsmap_denote leapfrog_bmap (leapfrog_vmap pnf qnf).
Proof.
intros.
destruct (iternF (p0, q0) n).
destruct (iternR (FT2R_prod (p0, q0)) h n).
intros.
pose proof ( itern_implies_bmd_aux f f0 r r0 n H0 H1) as prf.
destruct prf as (Hf & Hf0).
assert (is_finite _ _ f = true /\ 
 (is_finite _ _ f0 = true)).
split.
+ clear H1.  
destruct f; simpl;
  try (unfold FT2R_prod, FT2R in *; auto).
Search (is_finite ).
simpl in Hf.

unfold boundsmap_denote in *.
destruct (iternF (p0, q0) n).
destruct (iternR (FT2R_prod (p0, q0)) h n).
intros.
specialize (H i).
destruct (Maps.PTree.get i leapfrog_bmap).
destruct v.
pose proof leapfrog_vmap_i_aux f f0 p0 q0 i.
destruct (Maps.PTree.get i (leapfrog_vmap f f0)).
destruct (Maps.PTree.get i (leapfrog_vmap p0 q0)).
specialize (H2 s0 s eq_refl eq_refl). 

destruct H as (A & B & C & D).

split; try auto.
split.
subst; auto.
split; try auto.



replace (fprec (projT1 s)) with (fprec (projT1 s0)).
change (fprec (projT1 s0)) with (fprec (projT1 s)).
rewrite H2 in C.
apply symmetry in H2.
subst; auto.

 
pose proof leapfrog_vmap_i_aux

Maps.PTree.elements_correct



try (destruct v); auto. 
destruct H as (A & B & C).
repeat (split; try auto).
rewrite B.
destruct s0, s.
simpl.
+ 
Admitted.


Lemma reflect_reify_q : forall p q, 
             fval (env_ (leapfrog_vmap p q)) q' = leapfrog_stepq p q.
Proof.
intros.
destruct true.  
- unfold q', leapfrog_stepq, leapfrog_stepF, F,  fst, snd, lf_harm_float.h, half_pow2_h.
Admitted.

(**  Demonstration of reification and reflection, this time on  leapfrog_stepv *) 
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



Lemma global_error : 
  forall p q  : ftype Tsingle,
  forall n : nat, 
  (n <= 200)%nat -> 
  ( forall pnr qnr, ∥(pnr,qnr) ∥ <= 1.5) ->
  ∥(iternR (FT2R p, FT2R q) h n) .- FT2R_prod (iternF (p,q) n) ∥ <= (∥ (/ 4190000, / 4068166) ∥) * error_sum (1 + h) n.
  Proof.
intros.
induction n.
+ unfold Rprod_minus. simpl. repeat rewrite Rminus_eq_0.
unfold Rprod_norm, fst, snd. repeat rewrite pow_ne_zero; try lia.
rewrite Rplus_0_r. rewrite sqrt_0; try nra.
+ rewrite step_iternF; rewrite step_iternR. 
destruct (iternR (FT2R p, FT2R q) h n) as (pnr, qnr). 
destruct (iternF (p,q)  n) as (pnf, qnf).
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
specialize (IHn BNDn).
pose proof itern_implies_bmd pnf qnf pnr qnr n BNDn. 
specialize (H0 pnr qnr).
assert (∥ Rprod_minus (pnr, qnr) (FT2R_prod (pnf, qnf)) ∥ <=
      (∥ (/ 4190000, / 4068166) ∥) * error_sum (1 + h) n /\ ∥ (pnr, qnr) ∥ <= 1.5).
split; auto.
specialize (H1 H2).
clear H2.
pose proof roundoff_norm_bound pnf qnf H1.
rewrite reflect_reify_p in H2.
rewrite reflect_reify_q in H2.
change (leapfrog_stepp pnf qnf, leapfrog_stepq pnf qnf) with 
  (leapfrog_stepF (pnf, qnf)) in H2.
rewrite rval_correct_q in H2. 
rewrite rval_correct_p in H2.
change ((fst (leapfrog_stepR (FT2R_prod (pnf, qnf)) h),
         snd (leapfrog_stepR (FT2R_prod (pnf, qnf)) h))) with 
(leapfrog_stepR (FT2R_prod (pnf, qnf)) h) in H2.
destruct (FT2R_prod (leapfrog_stepF (pnf, qnf))). 
rewrite Rprod_minus_comm in H2. 
apply H2.  
destruct (Rprod_minus (pnr, qnr) (FT2R_prod (pnf, qnf))).
assert (0 < h < 2) by (unfold h; nra).
pose proof method_norm_bounded r r0 h H1.
eapply Rle_trans.
apply Rplus_le_compat_r.
apply H2. 
eapply Rle_trans.
apply Rplus_le_compat_r.
apply Rmult_le_compat_l; try (unfold h; nra).
assert (BNDn: (n<= 200)%nat) by lia.
specialize (IHn BNDn).
apply IHn. 
set (aa:= (∥ (/ 4190000, / 4068166) ∥)). 
replace ((1 + h) * (aa * error_sum (1 + h) n) + aa)
with
(aa * ((1 + h) * (error_sum (1 + h) n) + 1)) by nra.
rewrite <- error_sum_aux2; nra.
symmetry. apply Rprod_norm_plus_minus_eq.
Qed. 



End WITHNANS.



