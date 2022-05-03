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
Definition leapfrog_vmap_raw (pq: state) :=
 valmap_of_list [(_p, existT ftype _ (fst pq));(_q, existT ftype _ (snd pq))].


(** Step two, build that into "varmap" data structure, taking care to
  compute it into a lookup-tree ___here___, not later in each place
  where we look something up. *)
Definition leapfrog_vmap (pq : state) : valmap :=
 ltac:(let z := compute_PTree (leapfrog_vmap_raw pq) in exact z).


(**  Reification and reflection.   When you have a 
  deep-embedded "expr"ession, you can get back the shallow embedding
   by applying the "fval" function *)

Lemma reflect_reify_pq : forall pq, 
    let e := env_ (leapfrog_vmap pq) in 
     (fval e p', fval e q') = leapfrog_stepF pq.
Proof. reflexivity. Qed.

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
rewrite <- sqrt_1.
replace (FT2R q_init) with 1.
simpl. unfold Rprod_norm, fst, snd.
f_equal; nra.
unfold FT2R, q_init. 
 cbv [B2R]. simpl. cbv [Defs.F2R IZR IPR]. simpl;
field_simplify; nra.
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



Definition FT2R_prod (A: state)  := (FT2R (fst A), FT2R (snd A)).



(** Reification and reflection: get back the shallow embedding
   of the real functional model by applying the "rval" function *)
Lemma rval_correct_pq : 
forall pq,
  let e := env_ (leapfrog_vmap pq)
   in (rval e p', rval e q') = leapfrog_stepR (FT2R_prod pq) h.
Proof.
 intros. subst e. destruct pq as [p q]. unfold p', q'. 
 unfold_rval.
 unfold leapfrog_stepR,FT2R_prod, fst,snd, h,ω.  f_equal; nra.
Qed.

Definition sametype (v1 v2: sigT ftype) := projT1 v1 = projT1 v2.

Lemma Equivalence_sametype : Equivalence sametype.
Proof.
split; intro; intros; hnf; auto.
red in H,H0. congruence.
Qed.

Lemma leapfrog_vmap_shape:
  forall  pq1 pq0,
  Maps.PTree_Properties.Equal Equivalence_sametype
        (leapfrog_vmap pq0) (leapfrog_vmap pq1).
Proof.
intros.
intro i.
destruct (Maps.PTree.get i (leapfrog_vmap pq0)) eqn:H.
-
apply Maps.PTree.elements_correct in H.
repeat (destruct H; [inversion H; clear H; subst; simpl; reflexivity | ]).
destruct H.
-
rename H into H0.
destruct (Maps.PTree.get i (leapfrog_vmap pq1)) eqn:H.
apply Maps.PTree.elements_correct in H.
repeat (destruct H; [inversion H; clear H; subst; inversion H0 | ]).
destruct H.
auto.
Qed.

Lemma bmd_init : 
  boundsmap_denote leapfrog_bmap (leapfrog_vmap pq_init) .
Proof.
intros.
apply boundsmap_denote_i.
repeat constructor;
(eexists; split; [reflexivity | split; [reflexivity | split;  [reflexivity  | simpl; interval]]]).
repeat constructor.
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



