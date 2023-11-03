(** lf_harm_lemmas.v:  Definitions and lemmas for the round-off error analysis
  of a simple harmonic oscillator.
 Copyright (C) 2021-2022 Andrew W. Appel and Ariel Kellison.
*)

Require Import vcfloat.VCFloat.
Require Import Interval.Tactic.
Import Binary.
Import Coq.Lists.List ListNotations.
Set Bullet Behavior "Strict Subproofs".

Require Import float_model real_model real_lemmas.
Require Import harmonic_oscillator_system  matrix_analysis.

Open Scope R_scope.

Section WITHNANS.


Context {NANS: Nans}.


(** Calculate a new momentum, as a function of momentum p and position q *)
Definition leapfrog_step_p p q  := fst (leapfrog_stepF float_model.h (p,q)).
(** Calculate a new posisition, as a function of momentum p and position q *)
Definition leapfrog_step_q p q  := snd (leapfrog_stepF float_model.h (p,q)).


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
  [(_p, existT ftype _ (fst pq));(_q, existT ftype _ (snd pq))].

(** Step two, build that into "varmap" data structure, taking care to
  compute it into a lookup-tree ___here___, not later in each place
  where we look something up. *)
Definition leapfrog_vmap (pq : state) : valmap :=
  ltac:(make_valmap_of_list (leapfrog_vmap_raw pq)).

(**  Reification and reflection.   When you have a 
  deep-embedded "expr"ession, you can get back the shallow embedding
   by applying the "fval" function *)

Lemma reflect_reify_pq : forall pq, 
    let e := env_ (leapfrog_vmap pq) in 
     (fval e p', fval e q') = leapfrog_stepF float_model.h pq.
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



Definition leapfrog_bmap_list : list varinfo := 
  [ Build_varinfo Tsingle _p (-1.0041)  1.0041 ;  
      Build_varinfo Tsingle _q (-1.0041)  1.0041 ].

Definition leapfrog_bmap : boundsmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list leapfrog_bmap_list) in exact z).



Definition FT2R_prod (A: state)  := (FT2R (fst A), FT2R (snd A)).



(** Reification and reflection: get back the shallow embedding
   of the real functional model by applying the "rval" function *)
Lemma rval_correct_pq : 
forall pq,
  let e := env_ (leapfrog_vmap pq)
   in (rval e p', rval e q') = leapfrog_stepR h (FT2R_prod pq).
Proof.
 intros. subst e. destruct pq as [p q]. unfold p', q'.
 unfold_rval.
 unfold leapfrog_stepR,FT2R_prod, fst,snd, h,ω; simpl; unfold Defs.F2R; simpl.
 f_equal; nra.
Qed.

Definition sametype (v1 v2: sigT ftype) := projT1 v1 = projT1 v2.

Lemma Equivalence_sametype : Equivalence sametype.
Proof.
split; intro; intros; hnf; auto.
red in H,H0. congruence.
Qed.

Remark leapfrog_vmap_shape:
  forall  pq1 pq0,
  Maps.PTree_Properties.Equal Equivalence_sametype
        (proj1_sig (leapfrog_vmap pq0)) (proj1_sig (leapfrog_vmap pq1)).
Proof.
intros.
intro i.
destruct (Maps.PTree.get i _) eqn:H.
-
apply Maps.PTree.elements_correct in H.
repeat (destruct H; [inversion H; clear H; subst; simpl; reflexivity | ]).
destruct H.
-
rename H into H0.
destruct (Maps.PTree.get i (proj1_sig (leapfrog_vmap pq1))) eqn:H.
apply Maps.PTree.elements_correct in H.
repeat (destruct H; [inversion H; clear H; subst; inversion H0 | ]).
destruct H.
auto.
Qed.

Remark bmd_init : 
  boundsmap_denote leapfrog_bmap (leapfrog_vmap pq_init) .
Proof.
intros.
apply boundsmap_denote_i.
repeat constructor;
(eexists; split; [reflexivity | split; [reflexivity | split;  [reflexivity  | simpl; unfold FT2R; simpl; interval]]]).
repeat constructor.
Qed.



End WITHNANS.



