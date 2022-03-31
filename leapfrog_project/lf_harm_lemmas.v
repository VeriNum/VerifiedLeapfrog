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


(* The initial conditions of the momentum "p" and position "q" specified for the integration *)
Definition p_init: ftype Tsingle :=  0%F32.
Definition q_init: ftype Tsingle :=  1%F32.


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



Lemma reflect_reify_q : forall p q, 
             fval (env_ (leapfrog_vmap p q)) q' = leapfrog_stepq p q.
Proof.
intros.
unfold q'.
reflexivity. 
Qed.

Lemma reflect_reify_p : forall p q, fval (env_ (leapfrog_vmap p q)) p' = leapfrog_stepp p q.
Proof.
intros.
unfold p'.
reflexivity. 
Qed.


Definition FT2R_prod (A: ftype Tsingle * ftype Tsingle)  := (FT2R (fst A), FT2R (snd A)).


Lemma rval_correct_p : 
forall pnf qnf,
rval (env_ (leapfrog_vmap pnf qnf)) p' = fst (leapfrog_stepR (FT2R_prod (pnf,qnf)) h).
Proof.
intros.
 match goal with |- context [rval ?env ?x] =>
   let a := constr:(rval env x) in let b := eval hnf in a in change a with b
 end.
unfold leapfrog_stepR,FT2R_prod, fst,snd, h. 
 cbv beta iota delta [rval Rop_of_binop Rop_of_unop
            Rop_of_rounded_binop Rop_of_exact_unop Rop_of_rounded_unop];
 change (type_of_expr _) with Tsingle; 
 change (type_of_expr _) with Tdouble;
 fold (@FT2R Tsingle) in *; fold (@FT2R Tdouble).

 (* Perform all env lookups *)
 repeat 
    match goal with
    | |- context [env_ ?a ?b ?c] =>
       let u := constr:(env_ a b c) in let v := eval hnf in u in change u with v
   end.

 (* Clean up all FT2R constants *)
 repeat match goal with
 | |- context [@FT2R ?t (b32_B754_finite ?s ?m ?e ?H)] =>
 let j := fresh "j" in 
  set (j :=  @FT2R t (b32_B754_finite s m e H));
  simpl in j; subst j
 | |- context [@FT2R ?t (b64_B754_finite ?s ?m ?e ?H)] =>
 let j := fresh "j" in 
  set (j :=  @FT2R t (b64_B754_finite s m e H));
  simpl in j; subst j
 end;
 rewrite <- ?(F2R_eq radix2);
 (* clean up all   F2R radix2 {| Defs.Fnum := _; Defs.Fexp := _ |}   *)
 rewrite ?cleanup_Fnum;
 repeat match goal with |- context [cleanup_Fnum' ?f ?e] =>
  let x := constr:(cleanup_Fnum' f e) in
  let y := eval cbv - [Rdiv IZR] in x in
  change x with y
 end.
field_simplify.
nra.
Qed.


Lemma rval_correct_q : 
forall pnf qnf,
rval (env_ (leapfrog_vmap pnf qnf)) q' = snd (leapfrog_stepR (FT2R_prod (pnf,qnf)) h).
Proof.

intros.
 match goal with |- context [rval ?env ?x] =>
   let a := constr:(rval env x) in let b := eval hnf in a in change a with b
 end.
unfold leapfrog_stepR,FT2R_prod, fst,snd, h. 
 cbv beta iota delta [rval Rop_of_binop Rop_of_unop
            Rop_of_rounded_binop Rop_of_exact_unop Rop_of_rounded_unop];
 change (type_of_expr _) with Tsingle; 
 change (type_of_expr _) with Tdouble;
 fold (@FT2R Tsingle) in *; fold (@FT2R Tdouble).

 (* Perform all env lookups *)
 repeat 
    match goal with
    | |- context [env_ ?a ?b ?c] =>
       let u := constr:(env_ a b c) in let v := eval hnf in u in change u with v
   end.

 (* Clean up all FT2R constants *)
 repeat match goal with
 | |- context [@FT2R ?t (b32_B754_finite ?s ?m ?e ?H)] =>
 let j := fresh "j" in 
  set (j :=  @FT2R t (b32_B754_finite s m e H));
  simpl in j; subst j
 | |- context [@FT2R ?t (b64_B754_finite ?s ?m ?e ?H)] =>
 let j := fresh "j" in 
  set (j :=  @FT2R t (b64_B754_finite s m e H));
  simpl in j; subst j
 end;
 rewrite <- ?(F2R_eq radix2);
 (* clean up all   F2R radix2 {| Defs.Fnum := _; Defs.Fexp := _ |}   *)
 rewrite ?cleanup_Fnum;
 repeat match goal with |- context [cleanup_Fnum' ?f ?e] =>
  let x := constr:(cleanup_Fnum' f e) in
  let y := eval cbv - [Rdiv IZR] in x in
  change x with y
 end.
field_simplify.
nra.
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



Lemma itern_implies_bmd_aux:
  forall p0 q0 : ftype Tsingle,
  forall n,
  boundsmap_denote leapfrog_bmap 
    (leapfrog_vmap (fst(iternF (p0,q0) n)) (snd(iternF (p0,q0) n))) ->
  (is_finite _ _  (fst(iternF (p0,q0) (S n))) = true) /\
(is_finite _ _  (snd(iternF (p0,q0) (S n))) = true).
Proof.
intros.
rewrite step_iternF.
destruct (iternF  (p0, q0) n).
simpl in H.
change (fst (leapfrog_stepF (f, f0))) with
  (leapfrog_stepp f f0).
change (snd (leapfrog_stepF (f, f0))) with
  (leapfrog_stepq f f0).
split.
-
rewrite <- reflect_reify_p.
assert (EV1: expr_valid p' = true) by auto.
pose proof rndval_with_cond_correct2 p' EV1
  leapfrog_bmap (leapfrog_vmap f f0) H.
destruct H0 as (_ & _ & FIN & _ ); try apply FIN; auto.

  (* What's left is a Forall of all the conds.  Next, clean them up a bit. *)
  change (type_of_expr _) with Tsingle;
  change (type_of_expr _) with Tdouble;
  cbv beta iota zeta delta [
            mset shifts_MAP empty_shiftmap mempty
            compcert_map Maps.PMap.set Maps.PMap.init
            Maps.PTree.empty Maps.PTree.set Maps.PTree.set' 
              Maps.PTree.set0 Pos.of_succ_nat Pos.succ
            index_of_tr map_nat fst snd

          rndval_with_cond' rnd_of_binop_with_cond
          rnd_of_unop_with_cond is_div
          Rbinop_of_rounded_binop Runop_of_exact_unop Runop_of_rounded_unop
          type_of_expr make_rounding round_knowl_denote
         rounding_cond_ast no_overflow app].

 
  (* now process the boundsmap above the line, and the conds below the line *)
  process_boundsmap_denote;
  process_conds; interval.

-
rewrite <- reflect_reify_q.
assert (EV1: expr_valid q' = true) by auto.
pose proof rndval_with_cond_correct2 q' EV1
  leapfrog_bmap (leapfrog_vmap f f0) H.
destruct H0 as (_ & _ & FIN & _ ); try apply FIN; auto.

  (* What's left is a Forall of all the conds.  Next, clean them up a bit. *)
  change (type_of_expr _) with Tsingle;
  change (type_of_expr _) with Tdouble;
  cbv beta iota zeta delta [
            mset shifts_MAP empty_shiftmap mempty
            compcert_map Maps.PMap.set Maps.PMap.init
            Maps.PTree.empty Maps.PTree.set Maps.PTree.set' 
              Maps.PTree.set0 Pos.of_succ_nat Pos.succ
            index_of_tr map_nat fst snd

          rndval_with_cond' rnd_of_binop_with_cond
          rnd_of_unop_with_cond is_div
          Rbinop_of_rounded_binop Runop_of_exact_unop Runop_of_rounded_unop
          type_of_expr make_rounding round_knowl_denote
         rounding_cond_ast no_overflow app].

 
  (* now process the boundsmap above the line, and the conds below the line *)
  process_boundsmap_denote;
  process_conds; interval.
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





End WITHNANS.



