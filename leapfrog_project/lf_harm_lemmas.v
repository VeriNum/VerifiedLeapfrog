From Flocq Require Import Binary Bits Core.
From compcert.lib Require Import IEEE754_extra Coqlib Floats Zbits Integers.
Require Import float_lib lf_harm_float lf_harm_real vcfloat optimize real_lemmas.
Set Bullet Behavior "Strict Subproofs". 

Local Transparent Float32.of_bits.
Local Transparent Float32.div.
Local Transparent Float32.neg.
Local Transparent Float32.mul.
Local Transparent Float32.add.
Local Transparent Float32.sub.


Definition leapfrog_stepx x v := fst (leapfrog_step' (x,v)).
Definition leapfrog_stepv x v := snd (leapfrog_step' (x,v)).

Import ListNotations.
Definition _x : AST.ident := 1121%positive.
Definition _v : AST.ident := 1117%positive.

Definition x_init := float32_of_Z 0.
Definition v_init := float32_of_Z 1.

Import FPLangOpt. 
Import FPLang.
Import FPSolve.
Import Test.


Definition x' := ltac:(let e' := 
  HO_reify_float_expr constr:([_x; _v]) leapfrog_stepx in exact e').
Definition v' := ltac:(let e' := 
  HO_reify_float_expr constr:([_x; _v]) leapfrog_stepv in exact e').


Fixpoint mk_bounds_list (id_list: list  (AST.ident * (type * (R * R)))) : ( list  (AST.ident * Test.varinfo))  :=
  match id_list with
  | t :: t' => let i := fst t in let ty:= fst ( snd t) in let r1:= fst (snd ( snd t)) in let r2:= snd (snd ( snd t))  in 
      [(i, Build_varinfo ty i r1 r2)] ++ mk_bounds_list t'
  | nil => []
end.

Definition leapfrog_bmap_list := mk_bounds_list [(_x, (Tsingle, (-1,1))); (_v, (Tsingle, (-1,1)))].
Definition leapfrog_vmap_list (x v : float32) := [(_x, Values.Vsingle x);(_v, Values.Vsingle v)].
Definition leapfrog_env  := (fun x v => list_to_bound_env leapfrog_bmap_list (leapfrog_vmap_list x v)). 
Definition leapfrog_bmap :=  Maps.PTree_Properties.of_list leapfrog_bmap_list.
Definition leapfrog_vmap (x v : float32) := Maps.PTree_Properties.of_list (leapfrog_vmap_list x v).

Definition lf_bmap_list_n (erx erv: R) (n: nat) := 
  mk_bounds_list [(_x, (Tsingle, (- 1 * (1 + INR n * erx ), 1 *( 1+  INR n * erx) ))); 
                  (_v, (Tsingle, (-1 * (1 + INR n * erv ), 1* (1 + INR n * erv ))))].
Definition lf_bmap_n (erx erv: R) (n: nat) :=  
  Maps.PTree_Properties.of_list (lf_bmap_list_n erx erv n).
Definition lf_vmap := Maps.PTree_Properties.of_list (leapfrog_vmap_list x_init v_init).
Definition lf_env_n  (x v : float32) (ex ev: R) (n: nat) := 
  list_to_bound_env (lf_bmap_list_n ex ev n) (leapfrog_vmap_list x v). 

Lemma bmd_Sn_varinfo : 
forall e1 e2 : R, 
forall n: nat,
forall i,
forall v1 : varinfo,
Maps.PTree.get i (lf_bmap_n e1 e2 ( n)) = Some v1 -> 
exists v2 : varinfo,
Maps.PTree.get i (lf_bmap_n e1 e2 (S n)) = Some v2.  
Proof.
intros.
apply Maps.PTree.elements_correct in H.
destruct H.
+ inversion H. 
exists ({|
       var_type := Tsingle;
       var_name := _x;
       var_lobound := -1 * (1 + INR (S n) * e1);
       var_hibound := 1 * (1 + INR (S n) * e1)
     |}).
simpl; auto.
+ simpl in H. destruct H; try contradiction.
inversion H. 
exists ({|
       var_type := Tsingle;
       var_name := _v;
       var_lobound := -1 * (1 + INR (S n) * e2);
       var_hibound := 1 * (1 + INR (S n) * e2)
     |}).
simpl; auto. 
Qed.

Lemma bmd_Sn_exists_iff : 
forall e1 e2 : R, 
forall n: nat,
forall i,
(exists v1 : varinfo,
Maps.PTree.get i (lf_bmap_n e1 e2 ( n)) = Some v1) <-> 
(exists v2 : varinfo,
Maps.PTree.get i (lf_bmap_n e1 e2 (S n)) = Some v2).  
Proof.
intros.
split.
intros. destruct H. eapply bmd_Sn_varinfo. apply H.
intros. destruct H.
apply Maps.PTree.elements_correct in H.
destruct H.
+ inversion H. 
exists ({|
       var_type := Tsingle;
       var_name := _x;
       var_lobound := -1 * (1 + INR (n) * e1);
       var_hibound := 1 * (1 + INR (n) * e1)
     |}).
simpl; auto.
+ simpl in H. destruct H; try contradiction.
inversion H. 
exists ({|
       var_type := Tsingle;
       var_name := _v;
       var_lobound := -1 * (1 + INR ( n) * e2);
       var_hibound := 1 * (1 + INR (n) * e2)
     |}).
simpl; auto. 
Qed.


Lemma bmd_Sn_vars_eq : 
forall e1 e2 : R, 
forall n: nat,
forall i,
forall v1 v2 : varinfo,
Maps.PTree.get i (lf_bmap_n e1 e2 (S n)) = Some v1 -> 
Maps.PTree.get i (lf_bmap_n e1 e2 ( n)) = Some v2 -> 
v1.(var_name) = v2.(var_name) /\
v1.(var_type) = v2.(var_type).
Proof.
intros.
apply Maps.PTree.elements_correct in H.
destruct H.
+ inversion H. subst. clear H.
simpl in H0. inversion H0; auto.
+ simpl in H. destruct H; try contradiction.
inversion H. subst. clear H.
simpl in H0. inversion H0; auto. 
Qed.



Lemma bmd_Sn_bnds_le : 
forall e1 e2 : R, 
   0<= e1 ->
   0<= e2 ->
forall n: nat,
forall i,
forall v1 v2 : varinfo,
Maps.PTree.get i (lf_bmap_n e1 e2 (S n)) = Some v1-> 
Maps.PTree.get i (lf_bmap_n e1 e2 ( n)) = Some v2 -> 
v1.(var_lobound) <= v2.(var_lobound) /\ 
v2.(var_hibound) <= v1.(var_hibound). 
Proof.
intros.
apply Maps.PTree.elements_correct in H1.
inversion H1.
+ set (yy:= INR (S n)) in H3. inversion H3. subst. clear H1. 
simpl in H2. inversion H2. simpl. subst yy. rewrite ?S_INR.
split. all : (field_simplify; try nra).
+ set (yy:= INR (S n)) in H3. simpl in H3. destruct H3; try contradiction.
inversion H3. subst. clear H1. 
simpl in H2. inversion H2. simpl. subst yy. rewrite ?S_INR. 
split. all : (field_simplify; try nra).
Qed.


Lemma bmd_Sn : 
forall x v : float32, 
forall e1 e2 : R, 
0<= e1  ->
0<= e2  ->
forall n: nat,
boundsmap_denote (lf_bmap_n e1 e2 (n)) (leapfrog_vmap x v) ->
boundsmap_denote (lf_bmap_n e1 e2 (S n)) (leapfrog_vmap x v).
Proof.
intros.
unfold boundsmap_denote.
intros.
 specialize (H1 i).
pose proof bmd_Sn_bnds_le e1 e2 H H0 n i.
pose proof bmd_Sn_vars_eq e1 e2 n i.
pose proof bmd_Sn_exists_iff  e1 e2 n i.
destruct (Maps.PTree.get i (leapfrog_vmap x v)).
+ destruct (Maps.PTree.get i (lf_bmap_n e1 e2 ( n))); try contradiction.
++ destruct (Maps.PTree.get i (lf_bmap_n e1 e2 (S n))).
+++ specialize (H2 v2 v1 eq_refl eq_refl).
specialize (H3 v2 v1  eq_refl eq_refl).
destruct v1; destruct v2. 
destruct H1 as (xp & A & B & C & D).
simpl in H2; simpl in H3. destruct H3. subst.
exists xp; repeat split; auto.
eapply Rle_trans. apply H2. apply D.
eapply Rle_trans. apply D. apply H2.
+++ destruct H4; destruct H4. exists v1; auto. discriminate; auto.
+ destruct (Maps.PTree.get i (lf_bmap_n e1 e2 ( n))).
++  destruct v0; try contradiction.
++ destruct (Maps.PTree.get i (lf_bmap_n e1 e2 (S n))); auto.
destruct H4; destruct H5. exists v0; auto. discriminate; auto.
Qed.



Import B_Float_Notations.


Lemma env_fval_reify_correct_leapfrog_step_x:
  forall x v : float32,
  fval (leapfrog_env x v) x' = leapfrog_stepx x v.
Proof.
intros. 
unfold_reflect' x'.  
unfold_float_ops_for_equality. 
reflexivity.
Qed.  

Lemma env_n_fval_reify_correct_leapfrog_step_x:
  forall x v : float32,
  forall e1 e2 : R,
  forall n : nat,
  fval (lf_env_n x v e1 e2 n) x' = leapfrog_stepx x v.
Proof.
intros. 
unfold_reflect' x'.  
unfold_float_ops_for_equality. 
reflexivity.
Qed.  


Lemma env_fval_reify_correct_leapfrog_step_v:
  forall x v : float32,
  fval (leapfrog_env  x v) v' = leapfrog_stepv x v.
Proof.
intros.
unfold_reflect' v'.  
unfold_float_ops_for_equality. 
reflexivity. 
Qed.  

Lemma env_n_fval_reify_correct_leapfrog_step_v:
  forall x v : float32,
  forall x v : float32,
  forall e1 e2 : R,
  forall n : nat,
  fval (lf_env_n x v e1 e2 n) v' = leapfrog_stepv x v.
Proof.
intros.
unfold_reflect' v'.  
unfold_float_ops_for_equality. 
reflexivity. 
Qed.  


Lemma env_fval_reify_correct_leapfrog_step:
  forall x v : float32,
  fval (leapfrog_env x v) x' = leapfrog_stepx x v /\
  fval (leapfrog_env  x v) v' = leapfrog_stepv x v.
Proof.
intros. 
unfold leapfrog_env.
unfold leapfrog_env; split.
- unfold_reflect' x'. unfold_float_ops_for_equality. reflexivity.
- unfold_reflect' v'. unfold_float_ops_for_equality. reflexivity.
Qed.


Lemma env_n_fval_reify_correct_leapfrog_step:
  forall x v : float32,
  forall e1 e2 : R,
  forall n : nat,
  fval (lf_env_n x v e1 e2 n) x' = leapfrog_stepx x v /\
  fval (lf_env_n x v e1 e2 n) v' = leapfrog_stepv x v.
Proof.
intros. 
unfold leapfrog_env.
unfold leapfrog_env; split.
- unfold_reflect' x'. unfold_float_ops_for_equality. reflexivity.
- unfold_reflect' v'. unfold_float_ops_for_equality. reflexivity.
Qed.


Lemma env_rval_reify_correct_leapfrog_stepx:
  forall x v : float32,
  forall x1 v1 : R,
  x1 = B2R _ _ x ->
  v1 = B2R _ _ v -> 
  rval (leapfrog_env x v) (optimize_div x') = fst (leapfrog_stepR' (x1,v1)).
Proof.
intros.
unfold leapfrog_env.
simplify_shift_div_opt (optimize_div x').
match goal with |- context [rval ?env ?e] =>
  unfold_reflect_rval e; cbv [id]
end.
unfold leapfrog_stepR', F, h, fst, snd; subst.
cbv [fprec femax]; simpl.
unfold Defs.F2R; simpl; nra.
Qed.

Lemma env_n_rval_reify_correct_leapfrog_stepx:
  forall x v : float32,
  forall x1 v1 : R,
  forall e1 e2 : R,
  x1 = B2R _ _ x ->
  v1 = B2R _ _ v -> 
  forall n : nat,
  rval (lf_env_n x v e1 e2 n) (optimize_div x') = fst (leapfrog_stepR' (x1,v1)).
Proof.
intros.
unfold leapfrog_env.
simplify_shift_div_opt (optimize_div x'). unfold lf_env_n.
match goal with |- context [rval ?env ?e] =>
  unfold_reflect_rval e; cbv [id]
end.
unfold leapfrog_stepR', F, h, fst, snd; subst.
cbv [fprec femax]; simpl.
unfold Defs.F2R; simpl; nra.
Qed.


Lemma env_rval_reify_correct_leapfrog_stepv:
  forall x v : float32,
  forall x1 v1 : R,
  x1 = B2R _ _ x ->
  v1 = B2R _ _ v -> 
  rval (leapfrog_env x v) (optimize_div v') = snd (leapfrog_stepR' (x1,v1)).
Proof.
intros.
unfold leapfrog_env.
simplify_shift_div_opt (optimize_div v').
match goal with |- context [rval ?env ?e] =>
  unfold_reflect_rval e; cbv [id]
end.
simpl; rewrite ?Z.pow_pos_fold. 
unfold leapfrog_stepR', F, h, fst; subst.  
cbv [fprec femax]; simpl.
unfold Defs.F2R; simpl; nra.
Qed.

Lemma env_n_rval_reify_correct_leapfrog_stepv:
  forall x v : float32,
  forall x1 v1 : R,
  forall e1 e2 : R,
  x1 = B2R _ _ x ->
  v1 = B2R _ _ v -> 
  forall n : nat,
  rval (lf_env_n x v e1 e2 n) (optimize_div v') = snd (leapfrog_stepR' (x1,v1)).
Proof.
intros.
unfold leapfrog_env.
simplify_shift_div_opt (optimize_div v'). unfold lf_env_n.
match goal with |- context [rval ?env ?e] =>
  unfold_reflect_rval e; cbv [id]
end.
unfold leapfrog_stepR', F, h, fst, snd; subst.
cbv [fprec femax]; simpl.
unfold Defs.F2R; simpl; nra.
Qed.


Require Import Coq.Logic.FunctionalExtensionality.

Lemma leapfrog_env_eq: 
  forall x v : float32,
boundsmap_denote leapfrog_bmap  (leapfrog_vmap x v) ->
leapfrog_env x v = env_ (leapfrog_vmap x v).
Proof.
intros. pose proof (env_mk_env (leapfrog_bmap ) (leapfrog_vmap x v) H). 
replace (env_ (leapfrog_vmap x v)) with 
  (mk_env (leapfrog_bmap ) (leapfrog_vmap x v)). 
unfold leapfrog_env, list_to_bound_env, mk_env, leapfrog_bmap, leapfrog_vmap.
apply functional_extensionality_dep; intro ty.
apply functional_extensionality; intro i.
 destruct (Maps.PTree.get i (Maps.PTree_Properties.of_list 
    (leapfrog_bmap_list))) as [[t i' lo hi]|],
    (Maps.PTree.get i (Maps.PTree_Properties.of_list (leapfrog_vmap_list x v))) 
    as [v'|]; try contradiction; auto.
Qed.


Lemma lf_env_n_eq: 
forall x v : float32, 
  forall n : nat,
  forall e1 e2 : R, 
boundsmap_denote (lf_bmap_n e1 e2 n)  (leapfrog_vmap x v) ->
lf_env_n x v e1 e2 n  = env_ (leapfrog_vmap x v). 
Proof.
intros. pose proof (env_mk_env (lf_bmap_n e1 e2 n)  (leapfrog_vmap x v) H). 
replace (env_ (leapfrog_vmap x v)) with 
  (mk_env (lf_bmap_n e1 e2 n)  (leapfrog_vmap x v)). 
unfold lf_env_n, list_to_bound_env, mk_env, lf_bmap_n, leapfrog_vmap.
apply functional_extensionality_dep; intro ty.
apply functional_extensionality; intro i.
 destruct (Maps.PTree.get i (Maps.PTree_Properties.of_list 
    (lf_bmap_list_n e1 e2 n))) as [[t i' lo hi]|],
    (Maps.PTree.get i (Maps.PTree_Properties.of_list (leapfrog_vmap_list x v))) 
    as [v'|]; try contradiction; auto.
Qed.


Import Interval.Tactic.


Lemma conds2_hold_optx:
  forall x v : float32,
boundsmap_denote (leapfrog_bmap ) (leapfrog_vmap x v)->
 forall r si2 s p,
    rndval_with_cond 0 (mempty (Tsingle, Normal)) (optimize_div x') = ((r, (si2, s)), p)  ->
list_forall (eval_cond2 (mk_env (leapfrog_bmap ) (leapfrog_vmap x v)) s) p.
Proof.
intros.
apply boundsmap_denote_e in H.
rewrite list_forall_Forall in H.
rewrite list_forall_Forall.
rndval_inversion; subst.
fold Tsingle ; fold Tdouble.
prepare_assumptions_about_free_variables;
repeat (apply List.Forall_cons; try apply List.Forall_nil;
try solve_one_eval_cond2; 
try interval).
Qed.


Lemma conds2_hold_optx_n:
forall x v : float32, 
  forall n : nat,
  (n <=1000)%nat ->
  forall e1 e2 : R, 
   0<= e1 <= 1 ->
   0<= e2 <= 1 ->
  boundsmap_denote (lf_bmap_n e1 e2 n) (leapfrog_vmap x v)->
 forall r si2 s p,
    rndval_with_cond 0 (mempty (Tsingle, Normal)) (optimize_div x') = ((r, (si2, s)), p)  ->
list_forall (eval_cond2 (mk_env (lf_bmap_n e1 e2 n) (leapfrog_vmap x v)) s) p.
Proof.
intros.
apply boundsmap_denote_e in H2.
rewrite list_forall_Forall in H2.
rewrite list_forall_Forall.
rndval_inversion; subst.
fold Tsingle ; fold Tdouble.
prepare_assumptions_about_free_variables.
clear H3.


assert ( 1 * (1 + INR n * e1) <= 1001).
eapply Rle_trans.
eapply Rmult_le_compat_l; try nra.
eapply Rplus_le_compat_l; try nra.
eapply Rle_trans.
eapply Rmult_le_compat_l. 
apply pos_INR.
apply H0. rewrite Rmult_1_r. 
apply le_INR in H; apply H.
try (simpl;nra).
assert (-1001 <= FT2R Tsingle val_x).
apply Ropp_le_contravar in H2; auto.
rewrite Ropp_mult_distr_l in H2.
eapply Rle_trans.
apply H2. 
eapply Rle_trans.
apply Hrange_x. apply Rle_refl.
assert (FT2R Tsingle val_x <= 1001).
eapply Rle_trans.
apply Hrange_x.
apply H2.

assert ( 1 * (1 + INR n * e2) <= 1001).
eapply Rle_trans.
eapply Rmult_le_compat_l; try nra.
eapply Rplus_le_compat_l; try nra.
eapply Rle_trans.
eapply Rmult_le_compat_l.
apply pos_INR.
apply H1. rewrite Rmult_1_r. 
apply le_INR in H; apply H.
try (simpl;nra).
assert (-1001 <= FT2R Tsingle val_v).
apply Ropp_le_contravar in H5; auto.
rewrite Ropp_mult_distr_l in H5.
eapply Rle_trans.
apply H5. 
eapply Rle_trans.
apply Hrange_v. apply Rle_refl.
assert (FT2R Tsingle val_v <= 1001).
eapply Rle_trans.
apply Hrange_v.
apply H5.

repeat (apply List.Forall_cons; try apply List.Forall_nil;
try solve_one_eval_cond2; 
try interval).
Qed.


Lemma conds2_hold_optv:
  forall x v : float32,
boundsmap_denote (leapfrog_bmap ) (leapfrog_vmap x v)->
 forall r si2 s p,
    rndval_with_cond 0 (mempty (Tsingle, Normal)) (optimize_div v') = ((r, (si2, s)), p)  ->
list_forall (eval_cond2 (mk_env (leapfrog_bmap ) (leapfrog_vmap x v)) s) p.
Proof.
intros.
apply boundsmap_denote_e in H.
rewrite list_forall_Forall in H.
rewrite list_forall_Forall.
rndval_inversion; subst.
fold Tsingle ; fold Tdouble.
prepare_assumptions_about_free_variables;
repeat (apply List.Forall_cons; try apply List.Forall_nil;
try solve_one_eval_cond2; 
try interval).
Qed. 


Lemma conds2_hold_optv_n:
forall x v : float32, 
  forall n : nat,
  (n <=1000)%nat ->
  forall e1 e2 : R, 
   0<= e1 <= 1 ->
   0<= e2 <= 1 ->
boundsmap_denote (lf_bmap_n e1 e2 n) (leapfrog_vmap x v)->
 forall r si2 s p,
    rndval_with_cond 0 (mempty (Tsingle, Normal)) (optimize_div v') = ((r, (si2, s)), p)  ->
list_forall (eval_cond2 (mk_env (lf_bmap_n e1 e2 n) (leapfrog_vmap x v)) s) p.
Proof.
intros.
apply boundsmap_denote_e in H2.
rewrite list_forall_Forall in H2.
rewrite list_forall_Forall.
rndval_inversion; subst.
fold Tsingle ; fold Tdouble.
prepare_assumptions_about_free_variables.
clear H3.

assert ( 1 * (1 + INR n * e1) <= 1001).
eapply Rle_trans.
eapply Rmult_le_compat_l; try nra.
eapply Rplus_le_compat_l; try nra.
eapply Rle_trans.
eapply Rmult_le_compat_l.
apply pos_INR.
apply H0. rewrite Rmult_1_r. 
apply le_INR in H; apply H.
try (simpl;nra).
try nra.
assert (-1001 <= FT2R Tsingle val_x).
apply Ropp_le_contravar in H2; auto.
rewrite Ropp_mult_distr_l in H2.
eapply Rle_trans.
apply H2. 
eapply Rle_trans.
apply Hrange_x. apply Rle_refl.
assert (FT2R Tsingle val_x <= 1001).
eapply Rle_trans.
apply Hrange_x.
apply H2.

assert ( 1 * (1 + INR n * e2) <= 1001).
eapply Rle_trans.
eapply Rmult_le_compat_l; try nra.
eapply Rplus_le_compat_l; try nra.
eapply Rle_trans.
eapply Rmult_le_compat_l; try nra.
apply pos_INR.
apply H1. rewrite Rmult_1_r.
apply le_INR in H; apply H.
try (simpl;nra).
assert (-1001 <= FT2R Tsingle val_v).
apply Ropp_le_contravar in H5; auto.
rewrite Ropp_mult_distr_l in H5.
eapply Rle_trans.
apply H5. 
eapply Rle_trans.
apply Hrange_v. apply Rle_refl.
assert (FT2R Tsingle val_v <= 1001).
eapply Rle_trans.
apply Hrange_v.
apply H5.

repeat (apply List.Forall_cons; try apply List.Forall_nil;
try solve_one_eval_cond2; 
try interval).
Qed.


Ltac leapfrog_conds1_hold ex lc2:=
  match goal with
    H0: boundsmap_denote ?bmap ?vmap 
    |- forall i : cond, List.In i ?p -> eval_cond1 (env_ ?vmap) ?s i =>
assert (list_forall (eval_cond2 (mk_env bmap vmap) s) p) by (apply lc2);
replace (mk_env bmap vmap) with (env_ vmap) in * by (apply env_mk_env; auto);
apply list_forall_spec;
apply (list_forall_ext (eval_cond2 (env_ vmap) s)); auto;
    apply eval_cond2_correct
end.

Ltac get_rndval_with_conds ex:=
match goal with
    H: boundsmap_denote ?bmap ?vmap |- _ => 
let HFIN:= fresh in (
assert (forall ty i, is_finite (fprec ty) (femax ty) ((env_ vmap) ty i) = true) as HFIN by
 (apply (finite_env bmap vmap H))
);
(destruct (rndval_with_cond O (mempty  (Tsingle, Normal)) ex) as [[r [si2 s]] p] eqn:rndval);
let lc2:= fresh in ( 
assert (list_forall (eval_cond2 (mk_env bmap vmap) s) p ) as lc2)
end.


Ltac get_rndval_with_cond_correct ex HFIN lc2 rndval s p:=
match goal with
    H: boundsmap_denote ?bmap ?vmap |- _ => 
let HVALID:= fresh in ( 
assert (expr_valid ex = true) as HVALID by reflexivity
);
let listconds:= fresh in (
assert (forall i : cond, List.In i p -> eval_cond1 (env_ vmap) s i) as listconds by
(leapfrog_conds1_hold ex lc2)
);
replace (mk_env bmap vmap) with (env_ vmap) in * by (apply env_mk_env; auto);
(destruct (rndval_with_cond_correct
                          _ HFIN _ HVALID _ _ _ _ rndval lc2 _ (eq_refl _)) as [] eqn:correct)
end.

Ltac get_eps_delts := 
match goal with
  | H0:enum_exists 0 _ _ _
    |- _ =>
        hnf in H0;
repeat match type of H0 with context [@mget ?a ?b ?c ?d ?e ?f] => 
        let x := fresh "x" in set (x := @mget a b c d e f) in H0;
compute in x; subst x
   end; 
repeat
(let ed := fresh "ed" in
let B := fresh "B" in
destruct H0 as (ed & B & H0);
            match type of B with
            | context [ error_bound _ ?a ] =>
                match a with
                | Normal => let d := fresh "del" in
                            rename
                            ed into d
                | Denormal => let e := fresh "eps" in
                              rename
                              ed into e
                | uNormal => let e := fresh "eps" in
                              rename
                              ed into e
                end
             end;
unfold error_bound in B; simpl in B;
rewrite ?IZR_Zpower_pos in B;
rewrite ?mul_hlf_powerRZ in B
)
end;
repeat match goal with
  | H0:Rabs ?e <= powerRZ 2 (-?x - ?y)
    |- _ =>
match type of H0 with context [Rabs ?e <= powerRZ 2 (-?x - ?y)] => 
set (gg:=(-x - y)%Z) in H0; simpl in gg; subst gg
end
end
.


Lemma rndval_with_cond_correct_optx:
  forall x v : float32,
    boundsmap_denote (leapfrog_bmap ) (leapfrog_vmap x v)->
forall r si2 s p,
rndval_with_cond 0 (mempty (Tsingle, Normal)) (optimize_div x') = ((r, (si2, s)), p) ->
rndval_with_cond_result (env_ (leapfrog_vmap x v)) (optimize_div x') r si2 s
.
Proof.
intros.
assert
(HFIN : forall ty i, is_finite (fprec ty) (femax ty) (env_ (leapfrog_vmap x v) ty i) = true) by
apply (finite_env (leapfrog_bmap ) (leapfrog_vmap x v) H).
assert (lc2 : list_forall (eval_cond2 (mk_env (leapfrog_bmap ) (leapfrog_vmap x v)) s) p).
eapply conds2_hold_optx; auto; apply H0.
assert (HVALID : expr_valid (optimize_div x') = true) by reflexivity.
assert (listconds : forall i : cond, In i p -> eval_cond1 (env_ (leapfrog_vmap x v)) s i) by
           leapfrog_conds1_hold (optimize_div x') lc2.
eapply rndval_with_cond_correct; auto; try apply H0.
rewrite <- env_mk_env in lc2; auto.
Qed.


Lemma rndval_with_cond_correct_optv:
  forall x v : float32,
    boundsmap_denote (leapfrog_bmap ) (leapfrog_vmap x v)->
forall r si2 s p,
rndval_with_cond 0 (mempty (Tsingle, Normal)) (optimize_div v') = ((r, (si2, s)), p) ->
rndval_with_cond_result (env_ (leapfrog_vmap x v)) (optimize_div v') r si2 s
.
Proof.
intros.
assert
(HFIN : forall ty i, is_finite (fprec ty) (femax ty) (env_ (leapfrog_vmap x v) ty i) = true) by
apply (finite_env (leapfrog_bmap ) (leapfrog_vmap x v) H).
assert (lc2 : list_forall (eval_cond2 (mk_env (leapfrog_bmap ) (leapfrog_vmap x v)) s) p).
eapply conds2_hold_optv; auto; apply H0.
assert (HVALID : expr_valid (optimize_div v') = true) by reflexivity.
assert (listconds : forall i : cond, In i p -> eval_cond1 (env_ (leapfrog_vmap x v)) s i) by
           leapfrog_conds1_hold (optimize_div v') lc2.
eapply rndval_with_cond_correct; auto; try apply H0.
rewrite <- env_mk_env in lc2; auto.
Qed.


Lemma rndval_with_cond_correct_optx_n:
forall x v : float32, 
  forall n : nat,
  (n <=1000)%nat ->
  forall e1 e2 : R, 
   0<= e1 <= 1 ->
   0<= e2 <= 1 ->
boundsmap_denote (lf_bmap_n e1 e2 n) (leapfrog_vmap x v)->
forall r si2 s p,
    rndval_with_cond 0 (mempty (Tsingle, Normal)) (optimize_div x') = ((r, (si2, s)), p)  ->
rndval_with_cond_result (env_ (leapfrog_vmap x v)) (optimize_div x') r si2 s
.
Proof.
intros.
assert
(HFIN : 
  forall ty i, is_finite (fprec ty) (femax ty) (env_ (leapfrog_vmap x v) ty i) = true) by
apply (finite_env (lf_bmap_n e1 e2 n) (leapfrog_vmap x v) H2).
assert 
(lc2 : 
  list_forall (eval_cond2 (mk_env (lf_bmap_n e1 e2 n) (leapfrog_vmap x v)) s) p).
eapply conds2_hold_optx_n; auto; apply H3.
assert (HVALID : expr_valid (optimize_div x') = true) by reflexivity.
assert (listconds : forall i : cond, In i p -> eval_cond1 (env_ (leapfrog_vmap x v)) s i) by
           leapfrog_conds1_hold (optimize_div x') lc2.
eapply rndval_with_cond_correct; auto; try apply H3.
rewrite <- env_mk_env in lc2; auto.
Qed.


Lemma rndval_with_cond_correct_optv_n:
forall x v : float32, 
  forall n : nat,
  (n <=1000)%nat ->
  forall e1 e2 : R, 
   0<= e1 <= 1 ->
   0<= e2 <= 1 ->
boundsmap_denote (lf_bmap_n e1 e2 n) (leapfrog_vmap x v)->
forall r si2 s p,
    rndval_with_cond 0 (mempty (Tsingle, Normal)) (optimize_div v') = ((r, (si2, s)), p)  ->
rndval_with_cond_result (env_ (leapfrog_vmap x v)) (optimize_div v') r si2 s
.
Proof.
intros.
assert
(HFIN : 
  forall ty i, is_finite (fprec ty) (femax ty) (env_ (leapfrog_vmap x v) ty i) = true) by
apply (finite_env (lf_bmap_n e1 e2 n) (leapfrog_vmap x v) H2).
assert 
(lc2 : 
  list_forall (eval_cond2 (mk_env (lf_bmap_n e1 e2 n) (leapfrog_vmap x v)) s) p).
eapply conds2_hold_optv_n; auto; apply H3.
assert (HVALID : expr_valid (optimize_div v') = true) by reflexivity.
assert (listconds : forall i : cond, In i p -> eval_cond1 (env_ (leapfrog_vmap x v)) s i) by
           leapfrog_conds1_hold (optimize_div x') lc2.
eapply rndval_with_cond_correct; auto; try apply H3.
rewrite <- env_mk_env in lc2; auto.
Qed.


Ltac lf_rewrites :=
repeat match goal with |- context [(env_ ?vmap ?ty2 ?var)] =>
  set (yy:=(env_ vmap ty2 var));
  cbv in yy; subst yy
end;
repeat match goal with |- context [(?env ?x ?v ?ty2 ?var)] =>
  set (yy:=(env x v ty2 var));
  cbv in yy; subst yy
end;
unfold FT2R in *;
change (fprec Tsingle) with 24%Z in *; 
change (femax Tsingle) with 128%Z in *;
repeat match goal with H0: Maps.PTree.get ?_v ?vmap = Some ?s |- _ =>
  (cbv in H0;inversion H0; clear H0; subst; auto)
end
.

Ltac fvs_from_bndsmap_hyp H:=
  assert (boundsmap_denote _ _ ) as BMD by (apply H) ;
  apply boundsmap_denote_e in H;
  rewrite list_forall_Forall in H;
  prepare_assumptions_about_free_variables
.

Ltac interval_solve :=
match goal with |- context [Rabs (?v) <= _] =>
  field_simplify v;
repeat (try split; try interval)
end;
match goal with |- context [Rabs (?v) <= _] =>
  interval_intro (Rabs v) upper
end;
try nra 
.

Ltac simpl_pow :=
replace 8388608 with (2 ^ Pos.to_nat 23) by (simpl; field_simplify; nra);
assert  (2 <> 0) by lra;
 repeat (rewrite <- powerRZ_pos_sub; auto); 
repeat match goal with |-context[(Z.pos_sub ?a ?b)] =>
set (yy:= (Z.pos_sub a b)); compute in yy;
subst yy
end
.

Ltac intro_absolute_error_bound_aux ty kn bmd x v rndval_result:=
match goal with |- context [
    Rle (Rabs (?op (rval ?env ?e) 
   (B2R _ _ (fval ?env ?e)))) 
         ?val ] =>

unfold rndval_with_cond_result in rndval_result;
set (Hty:= type_of_expr e) in *;
simpl in Hty ;
cbv [Datatypes.id] in Hty;   
repeat change (type_lub ty ty) with ty in Hty;
unfold Hty in *; clear Hty;
pose proof rndval_result (fval env e) as RESULT_A ;
         (*rewrite ?leapfrog_env_eq in RESULT_A; auto;*)
 pose proof RESULT_A eq_refl as RESULT; clear RESULT_A ;
clear rndval_result; 
destruct RESULT as (HFIN & ERRORS); 
clear HFIN; revert ERRORS;
try simplify_shift_div_opt e;
fvs_from_bndsmap_hyp bmd;
intros;
rndval_inversion; subst;
fold lf_harm_lemmas._x in *;
fold lf_harm_lemmas._v in *;
subst;
fold ty in * ;
get_eps_delts ;
try (rewrite <- ERRORS; clear ERRORS);
try (rewrite ?leapfrog_env_eq; auto; rewrite <- ERRORS; clear ERRORS);
match goal with
  | |- context [ reval _ _ (mget (mset ?M _ _)) ] =>
        let m := fresh "m" in
        set (m := M); compute in m; unfold reval; simpl rval; try cbv[id]
end;
repeat match goal with
  | |- context [ mget ?m ?i ] =>
  let x := fresh "x" in
  set (x := mget m i); hnf in x; subst x
end;
cbv[reval Prog.binary Prog.real_operations Tree.binary_real Prog.unary
Prog.binary Tree.unary_real];
cbv[F2R Defs.F2R fone bpow radix_val radix2 Fexp Fnum];
rewrite ?Zpower_pos_powerRZ; unfold powerRZ; rewrite ?powerRZ_pos_sub2;
rewrite ?Rmult_1_l; rewrite ?Rmult_1_r; rewrite ?powerRZ_O; 
try lra;
lf_rewrites
end.

Ltac intro_absolute_error_bound ty kn bmd x v rndval_result:=
intro_absolute_error_bound_aux ty kn bmd x v rndval_result;
try interval_solve
.


Lemma leapfrog_opt_stepx_is_finite:
  forall x v : float32,
  boundsmap_denote leapfrog_bmap  (leapfrog_vmap x v)->
  Binary.is_finite _ _(fval (leapfrog_env x v) (optimize_div x')) = true.
Proof.
intros.
(destruct (rndval_with_cond O (mempty  (Tsingle, Normal)) (optimize_div x')) 
  as [[r [si2 s]] p] eqn:rndval).
pose proof (rndval_with_cond_correct_optx x v H r si2 s p rndval)
  as rndval_result. 
unfold rndval_with_cond_result in rndval_result;
set (Hty:= type_of_expr (optimize_div x')) in *.
repeat simpl in Hty.
cbv [Datatypes.id] in Hty.   
repeat change (type_lub Tsingle Tsingle) with Tsingle in Hty;
unfold Hty in *; clear Hty.
pose proof rndval_result (fval (leapfrog_env x v) x') as RESULT_A ;
rewrite ?lf_env_eq in RESULT_A; auto.
 pose proof RESULT_A eq_refl as RESULT; clear RESULT_A ;
clear rndval_result; 
destruct RESULT as (HFIN & ERRORS).
apply HFIN.
Qed.

Lemma leapfrog_opt_stepv_is_finite:
  forall x v : float32,
  boundsmap_denote leapfrog_bmap (leapfrog_vmap x v)->
  Binary.is_finite _ _(fval (leapfrog_env  x v) (optimize_div v')) = true.
Proof. 
intros.
(destruct (rndval_with_cond O (mempty  (Tsingle, Normal)) (optimize_div v')) 
  as [[r [si2 s]] p] eqn:rndval).
pose proof (rndval_with_cond_correct_optv x v H r si2 s p rndval)
  as rndval_result. 
unfold rndval_with_cond_result in rndval_result;
set (Hty:= type_of_expr (optimize_div v')) in *.
repeat simpl in Hty.
cbv [Datatypes.id] in Hty.   
repeat change (type_lub Tsingle Tsingle) with Tsingle in Hty;
unfold Hty in *; clear Hty.
pose proof rndval_result (fval (leapfrog_env x v) v') as RESULT_A ;
rewrite ?lf_env_eq in RESULT_A; auto.
 pose proof RESULT_A eq_refl as RESULT; clear RESULT_A ;
clear rndval_result; 
destruct RESULT as (HFIN & ERRORS).
apply HFIN.
Qed.


Lemma leapfrog_stepx_not_nan:
  forall x v : float32,
  boundsmap_denote leapfrog_bmap (leapfrog_vmap x v)->
  Binary.is_nan _ _(fval (leapfrog_env x v) x') = false.
Proof. 
intros; subst;
apply is_finite_not_is_nan.
apply leapfrog_opt_stepx_is_finite; auto. 
Qed.

Lemma leapfrog_stepv_not_nan:
  forall x v : float32,
  boundsmap_denote leapfrog_bmap (leapfrog_vmap x v)->
  Binary.is_nan _ _(fval (leapfrog_env x v) v') = false.
Proof. 
intros; subst;
apply is_finite_not_is_nan.
apply leapfrog_opt_stepv_is_finite; auto. 
Qed.


Lemma leapfrog_opt_stepx_is_finite_n:
forall x v : float32, 
  forall n : nat,
  (n <=1000)%nat ->
  forall e1 e2 : R, 
   0<= e1 <= 1 ->
   0<= e2 <= 1 ->
  boundsmap_denote (lf_bmap_n e1 e2 n) (leapfrog_vmap x v)->
  Binary.is_finite _ _(fval (lf_env_n x v e1 e2 n) (optimize_div x')) = true.
Proof.
intros.
(destruct (rndval_with_cond O (mempty  (Tsingle, Normal)) (optimize_div x')) 
  as [[r [si2 s]] p] eqn:rndval).
pose proof (rndval_with_cond_correct_optx_n x v n H e1 e2 H0 H1 H2 r si2 s p rndval)
  as rndval_result. 
unfold rndval_with_cond_result in rndval_result;
set (Hty:= type_of_expr (optimize_div x')) in *.
repeat simpl in Hty.
cbv [Datatypes.id] in Hty.   
repeat change (type_lub Tsingle Tsingle) with Tsingle in Hty;
unfold Hty in *; clear Hty.
pose proof rndval_result (fval (lf_env_n x v e1 e2 n) x') as RESULT_A ;
rewrite ?lf_env_eq in RESULT_A; auto.
 pose proof RESULT_A eq_refl as RESULT; clear RESULT_A ;
clear rndval_result; 
destruct RESULT as (HFIN & ERRORS).
apply HFIN.
Qed.

Lemma leapfrog_opt_stepv_is_finite_n:
forall x v : float32, 
  forall n : nat,
  (n <=1000)%nat ->
  forall e1 e2 : R, 
   0<= e1 <= 1 ->
   0<= e2 <= 1 ->
  boundsmap_denote (lf_bmap_n e1 e2 n) (leapfrog_vmap x v)->
  Binary.is_finite _ _(fval (lf_env_n x v e1 e2 n) (optimize_div v')) = true.
Proof.
intros.
(destruct (rndval_with_cond O (mempty  (Tsingle, Normal)) (optimize_div v')) 
  as [[r [si2 s]] p] eqn:rndval).
pose proof (rndval_with_cond_correct_optv_n x v n H e1 e2 H0 H1 H2 r si2 s p rndval)
  as rndval_result. 
unfold rndval_with_cond_result in rndval_result;
set (Hty:= type_of_expr (optimize_div v')) in *.
repeat simpl in Hty.
cbv [Datatypes.id] in Hty.   
repeat change (type_lub Tsingle Tsingle) with Tsingle in Hty;
unfold Hty in *; clear Hty.
pose proof rndval_result (fval (lf_env_n x v e1 e2 n) v') as RESULT_A ;
rewrite ?lf_env_eq in RESULT_A; auto.
 pose proof RESULT_A eq_refl as RESULT; clear RESULT_A ;
clear rndval_result; 
destruct RESULT as (HFIN & ERRORS).
apply HFIN.
Qed.


Lemma leapfrog_stepx_not_nan_n:
forall x v : float32, 
  forall n : nat,
  (n <= 1000)%nat ->
  forall e1 e2 : R, 
   0<= e1 <= 1 ->
   0<= e2 <= 1 ->
  boundsmap_denote (lf_bmap_n e1 e2 n) (leapfrog_vmap x v)->
  Binary.is_nan _ _(fval (lf_env_n x v e1 e2 n) x') = false.
Proof. 
intros; subst;
apply is_finite_not_is_nan.
eapply leapfrog_opt_stepx_is_finite_n; auto.
Qed.

Lemma leapfrog_stepv_not_nan_n:
forall x v : float32, 
  forall n : nat,
  (n <= 1000)%nat ->
  forall e1 e2 : R, 
   0<= e1 <= 1 ->
   0<= e2 <= 1 ->
  boundsmap_denote (lf_bmap_n e1 e2 n) (leapfrog_vmap x v)->
  Binary.is_nan _ _(fval (lf_env_n x v e1 e2 n) v') = false.
Proof. 
intros; subst;
apply is_finite_not_is_nan.
eapply leapfrog_opt_stepv_is_finite_n; auto.
Qed.

