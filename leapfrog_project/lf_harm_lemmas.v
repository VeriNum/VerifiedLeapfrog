(* This file contains lemmas and tactics for proofs of the floating point properties *)

From Flocq Require Import Binary Bits Core.
From compcert.lib Require Import IEEE754_extra.
Require Import lf_harm_float lf_harm_real vcfloat real_lemmas.
Set Bullet Behavior "Strict Subproofs". 

Open Scope R_scope.

Section WITHNANS.
Context {NANS: Nans}.

Definition leapfrog_stepx x v := fst (leapfrog_step' (x,v)).
Definition leapfrog_stepv x v := snd (leapfrog_step' (x,v)).

Definition leapfrog_step_q p q := snd (leapfrogF p q 1).
Definition leapfrog_step_p p q := fst (leapfrogF p q 1).

Import List ListNotations.

Definition _x : ident := 1%positive.
Definition _v : ident := 2%positive.

Definition x_init := 0%F32.
Definition v_init := 1%F32.

Definition x' := ltac:(let e' := 
  HO_reify_float_expr constr:([_x; _v]) leapfrog_stepx in exact e').
Definition v' := ltac:(let e' := 
  HO_reify_float_expr constr:([_x; _v]) leapfrog_stepv in exact e').

Definition q' := ltac:(let e' := 
  HO_reify_float_expr constr:([_v; _x]) leapfrog_step_q in exact e').
Definition p' := ltac:(let e' := 
  HO_reify_float_expr constr:([_v; _x]) leapfrog_step_p in exact e').



Definition leapfrog_vmap_list (x v : ftype Tsingle) := 
   [(_x, existT ftype _ x);(_v, existT ftype _ v)].
Definition leapfrog_vmap (x v : ftype Tsingle) : valmap :=
 ltac:(let z := compute_PTree (valmap_of_list (leapfrog_vmap_list x v)) in exact z).

Definition leapfrog_bmap_list : list varinfo := 
  [ Build_varinfo Tsingle _x (-100)  100 ;  Build_varinfo Tsingle _v (-100)  100 ].
Definition leapfrog_bmap : boundsmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list leapfrog_bmap_list) in exact z).

Definition leapfrog_env  x v := env_ (leapfrog_vmap x v).

Definition lf_bmap_list_n (n: Z) := 
  [ Build_varinfo Tsingle _x (-1 - IZR n)  (1 + IZR n) ;  
    Build_varinfo Tsingle _v  (-1 - IZR n)  (1 + IZR n) ].
Definition lf_bmap_n  (n: Z) :=  
 ltac:(let z := compute_PTree (boundsmap_of_list (lf_bmap_list_n n)) in exact z).

Definition lf_vmap := leapfrog_vmap x_init v_init.
Definition lf_env_n  (x v : ftype Tsingle) (n: Z) := env_ (leapfrog_vmap x v).

Lemma bmd_Sn_varinfo : 
forall n: Z,
forall i,
forall v1 : varinfo,
Maps.PTree.get i (lf_bmap_n   ( n)) = Some v1 -> 
exists v2 : varinfo,
Maps.PTree.get i (lf_bmap_n   (Z.succ n)) = Some v2.  
Proof.
intros ? ? ? H; apply Maps.PTree.elements_correct in H;
repeat destruct H as [ H | ]; try contradiction;
 inversion H; clear H; subst; eexists; reflexivity.
Qed.

Lemma bmd_Sn_exists_iff : 
forall n: Z,
forall i,
(exists v1 : varinfo,
Maps.PTree.get i (lf_bmap_n  ( n)) = Some v1) <-> 
(exists v2 : varinfo,
Maps.PTree.get i (lf_bmap_n  (Z.succ n)) = Some v2).  
Proof.
intros.
split;
intros [? H]; apply Maps.PTree.elements_correct in H;
repeat destruct H as [ H | ]; try contradiction;
 inversion H; clear H; subst; eexists; reflexivity.
Qed.

Lemma bmd_Sn_vars_eq : 
forall n: Z,
forall i,
forall v1 v2 : varinfo,
Maps.PTree.get i (lf_bmap_n  (Z.succ n)) = Some v1 -> 
Maps.PTree.get i (lf_bmap_n  ( n)) = Some v2 -> 
v1.(var_name) = v2.(var_name) /\
v1.(var_type) = v2.(var_type).
Proof.
intros.
apply Maps.PTree.elements_correct in H.
repeat destruct H as [ H | ]; try contradiction;
 inversion H; clear H; subst; inversion H0; clear H0; subst; split; reflexivity.
Qed.

Lemma bmd_Sn_bnds_le : 
forall n: Z,
forall i,
forall v1 v2 : varinfo,
Maps.PTree.get i (lf_bmap_n (Z.succ n)) = Some v1-> 
Maps.PTree.get i (lf_bmap_n ( n)) = Some v2 -> 
v1.(var_lobound) <= v2.(var_lobound) /\ 
v2.(var_hibound) <= v1.(var_hibound). 
Proof.
intros.
apply Maps.PTree.elements_correct in H.
repeat destruct H as [ H | ]; try contradiction;
rewrite succ_IZR in H;
 inversion H; clear H; subst; inversion H0; clear H0; subst; split;
simpl; lra.
Qed.

Lemma bmd_Sn : 
forall x v : ftype Tsingle, 
forall n: Z,
boundsmap_denote (lf_bmap_n   (n)) (leapfrog_vmap x v) ->
boundsmap_denote (lf_bmap_n   (Z.succ n)) (leapfrog_vmap x v).
Proof.
intros.
intro i; specialize (H i).
destruct (Maps.PTree.get i (lf_bmap_n n)) eqn:H0.
- (* Some *)
destruct (bmd_Sn_varinfo _ _ _ H0) as [w H1]; rewrite H1.
destruct v0 as [t i' lo hi], w as [t0 i'0 lo0 hi0].
destruct (Maps.PTree.get i (leapfrog_vmap x v)) as [ [ty u] | ] eqn:?H;
 [ | contradiction].
destruct H as [? [? [? ?]]]; subst i' t.
destruct (bmd_Sn_vars_eq _ _ _ _ H1 H0); simpl in *; subst.
split; [ | split; [ | split]]; auto.
destruct (bmd_Sn_bnds_le _ _ _ _ H1 H0); simpl in *.
lra.
-
destruct (bmd_Sn_exists_iff    n i) as [_ ?].
destruct (Maps.PTree.get i (lf_bmap_n (Z.succ n))); auto.
destruct H1. eauto. congruence.
Qed.

Lemma env_fval_reify_correct_leapfrog_step_x:
  forall x v : ftype Tsingle,
  fval (leapfrog_env x v) x' = leapfrog_stepx x v.
Proof. reflexivity. Qed.  

Lemma env_n_fval_reify_correct_leapfrog_step_x:
  forall x v : ftype Tsingle,
  forall n : Z,
  fval (lf_env_n x v   n) x' = leapfrog_stepx x v.
Proof. reflexivity. Qed.

Lemma env_fval_reify_correct_leapfrog_step_v:
  forall x v : ftype Tsingle,
  fval (leapfrog_env  x v) v' = leapfrog_stepv x v.
Proof. reflexivity. Qed.

Lemma env_n_fval_reify_correct_leapfrog_step_v:
  forall x v : ftype Tsingle,
  forall n : Z,
  fval (lf_env_n x v   n) v' = leapfrog_stepv x v.
Proof. reflexivity. Qed.

Lemma env_fval_reify_correct_leapfrog_step:
  forall x v : ftype Tsingle,
  fval (leapfrog_env x v) x' = leapfrog_stepx x v /\
  fval (leapfrog_env  x v) v' = leapfrog_stepv x v.
Proof. split; reflexivity. Qed.

Lemma env_n_fval_reify_correct_leapfrog_step:
  forall x v : ftype Tsingle,
  forall n : Z,
  fval (lf_env_n x v   n) x' = leapfrog_stepx x v /\
  fval (lf_env_n x v   n) v' = leapfrog_stepv x v.
Proof. split; reflexivity. Qed.

(* Don't need this, maybe? 

Lemma env_rval_reify_correct_leapfrog_stepx:
  forall x v : ftype Tsingle,
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
  x1 = B2R _ _ x ->
  v1 = B2R _ _ v -> 
  forall n : nat,
  rval (lf_env_n x v  n) (optimize_div x') = fst (leapfrog_stepR' (x1,v1)).
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
  x1 = B2R _ _ x ->
  v1 = B2R _ _ v -> 
  forall n : nat,
  rval (lf_env_n x v   n) (optimize_div v') = snd (leapfrog_stepR' (x1,v1)).
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
boundsmap_denote (lf_bmap_n   n)  (leapfrog_vmap x v) ->
lf_env_n x v   n  = env_ (leapfrog_vmap x v). 
Proof.
intros. pose proof (env_mk_env (lf_bmap_n   n)  (leapfrog_vmap x v) H). 
replace (env_ (leapfrog_vmap x v)) with 
  (mk_env (lf_bmap_n   n)  (leapfrog_vmap x v)). 
unfold lf_env_n, list_to_bound_env, mk_env, lf_bmap_n, leapfrog_vmap.
apply functional_extensionality_dep; intro ty.
apply functional_extensionality; intro i.
 destruct (Maps.PTree.get i (Maps.PTree_Properties.of_list 
    (lf_bmap_list_n   n))) as [[t i' lo hi]|],
    (Maps.PTree.get i (Maps.PTree_Properties.of_list (leapfrog_vmap_list x v))) 
    as [v'|]; try contradiction; auto.
Qed.

*)

Import Interval.Tactic.
Lemma prove_roundoff_bound_x:
  forall x v : ftype Tsingle,
  prove_roundoff_bound leapfrog_bmap (leapfrog_vmap x v) x' 
    (B2R _ _ 1.2290547968252271e-5%F64).
Proof.
intros.
prove_roundoff_bound.
- abstract (prove_rndval; interval).
- 
  prove_roundoff_bound2.
 compute_B2R.

 match goal with |- Rabs ?a <= _ => field_simplify a end. (* improves the bound *)
 match goal with |- Rabs ?a <= _ => interval_intro (Rabs a) end.
 (* Right now, just "lra" would solve the goal, but to see how to compactly
  represent the bound to the next-highest double-precision float, 
  this is the way: *)
 eapply Rle_trans; [apply H | clear].
 match goal with |- ?r <= _ => let x := float_nearest mode_UP r in
    apply Rle_trans with (B2R _ _ x)
 end.
 compute_B2R; lra.
 compute_B2R; lra.
Qed.

Lemma prove_roundoff_bound_v:
  forall x v : ftype Tsingle,
  prove_roundoff_bound leapfrog_bmap (leapfrog_vmap x v) v' 
    (B2R _ _ 6.5249424040849913e-6%F64).
Proof.
intros.
prove_roundoff_bound.
- abstract (prove_rndval; interval).
-
  prove_roundoff_bound2.
 compute_B2R.
 match goal with |- Rabs ?a <= _ => field_simplify a end.
 match goal with |- Rabs ?a <= _ => interval_intro (Rabs a) end.
 lra.
Qed.


Lemma prove_roundoff_bound_q:
  forall x v : ftype Tsingle,
  prove_roundoff_bound leapfrog_bmap (leapfrog_vmap x v) q' 
    (B2R _ _ 1.210137305900779e-5%F64).
Proof.
intros.
prove_roundoff_bound.
- abstract (prove_rndval; interval).
-
  prove_roundoff_bound2.
 compute_B2R.
 match goal with |- Rabs ?a <= _ => field_simplify a end.
 match goal with |- Rabs ?a <= _ => interval_intro (Rabs a) end.
 lra.
Qed.


Lemma prove_roundoff_bound_x_n:
  forall x v : ftype Tsingle,
  forall n: Z,
 (n <= 1000)%Z ->
  prove_roundoff_bound (lf_bmap_n n) (leapfrog_vmap x v) x' 
    (B2R _ _ 1.2302838516220536e-4%F64).
Proof.
intros.
 apply  prove_roundoff_bound_relax with (lf_bmap_n 1000).
-
 apply IZR_le in H.
 repeat apply Forall2_cons; try apply Forall2_nil; hnf; simpl; repeat split; 
 auto; lra.
-
 clear n H.
 prove_roundoff_bound.
 + abstract (prove_rndval; interval).
 +
  prove_roundoff_bound2.
 compute_B2R.
 match goal with |- Rabs ?a <= _ => field_simplify a end.
 match goal with |- Rabs ?a <= _ => interval_intro (Rabs a) end.
 lra.
Qed.

Lemma prove_roundoff_bound_v_n:
  forall x v : ftype Tsingle,
  forall n: Z,
 (n <= 1000)%Z ->
  prove_roundoff_bound (lf_bmap_n n) (leapfrog_vmap x v) v' 
    (B2R _ _ 6.5314673464890983e-5%F64).
Proof.
intros.
 apply  prove_roundoff_bound_relax with (lf_bmap_n 1000).
-
 apply IZR_le in H.
 repeat apply Forall2_cons; try apply Forall2_nil; hnf; simpl; repeat split; 
 auto; lra.
-
 clear n H.
 prove_roundoff_bound.
 + abstract (prove_rndval; interval).
 +
  prove_roundoff_bound2.
 compute_B2R.
 match goal with |- Rabs ?a <= _ => field_simplify a end.
 match goal with |- Rabs ?a <= _ => interval_intro (Rabs a) end.
 lra.
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

(*
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
(destruct (rndval_with_cond O (mempty  (Tsingle, Normal')) (optimize_div x')) 
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
(destruct (rndval_with_cond O (mempty  (Tsingle, Normal')) (optimize_div v')) 
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
  boundsmap_denote (lf_bmap_n  n) (leapfrog_vmap x v)->
  Binary.is_finite _ _(fval (lf_env_n x v   n) (optimize_div x')) = true.
Proof.
intros.
(destruct (rndval_with_cond O (mempty  (Tsingle, Normal')) (optimize_div x')) 
  as [[r [si2 s]] p] eqn:rndval).
pose proof (rndval_with_cond_correct_optx_n x v n H H0 r si2 s p rndval)
  as rndval_result. 
unfold rndval_with_cond_result in rndval_result;
set (Hty:= type_of_expr (optimize_div x')) in *.
repeat simpl in Hty.
cbv [Datatypes.id] in Hty.   
repeat change (type_lub Tsingle Tsingle) with Tsingle in Hty;
unfold Hty in *; clear Hty.
pose proof rndval_result (fval (lf_env_n x v  n) x') as RESULT_A ;
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
  boundsmap_denote (lf_bmap_n  n) (leapfrog_vmap x v)->
  Binary.is_finite _ _(fval (lf_env_n x v   n) (optimize_div v')) = true.
Proof.
intros.
(destruct (rndval_with_cond O (mempty  (Tsingle, Normal')) (optimize_div v')) 
  as [[r [si2 s]] p] eqn:rndval).
pose proof (rndval_with_cond_correct_optv_n x v n H  H0 r si2 s p rndval)
  as rndval_result. 
unfold rndval_with_cond_result in rndval_result;
set (Hty:= type_of_expr (optimize_div v')) in *.
repeat simpl in Hty.
cbv [Datatypes.id] in Hty.   
repeat change (type_lub Tsingle Tsingle) with Tsingle in Hty;
unfold Hty in *; clear Hty.
pose proof rndval_result (fval (lf_env_n x v   n) v') as RESULT_A ;
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
  boundsmap_denote (lf_bmap_n   n) (leapfrog_vmap x v)->
  Binary.is_nan _ _(fval (lf_env_n x v   n) x') = false.
Proof. 
intros; subst;
apply is_finite_not_is_nan.
eapply leapfrog_opt_stepx_is_finite_n; auto.
Qed.

Lemma leapfrog_stepv_not_nan_n:
forall x v : float32, 
  forall n : nat,
  (n <= 1000)%nat ->
  boundsmap_denote (lf_bmap_n   n) (leapfrog_vmap x v)->
  Binary.is_nan _ _(fval (lf_env_n x v   n) v') = false.
Proof. 
intros; subst;
apply is_finite_not_is_nan.
eapply leapfrog_opt_stepv_is_finite_n; auto.
Qed.
*)

End WITHNANS.