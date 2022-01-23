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

Import FPLangOpt. 
Import FPLang.
Import FPSolve.
Import Test.


Definition x' := ltac:(let e' := 
  HO_reify_float_expr constr:([_x; _v]) leapfrog_stepx in exact e').
Definition v' := ltac:(let e' := 
  HO_reify_float_expr constr:([_x; _v]) leapfrog_stepv in exact e').


Definition leapfrog_bmap_list := 
  [(_v, {|Test.var_type:=Tsingle; Test.var_name:=_v; Test.var_lobound:=-1; Test.var_hibound:=1|});
  (_x,{|Test.var_type:=Tsingle; Test.var_name:=_x; Test.var_lobound:=-1; Test.var_hibound:=1|})].
Definition leapfrog_vmap_list (x v : float32) := [(_x, Values.Vsingle x);(_v, Values.Vsingle v)].
Definition leapfrog_env  := (fun x v => list_to_bound_env leapfrog_bmap_list (leapfrog_vmap_list x v)). 
Definition leapfrog_bmap :=  Maps.PTree_Properties.of_list leapfrog_bmap_list.
Definition leapfrog_vmap (x v : float32) := Maps.PTree_Properties.of_list (leapfrog_vmap_list x v).

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


Lemma env_fval_reify_correct_leapfrog_step_v:
  forall x v : float32,
  fval (leapfrog_env  x v) v' = leapfrog_stepv x v.
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


Lemma env_rval_reify_correct_leapfrog_stepx:
  forall x v : float32,
  forall x1 v1 : R,
  x1 = B2R _ _ x ->
  v1 = B2R _ _ v -> 
  rval (leapfrog_env x v) (optimize_div x') = fst (leapfrog_stepR (x1,v1)).
Proof.
intros.
unfold leapfrog_env.
simplify_shift_div_opt (optimize_div x').
match goal with |- context [rval ?env ?e] =>
  unfold_reflect_rval e; cbv [id]
end.
unfold leapfrog_stepR, F, h, fst, snd; subst.
replace (B2R (fprec Tsingle) (femax Tsingle) x) with (B2R 24 128 x) by auto.
replace (B2R (fprec Tsingle) (femax Tsingle) v) with (B2R 24 128 v) by auto.
all: repeat f_equal; simpl; unfold Defs.F2R; simpl; nra.
Qed.

Lemma env_rval_reify_correct_leapfrog_stepv:
  forall x v : float32,
  forall x1 v1 : R,
  x1 = B2R _ _ x ->
  v1 = B2R _ _ v -> 
  rval (leapfrog_env x v) (optimize_div v') = snd (leapfrog_stepR (x1,v1)).
Proof.
intros.
unfold leapfrog_env.
simplify_shift_div_opt (optimize_div v').
match goal with |- context [rval ?env ?e] =>
  unfold_reflect_rval e; cbv [id]
end.
simpl; rewrite ?Z.pow_pos_fold. 
unfold leapfrog_stepR, F, h, fst; subst.  
replace (B2R (fprec Tsingle) (femax Tsingle) x) with (B2R 24 128 x) by auto.
replace (B2R (fprec Tsingle) (femax Tsingle) v) with (B2R 24 128 v) by auto.
all: repeat f_equal; simpl; unfold Defs.F2R; simpl; nra.
Qed.


Require Import Coq.Logic.FunctionalExtensionality.

Lemma lf_env_eq: 
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


Ltac intro_absolute_error_bound ty kn bmd x v rndval_result:=
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
rewrite ?lf_env_eq in RESULT_A; auto;
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
try (rewrite ?lf_env_eq; auto; rewrite <- ERRORS; clear ERRORS);
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
lf_rewrites;
match goal with |- context [Rabs (?v) <= _] =>
  field_simplify v;
repeat (try split; try interval)
end;
match goal with |- context [Rabs (?v) <= _] =>
  interval_intro (Rabs v) upper
end;
try nra 
end.


(* lemma for energy error, for difference of squares on v *)
Lemma one_step_sum_v:
  forall x v : float32,
    boundsmap_denote leapfrog_bmap (leapfrog_vmap x v)->
    Rle (Rabs (Rplus (rval (leapfrog_env x v)  (optimize_div v')) 
    (B2R _ _ (fval (leapfrog_env x v) (optimize_div v'))))) 
         (4646570650113373 / 2251799813685248)%R.
Proof.
intros.
(destruct (rndval_with_cond O (mempty  (Tsingle, Normal)) (optimize_div v')) 
  as [[r [si2 s]] p] eqn:rndval).
pose proof (rndval_with_cond_correct_optv x v H r si2 s p rndval)
  as rndval_result. 
intro_absolute_error_bound Tsingle Normal H x v rndval_result.
Qed.


(* lemma for energy error, for difference of squares on x *)
Lemma one_step_sum_x:
  forall x v : float32,
    boundsmap_denote (leapfrog_bmap ) (leapfrog_vmap x v)->
    Rle (Rabs (Rplus (rval (leapfrog_env  x v) (optimize_div x')) 
   (B2R _ _ (fval (leapfrog_env  x v) (optimize_div x'))))) 
         (4646536420130942 / 2251799813685248)%R.
Proof.
intros.
(destruct (rndval_with_cond O (mempty  (Tsingle, Normal)) (optimize_div x')) 
  as [[r [si2 s]] p] eqn:rndval).
pose proof (rndval_with_cond_correct_optx x v H r si2 s p rndval)
  as rndval_result.
intro_absolute_error_bound Tsingle Normal H x v rndval_result.
Qed.

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

