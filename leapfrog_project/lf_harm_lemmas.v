From Flocq Require Import Binary Bits Core.
From compcert.lib Require Import IEEE754_extra Coqlib Floats Zbits Integers.
Require Import float_lib lf_harm_float lf_harm_real vcfloat.

Local Transparent Float32.of_bits.
Local Transparent Float32.div.
Local Transparent Float32.neg.
Local Transparent Float32.mul.
Local Transparent Float32.add.
Local Transparent Float32.sub.

Definition initial_x : float32 := 1.
Definition initial_v : float32 := 0.
Definition initial_t : float32 := 0.

Definition half := Float32.div 1 2.

Lemma half_repr : Float32.of_bits (Int.repr 1056964608) =  half.
Proof. prove_float_constants_equal. Qed.

Lemma neg1_repr: 
  Float32.neg (Float32.of_bits (Int.repr 1065353216)) = - (1).
Proof.  prove_float_constants_equal. Qed.

Lemma exact_inverse_two: Float32.exact_inverse 2 = Some half.
Proof.  prove_float_constants_equal. Qed.

Lemma leapfrog_step_is_finite:
  forall n, 0 <= n < 100 ->
          Binary.is_finite 24 128 (fst (Z.iter n leapfrog_step (initial_x, initial_v))) = true.
Admitted.

Definition leapfrog_stepx x v := fst (leapfrog_step (x,v)).
Definition leapfrog_stepv x v := snd (leapfrog_step (x,v)).

Import ListNotations.
Definition _x : AST.ident := 1121%positive.
Definition _v : AST.ident := 1117%positive.

Import FPLangOpt. 
Import FPLang.

Definition e :=  ltac:(let e' := reify_float_expr constr:((float32_of_Z 1 / float32_of_Z 32)%F32 ) in exact e').
Definition e1 := ltac:(let e' := HO_reify_float_expr constr:([_x; _v]) leapfrog_stepx in exact e').
Definition e2 := ltac:(let e' := HO_reify_float_expr constr:([_x; _v]) leapfrog_stepv in exact e').


Definition list_to_bound_env (bindings: list  (AST.ident * Test.varinfo)) (bindings2: list  (AST.ident * Values.val)) : (forall ty : type, AST.ident -> ftype ty) .
pose (bm := Maps.PTree_Properties.of_list bindings).
pose (vm := Maps.PTree_Properties.of_list bindings2). 
intros ty i.
destruct (Maps.PTree.get i bm) as [[t i' lo hi]|] eqn:?H.
destruct (type_eq_dec ty t).
subst.
destruct (Maps.PTree.get i vm).
destruct (type_eq_dec (Test.ftype_of_val v) t).
subst.
apply (Test.fval_of_val v).
apply (B754_zero (fprec t) (femax t) true).
apply (B754_zero (fprec t) (femax t) true).
apply (B754_zero (fprec ty) (femax ty) true).
apply (B754_zero (fprec ty) (femax ty) true).
Defined.

Ltac unfold_reflect' E := 
match goal with |- context [fval (list_to_bound_env ?L1 ?L2) E] =>
 pattern (fval (list_to_bound_env L1 L2) E);
 let HIDE := fresh "HIDE" in match goal with |- ?A _ => set (HIDE:=A) end;
 let m := fresh "m" in let m' := fresh "m'" in
 set (m := list_to_bound_env L1 L2);
 hnf in m;
 set (m1 := (Maps.PTree_Properties.of_list L1)) in m;
 hnf in m1; simpl in m1;
 set (m2 := (Maps.PTree_Properties.of_list L2)) in m;
 hnf in m2; simpl in m2;
 let e' := eval hnf in E in change E with e';
 cbv [fval type_of_expr type_of_unop Datatypes.id];
 repeat change (type_lub _ _) with Tsingle;
 repeat change (type_lub _ _) with Tdouble;
 repeat change (cast_lub_l Tsingle Tsingle ?x) with x;
 repeat change (cast_lub_r Tsingle Tsingle ?x) with x;
 repeat change (cast_lub_l Tdouble Tdouble ?x) with x;
 repeat change (cast_lub_r Tdouble Tdouble ?x) with x;
 cbv [fop_of_unop fop_of_exact_unop fop_of_binop fop_of_rounded_binop];
 change (cast _ _ ?a) with a;
 change (BOPP Tsingle) with Float32.neg;
 change (BPLUS Tsingle) with Float32.add;
 change (BMULT Tsingle) with Float32.mul;
 change (BDIV Tsingle) with Float32.div;
 repeat match goal with |- context [m ?t ?i] =>
             let u := fresh "u" in set (u := m t i); hnf in u; subst u
 end;
 subst m1 m2 m; 
 subst HIDE; cbv beta
end.


Definition leapfrog_bmap_list := 
  [(_v, {|Test.var_type:=Tsingle; Test.var_name:=_v; Test.var_lobound:=-1; Test.var_hibound:=1|});
  (_x,{|Test.var_type:=Tsingle; Test.var_name:=_x; Test.var_lobound:=-1; Test.var_hibound:=1|})].
Definition leapfrog_vmap_list (x v : float32) := [(_x, Values.Vsingle x);(_v, Values.Vsingle v)].
Definition leapfrog_env  := (fun x v => list_to_bound_env leapfrog_bmap_list (leapfrog_vmap_list x v)). 
Definition leapfrog_bmap :=  Maps.PTree_Properties.of_list leapfrog_bmap_list.
Definition leapfrog_vmap (x v : float32) := Maps.PTree_Properties.of_list (leapfrog_vmap_list x v).

Lemma env_fval_reify_correct_leapfrog_step:
  forall x v : float32,
  fval (leapfrog_env x v) e1 = leapfrog_stepx x v /\
  fval (leapfrog_env x v) e2 = leapfrog_stepv x v.
Proof.
intros. 
set (e1':= e1); unfold e1 in e1'; compute in e1'; fold Tsingle in e1'; fold _x in e1'; fold _v in e1'.
set (e2':= e2); unfold e2 in e2'; compute in e2'; fold Tsingle in e2'; fold _x in e2'; fold _v in e2'.
unfold leapfrog_env; split.
{ unfold_reflect' e1'.
unfold leapfrog_stepx, leapfrog_step, fst, snd, 
lf_harm_float.F, lf_harm_float.h, lf_harm_float.half.
replace (Float32.div  1%Z  32%Z) with (B2 Tsingle (- (5))) by
(apply binary_float_eqb_eq; auto). 
replace (Float32.div  1%Z  2%Z) with (B2 Tsingle (- (1))) by
(apply binary_float_eqb_eq; auto). 
Search "B2".

x + B2 Tsingle (- (5)) * v + B2 Tsingle (- (11)) * - x

replace (lf_harm_float.h * lf_harm_float.h * (- 1%Z * x) *
 lf_harm_float.half) with
((lf_harm_float.half * lf_harm_float.h * lf_harm_float.h * (- 1%Z * x))%F32) by
auto.
all: try reflexivity. 
Admitted.

Lemma reify_correct_leapfrog_step:
  forall x v : float32,
  fval (list_to_env [(_x, Values.Vsingle x);(_v, Values.Vsingle v)]) e1 = leapfrog_stepx x v /\
  fval (list_to_env [(_x, Values.Vsingle x);(_v, Values.Vsingle v)]) e2 = leapfrog_stepv x v.
Proof.
intros.
unfold_reflect e1.
unfold_reflect e2.
split.
all: try reflexivity.
Admitted.

Ltac unfold_reflect_rval E := 
match goal with |- context [rval (list_to_bound_env ?L1 ?L2) E] =>
 pattern (rval (list_to_bound_env L1 L2) E);
 let HIDE := fresh "HIDE" in match goal with |- ?A _ => set (HIDE:=A) end;
 let m := fresh "m" in let m' := fresh "m'" in
 set (m := list_to_bound_env L1 L2);
 hnf in m;
 set (m1 := (Maps.PTree_Properties.of_list L1)) in m;
 hnf in m1; simpl in m1;
 set (m2 := (Maps.PTree_Properties.of_list L2)) in m;
 hnf in m2; simpl in m2;
 let e' := eval hnf in E in change E with e';
 cbv [rval];
 cbv [Rop_of_unop Rop_of_exact_unop Rop_of_binop Rop_of_rounded_binop];
 change (BOPP Tsingle) with Float32.neg;
 change (BPLUS Tsingle) with Float32.add;
 change (BMULT Tsingle) with Float32.mul;
 change (BDIV Tsingle) with Float32.div;
 repeat match goal with |- context [m ?t ?i] =>
             let u := fresh "u" in set (u := m t i); hnf in u; subst u
 end;
 subst m1 m2 m; 
 subst HIDE; cbv beta
end.

(*Lemma env_rval_reify_correct_leapfrog_step:
  forall x v : float32,
  forall x1 v1 : R,
  x1 = B2R _ _ x ->
  v1 = B2R _ _ v -> 
  rval (leapfrog_env x v) e1 = fst (leapfrog_stepR (x1,v1)) /\
  rval (leapfrog_env x v) e2 = snd (leapfrog_stepR (x1,v1)).
Proof.
intros.
unfold leapfrog_env.
unfold_reflect_rval e1.
unfold_reflect_rval e2.
simpl. cbv [Defs.F2R FLT_exp]; simpl. rewrite ?Z.pow_pos_fold. 
unfold leapfrog_stepR, F, h, fst; subst. 
replace (B2R (fprec Tsingle) 128 x) with (B2R 24 128 x) by auto.
replace (B2R (fprec Tsingle) 128 v) with (B2R 24 128 v) by auto.
all: try nra. 
Admitted. *)


Lemma finite_env (bmap: boundsmap) (vmap: valmap):
      boundsmap_denote bmap vmap ->
forall ty i, is_finite (fprec ty) (femax ty) ((env_ vmap) ty i) = true.
Proof. 
intros.
 unfold  env_.
 specialize (H i).
 destruct (Maps.PTree.get i bmap) as [[t i' lo hi]|],
    (Maps.PTree.get i vmap) as [v|]; auto.
 destruct H as [x [_ [? [? ?]]]].
 destruct v; simpl in *; auto.
 assert (t=Tdouble) by (inversion H; subst; auto). subst.
 assert (f=x) by (inversion H; clear H; subst; apply Eqdep.EqdepTheory.inj_pair2 in H4; subst; auto).
 subst.
 destruct (type_eq_dec ty Tdouble); [ | reflexivity].
 subst; auto.
 assert (t=Tsingle) by (inversion H; subst; auto). subst.
 assert (f=x) by (inversion H; clear H; subst; apply Eqdep.EqdepTheory.inj_pair2 in H4; subst; auto).
 subst.
 destruct (type_eq_dec ty Tsingle); [ | reflexivity].
 subst; auto.
Qed.

Ltac rndval_replace ex :=
  match goal with 
    H0: (rndval_with_cond 0 (mempty (Tsingle, Normal)) ex = (?r, (?si, ?s), ?p)) |- _ =>
      let m := fresh "m" in set (m:=rndval_with_cond 0 (mempty (Tsingle, Normal)) ex) in H0; 
      let H:= fresh  in 
      let H1:= fresh  in 
      let H2:= fresh  in 
      let H3:= fresh  in 
      assert (r = fst (fst (m))) as H by ( 
        replace m with (r, (si, s), p) by auto; auto);
      assert (si = fst (snd (fst (m)))) as H1 by (
        replace m with (r, (si, s), p) by auto; auto);
      assert (s = snd (snd (fst (m)))) as H2 by (
        replace m with (r, (si, s), p) by auto; auto);
      assert (p =  snd (m)) as H3 by (
        replace m with (r, (si, s), p) by auto; auto);
      compute in H, H1 ,H2 ,H3
end.

Import Interval.Tactic.

Ltac solve_one_eval_cond2_vmap := 
match goal with |- eval_cond2 (mk_env ?bmap ?vmap) _ _ =>
 hnf;
 repeat
 (match goal with |- context [@mget _ _ _ _ _ _]  =>
       let x := fresh "x" in set (x := @mget _ _ _ _ _ _); compute in x; subst x
   end;
 cbv beta iota;
 fold Tsingle; fold Tdouble);
 repeat 
  (let H := fresh in intros ? H;
   simpl in H; cbv beta iota delta [error_bound Tsingle Tdouble fprec] in H;
   simpl in H);
 match goal with |- context [reval _ _ (mget ?M)] =>
   let m := fresh "m" in set (m:=M); compute in m;
    unfold reval;
    repeat match goal with |- context [@mget _ _ _ ?MAP m ?i]  =>
       let x := fresh "x" in set (x := @mget _ _ _ MAP m i); compute in x; subst x
   end;
   clear m
  end;
 simpl;
 rewrite ?Pos2Z.inj_pow_pos, ? IZR_Zpower_pos in *;
  rewrite ?power_RZ_inv  in * by lra;
   rewrite <- ?powerRZ_add in * by lra;
   simpl Z.add ;
repeat
  match goal with |- context [mk_env bmap ?vmap ?ty ?v'] =>
       match goal with H: Maps.PTree.get ?v vmap = _ |- _ =>
         change (mk_env bmap vmap ty v') with (mk_env bmap vmap ty v);
         let x := fresh "x" in set (x := mk_env _ vmap _ v); 
         hnf in x;
             compute in x; subst x; 
         try (cbv in H; inversion H; clear H; subst)
  end end; 
 repeat change (B2R (fprec ?x) _) with (FT2R x);
 try apply lesseq_less_or_eq;
 rewrite ?Rmult_1_l;
 try interval
end.

Ltac leapfrog_conds2_hold ex:=
  match goal with 
    H0: boundsmap_denote ?bmap ?vmap 
      |- _ =>
      apply boundsmap_denote_e in H0;
      rewrite ?list_forall_Forall in *;
      rewrite list_forall_Forall in H0;
      rndval_replace ex; subst;
      prepare_assumptions_about_free_variables;

match goal with |- List.Forall (eval_cond2 _ ?M) _ =>
   let m := fresh "m" in set (m:=M); compute in m; subst m;
  fold Tsingle; fold Tdouble
end;
repeat
    match goal with |- context [ type_lub ?a ?b ] =>
     first [change (type_lub a b) with Tsingle 
            |change (type_lub a b) with Tdouble]
    end;
repeat (apply List.Forall_cons; try apply List.Forall_nil;
try solve_one_eval_cond2_vmap)
end.

Lemma leapfrogx_cond2_holds:
  forall x v : float32,
    boundsmap_denote leapfrog_bmap (leapfrog_vmap x v)->
   forall r0 si2_0 s0 p0 , 
      rndval_with_cond 0 (mempty (Tsingle, Normal)) e1 =
         (r0, (si2_0, s0), p0) ->
      list_forall (eval_cond2 (mk_env leapfrog_bmap (leapfrog_vmap x v)) s0) p0.
Proof.
intros.
leapfrog_conds2_hold e1.
Qed. 

Lemma leapfrogv_cond2_holds:
  forall x v : float32,
    boundsmap_denote leapfrog_bmap (leapfrog_vmap x v)->
   forall r0 si2_0 s0 p0 , 
      rndval_with_cond 0 (mempty (Tsingle, Normal)) e2 =
         (r0, (si2_0, s0), p0) ->
      list_forall (eval_cond2 (mk_env leapfrog_bmap (leapfrog_vmap x v)) s0) p0.
Proof.
intros.
leapfrog_conds2_hold e2.
Qed. 

Ltac leapfrog_conds1_hold ex:=
  match goal with
    H0: boundsmap_denote ?bmap ?vmap 
    |- forall i : cond, List.In i ?p -> eval_cond1 (env_ ?vmap) ?s i =>
assert (list_forall (eval_cond2 (mk_env bmap vmap) s) p) by (leapfrog_conds2_hold ex);
replace (mk_env bmap vmap) with (env_ vmap) in * by (apply env_mk_env; auto);
apply list_forall_spec;
apply (list_forall_ext (eval_cond2 (env_ vmap) s)); auto;
    apply eval_cond2_correct
end.

Lemma leapfrogx_cond1_holds:
  forall x v : float32,
    boundsmap_denote leapfrog_bmap (leapfrog_vmap x v)->
   forall r si2 s p, 
      rndval_with_cond 0 (mempty (Tsingle, Normal)) e1 =
         (r, (si2, s), p) ->
    forall i : cond, List.In i p -> eval_cond1 (env_ (leapfrog_vmap x v)) s i.
Proof.
intros ? ? ? ? ? ? ? ?. 
leapfrog_conds1_hold e1. 
Qed.

Ltac get_rndval_with_cond_correct ex:=
match goal with
    H: boundsmap_denote ?bmap ?vmap |- _ => 
let HFIN:= fresh in (
assert (forall ty i, is_finite (fprec ty) (femax ty) ((env_ vmap) ty i) = true) as HFIN by
 (apply (finite_env bmap vmap H))
);
(destruct (rndval_with_cond O (mempty  (Tsingle, Normal)) ex) as [[r [si2 s]] p] eqn:rndval);
let lc2:= fresh in ( 
assert (list_forall (eval_cond2 (mk_env bmap vmap) s) p ) as lc2 by
(leapfrog_conds2_hold ex)
);
let HVALID:= fresh in ( 
assert (expr_valid ex = true) as HVALID by reflexivity
);
replace (mk_env bmap vmap) with (env_ vmap) in lc2 by (apply env_mk_env; auto);
let listconds:= fresh in (
assert (forall i : cond, List.In i p -> eval_cond1 (env_ vmap) s i) as listconds by
(leapfrog_conds1_hold ex)
);
(destruct (rndval_with_cond_correct
                          _ HFIN _ HVALID _ _ _ _ rndval lc2 _ (eq_refl _)) as [] eqn:correct); 
clear correct HFIN HVALID listconds
end.

Lemma powerRZ_pos_sub2: 
forall (x : R) (n m : positive),
     x <> 0 ->
     x ^ Pos.to_nat n * / x ^ Pos.to_nat m = powerRZ x (Z.pos_sub n m).
Proof. 
intros; symmetry; apply powerRZ_pos_sub; auto. Qed.


Lemma neg_powerRZ (x:R) (n:Z) :
  x <> R0 -> 
  1 / (powerRZ x%R n%Z) = (powerRZ x%R (-n)%Z) .
Proof.
intros; pose proof power_RZ_inv x n H; symmetry; rewrite <- H0; nra. 
Qed.


Ltac get_eps_delts := 
match goal with 
  H0: enum_exists 0
       _ _ _|- _ =>
hnf in H0; 
repeat (let B := fresh "B" in destruct H0 as [?ed [B H0]]; simpl in B; 
match type of B with context [error_bound _ ?a] => 
  match a with 
    |Normal   => (let d:= fresh "del" in (rename ed into d)) 
    |Denormal => (let e:= fresh "eps" in (rename ed into e))
  end
end; unfold error_bound in B;
  rewrite ?type_lub_id; simpl in B; 
  rewrite ?IZR_Zpower_pos in B; 
  rewrite ?neg_powerRZ
)
end.


Ltac get_rexp_with_eps_delt e :=
match goal with 
  H0: rndval_with_cond 0 (mempty (Tsingle, Normal)) ?e =  
  (?r, (?si2, ?s), ?p) |- _ =>
  rndval_replace e;
  subst si2 s r;
  get_eps_delts

end.

Require Import Coq.Logic.FunctionalExtensionality.

Lemma lf_env_eq: 
  forall x v : float32,
boundsmap_denote leapfrog_bmap (leapfrog_vmap x v) ->
leapfrog_env x v = env_ (leapfrog_vmap x v).
Proof.
intros. pose proof (env_mk_env leapfrog_bmap (leapfrog_vmap x v) H). 
replace (env_ (leapfrog_vmap x v)) with (mk_env leapfrog_bmap (leapfrog_vmap x v)). 
unfold leapfrog_env, list_to_bound_env, mk_env, leapfrog_bmap, leapfrog_vmap.
apply functional_extensionality_dep; intro ty.
apply functional_extensionality; intro i.
 destruct (Maps.PTree.get i (Maps.PTree_Properties.of_list leapfrog_bmap_list)) as [[t i' lo hi]|],
    (Maps.PTree.get i (Maps.PTree_Properties.of_list (leapfrog_vmap_list x v))) as [v'|]; try contradiction; auto.
Qed.


Ltac fv_prepare_assumptions :=
match goal with
  H: boundsmap_denote (?bmap) (?vmap)
  |- _
  => 
apply boundsmap_denote_e in H;
rewrite list_forall_Forall in H;
repeat
 (let j := fresh "j" in let t := fresh "t" in let i' := fresh "i'" in 
  let lo := fresh "lo" in let hi := fresh "hi" in let yy := fresh "yy" in 
 let v := fresh "v" in 
 let x := fresh "x" in let U := fresh "U" in let W := fresh "W" in
 let Hx := fresh "Hx" in let Hj := fresh "Hj" in let Ht := fresh "Ht"  in
 let Hi := fresh "Hi" in  
inversion H as [ | [j [t i' lo hi]] yy [v [x [U W]]] Hx [Hj Ht Hi]];
 clear H; rename Hx into H;
 rewrite U in *; clear U;
subst j t lo hi yy;
 match type of Hi with _ = ?i =>
  let valx := fresh "val" i in 
  let Hval := fresh "Hval" i in
  let Hinj := fresh "Hinj" i in
  let Hfin := fresh "Hfin" i in
  let Hrange := fresh "Hrange" i in
  rename x into valx;
  destruct W as [Hval [Hinj [Hfin Hrange]]];
 first [apply val_inject_single_inv_r in Hinj
       | apply val_inject_double_inv_r in Hinj
       | fail 88 "val_inject_inv failed" ];
  subst v i'
 end)
 end.

Lemma Rminus_dist: 
  forall x y z : R,
  x - (y +z) = x - y - z.
Proof.
intros;nra.
Qed.

Ltac reduce_abs_error:=
match goal with |- context [reval _ _ (mget (mset (?M) _ _))] => 
     let m := fresh "m" in set (m:=M); compute in m; unfold reval;
simpl rval;
  repeat (
    match goal with |- context [{| Fnum := ?n; Fexp := _ |}] =>
      change n with (Z.pow_pos (2%Z) (Z.to_pos ((Z.log2 n%Z)%Z) ));
      let x:= fresh "x" in set (x:= Z.log2 _); simpl in x; subst x; try reflexivity;
      repeat (
      let x:= fresh "x" in set (x:= FLT_exp _ _ _); unfold FLT_exp in x; unfold Z.max in x; 
simpl in x; subst x
            )
    end );
      rewrite ?(mget_set Nat.eq_dec m);
      cbv [reval Prog.binary Prog.real_operations Tree.binary_real 
      Prog.unary Prog.binary Tree.unary_real ];
      repeat (
        match goal with |- context [mget m ?i] =>
          let x:= fresh "x" in set (x:= mget m i); hnf in x; subst x 
        end  );
      repeat (
        match goal with |- context [if Nat.eq_dec _ _ then _ else _] =>
          let x:= fresh "x" in set (x:= if Nat.eq_dec _ _ then _ else _); hnf in x; subst x 
        end  );
cbv [F2R Defs.F2R fone bpow radix_val radix2 Fexp Fnum];
rewrite ?Zpower_pos_powerRZ; unfold powerRZ; 
      rewrite ?powerRZ_pos_sub2; rewrite ?neg_powerRZ;
      rewrite ?Rmult_1_l;
      rewrite ?Rmult_1_r;
      rewrite ?powerRZ_O; try lra;
      repeat (
        match goal with |- context [(Z.pos_sub (Z.to_pos _) _)] =>
          let x:= fresh "x" in set (x:= (Z.pos_sub (Z.to_pos _) _)%Z); 
simpl in x; subst x 
        end);
fold Tsingle;
      repeat (
        match goal with |- context [(env_ _ Tsingle _)] =>
          let x:= fresh "x" in set (x:= (env_ _ Tsingle _)); 
hnf in x; subst x 
        end);
clear m;
unfold FT2R in *;
repeat(
match goal with | [H': Maps.PTree.get _ _ = _ |- _] => 
cbv in H'; inversion H'; subst; auto
end)
end.

Lemma one_step_errorx:
  forall x v : float32,
    boundsmap_denote leapfrog_bmap (leapfrog_vmap x v)->
    Rle (Rabs (Rminus (rval (leapfrog_env x v) e1) (B2R _ _ (fval (leapfrog_env x v) e1)))) 
         (4719104053608481 / 37778931862957161709568)%R.
Proof.
intros.
set (bmap:= leapfrog_bmap) in *.
hnf in bmap. simpl in bmap.
get_rndval_with_cond_correct e1.
(* Populate hyps with some bounds on x and v*)
fv_prepare_assumptions.
(* turn rndval rexp to flt with eps delt *)
rndval_replace e1; 
subst si2 s r;
get_eps_delts.
pattern (B2R (fprec (type_of_expr e1)) (femax (type_of_expr e1))
     (fval (leapfrog_env x v) e1));  try rewrite <- e3.
clear H1 e0 H4 H;
reduce_abs_error. 
clear rndval p m e3.
replace (leapfrog_env val_x val_v Tsingle lf_harm_lemmas._x) with val_x in * by 
(cbv in Hval_x;inversion Hval_x; clear Hval_x; subst; auto).
replace (leapfrog_env val_x val_v Tsingle lf_harm_lemmas._v) with val_v in * by 
(cbv in Hval_v;inversion Hval_v; clear Hval_v; subst; auto).
replace (B2R (fprec Tsingle) (femax Tsingle) val_v) with
(B2R (fprec Tsingle) 128 val_v) in * by auto.
replace (B2R (fprec Tsingle) (femax Tsingle) val_x) with
(B2R (fprec Tsingle) 128 val_x) in * by auto.
try (
 repeat(
    match goal with |- context [?a * (?b + ?c)] =>
    rewrite ?Rmult_plus_distr_l; rewrite ?Rmult_plus_distr_r
end
      ) ; rewrite ?Rmult_1_r
). 
    match goal with |- context [Rabs (?a + ?b + ?c -(?v)) <= _] =>
field_simplify (a + b + c - (v))
 end
.
    match goal with |- context [Rabs (?v) <= _] =>
interval_intro (Rabs v)
 end
;
nra.
(* oddly, the following doesn't work but above two lines do
interval with (i_bisect (B2R (fprec Tsingle) 128 val_x), i_bisect (B2R (fprec Tsingle) 128 val_v)).
*)
Qed.

Lemma local_errorx:
  forall x v : float32,
  forall x1 v1 : R,
  boundsmap_denote leapfrog_bmap (leapfrog_vmap x v)->
  x1 = B2R _ _ x ->
  v1 = B2R _ _ v -> 
    Rle (Rabs (Rminus (fst(leapfrog_stepR (x1,v1))) (B2R _ _ (leapfrog_stepx x v)))) (/ powerRZ 2 12)%R.
Proof.
intros.
replace (fst (leapfrog_stepR (x1,v1))) with (rval (leapfrog_env x v) e1).
replace (leapfrog_stepx x v) with ((fval (leapfrog_env x v) e1)).
pose proof one_step_errorx x v H; auto. 
pose proof env_fval_reify_correct_leapfrog_step x v; auto.
pose proof env_rval_reify_correct_leapfrog_step x v x1 v1 H0 H1; destruct H2; auto.
Qed.

(*velocity error between R and F functions over one step of integration*)
Lemma one_step_errorv:
  forall x v : float32,
    boundsmap_denote leapfrog_bmap (leapfrog_vmap x v)->
    Rle (Rabs (Rminus (rval (leapfrog_env x v) e2) (B2R _ _ (fval (leapfrog_env x v) e1)))) 
         (/ powerRZ 2 12)%R.
Proof.
intros.
set (bmap:= leapfrog_bmap) in *.
hnf in bmap. simpl in bmap.
get_rndval_with_cond_correct e2.
(* Populate hyps with some bounds on x and v*)
fv_prepare_assumptions.
Admitted.

Lemma local_errorv:
  forall x v : float32,
  forall x1 v1 : R,
  boundsmap_denote leapfrog_bmap (leapfrog_vmap x v)->
  x1 = B2R _ _ x ->
  v1 = B2R _ _ v -> 
    Rle (Rabs (Rminus (snd(leapfrog_stepR (x1,v1))) (B2R _ _ (leapfrog_stepv x v)))) (/ powerRZ 2 12)%R.
Proof.
intros.
replace (snd (leapfrog_stepR (x1,v1))) with (rval (leapfrog_env x v) e1).
replace (leapfrog_stepx x v) with ((fval (leapfrog_env x v) e1)).
pose proof one_step_errorx x v H; auto. 
pose proof env_fval_reify_correct_leapfrog_step x v; auto.
pose proof env_rval_reify_correct_leapfrog_step x v x1 v1; auto.
Admitted.

Definition iternf  (n:nat) (x v :float32) :=  leapfrog (x%F32, v%F32) n.
Definition iternfR (n:nat) (x v :R) :=  leapfrogR (x,v) n .

Lemma abs_lt:
 forall a b d: R,
 Rabs b <= d ->
 Rabs a - d <= Rabs a - Rabs b.
Proof.
intros; nra. 
Qed. 

Lemma abs_mul:
 forall a b: R,
 0 <= a ->
 Rabs (a * b) = a * Rabs b.
Proof.
intros; pose proof Rabs_mult a b. rewrite -> H0. pose proof Rabs_pos_eq a H; auto; nra.  
Qed. 

Lemma rabs_mul_t:
forall u a b c d: R ,
u <= a * Rabs(b) + c -> Rabs(b) <= d -> 0 <a -> u <= a * d + c.
Proof.
intros. nra.
Qed.

Lemma global_error2:
 (forall x v : float32, 
  forall x1 v1 : R,
  boundsmap_denote leapfrog_bmap (leapfrog_vmap x v)->
  x1 = B2R _ _ x ->
  v1 = B2R _ _ v -> 
  forall n: nat, 
  INR n <= 1/lf_harm_real.h -> 
( Rle (Rabs (Rminus (fst(iternfR n x1%R v1%R)) (B2R _ _ (fst(iternf n x%F32 v%F32))))) (2 *lf_harm_real.h* (INR n))%R /\
  Rle (Rabs (Rminus (snd(iternfR n x1%R v1%R)) (B2R _ _ (snd(iternf n x%F32 v%F32))))) (2 *lf_harm_real.h* (INR n))%R )
).
Proof.
intros. induction n. 
-unfold iternf ,iternfR ,INR, leapfrog, leapfrogR, 
leapfrog_stepx,lf_harm_real.h in *;
replace (powerRZ (/ powerRZ 2 12 + 1) (Z.of_nat 0)) with 1 by auto; 
replace (/ powerRZ 2 12 *0) with  (0) by nra; auto; subst; unfold fst; unfold snd;
replace (B2R 24 128 x - B2R 24 128 x) with 0 by nra;
replace (B2R 24 128 v - B2R 24 128 v) with 0 by nra;
split. all: try interval.
- replace (INR (S n)) with (INR n + 1) in H2 by (rewrite ?S_INR; auto);
assert (INR n <= 1 / lf_harm_real.h) by nra. pose proof IHn H3; clear H3 IHn.
unfold iternfR, iternf in *; rewrite lfn_eq_lfstep. 
set (LFfn:= (leapfrog (x, v) n)) in *.
set (xnf:= fst LFfn) in *. 
set (vnf:=snd LFfn) in *. 
set (xnr:= B2R _ _ xnf ) in *. 
set (vnr:= B2R _ _ vnf) in *. 
assert (xnr = B2R 24 128 xnf) by auto.
assert (vnr = B2R 24 128 vnf) by auto.
assert (boundsmap_denote leapfrog_bmap (leapfrog_vmap xnf vnf)) by admit.
pose proof (local_errorx xnf vnf xnr vnr H6 H3 H5).
pose proof (local_errorv xnf vnf xnr vnr H6 H3 H5).
unfold leapfrog_stepx in *. 
assert ((xnf, vnf) = LFfn) by ((unfold LFfn in *); destruct leapfrog as [g h]; auto). 
(* take real step over float input*)
replace (leapfrog_step (xnf, vnf)) with (leapfrog_step LFfn) in * by auto. 
set (xn1r:=(fst (leapfrog_stepR (xnr, vnr)))) in *.
set (xn1f:=(fst (leapfrog_step LFfn))) in *. 
set (vn1r:=(snd (leapfrog_stepR (xnr, vnr)))) in *.
set (vn1f:=(snd (leapfrog_step LFfn))) in *. 

(* x case *)
assert (
(Rabs (fst (leapfrogR (x1, v1) (S n)) - B2R 24 128 xn1f)) <=
        ((1 - (pow lf_harm_real.h 2)/ 2) *
         Rabs (fst (leapfrogR (x1, v1) n) - xnr) +
         lf_harm_real.h * Rabs (snd (leapfrogR (x1, v1) n) - vnr)) + 
      / powerRZ 2 12
). 
replace (fst (leapfrogR (x1, v1) (S n)) - B2R 24 128 xn1f) with
(fst (leapfrogR (x1, v1) (S n)) - xn1r + (xn1r - B2R 24 128 xn1f)) by nra. 

assert (Rabs
  (fst (leapfrogR (x1, v1) (S n)) - xn1r +
         (xn1r - B2R 24 128 xn1f)) <= 
Rabs
  (fst (leapfrogR (x1, v1) (S n)) - xn1r) + Rabs (xn1r - B2R 24 128 xn1f)
) by (
pose proof (Rabs_triang (fst (leapfrogR (x1, v1) (S n)) - xn1r)
(xn1r - B2R 24 128 xn1f)); auto). 

assert (Rabs (fst (leapfrogR (x1, v1) (S n)) - xn1r) +
     Rabs (xn1r - B2R 24 128 xn1f) <= Rabs (fst (leapfrogR (x1, v1) (S n)) - xn1r) +
     / powerRZ 2 12) by nra. 

pose proof (Rle_trans
(Rabs (fst (leapfrogR (x1, v1) (S n)) - xn1r + (xn1r - B2R 24 128 xn1f)))
(Rabs (fst (leapfrogR (x1, v1) (S n)) - xn1r) + Rabs (xn1r - B2R 24 128 xn1f))
(Rabs (fst (leapfrogR (x1, v1) (S n)) - xn1r) + / powerRZ 2 12)
H10 H11
); clear H10 H11.

assert (
Rabs (fst (leapfrogR (x1, v1) (S n)) - xn1r + (xn1r - B2R 24 128 xn1f)) <=
      Rabs ( (fst (leapfrogR (x1, v1) (S n)) - fst (leapfrogR (x1, v1) n))
      - (xn1r - xnr)
      + (fst (leapfrogR (x1, v1) n) - xnr)) + / powerRZ 2 12) by (
(replace (fst (leapfrogR (x1, v1) (S n)) - xn1r) with
( (fst (leapfrogR (x1, v1) (S n)) - fst (leapfrogR (x1, v1) n))
- (xn1r - xnr)
+ (fst (leapfrogR (x1, v1) n) - xnr)) in * by nra); nra); clear H12.  

unfold xn1r in H10 at 3. 
rewrite ?one_stepR_x in *; rewrite ?one_stepR_x_alt in *; unfold lf_harm_real.F in *. 
replace (fst (xnr, vnr)) with xnr in *; replace (snd (xnr, vnr)) with vnr in *. 
replace (0.5) with (1/2) in H10 by nra. 
replace (lf_harm_real.h * snd (leapfrogR (x1, v1) n) +
         1 / 2 * lf_harm_real.h ^ 2 * (-1 * fst (leapfrogR (x1, v1) n)) -
         (- xnr * lf_harm_real.h ^ 2 + 2 * lf_harm_real.h * vnr) / 2 +
         (fst (leapfrogR (x1, v1) n) - xnr)) with
((1- (lf_harm_real.h ^ 2)/2)*(fst (leapfrogR (x1, v1) n) - xnr) + lf_harm_real.h * (snd (leapfrogR (x1, v1) n) - vnr))
in H10 by nra. 
pose proof (Rabs_triang
((1 - lf_harm_real.h ^ 2 / 2) * (fst (leapfrogR (x1, v1) n) - xnr))
(lf_harm_real.h * (snd (leapfrogR (x1, v1) n) - vnr))).
rewrite ?abs_mul in H11.
assert (Rabs
        ((1 - lf_harm_real.h ^ 2 / 2) * (fst (leapfrogR (x1, v1) n) - xnr) +
         lf_harm_real.h * (snd (leapfrogR (x1, v1) n) - vnr)) + 
      / powerRZ 2 12 <=
      (1 - lf_harm_real.h ^ 2 / 2) * Rabs (fst (leapfrogR (x1, v1) n) - xnr) +
      lf_harm_real.h * Rabs (snd (leapfrogR (x1, v1) n) - vnr) + 
      / powerRZ 2 12) by nra; clear H11. 
pose proof (Rle_trans
(Rabs (fst (leapfrogR (x1, v1) (S n)) - xn1r + (xn1r - B2R 24 128 xn1f)))
(Rabs
        ((1 - lf_harm_real.h ^ 2 / 2) * (fst (leapfrogR (x1, v1) n) - xnr) +
         lf_harm_real.h * (snd (leapfrogR (x1, v1) n) - vnr)) + 
      / powerRZ 2 12)
(      (1 - lf_harm_real.h ^ 2 / 2) * Rabs (fst (leapfrogR (x1, v1) n) - xnr) +
      lf_harm_real.h * Rabs (snd (leapfrogR (x1, v1) n) - vnr) + 
      / powerRZ 2 12)
H10 H12
).
all: try auto; try unfold lf_harm_real.h; try nra.

(* v case *)
assert (
(Rabs (snd (leapfrogR (x1, v1) (S n)) - B2R 24 128 vn1f)) <=
        ((1 - (pow lf_harm_real.h 2)/ 2) *
         Rabs (snd (leapfrogR (x1, v1) n) - vnr) -
         (lf_harm_real.h - (pow lf_harm_real.h 3)/4) * Rabs (fst (leapfrogR (x1, v1) n) - vnr)) + 
      / powerRZ 2 12 
) by admit.

replace (INR (S n)) with (INR n + 1) by (rewrite ?S_INR; auto).
destruct H4; split.

(* x case *)
replace (/ powerRZ 2 12) with (powerRZ 2 (-(12))) in * by auto.
assert 
(((1 - (pow lf_harm_real.h 2)/ 2) *
         Rabs (fst (leapfrogR (x1, v1) n) - xnr) +
         lf_harm_real.h * Rabs (snd (leapfrogR (x1, v1) n) - vnr)) + 
      / powerRZ 2 12 <= ((1 - (pow lf_harm_real.h 2)/ 2) *
         2 * lf_harm_real.h * INR n +
         lf_harm_real.h * 2 * lf_harm_real.h * INR n) + 
      / powerRZ 2 12 ) by (unfold lf_harm_real.h in *; nra). 

assert (INR n <= 1 / lf_harm_real.h) by nra.  

assert (      (1 - lf_harm_real.h ^ 2 / 2) * 2 * lf_harm_real.h * INR n +
      lf_harm_real.h * 2 * lf_harm_real.h * INR n + 
      / powerRZ 2 12 <= 2 * lf_harm_real.h * (INR n + 1)) by ( 
assert (((1 - (pow lf_harm_real.h 2)/ 2) *
         2 * lf_harm_real.h * INR n +
         lf_harm_real.h * 2 * lf_harm_real.h * INR n) + 
      / powerRZ 2 12 -  2 * lf_harm_real.h * (INR n + 1) <= 0) by (
unfold lf_harm_real.h in *; 
replace (/ powerRZ 2 12) with (powerRZ 2 (-(12))) in * by auto;
rewrite ?INR_IZR_INZ in *; field_simplify; interval); 
(pose proof (Rminus_le ((1 - lf_harm_real.h ^ 2 / 2) * 2 * lf_harm_real.h * INR n +
      lf_harm_real.h * 2 * lf_harm_real.h * INR n + 
      / powerRZ 2 12) (2 * lf_harm_real.h * (INR n + 1)))); auto).   

replace (/ powerRZ 2 12) with (powerRZ 2 (-(12))) in * by auto.

pose proof (Rle_trans 
(Rabs (fst (leapfrogR (x1, v1) (S n)) - B2R 24 128 xn1f))
((1 - lf_harm_real.h ^ 2 / 2) *
     Rabs (fst (leapfrogR (x1, v1) n) - xnr) +
     lf_harm_real.h * Rabs (snd (leapfrogR (x1, v1) n) - vnr) +
     powerRZ 2 (- (12)))
((1 - lf_harm_real.h ^ 2 / 2) * 2 * lf_harm_real.h * INR n +
      lf_harm_real.h * 2 * lf_harm_real.h * INR n +
      powerRZ 2 (- (12)))
H10 H13
); auto. 

pose proof (Rle_trans 
(Rabs (fst (leapfrogR (x1, v1) (S n)) - B2R 24 128 xn1f))
((1 - lf_harm_real.h ^ 2 / 2) * 2 * lf_harm_real.h * INR n +
      lf_harm_real.h * 2 * lf_harm_real.h * INR n +
      powerRZ 2 (- (12)))
(2 * lf_harm_real.h * (INR n + 1))
H16 H15
); auto. 

(* v case *)
replace (/ powerRZ 2 12) with (powerRZ 2 (-(12))) in * by auto.
assert (0 <=
      (lf_harm_real.h - lf_harm_real.h ^ 3 / 4) *
      Rabs (fst (leapfrogR (x1, v1) n) - vnr))  by (
assert (0 <=
      (lf_harm_real.h - lf_harm_real.h ^ 3 / 4)) by (unfold lf_harm_real.h;nra); 
assert (0 <= Rabs (fst (leapfrogR (x1, v1) n) - vnr)) by 
(try apply Rabs_pos; auto);
nra).
assert 
((1 - lf_harm_real.h ^ 2 / 2) *
      Rabs (snd (leapfrogR (x1, v1) n) - vnr) -
      (lf_harm_real.h - lf_harm_real.h ^ 3 / 4) *
      Rabs (fst (leapfrogR (x1, v1) n) - vnr) + 
      / powerRZ 2 12 <= (1 - lf_harm_real.h ^ 2 / 2) *
      Rabs (snd (leapfrogR (x1, v1) n) - vnr) + 
      / powerRZ 2 12) by nra. 
assert (Rabs ((snd (leapfrogR (x1, v1) (S n))) - (B2R 24 128 vn1f))
<= (1 - lf_harm_real.h ^ 2 / 2) *
      Rabs (snd (leapfrogR (x1, v1) n) - vnr) + 
      / powerRZ 2 12) by 
(pose proof (Rle_trans
(Rabs ((snd (leapfrogR (x1, v1) (S n))) - (B2R 24 128 vn1f)))
((1 - lf_harm_real.h ^ 2 / 2) *
      Rabs (snd (leapfrogR (x1, v1) n) - vnr) -
      (lf_harm_real.h - lf_harm_real.h ^ 3 / 4) *
      Rabs (fst (leapfrogR (x1, v1) n) - vnr) + 
      / powerRZ 2 12)
((1 - lf_harm_real.h ^ 2 / 2) *
      Rabs (snd (leapfrogR (x1, v1) n) - vnr) + 
      / powerRZ 2 12)
H11 H14); auto). 
assert (
(Rabs ((snd (leapfrogR (x1, v1) (S n))) - (B2R 24 128 vn1f))) <=
      (((1 - ((lf_harm_real.h ^ 2) / 2)) *
       ((2 * lf_harm_real.h) * (INR n))) +
       (/ (powerRZ 2 12)))) by (assert (0 < (1 - ((lf_harm_real.h ^ 2) / 2)))
 by (unfold lf_harm_real.h;nra); nra).
assert ((((1 - ((lf_harm_real.h ^ 2) / 2)) *
        ((2 * lf_harm_real.h) * (INR n))) + (/ (powerRZ 2 12))) 
<= ((2 * lf_harm_real.h) * ((INR n) + 1))).


assert (0<= INR n /\ INR n <= 31). split. 
-apply pos_INR. 
-unfold lf_harm_real.h in *; field_simplify; nra. 
assert ((powerRZ 2 12) <> 0) by 
((assert (0 < (powerRZ 2 12)) by interval); interval).
assert ((((1 - ((lf_harm_real.h ^ 2) / 2)) *
        ((2 * lf_harm_real.h) * (INR n))) + (/ (powerRZ 2 12))) 
         - ((2 * lf_harm_real.h) * ((INR n) + 1)) <= 0); 
unfold lf_harm_real.h; field_simplify. interval. 
all: try auto.   

(pose proof (Rminus_le (((1 - ((lf_harm_real.h ^ 2) / 2)) *
         ((2 * lf_harm_real.h) * (INR n))) + (/ (powerRZ 2 12)))
(2 * lf_harm_real.h * (INR n + 1)) H19)); auto; clear H19.

unfold lf_harm_real.h in H20; field_simplify in H20; auto.
pose proof (Rle_trans
(Rabs ((snd (leapfrogR (x1, v1) (S n))) - (B2R 24 128 vn1f)))
(((1 - ((lf_harm_real.h ^ 2) / 2)) * ((2 * lf_harm_real.h) * (INR n))) +
       (/ (powerRZ 2 12)))
((2 * lf_harm_real.h) * ((INR n) + 1))
H16 H17
); auto.



