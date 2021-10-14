From Flocq Require Import Binary Bits Core.
From compcert.lib Require Import IEEE754_extra Coqlib Floats Zbits Integers.
Require Import float_lib lf_harm_float lf_harm_real.

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

Import ListNotations.
Definition _x : AST.ident := 5%positive.
Definition _v : AST.ident := 7%positive.

Print leapfrog_stepx.

(* TODO: the reification of these expressions breaks up h and F, and errors are then
incorrectly associated with the division and multiplication in these terms in the 
tactic get_eps_delts*)
Definition e := ltac:(let e' := reify_float_expr constr:((float32_of_Z 1 / float32_of_Z 32)%F32 ) in exact e').
Definition e1 := ltac:(let e' := HO_reify_float_expr constr:([_x; _v]) leapfrog_stepx in exact e').
Definition two_step (x v : float32) := leapfrog_stepx (leapfrog_stepx x v) (leapfrog_stepx x v).
Definition e2 := ltac:(let e' := HO_reify_float_expr constr:([_x; _v]) two_step in exact e').

Import FPLang.

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

Check list_to_bound_env.

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
 let e' := eval hnf in e1 in change e1 with e';
 cbv [fval type_of_expr type_of_unop Datatypes.id];
 repeat change (type_lub _ _) with Tsingle;
 repeat change (type_lub _ _) with Tdouble;
 repeat change (cast_lub_l Tsingle Tsingle ?x) with x;
 repeat change (cast_lub_r Tsingle Tsingle ?x) with x;
 repeat change (cast_lub_l Tdouble Tdouble ?x) with x;
 repeat change (cast_lub_r Tdouble Tdouble ?x) with x;
 cbv [fop_of_unop fop_of_exact_unop fop_of_binop fop_of_rounded_binop];
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

Lemma env_fval_reify_correct_leapfrog_stepx:
  forall x v : float32,
  fval (leapfrog_env x v) e1 = leapfrog_stepx x v.
Proof.
intros.
unfold leapfrog_env.
unfold_reflect' e1.
reflexivity.
Qed.

Lemma reify_correct_leapfrog_stepx:
  forall x v : float32,
  fval (list_to_env [(_x, Values.Vsingle x);(_v, Values.Vsingle v)]) e1 = leapfrog_stepx x v.
Proof.
intros.
unfold_reflect e1.
reflexivity.
Qed.

Lemma env_rval_reify_correct_leapfrog_stepx:
  forall x v : float32,
  forall x1 v1 : R,
  x1 = B2R _ _ x ->
  v1 = B2R _ _ v -> 
  rval (leapfrog_env x v) e1 = fst (leapfrog_stepR (x1,v1)).
Proof.
intros.
unfold leapfrog_env.
match goal with |- context [rval (list_to_bound_env ?L1 ?L2) e1] =>
 pattern (rval (list_to_bound_env L1 L2) e1);
 let HIDE := fresh "HIDE" in match goal with |- ?A _ => set (HIDE:=A) end;
 let m := fresh "m" in let m' := fresh "m'" in
 set (m := list_to_bound_env L1 L2);
 hnf in m;
 set (m1 := (Maps.PTree_Properties.of_list L1)) in m;
 hnf in m1; simpl in m1;
 set (m2 := (Maps.PTree_Properties.of_list L2)) in m;
 hnf in m2; simpl in m2;
 let e' := eval hnf in e1 in change e1 with e';
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
simpl. cbv [Defs.F2R FLT_exp]; simpl. rewrite ?Zpower_pos_powerRZ. 
replace (8388608 * / powerRZ 2 23) with 1. 
replace ((8388608 * / powerRZ 2 18)) with 32.
replace ((8388608 * / powerRZ 2 22)) with 2. 
unfold leapfrog_stepR, F, h, fst; subst.
replace (B2R (fprec Tsingle) 128 x) with (B2R 24 128 x) by auto.
replace (B2R (fprec Tsingle) 128 v) with (B2R 24 128 v) by auto. 
nra. 
replace ((8388608 * / powerRZ 2 22)) with (8388608 / 2^22). nra. auto.
replace ((8388608 * / powerRZ 2 18)) with (8388608 / 2^18). nra. auto.
replace ((8388608 * / powerRZ 2 23)) with (8388608 / 2^23). nra. auto.
Qed. 

Import vcfloat.Test.
Import vcfloat.FPSolve.

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

(* solve_all_eval_cond tactics are very slow*)
Lemma leapfrog_cond2_holds:
   forall vmap : valmap,
      boundsmap_denote leapfrog_bmap vmap -> 
   forall r si2 s p, 
      rndval_with_cond 0 (mempty (Tsingle, Normal)) e1 =
         (r, (si2, s), p) ->
      list_forall (eval_cond2 (mk_env leapfrog_bmap vmap) s) p . 
Proof.
intros. 
set (bmap:= leapfrog_bmap) in *.
apply boundsmap_denote_e in H.
rewrite list_forall_Forall in H.
rewrite list_forall_Forall. 
prepare_assumptions_about_free_variables.
solve_all_eval_cond2;
solve_one_eval_cond2.
Qed.

Lemma two_step_cond2_holds:
   forall vmap : valmap,
      boundsmap_denote leapfrog_bmap vmap -> 
   forall r si2 s p, 
      rndval_with_cond 0 (mempty (Tsingle, Normal)) e2 =
         (r, (si2, s), p) ->
      list_forall (eval_cond2 (mk_env leapfrog_bmap vmap) s) p . 
Proof.
intros. 
set (bmap:= leapfrog_bmap) in *.
apply boundsmap_denote_e in H.
rewrite list_forall_Forall in H.
rewrite list_forall_Forall. 
prepare_assumptions_about_free_variables.
solve_all_eval_cond2;
solve_one_eval_cond2.
Qed.

(*TODO: the following lemmas and the above two lemmas should be generalized
into tactics*)
Lemma leapfrog_cond1_holds:
   forall vmap : valmap,
      boundsmap_denote leapfrog_bmap vmap -> 
   forall r si2 s p, 
      rndval_with_cond 0 (mempty (Tsingle, Normal)) e1 =
         (r, (si2, s), p) ->
    forall i : cond, List.In i p -> eval_cond1 (env_ vmap) s i.
Proof.
intros ? ? ? ? ? ? ?. 
pose proof (leapfrog_cond2_holds vmap H r si2 s p H0).
set (bmap:= leapfrog_bmap) in *;
replace (mk_env bmap vmap) with (env_ vmap) in H1 by (apply env_mk_env; auto). 
set (env:= env_ vmap) in *.
apply list_forall_spec. apply (list_forall_ext (eval_cond2 env s)). apply eval_cond2_correct. auto.
Qed.

Lemma two_step_cond1_holds:
   forall vmap : valmap,
      boundsmap_denote leapfrog_bmap vmap -> 
   forall r si2 s p, 
      rndval_with_cond 0 (mempty (Tsingle, Normal)) e2 =
         (r, (si2, s), p) ->
    forall i : cond, List.In i p -> eval_cond1 (env_ vmap) s i.
Proof.
intros ? ? ? ? ? ? ?. 
pose proof (two_step_cond2_holds vmap H r si2 s p H0).
set (bmap:= leapfrog_bmap) in *;
replace (mk_env bmap vmap) with (env_ vmap) in H1 by (apply env_mk_env; auto). 
set (env:= env_ vmap) in *.
apply list_forall_spec. apply (list_forall_ext (eval_cond2 env s)). apply eval_cond2_correct. auto.
Qed.

(*TODO: this tactic uses lemmas specific for e = e1; needs to be generalized*)
Ltac get_rndval_with_cond_correct_e1:=
match goal with
    H: boundsmap_denote ?bmap ?vmap |- _ => 
let HFIN:= fresh in (
assert (forall ty i, is_finite (fprec ty) (femax ty) ((env_ vmap) ty i) = true) as HFIN by
 (apply (finite_env bmap vmap H))
);
(destruct (rndval_with_cond O (mempty  (Tsingle, Normal)) e1) as [[r [si2 s]] p] eqn:rndval);
let lc2:= fresh in (
assert (list_forall (eval_cond2 (mk_env bmap vmap) s) p ) as lc2 by
(apply (leapfrog_cond2_holds vmap H r si2 s p rndval))
);
let HVALID:= fresh in ( 
assert (expr_valid e1 = true) as HVALID by reflexivity
);
replace (mk_env bmap vmap) with (env_ vmap) in lc2 by (apply env_mk_env; auto);
let listconds:= fresh in (
assert (forall i : cond, List.In i p -> eval_cond1 (env_ vmap) s i) as listconds by
(apply (leapfrog_cond1_holds vmap H r si2 s p rndval))
);
(destruct (rndval_with_cond_correct
                          _ HFIN _ HVALID _ _ _ _ rndval lc2 _ (eq_refl _)) as [] eqn:correct); 
clear correct HFIN HVALID listconds 
end.

Ltac get_rndval_with_cond_correct_e2:=
match goal with
    H: boundsmap_denote ?bmap ?vmap |- _ => 
let HFIN:= fresh in (
assert (forall ty i, is_finite (fprec ty) (femax ty) ((env_ vmap) ty i) = true) as HFIN by
 (apply (finite_env bmap vmap H))
);
(destruct (rndval_with_cond O (mempty  (Tsingle, Normal)) e2) as [[r [si2 s]] p] eqn:rndval);
let lc2:= fresh in (
assert (list_forall (eval_cond2 (mk_env bmap vmap) s) p ) as lc2 by
(apply (two_step_cond2_holds vmap H r si2 s p rndval))
);
let HVALID:= fresh in ( 
assert (expr_valid e2 = true) as HVALID by reflexivity
);
replace (mk_env bmap vmap) with (env_ vmap) in lc2 by (apply env_mk_env; auto);
let listconds:= fresh in (
assert (forall i : cond, List.In i p -> eval_cond1 (env_ vmap) s i) as listconds by
(apply (two_step_cond1_holds vmap H r si2 s p rndval))
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

(* TODO: fix so that eps and delts aren't associated with exact unary operations
and powers of 2; i.e. consistent with VCFloat annotation of terms*)
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
  inversion H0;
  subst si2 s r;
  get_eps_delts;
  match goal with | [H': reval _ _ (mget (mset (?M) _ _)) = B2R _ _ _ |- _] => 
  try (
    match type of H' with context [{| Fnum := ?n; Fexp := FLT_exp _ _ _ |}] =>
      change n with (Z.pow_pos (2%Z) (Z.to_pos ((Z.log2 n%Z)%Z) ) ) in H';
      let x:= fresh "x" in set (x:= Z.log2 _) in H'; simpl in x; subst x; try reflexivity;
      repeat (
      let x:= fresh "x" in set (x:= FLT_exp _ _ _) in H'; unfold FLT_exp in x; unfold Z.max in x; simpl in x; subst x
            )
    end
      );
      let m := fresh "m" in set (m:=M); compute in m; unfold reval in H';
      rewrite ?(mget_set Nat.eq_dec m) in H' ;
      cbv [reval Prog.binary Prog.real_operations Tree.binary_real 
      Prog.unary Prog.binary Tree.unary_real F2R fone bpow radix_val radix2] in H';
      repeat (
        match type of H' with context [mget m ?i] =>
          let x:= fresh "x" in set (x:= mget m i) in H'; hnf in x; subst x 
        end  );
      repeat (
        match type of H' with context [if Nat.eq_dec _ _ then _ else _] =>
          let x:= fresh "x" in set (x:= if Nat.eq_dec _ _ then _ else _) in H'; hnf in x; subst x 
        end  ) ; 
      rewrite ?Rmult_1_l in H';
      rewrite ?Rmult_1_r in H';
      rewrite ?Pos2Z.inj_pow_pos in H'; rewrite ?IZR_Zpower_pos in H'; unfold powerRZ in H'; 
      rewrite ?powerRZ_pos_sub2 in H'; try lra ; rewrite ?powerRZ_O in H'; rewrite ?neg_powerRZ in H'; try lra;
      repeat (
        match type of H' with context [Z.pos_sub _ _] =>
          let x:= fresh "x" in set (x:= Z.pos_sub _ _) in H'; simpl in x; subst x 
        end ) 
    end
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

Import Interval.Tactic.

(* position error between R and F functions over one step of integration*)
Lemma one_step_errorx:
  forall x v : float32,
    boundsmap_denote leapfrog_bmap (leapfrog_vmap x v)->
    Rle (Rabs (Rminus (rval (leapfrog_env x v) e1) (B2R _ _ (fval (leapfrog_env x v) e1)))) 
         (/ powerRZ 2 12)%R.
Proof.
intros.
set (bmap:= leapfrog_bmap) in *.
hnf in bmap. simpl in bmap.
(* TO DO: are conditions p required from get_rndval_with_cond_correct?
I.e., either p haven't been solved OR they've already been
solved and therefore, for efficiency, we shouldn't have to look at them *)
get_rndval_with_cond_correct e1.
(* Populate hyps with some bounds on x and v*)
fv_prepare_assumptions.
(* turn rndval rexp to flt with eps delt *)
get_rexp_with_eps_delt e1.
clear H1 rndval H5 m H e0 p.
(* BLOCK 1*)
(* TODO : cleanup with tactic or lemma *)
simpl rval.  
  try (
    match goal with |- context [{| Fnum := ?n; Fexp := FLT_exp _ _ _ |}] =>
      change n with (Z.pow_pos (2%Z) (Z.to_pos ((Z.log2 n%Z)%Z) ) ) ;
      let x:= fresh "x" in set (x:= Z.log2 _); simpl in x; subst x; try reflexivity;
      repeat (
      let x:= fresh "x" in set (x:= FLT_exp _ _ _); unfold FLT_exp in x; unfold Z.max in x; simpl in x; subst x
            )
    end
      ).  
cbv [Defs.F2R fone bpow radix_val radix2 Fexp Fnum]. 
rewrite ?Zpower_pos_powerRZ. unfold powerRZ. 
      rewrite ?powerRZ_pos_sub2 ; try lra . rewrite ?neg_powerRZ ; try lra.
      repeat (
        match goal with |- context [Z.pos_sub _ _] =>
          let x:= fresh "x" in set (x:= Z.pos_sub _ _); simpl in x; subst x 
        end ) .
rewrite ?powerRZ_O .
(* BLOCK 2*)
pattern (B2R (fprec (type_of_expr e1)) (femax (type_of_expr e1))
     (fval (leapfrog_env x v) e1));  try rewrite <- e2.
(* BLOCK 3*)
unfold FT2R in *.
replace (leapfrog_env x v Tsingle lf_harm_lemmas._x) with val_x in * by 
(cbv in Hval_x;inversion Hval_x; clear Hval_x; subst; auto).
replace (env_ (leapfrog_vmap x v) Tsingle lf_harm_lemmas._x) with val_x in * by 
(cbv in Hval_x;inversion Hval_x; clear Hval_x; subst; auto).
replace (leapfrog_env x v Tsingle lf_harm_lemmas._v) with val_v in * by 
(cbv in Hval_v;inversion Hval_v; clear Hval_v; subst; auto).
replace (env_ (leapfrog_vmap x v) Tsingle lf_harm_lemmas._v) with val_v in * by 
(cbv in Hval_v;inversion Hval_v; clear Hval_v; subst; auto).
clear e2.
replace (B2R (fprec Tsingle) (femax Tsingle) val_v) with
(B2R (fprec Tsingle) 128 val_v) in * by auto.
replace (B2R (fprec Tsingle) (femax Tsingle) val_x) with
(B2R (fprec Tsingle) 128 val_x) in * by auto.
(* clear var_x occurence*)
set (r1:= ((((powerRZ 2 (- (5)) * (1 + del5) + eps5) *
        (powerRZ 2 (- (5)) * (1 + del4) + eps4) * 
        (1 + del3) + eps3) *
       (- (1) * B2R (fprec Tsingle) 128 val_x * (1 + del2) + eps2) *
       (1 + del1) + eps1) / powerRZ 2 1 * (1 + del0)) ) in *.
set (r2:= ((powerRZ 2 (- (5)) * (1 + del8) + eps8) * B2R (fprec Tsingle) 128 val_v *
       (1 + del7) + eps7)) in *. 
try (
 repeat(
    match goal with |- context [?a * (?b + ?c)] =>
    rewrite ?Rmult_plus_distr_l; rewrite ?Rmult_plus_distr_r
end
      ) ; rewrite ?Rmult_1_r
). 
try (
repeat (
    match goal with |- context [?a - (?b + ?d)] =>
     rewrite ?Rminus_dist 
end) 
      ).
replace   (B2R (fprec Tsingle) 128 val_x + powerRZ 2 (- (5)) * B2R (fprec Tsingle) 128 val_v +
   powerRZ 2 (- (5)) * powerRZ 2 (- (5)) * (- (1) * B2R (fprec Tsingle) 128 val_x) / powerRZ 2 1 -
   B2R (fprec Tsingle) 128 val_x - r2 - B2R (fprec Tsingle) 128 val_x * del6 - 
   r2 * del6 - eps6 - r1 - eps0 - B2R (fprec Tsingle) 128 val_x * del - 
   r2 * del - B2R (fprec Tsingle) 128 val_x * del6 * del - r2 * del6 * del - 
   eps6 * del - r1 * del - eps0 * del - eps) with  
(powerRZ 2 (- (5)) * B2R (fprec Tsingle) 128 val_v +
   powerRZ 2 (- (5)) * powerRZ 2 (- (5)) * (- (1) * B2R (fprec Tsingle) 128 val_x) / powerRZ 2 1 
   - r2 - B2R (fprec Tsingle) 128 val_x * del6 - 
   r2 * del6 - eps6 - r1 - eps0 - B2R (fprec Tsingle) 128 val_x * del - 
   r2 * del - B2R (fprec Tsingle) 128 val_x * del6 * del - r2 * del6 * del - 
   eps6 * del - r1 * del - eps0 * del - eps).
unfold r1, r2 in *; clear r2 r1.
(*apply interval; simple "interval" doesn't work*)
interval with (i_bisect (B2R (fprec Tsingle) 128 val_x), i_bisect (B2R (fprec Tsingle) 128 val_v), 
i_taylor (B2R (fprec Tsingle) 128 val_x), i_taylor (B2R (fprec Tsingle) 128 val_v)).
nra. 
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
pose proof env_fval_reify_correct_leapfrog_stepx x v; auto.
pose proof env_rval_reify_correct_leapfrog_stepx x v x1 v1; auto.
Qed.

Definition iternf  (n:nat) (x v :float32) :=  leapfrog (x%F32, v%F32) n.
Definition iternfR (n:nat) (x v :R) :=  leapfrogR (x,v) n .

(*TODO: compute two ways, using (1) standard Lipschitz decomp of terms and 
(2) using difference between consecutive FP and R steps*)

(* bound on real valued difference in floating point solutions between one and two steps *) 
Lemma one_stepFx:
  forall x v : float32,
    boundsmap_denote leapfrog_bmap (leapfrog_vmap x v)->
    Rle (Rabs (Rminus (B2R _ _ (fval (leapfrog_env x v) e2)) (B2R _ _ (fval (leapfrog_env x v) e1)))) 
         (/ powerRZ 2 12)%R.
Proof.
intros.
set (bmap:= leapfrog_bmap) in *.
set (vmap:= leapfrog_vmap) in *.
hnf in bmap. simpl in bmap.
get_rndval_with_cond_correct_e2.
(* Populate hyps with some bounds on x and v*)
fv_prepare_assumptions.
(* turn rndval rexp to flt with eps delt *)
get_rexp_with_eps_delt e2.
Admitted.

(*TODO: relate difference of n and n+1 iterations to difference between e1 and e2*)
Lemma one_stepFx:
  forall x v : float32,
   forall n: nat,
    boundsmap_denote leapfrog_bmap (leapfrog_vmap x v)->
    Req (Rminus (B2R _ _ (fval (leapfrog_env x v) e2)) (B2R _ _ (fval (leapfrog_env x v) e1))) 
         (Rminus (B2R _ _ (fst(leapfrog_step (iternf (S n) x%F32 v%F32)))) (B2R _ _ (fst(leapfrog_step (iternf n x%F32 v%F32))))).
Proof.
Admitted.

Lemma global_error2:
  (forall x v : float32, 
  forall n: nat,
(
  Rle (Rabs (Rminus (fst(leapfrog_stepR (iternfR n x1%R v1%R))) (B2R _ _ (fst(leapfrog_step (iternf n x%F32 v%F32)))))) 
((Rabs (Rminus (fst(leapfrog_stepR (x1%R,v1%R))) (B2R _ _ (fst(leapfrog_step (x%F32,v%F32)))))) * ((INR n)%R + 1))
)
).
Proof.
intros.
induction n.
-unfold iternf ,iternfR ,INR, leapfrog, leapfrogR in *; nra.
-unfold iternfR, iternf in *. 
set (s1:= fst (leapfrog_stepR (leapfrogR (x1, v1) n))) in *.
set (s2:= B2R 24 128 (fst (leapfrog_step (leapfrog (x, v) n)))) in *.
replace (fst (leapfrog_stepR (leapfrogR (x1, v1) (S n))) -
   B2R 24 128 (fst (leapfrog_step (leapfrog (x, v) (S n))))) with
(fst (leapfrog_stepR (leapfrogR (x1, v1) (S n))) - s1 -
   B2R 24 128 (fst (leapfrog_step (leapfrog (x, v) (S n)))) + s2 +(s1-s2) ) by nra.
unfold s1, s2 in *; clear s1 s2. 
rewrite ?lfstepR_lfn; rewrite ?lfstep_lfn. 
set (s:=(leapfrog_stepR (x1, v1))) in *;
pose proof (one_stepR n s). 


pose proof one_stepR

assert (Rabs (fst (leapfrog_stepR r r0) - B2R 24 128 (leapfrog_stepx f f0)) <=
      Rabs (fst (leapfrog_stepR x1 v1) - B2R 24 128 (leapfrog_stepx x v)) *
      (INR n + 1)) by (specialize (IHn f f0 r r0); apply IHn ; auto). clear IHn.
replace (leapfrog_stepR r r0) with (x1', v1') in *. unfold leapfrog_stepx in H1.
replace (leapfrog_step (f, f0)) with (x', v') in *. clear H H0.
replace (Rabs (fst (x1', v1') - B2R 24 128 (fst (x', v')))) with (Rabs x1' - B2R 24 128 x') in *.
replace ((fst (leapfrog_stepR x1' v1') - B2R 24 128 (leapfrog_stepx x' v'))) 
with ((fst (leapfrog_stepR x1' v1') - B2R 24 128 (leapfrog_stepx x' v') - (x1' - B2R 24 128 x') + (x1' - B2R 24 128 x') )) by nra.



assert ( (x',v') = (leapfrog_stepx (fst (iternf n x%F32 v%F32))%F32 (snd (iternf n x%F32 v%F32)%F32)) ).

unfold leapfrog_stepR, leapfrog_stepx, leapfrog_step, 
lf_harm_real.F,lf_harm_real.h, lf_harm_float.F,lf_harm_float.h, fst,snd. 
unfold leapfrogR, leapfrog, fst; subst. replace (B2R 24 128 x - B2R 24 128 x) with 0. 
 (* 
((Rabs (Rminus (fst(leapfrog_stepR x1%R v1%R)) (B2R _ _ (leapfrog_stepx x%F32 v%F32)))) * (INR n)%R)
Rle (Rabs (Rminus (iternfR n%Z x1%R v1%R) (B2R _ _ (iternf n%Z x%F32 v%F32) ) ) ) ((/ powerRZ 2 12)%R * (IZR n)%R)%R.
 Rle (Rabs (Rminus (iternfR n x1%R v1%R) (B2R _ _ (iternf n x%F32 v%F32) ) ) ) ((/ powerRZ 2 12)%R * (INR n)%R)%R.*)
Proof.
intros.
unfold iternf, iternfR. (*
get_rndval_with_cond_correct e1.

(* Populate hyps with some bounds on x and v*)
fv_prepare_assumptions.
(* turn rndval rexp to flt with eps delt *)
get_rexp_with_eps_delt e1.
clear H3 rndval H7. *)

induction n.
unfold leapfrogR, leapfrog, fst; subst. replace (B2R 24 128 x - B2R 24 128 x) with 0. 
try interval. assert (B2R 24 128 x = B2R 24 128 x) by auto; nra.

replace (leapfrogR x1 v1 (S n)) with (leapfrog_stepR (fst (leapfrogR x1 v1 n)) (snd (leapfrogR x1 v1 n))).
replace (leapfrog (x,v) (S n)) with (leapfrog_step (fst(leapfrog (x,v) n),snd(leapfrog (x,v) n))) .
destruct (leapfrogR x1 v1 n), (leapfrog (x, v) n), (leapfrog (x, v) (S n)), (leapfrogR x1 v1 n). 
set (s:=(fst (r, r0))) in *. 
unfold fst in s; subst s. 
set (s:=(snd (r, r0))) in *. 
unfold snd in s; subst s. 
set (s:=(fst (f, f0))) in *. 
unfold fst in s; subst s. 
set (s:=(snd (f, f0))) in *. 
unfold snd in s; subst s. 
unfold leapfrog_stepR, fst, snd, lf_harm_real.h, lf_harm_real.F in *. 
Admitted.

