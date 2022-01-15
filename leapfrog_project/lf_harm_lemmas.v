From Flocq Require Import Binary Bits Core.
From compcert.lib Require Import IEEE754_extra Coqlib Floats Zbits Integers.
Require Import float_lib lf_harm_float lf_harm_real vcfloat.
Set Bullet Behavior "Strict Subproofs". 

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

Definition leapfrog_stepx x v := fst (leapfrog_step' (x,v)).
Definition leapfrog_stepv x v := snd (leapfrog_step' (x,v)).

Import ListNotations.
Definition _x : AST.ident := 1121%positive.
Definition _v : AST.ident := 1117%positive.


Import FPLangOpt. 
Import FPLang.
Import FPSolve.


Definition x' := ltac:(let e' := 
  HO_reify_float_expr constr:([_x; _v]) leapfrog_stepx in exact e').
Definition v' := ltac:(let e' := 
  HO_reify_float_expr constr:([_x; _v]) leapfrog_stepv in exact e').


Definition list_to_bound_env (bindings: list  (AST.ident * Test.varinfo)) 
  (bindings2: list  (AST.ident * Values.val)) : (forall ty : type, AST.ident -> ftype ty) .
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

Ltac unfold_corresponding e :=
  (* This tactic is given a term (E1=E2), where E1 is an expression
     with internal nodes Bplus, Bminus, etc. and arbitrary leaves;
    and E2 is an expression which, if carefully unfolded in the right places,
    would have just the same tree structure.  And it carefully unfolds
    just in the right places, and returns (E1=E2') where E2' is the unfolding of E2.

    We want this tactic because, if we do not carefully unfold E2 before
   calling reflexivity, then reflexivity takes forever and then Qed takes
   two-to-the-forever.   In particular, some of the operators we may need
   to unfold are Float32.add, Float32.sub, et cetera. *)
lazymatch e with eq ?E1 ?E2 =>
lazymatch E1 with
 | Bplus ?a1 ?b1 ?c1 ?d1 ?e1 ?f1 ?l1 ?r1 =>
    lazymatch E2 with
    | Bplus _ _ _ _ _ _ ?l2 ?r2 => 
          let l2' := unfold_corresponding constr:(eq l1 l2) in
          let r2' := unfold_corresponding constr:(eq r1 r2) in
          constr:(Bplus a1 b1 c1 d1 e1 f1 l2' r2')
   | _ => 
          let E2' := eval red  in E2 in unfold_corresponding constr:(eq E1 E2')
    end
 | Bminus ?a1 ?b1 ?c1 ?d1 ?e1 ?f1 ?l1 ?r1 =>
    lazymatch E2 with
    | Bminus _ _ _ _ _ _ ?l2 ?r2 => 
          let l2' := unfold_corresponding constr:(eq l1 l2) in
          let r2' := unfold_corresponding constr:(eq r1 r2) in
          constr:(Bminus a1 b1 c1 d1 e1 f1 l2' r2') 
   | _ => 
          let E2' := eval red  in E2 in unfold_corresponding constr:(eq E1 E2')
    end
 | Bmult ?a1 ?b1 ?c1 ?d1 ?e1 ?f1 ?l1 ?r1 =>
    lazymatch E2 with
    | Bmult _ _ _ _ _ _ ?l2 ?r2 => 
          let l2' := unfold_corresponding constr:(eq l1 l2) in
          let r2' := unfold_corresponding constr:(eq r1 r2) in
          constr:(Bmult a1 b1 c1 d1 e1 f1 l2' r2')
   | _ => 
          let E2' := eval red  in E2 in unfold_corresponding constr:(eq E1 E2')
    end
 | Bdiv ?a1 ?b1 ?c1 ?d1 ?e1 ?f1 ?l1 ?r1 =>
    lazymatch E2 with
    | Bdiv _ _ _ _ _ _ ?l2 ?r2 => 
          let l2' := unfold_corresponding constr:(eq l1 l2) in
          let r2' := unfold_corresponding constr:(eq r1 r2) in
          constr:(Bdiv a1 b1 c1 d1 e1 f1 l2' r2') 
   | _ => 
          let E2' := eval red  in E2 in unfold_corresponding constr:(eq E1 E2')
    end
 | Bopp ?a1 ?b1 ?c1 ?x1 =>
    lazymatch E2 with
    | Bopp _ _ _ ?x2 => 
          let x2' := unfold_corresponding constr:(eq x1 x2) in
          constr:(Bopp a1 b1 c1 x2') 
   | _ => 
          let E2' := eval red  in E2 in unfold_corresponding constr:(eq E1 E2')
    end
 | _ => constr:(E2)
end end.

Ltac unfold_float_ops_for_equality :=
  (* see comment at Ltac unfold_corresponding. *)
  lazymatch goal with |- ?a = ?b => 
        let b' := unfold_corresponding constr:(a=b) in change (a=b')
  end.

Ltac unfold_reflect' E := 
repeat lazymatch goal with 
| |- context [fval (list_to_bound_env ?L1 ?L2) E] =>
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
 cbv [fval type_of_expr type_of_unop 
        fop_of_unop fop_of_exact_unop fop_of_rounded_unop
        fop_of_binop fop_of_rounded_binop Datatypes.id];
 repeat match goal with |- context [m ?t ?i] =>
             let u := fresh "u" in set (u := m t i); hnf in u; subst u
 end;
 subst m1 m2 m; 
 repeat (change (type_lub ?a ?b) with a || change (type_lub ?a ?b) with b);
 repeat change (cast_lub_l _ _ ?x) with x;
 repeat change (cast_lub_r _ _ ?x) with x;
 repeat change (cast _ _ ?x) with x;
 cbv beta delta [BPLUS BMINUS BMULT BDIV BOPP BINOP];
 change (fprec_gt_0 Tsingle) with (eq_refl Lt);
 change (fprec_lt_femax Tsingle) with (eq_refl Lt);
(* change (Bplus (fprec Tsingle) (femax Tsingle) _ _ _ _) with Float32.add;
 change (Bminus (fprec Tsingle) (femax Tsingle) _ _ _ _) with Float32.sub;
 change (Bmult (fprec Tsingle) (femax Tsingle) _ _ _ _) with Float32.mul;
 change (Bdiv (fprec Tsingle) (femax Tsingle) _ _ _ _) with Float32.div; 
 change (Bopp (fprec Tsingle) (femax Tsingle) _) with Float32.neg;
 change (Bplus (fprec Tsingle) (femax Tsingle) _ _ _ _) with Float.add;
 change (Bminus (fprec Tsingle) (femax Tsingle) _ _ _ _) with Float.sub;
 change (Bmult (fprec Tsingle) (femax Tsingle) _ _ _ _) with Float.mul;
 change (Bdiv (fprec Tsingle) (femax Tsingle) _ _ _ _) with Float.div; 
 change (Bopp (fprec Tsingle) (femax Tsingle) _) with Float.neg;
*)
 subst HIDE; cbv beta
(* lazymatch goal with |- ?a = ?b => 
        let b' := unfold_corresponding constr:(a=b) in change (a=b')
  end
*)
| |- context [fval ?env E] => let y := eval red in env in change env with y
end.



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

Lemma env_rval_reify_correct_leapfrog_stepx:
  forall x v : float32,
  forall x1 v1 : R,
  x1 = B2R _ _ x ->
  v1 = B2R _ _ v -> 
  rval (leapfrog_env x v) (optimize_div x') = fst (leapfrog_stepR (x1,v1)).
Proof.
intros.
unfold leapfrog_env.
match goal with |- context [rval ?env ?e] =>
  simplify_shift_div_opt e
end. 
match goal with |- context [rval ?env ?e] =>
  unfold_reflect_rval e; cbv [id]
end.
unfold leapfrog_stepR, F, h, fst, snd; subst.
replace (B2R (fprec Tsingle) (femax Tsingle) x) with 
  (B2R 24 128 x) by auto.
replace (B2R (fprec Tsingle) (femax Tsingle) v) with 
  (B2R 24 128 v) by auto.
simpl; unfold Defs.F2R; simpl; try nra.
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
match goal with |- context [rval ?env ?e] =>
  simplify_shift_div_opt e
end.
match goal with |- context [rval ?env ?e] =>
  unfold_reflect_rval e; cbv [id]
end. 
unfold leapfrog_stepR, F, h, fst; subst.  
replace (B2R (fprec Tsingle) (femax Tsingle) x) with 
  (B2R 24 128 x) by auto.
replace (B2R (fprec Tsingle) (femax Tsingle) v) with 
  (B2R 24 128 v) by auto.
simpl; unfold Defs.F2R; simpl; try nra.
Qed.


Import vcfloat.Test.


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


Ltac fin_assumptions :=
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
 end
.


Ltac rndval_replace :=
  match goal with 
    H0: (rndval_with_cond 0 (mempty (Tsingle, Normal)) ?ex = (?r, (?si, ?s), ?p)) |- _ =>
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
end
.

Import Interval.Tactic.


Lemma neg_powerRZ (x:R) (n:Z) :
  x <> R0 -> 
  1 / (powerRZ x%R n%Z) = (powerRZ x%R (-n)%Z) .
Proof.
intros; pose proof power_RZ_inv x n H; symmetry; rewrite <- H0; nra. 
Qed.

Lemma mul_hlf_powerRZ (n:Z) :
 / 2 * / powerRZ 2 n = powerRZ 2 (-n-1).
Proof.
assert (2 <> R0) by nra.
replace (/ 2) with (1/2) by nra.
replace (1 / 2 * / powerRZ 2 n) with
(1 / 2 * powerRZ 2 (- n)).
match goal with |- ?s = powerRZ ?a ?b' =>
replace b' with (-1 + - n)%Z by ring
end.
pose proof powerRZ_add 2 (-1) (-n) H. rewrite H0.
replace (1 / 2) with (powerRZ 2 (-1)). reflexivity.
simpl; nra.
replace (powerRZ 2 (- n)) with 
(1 / powerRZ 2 n). 
nra.
(apply neg_powerRZ); nra.
Qed.


Ltac solve_one_cond2 := 
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
simpl in H;
rewrite ?IZR_Zpower_pos in H;
rewrite ?mul_hlf_powerRZ in H);

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
  match goal with |- context [mk_env ?bmap' ?vmap' ?ty ?v'] =>
       match goal with H: Maps.PTree.get ?v vmap' = _ |- _ =>
         change (mk_env bmap' vmap' ty v') with (mk_env bmap' vmap' ty v);
         let x := fresh "x" in set (x := mk_env _ vmap' _ v); 
         hnf in x;
             compute in x; subst x; 
         try (cbv in H; inversion H; clear H; subst)
  end end; 
 repeat change (B2R (fprec ?x) _) with (FT2R x);
 try apply lesseq_less_or_eq;
 rewrite ?Rmult_1_l
end.

Ltac get_conds2 :=
  match goal with 
    H0: boundsmap_denote ?bmap ?vmap 
      |- _ =>
      apply boundsmap_denote_e in H0;
      rewrite ?list_forall_Forall in *;
      rewrite list_forall_Forall in H0;
      rndval_replace; subst;
      prepare_assumptions_about_free_variables;

match goal with |- List.Forall (eval_cond2 _ ?M) _ =>
   let m := fresh "m" in set (m:=M); compute in m; subst m;
  fold Tsingle; fold Tdouble
end;
repeat
    match goal with |- context [ type_lub ?a ?b ] =>
     first [change (type_lub a b) with Tsingle 
            |change (type_lub a b) with Tdouble]
    end
end.

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

Lemma powerRZ_pos_sub2: 
forall (x : R) (n m : positive),
     x <> 0 ->
     x ^ Pos.to_nat n * / x ^ Pos.to_nat m = powerRZ x (Z.pos_sub n m).
Proof. 
intros; symmetry; apply powerRZ_pos_sub; auto. Qed.


Lemma mul_powerRZ (a:R) (n:Z) :
 a / powerRZ 2 n = a * powerRZ 2 (-n).
Proof.
replace (powerRZ 2 (- n)) with 
(1 / powerRZ 2 n). 
nra.
(apply neg_powerRZ); nra.
Qed.


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


Ltac get_rexp_with_eps_delt e :=
match goal with 
  H0: rndval_with_cond 0 (mempty (Tsingle, Normal)) ?e =  
  (?r, (?si2, ?s), ?p) |- _ =>
  rndval_replace;
  subst si2 s r;
  get_eps_delts

end.

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


Ltac fv_prepare_assumptions :=
match goal with
  H: boundsmap_denote (?bmap) (?vmap)
  |- _
  => 
assert (boundsmap_denote (bmap) (vmap)) as BMD by (apply H);
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
match goal with |- context [reval _ _ (mget (mset (?M) _ _))  = _ ] => 
  let m := fresh "m" in set (m:=M); compute in m; unfold reval;
  simpl rval; try (cbv [id]);
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
      rewrite ?powerRZ_pos_sub2;
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
end);
try change (fprec Tsingle) with 24%Z ;
try change (femax Tsingle) with 128%Z ;
repeat match goal with |- context [(/ ?b ^ Pos.to_nat ?p)] =>
let x:= (constr:(Z.opp ( Z.of_nat (Pos.to_nat p)))) in
set (x':= x) in *; simpl in x';
replace (/ b ^ Pos.to_nat p) with
(powerRZ b x') by
(try rewrite ?pow_powerRZ; try simpl; try nra); unfold x'; clear x'
end
end.


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
intros; pose proof Rabs_mult a b. rewrite -> H0. 
pose proof Rabs_pos_eq a H; auto; nra.  
Qed. 

Lemma abs_mul2:
 forall a b: R,
 0 <= b ->
 Rabs (a * b) =  b * Rabs a.
Proof.
intros; pose proof Rabs_mult a b. rewrite -> H0. 
pose proof Rabs_pos_eq b H. auto; nra.  
Qed. 

Lemma rabs_mul_t:
forall u a b c d: R ,
u <= a * Rabs(b) + c -> Rabs(b) <= d -> 0 <a -> u <= a * d + c.
Proof.
intros. nra.
Qed.

Lemma del_eps_reduce1 : 
forall a del eps: R,
a - (a*(1+del)+eps) = -a*del - eps.
Proof.
intros; field_simplify; reflexivity.
Qed.

Lemma del_eps_reduce2 : 
forall a c d d' del eps: R,
a*(c + d) - a*((c + d')*(1+del)+eps) = a*(d - d') - a*(c + d')*del - a* eps.
Proof.
intros; field_simplify; reflexivity.
Qed.

Lemma Rabs_le_inv2 (x y :  R):
0 <= Rabs x <= y -> - y <= x <= y.
Proof.
intros.
assert (Rabs x <= y) by nra;
pose proof Rabs_le_inv x y H0; assumption.
Qed.


Lemma leapfrog_stepx_is_finite:
  forall x v : float32,
  boundsmap_denote leapfrog_bmap  (leapfrog_vmap x v)->
  Binary.is_finite _ _(fval (leapfrog_env x v) x') = true.
Proof.
unfold optimize_div. 
intros; subst.
set (bmap:= leapfrog_bmap) in *.
hnf in bmap. simpl in bmap.
get_rndval_with_conds x'.
get_conds2.
repeat (apply List.Forall_cons; try apply List.Forall_nil;
try solve_one_cond2; 
try interval;
try interval with (i_bisect (FT2R Tsingle val_v), 
i_bisect (FT2R Tsingle val_x), i_taylor (FT2R Tsingle val_v), 
i_taylor (FT2R Tsingle val_x))
). 
get_rndval_with_cond_correct x' H0 H1 rndval s p.
replace (leapfrog_env x v) with (env_ (leapfrog_vmap x v)). 
+ apply e.
+ symmetry; apply lf_env_eq; apply H.
Qed.

Lemma leapfrog_stepv_is_finite:
  forall x v : float32,
  boundsmap_denote leapfrog_bmap (leapfrog_vmap x v)->
  Binary.is_finite _ _(fval (leapfrog_env  x v) v') = true.
Proof. 
intros; subst.
set (bmap:= leapfrog_bmap) in *.
hnf in bmap. simpl in bmap.
get_rndval_with_conds v'.
get_conds2.
repeat (apply List.Forall_cons; try apply List.Forall_nil;
try solve_one_cond2; 
try interval;
try interval with (i_bisect (FT2R Tsingle val_v), 
i_bisect (FT2R Tsingle val_x), i_taylor (FT2R Tsingle val_v), 
i_taylor (FT2R Tsingle val_x))
). 
repeat (apply List.Forall_cons; try apply List.Forall_nil;
try solve_one_cond2 (FT2R Tsingle val_x ) (FT2R Tsingle val_v )). 
get_rndval_with_cond_correct v' H0 H1 rndval s p.
replace (leapfrog_env  x v) with (env_ (leapfrog_vmap x v)). 
+ apply e.
+ symmetry; apply lf_env_eq; apply H.
Qed.

Lemma leapfrog_stepx_not_nan:
  forall x v : float32,
  boundsmap_denote leapfrog_bmap (leapfrog_vmap x v)->
  Binary.is_nan _ _(fval (leapfrog_env x v) x') = false.
Proof. 
intros; subst;
apply is_finite_not_is_nan.
apply leapfrog_stepx_is_finite; auto. 
Qed.

Lemma leapfrog_stepv_not_nan:
  forall x v : float32,
  boundsmap_denote leapfrog_bmap (leapfrog_vmap x v)->
  Binary.is_nan _ _(fval (leapfrog_env x v) v') = false.
Proof. 
intros; subst;
apply is_finite_not_is_nan.
apply leapfrog_stepv_is_finite; auto. 
Qed.

Lemma leapfrog_opt_stepx_is_finite:
  forall x v : float32,
  boundsmap_denote leapfrog_bmap (leapfrog_vmap x v)->
  Binary.is_finite _ _ (fval (leapfrog_env x v) (optimize_div x')) = true.
Proof.
intros.
set (env:=(leapfrog_env x v)) in *. 
pose proof 
  (optimize_div_correct' env x' (leapfrog_stepx_not_nan x v H )).
pose proof 
  binary_float_eqb_is_finite (fval env x') 
    (fval env (optimize_div x'))
    (leapfrog_stepx_is_finite x v H) H0.
assumption.
Qed.

Lemma leapfrog_opt_stepv_is_finite:
  forall x v : float32,
  boundsmap_denote leapfrog_bmap (leapfrog_vmap x v)->
  Binary.is_finite _ _ (fval (leapfrog_env  x v) (optimize_div v')) = true.
Proof.
intros.
set (env:=(leapfrog_env x v)) in *.
pose proof 
  binary_float_eqb_is_finite (fval env v') 
    (fval env (optimize_div v')) 
    (leapfrog_stepv_is_finite x v H)
    (optimize_div_correct' env v' (leapfrog_stepv_not_nan x v H)).
assumption.
Qed.

Lemma error_reduce a b c d :
a - (b * (1 + c) + d) = 
(a - b )  - b * c - d.
Proof.
intros.
nra.
Qed.


Definition iternF  (n:nat) (x v :float32) :=  leapfrog' (x%F32, v%F32) n.
Definition iternR (n:nat) (x v :R) :=  leapfrogR (x,v) n .

Lemma step_iternR : 
  forall n : nat,
  forall x v : R,
  (iternR (S n) x v) = leapfrog_stepR (iternR n x v).
Proof.
intros; unfold iternR; 
rewrite ?lfn_eq_lfstepR; 
congruence.
Qed.

Lemma step_iternF : 
  forall n : nat,
  forall x v : float32,
  (iternF (S n) x v) = leapfrog_step' (iternF n x v).
Proof.
intros; unfold iternF; 
rewrite ?lfn_eq_lfstep; 
congruence.
Qed.

Lemma Rabs_triang_aux : 
  forall a b c : R,
  Rabs a + Rabs b <= c ->
  Rabs( a + b ) <= c.
Proof.
intros.
pose proof Rabs_triang a b.
pose proof Rle_trans _ _ _ H0 H; assumption.
Qed.


Lemma Rabs_triang_aux2 : 
  forall a b c d : R,
  Rabs a + Rabs b + Rabs c <= d ->
  Rabs (a + b) + Rabs c <= d.
Proof.
intros.
assert (Rabs (a + b) + Rabs c <= Rabs a + Rabs b + Rabs c).
pose proof Rcomplements.Rle_minus_r 
  (Rabs (a + b)) (Rabs a + Rabs b + Rabs c) (Rabs c); destruct H0. 
try apply H0; field_simplify; apply Rabs_triang.
try pose proof Rle_trans _ _ d H0 H; assumption.
Qed.

Lemma Rabs_triang_aux3 : 
  forall a b c x y z : R,
  Rabs a <= x ->
  Rabs b <= y ->
  Rabs c <= z ->
  Rabs a + Rabs b + Rabs c <= x + y +z.
Proof. intros; nra. Qed.

(*
Lemma local_error_x :
  forall x v : float32,
  forall x1 v1 : R,
  boundsmap_denote leapfrog_bmap (leapfrog_vmap x v)->
  x1 = B2R _ _ x ->
  v1 = B2R _ _ v -> 
    Rle (Rabs (Rminus (fst(leapfrog_stepR (x1,v1))) 
    (B2R _ _ (leapfrog_stepx x v)))) 
    error_x.
Proof.
intros.
replace (fst (leapfrog_stepR (x1,v1))) with 
  (rval (leapfrog_env x v) (optimize_div e1)).
+ replace (B2R 24 128 (leapfrog_stepx x v)) with
  (B2R _ _(fval (leapfrog_env x v) (optimize_div e1))).
  - pose proof one_step_errorx x v H; apply H2.
  - rewrite <- env_fval_reify_correct_leapfrog_step_x; 
  pose proof optimize_div_correct' (leapfrog_env x v) e1 
  (leapfrog_stepx_not_nan x v H);
revert H2;
generalize (fval (leapfrog_env x v) (optimize_div e1));
rewrite optimize_div_type; intros;
apply binary_float_eqb_eq in H2; subst; reflexivity.
+ rewrite (@env_rval_reify_correct_leapfrog_stepx x v x1 v1); auto.
Qed.

Lemma local_error_v:
  forall x v : float32,
  forall x1 v1 : R,
  boundsmap_denote leapfrog_bmap (leapfrog_vmap x v)->
  x1 = B2R _ _ x ->
  v1 = B2R _ _ v -> 
    Rle (Rabs (Rminus (snd(leapfrog_stepR (x1,v1))) 
    (B2R _ _ (leapfrog_stepv x v)))) 
    error_v.
Proof.
intros.
replace (snd (leapfrog_stepR (x1,v1))) with 
  (rval (leapfrog_env x v) (optimize_div e2)).
+ replace (B2R 24 128 (leapfrog_stepv x v)) with
  (B2R _ _(fval (leapfrog_env x v) (optimize_div e2))).
  - pose proof one_step_errorv x v H. apply H2.
  - rewrite <- env_fval_reify_correct_leapfrog_step_v; 
  pose proof optimize_div_correct' (leapfrog_env x v) e2 
  (leapfrog_stepv_not_nan x v H);
revert H2;
generalize (fval (leapfrog_env x v) (optimize_div e2));
rewrite optimize_div_type; intros;
apply binary_float_eqb_eq in H2; subst; reflexivity.
+ rewrite (@env_rval_reify_correct_leapfrog_stepv x v x1 v1); auto.
Qed.

*)



