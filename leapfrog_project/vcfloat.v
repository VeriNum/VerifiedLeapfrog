From Flocq Require Import Binary Bits Core.
From compcert.lib Require Import IEEE754_extra Coqlib Floats Zbits Integers.

Require Import float_lib.

Require Import vcfloat.Test.
Require Import vcfloat.FPLang.
Require Import vcfloat.FPLangOpt.


Definition SterbenzSub32 := Float32.sub.
Definition SterbenzSub   := Float.sub.

Definition placeholder32: AST.ident -> float32. intro. apply Float32.zero. Qed.

Module B_Float_Notations.

Declare Scope float1_scope.
Delimit Scope float1_scope with F1.
Declare Scope float2_scope.
Delimit Scope float2_scope with F2.

Notation "x + y" := (Bplus (fprec Tsingle) (femax Tsingle) eq_refl eq_refl (plus_nan _) mode_NE x y) (at level 50, left associativity) : float1_scope.
Notation "x - y"  := (Bminus (fprec Tsingle) (femax Tsingle) eq_refl eq_refl (plus_nan _) mode_NE x y) (at level 50, left associativity) : float1_scope.
Notation "x * y"  := (Bmult (fprec Tsingle) (femax Tsingle) eq_refl eq_refl (mult_nan _) mode_NE x y) (at level 40, left associativity) : float1_scope.
Notation "x / y"  := (Bdiv (fprec Tsingle) (femax Tsingle) eq_refl eq_refl (div_nan _) mode_NE x y) (at level 40, left associativity) : float1_scope.
Notation "- x" := (Bopp (fprec Tsingle) (femax Tsingle) (opp_nan _) x) (at level 35, right associativity) : float1_scope.

Notation "x + y" := (Bplus (fprec Tdouble) (femax Tdouble) eq_refl eq_refl (plus_nan _) mode_NE x y) (at level 50, left associativity) : float2_scope.
Notation "x - y"  := (Bminus (fprec Tdouble) (femax Tdouble) eq_refl eq_refl (plus_nan _) mode_NE x y) (at level 50, left associativity) : float2_scope.
Notation "x * y"  := (Bmult (fprec Tdouble) (femax Tdouble) eq_refl eq_refl (mult_nan _) mode_NE x y) (at level 40, left associativity) : float2_scope.
Notation "x / y"  := (Bdiv (fprec Tdouble) (femax Tdouble) eq_refl eq_refl (div_nan _) mode_NE x y) (at level 40, left associativity) : float2_scope.
Notation "- x" := (Bopp (fprec Tdouble) (femax Tdouble) (opp_nan _) x) (at level 35, right associativity) : float2_scope.

End B_Float_Notations.


Ltac ground_pos p := 
 match p with
 | Z.pos ?p' => ground_pos p'
 | xH => constr:(tt) 
 | xI ?p' => ground_pos p' 
 | xO ?p' => ground_pos p' 
 end.

Ltac find_type prec emax :=
 match prec with
 | 24%Z => match emax with 128%Z => constr:(Tsingle) end
 | 53%Z => match emax with 1024%Z => constr:(Tdouble) end
 | Z.pos ?precp => 
     let g := ground_pos precp in let g := ground_pos emax in 
     constr:(TYPE precp emax (ZLT_intro prec emax (eq_refl _)) (BOOL_intro _ (eq_refl _)))
 end.

Definition Zconst (t: type) : Z -> ftype t :=
  BofZ (fprec t) (femax t) (Pos2Z.is_pos (fprecp t)) (fprec_lt_femax t).

Ltac reify_float_expr E :=
 match E with
 | placeholder32 ?i => constr:(@Var AST.ident Tsingle i)
 | cast ?tto _ ?f => constr:(@Unop AST.ident (CastTo tto None) f)
 | BofZ ?prec ?emax _ _ ?z => let t := find_type prec emax in
                                                 constr:(@Const AST.ident t (Zconst t z))
 | BofZ (fprec ?t) _ _ _ ?z => constr:(@Const AST.ident t (Zconst t z))
 | Zconst ?t ?z => constr:(@Const AST.ident t (Zconst t z))
 | BofZ _ _ _ _ => fail 1 "reify_float_expr failed on" E "because the prec,emax arguments must be either integer literals or of the form (fprec _),(femax _)"
 | Bplus _ _ _ _ mode_NE ?a ?b => let a' := reify_float_expr a in let b' := reify_float_expr b in 
                                      constr:(@Binop AST.ident (Rounded2 PLUS None) a' b')
 | Bminus _ _ _ _ mode_NE ?a ?b => let a' := reify_float_expr a in let b' := reify_float_expr b in 
                                      constr:(@Binop AST.ident (Rounded2 MINUS None) a' b')
 | Bmult _ _ _ _ mode_NE ?a ?b => let a' := reify_float_expr a in let b' := reify_float_expr b in 
                                      constr:(@Binop AST.ident (Rounded2 MULT None) a' b')
 | Bdiv _ _ _ _ mode_NE ?a ?b => let a' := reify_float_expr a in let b' := reify_float_expr b in 
                                      constr:(@Binop AST.ident (Rounded2 DIV None) a' b')
 | Bopp _ _ _ ?a => let a' := reify_float_expr a in 
                                      constr:(@Unop AST.ident (Exact1 Opp) a')
 | Babs _ _ _ ?a => let a' := reify_float_expr a in 
                                      constr:(@Unop AST.ident (Exact1 Abs) a')
 | Float.of_single ?f => constr:(@Unop AST.ident (CastTo Tdouble None) f)
 | Float.to_single ?f => constr:(@Unop AST.ident (CastTo Tsingle None) f)
 | float32_of_Z ?n => constr:(@Const AST.ident Tsingle (float32_of_Z n))
 | Float32.of_int ?i => constr:(@Const AST.ident Tsingle (float32_of_Z (Int.signed i)))
 | Float32.of_intu ?i => constr:(@Const AST.ident Tsingle (float32_of_Z (Int.unsigned i)))
 | Float32.of_long ?i => constr:(@Const AST.ident Tsingle (float32_of_Z (Int64.signed i)))
 | Float32.of_longu ?i => constr:(@Const AST.ident Tsingle (float32_of_Z (Int64.unsigned i)))
 | Float32.mul ?a ?b => let a' := reify_float_expr a in let b' := reify_float_expr b in 
                                      constr:(@Binop AST.ident (Rounded2 MULT None) a' b')
 | Float32.div ?a ?b => let a' := reify_float_expr a in let b' := reify_float_expr b in 
                                      constr:(@Binop AST.ident (Rounded2 DIV None) a' b')
 | Float32.add ?a ?b => let a' := reify_float_expr a in let b' := reify_float_expr b in 
                                      constr:(@Binop AST.ident (Rounded2 PLUS None) a' b')
 | Float32.sub ?a ?b => let a' := reify_float_expr a in let b' := reify_float_expr b in 
                                      constr:(@Binop AST.ident (Rounded2 MINUS None) a' b')
 | SterbenzSub32 ?a ?b => let a' := reify_float_expr a in let b' := reify_float_expr b in 
                                      constr:(@Binop AST.ident SterbenzMinus a' b')
 | Float32.neg ?a => let a' := reify_float_expr a in
                                      constr:(@Unop AST.ident (Exact1 Opp) a')
 | Float32.abs ?a => let a' := reify_float_expr a in
                                      constr:(@Unop AST.ident (Exact1 Abs) a')
 | b32_B754_finite _ _ _ _ => constr:(@Const AST.ident Tsingle E)
 | b64_B754_finite _ _ _ _ => constr:(@Const AST.ident Tdouble E)
 | float_of_Z ?n => constr:(@Const AST.ident Tsingle (float_of_Z n))
 | Float.of_int ?i => constr:(@Const AST.ident Tsingle (float_of_Z (Int.signed i)))
 | Float.of_intu ?i => constr:(@Const AST.ident Tsingle (float_of_Z (Int.unsigned i)))
 | Float.of_long ?i => constr:(@Const AST.ident Tsingle (float_of_Z (Int64.signed i)))
 | Float.of_longu ?i => constr:(@Const AST.ident Tsingle (float_of_Z (Int64.unsigned i)))
 | Float.mul ?a ?b => let a' := reify_float_expr a in let b' := reify_float_expr b in 
                                      constr:(@Binop AST.ident (Rounded2 MULT None) a' b')
 | Float.div ?a ?b => let a' := reify_float_expr a in let b' := reify_float_expr b in 
                                      constr:(@Binop AST.ident (Rounded2 DIV None) a' b')
 | Float.add ?a ?b => let a' := reify_float_expr a in let b' := reify_float_expr b in 
                                      constr:(@Binop AST.ident (Rounded2 PLUS None) a' b')
 | Float.sub ?a ?b => let a' := reify_float_expr a in let b' := reify_float_expr b in 
                                      constr:(@Binop AST.ident (Rounded2 MINUS None) a' b')
 | SterbenzSub ?a ?b => let a' := reify_float_expr a in let b' := reify_float_expr b in 
                                      constr:(@Binop AST.ident SterbenzMinus a' b')
                                  
 | Float.neg ?a => let a' := reify_float_expr a in
                                constr:(@Unop AST.ident (Exact1 Opp) a')
 | Float.abs ?a => let a' := reify_float_expr a in
                                constr:(@Unop AST.ident (Exact1 Abs) a')
 | _ => let E' := eval red in E in reify_float_expr E'
 | _ => fail 100 "could not reify" E
 end.

Ltac HO_reify_float_expr names E :=
 lazymatch names with
 | ?n :: ?names' =>
             let Ev := constr:(E (placeholder32 n)) in 
             HO_reify_float_expr names' Ev
 | nil =>reify_float_expr E
 end.

Definition list_to_env (bindings: list (AST.ident * Values.val)) : (forall ty : type, AST.ident -> ftype ty) .
pose (m :=   Maps.PTree_Properties.of_list bindings).
intros ty i.
destruct (type_eq_dec ty Tsingle); [ | destruct (type_eq_dec ty Tdouble)].
{
subst.
destruct (Maps.PTree.get i m); [ | exact Float32.zero].
destruct v; try exact f; exact Float32.zero.
}
{
subst.
destruct (Maps.PTree.get i m); [ | exact Float.zero].
destruct v; try exact f; exact Float.zero.
}
exact (B754_zero (fprec ty) (femax ty) false).
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
 subst HIDE; cbv beta
| |- context [fval ?env E] => let y := eval red in env in change env with y
end.


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
