From Flocq Require Import Binary Bits Core.
From compcert.lib Require Import IEEE754_extra Coqlib Floats Zbits Integers.

Require Import float_lib.

Require vcfloat.Test.
Require Import vcfloat.FPLang.

Definition SterbenzSub32 := Float32.sub.
Definition SterbenzSub := Float.sub.

Definition placeholder32: AST.ident -> float32. intro. apply Float32.zero. Qed.

Ltac reify_float_expr E :=
 match E with
 | placeholder32 ?i => constr:(@Var AST.ident Tsingle i)
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
 | _ =>  let E' := eval red in E in reify_float_expr E'
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

Ltac unfold_reflect E := 
match goal with |- context [fval (list_to_env ?L) E] =>
 pattern (fval (list_to_env L) E);
 let HIDE := fresh "HIDE" in match goal with |- ?A _ => set (HIDE:=A) end;
 let m := fresh "m" in let m' := fresh "m'" in
 set (m := list_to_env L);
 hnf in m;
 set (m' := (Maps.PTree_Properties.of_list L)) in m;
 hnf in m'; simpl in m';
 let e' := eval hnf in E in change E with e';
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
 subst m' m;
 subst HIDE; cbv beta
end.





