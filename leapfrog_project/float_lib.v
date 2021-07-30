From Flocq Require Import Binary Bits Core.
From compcert.lib Require Import IEEE754_extra Coqlib Floats Zbits Integers.

Require vcfloat.Test.

Local Transparent Float32.of_bits.
Local Transparent Float32.div.
Local Transparent Float32.neg.
Local Transparent Float32.mul.
Local Transparent Float32.add.
Local Transparent Float32.sub.

Definition float32_of_Z : Z -> float32 := BofZ 24 128 eq_refl eq_refl.
Definition float_of_Z : Z -> float := BofZ 53 1024 eq_refl eq_refl.

Coercion float32_of_Z: Z >-> float32.
Coercion float_of_Z: Z >-> float.

Declare Scope F32.
Delimit Scope F32 with F32.

Notation "x + y" := (Float32.add x y) (at level 50, left associativity) : F32.
Notation "x - y"  := (Float32.sub x y) (at level 50, left associativity) : F32.
Notation "x * y"  := (Float32.mul x y) (at level 40, left associativity) : F32.
Notation "x / y"  := (Float32.div x y) (at level 40, left associativity) : F32.
Notation "- x" := (Float32.neg x) (at level 35, right associativity) : F32.

Notation "x <= y" := (Float32.cmp Cle x y = true) (at level 70, no associativity) : F32.
Notation "x < y" := (Float32.cmp Clt x y = true) (at level 70, no associativity) : F32.
Notation "x >= y" := (Float32.cmp Cge x y = true) (at level 70, no associativity) : F32.
Notation "x > y" := (Float32.cmp Cgt x y = true) (at level 70, no associativity) : F32.

Notation "x <= y <= z" := (x <= y /\ y <= z)%F32 (at level 70, y at next level) : F32.
Notation "x <= y < z" := (x <= y /\ y < z)%F32 (at level 70, y at next level) : F32.
Notation "x < y < z" := (x < y /\ y < z)%F32 (at level 70, y at next level) : F32.
Notation "x < y <= z" := (x < y /\ y <= z)%F32 (at level 70, y at next level) : F32.

Ltac eq_hnf := 
 lazymatch goal with |- ?A = ?B =>
   let x := fresh "x" in
    set (x:=A); hnf in x; subst x;
    set (x:=B); hnf in x; subst x
 end.
 
Ltac prove_float_constants_equal :=
 lazymatch goal with
 | |- @eq ?t ?A ?B =>
   let y := eval hnf in t in 
   lazymatch y with
   | option ?u => let u' := eval hnf in u in match u' with binary_float _ _ => idtac end
   | binary_float _ _ => idtac
   | _ => fail "prove_float_constants_equal is meant to be used on equality goals at type (binary_float _ _) but this goal is an equality at type" t
   end;
    eq_hnf;
    match t with option _ => f_equal | _ => idtac end;
    apply B2FF_inj; reflexivity
  | _ => fail "prove_float_constants_equal is meant to be used on equality goals at type (binary_float _ _)"
  end.

Require Import Lra Lia.

Lemma mul_one: forall x : float32, 
  Binary.is_finite 24 128 x = true ->
  Float32.mul x 1%Z = x.
Proof.
intros.
destruct x; try solve [simpl; rewrite ?xorb_false_r; try discriminate; try reflexivity].
clear H.
apply B2FF_inj.
simpl.
rewrite B2FF_FF2B.
rewrite xorb_false_r.
rewrite Pos2Z.inj_mul.
change 8388608%Z with (radix_val radix2 ^ 23).
unfold Binary.bounded in e0.
rewrite andb_true_iff in e0.
destruct e0.
apply Z.leb_le in H0.
unfold canonical_mantissa in H.
apply Zeq_bool_eq in H.
unfold FLT_exp in H.
rewrite Digits.Zpos_digits2_pos in H.
set (d := Digits.Zdigits radix2 _) in *.
(* should be provable from here . . ., but what a pain! *)
Admitted.

Lemma is_finite_negate:
  forall x, Binary.is_finite 24 128 x = true ->
   Binary.is_finite 24 128 (Float32.neg x)  = true .
Proof.
intros.
change Float32.neg with (Bopp 24 128 Float32.neg_nan).
rewrite Binary.is_finite_Bopp; auto.
Qed.

Lemma mul_minusone_negate:
 forall x, 
    Binary.is_finite 24 128 x = true ->
   Float32.mul (Float32.neg 1) x = Float32.neg x.
Admitted.

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






