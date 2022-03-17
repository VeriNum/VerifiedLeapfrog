From Flocq Require Import Binary Bits Core.
From compcert.lib Require Import IEEE754_extra Coqlib Floats Zbits Integers.

(*Require Import float_lib.*)

From vcfloat Require Export FPCore FPLang FPLangOpt Rounding Automate Reify Float_notations.

(*
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
*)
