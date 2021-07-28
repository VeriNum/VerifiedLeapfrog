From Flocq Require Import Binary Bits Core.
From compcert.lib Require Import IEEE754_extra Coqlib Floats Zbits Integers.

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

Lemma mul_one: forall x : float32, 
  Binary.is_finite 24 128 x = true ->
  Float32.mul x 1 = x.
Proof.
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








