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
Search Digits.Zdigits.
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








