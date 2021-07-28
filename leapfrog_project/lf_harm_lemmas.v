From Flocq Require Import Binary Bits Core.
From compcert.lib Require Import IEEE754_extra Coqlib Floats Zbits Integers.
Require Import lf_harm_float.

Transparent Float32.of_bits.
Transparent Float32.div.
Transparent Float32.neg.
Transparent Float32.mul.
Transparent Float32.add.

Definition initial_x := float32_of_Z 1.
Definition initial_v := Float32.zero.
Definition initial_t := Float32.zero.

Definition half := Float32.div (float32_of_Z 1) (float32_of_Z 2).

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

Lemma half_repr : Float32.of_bits (Int.repr 1056964608) =  half.
Proof. prove_float_constants_equal. Qed.

Lemma neg1_repr: 
  Float32.neg (Float32.of_bits (Int.repr 1065353216)) =
   float32_of_Z (- (1)).
Proof.  prove_float_constants_equal. Qed.

Lemma exact_inverse_two: Float32.exact_inverse (float32_of_Z 2) = Some half.
Proof.  prove_float_constants_equal. Qed.

Lemma mul_one: forall x : float32, 
  Binary.is_finite 24 128 x = true ->
  Float32.mul x (float32_of_Z 1) = x.
Proof.
Admitted.

Lemma is_finite_negate:
  forall x, Binary.is_finite 24 128 x = true ->
   Binary.is_finite 24 128 (Float32.neg x)  = true .
Proof.
intros.
unfold Float32.neg.
rewrite Binary.is_finite_Bopp; auto.
Qed.

Lemma mul_minusone_negate:
 forall x, 
    Binary.is_finite 24 128 x = true ->
   Float32.mul (Float32.neg (float32_of_Z 1)) x = Float32.neg x.
Admitted.

Lemma leapfrog_step_is_finite:
  forall n, 0 <= n < 100 ->
          Binary.is_finite 24 128 (fst (Z.iter n leapfrog_step (initial_x, initial_v))) = true.
Admitted.








