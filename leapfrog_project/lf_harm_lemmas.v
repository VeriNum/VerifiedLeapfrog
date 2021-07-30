From Flocq Require Import Binary Bits Core.
From compcert.lib Require Import IEEE754_extra Coqlib Floats Zbits Integers.
Require Import float_lib lf_harm_float.

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


Definition leapfrog_stepx x v :=
(  let x' := (x + h * v) + (h * h * F x) / 2%Z in
  let v' :=  v + (h*(F x + F x')/2%Z) in x' )%F32.

   
Import ListNotations.
Definition _x : AST.ident := 5%positive.
Definition _v : AST.ident := 7%positive.

Definition e := ltac:(let e' := reify_float_expr constr:((float32_of_Z 1 / float32_of_Z 32)%F32 ) in exact e').
Definition e1 := ltac:(let e' := HO_reify_float_expr constr:([_x; _v]) leapfrog_stepx in exact e').
Print e1.

Import FPLang.

Lemma reify_correct_leapfrog_stepx:
  forall x v : float32,
  fval (list_to_env [(_x, Values.Vsingle x);(_v, Values.Vsingle v)]) e1 = leapfrog_stepx x v.
Proof.
intros.
unfold_reflect e1.
reflexivity.
Qed.






