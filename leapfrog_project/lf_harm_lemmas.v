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








