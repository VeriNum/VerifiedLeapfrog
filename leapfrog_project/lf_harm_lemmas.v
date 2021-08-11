(* The purpose of this file, to the extent it's needed at all, is to
   PROVIDE LEMMAS ABOUT THE FUNCTIONAL MODEL, NEEDED IN
   Functional-model-to-C REFINEMENT PROOF  in verif_lfharm.v. 
   Because we do NOT want to import the entire
  VCFloat system into C program verifications, this file SHOULD NOT
  Require vcfloat.anything, even indirectly.
*)

From Flocq Require Import Binary Bits Core.
From compcert.lib Require Import IEEE754_extra Coqlib Floats Zbits Integers.
Require Import float_lib lf_harm_float.
Require compcert.common.AST.

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

Lemma leapfrog_step_is_finite:
  forall n, 0 <= n < 100 ->
          Binary.is_finite 24 128 (fst (Z.iter n leapfrog_step (initial_x, initial_v))) = true.
Abort.  (* true, but no longer needed *)

Definition leapfrog_stepx x v := fst (leapfrog_step (x,v)).

(*
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
*)





