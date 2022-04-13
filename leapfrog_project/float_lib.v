From Flocq Require Import Binary Bits Core.
From vcfloat Require Import FPCore FPLang FPLangOpt Rounding Automate Reify Float_notations.
From compcert.lib Require Import IEEE754_extra Coqlib Floats Zbits Integers.

(* MUST DO THE IMPORTS IN THIS ORDER
   because "float" is defined in two different modules
   and we want to end up with compcert.lib.Floats.float.
*)

Local Transparent Float32.of_bits.
Local Transparent Float32.div.
Local Transparent Float32.neg.
Local Transparent Float32.mul.
Local Transparent Float32.add.
Local Transparent Float32.sub.
 
Axiom prop_ext: ClassicalFacts.prop_extensionality.
Arguments prop_ext [A B] _.

Lemma proof_irr: ClassicalFacts.proof_irrelevance.
Proof.
  exact (ClassicalFacts.ext_prop_dep_proof_irrel_cic prop_ext).
Qed.
Arguments proof_irr [A] _ _.

Require Import Lra Lia.


Lemma mul_one: forall x : float32, 
  Binary.is_finite 24 128 x = true ->
  Float32.mul x 1%F32 = x.
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
Abort.

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
   Float32.mul (Float32.neg 1%F32) x = Float32.neg x.
Proof.
(* Almost certainly true, but a royal pain to prove. *)
Abort.


