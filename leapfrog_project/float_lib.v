(* The purpose of this file is to 
   PROVIDE A LIBRARY FOR FUNCTIONAL MODELS.  Then we will 
   write functional models of floating-point computations, and prove,
   (1) The C program refines the functional model
   (2) This functional model computes a good approximation to the real number we want.
   Because we do NOT want to import the entire
  VCFloat system into C program verifications, this file SHOULD NOT
  Require vcfloat.anything, even indirectly.
*)

From Flocq Require Import Binary Bits Core.
From compcert.lib Require Import IEEE754_extra Coqlib Floats Zbits Integers.

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
Declare Scope F64.
Delimit Scope F64 with F64.

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

Notation "x + y" := (Float.add x y) (at level 50, left associativity) : F64.
Notation "x - y"  := (Float.sub x y) (at level 50, left associativity) : F64.
Notation "x * y"  := (Float.mul x y) (at level 40, left associativity) : F64.
Notation "x / y"  := (Float.div x y) (at level 40, left associativity) : F64.
Notation "- x" := (Float.neg x) (at level 35, right associativity) : F64.

Notation "x <= y" := (Float.cmp Cle x y = true) (at level 70, no associativity) : F64.
Notation "x < y" := (Float.cmp Clt x y = true) (at level 70, no associativity) : F64.
Notation "x >= y" := (Float.cmp Cge x y = true) (at level 70, no associativity) : F64.
Notation "x > y" := (Float.cmp Cgt x y = true) (at level 70, no associativity) : F64.

Notation "x <= y <= z" := (x <= y /\ y <= z)%F64 (at level 70, y at next level) : F64.
Notation "x <= y < z" := (x <= y /\ y < z)%F64 (at level 70, y at next level) : F64.
Notation "x < y < z" := (x < y /\ y < z)%F64 (at level 70, y at next level) : F64.
Notation "x < y <= z" := (x < y /\ y <= z)%F64 (at level 70, y at next level) : F64.


Ltac eq_hnf := 
 lazymatch goal with |- ?A = ?B =>
   let x := fresh "x" in
    set (x:=A); hnf in x; subst x;
    set (x:=B); hnf in x; subst x
 end.
 
Definition f_lit (s: string) {T: Type} {x: T} := x.

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
   Float32.mul (Float32.neg 1) x = Float32.neg x.
Proof.
(* Almost certainly true, but a royal pain to prove. *)
Abort.


(* BEGIN system for parsing and rewriting floating-point literals.

  FEATURE 1: literals expressed on C notation.
  How to use it: In notation scope F32 or F64, the term  ($ s) 
  produces a fully reduced floating-point value of type float32 or float,
  where the string s is a floating-point literal in C standard notation.
  Examples: $"0.5f", $".5f", $"5E-1f" all produce the float32 value 1/2;
      $"0.5", $".5", $"5E-1" all produce the 64-bit float value 1/2.
  Important:  No matter whether you're in Notation Scope F32 or F64,
  $"0.5" is a 64-bit floating point constant whose type is [float], and
  $"0.5f" is a 32-bit floating point constant of type [float32].

  FEATURE 2: Clight abstract syntax trees contain a lot of 
  constants of the form, (Float32.of_bits (Int.repr 1065353216)).
  You might want to rewrite that into something like 
  (float_of_Z 1)  $"1.0f"  or   one     (assuming that "one" is your own
   Definition that unfolds to a floating-point constant).
 To do that, you can write any of these:

   Hint Rewrite float_const_rewrite "1.0f" : float_const.
   Hint Rewrite float_const_rewrite (float_of_Z 1) : float_const.
   Hint Rewrite float_const_rewrite one : float_const.

   float_const_rewrite is a tactic that takes an argument of type 
   string, or of type float32 or float.   It computes that argument [s]
   into a floating point constant, calculates an integer constant [n], 
   and produces the proof of an equation,
    Float32.of_bits (Int.repr n) = s
  which you can then use as a rule in a Hint Rewrite database.
  (or Float.bits, as appropriate, if s is a 64-bit float).

   It's a good idea to pick only one of the above, because otherwise
   you'll get 3 different rewrite rules all with the same l.h.s,
   which is not so useful.

*)

Definition Bparse_float32 := Bparse 24 128 (eq_refl _) (eq_refl _) 10.
Definition Bparse_float := Bparse 53 1024 (eq_refl _) (eq_refl _) 10.

Fixpoint parse_decimal (b: N) (len: N) (s: string) : N * N * string :=
 match s with
 | EmptyString => (b,len,s)
 | String c r => let c' := Ascii.N_of_ascii c in
             if andb (N.leb 48 c') (N.ltb c' 58) 
             then parse_decimal (b*10+c'-48)%N  (len+1) r
             else (b,len,s)
 end.
 
Import Ascii.
Import ListNotations.
Require compcert.common.Errors.

Inductive float_type := ft_single | ft_double.

Definition parse_float_exponent'  (sign:bool) (mantissa: N) (len2: N) (esign: Z) (e len3: N) (ft: float_type) : 
             Errors.res (bool * option (positive*Z) * float_type) :=
          if N.eqb len3 0 
                     then Errors.Error [Errors.MSG "No digits in exponent"]
                   else if N.eqb mantissa 0 then Errors.OK(sign,None,ft)
                   else Errors.OK(sign,Some(Pos.pred (N.succ_pos mantissa),
                                          esign * Z.of_N e - Z.of_N len2), ft).

Definition parse_float_exponent (sign:bool) (mantissa: N) (len1 len2: N) (esign: Z) (s: string) : 
             Errors.res (bool * option (positive*Z) * float_type) :=
  if N.eqb (len1+len2) 0
  then Errors.Error [Errors.MSG "No digits before or after decimal point"]
  else match parse_decimal 0 0 s with
          | (_,0%N, _) => Errors.Error [Errors.MSG "Missing exponent"]
          | (e,len3,EmptyString) => parse_float_exponent' sign mantissa len2 esign e len3 ft_double
          | (e,len3,String ("f"|"F") EmptyString) => parse_float_exponent' sign mantissa len2 esign e len3 ft_single
          | (e,len3,String ("f"|"F") _) => Errors.Error [Errors.MSG "Junk after f suffix"]
          | (_,_, String _ _) => Errors.Error [Errors.MSG "Junk after exponent"]
          end.

Definition parse_float_noexponent (sign:bool) (mantissa: N) (len1 len2: N) (ft: float_type) : 
             Errors.res (bool * option (positive*Z) * float_type) :=
     if N.eqb mantissa 0
        then if N.eqb (len1+len2) 0
                       then Errors.Error [Errors.MSG "No digits before or after decimal point"]
                       else Errors.OK (sign,None,ft)
                    else Errors.OK (sign, Some
                                  (Pos.pred (N.succ_pos mantissa),
                                  (- Z.of_N len2)), ft).

Definition parse_float_mantissa2 (sign: bool) (mantissa: N) (len1 len2: N) (s: string) : 
             Errors.res (bool * option (positive*Z) * float_type) :=
 match s with
 | String ("e"|"E") (String "+" r) => parse_float_exponent sign mantissa len1 len2 1 r
 | String ("e"|"E") (String "-" r) => parse_float_exponent sign mantissa len1 len2 (-1) r
 | String ("e"|"E") r => parse_float_exponent sign mantissa len1 len2 1 r
 | EmptyString => parse_float_noexponent sign mantissa len1 len2 ft_double
 | String ("f"|"F") EmptyString => parse_float_noexponent sign mantissa len1 len2 ft_single
 | _ => Errors.Error [Errors.MSG "Cannot parse the rest of this float:"; Errors.MSG s]
 end.

Definition parse_float_mantissa1 (sign: bool) (s: string) :
             Errors.res (bool * option (positive*Z) * float_type) :=
 let '(i,len1,s1) := parse_decimal 0%N 0 s in
 match s1 with 
 | String "." r => let '(j,len2,s2) := parse_decimal i 0 r in
                          parse_float_mantissa2 sign j len1 len2 s2
 | _ => parse_float_mantissa2 sign i len1 0 s1
 end.

Definition parse_float (s: string) :=
 match s with
 | String "+" r => parse_float_mantissa1 true r
 | String "-" r => parse_float_mantissa1 false r
 | _ => parse_float_mantissa1 true s
 end.

Ltac f_lit_exact s x := let y := eval simpl in x in exact (@f_lit s _ y).

Ltac f_lit_aux cont s :=
 let r := constr:(parse_float s) in
 let r := eval vm_compute in r in
 lazymatch r with
 | Errors.Error ?c => fail 0 c
 | Errors.OK (?p, None,ft_single) => 
  lazymatch p with
  | true => cont s constr:(Float32.zero)
  | false =>cont s constr:(Float32.neg Float32.zero)
 end
 | Errors.OK (?p, None,ft_double) => 
  lazymatch p with
  | true => cont s constr:(Float.zero)
  | false =>cont s constr:(Float.neg Float.zero)
 end
 | Errors.OK (?p, Some (?m,?e),ft_single) =>
   let x := constr:(Bparse_float32 m e) in
   let x := eval hnf in x in 
   let x := eval simpl in x in 
  lazymatch p with
  | true => cont s x
  | false =>cont s (Float32.neg x)
 end 
 | Errors.OK (?p, Some (?m,?e),ft_double) =>
   let x := constr:(Bparse_float m e) in
   let x := eval hnf in x in 
   let x := eval simpl in x in 
  lazymatch p with
  | true => cont s x
  | false =>cont s (Float.neg x)
 end 
end.

Ltac f_lit s := f_lit_aux f_lit_exact s.

Lemma constant_rewrite32 (x: float32):
  forall n, n = Bits.bits_of_b32 x ->
  Float32.of_bits (Int.repr n) = x.
Proof.
 intros. subst.
 cbv delta [Float32.of_bits]; cbv beta.
 rewrite Int.unsigned_repr.
 unfold Bits.b32_of_bits.
 unfold Bits.bits_of_b32.
 rewrite Bits.binary_float_of_bits_of_binary_float.
 auto.
 unfold Bits.bits_of_b32.
 assert (Int.max_unsigned + 1 = Int.modulus) by reflexivity.
 assert (0 <= Bits.bits_of_binary_float 23 8 x < Int.modulus); [ | lia].
 clear H.
 apply Bits.bits_of_binary_float_range; reflexivity.
Qed.

Lemma constant_rewrite64 (x: float):
  forall n, n = Bits.bits_of_b64 x ->
  Float.of_bits (Int64.repr n) = x.
Proof.
 intros. subst.
 cbv delta [Float.of_bits]; cbv beta.
 rewrite Int64.unsigned_repr.
 unfold Bits.b64_of_bits.
 unfold Bits.bits_of_b64.
 rewrite Bits.binary_float_of_bits_of_binary_float.
 auto.
 unfold Bits.bits_of_b64.
 assert (Int64.max_unsigned + 1 = Int64.modulus) by reflexivity.
 assert (0 <= Bits.bits_of_binary_float 52 11 x < Int64.modulus); [ | lia].
 clear H.
 apply Bits.bits_of_binary_float_range; reflexivity.
Qed.

Ltac compute_Float_bits f h :=
 let h := eval hnf in h in 
 let h' := eval cbv [Float32.zero Float32.div Float32.mul Float32.add Float32.sub Float32.neg
                             Float.zero Float.div Float.mul Float.add Float.sub Float.neg]
                              in h in
  let n := constr:(f h') in
           let n' := eval compute in n in constr:(n').

Ltac float_const h :=
 match type of h with
 | string => 
          f_lit_aux f_lit_x h
 | ?t =>
 tryif unify t float32 
 then let n := compute_Float_bits Bits.bits_of_b32 h in
     exact (constant_rewrite32 h n (eq_refl _))
 else  tryif unify t float 
 then let n := compute_Float_bits Bits.bits_of_b64 h in
          exact (constant_rewrite64 h n (eq_refl _))
 else fail 0  "This expression does not have type float or float32:" h
 end
with f_lit_x s x :=
  let y := eval simpl in x in float_const (@f_lit s _ y).



Module FloatLiteralNotation.
 Notation "$ s" := (ltac:(f_lit s%string)) (at level 1, only parsing) : F32.
 Notation "$ s" := (ltac:(f_lit s%string)) (at level 1, only parsing) : F64.
 Notation "'float_const_rewrite' s" := (ltac:(float_const s%string)) (at level 1, only parsing).
End FloatLiteralNotation.

Import FloatLiteralNotation.

Local Open Scope F32.

(* Unit tests *)

Goal $"0f" =  Float32.zero.
prove_float_constants_equal. Abort.
Goal $"0e6f"  =  Float32.zero.
prove_float_constants_equal. Abort.
Goal $"-0.5f"  =  Float32.neg (Float32.div 1 2).
prove_float_constants_equal. Abort.
Goal $".5f"  =  Float32.div 1 2.
prove_float_constants_equal. Abort.
Goal $".05E1f"  =  Float32.div 1 2.
prove_float_constants_equal. Abort.
Goal $".05E+1f"  =  Float32.div 1 2.
prove_float_constants_equal. Abort.
Goal $".05E+1"  =  Float.div 1 2.
prove_float_constants_equal. Abort.
Goal $"5E-1"  =  Float.div 1 2.
prove_float_constants_equal. Abort.
Goal $"1.5F"  =  (Float32.div 3 2).
prove_float_constants_equal. Abort.

Ltac test_flit_error s e :=
 let r := constr:(parse_float s) in
 let r := eval compute in r in
 lazymatch r with
 | Errors.Error ?c => 
   tryif unify c (map Errors.MSG e) then exact True else fail 0 c
 end.

Local Open Scope string.
Goal ltac:(test_flit_error "." ["No digits before or after decimal point"]). Abort.
Goal ltac:(test_flit_error "3g." ["Cannot parse the rest of this float:";"g."]). Abort.

Goal False.
assert (H := float_const_rewrite "0").
match type of H with Float.of_bits (Int64.repr 0) = f_lit "0" => idtac end.
Abort.

Goal False.
assert (H := float_const_rewrite (float_of_Z 1)).
match type of H with Float.of_bits (Int64.repr _) = float_of_Z 1 => idtac end.
Abort.

Goal False.
assert (H := float_const_rewrite (float32_of_Z 1)).
match type of H with Float32.of_bits (Int.repr _) = float32_of_Z 1 => idtac end.
Abort.

(* END system for parsing floating-point literals *)





