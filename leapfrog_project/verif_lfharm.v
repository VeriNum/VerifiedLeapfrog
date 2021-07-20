Require Import VST.floyd.proofauto.
Require Import lfharm.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Open Scope logic.

Require Import lf_harm_float.

Definition force_spec :=
 DECLARE _force
 WITH xp: val, x : float
 PRE [ tptr tfloat ] PROP() PARAMS(xp) SEP(data_at Tsh tfloat (Vsingle x) xp)
 POST [ tfloat ] PROP() RETURN (Vsingle (F x)) 
                        SEP(data_at Tsh tfloat (Vsingle x) xp).

Definition lfstep_spec := 
  DECLARE _lfstep
  WITH xp: val, x: float, vp: val, v: float
  PRE [ tptr tfloat , tptr tfloat , tfloat ]
    PROP(Binary.is_finite_strict 24 128 x = true)
    PARAMS (xp; vp; Vsingle h)
    SEP(data_at Tsh tfloat (Vsingle x) xp; data_at Tsh tfloat (Vsingle v) vp )
  POST [ tvoid ]
    PROP()
    RETURN()
    SEP(data_at Tsh tfloat (Vsingle (fst(leapfrog_step (x,v)))) xp; 
          data_at Tsh tfloat (Vsingle (snd(leapfrog_step (x,v)))) vp ).

Definition initial_x := float_of_Z 1.
Definition initial_v := Float32.zero.
Definition initial_t := Float32.zero.

Definition integrate_spec := 
  DECLARE _integrate
  WITH xp: val, vp: val
  PRE [ tptr tfloat , tptr tfloat ]
    PROP()
    PARAMS (xp; vp)
    SEP(data_at_ Tsh tfloat xp; data_at_ Tsh tfloat vp )
  POST [ tvoid ]
    PROP()
    RETURN()
    SEP(data_at Tsh tfloat (Vsingle (fst(leapfrog (initial_x,initial_v) 100))) xp; 
          data_at Tsh tfloat (Vsingle (snd(leapfrog (initial_x,initial_v) 100))) vp ).

Definition main_spec :=
 DECLARE _main
  WITH gv: globals
  PRE  [] main_pre prog tt gv
  POST [ tint ]
       PROP() RETURN (Vint (Int.repr 0)) SEP(TT).

Definition Gprog : funspecs := [force_spec; lfstep_spec; integrate_spec; main_spec].

Lemma float_of_Z_one:
  float_of_Z 1 = Binary.Bone ms es (eq_refl _) (eq_refl _).
Proof.
 reflexivity.
Qed.

Definition half := Float32.div (float_of_Z 1) (float_of_Z 2).

Lemma half_repr : Float32.of_bits (Int.repr 1056964608) =  half.
Proof.
 Transparent Float32.of_bits.
 Transparent Float32.div.
 unfold Float32.of_bits, Float32.div.
 unfold float_of_Z.
 rewrite Int.unsigned_repr by computable.
 unfold IEEE754_extra.BofZ.
 unfold ms, es. simpl.
 unfold Bits.b32_of_bits.
unfold Bits.binary_float_of_bits.
 unfold Binary.FF2B.
 simpl.
 change (Z.pow_pos 2 7) with 128.
 change (2147483648 <=? 1056964608) with false.
 unfold FLT.FLT_exp.
 simpl Z.max.
apply Binary.B2R_inj.
reflexivity. reflexivity. reflexivity.
Qed.

Lemma neg1_repr: 
  Float32.neg (Float32.of_bits (Int.repr 1065353216)) =
   float_of_Z (- (1)).
Proof.
Transparent Float32.neg.
Transparent Float32.of_bits.
unfold Float32.neg, Float32.of_bits.
unfold float_of_Z.
apply Binary.B2R_inj.
reflexivity.
reflexivity.
rewrite Binary.B2R_Bopp.
rewrite Int.unsigned_repr by computable.
simpl.
rewrite <- Operations.F2R_opp.
simpl. reflexivity.
Qed.

Lemma exact_inverse_two: Float32.exact_inverse (float_of_Z 2) = Some half.
Proof.
unfold Float32.exact_inverse, half.
simpl.
f_equal. f_equal.
apply proof_irr.
Qed.

Lemma mul_one: forall x : float32, 
  Binary.is_finite_strict 24 128 x = true ->
  Float32.mul x (float_of_Z 1) = x.
Proof.
Admitted.

Lemma is_finite_strict_negate:
  forall x, Binary.is_finite_strict 24 128 x = true ->
   Binary.is_finite_strict 24 128 (Float32.mul (float_of_Z (- (1))) x)  = true .
Admitted.

Lemma body_force: semax_body Vprog Gprog f_force force_spec.
Proof.
start_function.
forward.
forward.
entailer!.
f_equal.
unfold F.
change float_mult with Float32.mul.
f_equal.
apply neg1_repr.
Qed.

Lemma float_plus_eq: float_plus = Float32.add.
Proof. reflexivity. Qed.  (* Do it this way because "change" is expensive! *)

Lemma float_div_eq: float_div = Float32.div.
Proof. reflexivity. Qed.  (* Do it this way because "change" is expensive! *)

Lemma float_mult_eq: float_mult = Float32.mul.
Proof. reflexivity. Qed.  (* Do it this way because "change" is expensive! *)

Lemma leapfrog_step_x:
 forall x v, Binary.is_finite_strict 24 128 x = true ->
  fst (leapfrog_step (x,v)) = 
  Float32.add (Float32.add x (Float32.mul h v))
        (Float32.mul (Float32.of_bits (Int.repr 1056964608))
           (Float32.mul (Float32.mul h h) (F x))).
Proof.
 intros.
 cbv [leapfrog_step F float_pow fst snd].
rewrite ?float_plus_eq, ?float_div_eq, ?float_mult_eq.
  rewrite half_repr.
   forget (Float32.mul (float_of_Z (- (1))) x) as minusx.
   rewrite mul_one by reflexivity.
   rewrite (Float32.div_mul_inverse _ _ half)
     by apply exact_inverse_two.
  f_equal.
  apply Float32.mul_commut; right; reflexivity.
Qed.

Lemma leapfrog_step_v:
 forall x v, Binary.is_finite_strict 24 128 x = true ->
  snd (leapfrog_step (x,v)) = 
  Float32.add v
        (Float32.mul (Float32.of_bits (Int.repr 1056964608))
           (Float32.mul h
              (Float32.add
                 (F
                    (Float32.add
                       (Float32.add x (Float32.mul h v))
                       (Float32.mul
                          (Float32.of_bits (Int.repr 1056964608))
                          (Float32.mul (Float32.mul h h) (F x)))))
                 (F x)))).
Proof.
 intros.
 cbv [leapfrog_step F float_pow fst snd].
rewrite ?float_plus_eq, ?float_div_eq, ?float_mult_eq.
 rewrite half_repr.
 f_equal.
 rewrite mul_one by reflexivity.
 set (h2 := Float32.mul h h).
 set (minusx := Float32.mul (float_of_Z (-(1))) x).
   rewrite (Float32.div_mul_inverse _ _ half)
     by apply exact_inverse_two.
   rewrite (Float32.div_mul_inverse _ _ half)
     by apply exact_inverse_two.
  rewrite (Float32.mul_commut half) by (left; reflexivity).
  f_equal. f_equal.
  rewrite (Float32.add_commut).
  f_equal. f_equal. f_equal.
  apply Float32.mul_commut; right; reflexivity.
  left.
  apply is_finite_strict_negate in H.
  fold minusx in H.
  clearbody minusx. destruct minusx; try discriminate. reflexivity.
Qed.

Lemma body_lfstep: semax_body Vprog Gprog f_lfstep lfstep_spec.
Proof.
start_function.
forward_call.
forward_call.
forward.
forward.
forward.
forward_call.
forward.
forward.
entailer!.
clear - H.
rewrite leapfrog_step_x by auto.
rewrite leapfrog_step_v by auto.
cancel.
Qed.

Lemma leapfrog_step_is_finite_strict:
  forall n, 0 <= n < 100 ->
          Binary.is_finite_strict 24 128 (fst (Z.iter n leapfrog_step (initial_x, initial_v))) = true.
Admitted.

Lemma body_integrate: semax_body Vprog Gprog f_integrate integrate_spec.
Proof.
start_function.
forward.
forward.
forward.
forward.
forward.
replace (Vsingle (Float32.of_bits (Int.repr 1065353216))) with (Vsingle initial_x).
 2:{ unfold initial_x. rewrite float_of_Z_one.
   unfold Float32.of_bits. rewrite Int.unsigned_repr by computable.
   cbv [Bits.b32_of_bits Bits.binary_float_of_bits Binary.Bone]. simpl.
   f_equal. f_equal. apply proof_irr.
 }
 change (data_at Tsh tfloat (Vsingle (Float32.of_bits (Int.repr 0))) vp)
      with (data_at Tsh tfloat (Vsingle initial_v) vp).
 change (Float32.of_bits (Int.repr 0)) with Float32.zero.
 replace (Float32.of_bits (Int.repr 1065353216)) with (float_of_Z 1).
2:{ rewrite float_of_Z_one.
   unfold Float32.of_bits. rewrite Int.unsigned_repr by computable.
   cbv [Bits.b32_of_bits Bits.binary_float_of_bits Binary.Bone]. simpl.
   f_equal. f_equal. apply proof_irr.
  }
 replace (Float32.div _ _) with h.
2:{ unfold h, float_of_Z.
   rewrite float_div_eq. f_equal. 
   unfold Float32.of_bits. rewrite Int.unsigned_repr by computable.
   cbv [Bits.b32_of_bits Bits.binary_float_of_bits Binary.Bone ms es]. simpl.
   f_equal. apply proof_irr.
  }
pose (step n := Z.iter n leapfrog_step (initial_x, initial_v)).
 forward_for_simple_bound 100 (EX n:Z,
       PROP() 
       LOCAL (temp _h (Vsingle h);
                   temp _max_step (Vint (Int.repr 100));
                   temp _t (Vsingle (Z.iter n (Float32.add h) Float32.zero)); 
                   temp _x xp; temp _v vp)
   SEP (data_at Tsh tfloat (Vsingle (fst (step n))) xp;
          data_at Tsh tfloat (Vsingle (snd (step n))) vp))%assert.
- 
  entailer!.
- forward_call.
   apply leapfrog_step_is_finite_strict; auto.
   forward.
   entailer!.
   fold (Z.succ i); rewrite Zbits.Ziter_succ.
   f_equal. apply Float32.add_commut. left; reflexivity.
   lia.
   fold (Z.succ i); unfold step; rewrite Zbits.Ziter_succ.
   cancel. lia.
-
   forward.
Qed.

Lemma body_main: semax_body Vprog Gprog f_main main_spec.
Proof.
start_function.
forward_call.
forget (leapfrog (initial_x, initial_v) 100) as final_xv.
forward.
cancel.
Qed.























