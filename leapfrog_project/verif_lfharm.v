Require Import VST.floyd.proofauto.
Require Import lfharm.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Open Scope logic.

Require Import float_lib lf_harm_float lf_harm_lemmas.
Import IEEE754_extra.

Definition force_spec :=
 DECLARE _force
 WITH xp: val, x : float32
 PRE [ tptr tfloat ] PROP() PARAMS(xp) SEP(data_at Tsh tfloat (Vsingle x) xp)
 POST [ tfloat ] PROP() RETURN (Vsingle (F x)) 
                        SEP(data_at Tsh tfloat (Vsingle x) xp).

Definition lfstep_spec := 
  DECLARE _lfstep
  WITH xp: val, x: float32, vp: val, v: float32
  PRE [ tptr tfloat , tptr tfloat , tfloat ]
    PROP(Binary.is_finite 24 128 x = true)
    PARAMS (xp; vp; Vsingle h)
    SEP(data_at Tsh tfloat (Vsingle x) xp; data_at Tsh tfloat (Vsingle v) vp )
  POST [ tvoid ]
    PROP()
    RETURN()
    SEP(data_at Tsh tfloat (Vsingle (fst(leapfrog_step (x,v)))) xp; 
          data_at Tsh tfloat (Vsingle (snd(leapfrog_step (x,v)))) vp ).

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

Lemma body_force: semax_body Vprog Gprog f_force force_spec.
Proof.
start_function.
forward.
forward.
entailer!.
f_equal.
unfold F.
f_equal.
prove_float_constants_equal.
Qed.

Lemma leapfrog_step_x:
 forall x v, Binary.is_finite 24 128 x = true ->
  fst (leapfrog_step (x,v)) = (x + h*v +half*((h*h)*(F x)))%F32.
Proof.
 intros.
 cbv [leapfrog_step F fst snd].
  f_equal.
   rewrite (Float32.div_mul_inverse _ _ half)
     by apply exact_inverse_two.
  rewrite (Float32.mul_commut half) by (left; reflexivity).
  auto.
Qed.

Lemma leapfrog_step_v:
 forall x v, Binary.is_finite 24 128 x = true ->
  snd (leapfrog_step (x,v)) = 
  (v + half * (h * (F (x+h*v+half*((h*h)*(F x))) + F x)))%F32.
Proof.
 intros.
 cbv [leapfrog_step F fst snd].
 f_equal.
 rewrite !mul_minusone_negate by auto.
 rewrite !(Float32.div_mul_inverse _ _ half)
     by apply exact_inverse_two.
 rewrite Float32.mul_commut by (right; reflexivity).
 f_equal. f_equal.
 rewrite (Float32.add_commut) 
   by (left; apply is_finite_not_is_nan; apply is_finite_negate; auto).
 f_equal. f_equal. f_equal.
 rewrite Float32.mul_commut by (right; reflexivity).
 f_equal.
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
rewrite half_repr.
rewrite leapfrog_step_x by auto.
rewrite leapfrog_step_v by auto.
cancel.
Qed.

Lemma body_integrate: semax_body Vprog Gprog f_integrate integrate_spec.
Proof.
start_function.
forward.
forward.
forward.
forward.
forward.
replace (Vsingle (Float32.of_bits (Int.repr 1065353216))) with (Vsingle initial_x)
  by (f_equal; prove_float_constants_equal).
 change (data_at Tsh tfloat (Vsingle (Float32.of_bits (Int.repr 0))) vp)
      with (data_at Tsh tfloat (Vsingle initial_v) vp).
 change (Float32.of_bits (Int.repr 0)) with Float32.zero.
 replace (Float32.of_bits (Int.repr 1065353216)) with (1:float32)
  by (prove_float_constants_equal).
 replace (Float32.div _ _) with h
  by (prove_float_constants_equal).
pose (step n := Z.iter n leapfrog_step (initial_x, initial_v)).
 forward_for_simple_bound 100 (EX n:Z,
       PROP() 
       LOCAL (temp _h (Vsingle h);
                   temp _max_step (Vint (Int.repr 100));
                   temp _t (Vsingle (Z.iter n (Float32.add h) (0:float32))); 
                   temp _x xp; temp _v vp)
   SEP (data_at Tsh tfloat (Vsingle (fst (step n))) xp;
          data_at Tsh tfloat (Vsingle (snd (step n))) vp))%assert.
- 
  entailer!.
- forward_call.
   apply leapfrog_step_is_finite; auto.
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









