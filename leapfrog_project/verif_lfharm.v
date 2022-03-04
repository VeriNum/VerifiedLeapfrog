Require Import VST.floyd.proofauto.
Require Import lfharm.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Open Scope logic.

Require Import float_lib lf_harm_float lf_harm_lemmas.
Import IEEE754_extra.
Import Float32_Notation.
Set Bullet Behavior "Strict Subproofs". 

Definition force_spec :=
 DECLARE _force
 WITH  x : float32
 PRE [ tfloat ] PROP() PARAMS(Vsingle x) SEP()
 POST [ tfloat ] PROP() RETURN (Vsingle (F x)) SEP().

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

Definition initial_x := (1:float32).
Definition initial_v := (0:float32).

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
    SEP(data_at Tsh tfloat (Vsingle (fst(leapfrog' (initial_x,initial_v) 100))) xp; 
          data_at Tsh tfloat (Vsingle (snd(leapfrog' (initial_x,initial_v) 100))) vp ).

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
Qed.

Lemma body_lfstep: semax_body Vprog Gprog f_lfstep lfstep_spec.
Proof.
start_function.
forward.
forward_call.
forward.
forward.
forward.
forward.
forward.
forward_call.
forward.
forward.
entailer!.
replace (Float32.of_bits (Int.repr 1056964608)) with (1%Z/2%Z)%F32
   by prove_float_constants_equal.
apply derives_refl.
Qed.

Lemma leapfrog_step_is_finite:
 forall i,  0 <= i < 100 ->
  Binary.is_finite 24 128 (fst (Z.iter i leapfrog_step (initial_x, initial_v))) = true.
Admitted.

Lemma body_integrate: semax_body Vprog Gprog f_integrate integrate_spec.
Proof.
start_function.
forward.
forward.
forward.
forward.
forward.
replace (Float32.div _ _) with h
    by prove_float_constants_equal.
replace (Float32.of_bits (Int.repr 1065353216)) with (1:float32)
    by prove_float_constants_equal.
change (Float32.of_bits (Int.repr 0)) with (0:float32).
pose (step n := Z.iter n leapfrog_step (initial_x, initial_v)).
 forward_for_simple_bound 100 (EX n:Z,
       PROP() 
       LOCAL (temp _h (Vsingle h);
                   temp _max_step (Vint (Int.repr 100));
                   temp _t (Vsingle (Z.iter n (Float32.add h) (0:float32))); 
                   temp lfharm._x xp; temp lfharm._v vp)
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
forward.
cancel.
Qed.










