Require Import VST.floyd.proofauto.
Require Import lfharm.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Open Scope logic.

From vcfloat Require Import FPSolve Float_notations.
Require Import lf_harm_float lf_harm_lemmas lf_harm_theorems.

Set Bullet Behavior "Strict Subproofs". 

Section WITHNANS.

Context {NANS: Nans}.

Definition force_spec :=
 DECLARE _force
 WITH  x : ftype Tsingle
 PRE [ tfloat ] PROP() PARAMS(Vsingle x) SEP()
 POST [ tfloat ] PROP() RETURN (Vsingle (F x)) SEP().

Definition lfstep_spec := 
  DECLARE _lfstep
  WITH xp: val, x: ftype Tsingle, vp: val, v: ftype Tsingle
  PRE [ tptr tfloat , tptr tfloat , tfloat ]
    PROP(Binary.is_finite 24 128 x = true)
    PARAMS (xp; vp; Vsingle h)
    SEP(data_at Tsh tfloat (Vsingle x) xp; data_at Tsh tfloat (Vsingle v) vp )
  POST [ tvoid ]
    PROP()
    RETURN()
    SEP(data_at Tsh tfloat (Vsingle (fst(leapfrog_stepF_ver (x,v)))) xp; 
          data_at Tsh tfloat (Vsingle (snd(leapfrog_stepF_ver (x,v)))) vp ).

Definition initial_x : ftype Tsingle := 1%F32.
Definition initial_v : ftype Tsingle := 0%F32.

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
    SEP(data_at Tsh tfloat (Vsingle (fst(iternF_ver (initial_x,initial_v) 100))) xp; 
          data_at Tsh tfloat (Vsingle (snd(iternF_ver (initial_x,initial_v) 100))) vp ).

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
autorewrite with float_elim in *.
unfold F.
Admitted.


Lemma body_lfstep: semax_body Vprog Gprog f_lfstep lfstep_spec.
Proof.
start_function. 
subst MORE_COMMANDS; unfold abbreviate; canonicalize_float_constants.
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
autorewrite with float_elim in *.
unfold leapfrog_stepF_ver, fst, snd.
replace (BMULT Tsingle 0.5%F32 h) with 
  (BMULT Tsingle (BDIV Tsingle 1%F32 2%F32) h) in *by 
  (compute_binary_floats; auto).
replace (BMULT Tsingle 0.5%F32 (BMULT Tsingle h h)) with
  (BMULT Tsingle (BDIV Tsingle 1%F32 2%F32)
                  (BMULT Tsingle h h)) in * by 
  (compute_binary_floats; auto).
auto.
set (aa:= Vsingle
     (BPLUS Tsingle v
        (BMULT Tsingle (BMULT Tsingle (BDIV Tsingle 1%F32 2%F32) h)
           (BPLUS Tsingle (F x)
              (F
                 (BPLUS Tsingle (BPLUS Tsingle x (BMULT Tsingle h v))
                    (BMULT Tsingle
                       (BMULT Tsingle (BDIV Tsingle 1%F32 2%F32)
                          (BMULT Tsingle h h)) (F x)))))))).
set (bb:= Vsingle
         (BPLUS Tsingle v
            (BMULT Tsingle (BMULT Tsingle (BDIV Tsingle 1%F32 2%F32) h)
               (BPLUS Tsingle (F x)
                  (F
                     (BPLUS Tsingle (BPLUS Tsingle x (BMULT Tsingle h v))
                        (BMULT Tsingle
                           (BMULT Tsingle (BDIV Tsingle 1%F32 2%F32)
                              (BMULT Tsingle h h)) 
                           (F x)))))))).
Qed.

Lemma leapfrog_step_is_finite:
 forall i,  (0 <= i < 100)%Z ->
  Binary.is_finite 24 128 (fst (Z.iter i leapfrog_step (initial_x, initial_v))) = true.
Admitted.

Lemma body_integrate: semax_body Vprog Gprog f_integrate integrate_spec.
Proof.
start_function.
subst MORE_COMMANDS; unfold abbreviate; canonicalize_float_constants.
forward.
forward.
forward.
forward.
forward.
autorewrite with float_elim in *.
pose (step n := Z.iter n leapfrog_step (initial_x, initial_v)).
 forward_for_simple_bound 100%Z (EX n:Z,
       PROP() 
       LOCAL (temp _h (Vsingle h);
                   temp _max_step (Vint (Int.repr 100));
                   temp _t (Vsingle (Z.iter n (BPLUS Tsingle h) (0%F32))); 
                   temp lfharm._x xp; temp lfharm._v vp)
   SEP (data_at Tsh tfloat (Vsingle (fst (step n))) xp;
          data_at Tsh tfloat (Vsingle (snd (step n))) vp))%assert.
- 
  entailer!.
- forward_call.
   apply leapfrog_step_is_finite; lia.
   forward.
   autorewrite with float_elim in *.
   entailer!.
   fold (Z.succ i); rewrite Zbits.Ziter_succ by lia.
   rewrite BPLUS_commut by reflexivity; auto.
   fold (Z.succ i); unfold step; rewrite Zbits.Ziter_succ by lia.
   cancel.
-
   change (leapfrog' (initial_x, initial_v) 100) with (step 100%Z).
   forward.
Qed.

Lemma body_main: semax_body Vprog Gprog f_main main_spec.
Proof.
start_function.
forward_call.
forget (leapfrog' (initial_x, initial_v) 100)  as a.
forward.
cancel.
Qed.










