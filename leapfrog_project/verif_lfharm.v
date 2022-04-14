Require Import VST.floyd.proofauto.
Require Import lfharm.
#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Open Scope logic.

From vcfloat Require Import FPSolve Float_notations.
Require Import lf_harm_float.

Set Bullet Behavior "Strict Subproofs". 

Definition force_spec :=
 DECLARE _force
 WITH  q : ftype Tsingle
 PRE [ tfloat ] PROP() PARAMS(Vsingle q) SEP()
 POST [ tfloat ] PROP() RETURN (Vsingle (F q)) SEP().

Definition floats_to_vals (pq: ftype Tsingle * ftype Tsingle) : val*val :=
 (Vsingle (fst pq), Vsingle (snd pq)).
Definition t_state := Tstruct _state noattr.

Definition lfstep_spec := 
  DECLARE _lfstep
  WITH s: val, pq: ftype Tsingle * ftype Tsingle
  PRE [ tptr t_state, tfloat ]
    PROP(Binary.is_finite 24 128 (snd pq) = true)
    PARAMS (s; Vsingle h)
    SEP(data_at Tsh t_state (floats_to_vals pq) s)
  POST [ tvoid ]
    PROP()
    RETURN()
    SEP(data_at Tsh t_state (floats_to_vals (leapfrog_stepF pq)) s ).

Definition integrate_spec_lowlevel := 
  DECLARE _integrate
  WITH s: val
  PRE [ tptr t_state ]
    PROP(iternF_is_finite)
    PARAMS (s)
    SEP(data_at_ Tsh t_state s)
  POST [ tvoid ]
    PROP()
    RETURN()
    SEP(data_at Tsh t_state (floats_to_vals (iternF (p_init,q_init) 100)) s).

Definition main_spec :=
 DECLARE _main
  WITH gv: globals
  PRE  [] main_pre prog tt gv
  POST [ tint ]
       PROP() RETURN (Vint (Int.repr 0)) SEP(TT).

Definition Gprog : funspecs := [force_spec; lfstep_spec; integrate_spec_lowlevel; main_spec].

Lemma body_force: semax_body Vprog Gprog f_force force_spec.
Proof.
start_function.
forward.
Qed.

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
autorewrite with float_elim in *.
unfold leapfrog_stepF, floats_to_vals, fst, snd.
entailer!.
Qed.

Lemma body_integrate: semax_body Vprog Gprog f_integrate integrate_spec_lowlevel.
Proof.
start_function.
subst MORE_COMMANDS; unfold abbreviate; canonicalize_float_constants.
forward.
forward.
forward.
forward.
forward.
autorewrite with float_elim in *. 
pose (step n := iternF (p_init, q_init) (Z.to_nat n)).
 forward_for_simple_bound 100%Z (EX n:Z,
       PROP() 
       LOCAL (temp _h (Vsingle h);
                   temp _max_step (Vint (Int.repr 100));
                   temp _t (Vsingle (Z.iter n (BPLUS Tsingle h) (0%F32))); 
                   temp lfharm._s s)
   SEP (data_at Tsh t_state (floats_to_vals (step n)) s))%assert.
- entailer!.
- forward_call (s, step i).
  apply H; lia.
  forward.
  autorewrite with float_elim in *.
  entailer!.
  fold (Z.succ i); rewrite Zbits.Ziter_succ by lia.
  rewrite BPLUS_commut by reflexivity; auto.
  unfold step at 2.
  replace (Z.to_nat (i+1)) with (S (Z.to_nat i)) by lia.
  rewrite step_iternF.
  apply derives_refl.
- change (iternF(p_init, q_init) 100) with (step 100%Z).
   forward.
Qed.









