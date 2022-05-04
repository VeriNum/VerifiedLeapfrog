Require Import VST.floyd.proofauto.
Require Import Reals.
Require Import real_lemmas.
Require Import lfharm.
Require Import verif_lfharm.
Require Import float_model total_error.
Require Import vcfloat.FPCompCert.

Definition integrate_spec := 
  DECLARE _integrate
  WITH s: val
  PRE [ tptr t_state ]
    PROP()
    PARAMS (s)
    SEP(data_at_ Tsh t_state s)
  POST [ tvoid ]
   EX (pq: float32*float32),
    PROP(accurate_harmonic_oscillator pq max_step 0.0308)
    RETURN()
    SEP(data_at Tsh t_state (floats_to_vals pq) s).

Lemma subsume_integrate: funspec_sub (snd integrate_spec_lowlevel) (snd integrate_spec).
Proof.
apply NDsubsume_subsume.
split; auto.
unfold snd.
hnf; intros.
split; auto. intros s [? ?]. Exists s emp.
Intros. simpl in H.
inv H. inv H4.
pose proof yes_iternF_is_finite.
destruct (H 1000%nat ltac:(unfold max_step;lia)) as [_ ?].
pose proof yes_accurate_harmonic_oscillator.
unfold max_step in *.
set (pq := iternF (p_init, q_init) 1000) in *.
clearbody pq.
unfold_for_go_lower; normalize.
inv H2.
simpl.
entailer!.
intros.
Exists pq.
entailer!.
Qed.

Theorem body_integrate_highlevel :
   semax_body Vprog Gprog f_integrate integrate_spec.
Proof.
eapply semax_body_funspec_sub.
apply body_integrate.
apply subsume_integrate.
repeat constructor; intro H; simpl in H; decompose [or] H; try discriminate; auto.
Qed.

(* Print Assumptions body_integrate_highlevel. *)

Lemma body_main: semax_body Vprog Gprog f_main main_spec.
Proof.
start_function.
forward_call. apply yes_iternF_is_finite.
forget (iternF (p_init, q_init) 1000)  as a.
forward.
cancel.
Qed.

#[export] Existing Instance NullExtension.Espec.

Lemma prog_correct:
  semax_prog prog tt Vprog Gprog.
Proof.
  prove_semax_prog.
  semax_func_cons body_force.
  semax_func_cons body_lfstep.
  semax_func_cons body_integrate.
  semax_func_cons body_main.
Qed.

