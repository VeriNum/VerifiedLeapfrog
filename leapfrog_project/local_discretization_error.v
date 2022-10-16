From Coq Require Import ZArith Reals Psatz.
From Coq Require Import Arith.Arith.
Require Import real_lemmas real_model harmonic_oscillator_system.
From Coquelicot Require Import Coquelicot.
Set Bullet Behavior "Strict Subproofs". 

Require Import Interval.Tactic.

Open Scope R_scope.


Lemma Harm_sys_norm_bound p q:
  forall t0 t1 t2 t3,
  forall ω h,
  0 < ω ->
  (* the following hypothesis, which is NOT derived from stability analysis on h ,
     is required in order to show that (h ω)^4/ 4! can be upper bounded by (h ω)^3/ 3! *)
  0 <= h * ω <= 4 ->
  Harmonic_oscillator_system ω p q  ->
  let r1 := h^4/INR(fact 4) * (Derive_n p 4 t2) - h^3/12 * ω^4 * q t3 in
  let r2 := h^3/INR(fact 3) * ω * (Derive_n q 3 t1) in
  ∥(r1,r2)∥  <= (h*ω)^3 * ∥(p t0, ω * q t0)∥.
Proof.
intros ? ? ? ? ? ? ωpos hsep H.
pose proof Harm_sys_derive_eq p q _ ωpos H t1 as (A0 & A & _ & _ & _).
pose proof Harm_sys_derive_eq p q _ ωpos H t2 as (B0 & _ & _ & _ & C2).
rewrite A, C2. clear A C2.
assert (C := fun t => system_implies_cons_e' _ _ _ t0 t ωpos H).
destruct H as (HA & HB & _).
assert (C1 := C t1).
assert (C2 := C t2).
assert (C3 := C t3).
unfold Rprod_norm, fst, snd in *. cbv [prod_norm fst snd].
apply sqrt_inj in C1, C2, C3; try nra.
assert (p t1 ^ 2  <= ω ^2 * q t0 ^ 2 + p t0 ^ 2) by nra; 
  clear C.
assert (p t2 ^ 2  <= ω ^2 * q t0 ^ 2 + p t0 ^ 2) by nra; 
  clear C2.
assert (ω ^2 * q t3 ^ 2 <= ω ^2 * q t0 ^ 2 + p t0 ^ 2) by nra; 
  clear C3.
set (y:= ω ^ 2 * q t0 ^ 2 + p t0 ^ 2) in *. 
match goal with |- context[(?a - ?aa) ^2 ] =>
replace ((a - aa) ^2) with
  (a^2 + aa^2 -2*a*aa) by nra
end.
match goal with |- context[sqrt(?a) <= ?b] =>
assert (a <= b^2)
end.
+ eapply Rle_trans.
  eapply Rplus_le_compat_r.
  eapply Rplus_le_compat_r.
  eapply Rplus_le_compat_r.
  replace ((h ^ 4 / INR (fact 4) * (ω ^ 4 * p t2)) ^ 2)
  with ((h ^ 4 / INR (fact 4))^2 * (ω ^ 4)^2 * (p t2) ^ 2) by nra.
  eapply Rmult_le_compat_l; try nra. apply H0.
  eapply Rle_trans.
  eapply Rplus_le_compat_r.
  eapply Rplus_le_compat_r.
  eapply Rplus_le_compat_l.
  replace ((h ^ 3 / 12 * ω ^ 4 * q t3) ^ 2) 
  with ((h ^ 3 / 12)^2 * (ω ^ 3)^2 * (ω ^2 * q t3 ^ 2)) by nra.
  eapply Rmult_le_compat_l; try nra. apply H1.
  eapply Rle_trans.
  eapply Rplus_le_compat_r.
  eapply Rplus_le_compat_l.
  eapply Rle_trans.
  apply Rabs_maj2.
  repeat rewrite Rabs_mult.
  eapply Rmult_le_compat_l. 
  repeat rewrite <- Rabs_mult. apply Rabs_pos.
  rewrite Rmult_assoc.
  eapply Rmult_le_compat_l. apply Rabs_pos.
  replace (Rabs (ω ^ 4) * Rabs (q t3)) with
  (Rabs (ω ^ 3) * Rabs (ω * q t3)).
  eapply Rmult_le_compat_l. apply Rabs_pos.
  apply Rabs_pos_le in H1; try nra; auto.
  replace (ω ^ 2 * q t3 ^ 2) with
  ((ω * q t3) ^ 2) in H1.
  rewrite Rabs_sqr_le in H1.
  apply sqrt_le_1_alt in H1.
  rewrite sqrt_pow2 in H1; try (apply Rabs_pos).
  apply H1. 
  try nra.
  repeat rewrite <- Rabs_mult. f_equal. nra.
  eapply Rle_trans.
  eapply Rplus_le_compat_r.
  eapply Rplus_le_compat_l.
  eapply Rmult_le_compat_r.
  rewrite <- Rmult_assoc.
  apply Rle_mult.
  rewrite <- Rabs_mult. apply Rabs_pos.
  apply sqrt_pos.
  eapply Rmult_le_compat_l. apply Rabs_pos.
  eapply Rmult_le_compat_l. apply Rabs_pos.
  eapply Rmult_le_compat_l. apply Rabs_pos.
  apply Rabs_pos_le in H0; try nra; auto.
  rewrite Rabs_sqr_le in H0.
  apply sqrt_le_1_alt in H0.
  rewrite sqrt_pow2 in H0; try (apply Rabs_pos).
  apply H0.
  eapply Rle_trans.
  eapply Rplus_le_compat_l.
  replace ((h ^ 3 / INR (fact 3) * ω * (- ω ^ 2 * p t1)) ^ 2)
  with ((h ^ 3 / INR (fact 3) )^2 * ω^2 * (ω ^ 2)^2 * (p t1) ^ 2) by nra.
  eapply Rmult_le_compat_l. nra.
  apply H.
  replace (Rabs 2 * (Rabs (h ^ 4 / INR (fact 4)) * (Rabs (ω ^ 4) * sqrt (Rabs y))) *
  (Rabs (h ^ 3 / 12) * (Rabs (ω ^ 3) * sqrt (Rabs y)))) with
  (2 * h ^ 4 / INR (fact 4) * ω ^ 4 * h ^ 3 / 12 *  ω ^ 3 * y).
  assert (h ^ 3 / 12 * ω ^ 3 <= h ^ 3 / INR (fact 3) * (ω ^ 3)).
  replace (INR (fact 3)) with (6) by (simpl;nra).
  apply Rmult_le_compat_r; try nra.
  assert (h ^ 4 / INR (fact 4) * ω ^ 4 <= h ^ 3 / INR (fact 3) * (ω ^ 3)).
  replace (INR (fact 4)) with (24) by (simpl;nra).
  replace (h ^ 4 / 24 * ω ^ 4) with
  ((h * ω)^3 * (h * ω) * /24) by nra.
  replace (h ^ 3 / INR (fact 3) * ω ^ 3) with
  ((h * ω) ^ 3 * 4 *  /24) by (simpl; nra).
  apply Rmult_le_compat_r; try nra.
  apply Rmult_le_compat_l; try nra. 
  apply pow_le; nra.
  eapply Rle_trans.
  apply Rplus_le_compat_r.
  apply Rplus_le_compat_r.
  eapply Rle_trans.
  apply Rplus_le_compat_r.
  apply Rmult_le_compat_r; try nra.
  replace ((h ^ 4 / INR (fact 4)) ^ 2 * (ω ^ 4) ^ 2)
  with ((h ^ 4 / INR (fact 4) * (ω ^ 4)) ^ 2) by nra.
  apply pow_incr.
  split. simpl. nra.
  apply H3.
  apply Rplus_le_compat_l.
  apply Rmult_le_compat_r; try nra.
  replace ((h ^ 3 / 12) ^ 2 * (ω ^ 3) ^ 2)
  with ((h ^ 3 / 12 * ω ^ 3) ^ 2) by nra.
  apply pow_incr.
  split. apply Rle_mult; try nra.
  apply H2.
  eapply Rle_trans.
  apply Rplus_le_compat_r.
  apply Rplus_le_compat_l.
  apply Rmult_le_compat_r; try nra.
  eapply Rle_trans.
  apply Rmult_le_compat_r; try nra.
  apply Rmult_le_compat_r; try nra.
  apply Rmult_le_compat_r; try nra.
  replace (2 * h ^ 4 / INR (fact 4) * ω ^ 4)
  with (2 * (h ^ 4 / INR (fact 4) * ω ^ 4)) by nra.
  apply Rmult_le_compat_l; try nra. 
  apply H3.
  rewrite Rmult_assoc.
  rewrite Rmult_assoc.
  apply Rmult_le_compat_l.
  repeat (apply Rle_mult; simpl; try nra).
  rewrite <- Rmult_assoc.
  apply H2.
  match goal with |- context [?a <= ?b] =>
  replace a with ( 5 * (h ^ 3 / INR (fact 3)) ^ 2 * (ω ^ 3) ^ 2 * y);
  replace b with  ((h ^3)^2 * (ω ^ 3)^2 * (ω^2 * q t0 ^2 + p t0 ^ 2))
  end.
  subst y.
  apply Rmult_le_compat_r; try (simpl; nra).
  rewrite Rpow_mult_distr.
  rewrite pow2_sqrt. nra. nra.
  replace ((h ^ 3 / INR (fact 3)) ^ 2 * ω ^ 2 * (ω ^ 2) ^ 2 * y)
  with ((h ^ 3 / INR (fact 3)) ^ 2 * (ω ^ 3) ^ 2 * y) by nra.
  field_simplify. nra.
  simpl; nra. simpl; nra.
  field_simplify. 
  rewrite pow2_sqrt. nra.
  apply sqr_plus_pos.
  symmetry.
  rewrite <- Rmult_assoc.
  rewrite <- Rmult_assoc.
  rewrite <- Rmult_assoc.
  rewrite <- Rmult_assoc.
  rewrite <- Rabs_mult.
  rewrite <- Rabs_mult.
  rewrite Rmult_comm.
  rewrite Rmult_assoc.
  rewrite<- Rabs_mult.
  rewrite Rmult_comm.
  rewrite Rmult_assoc.
  rewrite Rmult_assoc.
  replace (sqrt (Rabs y) * (Rabs (h ^ 3 / 12 * ω ^ 3) * sqrt (Rabs y))) with 
  ((Rabs y) * Rabs (h ^ 3 / 12 * ω ^ 3)).
  repeat rewrite<- Rabs_mult.
  field_simplify.
  match goal with |- context [Rabs ?a = ?b] =>
  field_simplify a
  end.
  apply Rabs_pos_eq. 
  repeat apply Rle_mult; try (simpl;nra).
  simpl. nra.
  simpl. nra.
  symmetry; rewrite Rmult_comm.
  rewrite Rmult_assoc.
  symmetry; rewrite Rmult_comm.
  f_equal; symmetry. apply sqrt_def.
  subst y; apply Rabs_pos.
  + apply sqrt_le_1_alt in H2.
  rewrite sqrt_pow2 in H2.
  eapply Rle_trans.
  apply H2. try nra.
  repeat apply Rle_mult; try (simpl;nra).
  apply sqrt_pos.
Qed.

(* the componentwise truncation error for the solution vector *)
Theorem local_discretization_error_aux:
  forall p q: R -> R,
  forall t0 tn: R,
  forall h : R, 
  0 < ω*h <= 4 ->  
  Harmonic_oscillator_system 1 p q  ->
  exists t1 t2: R,
  tn < t1 < tn + h /\
  tn < t2 < tn + h /\
  q (tn + h) - snd(leapfrog_stepR h (p tn, q tn)) = 
    h^3 / INR (fact 3) * Derive_n q 3 t1 /\
  p (tn + h) - fst(leapfrog_stepR h (p tn,  q tn)) = 
    h^4 / INR (fact 4) * Derive_n p 4 t2 - h^3 / 12 * q tn . 
Proof.
intros ? ? ? ? ? ? HSY; intros.
rewrite Rmult_1_l in H.
assert (wpos: 0 < 1) by nra.
pose proof (HOS_implies_k_diff p q 1 tn h HSY) as Hdiff.
assert (tn < tn + h) as LT by nra.
destruct Hdiff as ( KP & KQ); unfold k_differentiable in *.
(* apply Taylor's theorem for each component of the solution vector *) 
pose proof Taylor_Lagrange q 2 tn (tn + h) LT KQ as TLRq. 
pose proof Taylor_Lagrange p 3 tn (tn + h) LT KP as TLRp.
destruct TLRq as (t1 & A & B). 
destruct TLRp as (t2 & C & D).
replace (tn + h - tn) with h in * by nra.
pose proof Harm_sys_derive_eq p q 1 ltac:(lra) HSY tn as (HD1 & HD2 & HD3 & HD4 & HD5).
exists t1, t2. 
repeat split; try apply A; try apply C.
  + rewrite B. cbv [sum_f_R0].
    destruct HSY as ( _& _ &HSY).
    specialize (HSY tn). destruct HSY as (Hxd1 & Hxd2).
rewrite Hxd1, HD1, Hxd2. 
    unfold Derive_n at 1. unfold dUdq.
    unfold leapfrog_stepR, fst, snd.
    simpl; unfold ω; nra.
  + rewrite D. cbv [sum_f_R0].
    replace (Derive_n p 2 tn) with 
    (Derive_n (fun y : R => - dUdq (q y) 1) 1 tn). 
    2: {
    replace (Derive_n (fun y : R => - dUdq (q y) 1) 1 tn) with 
    (Derive_n (Derive_n q 1) 2 tn ). 
    (apply Derive_n_ext; apply HSY).
    replace (Derive_n (Derive_n q 1) 2 tn) with
    (Derive_n (Derive_n q 2) 1 tn) by auto.
    apply Derive_n_ext.
    intros. 
    pose proof Harm_sys_derive_eq p q 1 ltac:(lra) HSY t.
  destruct H0 as ( H0 & _).
    rewrite H0.
  destruct HSY as (_ & _ &HSY).
        specialize (HSY t).
apply HSY.
    }
    unfold dUdq. 
    rewrite Derive_n_opp.
    rewrite Derive_n_scal_l.
    replace (Derive_n p 1 tn) with 
    (Derive_n q 2 tn) by (
    replace (Derive_n q 2 tn) with
    (Derive_n (Derive_n q 1) 1 tn) by auto;
    apply Derive_n_ext; apply HSY).
    destruct HSY as ( _ & _ &HSY).
    specialize (HSY tn). destruct HSY as (Hxd1 & Hxd2).
    rewrite HD1. rewrite Hxd1. unfold Derive_n at 1.
    rewrite Hxd2. rewrite HD4.
    unfold leapfrog_stepR, dUdq, fst, snd.
    simpl; unfold ω; nra.
Qed.

(* upper bound the norm of the truncation error *)
Theorem local_discretization_error_norm_aux:
  forall p q: R -> R,
  forall t0 tn: R,
  forall h : R, 
  0 < ω*h <= 4 ->  
  Harmonic_oscillator_system 1 p q  ->
  exists t1 t2: R,
  tn < t1 < tn + h /\
  tn < t2 < tn + h /\
  let '(r1, r2) := (h^4/INR(fact 4) * Derive_n p 4 t2 - h^3 / 12 * q tn,  h^3/INR(fact 3) * Derive_n q 3 t1) in
  ∥(p (tn + h)%R, q (tn + h)%R) - (leapfrog_stepR h (p tn, q tn))∥ <= ∥(r1 , r2)∥.
Proof.
intros ? ? ? ? ? Hbnd HSY; intros.
pose proof local_discretization_error_aux p q t0 tn h Hbnd HSY as LTE.
destruct LTE as [t1 [t2 [A [B [ C D ] ] ] ]].
exists t1, t2.
split; auto.
split; auto.
unfold Rprod_norm, Rprod_minus.
unfold fst at 1 2. unfold snd at 1 2.
unfold fst at 2. unfold snd at 2.
rewrite C, D.
apply Req_le.
nra.
Qed.

Theorem local_discretization_error:
  forall p q : R -> R,
  forall t0 tn: R,
  forall h : R, 
  0 < ω*h <= 4 -> 
  Harmonic_oscillator_system ω p q  ->
  let '(pn,qn):= (leapfrog_stepR h (p tn, q tn)) in
  ∥(p (tn + h)%R, q (tn + h)%R) - (pn, qn)∥ <= h^3 * ∥(p t0,  q t0)∥.
Proof.
intros ? ? ? ? ? Hbnd HSY; intros.
pose proof local_discretization_error_norm_aux 
  p q t0 tn h Hbnd HSY as (t1 & t2 & A & B & C).
eapply Rle_trans.
apply C.
assert (HBND2: 0 <= h * ω <= 4) by nra.
pose proof ( Harm_sys_norm_bound p q t0 t1 t2 tn 1 h Rlt_0_1 HBND2 HSY)as Hsys.
rewrite pow1 in Hsys. 
repeat rewrite Rmult_1_r in Hsys.
repeat rewrite Rmult_1_l in Hsys.
apply Hsys. 
Qed.

Close Scope R_scope. 
