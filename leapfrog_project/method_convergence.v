From Coq Require Import ZArith Reals Psatz.
From Coq Require Import Arith.Arith.
Require Import real_lemmas real_model.
From Coquelicot Require Import Coquelicot.
Set Bullet Behavior "Strict Subproofs". 

Require Import IntervalFlocq3.Tactic.

Open Scope R_scope.



Lemma method_norm_bounded_aux_p : 
forall p q h: R,
  0 < ω*h <= 2 ->  (* ideally we would write 0 < ω*h <= 2   here *)
Rabs (fst(leapfrog_stepR (p,q) h)) <=  Rabs p + h * Rabs q.
Proof.
intros.
unfold leapfrog_stepR, fst, snd.
rewrite pow1, Rmult_1_r. rewrite Rmult_1_l in H.
eapply Rle_trans. eapply Rabs_triang.
replace (p - 0.5 * h ^ 2 * p) with
((1 - 0.5 * h ^ 2) * p) by nra.
replace (- (0.5 * h * (2 - 0.5 * h ^ 2) * q)) with
((h^3/4 - h) * q) by nra.
repeat rewrite Rabs_mult.
eapply Rle_trans.
eapply Rplus_le_compat_l.
assert (Rabs (h ^ 3 / 4 - h) * Rabs q <= h * Rabs q).
eapply Rmult_le_compat_r; try (apply Rabs_pos).
apply Rabs_le. nra.
apply H0.
eapply Rle_trans.
apply Rplus_le_compat_r.
apply Rmult_le_compat_r.
apply Rabs_pos.
assert (Rabs (1 - 0.5 * h ^ 2) <= 1).
apply Rabs_le. nra.
apply H0.
nra. 
Qed.

Lemma method_norm_bounded_aux_q : 
forall p q h: R,
  0 < ω*h <= 2 -> 
Rabs (snd(leapfrog_stepR (p,q) h)) <=  Rabs q + h * Rabs p.
Proof.
intros.
rewrite Rmult_1_l in H.
unfold leapfrog_stepR, fst, snd.
rewrite pow1, Rmult_1_r.
eapply Rle_trans.
rewrite Rplus_comm.
replace (h * p + q - 0.5 * h ^ 2 * q) with
(h * p + (1 - 0.5 * h ^ 2) * q) by nra.
eapply Rabs_triang.
rewrite Rplus_comm.
repeat rewrite Rabs_mult.
assert (Rabs h = h).
apply Rabs_pos_eq; nra.
rewrite H0.
eapply Rle_trans.
apply Rplus_le_compat_r.
apply Rmult_le_compat_r.
apply Rabs_pos.
assert (Rabs (1 - 0.5 * h ^ 2) <= 1).
apply Rabs_le. nra.
apply H1.
nra. 
Qed. 

Lemma method_norm_bounded : 
forall p q h: R,
  0 < ω*h <= 2 -> 
∥(leapfrog_stepR (p,q) h)∥ <= (1 + h) * ∥(p,q)∥.
Proof.
intros.
pose proof method_norm_bounded_aux_q p q h H.
pose proof method_norm_bounded_aux_p p q h H.
rewrite Rmult_1_l in H.
unfold Rprod_norm.
assert (forall x, x ^  2 = Rabs x ^ 2).
intros.
rewrite <- Rabs_sqr_le.
rewrite Rabs_pos_eq; try nra.
replace ((1 + h) * sqrt (fst (p, q) ^ 2 + snd (p, q) ^ 2))
with ( sqrt ((1 + h)^2 * (fst (p, q) ^ 2 + snd (p, q) ^ 2))).
apply sqrt_le_1_alt.
eapply Rle_trans.
apply Rplus_le_compat_l.
apply pow_maj_Rabs. 
apply H0.
eapply Rle_trans.
apply Rplus_le_compat_r.
apply pow_maj_Rabs. 
apply H1.
unfold fst, snd.
replace ((Rabs p + h * Rabs q) ^ 2 + (Rabs q + h * Rabs p) ^ 2)
with ((Rabs q ^2 + h ^2 * Rabs p ^2 + 2 * h * Rabs p * Rabs q)  
  + (Rabs p ^ 2 + h^2 * Rabs q ^2 + 2 * h * Rabs p * Rabs q) ) by nra.
replace ((Rabs q ^2 + h ^2 * Rabs p ^2 + 2 * h * Rabs p * Rabs q)  
  + (Rabs p ^ 2 + h^2 * Rabs q ^2 + 2 * h * Rabs p * Rabs q) ) 
with ((1 + h^2) * (Rabs q ^2 + Rabs p ^2) + 4 * h * Rabs p * Rabs q) by nra.
match goal with |-context[Rabs ?a ^ 2] => 
replace (Rabs a ^ 2) with (a ^2)
end.
match goal with |-context[Rabs ?a ^ 2] => 
replace (Rabs a ^ 2) with (a ^2)
end.
replace ((1 + h) ^ 2 * (p ^ 2 + q ^ 2)) with
((1 + h^2) * (q ^ 2 + p ^ 2) + 2*h *  (p ^ 2 + q ^ 2)) by nra.
apply Rplus_le_compat_l.
assert (2 *Rabs p * Rabs q <= (p ^ 2 + q ^ 2)).
rewrite Rminus_le_0.
replace (p ^ 2 + q ^ 2 - 2 * Rabs p * Rabs q)
with ( (Rabs p - Rabs q) ^ 2).
apply square_pos.
replace ((Rabs p - Rabs q) ^ 2) with
(Rabs p ^2 + Rabs q ^2 - 2 * Rabs p * Rabs q) by nra.
pose proof H2 p. rewrite H3.
pose proof H2 q. rewrite H4.
nra.
apply (Rmult_le_compat_l (2*h)) in H3.
field_simplify in H3.
field_simplify.
nra.
nra.
specialize( H2 p); auto. 
specialize( H2 q); auto.
rewrite sqrt_mult_alt.
rewrite sqrt_pow2; try nra.
apply square_pos.
Qed.

Lemma method_bound_n: 
  forall p q h: R,
  forall n : nat, 
    0 < ω*h <= 2 -> 
  ∥iternR (p,q) h n∥ <= (1 + h) ^ n * ∥(p,q)∥.
Proof.
intros.
rewrite Rmult_1_l in H.
induction n.
-  simpl; nra.
- rewrite step_iternR.
rewrite <- tech_pow_Rmult.
destruct (iternR (p, q) h n).
eapply Rle_trans.
apply method_norm_bounded; unfold ω; try nra.
rewrite Rmult_assoc.
eapply Rmult_le_compat_l; try nra.
Qed.

Lemma global_truncation_error_sum : 
  forall p q: R -> R,
  forall t0 T: R,
  forall h : R, 
  0 < ω*h <= 2 -> 
  Harmonic_oscillator_system p q 1 t0  -> 
  forall n : nat, 
  let tn:= t0 + INR n * h  in 
  tn <= T -> 
  ∥ (p tn, q tn) - (iternR (p t0, q t0) h n)∥
    <= h^3 * ∥(p t0,  q t0)∥ * error_sum (1+h) n.
Proof.
intros ? ? ? ? ? HBND HSY; intros. 
induction n.
+ subst tn. 
rewrite Rmult_0_l. rewrite Rmult_0_r.
rewrite Rplus_0_r. unfold Rprod_minus, Rprod_norm, iternR, fst, snd.
repeat rewrite Rminus_eq_0. rewrite pow_i. rewrite Rplus_0_r.
rewrite sqrt_0. nra. lia.
+ rewrite step_iternR. 
cbv zeta in IHn.
subst tn.
rewrite S_INR in H. rewrite Rmult_1_l in HBND.
assert (HSN: t0 + INR n * h <= T) by lra.
specialize (IHn HSN); clear HSN.
set (phi1:= leapfrog_stepR (p (t0 + INR  n * h), q (t0 + INR  n * h)) h) in *.
set (phi2:=  
leapfrog_stepR (iternR (p t0, q t0) h n) h ).
eapply Rle_trans.
match goal with |- context[ ?a <= ?b] =>
  replace a with (Rprod_norm 
  (Rprod_plus (Rprod_minus (p (t0 + INR (S n) * h ),  q (t0 + INR (S n) * h)) phi1)
(Rprod_minus phi1 phi2))) by (symmetry; apply Rprod_norm_plus_minus_eq)
end.
apply Rprod_triang_ineq.
assert (HBND2: 0 < ω*h <= 4) by (unfold ω; nra).
assert (TBND: t0 + (INR n ) * h <= T) by nra.
field_simplify in H.
assert (t0 <= t0 + INR n * h).
apply Rle_minus_l_2.
rewrite Rminus_eq_0.
apply Rle_mult; try nra. apply pos_INR.
clear H0.
pose proof local_truncation_error p q t0 (t0 + INR n * h) h HBND2 HSY as H0.
fold phi1 in H0.
eapply Rle_trans.
eapply Rplus_le_compat_r.
rewrite S_INR.
replace (t0 + (INR n + 1) * h) with (t0 + INR n * h + h) by nra.
apply H0; auto.
eapply Rle_trans.
eapply Rplus_le_compat_l.
subst phi1 phi2.
pose proof leapfrog_minus_args
(p (t0 + INR n * h), q (t0 + INR n * h))
(iternR (p t0, q t0) h n) h as H1.
rewrite H1.
pose proof (method_norm_bounded) as H2.
apply H2; rewrite Rmult_1_l; auto. 
unfold fst at 1.
eapply Rle_trans.
eapply Rplus_le_compat_l.
eapply Rmult_le_compat_l; try nra.
apply IHn. 
set 
  (aa:=h ^ 3 *  ∥ (p t0, q t0) ∥).
replace (aa + (1 + h) * (aa * error_sum ((1 + h) ^ n) n))
with 
(aa + aa * (1 + h) * error_sum ((1 + h) ^ n) n) by nra.
rewrite <- error_sum_aux2.
field_simplify.
subst aa.
nra.
Qed.

Lemma global_truncation_error_aux: 
  forall p q: R -> R,
  forall t0 T: R,
  forall h : R, 
  0 < ω*h <= 2 -> 
  Harmonic_oscillator_system p q 1 t0 -> 
  forall n : nat, 
  let tn:= t0 + INR n * h  in 
  tn <= T -> 
  ∥ (p tn , q tn ) - (iternR (p t0, q t0) h n) ∥ <= 
  h^2 * ∥(p t0, q t0)∥ * ((1 + h)^ n - 1) .
Proof.
intros ? ? ? ? ? HBND HSY; intros.
assert (1  + h <> 1) by nra.
induction n.
+ 
 subst tn. 
rewrite Rmult_0_l. 
rewrite Rplus_0_r. unfold Rprod_minus, Rprod_norm, iternR, fst, snd.
repeat rewrite Rminus_eq_0.  rewrite Rmult_0_r. rewrite pow_i; try lia. rewrite Rplus_0_r.
rewrite sqrt_0. nra. 
+  subst tn.
pose proof 
  global_truncation_error_sum p q t0 T h HBND HSY (S n) H.
eapply Rle_trans. apply H1.
apply Req_le.
assert (0 < h) by (unfold ω in *; nra).
pose proof error_sum_GS (S n) h H2.
rewrite  H3.
field_simplify; nra.
Qed.

Lemma global_truncation_error: 
 forall p q: R -> R,
  forall t0 T : R,
  forall h : R, 
  0 < ω*h <= 2 -> 
  Harmonic_oscillator_system p q 1 t0 -> 
  forall n : nat, 
  let tn := t0 + INR n * h in
  tn <= T -> 
  ∥ (p (t0 + INR n * h)%R, q (t0 + INR n * h)%R) - (iternR (p t0, q t0) h n)∥
        <= h^ 2 * ∥(p t0, q t0)∥ * (exp (INR n *h) - 1) .
Proof.
intros ? ? ? ? ? HBND; intros.
subst tn.
eapply Rle_trans.
eapply global_truncation_error_aux; auto.
apply H0.
apply Rmult_le_compat_l.
pose proof (Rnorm_pos (p t0, q t0)); nra.
apply Rplus_le_compat_r.
apply bounded_one_plus_pow.
unfold ω in HBND; nra.
Qed.

Lemma convergence_aux: 
  forall p q: R -> R,
  forall t0 T : R,
  forall h : R, 
  0 <= t0 -> 
  0 < ω*h <= 2 -> 
  Harmonic_oscillator_system p q 1 t0 -> 
  forall n : nat, 
  let tn := t0 + INR n * h in
  tn <= T -> 
  ∥ (p tn, q tn) - (iternR (p t0, q t0) h n)∥ <= h^ 2 * (∥(p t0, q t0)∥ * (exp T - 1) ).
Proof.
intros ? ? ? ? ? ? HBND; intros.
subst tn.

eapply Rle_trans.
eapply global_truncation_error; auto.
apply H1.

rewrite <- Rmult_assoc.
eapply Rmult_le_compat_l.
pose proof (Rnorm_pos (p t0, q t0)); nra.
eapply Rplus_le_compat_r.
apply Raux.exp_le.

eapply Rle_trans.
assert (INR n * h <= t0 + INR n * h) by nra.
apply H2.
auto.
Qed.

Theorem method_convergence:
  forall p q: R -> R,
  forall t0 T : R,
  forall h : R, 
  0 <= t0 -> 
  0 < ω*h <= 2 -> 
  Harmonic_oscillator_system p q 1 t0 -> 
  forall n : nat, 
  let tn := t0 + INR n * h in
  tn <= T -> 
    (forall y,  
  t0 < t0 + INR n * y <= T) -> 
  is_lim 
    (fun h => ∥ (p (t0 + INR n * h)%R, q (t0 + INR n * h)%R) - (iternR (p t0, q t0) h n)∥) 0 0. 
Proof.
intros ? ? ? ? ? ? hbnd hsys ? ? ? hy.
induction n.
- simpl. 
apply (is_lim_ext ((fun h0 : R => 0))
  ((fun h0 : R =>
   ∥ Rprod_minus (p (t0 + 0 * h0)%R, q (t0 + 0 * h0)%R) (p t0, q t0) ∥))).
intros. rewrite Rmult_0_l. rewrite Rplus_0_r. unfold Rprod_minus, Rprod_norm. simpl.
repeat rewrite Rminus_eq_0. rewrite  Rmult_0_l. rewrite Rplus_0_r. rewrite sqrt_0; auto.
apply is_lim_const.
-
apply (is_lim_le_le_loc 
  (fun _ => 0) 
    (fun h => h^ 2 * (∥(p t0, q t0)∥ * (exp T - 1)))).
+ unfold Rbar_locally'. unfold locally'. unfold within. unfold locally. 
    assert ( 0 < 2) as bnd by (nra).
    exists (mkposreal 2 bnd). intros; split.
    * apply Rnorm_pos.
    * assert ( 0 < ω*y <= 2) as ybnd. split. 
      -- specialize (hy y).  rewrite Rplus_comm in hy. destruct hy as (hy & hy1).
        apply Rlt_minus_l in hy. rewrite Rminus_eq_0 in hy; auto. 
rewrite Rmult_1_l; apply mult_pos in hy; auto. rewrite S_INR. apply Rplus_le_le_0_compat; try nra. apply pos_INR.
      -- simpl in H1. rewrite Coquelicot.ball_to_lra in H1; simpl in H1. unfold ω in *; nra.
 --
specialize (hy y).
assert (t0 + INR (S n) * y <= T) by nra.
pose proof convergence_aux p  q t0 T y H ybnd hsys (S n) H3; auto.
  + apply is_lim_const.
+ pose proof 
      is_lim_mult (fun x => x^2) ( fun _ => ((∥ (p t0, q t0) ∥) * (exp T - 1))) 0 0 ((∥ (p t0, q t0) ∥) * (exp T - 1)) .
    rewrite Rbar_mult_0_l in H1.
apply H1.
    *  apply (is_lim_ext (fun h:R => h * h) (fun h:R => h ^ 2)). intros; nra.
        pose proof (is_lim_mult id id 0 0 0 (is_lim_id 0) (is_lim_id 0)).   
        simpl in H2. rewrite Rmult_0_l in H2. apply H2; auto.

   * apply is_lim_const.

   *unfold ex_Rbar_mult; auto.
Qed.

(* assuming we have an upper bound on powers of the transition matrix,
we can prove that each of the individual components of solution vector are
bounded. the choice of (sqrt 2) for the bound is justified by hand. *)
Lemma components_bounded : 
  forall p q h, 
  forall n,
    let (pn,qn) := iternR (p,q) h n in
  ∥(pn,qn)∥ <= (sqrt 2 * ∥(p,q)∥) -> 
  Rabs pn <= sqrt 2 * (∥(p,q)∥) /\ Rabs qn <= sqrt 2 * ∥(p,q)∥.
Proof.
intros. 
destruct (iternR (p,q) h n). 
intros; split; unfold Rprod_norm, fst, snd in *.
+ rewrite <- sqrt_mult_alt in H; try nra.
  apply sqrt_le_0 in H; try (apply sqr_plus_pos).
  assert (r ^ 2  <= 2 * (p ^ 2 + q ^ 2)) by nra.
  rewrite square_abs in H0. rewrite <-  sqrt_mult_alt ; try nra.
  apply sqrt_le. rewrite square_abs. auto.
  apply Rle_mult; try nra.
+ rewrite <- sqrt_mult_alt in H; try nra.
  apply sqrt_le_0 in H; try (apply sqr_plus_pos).
  assert (r0 ^ 2  <= 2 * (p ^ 2 + q ^ 2)) by nra.
  rewrite square_abs in H0. rewrite <-  sqrt_mult_alt ; try nra.
  apply sqrt_le. rewrite square_abs. auto.
  apply Rle_mult; try nra.
Qed.
