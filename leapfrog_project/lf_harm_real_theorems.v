From Coq Require Import ZArith Reals Psatz.
From Coq Require Import Arith.Arith.
Require Import real_lemmas lf_harm_real.
From Coquelicot Require Import Coquelicot.
Set Bullet Behavior "Strict Subproofs". 

Require Import Interval.Tactic.

(* This file contains real properties proofs for leapfrog integration of the 
harmonic oscillator. In particular, 
(1) The theorem "method_convergence" on line 719
shows that the numerical solution converges to the coninuous solution as the 
discretization parameter tends toward zero. 
(2) The theorem  "components bounded" on line 779 bounds the individual components of solution vector; 
these bounds are used for deriving tight round-off error bounds. a strong assumption
is currently made in this proof: we assume that we have a known upper bound on 
the powers of the transition matrix corresponding to our numerical method. *)



Open Scope R_scope.

Notation "∥ L ∥" := (Rprod_norm L) (at level 50).
Notation "∥·∥" := Rprod_norm (only parsing).


Notation " L1 .- L2 " := (Rprod_minus L1 L2) (at level 50, only parsing).

Notation " L1 .+ L2 " := (Rprod_plus L1 L2) (at level 50, only parsing).


(* the function f is k times differentiable in the interval [a,b] *)
Definition k_differentiable f k a b:=
  forall x, a<= x <= b -> forall n:nat, (n<=k)%nat ->  ex_derive_n f n x
.



(* a model for the continuous harmonic oscillator *) 
Definition Harmonic_osc_system p q w t0 p0 q0:=
  p t0 = p0 /\ q t0 = q0 /\  
  forall t, 
  Derive_n q 1 t  = p t /\  
  Derive_n q 2 t = (fun y => F (q y) w) t /\
  Rprod_norm ( p t , w * q t ) = Rprod_norm( p t0, w * q t0)
.



(* relating derivatives of the continuous system for future rewrites *)
Lemma Harm_sys_derive_eq p q w t0: 
  Harmonic_osc_system p q w t0 (p t0) (q t0)-> 
  forall t,
  Derive_n q 3 t  = - w ^2 * p t /\
  Derive_n p 2 t  = Derive_n q 3 t /\ 
  Derive_n p 3 t  = w ^4 * q t /\
  Derive_n p 4 t  = w^4 * p t.
Proof.
unfold Harmonic_osc_system; intros.
destruct H as (H1 & H2 & H).
pose proof (H t) as (A & B & C).
split.
+ replace (Derive_n q 3 t) with 
(Derive_n (fun y : R => F (q y) w) 1 t).
2: {
replace (Derive_n (fun y : R => F (q y) w) 1 t) with 
(Derive_n (Derive_n q 1) 2 t ).  
symmetry.
rewrite  Coquelicot.Derive_nS.
replace (Derive_n q 1) with (Derive q); auto.
replace (Derive_n (Derive_n q 1) 2 t) with
(Derive_n (Derive_n q 2) 1 t) by auto.
apply Derive_n_ext.
apply H.
}
unfold F. 
rewrite Derive_n_scal_l.
rewrite A; auto.
+ split. 
  - symmetry. 
    rewrite  Coquelicot.Derive_nS.
    replace (Derive q) with (Derive_n q 1); auto.
    apply Derive_n_ext.
    apply H.
  - split.
      ++ unfold F in B. 
         assert (Derive_n q 4 t =  - w^2 *  Derive_n q 2 t).
         rewrite  Coquelicot.Derive_nS. 
         rewrite  Coquelicot.Derive_nS.
         rewrite <- Derive_n_scal_l.
         apply Derive_n_ext. apply H.
         rewrite B in H0; field_simplify in H0.
         rewrite <- H0.
         replace (Derive_n q 4 t) with (Derive_n (Derive_n q 1) 3 t); auto.
         symmetry; apply Derive_n_ext; apply H.
    ++  rewrite <- A.
        replace (Derive_n p 4 t) with
        (Derive_n (Derive_n p 3) 1 t) by auto.
        rewrite <- Derive_n_scal_l.
        apply Derive_n_ext.
        intros.
        replace (w ^ 4 * q t1) with 
        (- w ^ 2 * Derive_n q 2 t1).
        rewrite <- Derive_n_scal_l.
        rewrite  Coquelicot.Derive_nS. 
        apply Derive_n_ext.
        intros.
        replace (- w ^ 2 * q t2) with
        ( Derive_n q 2 t2).
        rewrite  Coquelicot.Derive_nS.
         replace (Derive p) with (Derive_n p 1); auto.
        apply Derive_n_ext.
        intros.
        specialize (H t3).
        symmetry; replace (Derive q t3) with (Derive_n q 1 t3) by auto.
        apply H.
        specialize (H t2).
        destruct H as (_ & B1 & _).
        rewrite B1. unfold F; auto.
        specialize (H t1).
        destruct H as (_ & B1 & _).
        rewrite B1. unfold F; nra.
Qed.


(* a loose but simply stated upper bound on the norm of the componentwise
  expected remainders for the local errors resulting from the Taylor expansion of
  the continuous system  *)
Lemma Harm_sys_norm_bound p q:
  forall t0 t1 t2 t3,
  forall w h,
  0 < w ->
  (* the following hypothesis, derived from stability analysis on h,
     is required in order to show that (h w)^4/ 4! can be upper bounded by (h w)^3/ 3! *)
  0 < h * w < 2 ->
  Harmonic_osc_system p q w t0 (p t0) (q t0)-> 
  let '(r1, r2) := (h^4/INR(fact 4) * (Derive_n p 4 t2) - h^3/12 * w^4 * q t3, h^3/INR(fact 3) * w * (Derive_n q 3 t1)) in
  ∥(r1,r2)∥  <= (h*w)^3 * ∥(p t0 , w * q t0)∥.
Proof.
intros ? ? ? ? ? ? wpos hsep H.
unfold Harmonic_osc_system in H.
pose proof Harm_sys_derive_eq p q w t0 H t1 as (A & _ & _ & _).
pose proof Harm_sys_derive_eq p q w t0 H t2 as (_ & _ & _ & C2). 
rewrite A, C2. clear A C2.
destruct H as (HA & HB & H).
pose proof (H t1) as A1; destruct A1 as (_ & _ &C).
pose proof (H t2) as A1; destruct A1 as (_ & _ &C2).
specialize (H t3). destruct H as (_ & _ & C3). 
unfold Rprod_norm, fst, snd in *. cbv [prod_norm fst snd].
apply sqrt_inj in C, C2, C3; try nra.
assert (p t1 ^ 2  <= w ^2 * q t0 ^ 2 + p t0 ^ 2) by nra; 
  clear C.
assert (p t2 ^ 2  <= w ^2 * q t0 ^ 2 + p t0 ^ 2) by nra; 
  clear C2.
assert (w ^2 * q t3 ^ 2 <= w ^2 * q t0 ^ 2 + p t0 ^ 2) by nra; 
  clear C3.
set (y:= w ^ 2 * q t0 ^ 2 + p t0 ^ 2) in *. 
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
  replace ((h ^ 4 / INR (fact 4) * (w ^ 4 * p t2)) ^ 2)
  with ((h ^ 4 / INR (fact 4))^2 * (w ^ 4)^2 * (p t2) ^ 2) by nra.
  eapply Rmult_le_compat_l; try nra. apply H0.
  eapply Rle_trans.
  eapply Rplus_le_compat_r.
  eapply Rplus_le_compat_r.
  eapply Rplus_le_compat_l.
  replace ((h ^ 3 / 12 * w ^ 4 * q t3) ^ 2) 
  with ((h ^ 3 / 12)^2 * (w ^ 3)^2 * (w ^2 * q t3 ^ 2)) by nra.
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
  replace (Rabs (w ^ 4) * Rabs (q t3)) with
  (Rabs (w ^ 3) * Rabs (w * q t3)).
  eapply Rmult_le_compat_l. apply Rabs_pos.
  apply Rabs_pos_le in H1; try nra; auto.
  replace (w ^ 2 * q t3 ^ 2) with
  ((w * q t3) ^ 2) in H1.
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
  replace ((h ^ 3 / INR (fact 3) * w * (- w ^ 2 * p t1)) ^ 2)
  with ((h ^ 3 / INR (fact 3) )^2 * w^2 * (w ^ 2)^2 * (p t1) ^ 2) by nra.
  eapply Rmult_le_compat_l. nra.
  apply H.
  replace (Rabs 2 * (Rabs (h ^ 4 / INR (fact 4)) * (Rabs (w ^ 4) * sqrt (Rabs y))) *
  (Rabs (h ^ 3 / 12) * (Rabs (w ^ 3) * sqrt (Rabs y)))) with
  (2 * h ^ 4 / INR (fact 4) * w ^ 4 * h ^ 3 / 12 *  w ^ 3 * y).
  assert (h ^ 3 / 12 * w ^ 3 <= h ^ 3 / INR (fact 3) * (w ^ 3)).
  replace (INR (fact 3)) with (6) by (simpl;nra).
  apply Rmult_le_compat_r; try nra.
  assert (h ^ 4 / INR (fact 4) * w ^ 4 <= h ^ 3 / INR (fact 3) * (w ^ 3)).
  replace (INR (fact 4)) with (24) by (simpl;nra).
  replace (h ^ 4 / 24 * w ^ 4) with
  ((h * w)^3 * (h * w) * /24) by nra.
  replace (h ^ 3 / INR (fact 3) * w ^ 3) with
  ((h * w) ^ 3 * 4 *  /24) by (simpl; nra).
  apply Rmult_le_compat_r; try nra.
  eapply Rle_trans.
  apply Rplus_le_compat_r.
  apply Rplus_le_compat_r.
  eapply Rle_trans.
  apply Rplus_le_compat_r.
  apply Rmult_le_compat_r; try nra.
  replace ((h ^ 4 / INR (fact 4)) ^ 2 * (w ^ 4) ^ 2)
  with ((h ^ 4 / INR (fact 4) * (w ^ 4)) ^ 2) by nra.
  apply pow_incr.
  split. simpl. nra.
  apply H3.
  apply Rplus_le_compat_l.
  apply Rmult_le_compat_r; try nra.
  replace ((h ^ 3 / 12) ^ 2 * (w ^ 3) ^ 2)
  with ((h ^ 3 / 12 * w ^ 3) ^ 2) by nra.
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
  replace (2 * h ^ 4 / INR (fact 4) * w ^ 4)
  with (2 * (h ^ 4 / INR (fact 4) * w ^ 4)) by nra.
  apply Rmult_le_compat_l; try nra. 
  apply H3.
  rewrite Rmult_assoc.
  rewrite Rmult_assoc.
  apply Rmult_le_compat_l.
  repeat (apply Rle_mult; simpl; try nra).
  rewrite <- Rmult_assoc.
  apply H2.
  match goal with |- context [?a <= ?b] =>
  replace a with ( 5 * (h ^ 3 / INR (fact 3)) ^ 2 * (w ^ 3) ^ 2 * y);
  replace b with  ((h ^3)^2 * (w ^ 3)^2 * (w^2 * q t0 ^2 + p t0 ^ 2))
  end.
  subst y.
  apply Rmult_le_compat_r; try (simpl; nra).
  rewrite Rpow_mult_distr.
  rewrite pow2_sqrt. nra. nra.
  replace ((h ^ 3 / INR (fact 3)) ^ 2 * w ^ 2 * (w ^ 2) ^ 2 * y)
  with ((h ^ 3 / INR (fact 3)) ^ 2 * (w ^ 3) ^ 2 * y) by nra.
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
  replace (sqrt (Rabs y) * (Rabs (h ^ 3 / 12 * w ^ 3) * sqrt (Rabs y))) with 
  ((Rabs y) * Rabs (h ^ 3 / 12 * w ^ 3)).
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
Theorem local_truncation_error_aux:
  forall p q: R -> R,
  forall t0 tn: R,
  forall h : R, 
  0 < h < 2 -> 
  Harmonic_osc_system p q 1 t0 (p t0) (q t0) -> 
  (forall t1 t2: R,
  k_differentiable p 4 t1 t2 /\
  k_differentiable q 3 t1 t2)  ->
  exists t1 t2: R,
  tn < t1 < tn + h /\
  tn < t2 < tn + h /\
  q (tn + h) - snd(leapfrog_stepR (p tn, q tn) h) = 
    h^3 / INR (fact 3) * Derive_n q 3 t1 /\
  p (tn + h) - fst(leapfrog_stepR (p tn,  q tn) h) = 
    h^4 / INR (fact 4) * Derive_n p 4 t2 - h^3 / 12 * q tn . 
Proof.
intros ? ? ? ? ? Hbnd HSY; intros.
assert (tn < tn + h) as LT by nra.
specialize (H  tn (tn + h)).
destruct H as ( KP & KQ); unfold k_differentiable in *.
(* apply Taylor's theorem for each component of the solution vector *) 
pose proof Taylor_Lagrange q 2 tn (tn + h) LT KQ as TLRq. 
pose proof Taylor_Lagrange p 3 tn (tn + h) LT KP as TLRp.
destruct TLRq as (t1 & A & B). 
destruct TLRp as (t2 & C & D).
replace (tn + h - tn) with h in * by nra.
pose proof Harm_sys_derive_eq p q 1 t0 HSY tn as (HD1 & HD2 & HD3 & HD4).
unfold Harmonic_osc_system in HSY.
exists t1, t2. 
repeat split; try apply A; try apply C.
  + rewrite B. cbv [sum_f_R0].
    destruct HSY as (HA & HB & HSY).
    specialize (HSY tn). destruct HSY as (Hxd1 & Hxd2 & _ ).
    rewrite Hxd1, Hxd2. 
    unfold Derive_n at 1. unfold F.
    unfold leapfrog_stepR, fst, snd.
    simpl; nra.
  + rewrite D. cbv [sum_f_R0].
    replace (Derive_n p 2 tn) with 
    (Derive_n (fun y : R => F (q y) 1) 1 tn). 
    2: {
    replace (Derive_n (fun y : R => F (q y) 1) 1 tn) with 
    (Derive_n (Derive_n q 1) 2 tn ). 
    (apply Derive_n_ext; apply HSY).
    replace (Derive_n (Derive_n q 1) 2 tn) with
    (Derive_n (Derive_n q 2) 1 tn) by auto.
    apply Derive_n_ext.
    apply HSY.
    }
    unfold F. 
    rewrite Derive_n_scal_l.
    replace (Derive_n p 1 tn) with 
    (Derive_n q 2 tn) by (
    replace (Derive_n q 2 tn) with
    (Derive_n (Derive_n q 1) 1 tn) by auto;
    apply Derive_n_ext; apply HSY).
    destruct HSY as (HA & HB & HSY).
    specialize (HSY tn). destruct HSY as (Hxd1 & Hxd2 & _).
    rewrite Hxd2. rewrite Hxd1. unfold Derive_n at 1.
    rewrite HD3. 
    unfold leapfrog_stepR, F, fst, snd.
    simpl; nra.
Qed.



(* upper bound the norm of the truncation error *)
Theorem local_truncation_error_norm_aux:
  forall p q: R -> R,
  forall t0 tn: R,
  forall h : R, 
  0 < h < 2 -> 
  Harmonic_osc_system p q 1 t0 (p t0) (q t0) ->
  (forall t1 t2: R,
  k_differentiable p 4 t1 t2 /\
  k_differentiable q 3 t1 t2)  ->
  exists t1 t2: R,
  tn < t1 < tn + h /\
  tn < t2 < tn + h /\
  let '(r1, r2) := (h^4/INR(fact 4) * Derive_n p 4 t2 - h^3 / 12 * q tn,  h^3/INR(fact 3) * Derive_n q 3 t1) in
  ∥(p (tn + h), q (tn + h)) .- (leapfrog_stepR (p tn, q tn) h)∥ <= ∥(r1 , r2)∥.
Proof.
intros ? ? ? ? ? Hbnd HSY; intros.
pose proof local_truncation_error_aux p q t0 tn h Hbnd HSY H as LTE.
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



(* a simply stated loose local error bound *) 
Theorem local_truncation_error_norm:
  forall p q: R -> R,
  forall t0 tn,
  forall h : R, 
  0 < h < 2 -> 
  Harmonic_osc_system p q 1 t0 (p t0) (q t0) -> 
  (forall t1 t2: R,
  k_differentiable p 4 t1 t2 /\
  k_differentiable q 3 t1 t2)  ->
  let '(pn,qn):= (leapfrog_stepR (p tn, q tn) h ) in
  ∥(p (tn + h), q (tn + h)) .- (pn, qn)∥ <= h^3 * ∥(p t0,  q t0)∥.
Proof.
intros ? ? ? ? ? Hbnd HSY; intros.
pose proof local_truncation_error_norm_aux 
  p q t0 tn h Hbnd HSY H as (t1 & t2 & A & B & C).
eapply Rle_trans.
apply C.
specialize (H t1 t2).
eapply Rle_trans.
assert (HBND2: 0 < h * 1 < 2) by nra.
pose proof ( Harm_sys_norm_bound p q t0 t1 t2 tn 1 h Rlt_0_1 HBND2 HSY)as Hsys.
rewrite pow1 in Hsys. 
repeat rewrite Rmult_1_r in Hsys.
apply Hsys. 
rewrite Rmult_1_l.
apply Req_le. auto. 
Qed.



Lemma method_norm_bounded_aux_p : 
forall p q h: R,
0 < h < 2 ->
Rabs (fst(leapfrog_stepR (p,q) h)) <=  Rabs p + h * Rabs q.
Proof.
intros.
unfold leapfrog_stepR, fst, snd.
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
0 < h <  2 ->
Rabs (snd(leapfrog_stepR (p,q) h)) <=  Rabs q + h * Rabs p.
Proof.
intros.
unfold leapfrog_stepR, fst, snd.
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


 

(* a loose upper bound on the norm of the method *)
Lemma method_norm_bounded : 
forall p q h: R,
0 < h < 2 ->
∥(leapfrog_stepR (p,q) h)∥ <= (1 + h) * ∥(p,q)∥.
Proof.
intros.
pose proof method_norm_bounded_aux_q p q h H.
pose proof method_norm_bounded_aux_p p q h H.
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




Lemma global_truncation_error_sum : 
  forall p q: R -> R,
  forall t0 : R,
  forall h : R, 
  0 < h < 2 -> 
  Harmonic_osc_system p q 1 t0 (p t0) (q t0) -> 
  (forall t1 t2: R,
  k_differentiable p 4 t1 t2 /\
  k_differentiable q 3 t1 t2)  ->
  forall n : nat, 
  ∥ (p (t0 + INR n * h), q (t0 + INR n * h)) .- (iternR (p t0, q t0) h n)∥
    <= h^3 * ∥(p t0,  q t0)∥ * error_sum (1 + h) n.
Proof.
intros ? ? ? ? HBND HSY; intros. 
induction n.
+ simpl. 
rewrite Rmult_0_l. rewrite Rmult_0_r.
rewrite Rplus_0_r. unfold Rprod_minus, Rprod_norm, fst, snd.
repeat rewrite Rminus_eq_0. rewrite pow_i. rewrite Rplus_0_r.
rewrite sqrt_0. nra. lia.
+ rewrite step_iternR.
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
pose proof local_truncation_error_norm p q t0 (t0 + INR n * h) h HBND HSY H.
fold phi1 in H0.
eapply Rle_trans.
eapply Rplus_le_compat_r.
rewrite S_INR.
replace (t0 + (INR n + 1) * h) with (t0 + INR n * h + h) by nra.
apply H0.
eapply Rle_trans.
eapply Rplus_le_compat_l.
subst phi1 phi2.
pose proof leapfrog_minus_args
(p (t0 + INR n * h), q (t0 + INR n * h))
(iternR (p t0, q t0) h n).
rewrite H1.
pose proof (method_norm_bounded).
apply H2; auto. 
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
  forall t0 : R,
  forall h : R, 
  0 < h < 2 -> 
  Harmonic_osc_system p q 1 t0 (p t0) (q t0)->
  (forall t1 t2: R,
  k_differentiable p 4 t1 t2 /\
  k_differentiable q 3 t1 t2)  ->
  forall n : nat, 
  ∥ (p (t0 + INR n * h), q (t0 + INR n * h)) .- (iternR (p t0, q t0) h n) ∥ <= 
  h^2 * ∥(p t0, q t0)∥ * ((1 + h)^ n - 1) .
Proof.
intros ? ? ? ? HBND HSY; intros.
assert (1  + h <> 1) by nra.
induction n.
+ unfold Rprod_minus, Rprod_norm. simpl.
rewrite Rmult_0_l. rewrite Rplus_0_r. 
repeat rewrite Rmult_1_r. 
replace (p t0 - p t0) with 0 by nra.
replace (q t0 - q t0) with 0 by nra.
field_simplify. rewrite Rmult_0_l. 
replace (0+0) with 0 by nra.
rewrite sqrt_0. nra.
+  
pose proof 
  global_truncation_error_sum p q t0 h HBND HSY H (S n).
eapply Rle_trans. apply H1.
apply Req_le.
assert (0 < h) by nra.
pose proof error_sum_GS (S n) h H2.
rewrite  H3.
field_simplify; nra.
Qed.




Lemma global_truncation_error: 
  forall p q: R -> R,
  forall t0 : R,
  forall h : R, 
  0 < h < 2 -> 
  Harmonic_osc_system p q 1 t0 (p t0) (q t0) -> 
  (forall t1 t2: R,
  k_differentiable p 4 t1 t2 /\
  k_differentiable q 3 t1 t2)  ->
  forall n : nat, 
  ∥ (p (t0 + INR n * h), q (t0 + INR n * h)) .- (iternR (p t0, q t0) h n)∥ <= h^ 2 * ∥(p t0, q t0)∥ * (exp (INR n *h) - 1) .
Proof.
intros ? ? ? ? HBND; intros.
eapply Rle_trans.
apply global_truncation_error_aux; auto.
eapply Rle_trans.
eapply Rmult_le_compat_l.
nra.
apply Rmult_le_compat_l.
apply Rnorm_pos.
apply Rplus_le_compat_r.
apply bounded_one_plus_pow.
nra.
nra.
Qed.



(* this is the main theorem regarding the convergence of the method. in particular, we see
that, as h approached zero, the numerical solution converges to the continuous solution *)
Theorem method_convergence:
  forall p q: R -> R,
  forall t0 : R,
  forall h : R, 
  0 < h < 2 -> 
  Harmonic_osc_system p q 1 t0 (p t0) (q t0) ->
  (forall t1 t2: R,
  k_differentiable p 4 t1 t2 /\
  k_differentiable q 3 t1 t2)  ->
  forall n : nat, 
  (forall y,  
  t0 < t0 + y) -> 
  is_lim 
    (fun h => ∥ (p (t0 + INR n * h), q (t0 + INR n * h)) .- (iternR (p t0, q t0) h n)∥) 0 0. 
Proof.
intros ? ? ? ? hbnd hsys ? ? hy. 
induction n.
* simpl. 
apply (is_lim_ext ((fun h0 : R => 0))
  ((fun h0 : R =>
   ∥ Rprod_minus (p (t0 + 0 * h0), q (t0 + 0 * h0)) (p t0, q t0) ∥))).
intros. rewrite Rmult_0_l. rewrite Rplus_0_r. unfold Rprod_minus, Rprod_norm. simpl.
repeat rewrite Rminus_eq_0. rewrite  Rmult_0_l. rewrite Rplus_0_r. rewrite sqrt_0; auto.
apply is_lim_const.
* apply (is_lim_le_le_loc 
  (fun _ => 0) 
    (fun h => h^ 2 * ∥(p t0, q t0)∥ * (exp (INR (S n) *h) - 1))).
  + unfold Rbar_locally'. unfold locally'. unfold within. unfold locally. 
    assert ( 0 < 2) as bnd by (nra).
    exists (mkposreal 2 bnd). intros; split.
    ++ apply Rnorm_pos.
    ++ assert ( 0 < y < 2) as ybnd. split. 
      - specialize (hy y).  rewrite Rplus_comm in hy.
        apply Rlt_minus_l in hy. rewrite Rminus_eq_0 in hy; auto.
      - simpl in H0. rewrite Coquelicot.ball_to_lra in H0; nra.
      - pose proof global_truncation_error p q t0 y ybnd hsys H (S n); auto.
  + apply is_lim_const.
  + pose proof 
      is_lim_mult (fun x => x^2) ( fun x => ((∥ (p t0, q t0) ∥) * (exp (INR (S n) * x) - 1))) 0 0 0 .
    rewrite Rbar_mult_0_l in H0.
    apply H0.
    ++  apply (is_lim_ext (fun h:R => h * h) (fun h:R => h ^ 2)). intros; nra.
        pose proof (is_lim_mult id id 0 0 0 (is_lim_id 0) (is_lim_id 0)).   
        simpl in H1. rewrite Rmult_0_l in H1. apply H1; auto.
    ++  pose proof 
        (is_lim_scal_l (fun x => (exp (INR (S n) * x) - 1)) (∥ (p t0, q t0) ∥) 0 0).
        rewrite Rbar_mult_0_r in H1.
        apply H1.
        eapply is_lim_minus.
        apply is_lim_exp_pow. apply is_lim_const.
        unfold is_Rbar_minus. simpl. unfold is_Rbar_plus. 
        simpl. f_equal. rewrite Rplus_opp_r. auto.
    ++ unfold ex_Rbar_mult; auto.
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


Close Scope R_scope. 
