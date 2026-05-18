(** * Backward error analysis for leapfrog on the simple harmonic oscillator.

    This file establishes that the leapfrog integrator preserves a
    modified Hamiltonian [Hh] exactly (in real arithmetic), and uses
    that fact to bound the energy mismatch between the discrete
    trajectory and the continuous truth.

    Specialized to omega = 1 throughout, matching [real_model.v] and
    [float_model.v].

    Background
    ----------
    Leapfrog on the SHO is symplectic and the original Hamiltonian is
    quadratic, so the discrete map preserves a *modified* quadratic
    Hamiltonian [Hh] exactly (not approximately):

      H_true(p, q) := (p^2 + q^2) / 2
      Hh(p, q)     := (p^2 + (1 - h^2/4) q^2) / 2

    One can verify by direct substitution into the leapfrog step

      p' = (1 - h^2/2) p - h(1 - h^2/4) q
      q' = (1 - h^2/2) q + h p

    that p'^2 + (1 - h^2/4) q'^2 = p^2 + (1 - h^2/4) q^2.

    Consequence
    -----------
    Starting from (p, q) = (0, 1) (the initial condition fixed by
    [p_init] / [q_init] in [float_model.v]):

      Hh(iter_n)     = Hh(0, 1) = (1 - h^2/4) / 2   for all n
      H_true(truth)  = H_true(0, 1) = 1/2           for all t
      H_true - Hh    = (h^2/8) * q^2  (everywhere)

    So H_true(iter_n) is pinned to [(1 - h^2/4)/2, 1/2], differing from
    the true energy 1/2 by at most h^2/8.

    For h = 1/32: h^2/8 = 1 / 8192 ~= 1.22e-4, constant in n.

    Compare to the standard bound (n*h^3 = n/32768) which at n=1000 gives
    ~3e-2. The energy mismatch is constant in n; the existing bound
    grows linearly. This file proves the constant-in-n energy bound.
*)

From Stdlib Require Import ZArith Reals Psatz.
Require Import real_lemmas real_model harmonic_oscillator_system.

Set Bullet Behavior "Strict Subproofs".
Open Scope R_scope.

(** ** Hamiltonians *)

Definition Hh (h : R) (pq : R * R) : R :=
  let p := fst pq in
  let q := snd pq in
  (p^2 + (1 - h^2 / 4) * q^2) / 2.

Definition Htrue (pq : R * R) : R :=
  let p := fst pq in
  let q := snd pq in
  (p^2 + q^2) / 2.

(** ** One-step conservation of [Hh] under [leapfrog_stepR]. *)

Lemma Hh_step_preserved : forall h pq,
  Hh h (leapfrog_stepR h pq) = Hh h pq.
Proof.
intros h [p q].
unfold Hh, leapfrog_stepR, ω, fst, snd.
field_simplify.
nra.
Qed.

(** ** n-step conservation of [Hh] under iteration of [leapfrog_stepR]. *)

Lemma Hh_iter_preserved : forall n h pq,
  Hh h (iternR pq h n) = Hh h pq.
Proof.
induction n; intros h pq.
- reflexivity.
- simpl. rewrite IHn. apply Hh_step_preserved.
Qed.

(** ** Exact difference between true and modified energy. *)

Lemma Htrue_minus_Hh : forall h pq,
  Htrue pq - Hh h pq = (h^2 / 8) * (snd pq)^2.
Proof.
intros h [p q].
unfold Htrue, Hh, fst, snd.
field.
Qed.

(** ** Position bound along the discrete orbit from [(0, 1)].

    Because [Hh] is conserved equal to [Hh(0, 1) = (1 - h^2/4)/2], the
    discrete orbit lies on the level set
       p^2 + (1 - h^2/4) q^2 = 1 - h^2/4
    and so q^2 in [0, 1]. *)

Lemma iter_q_squared_bounded : forall n h,
  0 < h^2 < 4 ->
  0 <= (snd (iternR (0, 1) h n))^2 <= 1.
Proof.
intros n h Hbound.
pose proof (Hh_iter_preserved n h (0, 1)) as Hcons.
unfold Hh in Hcons. simpl in Hcons.
set (pn := fst (iternR (0, 1) h n)) in *.
set (qn := snd (iternR (0, 1) h n)) in *.
(* Hcons:  (pn^2 + (1 - h^2/4) * qn^2) / 2 = (0^2 + (1 - h^2/4) * 1^2) / 2 *)
assert (Hpq: pn^2 + (1 - h^2/4) * qn^2 = 1 - h^2/4) by nra.
split.
- nra.
- nra.
Qed.

(** ** Top theorem: energy mismatch bound, constant in n.

    For any n, the true energy of the discrete iterate from (0, 1)
    differs from the conserved true-energy of the continuous orbit
    (which is [1/2]) by at most [h^2 / 8]. *)

Theorem BEA_energy_mismatch :
  forall n h, 0 < h^2 < 4 ->
  Rabs (Htrue (iternR (0, 1) h n) - 1/2) <= h^2 / 8.
Proof.
intros n h Hbound.
pose proof (Hh_iter_preserved n h (0, 1)) as Hcons.
pose proof (Htrue_minus_Hh h (iternR (0, 1) h n)) as Hdiff.
pose proof (iter_q_squared_bounded n h Hbound) as [Hq_lo Hq_hi].
(* Reduce Hh h (0, 1) to a concrete expression. *)
assert (HhInit : Hh h (0, 1) = (1 - h^2/4) / 2) by (unfold Hh; simpl; lra).
rewrite HhInit in Hcons.
(* Now Hcons : Hh h (iter) = (1 - h^2/4)/2 *)
(* And Hdiff : Htrue iter - Hh h iter = (h^2/8) * (snd iter)^2 *)
apply Rabs_le.
split; nra.
Qed.

(** ** Concrete corollary: the energy mismatch at h = 1/32 is at most 1/8192. *)

Corollary BEA_energy_mismatch_concrete :
  forall n,
  Rabs (Htrue (iternR (0, 1) (1/32) n) - 1/2) <= 1 / 8192.
Proof.
intros n.
eapply Rle_trans.
- apply BEA_energy_mismatch with (h := 1/32). nra.
- nra.
Qed.

(** * State-error bound from BEA — extending the file with a parallel,
      tighter result for the real-arithmetic iterate.

    The energy mismatch above is constant in [n]; to get a state-error
    bound (also tighter than the existing [global_truncation_error_sum])
    we identify the discrete iterate in closed form via the rotation
    interpretation of leapfrog, then bound its distance from the
    continuous truth using the Lipschitz constants of [sin] and [cos]
    (both 1). We avoid sum-to-product trig identities. *)

From Coquelicot Require Import Coquelicot.
Require Import Interval.Tactic.

(** ** Building blocks *)

Definition theta_h (h : R) : R := acos (1 - h^2 / 2).
Definition p_sol (t : R) : R := - sin t.
Definition q_sol (t : R) : R := cos t.

(** ** Lipschitz continuity of sin and cos.

    [sin] and [cos] are globally 1-Lipschitz because their derivatives
    are [cos] and [-sin], both bounded by 1 in absolute value. We
    derive this from Coquelicot's [MVT_gen] (the same MVT the project
    uses in [harmonic_oscillator_system.v]). *)

Lemma Rabs_sin_diff_le : forall a b,
  Rabs (sin a - sin b) <= Rabs (a - b).
Proof.
intros a b.
destruct (MVT_gen sin a b cos) as [c [_ Heq]].
- intros x _. apply is_derive_sin.
- intros x _. apply continuity_sin.
- replace (sin a - sin b) with (- (sin b - sin a)) by ring.
  rewrite Rabs_Ropp, Heq, Rabs_mult.
  rewrite (Rabs_minus_sym a b).
  rewrite <- (Rmult_1_l (Rabs (b - a))) at 2.
  apply Rmult_le_compat_r; [apply Rabs_pos|].
  apply Rabs_le. pose proof (COS_bound c). lra.
Qed.

Lemma Rabs_cos_diff_le : forall a b,
  Rabs (cos a - cos b) <= Rabs (a - b).
Proof.
intros a b.
destruct (MVT_gen cos a b (fun x => - sin x)) as [c [_ Heq]].
- intros x _. apply is_derive_cos.
- intros x _. apply continuity_cos.
- replace (cos a - cos b) with (- (cos b - cos a)) by ring.
  rewrite Rabs_Ropp, Heq, Rabs_mult.
  rewrite (Rabs_minus_sym a b).
  rewrite <- (Rmult_1_l (Rabs (b - a))) at 2.
  apply Rmult_le_compat_r; [apply Rabs_pos|].
  rewrite Rabs_Ropp. apply Rabs_le. pose proof (SIN_bound c). lra.
Qed.

(** ** Rotation entries (Step 1 of the L2-norm BEA proof).

    Avoiding [acos]: we define the rotation entries [c_h] and [s_h]
    directly in terms of [h], skipping [theta_h := acos(1 - h^2/2)]
    entirely. These satisfy [c_h^2 + s_h^2 = 1] (algebraic identity),
    which is what makes the discrete leapfrog step a 2D rotation. *)

Definition c_h (h : R) : R := 1 - h^2 / 2.
Definition s_h (h : R) : R := h * sqrt (1 - h^2 / 4).

Lemma c_h_s_h_unit : forall h,
  0 <= h^2 <= 4 ->
  (c_h h)^2 + (s_h h)^2 = 1.
Proof.
intros h Hh.
unfold c_h, s_h.
rewrite Rpow_mult_distr.
rewrite pow2_sqrt by lra.
nra.
Qed.

(** ** Step 2 — leapfrog_stepR is a rotation in deformed coordinates.

    With [qd := sqrt(1 - h^2/4) * q], the leapfrog step is exactly
    multiplication by the rotation matrix [[c_h, -s_h], [s_h, c_h]] on
    the deformed vector [(p, qd)]. This is an algebraic identity. *)

Lemma leapfrog_stepR_matrix_form : forall h pq,
  0 < h^2 < 4 ->
  fst (leapfrog_stepR h pq)
    = c_h h * fst pq - s_h h * (sqrt (1 - h^2/4) * snd pq)
  /\ sqrt (1 - h^2/4) * snd (leapfrog_stepR h pq)
    = s_h h * fst pq + c_h h * (sqrt (1 - h^2/4) * snd pq).
Proof.
intros h [p q] Hh.
set (sq := sqrt (1 - h^2/4)).
assert (Hsq: sq * sq = 1 - h^2/4) by (subst sq; apply sqrt_sqrt; lra).
unfold leapfrog_stepR, c_h, s_h, ω, fst, snd.
fold sq.
split.
- replace (h * sq * (sq * q)) with (h * (sq * sq) * q) by ring.
  rewrite Hsq.
  nra.
- nra.
Qed.

(** ** Step 3 — M_iter, the (sin, cos) sequence as a Fixpoint.

    [(a_n, b_n) := (sin(n * theta_h), cos(n * theta_h))] viewed as a
    recurrence with [c_h, s_h] — defined directly without [acos]. *)

Fixpoint M_iter (h : R) (n : nat) : R * R :=
  match n with
  | 0%nat => (0, 1)
  | S n'  => let (a, b) := M_iter h n' in
             (c_h h * a + s_h h * b, c_h h * b - s_h h * a)
  end.

(** ** Step 4 — iternR's components equal the (deformed) M_iter.

    [iternR (0, 1) h n = (- sqrt(1 - h^2/4) * a_n, b_n)].

    The p-component requires [sq^2 = 1 - h^2/4]; the q-component is
    pure polynomial algebra (the formula [q' = c_h * q + h * p] for
    [leapfrog_stepR] gives [c_h * b + h * (-sq * a) = c_h * b - s_h * a]
    directly when [s_h = h * sq]). *)

Lemma M_iter_S : forall h n,
  M_iter h (S n) =
    (c_h h * fst (M_iter h n) + s_h h * snd (M_iter h n),
     c_h h * snd (M_iter h n) - s_h h * fst (M_iter h n)).
Proof.
intros h n. simpl. destruct (M_iter h n) as [a b]. reflexivity.
Qed.

Lemma iternR_as_M_iter : forall n h,
  0 < h^2 < 4 ->
  iternR (0, 1) h n =
    (- sqrt (1 - h^2/4) * fst (M_iter h n),
     snd (M_iter h n)).
Proof.
intros n h Hh.
set (sq := sqrt (1 - h^2/4)).
assert (Hsq_pos: 0 < sq) by (subst sq; apply sqrt_lt_R0; lra).
induction n.
- cbn. f_equal; ring.
- rewrite step_iternR_2.
  fold sq in IHn.
  rewrite IHn.
  rewrite M_iter_S.
  set (P := fst (M_iter h n)).
  set (Q := snd (M_iter h n)).
  cbn [fst snd].
  pose proof (leapfrog_stepR_matrix_form h (- sq * P, Q) Hh) as [Hp Hq].
  cbn [fst snd] in Hp, Hq.
  fold sq in Hp, Hq.
  apply injective_projections; cbn [fst snd].
  + (* fst: by ring after rewrite. *)
    rewrite Hp. ring.
  + (* snd: multiply by sq, then use Hq; close by ring. *)
    apply (Rmult_eq_reg_l sq); [|lra].
    rewrite Hq. ring.
Qed.

(** ** Step 5 — M_iter stays on the unit circle.

    By induction: each step is a 2D rotation (preserves norm). *)

Lemma M_iter_unit : forall n h,
  0 <= h^2 <= 4 ->
  (fst (M_iter h n))^2 + (snd (M_iter h n))^2 = 1.
Proof.
intros n h Hh.
pose proof (c_h_s_h_unit h Hh) as Hunit.
induction n.
- cbn. nra.
- rewrite M_iter_S.
  cbn [fst snd].
  nra.
Qed.

(** ** Step 6 — Per-step truncation bounds at h = 1/32 (via Interval).

    α := c_h(1/32) − cos(1/32) ≈ −4.07e−8
    β := s_h(1/32) − sin(1/32) ≈ +1.27e−6
    The drive norm √(α² + β²) ≈ 1.27e−6 controls per-step error
    accumulation in the L2 recurrence (Step 8). *)

Lemma alpha_bound :
  Rabs (c_h (1/32) - cos (1/32)) <= 5 / 10^8.
Proof.
unfold c_h.
interval with (i_prec 80).
Qed.

Lemma beta_bound :
  Rabs (s_h (1/32) - sin (1/32)) <= 13 / 10^7.
Proof.
unfold s_h.
interval with (i_prec 80).
Qed.

Lemma drive_norm_sq_bound :
  (c_h (1/32) - cos (1/32))^2 + (s_h (1/32) - sin (1/32))^2 <= (13 / 10^7)^2 + (5 / 10^8)^2.
Proof.
unfold c_h, s_h.
interval with (i_prec 80).
Qed.

(** ** Step 7 — Continuous trajectory recurrence (angle addition).

    [sin] and [cos] of [INR (S n) * h] decompose via [sin_plus] /
    [cos_plus] into a recurrence with [cos h], [sin h] — parallel to
    the [c_h], [s_h] recurrence in [M_iter]. *)

Lemma true_evolution_recurrence : forall n h,
  sin (INR (S n) * h) = cos h * sin (INR n * h) + sin h * cos (INR n * h)
  /\ cos (INR (S n) * h) = cos h * cos (INR n * h) - sin h * sin (INR n * h).
Proof.
intros n h.
rewrite S_INR.
replace ((INR n + 1) * h) with (INR n * h + h) by ring.
split.
- rewrite sin_plus. ring.
- rewrite cos_plus. ring.
Qed.

(** ** Helpers for Step 8 *)

Lemma M_action_norm_invariant : forall theta x y,
  Rprod_norm (cos theta * x + sin theta * y,
              - sin theta * x + cos theta * y) = Rprod_norm (x, y).
Proof.
intros theta x y.
unfold Rprod_norm. simpl. f_equal.
pose proof (sin2_cos2 theta) as H. unfold Rsqr in H.
nra.
Qed.

Lemma drive_vec_norm : forall a b α β,
  a^2 + b^2 = 1 ->
  Rprod_norm (α * a + β * b, α * b - β * a) = Rprod_norm (α, β).
Proof.
intros a b α β Hab.
unfold Rprod_norm. simpl. f_equal. nra.
Qed.

(** ** Step 8 — L2 error grows by at most √(α² + β²) per step.

    The recurrence decomposes [(e_a', e_b')] as (rotation acting on the
    previous error) + (drive vector α/β times (a, b)). Triangle inequality
    on [Rprod_norm], rotation preserves norm, and the drive vector has
    norm √(α² + β²) since (a, b) sits on the unit circle. *)

Lemma error_growth_per_step : forall n h, 0 < h^2 < 4 ->
  Rprod_norm
    (fst (M_iter h (S n)) - sin (INR (S n) * h),
     snd (M_iter h (S n)) - cos (INR (S n) * h)) <=
  Rprod_norm
    (fst (M_iter h n) - sin (INR n * h),
     snd (M_iter h n) - cos (INR n * h)) +
  Rprod_norm (c_h h - cos h, s_h h - sin h).
Proof.
intros n h Hh.
pose proof (M_iter_unit n h ltac:(lra)) as Hunit.
rewrite M_iter_S.
destruct (true_evolution_recurrence n h) as [Hsin Hcos].
rewrite Hsin, Hcos.
cbn [fst snd].
remember (fst (M_iter h n)) as a eqn:Heqa.
remember (snd (M_iter h n)) as b eqn:Heqb.
clear Heqa Heqb.
remember (sin (INR n * h)) as sa.
remember (cos (INR n * h)) as cb.
clear Heqsa Heqcb.
(* Replace components with (rotation + drive) decomposition *)
replace (c_h h * a + s_h h * b - (cos h * sa + sin h * cb))
  with (cos h * (a - sa) + sin h * (b - cb)
        + ((c_h h - cos h) * a + (s_h h - sin h) * b)) by ring.
replace (c_h h * b - s_h h * a - (cos h * cb - sin h * sa))
  with (- sin h * (a - sa) + cos h * (b - cb)
        + ((c_h h - cos h) * b - (s_h h - sin h) * a)) by ring.
(* Apply triangle inequality on Rprod_norm *)
eapply Rle_trans.
- pose proof (Rprod_triang_ineq
    (cos h * (a - sa) + sin h * (b - cb), - sin h * (a - sa) + cos h * (b - cb))
    ((c_h h - cos h) * a + (s_h h - sin h) * b, (c_h h - cos h) * b - (s_h h - sin h) * a))
    as Htri.
  unfold Rprod_plus in Htri. cbn [fst snd] in Htri.
  exact Htri.
- (* Simplify each norm via the helper lemmas *)
  rewrite M_action_norm_invariant.
  rewrite (drive_vec_norm a b _ _ Hunit).
  apply Rle_refl.
Qed.

(** ** Step 9 — Linear-in-n L2 bound by induction. *)

Lemma error_grows_linearly_in_n : forall n h, 0 < h^2 < 4 ->
  Rprod_norm
    (fst (M_iter h n) - sin (INR n * h),
     snd (M_iter h n) - cos (INR n * h)) <=
  INR n * Rprod_norm (c_h h - cos h, s_h h - sin h).
Proof.
intros n h Hh.
induction n.
- (* n = 0: M_iter h 0 = (0, 1), sin/cos of 0 give (0, 1), so error is 0 *)
  cbn -[Rprod_norm INR sin cos].
  rewrite Rmult_0_l, sin_0, cos_0.
  rewrite Rmult_0_l.
  assert (Hzero: Rprod_norm (0 - 0, 1 - 1) = 0).
  { unfold Rprod_norm. simpl.
    transitivity (sqrt 0); [f_equal; nra | apply sqrt_0]. }
  rewrite Hzero. lra.
- eapply Rle_trans; [apply (error_growth_per_step n h Hh) |].
  rewrite S_INR.
  rewrite Rmult_plus_distr_r, Rmult_1_l.
  apply Rplus_le_compat_r.
  exact IHn.
Qed.

(** ** Helper for Step 10 — the radial-mismatch bound. *)

Lemma Rprod_norm_scale_unit_zero : forall c a b,
  a^2 + b^2 = 1 -> Rprod_norm (c * a, 0) <= Rabs c.
Proof.
intros c a b Hab.
unfold Rprod_norm. cbn [fst snd].
destruct (Rle_lt_dec 0 c) as [Hc | Hc].
- rewrite Rabs_right by lra.
  apply Rle_trans with (sqrt (c^2)).
  + apply sqrt_le_1; nra.
  + rewrite sqrt_pow2; lra.
- rewrite Rabs_left by lra.
  apply Rle_trans with (sqrt ((-c)^2)).
  + apply sqrt_le_1; nra.
  + rewrite sqrt_pow2; lra.
Qed.

(** ** Step 10 — Convert the L2 bound on M_iter to a Rprod_norm
       bound on iternR vs (-sin, cos). *)

Lemma iternR_truncation_bound : forall n h, 0 < h^2 < 4 ->
  Rprod_norm
    (fst (iternR (0, 1) h n) - - sin (INR n * h),
     snd (iternR (0, 1) h n) - cos (INR n * h)) <=
  INR n * Rprod_norm (c_h h - cos h, s_h h - sin h) +
  (1 - sqrt (1 - h^2/4)).
Proof.
intros n h Hh.
rewrite (iternR_as_M_iter n h Hh).
cbn [fst snd].
set (sq := sqrt (1 - h^2/4)).
assert (Hsq_pos: 0 <= sq) by (subst sq; apply sqrt_pos).
assert (Hsq_le_1: sq <= 1).
{ subst sq. rewrite <- sqrt_1 at 2. apply sqrt_le_1; lra. }
pose proof (M_iter_unit n h ltac:(lra)) as Hunit.
remember (fst (M_iter h n)) as a eqn:Heqa.
remember (snd (M_iter h n)) as b eqn:Heqb.
remember (sin (INR n * h)) as sa eqn:Heqsa.
remember (cos (INR n * h)) as cb eqn:Heqcb.
(* Decompose (- sq * a - (- sa), b - cb) = (sa - a, b - cb) + ((1 - sq) * a, 0) *)
replace (- sq * a - - sa) with ((sa - a) + (1 - sq) * a) by ring.
replace (b - cb) with ((b - cb) + 0) at 1 by ring.
eapply Rle_trans.
- pose proof (Rprod_triang_ineq (sa - a, b - cb) ((1 - sq) * a, 0)) as Htri.
  unfold Rprod_plus in Htri. cbn [fst snd] in Htri.
  exact Htri.
- apply Rplus_le_compat.
  + (* L2 norm of (sa - a, b - cb) = L2 norm of (a - sa, b - cb), then apply Step 9 *)
    replace (Rprod_norm (sa - a, b - cb))
       with (Rprod_norm (a - sa, b - cb))
       by (unfold Rprod_norm; simpl; f_equal; nra).
    subst a b sa cb.
    apply (error_grows_linearly_in_n n h Hh).
  + (* Rprod_norm ((1 - sq) * a, 0) <= 1 - sq *)
    eapply Rle_trans.
    * apply (Rprod_norm_scale_unit_zero (1 - sq) a b Hunit).
    * rewrite Rabs_right; lra.
Qed.

(** ** Step 14 — Drive vector norm bound at h = 1/32.

    [Rprod_norm (c_h(1/32) − cos(1/32), s_h(1/32) − sin(1/32)) ≤ 13·10⁻⁷].
    All sub-bounds discharge via [interval] (no [acos]). *)

Lemma drive_norm_bound :
  Rprod_norm (c_h (1/32) - cos (1/32), s_h (1/32) - sin (1/32)) <= 13 / 10^7.
Proof.
unfold Rprod_norm. cbn [fst snd].
apply Rle_trans with (sqrt ((13 / 10^7) ^ 2)).
- apply sqrt_le_1.
  + pose proof (Rle_0_sqr (c_h (1/32) - cos (1/32))).
    pose proof (Rle_0_sqr (s_h (1/32) - sin (1/32))).
    unfold Rsqr in *. nra.
  + nra.
  + unfold c_h, s_h. interval with (i_prec 80).
- rewrite sqrt_pow2; nra.
Qed.

(** ** Step 15 — Concrete corollary: the BEA state-error bound
       against (−sin, cos) at h = 1/32 and any n ≤ 1000.

    The bound [iternR_truncation_bound] is in terms of [iternR] vs
    [(−sin, cos)] directly; the standard SHO solution from initial
    conditions [(p, q) = (0, 1)] is exactly [(−sin t, cos t)] by
    standard theory (Picard–Lindelöf uniqueness applied to the linear
    SHO ODE; formalizing this uniqueness in Coq via [smooth_fun]
    closure under subtraction is left as future work). *)

Lemma sqrt_factor_bound :
  1 - sqrt (1 - (1/32) ^ 2 / 4) <= 1 / 4096.
Proof.
interval with (i_prec 80).
Qed.

Theorem BEA_iternR_truncation_bound_1000 : forall n,
  (n <= 1000)%nat ->
  Rprod_norm
    (fst (iternR (0, 1) (1/32) n) - - sin (INR n * (1/32)),
     snd (iternR (0, 1) (1/32) n) - cos (INR n * (1/32))) <= 2 / 1000.
Proof.
intros n Hn.
eapply Rle_trans.
- apply (iternR_truncation_bound n (1/32)). nra.
- pose proof drive_norm_bound as Hdb.
  pose proof sqrt_factor_bound as Hsf.
  pose proof (pos_INR n) as HnPos.
  apply le_INR in Hn.
  assert (HINR: INR 1000 = 1000) by (simpl; lra).
  rewrite HINR in Hn.
  apply Rle_trans with (1000 * (13 / 10^7) + 1 / 4096).
  + apply Rplus_le_compat; [|exact Hsf].
    apply Rle_trans with
      (1000 * Rprod_norm (c_h (1/32) - cos (1/32), s_h (1/32) - sin (1/32))).
    * apply Rmult_le_compat_r.
      -- unfold Rprod_norm. apply sqrt_pos.
      -- exact Hn.
    * apply Rmult_le_compat_l; [lra | exact Hdb].
  + lra.
Qed.

(** ** Step 11 — Smoothness and SHO closure under subtraction. *)

Lemma Derive_n_minus_pointwise : forall n f g x,
  smooth_fun f -> smooth_fun g ->
  Derive_n (fun t => f t - g t) n x = Derive_n f n x - Derive_n g n x.
Proof.
induction n; intros f g x Hf Hg.
- simpl. reflexivity.
- simpl.
  rewrite (Derive_ext _ (fun y => Derive_n f n y - Derive_n g n y)).
  + apply Derive_minus.
    * specialize (Hf x (S n)). simpl in Hf. exact Hf.
    * specialize (Hg x (S n)). simpl in Hg. exact Hg.
  + intros y. apply IHn; auto.
Qed.

Lemma smooth_fun_minus : forall f g,
  smooth_fun f -> smooth_fun g -> smooth_fun (fun t => f t - g t).
Proof.
intros f g Hf Hg x n.
revert x.
induction n; intros x.
- exact I.
- simpl.
  apply (ex_derive_ext (fun y => Derive_n f n y - Derive_n g n y)).
  + intros y. symmetry. apply Derive_n_minus_pointwise; auto.
  + apply (@ex_derive_minus R_AbsRing R_NormedModule).
    * specialize (Hf x (S n)). simpl in Hf. exact Hf.
    * specialize (Hg x (S n)). simpl in Hg. exact Hg.
Qed.

Lemma Harmonic_oscillator_system_minus :
  forall p1 q1 p2 q2 : R -> R,
  Harmonic_oscillator_system 1 p1 q1 ->
  Harmonic_oscillator_system 1 p2 q2 ->
  Harmonic_oscillator_system 1 (fun t => p1 t - p2 t) (fun t => q1 t - q2 t).
Proof.
intros p1 q1 p2 q2 H1 H2.
destruct H1 as (Hp1s & Hq1s & H1ode).
destruct H2 as (Hp2s & Hq2s & H2ode).
unfold Harmonic_oscillator_system.
split; [|split].
- apply smooth_fun_minus; auto.
- apply smooth_fun_minus; auto.
- intros t.
  destruct (H1ode t) as [Hq1d Hp1d].
  destruct (H2ode t) as [Hq2d Hp2d].
  split.
  + rewrite Derive_n_minus_pointwise; auto.
    rewrite Hq1d, Hq2d. reflexivity.
  + rewrite Derive_n_minus_pointwise; auto.
    rewrite Hp1d, Hp2d.
    unfold dUdq. ring.
Qed.

(** ** Step 12 — (−sin, cos) satisfies SHO at ω = 1.

    [smooth_fun_sin] and [smooth_fun_cos] are standard facts (sin and cos
    are C∞). Coquelicot doesn't provide them as one-line lemmas — they
    require an n-mod-4 case analysis showing [Derive_n sin n] is in
    [{sin, cos, -sin, -cos}]. Admitted here for brevity; the proof is
    purely mechanical case-splitting using [is_derive_sin],
    [is_derive_cos], [is_derive_opp]. *)

(** [Derive_n sin n] is pointwise equal to one of [sin], [cos], [-sin], [-cos]. *)
Lemma Derive_n_sin_form : forall n,
  (forall x, Derive_n sin n x = sin x) \/
  (forall x, Derive_n sin n x = cos x) \/
  (forall x, Derive_n sin n x = - sin x) \/
  (forall x, Derive_n sin n x = - cos x).
Proof.
induction n.
- left. intros. reflexivity.
- destruct IHn as [H | [H | [H | H]]].
  + right. left. intros x. simpl.
    transitivity (Derive sin x); [apply Derive_ext; exact H |].
    apply is_derive_unique. apply is_derive_sin.
  + right. right. left. intros x. simpl.
    transitivity (Derive cos x); [apply Derive_ext; exact H |].
    apply is_derive_unique. apply is_derive_cos.
  + right. right. right. intros x. simpl.
    transitivity (Derive (fun y => - sin y) x); [apply Derive_ext; exact H |].
    rewrite Derive_opp.
    rewrite (is_derive_unique sin x (cos x)) by apply is_derive_sin.
    reflexivity.
  + left. intros x. simpl.
    transitivity (Derive (fun y => - cos y) x); [apply Derive_ext; exact H |].
    rewrite Derive_opp.
    rewrite (is_derive_unique cos x (- sin x)) by apply is_derive_cos.
    ring.
Qed.

Lemma smooth_fun_sin : smooth_fun sin.
Proof.
intros x n.
revert x.
induction n; intros x.
- exact I.
- simpl.
  destruct (Derive_n_sin_form n) as [H | [H | [H | H]]].
  + apply (ex_derive_ext sin). { intros y. symmetry. exact (H y). }
    eexists. apply is_derive_sin.
  + apply (ex_derive_ext cos). { intros y. symmetry. exact (H y). }
    eexists. apply is_derive_cos.
  + apply (ex_derive_ext (fun y => - sin y)).
    { intros y. symmetry. exact (H y). }
    apply (@ex_derive_opp R_AbsRing R_NormedModule).
    eexists. apply is_derive_sin.
  + apply (ex_derive_ext (fun y => - cos y)).
    { intros y. symmetry. exact (H y). }
    apply (@ex_derive_opp R_AbsRing R_NormedModule).
    eexists. apply is_derive_cos.
Qed.

(** [Derive_n cos n] is pointwise one of [cos], [-sin], [-cos], [sin].
    Same idea as for sin, just shifted by one in the cycle. *)
Lemma Derive_n_cos_form : forall n,
  (forall x, Derive_n cos n x = cos x) \/
  (forall x, Derive_n cos n x = - sin x) \/
  (forall x, Derive_n cos n x = - cos x) \/
  (forall x, Derive_n cos n x = sin x).
Proof.
induction n.
- left. intros. reflexivity.
- destruct IHn as [H | [H | [H | H]]].
  + right. left. intros x. simpl.
    transitivity (Derive cos x); [apply Derive_ext; exact H |].
    apply is_derive_unique. apply is_derive_cos.
  + right. right. left. intros x. simpl.
    transitivity (Derive (fun y => - sin y) x); [apply Derive_ext; exact H |].
    rewrite Derive_opp.
    rewrite (is_derive_unique sin x (cos x)) by apply is_derive_sin.
    reflexivity.
  + right. right. right. intros x. simpl.
    transitivity (Derive (fun y => - cos y) x); [apply Derive_ext; exact H |].
    rewrite Derive_opp.
    rewrite (is_derive_unique cos x (- sin x)) by apply is_derive_cos.
    ring.
  + left. intros x. simpl.
    transitivity (Derive sin x); [apply Derive_ext; exact H |].
    apply is_derive_unique. apply is_derive_sin.
Qed.

Lemma smooth_fun_cos : smooth_fun cos.
Proof.
intros x n.
revert x.
induction n; intros x.
- exact I.
- simpl.
  destruct (Derive_n_cos_form n) as [H | [H | [H | H]]].
  + apply (ex_derive_ext cos). { intros y. symmetry. exact (H y). }
    eexists. apply is_derive_cos.
  + apply (ex_derive_ext (fun y => - sin y)).
    { intros y. symmetry. exact (H y). }
    apply (@ex_derive_opp R_AbsRing R_NormedModule).
    eexists. apply is_derive_sin.
  + apply (ex_derive_ext (fun y => - cos y)).
    { intros y. symmetry. exact (H y). }
    apply (@ex_derive_opp R_AbsRing R_NormedModule).
    eexists. apply is_derive_cos.
  + apply (ex_derive_ext sin). { intros y. symmetry. exact (H y). }
    eexists. apply is_derive_sin.
Qed.

Lemma smooth_fun_opp : forall f,
  smooth_fun f -> smooth_fun (fun t => - f t).
Proof.
intros f Hf x n.
revert x.
induction n; intros x.
- exact I.
- simpl.
  apply (ex_derive_ext (fun y => - Derive_n f n y)).
  + intros y. symmetry.
    apply (Derive_n_opp).
  + apply (@ex_derive_opp R_AbsRing R_NormedModule).
    specialize (Hf x (S n)). simpl in Hf. exact Hf.
Qed.

Lemma p_sol_q_sol_satisfy_SHO :
  Harmonic_oscillator_system 1 (fun t => - sin t) cos.
Proof.
unfold Harmonic_oscillator_system, dUdq.
split; [|split].
- apply smooth_fun_opp. exact smooth_fun_sin.
- exact smooth_fun_cos.
- intros t. split.
  + (* Derive_n cos 1 t = - sin t *)
    replace (Derive_n cos 1 t) with (Derive cos t) by reflexivity.
    apply is_derive_unique. apply is_derive_cos.
  + (* Derive_n (-sin) 1 t = - (1^2 * cos t) = - cos t *)
    replace (Derive_n (fun t => - sin t) 1 t) with (Derive (fun t => - sin t) t) by reflexivity.
    rewrite Derive_opp.
    rewrite (is_derive_unique sin t (cos t)) by apply is_derive_sin.
    ring.
Qed.

(** ** Step 13 — SHO uniqueness from IC (0, 1).

    For any [(pt, qt)] satisfying SHO with [pt 0 = 0], [qt 0 = 1], we have
    [pt t = -sin t] and [qt t = cos t]. Proof via energy conservation of
    the difference. *)

Lemma SHO_unique_from_init :
  forall pt qt : R -> R,
  pt 0 = 0 -> qt 0 = 1 ->
  Harmonic_oscillator_system 1 pt qt ->
  forall t, pt t = - sin t /\ qt t = cos t.
Proof.
intros pt qt Hp0 Hq0 HSHO t.
pose proof p_sol_q_sol_satisfy_SHO as Hsol.
pose proof (Harmonic_oscillator_system_minus pt qt _ _ HSHO Hsol) as Hdiff.
pose proof (system_implies_cons_e' _ _ 1 0 t Rlt_0_1 Hdiff) as Hcons.
unfold Rprod_norm in Hcons. simpl in Hcons.
rewrite Hp0, Hq0, sin_0, cos_0 in Hcons.
(* Simplify the RHS of Hcons: it's sqrt of an expression that's 0 *)
match type of Hcons with
| _ = sqrt ?Y => assert (HY: Y = 0) by ring; rewrite HY, sqrt_0 in Hcons
end.
(* Hcons : sqrt ((pt t - - sin t)^2 + (1 * (qt t - cos t))^2) = 0 *)
(* Both squares are non-negative; their sqrt is zero iff their sum is zero *)
pose proof (Rle_0_sqr (pt t - - sin t)) as H1.
pose proof (Rle_0_sqr (1 * (qt t - cos t))) as H2.
unfold Rsqr in H1, H2.
assert (Hsum_pos: 0 <= (pt t - - sin t) ^ 2 + (1 * (qt t - cos t)) ^ 2) by nra.
pose proof (sqrt_eq_0 _ Hsum_pos Hcons) as Hsum.
(* Hsum : (pt t - - sin t) ^ 2 + (1 * (qt t - cos t)) ^ 2 = 0 *)
split; nra.
Qed.

(** ** Abstract-form BEA truncation bound — parameterized over (pt, qt). *)

Theorem BEA_truncation_bound :
  forall pt qt : R -> R,
  forall n : nat, (n <= 1000)%nat ->
  pt 0 = 0 -> qt 0 = 1 ->
  Harmonic_oscillator_system 1 pt qt ->
  Rprod_norm
    (pt (INR n * (1/32)) - fst (iternR (0, 1) (1/32) n),
     qt (INR n * (1/32)) - snd (iternR (0, 1) (1/32) n)) <= 2 / 1000.
Proof.
intros pt qt n Hn Hp0 Hq0 HSHO.
pose proof (SHO_unique_from_init pt qt Hp0 Hq0 HSHO (INR n * (1/32))) as [Hpt Hqt].
rewrite Hpt, Hqt.
(* Reconcile sign convention: goal has (-sin - fst, cos - snd); BEA bound has
   (fst - -sin, snd - cos). Both have the same Rprod_norm since
   sqrt(x² + y²) is invariant under componentwise sign flip. *)
replace (Rprod_norm
    (- sin (INR n * (1/32)) - fst (iternR (0, 1) (1/32) n),
     cos (INR n * (1/32)) - snd (iternR (0, 1) (1/32) n)))
   with (Rprod_norm
    (fst (iternR (0, 1) (1/32) n) - - sin (INR n * (1/32)),
     snd (iternR (0, 1) (1/32) n) - cos (INR n * (1/32)))).
- apply (BEA_iternR_truncation_bound_1000 n Hn).
- unfold Rprod_norm. simpl. f_equal. nra.
Qed.
