(** matrix_analysis.v: stability analysis for leapfrog integration
  of a simple harmonic oscillator.
 Copyright (C) 2021-2022  Ariel Eileen Kellison.
*)

From Coq Require Import ZArith Reals Psatz.
From Coq Require Import Arith.Arith.
Require Import real_lemmas lf_harm_real matrix_lemmas lf_harm_real_theorems.


From Coquelicot Require Import Coquelicot.
Require Import Interval.Tactic.

Import Bool.

Set Bullet Behavior "Strict Subproofs". 

Require Import Coq.Logic.FunctionalExtensionality.

Definition vec_coeff_mult (a : C) (n:nat) (V: @matrix C n 1%nat) : @matrix C n 1%nat :=
  @mk_matrix C n 1%nat (fun i _ => 
      Cmult a (@coeff_mat C n 1%nat Hierarchy.zero V i 0)).

Definition vec_two_norm (u : @matrix C 2 1%nat) : R := 
  Rprod_norm (Cmod (@coeff_mat C 2 1%nat Hierarchy.zero u 0 0), Cmod (@coeff_mat C 2 1%nat Hierarchy.zero u 1 0)). 


(* the maximum eigenvalue x of the matrix ATA, given A and the eigenvector v corresponding to x *)
(* the two norm is the sqrt of the modulus of the first projection *)
Definition matrix_two_norm_sig (A : @matrix C 2 2) (v : @matrix C 2 1%nat) := 
  { x : C | let ATA := Mmult (matrix_conj_transpose 2 A) A in
            (Mmult ATA v = vec_coeff_mult x 2 v ) /\ (* x/v is an eigenvalue/eigenvector of ATA *)
            (forall i, (i < 2)%nat /\ (@coeff_mat C 2 1%nat Hierarchy.zero v i 0 <> 0 )) (* eigenvalue is non-zero*) /\ 
            (forall (u : @matrix C 2 1%nat), vec_two_norm (Mmult A u) <= sqrt (Cmod x) * vec_two_norm u) /\ (* x is max *)
            (0 < (Cmod x)) (* x is positive (iff ATA is non-singular)*)}.

Lemma matrix_two_norm_sig_positive (A : @matrix C 2 2) (v : @matrix C 2 1%nat) :
    forall (l : matrix_two_norm_sig  A v),
    0 <= sqrt ( Cmod (proj1_sig l)) .
Proof.
intros.
apply sqrt_pos.
Qed.

Lemma eq_V0_iff (n: nat) (V : @matrix C n 1%nat) :
  V = V0 n <-> forall i, (i < n)%nat -> (@coeff_mat C_Ring n 1%nat zero V i 0) = zero.
Proof.
split; intros.
- 
subst. unfold V0, Mzero.
apply coeff_mat_bij; try lia; auto.
- 
destruct n.
+ 
destruct V; auto.
+
unfold V0, Mzero.
pose proof @mk_matrix_bij C_Ring (S n) 1 zero V as Hm.
rewrite <- Hm.
apply mk_matrix_ext => i j Hi Hj.
assert (j=0%nat) by lia.
subst.
apply H; auto.
Qed.

Lemma two_norm_zero_lem (A : @matrix C 2 2)  : 
  A = M0 2 -> 
  forall u : matrix 2 1, (vec_two_norm (Mmult A u) = 0).
Proof.
intros.
assert ((Mmult A u) = V0 2).
- 
apply mk_matrix_ext => i j Hi Hj.
unfold sum_n; simpl. 
rewrite sum_n_Sm; try lia.
rewrite sum_n_n.
assert (A = M0 2) by auto.
assert ((i < 2)%nat /\ (0 < 2)%nat) by lia.
pose proof eq_M0_iff.
eapply eq_M0_iff in H; try apply H1.
assert ((i < 2)%nat /\ (1 < 2)%nat) by lia.
eapply eq_M0_iff in H0; try apply H3.
cbv [plus mult]; simpl.
cbv [Cplus Cmult]; simpl.
assert (@coeff_mat C 2 2 (@zero C_Ring) A i 1 = @zero C_Ring) by auto.
assert (@coeff_mat C 2 2 (@zero C_Ring) A i 0 = @zero C_Ring) by auto.
rewrite H4.
rewrite H5.
simpl; repeat rewrite Rmult_0_l.
repeat rewrite Rminus_0_r.
repeat rewrite Rplus_0_l.
auto.
- 
rewrite H0.
unfold vec_two_norm.
unfold V0, Rprod_norm, fst, snd, Cmod, C0. 
rewrite coeff_mat_bij; try lia.
rewrite coeff_mat_bij; try lia.
unfold fst, snd.
repeat rewrite pow_i; try lia.
rewrite Rplus_0_l.
rewrite sqrt_0.
repeat rewrite pow_i; try lia.
rewrite Rplus_0_l.
rewrite sqrt_0; auto.
Qed.



Lemma two_norm_M0 (v : @matrix C 2 1%nat) :
    forall (l : matrix_two_norm_sig (M0 2) v),
    0 =  sqrt (Cmod (proj1_sig l)).
Proof.
intros.
destruct l; simpl in a; simpl.
Admitted.

Lemma matrix_two_norm_sig_definite (A : @matrix C 2 2) (v : @matrix C 2 1%nat) :
    forall (l : matrix_two_norm_sig  A v),
    0 = sqrt ( Cmod (proj1_sig l)) <-> A = M0 2.
Proof.
intros; split.
- 
destruct l as (lam_max & H1 & H2 & H3 & H4); simpl.
intros.
symmetry in H.
apply sqrt_eq_0 in H; try apply Cmod_ge_0.
rewrite H in H4.
pose proof Rlt_irrefl 0; contradiction.
-
intros.
subst.
pose proof two_norm_M0 v l.
auto.
Qed.


(* the approximate transition matrix *)
Definition t_matrix (h: R) : @matrix C 2 2 := 
  let a := 0.5 * h^2 in 
  mk_matrix 2 2 (fun i j => if (Nat.eqb i j) then ((1 - a) , 0) else 
    if ( Nat.ltb j i)%nat then (h,0) else ((-0.5 * h * (2 - a)),0)) .

(* ideal solution vector *)
Definition pq_vector (h: R) (p q : R -> R) (t : R) : @matrix C 2 1 := 
  mk_matrix 2 1 (fun i j => if (Nat.eqb i j) then (p t , 0) else (q t , 0)) .

(* an arbitrary solution vector *)
Definition s_vector (ic: R * R) := @mk_matrix C 2 1%nat
  (fun i j => if (Nat.eqb i j) then ((fst ic),0) else ((snd ic),0)).

(* the first component of the vector result of multiplication 
of the transition matrix by an arbitrary vector is equal to the 
first component of a leapfrog update. *)
Lemma transition_matrix_equiv_1:
  forall (ic : R * R) (h : R),  
  let Mx := Mmult (t_matrix h) (s_vector ic) in
   coeff_mat Hierarchy.zero Mx 0 0 = (fst (leapfrog_stepR ic h),0).
Proof.
intros. subst Mx. destruct ic. cbv. 
all : (f_equal; field_simplify; nra) .
Qed.

(* the second component of the vector result of multiplication 
of the transition matrix by an arbitrary vector is equal to the 
second component of a leapfrog update. *)
Lemma transition_matrix_equiv_2:
  forall (ic : R * R) (h : R), 
  let Mx := Mmult (t_matrix h) (s_vector ic) in
coeff_mat Hierarchy.zero Mx 1 0 = (snd (leapfrog_stepR ic h),0).
Proof.
intros. subst Mx. destruct ic. cbv.
all : (f_equal; field_simplify; nra) .
Qed.


Definition lambda_1 (h : R) : C := (1 -0.5 * h^2 , -h * sqrt(2 - h) * 0.5 * sqrt(h + 2)). 
Definition lambda_2 (h : R) : C := (1 -0.5 * h^2 ,  h * sqrt(2 - h) * 0.5 * sqrt(h + 2)).

Definition eigenvalue_vector (h : R) : @matrix C 2 1 :=
mk_matrix 2 1 ( fun i j => if ((Nat.eqb i j)) then lambda_1 h else lambda_2 h).

Definition eigenvalue_matrix (h : R) : @matrix C 2 2 :=
   mk_matrix 2 2 ( fun i j => if ((Nat.eqb i 0) && (Nat.eqb j 0) ) then lambda_1 h else
    if ( (Nat.eqb i 1) && (Nat.eqb j 1) ) then lambda_2 h else 0).


Definition eV_1 (h: R) : C * C := ((0 , -0.5 * sqrt(4 - h^2)) , C1).
Definition eV_2 (h: R) : C * C := ((0 ,  0.5 * sqrt(4 - h^2)) , C1).
Definition eigenvector_matrix (h : R) : @matrix C 2 2 :=
   mk_matrix 2 2 ( fun i j => if ( (Nat.eqb i 0) && (Nat.eqb j 0)) then fst (eV_1 h) else
    if ( (Nat.eqb i 0) && (Nat.eqb j 1)) then fst (eV_2 h) else 1).




(* M * V = V * L *)
Lemma eigens_correct (h : R) :
  0 <= h <= 2 -> 
  Mmult (t_matrix h) (eigenvector_matrix h) = 
  Mmult (eigenvector_matrix h) (eigenvalue_matrix h).
Proof.
intros.
apply mk_matrix_ext => i j Hi Hj.
replace (Init.Nat.pred 2) with (S 0) by lia.
repeat rewrite sum_Sn.
repeat rewrite sum_O.
unfold t_matrix, eigenvector_matrix, eigenvalue_matrix, 
  eV_1, eV_2, lambda_1, lambda_2, matrix_lemmas.C1.
repeat rewrite coeff_mat_bij.
all: try lia.
assert (A: i = 0%nat \/ i = 1%nat) by lia;
destruct A. 
-
assert (B: j = 0%nat \/ j = 1%nat) by lia;
destruct B. 
+
subst.
simpl.
cbv [mult Cmult]; simpl.
rewrite ?mult_aux1.
rewrite ?mult_aux2. 
rewrite ?mult_aux3.
cbv [mult Cmult]; simpl. repeat rewrite Rmult_0_r; unfold C0.
cbv [plus Cplus]; simpl. repeat rewrite Rplus_0_r.
repeat rewrite Rmult_1_r. repeat rewrite Rplus_0_r.
repeat rewrite Rminus_0_r.
cbv [plus Cplus]; simpl. repeat rewrite Rplus_0_r.
repeat rewrite Rplus_0_l.
repeat rewrite Rminus_0_l.
repeat rewrite Rmult_0_l.
f_equal; try nra.
replace
(- h * sqrt (2 - h) * 0.5 * sqrt (h + 2))
with 
(- 0.5 * h * sqrt (2 - h) * sqrt (h + 2)) by nra.
rewrite Rmult_assoc.
rewrite Rmult_assoc.
rewrite Rmult_assoc.
rewrite <- sqrt_mult; try nra.
replace (- (-0.5 * sqrt (4 - h * h)) *
(-0.5 * (h * sqrt ((2 - h) * (h + 2))))) with
(- (-0.5 * -0.5 * h * sqrt (4 - h * h) * sqrt ((2 - h) * (h + 2))))
by nra.
rewrite Rmult_assoc.
rewrite Rmult_assoc.
rewrite <- sqrt_mult; try nra.
replace ((2 - h) * (h + 2)) with ((4 - h * h)) by nra.
rewrite sqrt_square; try nra.
+
subst.
simpl.
cbv [mult Cmult]; simpl.
rewrite ?mult_aux1.
rewrite ?mult_aux2. 
rewrite ?mult_aux3.
cbv [mult Cmult]; simpl. repeat rewrite Rmult_0_r; unfold C0.
cbv [plus Cplus]; simpl. repeat rewrite Rplus_0_r.
repeat rewrite Rmult_1_r. repeat rewrite Rplus_0_r.
repeat rewrite Rminus_0_r.
cbv [plus Cplus]; simpl. repeat rewrite Rplus_0_r.
repeat rewrite Rplus_0_l.
f_equal; try nra.
replace 
(h * sqrt (2 - h) * 0.5 * sqrt (h + 2))
with 
(0.5 * h * sqrt (2 - h) * sqrt (h + 2)) by nra.
rewrite Rmult_assoc.
rewrite Rmult_assoc.
rewrite Rmult_assoc.
rewrite <- sqrt_mult; try nra.
symmetry.
rewrite <- Rmult_assoc.
repeat rewrite Rmult_0_l.
repeat rewrite Rminus_0_l.
replace (- (0.5 * sqrt (4 - h * h)) * 0.5 * (h * sqrt ((2 - h) * (h + 2))))
with
(- (0.5^2 * h * (sqrt (4 - h * h) * sqrt ((2 - h) * (h + 2))))) by nra.
rewrite <- sqrt_mult; try nra.
replace ((2 - h) * (h + 2)) with ((4 - h * h)) by nra.
rewrite sqrt_square; try nra.
-
assert (B: j = 0%nat \/ j = 1%nat) by lia;
destruct B. 
+
subst.
simpl.
cbv [mult Cmult]; simpl.
rewrite ?mult_aux1.
rewrite ?mult_aux2. 
rewrite ?mult_aux3.
cbv [mult Cmult]; simpl. repeat rewrite Rmult_0_r; unfold C0.
cbv [plus Cplus]; simpl. repeat rewrite Rplus_0_r.
repeat rewrite Rmult_1_r. repeat rewrite Rplus_0_r.
repeat rewrite Rminus_0_r. repeat rewrite Rmult_1_l.
cbv [plus Cplus]; simpl. repeat rewrite Rplus_0_r.
repeat rewrite Rplus_0_l. repeat rewrite Rmult_0_l.
repeat rewrite Rminus_0_r. repeat rewrite Rplus_0_r.
f_equal; try nra.
replace 
(-h * sqrt (2 - h) * 0.5 * sqrt (h + 2))
with 
(-0.5 * h * sqrt (2 - h) * sqrt (h + 2)) by nra.
rewrite Rmult_assoc.
rewrite Rmult_assoc.
rewrite <- sqrt_mult; try nra.
replace ((2 - h) * (h + 2)) with ((4 - h * h)) by nra.
nra.
+
subst.
simpl.
cbv [mult Cmult]; simpl.
rewrite ?mult_aux1.
rewrite ?mult_aux2. 
rewrite ?mult_aux3.
cbv [mult Cmult]; simpl. repeat rewrite Rmult_0_r; unfold C0.
cbv [plus Cplus]; simpl. repeat rewrite Rplus_0_r.
repeat rewrite Rmult_1_r. repeat rewrite Rplus_0_r.
repeat rewrite Rminus_0_r. repeat rewrite Rmult_1_l.
cbv [plus Cplus]; simpl. repeat rewrite Rplus_0_r.
repeat rewrite Rplus_0_l. repeat rewrite Rmult_0_l.
repeat rewrite Rminus_0_r. repeat rewrite Rplus_0_r.
f_equal; try nra.
replace 
(h * sqrt (2 - h) * 0.5 * sqrt (h + 2))
with 
(0.5 * h * sqrt (2 - h) * sqrt (h + 2)) by nra.
rewrite Rmult_assoc.
rewrite Rmult_assoc.
rewrite <- sqrt_mult; try nra.
replace ((2 - h) * (h + 2)) with ((4 - h * h)) by nra.
nra.
Qed.

(* in order to prove that two norm of M is - 
  you need to prove 
1. a closed form of MTM
2. that V & L are eigenvectors and values of MTM!
3. the largest value of L
*)

Definition MTM (h : R) : @matrix C 2 2 :=
   mk_matrix 2 2 ( fun i j => if ( (Nat.eqb i 0) && (Nat.eqb j 0)) then (0.25 * h^4 + 1, 0) else
    if ( negb (Nat.eqb i j) ) then (0.125 * h^3*(2 - h^2),0) else 
    (0.0625 * h^6 - 0.25*h^4 + 1, 0)).

(*
Matrix([[(h**3 - 8*h + sqrt(h**6 + 64))/(4*(h**2 - 2)), (h**3 - 8*h - sqrt(h**6 + 64))/(4*(h**2 - 2))], [1, 1]])
Matrix([[h**6/32 - h**3*sqrt(h**2 + 4)*sqrt(h**4 - 4*h**2 + 16)/32 + 1, 0], [0, h**6/32 + h**3*sqrt(h**2 + 4)*sqrt(h**4 - 4*h**2 + 16)/32 + 1]])

Matrix([[-sqrt(h**2 - 4)/2, sqrt(h**2 - 4)/2], [1, 1]])
Matrix([[-h**2/2 - h*sqrt(h - 2)*sqrt(h + 2)/2 + 1, 0], [0, -h**2/2 + h*sqrt(h - 2)*sqrt(h + 2)/2 + 1]])
*)


Definition MTM_lambda_1 (h : R) : C := (1 + 0.03125 * h ^ 6 - 0.03125 * h^3 * sqrt(h^2 + 4) * sqrt(h^4 - 4 * h^2 + 16), 0) .
Definition MTM_lambda_2 (h : R) : C := (1 + 0.03125 * h ^ 6 + 0.03125 * h^3 * sqrt(h^2 + 4) * sqrt(h^4 - 4 * h^2 + 16), 0) .

Definition MTM_eigenvalue_vector (h : R) : @matrix C 2 1 :=
mk_matrix 2 1 ( fun i j => if ((Nat.eqb i j)) then MTM_lambda_1 h else MTM_lambda_2 h).

Definition MTM_eigenvalue_matrix (h : R) : @matrix C 2 2 :=
   mk_matrix 2 2 ( fun i j => if ((Nat.eqb i 0) && (Nat.eqb j 0) ) then MTM_lambda_1 h else
    if ( (Nat.eqb i 1) && (Nat.eqb j 1) ) then MTM_lambda_2 h else 0).

Definition MTM_eV_1 (h: R) : C * C := ((0.25 * (h^3 - 8*h + sqrt(h^6 + 64))/(h^2 - 2) ,0) , C1).
Definition MTM_eV_2 (h: R) : C * C := ((0.25 * (h^3 - 8*h - sqrt(h^6 + 64))/(h^2 - 2) ,0) , C1).

Definition MTM_eV_1_vector (h : R) : @matrix C 2 1 :=
  mk_matrix 2 1 ( fun i j => if ((Nat.eqb i j)) then fst (MTM_eV_1 h) else snd (MTM_eV_1 h)).

Definition MTM_eV_2_vector (h : R) : @matrix C 2 1 :=
  mk_matrix 2 1 ( fun i j => if ((Nat.eqb i j)) then fst (MTM_eV_2 h) else snd (MTM_eV_2 h)).

Definition MTM_eigenvector_matrix (h : R) : @matrix C 2 2 :=
   mk_matrix 2 2 ( fun i j => if ( (Nat.eqb i 0) && (Nat.eqb j 0)) then fst (MTM_eV_1 h) else
    if ( (Nat.eqb i 0) && (Nat.eqb j 1)) then fst (MTM_eV_2 h) else 1).

  

Lemma MTM_aux  (h : R) :
  Mmult (matrix_conj_transpose _ (t_matrix h)) (t_matrix h) = MTM h.
Proof.
unfold MTM.
apply mk_matrix_ext => i j Hi Hj.
replace (Init.Nat.pred 2) with (S 0) by lia.
repeat rewrite sum_Sn.
repeat rewrite sum_O.
unfold t_matrix, matrix_conj_transpose, Cconj.
repeat rewrite coeff_mat_bij.
all: try lia.
assert (A: i = 0%nat \/ i = 1%nat) by lia;
destruct A. 
-
assert (B: j = 0%nat \/ j = 1%nat) by lia;
destruct B. 
+
subst.
simpl.
cbv [mult Cmult]; simpl.
rewrite ?mult_aux1.
rewrite ?mult_aux2. 
rewrite ?mult_aux3.
cbv [mult Cmult]; simpl. repeat rewrite Rmult_0_r; unfold C0.
cbv [plus Cplus]; simpl. repeat rewrite Rplus_0_r.
repeat rewrite Rmult_1_r. repeat rewrite Rplus_0_r.
repeat rewrite Rminus_0_r.
cbv [plus Cplus]; simpl. repeat rewrite Rplus_0_r.
repeat rewrite Rplus_0_l.
f_equal; try nra.
+
subst.
simpl.
cbv [mult Cmult]; simpl.
rewrite ?mult_aux1.
rewrite ?mult_aux2. 
rewrite ?mult_aux3.
cbv [mult Cmult]; simpl. repeat rewrite Rmult_0_r; unfold C0.
cbv [plus Cplus]; simpl. repeat rewrite Rplus_0_r.
repeat rewrite Rmult_1_r. repeat rewrite Rplus_0_r.
repeat rewrite Rminus_0_r.
cbv [plus Cplus]; simpl. repeat rewrite Rplus_0_r.
repeat rewrite Rplus_0_l.
f_equal; try nra.
-
assert (B: j = 0%nat \/ j = 1%nat) by lia;
destruct B. 
+
subst.
simpl.
cbv [mult Cmult]; simpl.
rewrite ?mult_aux1.
rewrite ?mult_aux2. 
rewrite ?mult_aux3.
cbv [mult Cmult]; simpl. repeat rewrite Rmult_0_r; unfold C0.
cbv [plus Cplus]; simpl. repeat rewrite Rplus_0_r.
repeat rewrite Rmult_1_r. repeat rewrite Rplus_0_r.
repeat rewrite Rminus_0_r. repeat rewrite Rmult_1_l.
cbv [plus Cplus]; simpl. repeat rewrite Rplus_0_r.
repeat rewrite Rplus_0_l. repeat rewrite Rmult_0_l.
repeat rewrite Rminus_0_r. repeat rewrite Rplus_0_r.
f_equal; try nra.
+
subst.
simpl.
cbv [mult Cmult]; simpl.
rewrite ?mult_aux1.
rewrite ?mult_aux2. 
rewrite ?mult_aux3.
cbv [mult Cmult]; simpl. repeat rewrite Rmult_0_r; unfold C0.
cbv [plus Cplus]; simpl. repeat rewrite Rplus_0_r.
repeat rewrite Rmult_1_r. repeat rewrite Rplus_0_r.
repeat rewrite Rminus_0_r. repeat rewrite Rmult_1_l.
cbv [plus Cplus]; simpl. repeat rewrite Rplus_0_r.
repeat rewrite Rplus_0_l. repeat rewrite Rmult_0_l.
repeat rewrite Rminus_0_r. repeat rewrite Rplus_0_r.
f_equal; try nra.
Qed.


  
(* MTM * V = V * L *)
Lemma MTM_eigens_correct (h : R) :
  0 < h  ^ 2 < 2 -> 
  Mmult (MTM h) (MTM_eigenvector_matrix h) = 
  Mmult (MTM_eigenvector_matrix h) (MTM_eigenvalue_matrix h).
Proof.
intros.
apply mk_matrix_ext => i j Hi Hj.
replace (Init.Nat.pred 2) with (S 0) by lia.
repeat rewrite sum_Sn.
repeat rewrite sum_O.
unfold MTM, MTM_eigenvector_matrix, MTM_eigenvalue_matrix, 
  MTM_eV_1, MTM_eV_2, MTM_lambda_1, MTM_lambda_2, matrix_lemmas.C1.
repeat rewrite coeff_mat_bij.
all: try lia.
assert (A: i = 0%nat \/ i = 1%nat) by lia;
destruct A. 
-
assert (B: j = 0%nat \/ j = 1%nat) by lia;
destruct B. 
+
subst.
simpl.
cbv [mult Cmult]; simpl.
rewrite ?mult_aux1.
rewrite ?mult_aux2. 
rewrite ?mult_aux3.
cbv [mult Cmult]; simpl. repeat rewrite Rmult_0_r; unfold C0.
cbv [plus Cplus]; simpl. repeat rewrite Rplus_0_r.
repeat rewrite Rmult_1_r. repeat rewrite Rplus_0_r.
repeat rewrite Rminus_0_r.
cbv [plus Cplus]; simpl. repeat rewrite Rplus_0_r.
repeat rewrite Rplus_0_l.
rewrite Rmult_assoc.
rewrite Rmult_assoc.
rewrite Rmult_assoc.
rewrite Rmult_assoc.
rewrite <- sqrt_mult; try nra.
replace (((h * h + 4) * (h * (h * (h * h)) - 4 * (h * h) + 16))) 
with ((h * (h * (h * (h * (h * h)))) + 64)) by nra.
f_equal; try nra.
field_simplify.
rewrite pow2_sqrt; try nra.
all : cbv; nra.
+
subst.
simpl.
repeat cbv [mult Cmult plus Cplus]; simpl.
rewrite ?mult_aux1.
rewrite ?mult_aux2. 
rewrite ?mult_aux3.
repeat cbv [mult Cmult plus Cplus C0]; simpl.
repeat rewrite Rmult_0_r.
repeat rewrite Rplus_0_r.
repeat rewrite Rmult_1_r. 
repeat rewrite Rplus_0_r.
repeat rewrite Rminus_0_r.
repeat rewrite Rplus_0_l.
rewrite Rmult_assoc.
rewrite Rmult_assoc.
rewrite Rmult_assoc.
rewrite Rmult_assoc.
rewrite <- sqrt_mult; try nra.
replace (((h * h + 4) * (h * (h * (h * h)) - 4 * (h * h) + 16))) 
with ((h * (h * (h * (h * (h * h)))) + 64)) by nra.
f_equal; try nra.
field_simplify. 
rewrite pow2_sqrt; try nra.
all : cbv; nra.
-
assert (B: j = 0%nat \/ j = 1%nat) by lia;
destruct B. 
+
subst.
simpl.
cbv [mult Cmult]; simpl.
rewrite ?mult_aux1.
rewrite ?mult_aux2. 
rewrite ?mult_aux3.
cbv [mult Cmult]; simpl. repeat rewrite Rmult_0_r; unfold C0.
cbv [plus Cplus]; simpl. repeat rewrite Rplus_0_r.
repeat rewrite Rmult_1_r. repeat rewrite Rplus_0_r.
repeat rewrite Rminus_0_r.
cbv [plus Cplus]; simpl. repeat rewrite Rplus_0_r.
repeat rewrite Rplus_0_l.
repeat rewrite Rmult_1_l.
repeat rewrite Rmult_0_l.
symmetry.
rewrite Rmult_assoc.
rewrite <- sqrt_mult; try nra.
replace (((h * h + 4) * (h * (h * (h * h)) - 4 * (h * h) + 16))) 
with ((h * (h * (h * (h * (h * h)))) + 64)) by nra.
f_equal; try nra.
simpl. cbv -[sqrt]. field.
all : cbv; nra. 
+
subst.
simpl.
cbv [mult Cmult]; simpl.
rewrite ?mult_aux1.
rewrite ?mult_aux2. 
rewrite ?mult_aux3.
cbv [mult Cmult]; simpl. repeat rewrite Rmult_0_r; unfold C0.
cbv [plus Cplus]; simpl. repeat rewrite Rplus_0_r.
repeat rewrite Rmult_1_r. repeat rewrite Rplus_0_r.
repeat rewrite Rminus_0_r.
cbv [plus Cplus]; simpl. repeat rewrite Rplus_0_r.
repeat rewrite Rplus_0_l.
repeat rewrite Rmult_1_l.
repeat rewrite Rmult_0_l.
symmetry.
rewrite Rmult_assoc.
rewrite <- sqrt_mult; try nra.
replace (((h * h + 4) * (h * (h * (h * h)) - 4 * (h * h) + 16))) 
with ((h * (h * (h * (h * (h * h)))) + 64)) by nra.
f_equal; try nra.
simpl. cbv -[sqrt]. field.
all : cbv; nra. 
Qed.

Corollary eigenvalues_MTM_correct_cor (h :R) :
Mmult (MTM h) (MTM_eV_2_vector h) =
     vec_coeff_mult (MTM_lambda_2 h) 2 (MTM_eV_2_vector h).
Proof.
Admitted.


Lemma eig_mod_eq_1 (h: R):
  0 <= h <= 2 -> 
  Cmod (lambda_1 h) = 1.
Proof.
unfold lambda_1, Cmod; intros.
simpl.
replace 1 with (sqrt 1) by (rewrite sqrt_1; auto).
f_equal.
field_simplify. 
(rewrite sqrt_1; auto).
field_simplify.
repeat rewrite pow2_sqrt; try nra.
Qed.

Lemma eig_MTM_mod_le (h: R):
  0 <= h <= 2 -> 
  Cmod (MTM_lambda_1 h) <= Cmod (MTM_lambda_2 h).
Proof.
unfold MTM_lambda_1, MTM_lambda_2, Cmod; intros.
simpl.
apply sqrt_le_1_alt.
field_simplify.
apply Rplus_le_compat_r.
apply Rminus_le.
field_simplify.
set (aa:= sqrt (h * (h * (h * (h * 1))) - 4 * (h * (h * 1)) + 16)).
apply Rle_minus.
match goal with |-context[?A <= ?b] =>
replace A with (4 * 0.03125 * (- 0.03125 * h ^ 9) * sqrt (h * (h * 1) + 4) * aa) by nra
end.
repeat rewrite Rmult_assoc.
apply Rmult_le_compat_l; try nra.
apply Rmult_le_compat_l; try nra.
repeat rewrite <- Rmult_assoc.
apply Rmult_le_compat_r; try nra.
unfold aa. apply sqrt_pos.
apply Rmult_le_compat_r; try nra.
apply sqrt_pos.
apply Rminus_le.
replace (-0.03125 * h ^ 9 - h ^ 3) with ( - (0.03125 * h ^ 9 + h ^ 3)) by nra.
apply Private.IT2.IT.TM.TMI.Ropp_le_0.
apply Rle_plus.
apply Rle_mult; try nra.
interval.
interval.
Qed.


Lemma eig_mod_eq_lemma (h: R):
  Cmod (lambda_1 h) = Cmod (lambda_2 h).
Proof.
unfold lambda_1, Cmod; intros.
simpl.
f_equal.
field_simplify; nra.
Qed.

Lemma sep_0_div (a b : R) :
  a <> 0 /\ b <> 0 -> a/b <> 0.
Proof.
intros.
replace (a / b) with (a * / b) by nra.
destruct H as (HA & HB).
generalize (Rinv_neq_0_compat b HB).
pose proof Req_dec (a / b) 0 as Hy; destruct Hy; try auto.
Qed.

Theorem t_matrix_two_norm_eq:
  forall (h : R),
  0 <= h * h  < 2 ->  (* this additional restriction on h is required 
  by the eigenvectors of MTM_ev_2; this restriction is noted in the literature 
  following empirical analysis of the scheme, but I haven't seen the reason behind 
  it discussed explicitly *)
  forall (l : matrix_two_norm_sig  (t_matrix h) (MTM_eV_2_vector h)),
  proj1_sig l = (MTM_lambda_2 h).
Proof.
intros.
destruct l as (lam_max & H1 & H2 & H3 & H4); simpl.
rewrite MTM_aux in H1.
rewrite eigenvalues_MTM_correct_cor in H1.
unfold vec_coeff_mult in H1.
assert (A : (0 <2)%nat) by lia.
assert (B : (0 <1)%nat) by lia.
eapply mk_matrix_ext in H1; try apply A; try apply B.
cbv [Cmult MTM_lambda_2 MTM_eV_2_vector MTM_eV_2] in H1.
rewrite coeff_mat_bij in H1; try lia.
simpl in H1.
repeat rewrite Rmult_0_r in H1.
repeat rewrite Rmult_0_l in H1.
repeat rewrite Rplus_0_l in H1.
repeat rewrite Rminus_0_r in H1.
destruct lam_max.
unfold fst, snd in H1.
apply pair_equal_spec in H1; destruct H1 as (H1A & H1B).
unfold MTM_lambda_2.
symmetry in H1B.
assert (0<= h< sqrt 2) by admit.
assert (0.25 * (h * (h * (h * 1)) - 8 * h - sqrt (h * (h * (h * (h * (h * (h * 1))))) + 64)) /
    (h * (h * 1) - 2) <> 0).
apply sep_0_div; split; try nra.
apply Rlt_not_eq.
try interval.
apply Rmult_integral in H1B.
destruct H1B as [C | D]; try contradiction.
Admitted.


Lemma two_norm_t_matrix_eq :
sqrt (Cmod (MTM_lambda_2 h)) <= 4503616807272450 / 4503599627370496
(* <= 1.000003814704542 *).
Proof.
unfold MTM_lambda_2, Cmod, fst, snd, h.
match goal with |-context [sqrt (sqrt ?a) <= ?b] =>
  field_simplify a
end.
match goal with |-context [sqrt (sqrt ?a) <= _] =>
interval_intro (sqrt (sqrt a)) upper
end.
apply H.
Qed.

Lemma t_matrix_norm_sub_mult :
  forall (h : R),
  0 <= h * h < 2 -> 
  forall (l : matrix_two_norm_sig  (t_matrix h) (MTM_eV_2_vector h)),
  forall (y : @matrix C 2 1%nat),
  vec_two_norm (Mmult (t_matrix h) y) <= sqrt (Cmod (MTM_lambda_2 h)) * vec_two_norm y.
Proof.
intros.
pose proof t_matrix_two_norm_eq h H l as Hyp; rewrite <- Hyp.
destruct l as (lam_max & H1 & H2 & H3 & H4); simpl.
apply H3.
Qed.

Lemma matrix_analysis_local_truncation_error:
  forall p q : R -> R,
  forall t0 tn: R,
  forall h : R, 
  0 < ω * h <= 4 ->  
  Harmonic_oscillator_system p q ω t0 ->  
  forall (l : matrix_two_norm_sig  (t_matrix h) (MTM_eV_2_vector h)),
  vec_two_norm (Mplus (pq_vector h p q (tn + h)) (Mopp (Mmult (t_matrix h) (s_vector (p tn, q tn))))) <= 
      h^3 * vec_two_norm (s_vector (p t0, q t0)).
Proof.
intros ? ? ? ? ? Hbnd HSY; intros.
unfold vec_two_norm.
unfold Mplus, Mopp, Mmult.
rewrite coeff_mat_bij; try lia.
rewrite coeff_mat_bij; try lia.
rewrite coeff_mat_bij; try lia.
rewrite coeff_mat_bij; try lia.
rewrite coeff_mat_bij; try lia.
rewrite coeff_mat_bij; try lia.
unfold sum_n; simpl. 
repeat rewrite sum_n_Sm; try lia.
repeat rewrite sum_n_n.
unfold t_matrix, s_vector.
rewrite coeff_mat_bij; try lia.
rewrite coeff_mat_bij; try lia.
rewrite coeff_mat_bij; try lia.
rewrite coeff_mat_bij; try lia.
rewrite coeff_mat_bij; try lia.
rewrite coeff_mat_bij; try lia.
rewrite coeff_mat_bij; try lia.
rewrite coeff_mat_bij; try lia.
simpl.
cbv [mult plus Cmult Cplus Cmod].
simpl.
simpl; repeat rewrite Rmult_0_l.
repeat rewrite Rminus_0_r.
repeat rewrite Rplus_0_l.
repeat rewrite Rmult_1_r.
repeat rewrite Rplus_0_r.
repeat rewrite Rmult_0_r.
repeat rewrite Rplus_0_r.
repeat rewrite Ropp_0.
repeat rewrite Rmult_0_r.
repeat rewrite Rplus_0_r.
unfold Rprod_norm, fst, snd.
pose proof local_truncation_error p q t0 tn h Hbnd HSY as LTE.
simpl in LTE; unfold Rprod_norm, fst ,snd in LTE.
simpl in LTE.
repeat rewrite Rmult_1_r in LTE.
repeat rewrite pow2_sqrt.
match goal with H0 : context[ sqrt ?a <= ?b] |- _=> 
set (yy:=  a)
end.
match goal with |- context[ sqrt ?a <= ?b] => 
replace ( a) with yy
end.
subst yy;  apply LTE; auto.
subst yy. field_simplify. nra.
all: try match goal with |-context [?a * ?a] =>
replace (a * a) with (a ^ 2) by (simpl;nra);
apply square_pos; try nra
end.
Qed.



Lemma matrix_analysis_method_bound_n : 
  forall p q h: R,
  forall n : nat, 
    0 < ω*h * ω*h < 2 -> 
  forall (l : matrix_two_norm_sig  (t_matrix h) (MTM_eV_2_vector h)),
  let Mn := Mpow 2 n (t_matrix h) in
  vec_two_norm  (Mmult Mn (s_vector (p, q))) <= 
      (sqrt (Cmod (MTM_lambda_2 h))) ^ n * vec_two_norm (s_vector (p,q)).
Proof.
intros.
induction n.
- 
simpl. simpl in Mn.
rewrite Rmult_1_l. 
subst Mn.
rewrite M_ID_equiv_M1.
rewrite Mmult_one_l.
apply Rle_refl.
-
unfold Mpow in Mn.
fold Mpow in Mn.
simpl in IHn.
subst Mn. 
replace (Mmult (Mmult (Mpow 2 n (t_matrix h)) (t_matrix h)) (s_vector (p, q)))
with
( Mmult (t_matrix h) (Mmult (Mpow 2 n (t_matrix h)) (s_vector (p, q)))).
destruct (Mmult (Mpow 2 n (t_matrix h)) (s_vector (p, q))).
eapply Rle_trans.
unfold ω in H;  rewrite Rmult_1_l in H; rewrite Rmult_1_r in H.
apply t_matrix_norm_sub_mult; auto; try nra.
simpl.
rewrite Rmult_assoc.
apply Rmult_le_compat_l; try apply sqrt_pos.
apply IHn.
rewrite Mmult_assoc.
rewrite Mpow_comm; auto.
Qed.

Theorem matrix_analysis_method_bound_fixed_h_n : 
  forall p q: R,
  forall n : nat, 
  forall (l : matrix_two_norm_sig  (t_matrix h) (MTM_eV_2_vector h)),
  let Mn := Mpow 2 n (t_matrix h) in
  vec_two_norm  (Mmult Mn (s_vector (p, q))) <= 
      (4503616807272450 / 4503599627370496) ^ n * vec_two_norm (s_vector (p,q)).
Proof.
intros.
assert (Hbnd: 0 < ω * h * ω * h < 2) by (unfold h; unfold ω; nra).
pose proof matrix_analysis_method_bound_n p q h n Hbnd l.
pose proof two_norm_t_matrix_eq.
simpl in H.
eapply Rle_trans.
apply H.
apply Rmult_le_compat_r.
unfold vec_two_norm. apply Rnorm_pos.
apply pow_incr; split; auto.
apply sqrt_pos.
Qed.


Close Scope R_scope. 