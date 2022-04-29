(** matrix_analysis.v: stability analysis for leapfrog integration
  of a simple harmonic oscillator.
 Copyright (C) 2021-2022  Ariel Eileen Kellison.
*)

From Coq Require Import ZArith Reals Psatz.
From Coq Require Import Bool Arith.Arith.
Require Import real_lemmas lf_harm_real matrix_lemmas lf_harm_real_theorems.


From Coquelicot Require Import Coquelicot.
Require Import Interval.Tactic.

Import Bool.

Set Bullet Behavior "Strict Subproofs". 

Require Import Coq.Logic.FunctionalExtensionality.



Definition vec_two_norm (n: nat ) (u : @matrix C n 1) : R :=
   sqrt (Cmod (@coeff_mat C 1%nat 1%nat Hierarchy.zero (Mmult (matrix_conj_transpose n 1 u) u) 0 0))
.

Definition vec_two_norm_2d (u : @matrix C 2 1) : R := 
  Rprod_norm (Cmod (@coeff_mat C 2 1%nat Hierarchy.zero u 0 0), Cmod (@coeff_mat C 2 1 Hierarchy.zero u 1 0))
.


Theorem two_norms_eq_2d (u : @matrix C 2 1%nat) :
vec_two_norm 2 u = vec_two_norm_2d u .
Proof.
unfold vec_two_norm_2d, Rprod_norm, vec_two_norm, Mmult, matrix_conj_transpose.
symmetry.
unfold fst at 1.
unfold snd at 1.
symmetry.
f_equal.
rewrite coeff_mat_bij; try lia.
etransitivity.
apply Ceq_Cmod_eq.
apply sum_Sn.
rewrite sum_O.
simpl.
repeat rewrite coeff_mat_bij; try lia.
rewrite Cmult_comm.
rewrite Cmod_Ccong.
rewrite Cmult_comm.
rewrite Cmod_Ccong.
repeat rewrite Rmult_1_r.
match goal with |-context[Cmod ?a * Cmod ?a] =>
replace (Cmod a * Cmod a) with (Cmod a ^ 2)
end.
match goal with |-context[Cmod ?a * Cmod ?a] =>
replace (Cmod a * Cmod a) with (Cmod a ^ 2)
end.
etransitivity.
unfold Cmod.
unfold RtoC.
repeat rewrite pow2_sqrt.
change plus with Cplus.
repeat match goal with |-context[sqrt (fst (?a) ^2 + snd?b ^2)] =>
replace (snd b) with 0
end.
rewrite pow_i; try lia.
rewrite Rplus_0_r.
cbv [Cplus].
unfold fst at 1.
apply sqrt_pow2.
unfold fst at 1.
unfold fst at 2.
apply Rle_plus;
apply sqr_plus_pos.
simpl; try nra.
apply sqr_plus_pos.
apply sqr_plus_pos.
unfold fst at 1.
unfold fst at 2.
fold Cmod.
etransitivity.
assert (fst (coeff_mat zero u 0 0) ^ 2 + snd (coeff_mat zero u 0 0) ^ 2 +
(fst (coeff_mat zero u 1 0) ^ 2 + snd (coeff_mat zero u 1 0) ^ 2) = 
(Cmod (coeff_mat zero u 0 0))^2  + (Cmod (coeff_mat zero u 1 0) )^2).
unfold Cmod.
repeat rewrite pow2_sqrt; try apply sqr_plus_pos; auto.
apply H; auto.
auto.
auto.
simpl.
rewrite Rmult_1_r; auto.
simpl.
rewrite Rmult_1_r; auto.
Qed.


Definition is_invertible_matrix (n: nat ) (Q : @matrix C n n) := 
  exists (Qinv : @matrix C n n),
  Mmult Qinv Q = Mone /\ 
  Mmult Q Qinv = Mone
.


(** Largest singular value of a square matrix A ∈ Mn(C) is the square root of the largest 
    eigenvalue of A'A*)
Definition max_sv_pred (n: nat ) (A : @matrix C n n) (σmax : R):=  
  let ATA := Mmult (matrix_conj_transpose n n A) A (* the Gram matrix A'A *) in
  let λmax := σmax^2 in 
  0 <= σmax /\
  exists (V Λ : @matrix C n n),
         Mmult ATA V = Mmult V Λ
      /\ is_orthogonal_matrix n V
      /\ diag_pred n Λ   
      /\ exists (i : nat | (i < n)%nat),  (@coeff_mat C n n Hierarchy.zero Λ (proj1_sig i) (proj1_sig i) ) = λmax
      /\ (forall (i : nat), (i < n)%nat ->
         (coeff_mat zero Λ i i) = RtoC (fst (coeff_mat zero Λ i i)) (* elements of Λ are real *)
         /\ 0 <= fst (coeff_mat zero Λ i i) <= λmax) (* λmax is positive and max in Λ *)
.



Definition basis_pred (n: nat ) (A : @matrix C n n) (u : @matrix C n 1%nat):= 
  let ATA := Mmult (matrix_conj_transpose n n A) A in (* the Gram matrix A'A *)
  forall (V Λ : @matrix C n n),
         Mmult ATA V = Mmult V Λ
      /\  is_orthogonal_matrix n V
      /\ diag_pred n Λ ->
  exists (a: @matrix C n 1%nat),  u = Mmult V a
.


Definition two_norm_pred (n: nat ) (A : @matrix C n n) (σ : R):=  
  forall (u : @matrix C n 1%nat), 
  vec_two_norm n (Mmult A u) <=  σ * vec_two_norm n u 
  /\ ~(exists (s : R), forall (x : matrix n 1), vec_two_norm n (Mmult A x) <= s * vec_two_norm n x < σ * vec_two_norm n x) (* sqrt σ is inf *)
.


(** Any vector can be written as the sum of the eigenvectors
  of a Hermitian matrix. We need this in order to satisfy the 
  two norm predicate. **)
Theorem vectors_in_basis (n : nat) : 
 forall (x : @matrix C n 1%nat), 
 forall (A: @matrix C n n), 
 basis_pred n A  x.
Proof.
intros.
unfold basis_pred.
intros.
destruct H as (H1 & H2 & H3).
unfold is_orthogonal_matrix in H2; destruct H2 as (H2a & H2b).
exists (Mmult (matrix_conj_transpose n n V) x). 
rewrite Mmult_assoc.
rewrite H2b.
rewrite Mmult_one_l; auto.
Qed.



(** the leapfrog transition matrix *)
Definition t_matrix (h: R) : @matrix C 2 2 := 
  let a := 0.5 * h^2 in 
  mk_matrix 2 2 (fun i j => if (Nat.eqb i j) then ((1 - a) , 0) else 
    if ( Nat.ltb j i)%nat then (h,0) else ((-0.5 * h * (2 - a)),0)) .

(** ideal solution vector *)
Definition pq_vector (h: R) (p q : R -> R) (t : R) : @matrix C 2 1 := 
  mk_matrix 2 1 (fun i j => if (Nat.eqb i j) then (p t , 0) else (q t , 0)) .

(** arbitrary solution vector *)
Definition s_vector (ic: R * R) := @mk_matrix C 2 1%nat
  (fun i j => if (Nat.eqb i j) then ((fst ic),0) else ((snd ic),0)).

(** equivalence between matrix update and leapfrog step*)
Lemma transition_matrix_equiv_1:
  forall (ic : R * R) (h : R),  
  let Mx := Mmult (t_matrix h) (s_vector ic) in
   coeff_mat Hierarchy.zero Mx 0 0 = (fst (leapfrog_stepR ic h),0).
Proof.
intros. subst Mx. destruct ic. cbv. 
all : (f_equal; field_simplify; nra) .
Qed.

(** equivalence between matrix update and leapfrog step*)
Lemma transition_matrix_equiv_2:
  forall (ic : R * R) (h : R), 
  let Mx := Mmult (t_matrix h) (s_vector ic) in
coeff_mat Hierarchy.zero Mx 1 0 = (snd (leapfrog_stepR ic h),0).
Proof.
intros. subst Mx. destruct ic. cbv.
all : (f_equal; field_simplify; nra) .
Qed.


(** equivalence between matrix updates and leapfrog iterations*)
Lemma transition_matrix_pow_equiv:
  forall (ic : R * R) (h : R) (n : nat), 
  let Mx := Mmult (Mpow 2 n (t_matrix h)) (s_vector ic) in
   (coeff_mat Hierarchy.zero Mx 0 0 , coeff_mat Hierarchy.zero Mx 1 0) = (RtoC (fst (iternR ic h n)) , RtoC (snd (iternR ic h n))) . 

Proof.
intros.
induction n.
-
subst Mx. unfold Mpow, iternR. 
replace M_ID with (@Mone C_Ring).
rewrite Mmult_one_l. 
unfold s_vector. repeat rewrite coeff_mat_bij; try lia.
simpl.
destruct ic. unfold RtoC; auto.
admit.
- 
Admitted.

(** The eigenvalues of the transition matrix *)
Definition lambda_1 (h : R) : C := (1 -0.5 * h^2 , -h * sqrt(2 - h) * 0.5 * sqrt(h + 2))
. 
Definition lambda_2 (h : R) : C := (1 -0.5 * h^2 ,  h * sqrt(2 - h) * 0.5 * sqrt(h + 2))
.
Definition eigenvalue_vector (h : R) : @matrix C 2 1 :=
mk_matrix 2 1 ( fun i j => if ((Nat.eqb i j)) then lambda_1 h else lambda_2 h)
.
Definition eigenvalue_matrix (h : R) : @matrix C 2 2 :=
   mk_matrix 2 2 ( fun i j => if ((Nat.eqb i 0) && (Nat.eqb j 0) ) then lambda_1 h else
    if ( (Nat.eqb i 1) && (Nat.eqb j 1) ) then lambda_2 h else 0)
.



(** The eigenvectors of the transition matrix *)
Definition eV_1 (h : R) : @matrix C 2 1 :=
mk_matrix 2 1 ( fun i j => if ((Nat.eqb i j)) then (0 , -0.5 * sqrt(4 - h^2)) else C1)
.
Definition eV_2 (h : R) : @matrix C 2 1 :=
mk_matrix 2 1 ( fun i j => if ((Nat.eqb i j)) then (0 ,  0.5 * sqrt(4 - h^2)) else C1)
.
Definition eigenvector_matrix (h : R) : @matrix C 2 2 :=
   mk_matrix 2 2 ( fun i j => if ( (Nat.eqb i 0) && (Nat.eqb j 0)) then (0 , -0.5 * sqrt(4 - h^2)) else
    if ( (Nat.eqb i 0) && (Nat.eqb j 1)) then (0 ,  0.5 * sqrt(4 - h^2)) else C1)
.
(** We define the Gram matrix MTM for the transition matrix. The eigenvalues of the matrix MTM are the 
    singular values of the transition matrix *)
Definition MTM (h : R) : @matrix C 2 2 :=
   mk_matrix 2 2 ( fun i j => if ( (Nat.eqb i 0) && (Nat.eqb j 0)) then (0.25 * h^4 + 1, 0) else
    if ( negb (Nat.eqb i j) ) then (0.125 * h^3*(2 - h^2),0) else 
    (0.0625 * h^6 - 0.25*h^4 + 1, 0))
.



(** The eigenvalues of MTM *)
Definition MTM_lambda_1 (h : R) : R := 
(h^10 - h^7*sqrt(h^6 + 64) + 4*h^6 + 64*h^4 - 4*h^3*sqrt(h^6 + 64) - 32*h*sqrt(h^6 + 64) + 256)/(2*(h^4*Rabs((h^3 - 8*h + sqrt(h^6 + 64))/(h^2 - 2))^2 + 16*h^4 - 4*h^2*Rabs((h^3 - 8*h + sqrt(h^6 + 64))/(h^2 - 2))^2 - 64*h^2 + 4*Rabs((h^3 - 8*h + sqrt(h^6 + 64))/(h^2 - 2))^2 + 64)) 
.
Definition MTM_lambda_2 (h : R) : R := 
(h^10 + h^7*sqrt(h^6 + 64) + 4*h^6 + 64*h^4 + 4*h^3*sqrt(h^6 + 64) + 32*h*sqrt(h^6 + 64) + 256)/(2*(h^4*Rabs((-h^3 + 8*h + sqrt(h^6 + 64))/(h^2 - 2))^2 + 16*h^4 - 4*h^2*Rabs((-h^3 + 8*h + sqrt(h^6 + 64))/(h^2 - 2))^2 - 64*h^2 + 4*Rabs((-h^3 + 8*h + sqrt(h^6 + 64))/(h^2 - 2))^2 + 64))
.
Definition MTM_eigenvalue_vector (h : R) : @matrix R 2 1 :=
mk_matrix 2 1 ( fun i j => if ((Nat.eqb i j)) then MTM_lambda_1 h else MTM_lambda_2 h)
.
Definition MTM_eigenvalue_matrix (h : R) : @matrix C 2 2 :=
   mk_matrix 2 2 ( fun i j => if ((Nat.eqb i 0) && (Nat.eqb j 0) ) then RtoC (MTM_lambda_1 h) else
    if ( (Nat.eqb i 1) && (Nat.eqb j 1) ) then RtoC (MTM_lambda_2 h) else 0)
.



(** The eigenvectors of MTM, numbered to match their eigenvalues *)
Definition MTM_eV_1 (h: R) : @matrix C 2 1 := mk_matrix 2 1 ( fun i _ =>
  if (Nat.eqb i 0) then RtoC((h^3 - 8*h + sqrt(h^6 + 64))/((h^2 - 2)*sqrt(Rabs((h^3 - 8*h + sqrt(h^6 + 64))/(h^2 - 2))^2 + 16))) else
    RtoC(4/sqrt(Rabs((h^3 - 8*h + sqrt(h^6 + 64))/(h^2 - 2))^2 + 16)))
.
Definition MTM_eV_2 (h: R) : @matrix C 2 1 := mk_matrix 2 1 ( fun i _ =>
  if (Nat.eqb i 0) then RtoC((h^3 - 8*h - sqrt(h^6 + 64))/((h^2 - 2)*sqrt(Rabs((-h^3 + 8*h + sqrt(h^6 + 64))/(h^2 - 2))^2 + 16))) else
    RtoC(4/sqrt(Rabs((-h^3 + 8*h + sqrt(h^6 + 64))/(h^2 - 2))^2 + 16)))
.




(** we use MTM_eigenvector_matrix as the matrix V in e.g. M V = V L , where L is the diagonal matrix of eigenvalues
   and M is the transition matrix.*)
Definition MTM_eigenvector_matrix (h : R) : @matrix C 2 2 :=
   mk_matrix 2 2 ( fun i j => if ( (Nat.eqb i 0) && (Nat.eqb j 0)) then (coeff_mat zero (MTM_eV_1 h) 0 0) else
    if ( (Nat.eqb i 0) && (Nat.eqb j 1)) then (coeff_mat zero (MTM_eV_2 h) 0 0) else
    if ( (Nat.eqb i 1) && (Nat.eqb j 0)) then (coeff_mat zero (MTM_eV_1 h) 1 0) else
    (coeff_mat zero (MTM_eV_2 h) 1 0))
.


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



Lemma MTM_aux  (h : R) :
  Mmult (matrix_conj_transpose _ _ (t_matrix h)) (t_matrix h) = MTM h.
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
Theorem MTM_eigens_correct (h : R) :
  0 < h  < 1.4 -> 
  Mmult (MTM h) (MTM_eigenvector_matrix h) = 
  Mmult (MTM_eigenvector_matrix h) (MTM_eigenvalue_matrix h).
Proof.
intros.
apply mk_matrix_ext => i j Hi Hj.
replace (Init.Nat.pred 2) with (S 0) by lia.
repeat rewrite sum_Sn.
repeat rewrite sum_O.
unfold MTM, MTM_eigenvector_matrix, MTM_eigenvalue_matrix.
repeat rewrite coeff_mat_bij.
all: try lia.
assert (A: i = 0%nat \/ i = 1%nat) by lia;
destruct A. 
-
assert (B: j = 0%nat \/ j = 1%nat) by lia;
destruct B. 
+ (* case i = 0 , j = 0 *)
subst.
simpl.
change mult with Cmult.
change plus with Cplus.
unfold RtoC.
cbv [Cplus Cmult]; simpl.
repeat rewrite Rmult_0_l. 
repeat rewrite Rmult_0_r; unfold C0.
repeat rewrite Rminus_0_r.
repeat rewrite Rplus_0_r. 
repeat rewrite Rmult_1_r.
f_equal; try nra.
unfold MTM_lambda_1, MTM_eV_1.
rewrite <- Rabs_mult.
repeat match goal with |-context [Rabs( (?a / ?b) * (?a / ?b)) ] =>
replace ( (a / b) * (a / b)) with ( (a/b)^2) by nra
end.
repeat rewrite Rabs_sqr_le.
repeat rewrite pow2_abs.
apply Rminus_diag_uniq.
field_simplify.
repeat rewrite pow2_sqrt; try nra.
field_simplify.
replace (sqrt (h * (h * (h * (h * (h * h)))) + 64))
with (sqrt (h ^ 6 + 64)).
repeat rewrite Rmult_assoc.
repeat rewrite sqrt_def.
field_simplify.

assert (forall a b , b <> 0 -> a = 0 -> a / b = 0).
intros.
subst.
field.
auto.

apply H0.
set (aa:= sqrt (((h * (h * h) - 8 * h + sqrt (h ^ 6 + 64)) / (h * h - 2)) ^ 2 + 16)).
match goal with |-context[ ?a <> 0] =>
replace a with 
((4 * h ^ 12  - 24 * h ^ 10  + 4 * h ^ 9 * sqrt (h ^ 6 + 64)  +
48 * h ^ 8  - 56 * h ^ 7 * sqrt (h ^ 6 + 64)  + 
224 * h ^ 6  + 240 * h ^ 5 * sqrt (h ^ 6 + 64)  - 
1536 * h ^ 4  - 416 * h ^ 3 * sqrt (h ^ 6 + 64)  + 
3072 * h ^ 2  + 256 * h * sqrt (h ^ 6 + 64)  - 
2048) * aa)
by nra
end.
apply Rmult_integral_contrapositive_currified.
interval with ( i_bisect h, i_taylor h, i_degree 3).
interval with ( i_bisect h, i_taylor h, i_degree 3).
*
(* TODO : Andrew *) admit.
*
interval with ( i_bisect h, i_taylor h, i_degree 3).
*
interval with ( i_bisect h, i_taylor h, i_degree 3).
*
f_equal; nra.
*
interval with ( i_bisect h, i_taylor h, i_degree 3).
*
repeat (split; try interval with ( i_bisect h, i_taylor h, i_degree 3)).
+ 
subst.
Admitted.




Lemma Cmod_RtoC (a : R): 
  0 <= a ->
Cmod (RtoC a) = a.
Proof.
unfold RtoC.
unfold Cmod, fst, snd.
rewrite pow_i; try lia.
rewrite Rplus_0_r.
apply sqrt_pow2.
Qed.

Lemma eq_sqrt_eq (x y : R) :
  x = y -> sqrt x = sqrt y.
Proof.
intros.
subst.
nra.
Qed.

Lemma sv_vector_implies (A V Λ : matrix 2 2):
   is_orthogonal_matrix 2 V ->
   diag_pred 2 Λ ->
   Mmult (Mmult (matrix_conj_transpose 2 2 A) A) V = Mmult V Λ -> 
  forall (i :nat), (i < 2)%nat ->
  let x := mk_matrix 2 1
  (fun ii _ : nat =>
     (coeff_mat zero V ii i)) in
  (Mmult (matrix_conj_transpose 2 1 x) (Mmult (Mmult (matrix_conj_transpose 2 2 A) A) x)) =
  (Mmult (matrix_conj_transpose 2 1 x) (mat_coeff_mult (coeff_mat zero Λ i i) 2 1 x)).
Proof.
intros.
apply mk_matrix_ext; intros.
unfold Mmult at 1 in H1.
unfold Mmult at 2 in H1.
rewrite <- mk_matrix_ext in H1.
subst x; auto.
Admitted.



(* if σ^2 is the largest singular value of A ∈ M(C^2) then σ is the two-norm of A *)
Theorem max_sv_pred_implies_two_norm_pred   (A : @matrix C 2 2) (σ : R):
  max_sv_pred 2 A σ  ->  two_norm_pred 2 A σ.
Proof.
intros.
unfold two_norm_pred. split.
- 
pose proof vectors_in_basis 2 u A as Hb.
unfold max_sv_pred in H.
destruct H as ( H0 & V & Λ & H1 & H2 & H3 & H4 & H5 & H6).
unfold basis_pred in Hb.
specialize (Hb V Λ).
assert (exists a : matrix 2 1, u = Mmult V a).
+
apply Hb; repeat (split; auto).
+
clear Hb.
destruct H as (a & Hu); subst.
unfold vec_two_norm.
repeat rewrite tranpose_rewrite.
rewrite <- Mmult_assoc.
rewrite <- Mmult_assoc.
replace (Mmult (matrix_conj_transpose 2 2 A) (Mmult A (Mmult V a))) with
(Mmult (Mmult (Mmult (matrix_conj_transpose 2 2 A) A) V) a)
by (repeat rewrite Mmult_assoc; auto).
rewrite H1.
replace (Mmult (matrix_conj_transpose 2 2 V) (Mmult (Mmult V Λ) a)) with
(Mmult (Mmult (matrix_conj_transpose 2 2 V) V) (Mmult Λ a))
by (repeat rewrite Mmult_assoc; auto).
replace (Mmult (Mmult (matrix_conj_transpose 2 1 a) (matrix_conj_transpose 2 2 V)) (Mmult V a))
with 
(Mmult (matrix_conj_transpose 2 1 a) (Mmult (Mmult (matrix_conj_transpose 2 2 V) V) a))
by (repeat rewrite Mmult_assoc; auto).
destruct H2 as (H2 & _).
rewrite H2.
repeat rewrite Mmult_one_l.
replace (Mmult Λ a)
with 
(mk_matrix 2 1 (fun i _ : nat =>
  mult (coeff_mat zero Λ i i) (coeff_mat zero a i 0))).
replace σ with (sqrt (σ^2)) by (apply sqrt_pow2; auto).
rewrite <- sqrt_mult; try nra; try apply Cmod_ge_0.
apply sqrt_le_1_alt.
replace (σ^2) with (Cmod (σ^2)) by (apply Cmod_RtoC; try nra).
rewrite <- Cmod_mult.
unfold Mmult.
repeat rewrite coeff_mat_bij; try lia.
replace (Init.Nat.pred 2) with (S 0) by lia.
repeat rewrite sum_Sn.
repeat rewrite coeff_mat_bij; try lia.
repeat rewrite sum_O.
repeat rewrite coeff_mat_bij; try lia.
repeat rewrite sum_Sn.
repeat rewrite sum_O.
change plus with Cplus.
change mult with Cmult.
unfold matrix_conj_transpose.
repeat rewrite coeff_mat_bij; try lia.
rewrite Cmult_comm.
rewrite <- Cmult_assoc.
rewrite C_sqr_ccong.
rewrite Cmult_comm.
rewrite Cplus_comm.
rewrite Cmult_comm.
rewrite <- Cmult_assoc.
rewrite C_sqr_ccong.
repeat rewrite C_sqr_ccong2.


assert (Hn: (1 < 2)%nat) by lia.
assert (Hnn: (0 < 2)%nat) by lia.
pose proof (H6 0%nat Hnn) as (HL1 & HL2 & HL3).
pose proof (H6 1%nat Hn) as (HL4 & HL5 & HL6).
rewrite HL1. 
rewrite HL4.

repeat rewrite <- RtoC_mult.
repeat rewrite <- RtoC_plus.
repeat rewrite <- RtoC_mult.
repeat rewrite Cmod_R.

rewrite Rmult_comm.
apply Rabs_pos_le.
apply Rle_plus; auto.
apply Rle_mult; auto.
apply sqr_plus_pos.
apply Rle_mult; auto.
apply sqr_plus_pos.

apply Rle_mult; auto; 
  try apply square_pos.
apply Rle_plus; auto; 
  apply sqr_plus_pos.

rewrite Rmult_plus_distr_l.
rewrite Rplus_comm.
apply Rplus_le_compat.
*
rewrite Rmult_comm.
apply Rmult_le_compat_r; auto.
apply sqr_plus_pos.
*
rewrite Rmult_comm.
apply Rmult_le_compat_r; auto.
apply sqr_plus_pos.
*
apply mk_matrix_ext; intros.
assert (Hj: (j = 0)%nat) by lia; subst.
assert (Hi: ((i = 0)%nat \/ (i <> 0)%nat)) by lia; destruct Hi.
--
replace (Init.Nat.pred 2) with (S 0) by lia.
rewrite sum_Sn.
rewrite sum_O.
unfold diag_pred in H3.
subst.
assert (Hij: (0 < 2)%nat /\ (1 < 2)%nat /\ 0%nat <> 1%nat) by lia.
specialize (H3 0%nat 1%nat Hij).
change ((@coeff_mat (AbelianGroup.sort (Ring.AbelianGroup C_Ring)) 2 2
        (@zero (Ring.AbelianGroup C_Ring)) Λ 0 1))
with 
(@coeff_mat C 2 2 (@zero C_AbelianGroup) Λ 0 1).
rewrite H3.
rewrite (@mult_zero_l).
rewrite (@plus_zero_r); auto.
--
replace (Init.Nat.pred 2) with (S 0) by lia.
rewrite sum_Sn.
rewrite sum_O.
assert (Hi: (i=1)%nat) by lia.
subst.
assert (Hij: (1 < 2)%nat /\ (0 < 2)%nat /\ 1%nat <> 0%nat) by lia.
specialize (H3 1%nat 0%nat Hij).
change ((@coeff_mat (AbelianGroup.sort (Ring.AbelianGroup C_Ring)) 2 2
        (@zero (Ring.AbelianGroup C_Ring)) Λ 1 0))
with 
(@coeff_mat C 2 2 (@zero C_AbelianGroup) Λ 1 0).
rewrite H3.
rewrite (@mult_zero_l).
rewrite (@plus_zero_l); auto.
-
unfold not; intros.
destruct H0 as (s & H0).
unfold max_sv_pred in H.
destruct H as (Hs & V & Λ & H1 & H2 & H3 & H4 & H5 & H6).
destruct H4 as (i & Hi).
set (x:= mk_matrix 2 1
  (fun ii _ : nat =>
     (coeff_mat zero V ii i))).
assert (σ * vec_two_norm 2 x <= s * vec_two_norm 2 x).
+
specialize (H0 x).
assert (vec_two_norm 2 (Mmult A x) = σ * vec_two_norm 2 x ).
*
etransitivity.
unfold vec_two_norm.
apply eq_sqrt_eq.
apply Ceq_Cmod_eq.
repeat rewrite tranpose_rewrite.
rewrite <- Mmult_assoc.
apply coeff_mat_ext.
pose proof sv_vector_implies A V Λ  H2 H3 H1 i Hi.



replace (Mmult (matrix_conj_transpose 2 2 A) (Mmult A x)) with
  (Mmult (Mmult (matrix_conj_transpose 2 2 A) A) x) by 
  (repeat rewrite Mmult_assoc; auto).

apply H.
unfold vec_two_norm.

replace σ with (sqrt (σ^2)) by (apply sqrt_pow2; auto).
rewrite <- sqrt_mult; try nra; try apply Cmod_ge_0.
apply eq_sqrt_eq.
replace (σ^2) with (Cmod (σ^2)) by (apply Cmod_RtoC; try nra).
rewrite <- Cmod_mult.
apply Ceq_Cmod_eq.
unfold Mmult.
unfold matrix_conj_transpose.
unfold mat_coeff_mult.
repeat rewrite coeff_mat_bij; try lia.
replace (Init.Nat.pred 2) with (S 0) by lia.
repeat rewrite sum_Sn.
repeat rewrite sum_O.
repeat rewrite coeff_mat_bij; try lia.
simpl in H5.
change (@coeff_mat C 2 2 (@zero C_AbelianGroup) Λ i i) with  
(@coeff_mat (AbelianGroup.sort C_AbelianGroup) 2 2 (@zero C_AbelianGroup) Λ i i)
in H5.
rewrite H5.
subst x.
repeat rewrite coeff_mat_bij; try lia.
change plus with Cplus.
change mult with Cmult.
rewrite Cmult_plus_distr_l; simpl; auto.
f_equal.
rewrite <- Cmult_comm.
rewrite <- Cmult_assoc.
f_equal.
rewrite Cmult_comm; auto.
rewrite <- Cmult_comm.
rewrite <- Cmult_assoc.
f_equal.
rewrite Cmult_comm; auto.
*
rewrite H in H0.
destruct H0; auto.
+ 
specialize (H0 x).
destruct H0.
assert (HF: s * vec_two_norm 2 x < s * vec_two_norm 2 x).
*
eapply Rlt_le_trans.
apply H4.
auto.
*
apply Rlt_irrefl in HF; auto.  
Qed.



Lemma MTM_lambda_2_pos (h : R | 0 < h < 1.4): 
0 <= (MTM_lambda_2 (proj1_sig h)).
Proof.
destruct h as (h & Hh); simpl.
unfold MTM_lambda_2.
interval with ( i_bisect h, i_taylor h, i_degree 3).
Qed.

Lemma MTM_lambda_2_pos_2 (h : R) :
 0 < h < 1.4-> 
0 <= (MTM_lambda_2 h).
Proof.
intros.
unfold MTM_lambda_2.
interval with ( i_bisect h, i_taylor h, i_degree 3).
Qed.


Lemma MTM_lambda_1_pos_2 (h : R) :
 0 < h < 1.4 -> 
0 <= (MTM_lambda_1 h).
Proof.
intros.
unfold MTM_lambda_1.
interval with ( i_bisect h, i_taylor h, i_degree 3).
Qed.


Lemma Rdiv_le a b c d :
  0 < b  -> 0 < d -> 
  a * b <= c * d -> a/d <= c/b.
Proof.
intros.
apply Rle_div_l in H1 ; auto.
replace (a * b / d ) with
(a / d * b) in H1 by nra.
rewrite Rle_div_r in H1; auto.
Qed.

Lemma Rdiv_le2 a b c  :
  0 < b  ->
  a  <= c  -> a/b <= c/b.
Proof.
intros.
apply Rle_div_l; auto.
replace (c / b * b) with c; auto.
field. nra.
Qed.


Lemma eig_MTM_le (h: R):
  0 < h < 1.4 -> 
   (MTM_lambda_1 h) <=  (MTM_lambda_2 h).
Proof.
intros.
unfold MTM_lambda_1, MTM_lambda_2.
assert (h ^ 4 - 4 * h ^ 2 + 4 <> 0) by 
  interval with ( i_bisect h, i_taylor h, i_degree 3).
apply Rdiv_le; try
interval with ( i_bisect h, i_taylor h, i_degree 3).
repeat rewrite pow2_abs.
field_simplify; try interval.
repeat rewrite pow2_sqrt; try nra.
field_simplify; auto. 
match goal with |-context [?a ^ 3] =>
replace (a^3) with (a^2 * a) by nra
end.
repeat rewrite pow2_sqrt; try nra.
field_simplify; auto.
apply Rdiv_le2; try
interval with ( i_bisect h, i_taylor h, i_degree 3).
apply Rminus_le.
field_simplify. 
replace (-16 * h ^ 17 * sqrt (h ^ 6 + 64) + 128 * h ^ 15 * sqrt (h ^ 6 + 64) -
384 * h ^ 13 * sqrt (h ^ 6 + 64) - 512 * h ^ 11 * sqrt (h ^ 6 + 64) +
7936 * h ^ 9 * sqrt (h ^ 6 + 64) - 24576 * h ^ 7 * sqrt (h ^ 6 + 64) +
32768 * h ^ 5 * sqrt (h ^ 6 + 64) - 16384 * h ^ 3 * sqrt (h ^ 6 + 64))
with
((-16 * h ^ 14 + 128 * h ^ 12  -
384 * h ^ 10  - 512 * h ^ 8  +
7936 * h ^ 6  - 24576 * h ^ 4  +
32768 * h ^ 2  - 16384) * h^3 * sqrt (h ^ 6 + 64)) by nra.
apply Rmult_le_0_r; try apply sqrt_pos.
apply Rmult_le_0_r; try nra.
interval
 with ( i_bisect h, i_depth 7, i_taylor h, i_degree 3).
Qed.

Lemma div_eq_1 : 
 (forall a b : R, a = b -> b <> 0 -> a / b = 1).
Proof.
intros; subst. field; auto. Qed.


Lemma MTM_eigenvectors_orthogonal_1 (h: R):
  0 < h < 1.4 -> 
Mmult (matrix_conj_transpose 2 2 (MTM_eigenvector_matrix h))
  (MTM_eigenvector_matrix h) = Mone.
Proof.
intros.
unfold MTM_eigenvector_matrix, matrix_conj_transpose.
repeat match goal with |- context [(@mk_matrix C 2 2 ?a)] =>
change (@mk_matrix C 2 2 a) with 
(@mk_matrix (AbelianGroup.sort C_AbelianGroup) 2 2 a)
end.
unfold Mmult, Mone.
apply mk_matrix_ext => i j Hi Hj.
assert (Hi2: (i = 1)%nat \/ (i <> 1)%nat) by lia; destruct Hi2;
assert (Hj2: (j = 1)%nat \/ (j <> 1)%nat) by lia; destruct Hj2; subst; simpl.
-
repeat rewrite sum_Sn.
repeat rewrite sum_O.
repeat rewrite coeff_mat_bij; try lia.
simpl.
unfold Cconj,RtoC, MTM_eV_2; simpl.
change mult with Cmult.
change plus with Cplus.
change one with C1.
repeat rewrite coeff_mat_bij; try lia.
simpl.
cbv [Cplus Cmult RtoC C1 fst snd].
f_equal; field_simplify; try nra.
repeat rewrite pow2_sqrt.
field_simplify.
repeat rewrite pow2_abs.
field_simplify.
apply div_eq_1.
repeat rewrite pow2_sqrt; nra.
repeat rewrite pow2_sqrt; try nra.
apply Rgt_not_eq;
field_simplify.
interval
 with ( i_bisect h, i_depth 7, i_taylor h, i_degree 3).
split. 
all: (try interval
 with ( i_bisect h, i_depth 7, i_taylor h, i_degree 3)).
repeat rewrite <- Rabs_mult.
match goal with |-context [?a <> 0] =>
  field_simplify a
end.
repeat match goal with |-context [Rabs( (?a / ?b) * (?a / ?b)) ] =>
replace ( (a / b) * (a / b)) with ( (a/b)^2) by nra
end.
repeat rewrite Rabs_sqr_le.
repeat rewrite pow2_abs.
match goal with |-context [?a <> 0] =>
  field_simplify a; try nra
end.
repeat rewrite pow2_sqrt; try nra.
match goal with |-context [?a <> 0] =>
  field_simplify a; try nra
end.
all: try split; try 
interval
 with ( i_bisect h, i_depth 7, i_taylor h, i_degree 3).
-
assert (j = 0)%nat by lia; subst.
repeat rewrite sum_Sn.
repeat rewrite sum_O.
repeat rewrite coeff_mat_bij; try lia.
simpl.
unfold Cconj,RtoC, MTM_eV_1; simpl.
change mult with Cmult.
change plus with Cplus.
change one with C1.
change zero with C0.
repeat rewrite coeff_mat_bij; try lia.
simpl.
cbv [Cplus Cmult RtoC C0 fst snd].
f_equal; field_simplify; try nra.
repeat rewrite pow2_sqrt.
field_simplify. 
assert ( forall a, 0/a = 0) by (intros;nra).
apply H0.
apply tech_Rplus.
apply Raux.Rle_0_minus.
Admitted.


Lemma MTM_eigenvectors_orthogonal_2 (h: R):
  0 < h < 1.4 -> 
Mmult (MTM_eigenvector_matrix h) 
(matrix_conj_transpose 2 2 (MTM_eigenvector_matrix h)) = Mone.
Proof.
Admitted.


Lemma two_norm_pred_eq (h : R | 0 < h < 1.4): 
 two_norm_pred 2 (t_matrix (proj1_sig h)) (sqrt (MTM_lambda_2 (proj1_sig h))).
Proof.
apply ( max_sv_pred_implies_two_norm_pred
  (t_matrix (proj1_sig h)) (sqrt (MTM_lambda_2 (proj1_sig h)))).
unfold max_sv_pred.
destruct h as (h & Hh); simpl; split; try apply sqrt_pos.
exists (MTM_eigenvector_matrix h), (MTM_eigenvalue_matrix h).
repeat split.
-
rewrite MTM_aux.
apply (MTM_eigens_correct h Hh).
-
apply MTM_eigenvectors_orthogonal_1; auto.
-
apply MTM_eigenvectors_orthogonal_2; auto.
-
unfold diag_pred, MTM_eigenvalue_matrix.
intros; rewrite coeff_mat_bij; try lia.
assert (Hi: (i = 0)%nat \/ (i <> 0)%nat) by lia; destruct Hi.
+ 
subst.
assert ((j =? 0) = false).
destruct H as (H & A & B).
apply Nat.eqb_neq; auto.
rewrite H0. unfold RtoC; auto.
+
apply Nat.eqb_neq in H0. 
rewrite H0. 
simpl.
assert (Hi: (i = 1)%nat \/ (i <> 1)%nat) by lia; destruct Hi.
*
subst.
assert ((j =? 1) = false).
destruct H as (H & A & B).
apply Nat.eqb_neq; auto.
rewrite H1. unfold RtoC; auto.
*
apply Nat.eqb_neq in H1.
rewrite H1. unfold RtoC; auto.
-
intros.
rewrite Rmult_1_r.
unfold Cmod.
rewrite <- sqrt_mult_alt; try apply MTM_lambda_2_pos_2; auto.
assert (H: (1 < 2)%nat) by lia.
exists (exist (fun i:nat => (i < 2)%nat) 1%nat H); simpl; repeat split.
+
rewrite sqrt_square; try apply MTM_lambda_2_pos_2; auto.
+
unfold MTM_eigenvalue_matrix.
assert (Hi: (i = 1)%nat \/ (i = 0)%nat) by lia; destruct Hi.
*
subst; simpl.
rewrite coeff_mat_bij; try lia; simpl; auto.
* 
subst; simpl.
rewrite coeff_mat_bij; try lia; simpl; auto.
+
assert (Hi: (i = 1)%nat \/ (i = 0)%nat) by lia; destruct Hi;subst; simpl;
try (apply MTM_lambda_2_pos_2; auto); try
(apply MTM_lambda_1_pos_2; auto).
+
assert (Hi: (i = 1)%nat \/ (i = 0)%nat) by lia; destruct Hi;subst; simpl.
*
rewrite sqrt_square; try apply MTM_lambda_2_pos_2; auto.
apply Rle_refl.
*
rewrite sqrt_square; try apply MTM_lambda_2_pos_2; auto.
apply eig_MTM_le; auto.
Qed.



Definition two_norm_t_matrix (h : R | 0 < h < 1.4):=
  proj1_sig (exist (two_norm_pred 2 (t_matrix (proj1_sig h))) (sqrt (MTM_lambda_2 (proj1_sig h))) (two_norm_pred_eq h))
.


Lemma eig1_mod_eq_1 (h: R):
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



Lemma eig_mod_eq_lemma (h: R):
  Cmod (lambda_1 h) = Cmod (lambda_2 h).
Proof.
unfold lambda_1, Cmod; intros.
simpl.
f_equal.
field_simplify; nra.
Qed.


Lemma eig2_mod_eq_1 (h: R):
  Cmod (lambda_2 h) = 1.
Proof.
Admitted.



Lemma two_norm_t_matrix_eq :
sqrt (Cmod (MTM_lambda_2 h)) <= 4503616807272453 / 4503599627370496
(* <= 1.0000038147045427 *).
Proof.
unfold MTM_lambda_2, RtoC, Cmod, fst, snd, h.
match goal with |-context [sqrt (sqrt ?a) <= ?b] =>
  field_simplify a
end.
match goal with |-context [sqrt (sqrt ?a) <= _] =>
interval_intro (sqrt (sqrt a)) upper
end.
apply H.
interval.
Qed.

Lemma t_matrix_norm_sub_mult :
  forall (h : R | 0 < h < 1.4),
  forall (y : @matrix C 2 1%nat),
  vec_two_norm_2d (Mmult (t_matrix (proj1_sig h)) y) <= (two_norm_t_matrix h) * vec_two_norm_2d y.
Proof.
intros.
pose proof two_norm_pred_eq h.
unfold two_norm_pred in H.
specialize (H y).
destruct H as (H1 & H2).
unfold two_norm_t_matrix. simpl.
repeat rewrite <- two_norms_eq_2d.
apply H1.
Qed.

Lemma matrix_analysis_local_truncation_error:
  forall p q : R -> R,
  forall t0 tn: R,
  forall (h  :R | 0 <  h < sqrt 2),
  Harmonic_oscillator_system p q ω t0 ->  
  vec_two_norm_2d (Mplus (pq_vector (proj1_sig h) p q (tn + (proj1_sig h))) (Mopp (Mmult (t_matrix (proj1_sig h)) (s_vector (p tn, q tn))))) <= 
      (proj1_sig h)^3 * vec_two_norm_2d (s_vector (p t0, q t0)).
Proof.
intros ? ? ? ? ? HSY; intros.
destruct h as (h & Hh). simpl in *.
unfold vec_two_norm_2d.
unfold Mplus, Mopp, Mmult; simpl in *.
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
assert (0 < ω * h <= 4).
(unfold ω; split; try nra; try interval).
pose proof local_truncation_error p q t0 tn h H HSY as LTE.
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
  forall p q : R,
  forall n : nat, 
  forall h : {h : R | 0 <  h < 1.4},
  let Mn := Mpow 2 n (t_matrix (proj1_sig h)) in
  vec_two_norm_2d  (Mmult Mn (s_vector (p, q))) <= 
      (sqrt (Cmod (MTM_lambda_2 (proj1_sig h)))) ^ n * vec_two_norm_2d (s_vector (p,q)).
Proof.
intros ? ? ? h; intros. 
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
replace (Mmult (Mmult (Mpow 2 n 
  (t_matrix (@proj1_sig R (fun h1 : R => 0 < h1 < 1.4) h))) (t_matrix (@proj1_sig R (fun h1 : R => 0 < h1 < 1.4) h))) (s_vector (p, q)))
with
( Mmult (t_matrix (@proj1_sig R (fun h1 : R => 0 < h1 < 1.4) h)) 
  (Mmult (Mpow 2 n (t_matrix (@proj1_sig R (fun h1 : R => 0 < h1 < 1.4) h))) (s_vector (p, q)))).
destruct (@Mmult C_Ring 2 2 1 (Mpow 2 n (t_matrix (@proj1_sig R (fun h1 : R => 0 < h1 < 1.4) h))) (s_vector (p, q))).
eapply Rle_trans.
pose proof t_matrix_norm_sub_mult h (t, t0).
apply H.
eapply Rle_trans.
apply Rmult_le_compat_l.
unfold two_norm_t_matrix; simpl.
apply sqrt_pos.
apply IHn.
unfold two_norm_t_matrix.
simpl.
rewrite Cmod_RtoC; try apply MTM_lambda_2_pos_2; try (destruct h; simpl; auto).
apply Req_le.
rewrite Rmult_assoc; auto.
rewrite Mmult_assoc.
rewrite Mpow_comm; auto.
Qed.


Lemma h_bnd_lem :
0 <  h < 1.4.
Proof.
split; unfold h; unfold ω; try nra.
Qed.


Theorem matrix_analysis_method_bound_fixed_h_n : 
  forall p q: R,
  forall n : nat, 
  let Mn := Mpow 2 n (t_matrix  h ) in
  vec_two_norm_2d  (Mmult Mn (s_vector (p, q))) <= 
      (4503616807272453 / 4503599627370496) ^ n * vec_two_norm_2d (s_vector (p,q)).
Proof.
intros.
pose proof h_bnd_lem as Hbnd.
set (j := (exist (fun x => 0 < x < 1.4) h) h_bnd_lem).
pose proof matrix_analysis_method_bound_n p q n j.
pose proof two_norm_t_matrix_eq.
simpl in H.
eapply Rle_trans.
apply H.
apply Rmult_le_compat_r.
apply Rnorm_pos.
apply pow_incr; split; auto.
apply sqrt_pos.
Qed.


(*Matrix([[-1/sqrt(h**2 - 4), 1/2], [1/sqrt(h**2 - 4), 1/2]]) *)
Definition eigenvector_matrix_inv (h : R) : matrix 2 2 :=
  mk_matrix 2 2 (fun i j => if (Nat.eqb i 0 && Nat.eqb j 0) then RtoC (-1/sqrt(h^2 - 4)) else 
    if (Nat.eqb i 1 && Nat.eqb j 0) then RtoC (1/sqrt(h^2 - 4)) else (0.5,0))
.


Lemma t_matrix_diagonalizable :
  forall h  : R, 
       0 <  h < sqrt 2 ->
  (t_matrix h) = Mmult (eigenvector_matrix h) (Mmult (eigenvalue_matrix h) (eigenvector_matrix_inv h)).
Proof.
intros.
Admitted.


Lemma two_norm_eV :
0.5 * vec_two_norm_2d (eV_1 h) + 0.5 * vec_two_norm_2d (eV_2 h) <= 1.41412724299301.
Proof.
unfold vec_two_norm_2d, Rprod_norm, eV_1, eV_2, C1,  Cmod, h.
repeat rewrite coeff_mat_bij; try lia.
simpl.
rewrite Rmult_0_l.
rewrite Rplus_0_l.
rewrite Rplus_0_r.
repeat rewrite Rmult_1_r.
rewrite sqrt_1.
repeat rewrite Rmult_1_r.
rewrite Rplus_0_l.
interval.
Qed.

Lemma n_steps_bounded_aux :
  forall n : nat, 
  let Mn := Mpow 2 n (t_matrix  h) in
  vec_two_norm_2d  (Mmult Mn (s_vector (0, 1))) <= 
    0.5 * vec_two_norm_2d (eV_1 h) + 0.5 * vec_two_norm_2d (eV_2 h).
Proof.
intros.
set (a:= mk_matrix 2 1 (fun _ _ => RtoC 0.5)).
assert ((s_vector (0, 1)) = Mmult (eigenvector_matrix h) a).
-
apply mk_matrix_ext => i j Hi Hj.
admit.
-
assert (Mmult (eigenvector_matrix_inv h)
  (eigenvector_matrix h) = Mone) by admit.

assert (Mpow 2 n (t_matrix h) =
     Mmult (eigenvector_matrix h)
       (Mmult (Mpow 2 n (eigenvalue_matrix h)) (eigenvector_matrix_inv h))).
apply Matrix_pow.
admit.
admit.
admit.
symmetry.
apply t_matrix_diagonalizable.
unfold h; split; try nra. admit.
subst Mn.
rewrite H1 .
rewrite H.
rewrite <- Mmult_assoc.
replace ((Mmult
        (Mmult (Mpow 2 n (eigenvalue_matrix h))
           (eigenvector_matrix_inv h))
        (Mmult (eigenvector_matrix h) a)))
with (
Mmult (Mpow 2 n (eigenvalue_matrix h))
    (Mmult (Mmult (eigenvector_matrix_inv h) (eigenvector_matrix h)) a)).
rewrite H0.
rewrite Mmult_one_l.
assert (     Mpow 2 n (eigenvalue_matrix h) =
     mk_matrix 2 2
       (fun i j : nat =>
        if i =? j
        then Cpow (coeff_mat zero (eigenvalue_matrix h) i j) n
        else C0)).
apply diag_mat_pow. admit. admit.
rewrite H2.
rewrite Mmult_assoc.
eapply Rle_trans.
unfold vec_two_norm_2d, Rprod_norm.
unfold Mmult.
repeat rewrite coeff_mat_bij; try lia.
eapply sqrt_le_1_alt.
replace (Init.Nat.pred 2) with (S 0) by lia.
repeat rewrite sum_Sn.
repeat rewrite coeff_mat_bij; try lia.
repeat rewrite sum_O.
repeat rewrite coeff_mat_bij; try lia.
repeat rewrite sum_Sn.
repeat rewrite sum_O.
repeat rewrite coeff_mat_bij; try lia.
simpl.
repeat rewrite Rmult_1_r.
apply Rplus_le_compat_l.
apply Rmult_le_compat_l.
apply Cmod_ge_0.
apply Cmod_triangle.
unfold eigenvector_matrix, vec_two_norm_2d,
  Rprod_norm, eV_2, eV_1, eigenvalue_matrix, a.
repeat rewrite coeff_mat_bij; try lia.
simpl.
repeat rewrite Cmult_0_r.
repeat rewrite Cplus_0_l.
repeat rewrite Cplus_0_r.
repeat rewrite Rmult_1_r.
repeat rewrite Cmult_1_l.
change plus with Cplus.
change mult with Cmult.
repeat rewrite Cmod_mult.
repeat rewrite Cmod_RtoC; try nra.

assert (Cmod (Cpow (lambda_2 h) n) = 1) by admit.
assert (Cmod (Cpow (lambda_1 h) n) = 1) by admit.
rewrite H3; rewrite H4.
repeat rewrite Rmult_1_l.


eapply Rle_trans.
eapply sqrt_le_1_alt.
apply Rplus_le_compat_r.
apply Rmult_le_compat_l.
apply Cmod_ge_0.
apply Cmod_triangle.

eapply Rle_trans.
eapply sqrt_le_1_alt.
apply Rplus_le_compat_r.
apply Rmult_le_compat_r.
apply Rle_plus;
apply Cmod_ge_0.
apply Cmod_triangle.

repeat rewrite Cmod_mult.

repeat rewrite H3; repeat rewrite H4.
repeat rewrite Rmult_1_r.
repeat rewrite Cmod_RtoC; try nra.

eapply Rle_trans.
eapply sqrt_le_1_alt.
apply Rplus_le_compat_l.
apply Rmult_le_compat_r; try nra.
apply Cmod_triangle.
repeat rewrite Cmod_mult.

repeat rewrite H3; repeat rewrite H4.
repeat rewrite Rmult_1_l.
repeat rewrite Cmod_RtoC; try nra.
replace (0.5 + 0.5) with 1 by nra.
repeat rewrite Rmult_1_l.
unfold Cmod, C1, fst, snd.
rewrite pow_i.
repeat rewrite Rplus_0_l.
repeat rewrite Rplus_0_r.
rewrite pow1.
rewrite sqrt_1.
rewrite Rmult_1_l.
repeat rewrite sqrt_norm.
change norm with Rabs.
replace (Rabs (-0.5 * sqrt (4 - h * h)) * 0.5 + Rabs (0.5 * sqrt (4 - h * h)) * 0.5)
with
(0.5 * (Rabs (-0.5 * sqrt (4 - h * h)) + Rabs (0.5 * sqrt (4 - h * h)))) by nra.
replace (Rabs (-0.5 * sqrt (4 - h * h)))
with
(Rabs (0.5 * sqrt (4 - h * h))).
replace (0.5 *
   (Rabs (0.5 * sqrt (4 - h * h)) +
    Rabs (0.5 * sqrt (4 - h * h)))) with
   (Rabs (0.5 * sqrt (4 - h * h))) by nra.
apply Req_le.
field_simplify.
nra.
repeat rewrite Rabs_mult; f_equal.
rewrite <- Rabs_Ropp. f_equal; nra.
try lia.

repeat rewrite Mmult_assoc; auto.
Admitted.


Lemma n_steps_bounded :
  forall n : nat, 
  let Mn := Mpow 2 n (t_matrix  h) in
  vec_two_norm_2d  (Mmult Mn (s_vector (0, 1))) <= 1.415.
Proof.
intros.
eapply Rle_trans.
apply n_steps_bounded_aux.
eapply Rle_trans.
apply two_norm_eV.
interval.
Qed.


Close Scope R_scope. 