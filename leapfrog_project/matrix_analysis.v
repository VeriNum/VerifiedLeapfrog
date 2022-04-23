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



(** Largest singular value of a square matrix A ∈ Mn(C) *)
Definition max_sv_pred (n: nat ) (A : @matrix C n n) (σ : R):=  
  let ATA := Mmult (matrix_conj_transpose n n A) A (* the Gram matrix A'A *) in
  exists (V Λ : @matrix C n n),
         Mmult ATA V = Mmult V Λ
      /\ is_orthogonal_matrix n V
      /\ diag_pred n Λ   
      /\ (forall i, (i < n)%nat ->  (Cmod (@coeff_mat C n n Hierarchy.zero Λ i i )) <= σ ) (* σ is max in Λ *)
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
  /\ forall (s : R), vec_two_norm n (Mmult A u) <= s * vec_two_norm n u ->  σ <= s (* sqrt σ is inf *)
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
exists (Mmult (matrix_conj_transpose n n V) x). 
unfold is_orthogonal_matrix in H2; destruct H2 as (_ & H2).
rewrite Mmult_assoc.
rewrite H2.
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
Definition eV_1 (h: R) : C * C := ((0 , -0.5 * sqrt(4 - h^2)) , C1)
.
Definition eV_2 (h: R) : C * C := ((0 ,  0.5 * sqrt(4 - h^2)) , C1)
.
Definition eigenvector_matrix (h : R) : @matrix C 2 2 :=
   mk_matrix 2 2 ( fun i j => if ( (Nat.eqb i 0) && (Nat.eqb j 0)) then fst (eV_1 h) else
    if ( (Nat.eqb i 0) && (Nat.eqb j 1)) then fst (eV_2 h) else 1)
.
(** We define the Gram matrix MTM for the transition matrix. The eigenvalues of the matrix MTM are the 
    singular values of the transition matrix *)
Definition MTM (h : R) : @matrix C 2 2 :=
   mk_matrix 2 2 ( fun i j => if ( (Nat.eqb i 0) && (Nat.eqb j 0)) then (0.25 * h^4 + 1, 0) else
    if ( negb (Nat.eqb i j) ) then (0.125 * h^3*(2 - h^2),0) else 
    (0.0625 * h^6 - 0.25*h^4 + 1, 0))
.
(** The eigenvalues of MTM *)
Definition MTM_lambda_1 (h : R) : R := (1 + 0.03125 * h ^ 6 - 0.03125 * h^3 * sqrt(h^2 + 4) * sqrt(h^4 - 4 * h^2 + 16)) 
.
Definition MTM_lambda_2 (h : R) : R := (1 + 0.03125 * h ^ 6 + 0.03125 * h^3 * sqrt(h^2 + 4) * sqrt(h^4 - 4 * h^2 + 16)) 
.
Definition MTM_eigenvalue_vector (h : R) : @matrix R 2 1 :=
mk_matrix 2 1 ( fun i j => if ((Nat.eqb i j)) then MTM_lambda_1 h else MTM_lambda_2 h)
.
Definition MTM_eigenvalue_matrix (h : R) : @matrix C 2 2 :=
   mk_matrix 2 2 ( fun i j => if ((Nat.eqb i 0) && (Nat.eqb j 0) ) then RtoC (MTM_lambda_1 h) else
    if ( (Nat.eqb i 1) && (Nat.eqb j 1) ) then RtoC (MTM_lambda_2 h) else 0)
.

(** The eigenvectors of MTM, numbered to match their eigenvalues *)
Definition MTM_eV_1 (h: R) : C * C := ((0.25 * (h^3 - 8*h + sqrt(h^6 + 64))/(h^2 - 2) ,0) , C1)
.
Definition MTM_eV_2 (h: R) : C * C := ((0.25 * (h^3 - 8*h - sqrt(h^6 + 64))/(h^2 - 2) ,0) , C1)
.

Definition MTM_eV1 (h : R) : @matrix C 2 1 :=
  mk_matrix 2 1 ( fun i j => if ((Nat.eqb i j)) then fst (MTM_eV_1 h) else snd (MTM_eV_1 h))
.
Definition MTM_eV2 (h : R) : @matrix C 2 1 :=
  mk_matrix 2 1 ( fun i j => if ((Nat.eqb i j)) then fst (MTM_eV_2 h) else snd (MTM_eV_2 h))
.
(** we use MTM_eigenvector_matrix as the matrix V in e.g. M V = V L , where V is the diagonal matrix of eigenvalues
   and M is the transition matrix.*)
Definition MTM_eigenvector_matrix (h : R) : @matrix C 2 2 :=
   mk_matrix 2 2 ( fun i j => if ( (Nat.eqb i 0) && (Nat.eqb j 0)) then fst (MTM_eV_1 h) else
    if ( (Nat.eqb i 0) && (Nat.eqb j 1)) then fst (MTM_eV_2 h) else 1)
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


Lemma Cmod_RtoC (a : R): 
Cmod (RtoC a) = a.
Admitted.


(* if σ^2 is the largest singular value of A ∈ M(C^2) then σ is the two-norm of A *)
Theorem max_sv_pred_implies_two_norm_pred   (A : @matrix C 2 2) (σ : R):
  max_sv_pred 2 A (σ ^2) ->  two_norm_pred 2 A σ.
Proof.
intros.
unfold two_norm_pred. split.
- 
pose proof vectors_in_basis 2 u A as Hb.
unfold max_sv_pred in H.
destruct H as (V & Λ & H1 & H2 & H3 & H4).
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
(Mmult (Mmult (Mmult (matrix_conj_transpose 2 2 A) A) V) a).
rewrite H1.
replace (Mmult (matrix_conj_transpose 2 2 V) (Mmult (Mmult V Λ) a)) with
(Mmult (Mmult (matrix_conj_transpose 2 2 V) V) (Mmult Λ a)).
replace (Mmult (Mmult (matrix_conj_transpose 2 1 a) (matrix_conj_transpose 2 2 V)) (Mmult V a))
with 
(Mmult (matrix_conj_transpose 2 1 a) (Mmult (Mmult (matrix_conj_transpose 2 2 V) V) a)).
destruct H2 as (H2 & _).
rewrite H2.
repeat rewrite Mmult_one_l.
replace (Mmult Λ a)
with 
(mk_matrix 2 1 (fun i _ : nat =>
  mult (coeff_mat zero Λ i i) (coeff_mat zero a i 0))).
replace σ with (sqrt (σ^2)).
rewrite <- sqrt_mult; try nra; try apply Cmod_ge_0.
apply sqrt_le_1_alt.
replace (σ^2) with (Cmod (σ^2)).
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
assert ( forall i : nat, (i < 2)%nat ->
     (coeff_mat zero Λ i i) = RtoC (fst (coeff_mat zero Λ i i))) by admit.

assert ((1 < 2)%nat) by lia.
assert ((0 < 2)%nat) by lia.
pose proof (H 0%nat H5).
pose proof (H 1%nat H0).
rewrite H6.
rewrite H7.

repeat rewrite <- RtoC_mult.
repeat rewrite <- RtoC_plus.
repeat rewrite <- RtoC_mult.
repeat rewrite Cmod_R.

rewrite Rmult_comm.
apply Rabs_pos_le.
apply Rle_plus.
apply Rle_mult.
apply sqr_plus_pos.
admit. (*0 <= fst (coeff_mat zero Λ 1 1)*)
apply Rle_mult.
apply sqr_plus_pos.
admit.
apply Rle_mult.
apply square_pos.
admit. (*apply sqr_plus_pos.*)
match goal with |-context [σ ^ 2 * (?a + ?b)]=>
replace (σ ^ 2 * (a + b)) with
( σ ^ 2 * a +  σ ^ 2 * b) by nra
end.
rewrite Rplus_comm.
apply Rplus_le_compat.
*
rewrite Rmult_comm.
apply Rmult_le_compat_r.
apply sqr_plus_pos.
specialize (H4 0%nat H5); try lia.
eapply Rle_trans.
2: apply H4.
change ((@coeff_mat C 2 2 (@zero C_AbelianGroup) Λ 0 0))
with 
(@coeff_mat (AbelianGroup.sort C_AbelianGroup) 2 2 (@zero C_AbelianGroup) Λ 0 0).
rewrite H6 at 2; rewrite Cmod_R.
apply Rle_abs.
*
rewrite Rmult_comm.
apply Rmult_le_compat_r.
apply sqr_plus_pos.
specialize (H4 1%nat H0); try lia.
eapply Rle_trans.
2: apply H4.
change ((@coeff_mat C 2 2 (@zero C_AbelianGroup) Λ 1 1))
with 
(@coeff_mat (AbelianGroup.sort C_AbelianGroup) 2 2 (@zero C_AbelianGroup) Λ 1 1).
rewrite H7 at 2; rewrite Cmod_R.
apply Rle_abs.
*
rewrite Cmod_R.
apply Rabs_pos_eq; nra.
*
rewrite sqrt_pow2; try nra.
admit (*0 <= σ*).
*
unfold Mmult.
apply mk_matrix_ext; intros.
assert (j = 0)%nat by lia; subst.
assert ( (i = 0)%nat \/ (i <> 0)%nat) by lia; destruct H5.
--
replace (Init.Nat.pred 2) with (S 0) by lia.
rewrite sum_Sn.
rewrite sum_O.
unfold diag_pred in H3.
subst.
specialize (H3 0%nat 1%nat).
Admitted.



Lemma two_norm_pred_eq (h : R | 0 < h < sqrt 2): 
 two_norm_pred 2 (t_matrix (proj1_sig h)) (sqrt (MTM_lambda_2 (proj1_sig h))).
Proof.
apply ( max_sv_pred_implies_two_norm_pred
  (t_matrix (proj1_sig h)) (sqrt (MTM_lambda_2 (proj1_sig h)))).
unfold max_sv_pred.
destruct h as (h & Hh).
exists (MTM_eigenvector_matrix h), (MTM_eigenvalue_matrix h).
simpl.
repeat split.
-
rewrite MTM_aux.
assert (0 < h ^ 2 < 2) by admit.
apply (MTM_eigens_correct h H).
-
admit.
-
admit.
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
rewrite <- sqrt_mult_alt.
apply sqrt_le_1_alt.
assert (Hi: (i = 1)%nat \/ (i = 0)%nat) by lia; destruct Hi.
+ 
subst.
unfold MTM_eigenvalue_matrix; simpl; nra.
+ 
subst.
unfold MTM_eigenvalue_matrix; simpl.
rewrite Rmult_0_l.
rewrite Rplus_0_r.
rewrite Rmult_1_r.
apply Rmult_le_compat.
admit. (* 0 <= MTM_lambda_2 h *)
admit. (* 0 <= MTM_lambda_2 h *)
admit (*MTM_lambda_1 h <= MTM_lambda_2 h*).
admit (*MTM_lambda_1 h <= MTM_lambda_2 h*).
+
admit. (* 0 <= MTM_lambda_2 h *)
Admitted.

Definition two_norm_t_matrix (h : R | 0 < h < sqrt 2):=
  proj1_sig (exist (two_norm_pred 2 (t_matrix (proj1_sig h))) (sqrt (MTM_lambda_2 (proj1_sig h))) (two_norm_pred_eq h))
.


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






Lemma MTM_eV_2_sep_0 (h  : R) : 
  MTM_eV_2 h <> (C0,C0).
Proof.
unfold MTM_eV_2.
match goal with |- context [?a <> _] =>
set (aa:=a)
end.
cbv -[aa]; intros.
subst aa.
apply pair_equal_spec in H.
destruct H.
unfold C1 in H0.
apply pair_equal_spec in H0.
destruct H0. 
pose proof R1_neq_R0.
try contradiction.
Qed.



Lemma pair_nequal_spec:
  forall (a1 a2 : C) (b1 b2 : C),
  (a1, b1) <> (a2, b2) <-> a1 <> a2 \/ b1 <> b2.
Proof.
split; intros.
-
pose proof Ceq_dec a1 a2; destruct H0; subst.
right.
cbv in H; cbv; intros; subst; auto.
left; auto.
-
cbv in H.
cbv; intros.
apply pair_equal_spec in H0.
destruct H; destruct H0; auto.
Qed.



Lemma two_norm_t_matrix_eq :
sqrt (Cmod (MTM_lambda_2 h)) <= 4503616807272450 / 4503599627370496
(* <= 1.000003814704542 *).
Proof.
unfold MTM_lambda_2, RtoC, Cmod, fst, snd, h.
match goal with |-context [sqrt (sqrt ?a) <= ?b] =>
  field_simplify a
end.
match goal with |-context [sqrt (sqrt ?a) <= _] =>
interval_intro (sqrt (sqrt a)) upper
end.
apply H.
Qed.

Lemma t_matrix_norm_sub_mult :
  forall (h : R | 0 < h < sqrt 2),
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
  forall h : {h : R | 0 <  h < sqrt 2},
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
  (t_matrix (@proj1_sig R (fun h1 : R => 0 < h1 < sqrt 2) h))) (t_matrix (@proj1_sig R (fun h1 : R => 0 < h1 < sqrt 2) h))) (s_vector (p, q)))
with
( Mmult (t_matrix (@proj1_sig R (fun h1 : R => 0 < h1 < sqrt 2) h)) 
  (Mmult (Mpow 2 n (t_matrix (@proj1_sig R (fun h1 : R => 0 < h1 < sqrt 2) h))) (s_vector (p, q)))).
destruct (@Mmult C_Ring 2 2 1 (Mpow 2 n (t_matrix (@proj1_sig R (fun h1 : R => 0 < h1 < sqrt 2) h))) (s_vector (p, q))).
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
rewrite Cmod_RtoC.
apply Req_le.
rewrite Rmult_assoc; auto.
rewrite Mmult_assoc.
rewrite Mpow_comm; auto.
Qed.


Lemma h_bnd_lem :
0 <  h < sqrt 2.
Proof.
split; unfold h; unfold ω; try nra.
interval.
Qed.


Theorem matrix_analysis_method_bound_fixed_h_n : 
  forall p q: R,
  forall n : nat, 
  let j := (exist (fun x => 0 < x < sqrt 2) h) h_bnd_lem in
  let Mn := Mpow 2 n (t_matrix  h ) in
  vec_two_norm_2d  (Mmult Mn (s_vector (p, q))) <= 
      (4503616807272450 / 4503599627370496) ^ n * vec_two_norm_2d (s_vector (p,q)).
Proof.
intros.
pose proof h_bnd_lem as Hbnd.
pose proof matrix_analysis_method_bound_n p q n j.
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