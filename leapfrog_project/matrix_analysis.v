(** matrix_analysis.v: stability analysis for leapfrog integration
  of a simple harmonic oscillator.
 Copyright (C) 2021-2022  Ariel Kellison.
*)

From Coq Require Import ZArith Reals Psatz.
From Coq Require Import Arith.Arith.
Require Import real_lemmas lf_harm_real matrix_lemmas.


From Coquelicot Require Import Coquelicot.
Require Import Interval.Tactic.

Import Bool.

Set Bullet Behavior "Strict Subproofs". 

Require Import Coq.Logic.FunctionalExtensionality.

(* define the transition matrix *)
Definition t_matrix (h: R) : @matrix C 2 2 := 
  let a := 0.5 * h^2 in 
  mk_matrix 2 2 (fun i j => if (Nat.eqb i j) then ((1 - a) , 0) else 
    if ( Nat.ltb j i)%nat then (h,0) else ((-0.5 * h * (2 - a)),0)) .

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
Search (Nat.eqb).
Definition eigenvalue_matrix (h : R) : @matrix C 2 2 :=
   mk_matrix 2 2 ( fun i j => if ((Nat.eqb i 0) && (Nat.eqb j 0) ) then lambda_1 h else
    if ( (Nat.eqb i 1) && (Nat.eqb j 1) ) then lambda_2 h else 0).


Definition eV_1 (h: R) : C * C := ((0 , -0.5 * sqrt(4 - h^2)) , C1).
Definition eV_2 (h: R) : C * C := ((0 ,  0.5 * sqrt(4 - h^2)) , C1).
Definition eigenvector_matrix (h : R) : @matrix C 2 2 :=
   mk_matrix 2 2 ( fun i j => if ( (Nat.eqb i 0) && (Nat.eqb j 0)) then fst (eV_1 h) else
    if ( (Nat.eqb i 0) && (Nat.eqb j 1)) then fst (eV_2 h) else 1).

(*
Definition lambda_1 (h : R) : R := (1 -0.5 * h^2 -  h * sqrt(h - 2) * 0.5 * sqrt(h + 2)). 
Definition lambda_2 (h : R) : R := (1 -0.5 * h^2 +  h * sqrt(h - 2) * 0.5 * sqrt(h + 2)).
Search (Nat.eqb).
Definition eigenvalue_matrix (h : R) : @matrix R 2 2 :=
   mk_matrix 2 2 ( fun i j => if ((Nat.eqb i 0) && (Nat.eqb j 0) ) then lambda_1 h else
    if ( (Nat.eqb i 1) && (Nat.eqb j 1) ) then lambda_2 h else 0).


Definition eV_1 (h: R) : R * R := (( -0.5 * sqrt(h^2 - 4)) , 1).
Definition eV_2 (h: R) : R * R := (( 0.5 * sqrt(h^2 - 4)) , 1).
Definition eigenvector_matrix (h : R) : @matrix R 2 2 :=
   mk_matrix 2 2 ( fun i j => if ( (Nat.eqb i 0) && (Nat.eqb j 0)) then fst (eV_1 h) else
    if ( (Nat.eqb i 0) && (Nat.eqb j 1)) then fst (eV_2 h) else 1).

*)
(*
Lemma eigenval_check_1 (h : R) :
  coeff_mat Hierarchy.zero (eigenvalue_matrix h) 0 0 = -h^2/2 - h*sqrt(h - 2)*sqrt(h + 2)/2 + 1.
Proof.
unfold eigenvalue_matrix. 
rewrite coeff_mat_bij; try lia. 
simpl; unfold lambda_1.
field_simplify.
nra.
Qed.

Lemma eigenval_check_2 (h : R) :
  coeff_mat Hierarchy.zero (eigenvalue_matrix h) 1 1 = -h^2/2 + h*sqrt(h - 2)*sqrt(h + 2)/2 + 1.
Proof.
unfold eigenvalue_matrix. 
rewrite coeff_mat_bij; try lia. 
simpl. unfold lambda_2.
field_simplify.
nra.
Qed.

Lemma eigenval_check_3 (h : R) :
  coeff_mat Hierarchy.zero (eigenvalue_matrix h) 1 0 = 0 /\
  coeff_mat Hierarchy.zero (eigenvalue_matrix h) 0 1 = 0.
Proof.
split.
unfold eigenvalue_matrix. 
rewrite coeff_mat_bij; try lia. 
simpl; nra. 
unfold eigenvalue_matrix. 
rewrite coeff_mat_bij; try lia. 
simpl; nra. 
Qed.



Lemma eigenvec_check_1 (h : R) :
  coeff_mat Hierarchy.zero (eigenvector_matrix h) 0 0 = -sqrt(h^2 - 4)/2.
Proof.
unfold eigenvector_matrix. 
rewrite coeff_mat_bij; try lia. 
simpl; unfold eV_1.
field_simplify.
nra.
Qed.

Lemma eigenvec_check_2 (h : R) :
  coeff_mat Hierarchy.zero (eigenvector_matrix h) 0 1 = sqrt(h^2 - 4)/2.
Proof.
unfold eigenvector_matrix. 
rewrite coeff_mat_bij; try lia. 
simpl; unfold eV_2.
field_simplify.
nra.
Qed.

Lemma eigenvec_check_3 (h : R) :
  coeff_mat Hierarchy.zero (eigenvector_matrix h) 1 1 = 1 /\
  coeff_mat Hierarchy.zero (eigenvector_matrix h) 1 0 = 1.
Proof.
split.
unfold eigenvector_matrix. 
rewrite coeff_mat_bij; try lia. 
simpl; nra.
unfold eigenvector_matrix. 
rewrite coeff_mat_bij; try lia. 
simpl; nra.
Qed.
*)

Lemma mult_aux1 (a b : R ) :
  @mult C_Ring (a , 0) (0 , b) = (0 , a * b).
Proof.
cbv. f_equal;
nra.
Qed.

Lemma mult_aux2 (a b c: R ) :
  @mult C_Ring (a , 0) (c , b) = (a * c , a * b).
Proof.
cbv. f_equal;
rewrite Rmult_0_l; nra.
Qed.

Lemma mult_aux3 (a b c: R ) :
  @mult C_Ring (0 , a) (b , c) = (-a * c , a * b).
Proof.
cbv. f_equal;
rewrite Rmult_0_l; nra.
Qed.


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
f_equal; try nra.
replace
(- h * sqrt (2 - h) * 0.5 * sqrt (h + 2))
with 
(- 0.5 * h * sqrt (2 - h) * sqrt (h + 2)) by nra.
rewrite Rmult_assoc.
rewrite Rmult_assoc.
rewrite <- sqrt_mult; try nra.
replace (- (-0.5 * sqrt (4 - h * h)) *
(-0.5 * h * sqrt ((2 - h) * (h + 2)))) with
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
rewrite <- sqrt_mult; try nra.
symmetry.
rewrite <- Rmult_assoc.
replace (- (0.5 * sqrt (4 - h * h)) * (0.5 * h) *
sqrt ((2 - h) * (h + 2)))
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
Definition MTM_eigenvalue_matrix (h : R) : @matrix C 2 2 :=
   mk_matrix 2 2 ( fun i j => if ((Nat.eqb i 0) && (Nat.eqb j 0) ) then MTM_lambda_1 h else
    if ( (Nat.eqb i 1) && (Nat.eqb j 1) ) then MTM_lambda_2 h else 0).

Definition MTM_eV_1 (h: R) : C * C := ((0.25 * (h^3 - 8*h + sqrt(h^6 + 64))/(h^2 - 2) ,0) , C1).
Definition MTM_eV_2 (h: R) : C * C := ((0.25 * (h^3 - 8*h - sqrt(h^6 + 64))/(h^2 - 2) ,0) , C1).
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


  
(* M * V = V * L *)
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

(* define P D such that P D invP *)
(* prove that P D invP = M for D and P *)



Close Scope R_scope. 