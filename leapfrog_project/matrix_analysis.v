(** matrix_analysis.v: stability analysis for leapfrog integration
  of a simple harmonic oscillator.
 Copyright (C) 2021-2022  Ariel Eileen Kellison.
*)

From Coq Require Import ZArith Reals Psatz.
From Coq Require Import Bool Arith.Arith.
Require Import real_lemmas real_model matrix_lemmas.

From Coquelicot Require Import Coquelicot.
Require Import IntervalFlocq3.Tactic.

Import Bool.

Set Bullet Behavior "Strict Subproofs". 

Require Import Coq.Logic.FunctionalExtensionality.



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

Definition basis_pred (n: nat ) (A : @matrix C n n) (u : @matrix C n 1):= 
  let ATA := Mmult (matrix_conj_transpose n n A) A in (* the Gram matrix A'A *)
  forall (V Λ : @matrix C n n),
         Mmult ATA V = Mmult V Λ
      /\  is_orthogonal_matrix n V
      /\ diag_pred n Λ ->
  exists (a: @matrix C n 1),  u = Mmult V a
.

Definition two_norm_pred (n: nat ) (A : @matrix C n n) (σ : R):=  
  forall (u : @matrix C n 1), 
  vec_two_norm n (Mmult A u) <=  σ * vec_two_norm n u 
  /\ ~(exists (s : R), forall (x : matrix n 1), 
      vec_two_norm n (Mmult A x) <= s * vec_two_norm n x < σ * vec_two_norm n x) (* σ is inf *)
.

(** Any vector can be written as the sum of the eigenvectors
  of a Hermitian matrix. We need this in order to satisfy the 
  two norm predicate. **)
Theorem vectors_in_basis (n : nat) : 
 forall (x : @matrix C n 1), 
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
Definition M (h: R) : @matrix C 2 2 := 
  let a := 0.5 * h^2 in 
  mk_matrix 2 2 (fun i j => if (Nat.eqb i j) then ((1 - a) , 0) else 
    if Nat.ltb j i then (h,0) else ((-0.5 * h * (2 - a)),0)) .

(** ideal solution vector *)
Definition pq_vector (h: R) (p q : R -> R) (t : R) : @matrix C 2 1 := 
  mk_matrix 2 1 (fun i j => if (Nat.eqb i j) then (p t , 0) else (q t , 0)) .

(** arbitrary solution vector *)
Definition s_vector (ic: R * R) := @mk_matrix C 2 1
  (fun i j => if (Nat.eqb i j) then ((fst ic),0) else ((snd ic),0)).

(** equivalence between matrix update and leapfrog step*)
Lemma transition_matrix_equiv_1:
  forall (ic : R * R) (h : R),  
  let Mx := Mmult (M h) (s_vector ic) in
   coeff_mat Hierarchy.zero Mx 0 0 = (fst (leapfrog_stepR h ic),0).
Proof.
intros. subst Mx. destruct ic. cbv. 
all : (f_equal; field_simplify; nra) .
Qed.

(** equivalence between matrix update and leapfrog step*)
Lemma transition_matrix_equiv_2:
  forall (ic : R * R) (h : R), 
  let Mx := Mmult (M h) (s_vector ic) in
coeff_mat Hierarchy.zero Mx 1 0 = (snd (leapfrog_stepR h ic),0).
Proof.
intros. subst Mx. destruct ic. cbv.
all : (f_equal; field_simplify; nra) .
Qed.


Lemma transition_matrix_equiv_iternR_aux:
  forall (h : R) (n : nat) i j, 
snd (coeff_mat zero (Mpow 2 n (M h)) i j) = 0.
Proof.
induction n; destruct i as [|[|]], j as [|[|]];
try reflexivity;
simpl; rewrite ?IHn; nra.
Qed.

(** equivalence between matrix update and leapfrog step*)
Lemma transition_matrix_equiv_iternR:
  forall (ic : R * R) (h : R) (n : nat), 
  (fst (coeff_mat Hierarchy.zero (Mmult (Mpow 2 n (M h)) (s_vector ic)) 0 0), 
    fst (coeff_mat Hierarchy.zero (Mmult (Mpow 2 n (M h)) (s_vector ic)) 1 0)) = iternR ic h n.
Proof.
intros.
induction n.
- 
destruct ic; simpl; f_equal; nra.
-
pose (m_iternR := mk_matrix 2 1 (fun i _ => if Nat.eqb i 0 then RtoC (fst (iternR ic h n)) 
  else RtoC (snd (iternR ic h n)) )).

assert ((Mmult (Mpow 2 (S n) (M h)) (s_vector ic)) = Mmult (M h) m_iternR). 
+ 
subst m_iternR.
unfold Mpow; fold Mpow.
symmetry. 
rewrite <- Mpow_comm.
rewrite <- Mmult_assoc.
rewrite <- IHn; clear IHn.
simpl.
rewrite ?Rmult_0_r, ?Rplus_0_r, ?Rminus_0_r.
f_equal.
apply mk_matrix_ext => i j Hi Hj.
simpl.
rewrite ?sum_Sn, ?sum_O.
destruct i as [|[|]], j; try lia;
 simpl; symmetry;
unfold s_vector; simpl;
repeat rewrite coeff_mat_bij by lia; simpl;
change plus with Cplus; 
change mult with Cmult;
unfold Cmult, Cplus; simpl;
rewrite ?transition_matrix_equiv_iternR_aux;
rewrite ?Rmult_0_l, ?Rmult_0_r,  ?Rplus_0_l, ?Rplus_0_r, ?Rminus_0_r;
auto.
+
clear IHn.
rewrite H; clear H.
rewrite step_iternR, surjective_pairing.
assert (m_iternR = (s_vector (iternR ic h n))). {
  unfold m_iternR, s_vector.
  apply mk_matrix_ext => i j Hi Hj.
  destruct i as [|[|]], j; try lia; auto.
}
rewrite H.
rewrite transition_matrix_equiv_2.
rewrite transition_matrix_equiv_1.
reflexivity.
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
let a:= sqrt(h^6 + 64) in
let A:= (h^10 - h^7*a + 4*h^6 + 64*h^4 - 4*h^3*a - 32*h*a + 256) * (h^2 -2)^2 in
let b:= (h^3 - 8*h + a)^2 in 
A / (2*(h^4  - 4*h^2 + 4) * (b + 16 * (h^2 - 2)^2))
.

Definition MTM_lambda_2 (h : R) : R := 
let a:= sqrt(h^6 + 64) in
let A:= (h^10 + h^7*a + 4*h^6 + 64*h^4 + 4*h^3*a + 32*h*a + 256) * (h^2 -2)^2 in
let b:= (-h^3 + 8*h + a)^2 in 
A / (2*(h^4  - 4*h^2 + 4) * (b + 16 * (h^2 - 2)^2))
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
  Mmult (M h) (eigenvector_matrix h) = 
  Mmult (eigenvector_matrix h) (eigenvalue_matrix h).
Proof.
intros.
apply mk_matrix_ext => i j Hi Hj.
replace (Init.Nat.pred 2) with (S 0) by lia.
repeat rewrite sum_Sn.
repeat rewrite sum_O.
unfold M, eigenvector_matrix, eigenvalue_matrix, 
  eV_1, eV_2, lambda_1, lambda_2, matrix_lemmas.C1.
repeat rewrite coeff_mat_bij.
all: try lia.
assert (sqrt (2-h) * sqrt (h+2) = sqrt (4-h*h))
  by (rewrite <- sqrt_mult by lra; f_equal; lra).
pose proof (sqrt_def (4-h*h) ltac:(nra)).
destruct i as [|[|]], j as [|[|]]; try lia;
unfold mult, plus; simpl;
rewrite ?mult_aux1, ?mult_aux2, ?mult_aux3;
rewrite ?Cmult_0_r, ?Cplus_0_r;
unfold Cplus; simpl;
rewrite ?Rmult_0_l, ?Rmult_0_r, ?Rmult_1_r, ?Rplus_0_l, ?Rplus_0_r, ?Rminus_0_l;
rewrite <- H0 in *;
f_equal; nra.
Qed.

Lemma MTM_aux  (h : R) :
  Mmult (matrix_conj_transpose _ _ (M h)) (M h) = MTM h.
Proof.
unfold MTM.
apply mk_matrix_ext => i j Hi Hj.
replace (Init.Nat.pred 2) with (S 0) by lia.
repeat rewrite sum_Sn.
repeat rewrite sum_O.
unfold M, matrix_conj_transpose, Cconj.
repeat rewrite coeff_mat_bij by lia.
destruct i as [|[|]], j as [|[|]]; try lia;
simpl;
unfold plus, mult; simpl;
cbv [Cmult Cplus]; simpl;
f_equal; nra.
Qed.

Lemma div_eq_0 : 
forall a b , b <> 0 -> a = 0 -> a / b = 0.
Proof.
intros.
subst.
field.
auto.
Qed.

(* MTM * V = V * L *)
Theorem MTM_eigens_correct (h : R) :
  0 < h  < 1.41 -> 
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
apply div_eq_0.
set (x := sqrt _).
set (y := sqrt _).
interval with ( i_bisect h, i_taylor h, i_degree 7).
set (x := sqrt _). nra.
set (x := sqrt _).
set (y := sqrt _).
interval with ( i_bisect h, i_taylor h, i_degree 3).
all: try repeat split; try interval with ( i_bisect h, i_taylor h, i_degree 3).
f_equal; nra.
+ (* case i = 0 , j = 1 *)
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
unfold MTM_lambda_1, MTM_lambda_2.
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
apply div_eq_0.
set (x := sqrt _).
set (y := sqrt _).
interval with ( i_bisect h, i_taylor h, i_degree 3).
set (x := sqrt _). nra.
set (x := sqrt _).
set (y := sqrt _).
interval with ( i_bisect h, i_taylor h, i_degree 3).
all: try repeat split; try interval with ( i_bisect h, i_taylor h, i_degree 3).
f_equal; nra.
- 
assert (B: j = 0%nat \/ j = 1%nat) by lia;
destruct B. 
+ (* case i = 1 , j = 0 *)
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
unfold MTM_lambda_1, MTM_lambda_2.
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
apply div_eq_0.
set (x := sqrt _).
set (y := sqrt _).
interval with ( i_bisect h, i_taylor h, i_degree 3).
set (x := sqrt _). nra.
set (x := sqrt _).
set (y := sqrt _).
interval with ( i_bisect h, i_taylor h, i_degree 3).
all: try repeat split; try interval with ( i_bisect h, i_taylor h, i_degree 3).
f_equal; nra.
+ (* case i = 1 , j = 1 *)
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
unfold MTM_lambda_1, MTM_lambda_2.
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
apply div_eq_0.
set (x := sqrt _).
set (y := sqrt _).
interval with ( i_bisect h, i_taylor h, i_degree 3).
set (x := sqrt _). nra.
set (x := sqrt _).
set (y := sqrt _).
interval with ( i_bisect h, i_taylor h, i_degree 3).
all: try repeat split; try interval with ( i_bisect h, i_taylor h, i_degree 3).
f_equal; nra.
Qed.




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
  forall (k :nat), (k < 2)%nat ->
  let x := mk_matrix 2 1
  (fun i0 _ : nat =>
     (coeff_mat zero V i0 k)) in
  (Mmult (matrix_conj_transpose 2 1 x) (Mmult (Mmult (matrix_conj_transpose 2 2 A) A) x)) =
  (Mmult (matrix_conj_transpose 2 1 x) (mat_coeff_mult (coeff_mat zero Λ k k) 2 1 x)).
Proof.
intros.
unfold Mmult at 1 3 in H1.
rewrite <- mk_matrix_ext in H1.
apply mk_matrix_ext; intros.
apply sum_n_ext_loc => m Hm.
assert (i = 0)%nat by lia; subst i.
assert (j = 0)%nat by lia; subst j.
subst x.
red in H0.
change (@zero C_AbelianGroup) with (@zero C_Ring) in *.
unfold Mmult at 1. 
rewrite coeff_mat_bij by lia.
simpl.
f_equal.
etransitivity; [apply H1; lia | simpl ].
unfold mat_coeff_mult.
rewrite !coeff_mat_bij by lia.
rewrite !sum_Sn, !sum_O.
destruct m as [|[|]]; try lia;
destruct k as [|[|]]; try lia;
match goal with |- context [coeff_mat _ Λ ?x ?y] =>  rewrite (H0 x y) by lia end;
rewrite ?mult_zero_l, ?mult_zero_r, ?plus_zero_l, ?plus_zero_r;
apply Cmult_comm.
Qed.

(* if σ^2 is the largest singular value of A ∈ M(C^2) then σ is the two-norm of A *)
Theorem max_sv_pred_implies_two_norm_pred   (A : @matrix C 2 2) (σ : R):
  max_sv_pred 2 A σ  ->  two_norm_pred 2 A σ.
Proof.
intros.
unfold two_norm_pred. split.
- 
pose proof vectors_in_basis 2 u A as Hb.
destruct H as ( H0 & V & Λ & H1 & H2 & H3 & H4 & H5 & H6).
assert (exists a : matrix 2 1, u = Mmult V a)
  by (apply  (Hb V Λ); repeat (split; auto)).
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
rewrite !Mmult_one_l.
replace (Mmult Λ a)
with 
(mk_matrix 2 1 (fun i _ : nat =>
  mult (coeff_mat zero Λ i i) (coeff_mat zero a i 0))).
{
replace σ with (sqrt (σ^2)) by (apply sqrt_pow2; auto).
rewrite <- sqrt_mult by (try nra; apply Cmod_ge_0).
apply sqrt_le_1_alt.
replace (σ^2) with (Cmod (σ^2)) by (apply Cmod_RtoC; try nra).
rewrite <- Cmod_mult.
unfold Mmult.
rewrite !coeff_mat_bij; try lia.
replace (Init.Nat.pred 2) with (S 0) by lia.
rewrite !sum_Sn.
rewrite !coeff_mat_bij; try lia.
rewrite !sum_O.
rewrite !coeff_mat_bij; try lia.
change plus with Cplus.
change mult with Cmult.
unfold matrix_conj_transpose.
rewrite !coeff_mat_bij; try lia.
rewrite Cmult_comm.
rewrite <- Cmult_assoc.
rewrite C_sqr_ccong.
rewrite Cmult_comm.
rewrite Cplus_comm.
rewrite Cmult_comm.
rewrite <- Cmult_assoc.
rewrite C_sqr_ccong.
rewrite !C_sqr_ccong2.

pose proof (H6 0%nat ltac:(lia)) as (HL1 & HL2 & HL3).
pose proof (H6 1%nat ltac:(lia)) as (HL4 & HL5 & HL6).
rewrite HL1. 
rewrite HL4.

rewrite <- !RtoC_mult.
rewrite <- !RtoC_plus.
rewrite <- !RtoC_mult.
rewrite !Cmod_R.

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
}
apply mk_matrix_ext; intros.
assert (Hj: (j = 0)%nat) by lia; subst.
change (Init.Nat.pred 2) with (S 0).
red in H3.
destruct i as [|[|]]; [ | | lia].
--
rewrite sum_Sn, sum_O.
specialize (H3 0%nat 1%nat ltac:(lia)).

change ((@coeff_mat (AbelianGroup.sort (Ring.AbelianGroup C_Ring)) 2 2
        (@zero (Ring.AbelianGroup C_Ring)) Λ 0 1))
with 
(@coeff_mat C 2 2 (@zero C_AbelianGroup) Λ 0 1).
rewrite H3.
rewrite ?@mult_zero_l, ?@mult_zero_r, ?@plus_zero_l, ?@plus_zero_r.
auto.
--
rewrite sum_Sn, sum_O.
specialize (H3 1%nat 0%nat ltac:(lia)).
change (@zero C_AbelianGroup) with (@zero C_Ring) in *.
change (@coeff_mat _ 2 2  (@zero C_Ring) Λ 1 0)
with (@coeff_mat C 2 2 (@zero C_Ring) Λ 1 0).
simpl.
rewrite H3.
rewrite ?@mult_zero_l, ?@mult_zero_r, ?@plus_zero_l, ?@plus_zero_r.
auto.
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
 0 < h < 1.41-> 
0 <= (MTM_lambda_2 h).
Proof.
intros.
unfold MTM_lambda_2.
interval with ( i_bisect h, i_taylor h, i_degree 3).
Qed.


Lemma MTM_lambda_1_pos_2 (h : R) :
 0 < h < 1.41 -> 
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
  0 < h < 1.41 -> 
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
try apply Rdiv_le2; try
interval with ( i_bisect h, i_taylor h, i_degree 3).
apply Rminus_le.
field_simplify.
set (x := sqrt _).
replace (-16 * h ^ 21 * x + 192 * h ^ 19 * x - 960 * h ^ 17 * x + 1536 * h ^ 15 * x + 8448 * h ^ 13 * x -
58368 * h ^ 11 * x + 162816 * h ^ 9 * x - 245760 * h ^ 7 * x + 196608 * h ^ 5 * x -
65536 * h ^ 3 * x) with
((-16 * h ^ 18 + 192 * h ^ 16 - 960 * h ^ 14 + 1536 * h ^ 12 + 8448 * h ^ 10 -
58368 * h ^ 8 + 162816 * h ^ 6 - 245760 * h ^ 4 + 196608 * h ^ 2 -
65536) * x * h^3) by nra.
try apply Rmult_le_0_r; try nra.
try apply Rmult_le_0_r; try apply sqrt_pos.
try interval
 with ( i_bisect h, i_depth 10, i_taylor h, i_degree 7, i_prec 64).
Qed.

Lemma div_eq_1 : 
 (forall a b : R, a = b -> b <> 0 -> a / b = 1).
Proof.
intros; subst. field; auto. Qed.

Lemma MTM_eigenvectors_orthogonal_1 (h: R):
  0 < h < 1.41 -> 
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
 with ( i_bisect h, i_depth 10, i_taylor h, i_degree 7).
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
repeat rewrite Rmult_assoc.
match goal with |-context[h ^ 4 * ?a] =>
set (y:= a )
end.
replace (h ^ 4 * y - 4 * (h ^ 2 * y) + 4 * y) with
((h ^ 4 - 4 * h ^ 2  + 4 ) *y) by nra.
apply Rmult_integral_contrapositive_currified.
interval
 with ( i_bisect h, i_depth 10, i_taylor h, i_degree 7).
subst y.
interval
 with ( i_bisect h, i_depth 10, i_taylor h, i_degree 7).
interval
 with ( i_bisect h, i_depth 10, i_taylor h, i_degree 7).
repeat split; try
interval
 with ( i_bisect h, i_depth 10, i_taylor h, i_degree 7).
repeat split; try
interval
 with ( i_bisect h, i_depth 10, i_taylor h, i_degree 7).
-
assert (i = 0)%nat by lia; subst.
repeat rewrite sum_Sn.
repeat rewrite sum_O.
repeat rewrite coeff_mat_bij; try lia.
simpl.
unfold Cconj,RtoC, MTM_eV_1, MTM_eV_2; simpl.
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
apply H1.
repeat rewrite Rmult_assoc.
match goal with |-context[h ^ 4 * ?a] =>
set (y:= a )
end.
replace (h ^ 4 * y - 4 * (h ^ 2 * y) + 4 * y) with
((h ^ 4 - 4 * h ^ 2  + 4 ) *y) by nra.
apply Rmult_integral_contrapositive_currified.
interval
 with ( i_bisect h, i_depth 7, i_taylor h, i_degree 3).
subst y.
rewrite <- sqrt_mult.
interval
 with ( i_bisect h, i_depth 10, i_taylor h, i_degree 7).
interval
 with ( i_bisect h, i_depth 10, i_taylor h, i_degree 7).
interval
 with ( i_bisect h, i_depth 10, i_taylor h, i_degree 7).
interval
 with ( i_bisect h, i_depth 7, i_taylor h, i_degree 3).
repeat split; try 
interval
 with ( i_bisect h, i_depth 10, i_taylor h, i_degree 7).
repeat split; try
interval
 with ( i_bisect h, i_depth 10, i_taylor h, i_degree 7).
-
assert (i = 0)%nat by lia; subst.
assert (j = 0)%nat by lia; subst.
repeat rewrite sum_Sn.
repeat rewrite sum_O.
repeat rewrite coeff_mat_bij; try lia.
simpl.
unfold Cconj,RtoC, MTM_eV_1; simpl.
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
 with ( i_bisect h, i_depth 10, i_taylor h, i_degree 7).
repeat split. 
all: (try repeat split; try interval
 with ( i_bisect h, i_depth 10, i_taylor h, i_degree 7)).
Qed.


Lemma MTM_eigenvectors_orthogonal_2 (h: R):
  0 < h < 1.41 -> 
Mmult (MTM_eigenvector_matrix h) 
(matrix_conj_transpose 2 2 (MTM_eigenvector_matrix h)) = Mone.
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
unfold Cconj,RtoC, MTM_eV_1, MTM_eV_2; simpl.
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
repeat rewrite pow2_sqrt; try nra.
match goal with |-context[sqrt ?a ^ 4] =>
  replace (sqrt a ^ 4) with
 (sqrt a ^ 2 * sqrt a ^ 2) by nra
end.
repeat rewrite pow2_sqrt; try nra.
repeat rewrite pow2_sqrt; try nra.
all: (try repeat split; try interval
 with ( i_bisect h, i_depth 10, i_taylor h, i_degree 7)).
-
assert (j = 0)%nat by lia; subst.
repeat rewrite sum_Sn.
repeat rewrite sum_O.
repeat rewrite coeff_mat_bij; try lia.
simpl.
unfold Cconj,RtoC, MTM_eV_1, MTM_eV_2; simpl.
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
assert ( forall a b, b = 0 -> a<>0 -> b/a = 0) by (intros;nra).
apply H0; try interval
 with ( i_bisect h, i_depth 10, i_taylor h, i_degree 7).
all: (try interval
 with ( i_bisect h, i_depth 10, i_taylor h, i_degree 7)).
repeat rewrite pow2_abs; field_simplify; try nra.
apply H0; try interval
 with ( i_bisect h, i_depth 10, i_taylor h, i_degree 7).
repeat rewrite pow2_sqrt; field_simplify; try nra.
repeat rewrite pow2_abs.
all: (try split; try apply sep_0_div; 
(try interval
 with ( i_bisect h, i_depth 10, i_taylor h, i_degree 7))).
all: (try split; try apply sep_0_div; 
(try interval
 with ( i_bisect h, i_depth 10, i_taylor h, i_degree 7))).
-
assert (i = 0)%nat by lia; subst.
repeat rewrite sum_Sn.
repeat rewrite sum_O.
repeat rewrite coeff_mat_bij; try lia.
simpl.
unfold Cconj,RtoC, MTM_eV_1, MTM_eV_2; simpl.
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
assert ( forall a b, b = 0 -> a<>0 -> b/a = 0) by (intros;nra).
apply H1.
repeat rewrite Rmult_assoc.
repeat rewrite pow2_abs; field_simplify; try nra.
apply H1; try interval
 with ( i_bisect h, i_depth 10, i_taylor h, i_degree 7).
repeat rewrite pow2_sqrt; try nra.
repeat rewrite pow2_abs. 
match goal with |-context[ ?a <> 0] =>
field_simplify a;try nra;
repeat rewrite pow2_sqrt; try nra
end.
match goal with |-context[sqrt ?a ^ 4 ] =>
replace (sqrt a ^ 4) with
(sqrt a ^ 2 * sqrt a ^ 2) by nra;
repeat rewrite pow2_sqrt; try nra
end.
match goal with |-context[ ?a <> 0] =>
field_simplify a;try nra;
repeat rewrite pow2_sqrt; try nra
end; try interval
 with ( i_bisect h, i_depth 7, i_taylor h, i_degree 3).
apply sep_0_div; try split;
interval
 with ( i_bisect h, i_depth 10, i_taylor h, i_degree 7).
all : try repeat split; try
interval
 with ( i_bisect h, i_depth 10, i_taylor h, i_degree 7).
-
assert (i = 0)%nat by lia; subst.
assert (j = 0)%nat by lia; subst.
repeat rewrite sum_Sn.
repeat rewrite sum_O.
repeat rewrite coeff_mat_bij; try lia.
simpl.
unfold Cconj,RtoC, MTM_eV_1, MTM_eV_2; simpl.
change mult with Cmult.
change plus with Cplus.
change one with C1.
repeat rewrite coeff_mat_bij; try lia.
simpl.
cbv [Cplus Cmult RtoC C1 fst snd].
f_equal; field_simplify; try nra.
repeat rewrite pow2_sqrt.
field_simplify.
all : try repeat split; try
interval
 with ( i_bisect h, i_depth 7, i_taylor h, i_degree 3).
repeat rewrite pow2_abs. 
field_simplify.
apply div_eq_1.
repeat rewrite pow2_sqrt; try nra;
match goal with |-context[sqrt ?a ^ 4 ] =>
replace (sqrt a ^ 4) with
(sqrt a ^ 2 * sqrt a ^ 2) by nra;
repeat rewrite pow2_sqrt; try nra
end.
repeat rewrite pow2_sqrt; try nra.
match goal with |-context[ ?a <> 0] =>
field_simplify a;try nra;
repeat rewrite pow2_sqrt; try nra
end.
match goal with |-context[sqrt ?a ^ 4 ] =>
replace (sqrt a ^ 4) with
(sqrt a ^ 2 * sqrt a ^ 2) by nra;
repeat rewrite pow2_sqrt; try nra
end.
all: (try repeat split; try interval
 with ( i_bisect h, i_depth 10, i_taylor h, i_degree 7)).
Qed.

Lemma two_norm_pred_eq (h : R | 0 < h < 1.41): 
 two_norm_pred 2 (M (proj1_sig h)) (sqrt (MTM_lambda_2 (proj1_sig h))).
Proof.
apply ( max_sv_pred_implies_two_norm_pred
  (M (proj1_sig h)) (sqrt (MTM_lambda_2 (proj1_sig h)))).
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

Definition σ (h: R) := sqrt (MTM_lambda_2 h).

Definition two_norm_M (h : R | 0 < h < 1.41):=
  proj1_sig (exist (two_norm_pred 2 (M (proj1_sig h))) 
                          (sqrt (MTM_lambda_2 (proj1_sig h)))
                          (two_norm_pred_eq h)).

Lemma sigma_eq_two_norm_M:
  forall h, σ (proj1_sig h) = two_norm_M h.
Proof.
intros.
unfold two_norm_M.
destruct h; simpl.
reflexivity.
Qed.

(* 1.000003814704542914881812976091168820858001708984375 *)

Definition σb := 1.000003814704543.

Lemma sigma_bound: σ h <= σb.
Proof.
unfold σ, σb, MTM_lambda_2, h.
match goal with |- sqrt ?a <= _ => field_simplify a end.
match goal with |- ?a <= _ => interval_intro a upper end.
eapply Rle_trans.
apply H. nra.
interval.
Qed.

Lemma M_norm_sub_mult :
  forall (h : R | 0 < h < 1.41),
  forall (y : @matrix C 2 1%nat),
  vec_two_norm_2d (Mmult (M (proj1_sig h)) y) <= (two_norm_M h) * vec_two_norm_2d y.
Proof.
intros.
pose proof two_norm_pred_eq h.
unfold two_norm_pred in H.
specialize (H y).
destruct H as (H1 & H2).
unfold two_norm_M. simpl.
repeat rewrite <- two_norms_eq_2d.
apply H1.
Qed.

Lemma matrix_analysis_method_bound_n : 
  forall p q : R,
  forall n : nat, 
  forall h : {h : R | 0 <  h < 1.41},
  let Mn := Mpow 2 n (M (proj1_sig h)) in
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
  (M (@proj1_sig R (fun h1 : R => 0 < h1 < 1.41) h))) (M (@proj1_sig R (fun h1 : R => 0 < h1 < 1.41) h))) (s_vector (p, q)))
with
( Mmult (M (@proj1_sig R (fun h1 : R => 0 < h1 < 1.41) h)) 
  (Mmult (Mpow 2 n (M (@proj1_sig R (fun h1 : R => 0 < h1 < 1.41) h))) (s_vector (p, q)))).
destruct (@Mmult C_Ring 2 2 1 (Mpow 2 n (M (@proj1_sig R (fun h1 : R => 0 < h1 < 1.41) h))) (s_vector (p, q))).
eapply Rle_trans.
pose proof M_norm_sub_mult h (t, t0).
apply H.
eapply Rle_trans.
apply Rmult_le_compat_l.
unfold two_norm_M; simpl.
apply sqrt_pos.
apply IHn.
unfold two_norm_M.
simpl.
rewrite Cmod_RtoC; try apply MTM_lambda_2_pos_2; try (destruct h; simpl; auto).
apply Req_le.
rewrite Rmult_assoc; auto.
rewrite Mmult_assoc.
rewrite Mpow_comm; auto.
Qed.

Lemma h_bnd_lem :
0 <  h < 1.41.
Proof.
split; unfold h; unfold ω; try nra.
Qed.

Theorem matrix_bound : 
  forall p q: R,
  forall n : nat, 
  let Mn := Mpow 2 n (M  h ) in
  vec_two_norm_2d  (Mmult Mn (s_vector (p, q))) <= 
      σb ^ n * vec_two_norm_2d (s_vector (p,q)).
Proof.
intros.
set (j := (exist (fun x => 0 < x < 1.41) h) h_bnd_lem).
pose proof matrix_analysis_method_bound_n p q n j.
simpl in H.
eapply Rle_trans.
apply H.
apply Rmult_le_compat_r.
apply Rnorm_pos.
apply pow_incr; split.
apply sqrt_pos.
rewrite Cmod_RtoC.
apply sigma_bound.
apply MTM_lambda_2_pos_2.
unfold h. lra.
Qed.

Lemma iternR_bound : 
  forall p q: R,
  forall nf : nat, 
  ( nf <=1000)%nat -> 
  ∥iternR (p, q) h nf∥ <= σb ^ nf * ∥(p,q)∥.
Proof.
intros.
unfold σb.
eapply Rle_trans.
pose proof matrix_bound p q nf.
simpl in H0.
pose proof transition_matrix_equiv_iternR (p, q) h nf.
set (Mx:= Mmult (Mpow 2 nf (M h)) (s_vector (p, q))) in *.
assert (vec_two_norm_2d Mx = ∥ iternR (p, q) h nf ∥ ).
subst Mx.
rewrite <- H1.
unfold vec_two_norm_2d, Rprod_norm.
unfold fst at 1.
unfold snd at 1.
unfold fst at 1.
unfold snd at 1.
unfold Cmod.
repeat rewrite pow2_sqrt; auto; try apply sqr_plus_pos.
(*pose proof transition_matrix_equiv_iternR_aux h nf as (HA & HB & HC & HD).*)
assert (@snd R R
        (@coeff_mat C 2 1 (@zero C_AbelianGroup) (@Mmult C_Ring 2 2 1 (Mpow 2 nf (M h)) (s_vector (p, q))) 0
           0) = 0).
- 
unfold Mmult.
rewrite coeff_mat_bij; try lia.
simpl.
change (@zero C_Ring) with (@zero C_AbelianGroup).
repeat match goal with |-context[(@coeff_mat C ?a ?b ?c ?d ?e ?f)] =>
  change (@coeff_mat C a b c d e f) with (@coeff_mat C_AbelianGroup a b c d e f)
end.
rewrite ? transition_matrix_equiv_iternR_aux.
nra.
-
assert (@snd R R
        (@coeff_mat C 2 1 (@zero C_AbelianGroup) (@Mmult C_Ring 2 2 1 (Mpow 2 nf (M h)) (s_vector (p, q))) 1
           0) = 0).
+
unfold Mmult.
rewrite coeff_mat_bij; try lia.
simpl.
change (@zero C_Ring) with (@zero C_AbelianGroup).
repeat match goal with |-context[(@coeff_mat C ?a ?b ?c ?d ?e ?f)] =>
  change (@coeff_mat C a b c d e f) with (@coeff_mat C_AbelianGroup a b c d e f)
end.
rewrite ? transition_matrix_equiv_iternR_aux.
nra.
+
rewrite H2; clear H2.
rewrite H3; clear H3.
rewrite pow_i; try lia.
repeat rewrite Rplus_0_r; auto.
-
repeat rewrite sqrt_pow2; auto.
rewrite <- H2.
apply H0.
-
eapply Rmult_le_compat_l. 
apply pow_le; try nra.
unfold vec_two_norm_2d, Rprod_norm.
unfold fst at 1.
unfold snd at 1.
unfold fst at 1.
unfold snd at 1.
unfold Cmod.
repeat rewrite pow2_sqrt; auto; try apply sqr_plus_pos.
simpl.
apply Req_le.
f_equal; nra.
Qed.

Lemma method_norm_bound : 
  forall p q: R,
  ∥(leapfrog_stepR h (p,q))∥ <= σb * ∥(p,q)∥.
Proof.
intros.
assert (H : (1 <= 1000)%nat) by (simpl; lia).
pose proof iternR_bound p q 1 H.
unfold iternR in H0.
eapply Rle_trans.
apply H0.
apply Rmult_le_compat_r; try apply   Rnorm_pos.
rewrite pow_1.
lra.
Qed.

Lemma iternR_bound_max_step : 
  forall p q: R,
  forall nf : nat, 
  ( nf <=1000)%nat -> 
  ∥iternR (p, q) h nf∥ <= 1.003822 * ∥(p,q)∥.
Proof.
intros.
pose proof iternR_bound p q nf H.
unfold σb in H0.
eapply Rle_trans.
apply H0.
eapply Rmult_le_compat_r; try apply Rnorm_pos.
eapply Rle_trans.
apply Rle_pow; try nra; apply H.
interval with (i_prec 256).
Qed.

Close Scope R_scope. 