(** matrix_analysis.v: stability analysis for leapfrog integration
  of a simple harmonic oscillator.
 Copyright (C) 2021-2022  Ariel Eileen Kellison.
*)
From Coq Require Import ZArith Reals Psatz.
From Coq Require Import Bool Arith.Arith.
Require Import real_lemmas real_model matrix_lemmas.

From Coquelicot Require Import Coquelicot.
Require Import Interval.Tactic.

Import Bool.

Set Bullet Behavior "Strict Subproofs". 

Lemma prod_equal: forall {A B} (x y: A*B) x1 x2 y1 y2,
  x = (x1,x2) ->
  y = (y1,y2) ->
  x1=y1 -> x2 = y2 -> x=y.
Proof.
destruct x,y; simpl; intros; congruence.
Qed.

Ltac matrix_ext :=
  lazymatch goal with 
  | |- @eq (matrix _ _) _ _ => idtac
  | _ => fail "matrix_ext must be applied to a goal of the form, @eq (matrix _ _) _ _"
 end;
repeat
(lazymatch goal with |- @eq ?t _ _ =>
  lazymatch t with 
  | matrix _ _ => idtac
  | Tn _ _ => idtac
  | prod _ unit => idtac
  end
 end;
 eapply prod_equal; [reflexivity | reflexivity | | try apply (eq_refl tt)]).

(** An upper bound σb on the singular values of a square matrix A ∈ Mn(C) 
      is given by an upper bound on the eigenvalues of A'A *)
Definition sv_bound (n: nat ) (A : @matrix C n n) (σb : R):=  
  let ATA := Mmult (matrix_conj_transpose n n A) A (* the Gram matrix A'A *) in
  let λb := σb^2 in 
  0 <= σb /\
  exists (V Λ : @matrix C n n),
         Mmult ATA V = Mmult V Λ
      /\ is_orthogonal_matrix n V
      /\ diag_pred n Λ   
      /\ (forall (i : nat), (i < n)%nat ->
         (coeff_mat zero Λ i i) = RtoC (Re (coeff_mat zero Λ i i)) (* elements of Λ are real *)
         /\ 0 <= Re (coeff_mat zero Λ i i) <= λb) (* λb is positive and at least as large as all elements of Λ *)
.


Definition two_norm_bound (n: nat ) (A : @matrix C n n) (σ : R):=  
  forall (u : @matrix C n 1), 
  vec_two_norm n (Mmult A u) <=  σ * vec_two_norm n u
.


(** any vector x ∈ Cn can be written as a linear combination of columns of an 
    orthogonal matrix V ∈ Cnxn *)
Lemma vectors_in_basis (n : nat) : 
 forall (x : @matrix C n 1), 
 forall (V : @matrix C n n), is_orthogonal_matrix n V ->
 exists (a: @matrix C n 1),  x = Mmult V a.
Proof.
intros.
unfold is_orthogonal_matrix in H; destruct H as (Ha & Hb).
exists (Mmult (matrix_conj_transpose n n V) x). 
rewrite Mmult_assoc.
rewrite Hb.
rewrite Mmult_one_l; auto.
Qed.

(** the leapfrog transition matrix *)
Definition M (h: R) : @matrix C 2 2 := 
  let a := 0.5 * h^2 in 
   [ [ (1-a, 0),  (-0.5 * h * (2 - a), 0) ],
     [ (h, 0),      (1-a, 0) ] ].

(** ideal solution vector *)
Definition pq_vector (h: R) (p q : R -> R) (t : R) : @matrix C 2 1 :=
   [ [ (p t, 0) ] ,
     [ (q t, 0) ] ].

(** arbitrary solution vector *)
Definition s_vector (ic: R * R) : @matrix C 2 1 := 
 [ [ (fst ic, 0) ] ,
   [ (snd ic, 0) ] ].

(** equivalence between matrix update and leapfrog step*)
Lemma transition_matrix_equiv:
  forall (ic : R * R) (h : R),  
  Mmult (M h) (s_vector ic) = s_vector (leapfrog_stepR h ic).
Proof.
intros. destruct ic.
matrix_ext; cbv [sum_n sum_n_m Iter.iter_nat Iter.iter coeff_mat]; simpl;
unfold plus, mult; simpl; unfold Cplus, Cmult, zero; simpl;
unfold ω; f_equal; nra.
Qed.

Lemma transition_matrix_equiv_iternR:
  forall (ic : R * R) (h : R) (n : nat), 
  Mmult (Mpow 2 n (M h)) (s_vector ic) = s_vector (iternR ic h n).
Proof.
induction n.
-
unfold Mpow.
rewrite M_ID_equiv_M1, Mmult_one_l.
reflexivity.
-
change (S n) with (1+n)%nat.
rewrite <- Mpow_pows_plus.
unfold Mpow at 1.
rewrite M_ID_equiv_M1, Mmult_one_l.
rewrite <- Mmult_assoc. rewrite IHn.
rewrite transition_matrix_equiv.
rewrite step_iternR. auto.
Qed.

(** The eigenvalues of the transition matrix *)
Definition lambda_1 (h : R) : C := (1 -0.5 * h^2 , -h * sqrt(2 - h) * 0.5 * sqrt(h + 2)). 
Definition lambda_2 (h : R) : C := (1 -0.5 * h^2 ,  h * sqrt(2 - h) * 0.5 * sqrt(h + 2)).
Definition eigenvalue_vector (h : R) : @matrix C 2 1 :=
 [ [ lambda_1 h ],
   [ lambda_2 h ] ].

Definition eigenvalue_matrix (h : R) : @matrix C 2 2 :=
  [ [ lambda_1 h , C0 ] , [ C0 , lambda_2 h ] ].

(** The eigenvectors of the transition matrix *)
Definition eV_1 (h : R) : @matrix C 2 1 :=
 [ [ (0 , -0.5 * sqrt(4 - h^2)) ] ,
   [ C1 ] ].

Definition eV_2 (h : R) : @matrix C 2 1 :=
 [ [ (0 ,  0.5 * sqrt(4 - h^2))] ,
   [ C1 ] ].

Definition eigenvector_matrix (h : R) : @matrix C 2 2 :=
 [ [ (0 , -0.5 * sqrt(4 - h^2)), (0 ,  0.5 * sqrt(4 - h^2)) ],
   [ C1,                                 C1 ]].

(** We define the Gram matrix MTM for the transition matrix. The eigenvalues of the matrix MTM are the 
    singular values of the transition matrix *)
Definition MTM (h : R) : @matrix C 2 2 :=
 [ [  (0.25 * h^4 + 1, 0), (0.125 * h^3*(2 - h^2),0) ],
   [ (0.125 * h^3*(2 - h^2),0),  (0.0625 * h^6 - 0.25*h^4 + 1, 0)] ].

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
 [ [ MTM_lambda_1 h ],
   [ MTM_lambda_2 h ] ].

Definition MTM_eigenvalue_matrix (h : R) : @matrix C 2 2 :=
  [ [ RtoC (MTM_lambda_1 h), C0 ], 
    [ C0,   RtoC (MTM_lambda_2 h) ] ].

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
  [ [ coeff_mat zero (MTM_eV_1 h) 0 0,  coeff_mat zero (MTM_eV_2 h) 0 0 ],
    [ coeff_mat zero (MTM_eV_1 h) 1 0, coeff_mat zero (MTM_eV_2 h) 1 0 ] ].

(* M * V = V * L *)
Lemma eigens_correct (h : R) :
  0 <= h <= 2 -> 
  Mmult (M h) (eigenvector_matrix h) = 
  Mmult (eigenvector_matrix h) (eigenvalue_matrix h).
Proof.
intros.
assert (sqrt (2-h) * sqrt (h+2) = sqrt (4-h*h))
  by (rewrite <- sqrt_mult by lra; f_equal; lra).
pose proof (sqrt_def (4-h*h) ltac:(nra)).
matrix_ext.
all: change (Init.Nat.pred 2) with (S 0);
repeat rewrite sum_Sn;
repeat rewrite sum_O;
unfold M, eigenvector_matrix, eigenvalue_matrix, 
  eV_1, eV_2, lambda_1, lambda_2, matrix_lemmas.C1,
 coeff_mat; simpl.
all:
unfold mult, plus; simpl;
rewrite ?mult_aux1, ?mult_aux2, ?mult_aux3;
rewrite ?Cmult_0_r, ?Cplus_0_r;
unfold Cplus; simpl;
rewrite ?Rmult_0_l, ?Rmult_0_r, ?Rmult_1_r, ?Rplus_0_l, ?Rplus_0_r, ?Rminus_0_l;
rewrite <- H0 in *;
f_equal; try nra.
Qed.

Lemma MTM_aux  (h : R) :
  Mmult (matrix_conj_transpose _ _ (M h)) (M h) = MTM h.
Proof.
unfold MTM.
matrix_ext;
change (Init.Nat.pred 2) with (S 0);
rewrite ?sum_Sn, ?sum_O;
unfold M, matrix_conj_transpose, Cconj;
repeat rewrite coeff_mat_bij by lia;
unfold coeff_mat; simpl;
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

Lemma sqr_def : forall x, x^2 = x*x.
Proof. intros; nra. Qed.

Lemma pow2'_sqrt : forall x n, 
  0 <= x ->
  sqrt x ^ (S (S n)) = x * sqrt x ^ n.
Proof.
intros.
simpl.
rewrite <- Rmult_assoc.
f_equal.
apply sqrt_def; auto.
Qed.

(* MTM * V = V * L *)
Theorem MTM_eigens_correct (h : R) :
  0 < h  < 1.41 -> 
  Mmult (MTM h) (MTM_eigenvector_matrix h) = 
  Mmult (MTM_eigenvector_matrix h) (MTM_eigenvalue_matrix h).
Proof.
intros.
matrix_ext;
change (Init.Nat.pred 2) with (S 0);
rewrite ?sum_Sn, ?sum_O;
unfold MTM, MTM_eigenvector_matrix, MTM_eigenvalue_matrix;
repeat rewrite coeff_mat_bij;
unfold coeff_mat; simpl;
change mult with Cmult;
change plus with Cplus;
unfold RtoC;
cbv [Cplus Cmult]; simpl;
rewrite ?Rmult_0_l, ?Rmult_0_r;
unfold C0;
rewrite ?Rminus_0_r, ?Rplus_0_r, ?Rmult_1_r.
-
f_equal.
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
-
f_equal.
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
f_equal.
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
f_equal.
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
rewrite pow_i by lia.
rewrite Rplus_0_r.
apply sqrt_pow2.
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

Lemma orthgonal_matrix_no_zero_columns:
 forall (V: matrix 2 2),
  is_orthogonal_matrix 2 V ->
  forall i, 
  (i < 2)%nat ->
 0 < vec_two_norm 2 [[coeff_mat zero V 0 i], [coeff_mat zero V 1 i]].
Proof.
intros V H2 i Hi.
assert (0 <> vec_two_norm 2 [ [ coeff_mat zero V 0 i ] , [ coeff_mat zero V 1 i ] ]).
2: assert (0 <= vec_two_norm 2 [[coeff_mat zero V 0 i], [coeff_mat zero V 1 i]])
      by apply sqrt_pos;
      lra.
intro.
assert (   [[coeff_mat zero V 0 i], [coeff_mat zero V 1 i]] = [ [C0], [C0] ]). {
 clear - H.
 set (a := coeff_mat _ _ _ _) in *. clearbody a.
 set (b := coeff_mat _ _ _ _) in *. clearbody b.
 symmetry in H.
 apply sqrt_eq_0 in H; [ | apply sqrt_pos].
 unfold Cmod in H; simpl in H.
 unfold coeff_mat in H; simpl in H.
 apply sqrt_eq_0 in H; [ | nra].
 destruct a as [ar ai], b as [br bi]. simpl in *. unfold C0.
 rewrite ?Rmult_1_r, ?Rplus_0_r in H.
 ring_simplify in H.
 replace (ar^4) with (ar^2 * ar^2) in H by nra.
 replace (br^4) with (br^2 * br^2) in H by nra.
 replace (ai^4) with (ai^2 * ai^2) in H by nra.
 replace (bi^4) with (bi^2 * bi^2) in H by nra.
 assert (ar^2=0 /\ ai^2=0 /\ br^2=0 /\ bi^2=0)
  by (repeat split; nra).
 clear H; destruct H0 as [? [? [? ?]]].
 repeat f_equal; nra.
}
clear H.
injection H0; clear H0; intros.
destruct H2.
assert (forall m1 m2 : @matrix C 2 2, m1=m2 -> 
   coeff_mat zero m1 0 0 = coeff_mat zero m2 0 0 /\
   coeff_mat zero m1 0 1 = coeff_mat zero m2 0 1 /\
   coeff_mat zero m1 1 0 = coeff_mat zero m2 1 0 /\
   coeff_mat zero m1 1 1 = coeff_mat zero m2 1 1) 
    by (intros; subst; auto).
apply H3 in H1; destruct H1 as [H1a [H1b [H1c H1d]]].
apply H3 in H2; destruct H2 as [H2a [H2b [H2c H2d]]].
clear H3.
set (u := @coeff_mat C_AbelianGroup 2 2 (@zero C_AbelianGroup)
        (@Mone C_Ring 2)) in *.
hnf in u. simpl in u. subst u.
simpl in *.
repeat match goal with H: _ = zero |- _ => clear H end.
repeat match goal with H: _ = one |- _ => injection H; clear H; intros end.
unfold C0 in *.
destruct i as [|[|]]; [ | | lia]; clear Hi;
rewrite H,H0 in *; clear H H0; simpl in *; lra.
Qed.

(* if σ^2 bounds the singular values of A ∈ M(C^2) then σ bounds the two-norm of A *)
Theorem sv_bound_implies_two_norm_bound   (A : @matrix C 2 2) (σ : R):
  sv_bound 2 A σ  ->  two_norm_bound 2 A σ.
Proof.
intros. intro.
red in H.
destruct H as [H0 [V [Λ [H1 [H2 [H3 H6]]]]]].
assert (exists a : matrix 2 1, u = Mmult V a)
  by (apply  (vectors_in_basis 2 u V ); auto).
destruct H as (a & Hu); subst.
unfold vec_two_norm.
repeat rewrite tranpose_rewrite.
do 2 rewrite <- Mmult_assoc.
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
rewrite <- (sqrt_pow2 σ) by auto.
rewrite <- sqrt_mult by (try nra; apply Cmod_ge_0).
apply sqrt_le_1_alt.
rewrite <- (Cmod_RtoC (σ^2)) by nra.
rewrite <- Cmod_mult.
unfold Mmult.
rewrite !coeff_mat_bij; try lia.
change (Init.Nat.pred 2) with 1%nat.
rewrite !sum_Sn.
rewrite !coeff_mat_bij by lia.
rewrite !sum_O.
rewrite !coeff_mat_bij by lia.
change plus with Cplus.
change mult with Cmult.
unfold matrix_conj_transpose.
rewrite !coeff_mat_bij by lia.
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
unfold Rminus.
rewrite ?Ropp_mult_distr_l.
rewrite <- ? Rmult_plus_distr_r.
apply Rmult_le_0_r; try apply sqrt_pos.
unfold pow.
rewrite <- ?Rmult_assoc, ?Rmult_1_r.
rewrite <- ? Rmult_plus_distr_r.
apply Rmult_le_0_r; try nra.
apply Rmult_le_0_r; try nra.
apply Rmult_le_0_r; try nra.
interval with ( i_bisect h, i_depth 9, i_taylor h, i_degree 5, i_prec 53).
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
unfold coeff_mat; simpl.
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
unfold coeff_mat; simpl.
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
unfold coeff_mat; simpl.
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
unfold coeff_mat; simpl.
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
unfold coeff_mat; simpl.
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
unfold coeff_mat; simpl.
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
unfold coeff_mat; simpl.
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
unfold coeff_mat; simpl.
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

Lemma two_norm_bound_lambda2 (h : R | 0 < h < 1.41): 
 two_norm_bound 2 (M (proj1_sig h)) (sqrt (MTM_lambda_2 (proj1_sig h))).
Proof.
apply ( sv_bound_implies_two_norm_bound
  (M (proj1_sig h)) (sqrt (MTM_lambda_2 (proj1_sig h)))).
unfold sv_bound.
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
unfold diag_pred, MTM_eigenvalue_matrix; unfold coeff_mat;
intros; simpl; try lia.
destruct i as [|[|]]; try lia;
destruct j as [|[|]]; try lia;
reflexivity.
-
unfold MTM_eigenvalue_matrix, coeff_mat; simpl.
destruct i as [|[|]]; try lia; reflexivity.
-
destruct i as [|[|]]; try lia; simpl.
apply MTM_lambda_1_pos_2; auto.
apply MTM_lambda_2_pos_2; auto.
-
rewrite Rmult_1_r.
rewrite sqrt_def by (apply MTM_lambda_2_pos_2; auto).
destruct i as [|[|]]; try lia; simpl.
apply eig_MTM_le; auto.
apply Rle_refl.
Qed.

Definition σ (h: R) := sqrt (MTM_lambda_2 h).

Definition two_norm_M (h : R | 0 < h < 1.41) :=
  proj1_sig (exist (two_norm_bound 2 (M (proj1_sig h))) 
                          (sqrt (MTM_lambda_2 (proj1_sig h)))
                          (two_norm_bound_lambda2 h)).

Lemma sigma_eq_two_norm_M:
  forall h, σ (proj1_sig h) = two_norm_M h.
Proof.
destruct h; reflexivity.
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
unfold two_norm_M. simpl.
repeat rewrite <- two_norms_eq_2d.
apply two_norm_bound_lambda2.
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

Lemma Rprod_norm_vec_two_norm : 
 forall ic,   ∥ ic ∥ = vec_two_norm _ (s_vector ic).
Proof.
intros.
rewrite two_norms_eq_2d.
unfold vec_two_norm_2d.
destruct ic as [p q]; simpl.
unfold Rprod_norm; simpl.
unfold Cmod, coeff_mat; simpl.
f_equal.
rewrite ?Rmult_0_l, ?Rplus_0_r, ?Rmult_1_r.
rewrite ?sqrt_sqrt; auto; nra.
Qed.

Lemma iternR_bound : 
  forall p q: R,
  forall nf : nat, 
  ( nf <=1000)%nat -> 
  ∥iternR (p, q) h nf∥ <= σb ^ nf * ∥(p,q)∥.
Proof.
intros.
unfold σb.
apply Rle_trans with (σb ^ nf * vec_two_norm_2d (s_vector (p, q))).
-
pose proof matrix_bound p q nf.
simpl in H0.
rewrite Rprod_norm_vec_two_norm.
rewrite <- transition_matrix_equiv_iternR.
rewrite two_norms_eq_2d. lra.
-
apply Rmult_le_compat_l. 
apply pow_le; try nra.
unfold vec_two_norm_2d, Rprod_norm.
unfold fst, snd, Cmod.
rewrite !pow2_sqrt by apply sqr_plus_pos.
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
eapply Rle_trans.
apply (iternR_bound p q 1 H).
apply Rmult_le_compat_r; try apply   Rnorm_pos.
lra.
Qed.

Lemma iternR_bound_max_step : 
  forall p q: R,
  forall nf : nat, 
  ( nf <=1000)%nat -> 
  ∥iternR (p, q) h nf∥ <= 1.003822 * ∥(p,q)∥.
Proof.
intros.
eapply Rle_trans.
apply (iternR_bound p q nf H).
eapply Rmult_le_compat_r; try apply Rnorm_pos.
eapply Rle_trans.
apply Rle_pow. unfold σb. lra. eassumption.
interval with (i_prec 256).
Qed.

Close Scope R_scope. 