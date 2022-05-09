(** matrix_lemmas.v:  Definitions and lemmas for error analysis
  of ODE systems using matrices.
 Copyright (C) 2021-2022 and Ariel Kellison.
*)


From Coq Require Import ZArith Reals Psatz.
From Coq Require Import Arith.Arith.
Require Import real_lemmas.
Require Import Init.Nat Arith.EqNat.

From Coq Require Import ssreflect. 
From Coquelicot Require Import Coquelicot.
Require Import IntervalFlocq3.Tactic.

Set Bullet Behavior "Strict Subproofs". 


Require Import Coq.Logic.FunctionalExtensionality.


Definition C0: C := (0,0).
Definition C1: C := (1,0).



(*********************************)
(* MATRIX TRANSPOSE       *)
(*********************************)

Definition matrix_conj_transpose (n m:nat) (M: @matrix C n m) : @matrix C m n := 
  mk_matrix m n (fun i j => Cconj (coeff_mat Hierarchy.zero M j i))
.

Lemma Cconj_plus (a b : C) :
  Cconj( Cplus a  b) = Cplus (Cconj a) (Cconj b).
Proof.
destruct a, b.
cbv [Cconj Cplus].
simpl.
apply pair_equal_spec; split; auto.
nra.
Qed.

Lemma Cconj_mult (a b : C) :
  Cconj( Cmult a  b) = Cmult (Cconj a) (Cconj b).
Proof.
destruct a, b.
cbv [Cconj Cmult].
simpl.
apply pair_equal_spec; split; auto.
nra.
field_simplify; nra.
Qed.

Lemma tranpose_rewrite (A: @matrix C 2 2) (x: @matrix C 2 1): 
(matrix_conj_transpose 2 1 (Mmult A x)) = 
Mmult (matrix_conj_transpose 2 1 x) (matrix_conj_transpose 2 2 A).
Proof.
unfold matrix_conj_transpose.
unfold Mmult.
apply mk_matrix_ext; intros.
rewrite coeff_mat_bij; try lia.
replace (Init.Nat.pred 2) with (S 0) by lia.
repeat rewrite sum_Sn.
repeat rewrite coeff_mat_bij; try lia.
repeat rewrite sum_O.
repeat rewrite coeff_mat_bij; try lia.
change plus with Cplus.
change mult with Cmult.
assert ( (i = 0)%nat) by lia.
subst.
assert ( (j = 0)%nat \/ (j <> 0)%nat) by lia; destruct H1.
- 
subst. 
unfold coeff_mat.
simpl.
rewrite Cconj_plus.
repeat rewrite Cconj_mult.
rewrite Cmult_comm.
rewrite Cplus_comm.
rewrite Cmult_comm.
rewrite Cplus_comm.
auto.
-
assert (j=1)%nat by lia.
subst.
unfold coeff_mat.
simpl.
rewrite Cconj_plus.
repeat rewrite Cconj_mult.
rewrite Cmult_comm.
rewrite Cplus_comm.
rewrite Cmult_comm.
rewrite Cplus_comm.
auto.
Qed.



(* multiply a matrix by a complex number *)
Definition mat_coeff_mult (a : C) (n m:nat) (V: @matrix C n m) : @matrix C n m :=
  @mk_matrix C n m (fun i j => 
      Cmult a (@coeff_mat C n m Hierarchy.zero V i j))
.



Lemma zero_d_matrices_eq (x y : @matrix C 0 1%nat) :
  x = y.
Proof.
destruct x , y; auto.
Qed.



(*********************************)
(* ID MATRIX & ZERO MATRIX       *)
(*********************************)

(* complex zero matrix and zero vector *)
Definition M0 (n:nat) : @matrix C n n := Mzero. 
Definition V0 (n:nat) : @matrix C n 1%nat := mk_matrix n 1%nat (fun _ _ => C0)
.


(* identity *)
Definition M_ID (n:nat) : @matrix C n n := 
  mk_matrix n n (fun i j => if (eqb i j) then C1 else C0)
.

(* vector of ones *)
Definition v1 (n:nat) : @matrix C n 1%nat := mk_matrix n 1%nat (fun _ _ => C1).


Lemma M_ID_equiv_M1 :
  forall n : nat, M_ID n = Mone.
Proof.
intros.
apply mk_matrix_ext => i j Hi Hj.
assert (i = j \/ i <> j) by lia.
destruct H.
- 
rewrite Mone_seq_diag; auto.
apply Nat.eqb_eq in H.
destruct eqb; try discriminate; auto.
-
rewrite Mone_seq_not_diag; auto.
apply Nat.eqb_neq in H.
destruct eqb; try discriminate; auto.
Qed.


Lemma Mmult_Mzero_r (n: nat) (M: @matrix C n n) :
  @Mmult C_Ring n n n M Mzero  = Mzero.
Proof.
apply mk_matrix_ext => i j Hi Hj.
pose proof @sum_n_ext_loc C_Ring
  (fun l : nat => mult (coeff_mat zero M i l) (@coeff_mat C n n zero Mzero l j))
  (fun l : nat => mult (coeff_mat zero M i l) zero)
  (pred n).
rewrite H; clear H; try apply sum_n_m_const_zero.
- 
rewrite sum_n_mult_r; apply mult_zero_r.
-
intros.
f_equal.
apply coeff_mat_bij;lia.
Qed.


Lemma Mmult_Mzero_l (n: nat) (M: @matrix C n n) :
  @Mmult C_Ring n n n Mzero M  = Mzero.
Proof.
apply mk_matrix_ext => i j Hi Hj.
pose proof @sum_n_ext_loc C_Ring
  (fun l : nat => mult (@coeff_mat C n n zero Mzero i l) (coeff_mat zero M l j))
  (fun l : nat => mult zero (coeff_mat zero M l j))
  (pred n).
rewrite H; clear H; try apply sum_n_m_const_zero.
- 
rewrite sum_n_mult_l; apply mult_zero_l.
-
intros.
f_equal.
apply coeff_mat_bij;lia.
Qed.


Lemma Mmult_M0_vec (n: nat) (V: @matrix C n 1%nat) :
  @Mmult C_Ring n n 1%nat (M0 n) V  = Mzero.
Proof.
apply mk_matrix_ext => i j Hi Hj.
pose proof @sum_n_ext_loc C_Ring
  (fun l : nat => @mult C_Ring (@coeff_mat C_Ring n n (@zero C_Ring) (M0 n) i l)
     (@coeff_mat C_Ring n 1 (@zero C_Ring) V l j)) 
  (fun l : nat => mult zero (coeff_mat zero V l j))
  (pred n).
rewrite H; clear H; try apply sum_n_m_const_zero.
- 
rewrite sum_n_mult_l; apply mult_zero_l.
-
intros.
f_equal.
apply coeff_mat_bij;lia.
Qed.


Lemma Mcong_transpose_zero (n: nat) (M: @matrix C n n) :
matrix_conj_transpose n n M = (M0 n) <-> M = (M0 n).
Proof.
split; intros.
-
rewrite (@coeff_mat_ext_aux C_Ring n n zero zero) in H.
replace M with (mk_matrix n n (coeff_mat zero M)) by
  (apply mk_matrix_bij).
apply mk_matrix_ext => i j  Hi Hj.
unfold matrix_conj_transpose in H.
specialize (H j i Hj Hi).
unfold M0, Mzero, Cconj in H.
repeat rewrite coeff_mat_bij in H; try lia.
destruct (coeff_mat zero M i j); simpl in H; auto.
symmetry in H; inversion H. subst.
assert (r0 = 0) by nra; subst; auto.
-
subst.
unfold matrix_conj_transpose, M0, Mzero, Cconj.
apply mk_matrix_ext => i j  Hi Hj.
repeat rewrite coeff_mat_bij; try lia; simpl.
rewrite Ropp_0; auto.
Qed.


Lemma M0_coeff_zero (n: nat) :
forall i j, (i < n)%nat /\ (j < n)%nat -> @coeff_mat C n n (@zero C_AbelianGroup) (M0 n) i j = 0.
intros.
unfold M0, Mzero. apply coeff_mat_bij; lia.
Qed.


Lemma eq_M0_iff (n: nat) (M : @matrix C n n) :
  M = M0 n <-> forall i j, ((i < n)%nat /\ (j < n)%nat) -> (@coeff_mat C_Ring n n zero M i j) = zero.
Proof.
split; intros.
- 
subst. unfold M0, Mzero.
apply coeff_mat_bij; try lia; auto.
- 
destruct n.
+ 
destruct M; auto.
+
unfold M0, Mzero.
pose proof @mk_matrix_bij C_Ring (S n) (S n) zero M as Hm.
rewrite <- Hm.
apply mk_matrix_ext => i j Hi Hj.
apply H; auto.
Qed.



Lemma neq_M0_implies_aux1 (n: nat) (M1 : @matrix C n n) (M2 : @matrix C (S n) (S n)):
  (M1 = M0 n -> False) ->
  (forall i j, ((i < n)%nat /\ (j < n)%nat) -> (coeff_mat zero M2 i j) = (coeff_mat zero M1 i j)) -> 
  (M2 = M0 (S n) -> False).
Proof.
intros.
contradiction H; clear H.
rewrite eq_M0_iff in H1.
apply eq_M0_iff; intros. 
specialize (H0 i j H).
assert (HS: (i < S n)%nat /\ (j < S n)%nat) by lia.
specialize (H1 i j HS).
etransitivity. symmetry. eassumption.
auto.
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
(* end ID and 0 matrix lemmas *)



(******************)
(** ORTHOGONAL MATRICES *)
(*******************)
Definition is_orthogonal_matrix (n: nat ) (Q : @matrix C n n) := 
  Mmult (matrix_conj_transpose n n Q) Q = Mone /\ 
  Mmult Q (matrix_conj_transpose n n Q) = Mone
.



(*******************)
(* DIAGONAL MATRICES *)
(*******************)
(* a matrix is diagonal if *)
Definition diag_pred (n: nat) (M: @matrix C n n) := 
  forall i j, (i < n)%nat /\ (j < n)%nat /\ (i <> j)%nat -> (@coeff_mat C n n Hierarchy.zero M i j) = zero
.


(* construct a diagonal matrix from a vector *)
Definition vec_to_diag (n:nat) (V: @matrix C n 1%nat) : @matrix C n n :=
  (@mk_matrix C n n (fun i j => if (eqb i j) then 
      (@coeff_mat C n 1%nat Hierarchy.zero V i 0) else C0))
.  


(* vec_to_diag construction is a diagonal matrix *)
Lemma vec_to_diag_pred (n: nat) (L: matrix n 1%nat) :
  diag_pred n (vec_to_diag n L).
Proof.
unfold diag_pred, vec_to_diag; intros.
rewrite coeff_mat_bij; try lia.
destruct H as (A & B & C).
apply Nat.eqb_neq in C.
destruct eqb; auto; try discriminate.
Qed.

Lemma M_ID_diag (m: nat) : 
diag_pred m (M_ID m).
Proof.
unfold diag_pred; intros.
unfold M_ID.
rewrite coeff_mat_bij; try auto; try lia.
destruct H as (A & B & C).
apply Nat.eqb_neq in C.
destruct eqb; auto; try discriminate.
Qed.


(*************************)
(* COMPLEX NUMBER LEMMAS *)
(*************************)
Lemma Czero_sqs (x : C) :
  0<= Cmod x /\ Cmod x <= 0 -> Cmod x = 0.
Proof.
unfold Cmod.
intros.
destruct H.
apply Rle_antisym; auto.
Qed.


Lemma Ceq_Cmod_eq (x y : C):
  x = y -> Cmod x = Cmod y.
Proof.
intros; subst; auto.
Qed.

Lemma C_sqr_ccong  (c : C) :
(Cmult c (Cconj c)) = fst(c)^2 + snd(c)^2.
Proof.
destruct c.
unfold Cconj.
cbv [Cmult RtoC].
simpl.
apply pair_equal_spec; split; nra.
Qed.

Lemma C_sqr_ccong2  (c : C) :
(Cmult (Cconj c) c ) = fst(c)^2 + snd(c)^2.
Proof.
destruct c.
unfold Cconj.
cbv [Cmult RtoC].
simpl.
apply pair_equal_spec; split; nra.
Qed.

Lemma Cmod_Ccong  (c : C) :
(Cmult c (Cconj c)) = (Cmod c)^2.
Proof.
destruct c.
unfold Cconj, Cmod.
cbv [Cmult RtoC].
simpl.
apply pair_equal_spec; split; try nra.
repeat rewrite Rmult_1_r.
rewrite sqrt_def; try nra.
Qed.


Lemma cmod_le_0 x: 
Cmod x <= 0 -> x = 0.
Proof.
intros.
unfold Cmod in *.
pose proof sqrt_pos (fst x ^ 2 + snd x ^ 2).
apply Cmod_eq_0.
apply Czero_sqs.
split; auto.
Qed.


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



Lemma Rmult_le (a b :R):
  0 <= a * b ->  0 < a ->  0 <= b .
Proof.
intros.
nra.
Qed.



Lemma Cdiv_zero (a : C):
  a <> 0 -> Cdiv 0 a = C0.
Proof.
intros. 
cbv [Cdiv Cinv].
destruct a.
unfold C0, fst, snd.
apply pair_equal_spec. unfold fst, snd; simpl.
repeat rewrite Rmult_0_l; nra.
Qed.

Lemma Cmult_zero (a b : C) :
  Cmult a b = 0 -> b <> 0 -> a = 0.
Proof.
intros.
assert (H1 : Cdiv (Cmult a b) b = Cdiv 0 b) by (rewrite H; auto).
assert (H2 : Cdiv (Cmult a b) b = Cmult a (Cdiv b b)).
destruct b; destruct a.
cbv [Cmult Cdiv]; simpl.
apply pair_equal_spec. nra.
rewrite H2 in H1.
replace (Cdiv b b ) with C1 in H1.
replace (Cmult a C1) with a in H1.
rewrite Cdiv_zero in H1; auto.
cbv [C1 Cmult]; destruct a; simpl; apply pair_equal_spec;split; nra.
replace (Cdiv b b) with (b * / b)%C.
rewrite Cinv_r; auto.
cbv [Cmult Cdiv]. apply pair_equal_spec;split; nra.
Qed.
(* end complex number lemmas *)



(******************)
(* EUCLIDEAN NORM *)
(******************)
Definition vec_two_norm (n: nat ) (u : @matrix C n 1) : R :=
   Coq.Reals.R_sqrt.sqrt (Cmod (@coeff_mat C 1%nat 1%nat Hierarchy.zero (Mmult (matrix_conj_transpose n 1 u) u) 0 0))
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
change mult with Cmult.
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
repeat match goal with |-context[R_sqrt.sqrt (fst (?a) ^2 + snd?b ^2)] =>
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






(* multiplying two diagonal matrices preserves diag predicate*)
Lemma Matrix_diag_mult_diag (n: nat) (M1 M2 M3: @matrix C n n):
  diag_pred n M1 ->
  diag_pred n M2 ->
  (Mmult M1 M2) = M3 -> diag_pred n M3.
Proof.
intros.
unfold diag_pred in *.
intros.
unfold Mmult in H1.
subst.
rewrite coeff_mat_bij; try lia.
pose proof (@sum_n_m_ext_loc C_Ring
(fun l : nat => mult (coeff_mat zero M1 i l) (coeff_mat zero M2 l j)) 
(fun _ : nat => zero) 0 (pred n)).
unfold sum_n.
rewrite H1; clear H1.
apply sum_n_m_const_zero.
intros.
assert (HK: i <> k \/ j <> k) by lia; destruct HK as [A | B].
-
assert ((i < n)%nat /\ (k < n)%nat /\ i <> k) as Hk1 by lia.
specialize (H i k Hk1); rewrite H; rewrite mult_zero_l; auto.
-
assert ((k < n)%nat /\ (j < n)%nat /\ k <> j) as Hk2 by lia.
specialize (H0 k j Hk2); rewrite H0; rewrite mult_zero_r; auto.
Qed.


(* a more constructive result of multiplying two diagonal matrices :
  we know the exact components of the resulting matrix *)
Lemma Matrix_diag_mult ( n: nat) (M1 M2 M3: @matrix C n n):
  diag_pred n M1 ->
  diag_pred n M2 ->
  (Mmult M1 M2) = M3 -> 
  forall i j, (i < n)%nat /\ (j < n)%nat -> 
  @coeff_mat C n n Hierarchy.zero M3 i j = 
  Cmult (@coeff_mat C n n Hierarchy.zero M1 i j) (@coeff_mat C n n Hierarchy.zero M2 i j).
Proof.
intros.
assert (Hij: i = j \/ i <> j) by lia; destruct Hij.
-
subst.
destruct j.
+ 
unfold coeff_mat at 1.
repeat rewrite coeff_Tn_bij; try lia.
assert (A: (0 <= 1)%nat) by lia.
assert (B: (0 <= pred n)%nat) by lia.
pose proof 
  @sum_n_m_Chasles C_Ring (fun l : nat => mult (coeff_mat zero M1 0 l) (coeff_mat zero M2 l 0))
  0 0 (pred n) A B.
unfold sum_n.
rewrite H1; clear H1.
match goal with |- context [plus ?a ?b = _] =>
  assert (b = zero)
end.
*
unfold diag_pred in *.
pose proof (@sum_n_m_ext_loc C_Ring
(fun l : nat => mult (coeff_mat zero M1 0l) (coeff_mat zero M2 l 0)) 
(fun _ : nat => zero) 1 (pred n)).
rewrite H1; clear  H1.
rewrite sum_n_m_const_zero; auto.
intros k Hk.
assert (Hjk: (0 < n)%nat /\ (k < n)%nat /\ (0 <> k)%nat ) by lia.
specialize (H 0%nat k Hjk); rewrite H.
rewrite mult_zero_l; auto.
*
rewrite H1; clear H1.
rewrite plus_zero_r.
rewrite sum_n_n.
unfold mult, Ring.mult; simpl; auto.
+ 
rewrite coeff_mat_bij; try lia.  
assert (Hj : (0 <= S (S j))%nat) by lia.
assert (Hjj: (S j <= pred n)%nat) by lia.
pose proof 
  @sum_n_m_Chasles C_Ring (fun l : nat => mult (coeff_mat zero M1 (S j) l) (coeff_mat zero M2 l (S j)))
  0 (S j) (pred n) Hj Hjj.
unfold sum_n.
rewrite H1; clear H1.
match goal with |- context [plus ?a ?b = _] =>
  assert (b = zero)
end.
* 
unfold diag_pred in *.
pose proof (@sum_n_m_ext_loc C_Ring
(fun l : nat => mult (coeff_mat zero M1 (S j) l) (coeff_mat zero M2 l (S j))) 
(fun _ : nat => zero) (S (S j)) (pred n)).
rewrite H1; clear  H1.
rewrite sum_n_m_const_zero; auto.
intros k Hk.
assert (Hjk: (S j < n)%nat /\ (k < n)%nat /\ S j <> k) by lia.
specialize (H (S j) k Hjk); rewrite H.
rewrite mult_zero_l; auto.
* 
rewrite H1; clear H1. 
rewrite plus_zero_r.
assert (A: (0 < S j)%nat) by lia.
assert (B: (0 <= S j)%nat) by lia.
assert (C: (j <= S j)%nat) by lia.
pose proof 
  @sum_n_m_Chasles C_Ring (fun l : nat => mult (coeff_mat zero M1 (S j) l) (coeff_mat zero M2 l (S j)))
  0 (j) (S j) B C. 

rewrite H1; clear H1.
match goal with |- context [plus ?a ?b = _] =>
  assert (a = zero)
end.
--
unfold diag_pred in *.
pose proof (@sum_n_m_ext_loc C_Ring
(fun l : nat => mult (coeff_mat zero M1 (S j) l) (coeff_mat zero M2 l (S j))) 
(fun _ : nat => zero) 0 j).
rewrite H1; clear  H1.
rewrite sum_n_m_const_zero; auto.
intros k Hk.
assert (Hjk: (S j < n)%nat /\ (k < n)%nat /\ S j <> k) by lia.
specialize (H (S j) k Hjk); rewrite H.
rewrite mult_zero_l; auto.
-- 
rewrite H1; clear H1.
rewrite plus_zero_l.
rewrite sum_n_n.
unfold mult, Ring.mult; simpl; auto.
-
unfold diag_pred in *.
subst.
rewrite coeff_mat_bij; try lia. 
pose proof (@sum_n_m_ext_loc C_Ring
(fun l : nat => mult (coeff_mat zero M1 i l) (coeff_mat zero M2 l j)) 
(fun _ : nat => zero) 0 (pred n)).
unfold sum_n.
rewrite H1.
rewrite sum_n_m_const_zero; auto.
pose proof H i j as A.
rewrite A; try lia.
pose proof H0 i j as B.
rewrite B; try lia. 
rewrite Cmult_0_l; auto.
intros.
assert (HK: i <> k \/ j <> k) by lia; destruct HK as [A | B].
+ 
assert ((i < n)%nat /\ (k < n)%nat /\ i <> k) as Hk1 by lia.
specialize (H i k Hk1); rewrite H; rewrite mult_zero_l; auto.
+
assert ((k < n)%nat /\ (j < n)%nat /\ k <> j) as Hk2 by lia.
specialize (H0 k j Hk2); rewrite H0; rewrite mult_zero_r; auto.
Qed.


(*[ a b ] [ x 0 ]   [ ax by ] 
  [ c d ] [ 0 y ] = [ cx dy ] *)
Lemma Mmult_diagonal_implies (n: nat) (M L A: @matrix C n n) :
  diag_pred n L -> 
  Mmult M L = A -> 
  forall i j, (i < n)%nat /\ (j < n)%nat -> 
  @coeff_mat C n n Hierarchy.zero A i j = 
  Cmult (@coeff_mat C n n Hierarchy.zero M i j) (@coeff_mat C n n Hierarchy.zero L j j).
Proof.
intros.
subst.
destruct j.
+ 
unfold coeff_mat at 1.
repeat rewrite coeff_Tn_bij; try lia.
assert (A: (0 <= 1)%nat) by lia.
assert (B: (0 <= pred n)%nat) by lia.
pose proof 
  @sum_n_m_Chasles C_Ring (fun l : nat => mult (coeff_mat zero M i l) (coeff_mat zero L l 0))
  0 0 (pred n) A B.
unfold sum_n.
rewrite H0; clear H0.
match goal with |- context [plus ?a ?b = _] =>
  assert (b = zero)
end.
*
unfold diag_pred in *.
pose proof (@sum_n_m_ext_loc C_Ring
(fun l : nat => mult (coeff_mat zero M i l) (coeff_mat zero L l 0)) 
(fun _ : nat => zero) 1 (pred n)).
rewrite H0; clear  H0.
rewrite sum_n_m_const_zero; auto.
intros k Hk.
assert (Hjk: (k < n)%nat /\ (0 < n)%nat /\ (k <> 0)%nat ) by lia.
specialize (H k 0%nat Hjk); rewrite H.
rewrite mult_zero_r; auto.
*
rewrite H0; clear H0.
rewrite plus_zero_r.
rewrite sum_n_n.
unfold mult, Ring.mult; simpl; auto.
+ 
rewrite coeff_mat_bij; try lia.  
assert (Hj : (0 <= S (S j))%nat) by lia.
assert (Hjj: (S j <= pred n)%nat) by lia.
pose proof 
  @sum_n_m_Chasles C_Ring (fun l : nat => mult (coeff_mat zero M i l) (coeff_mat zero L l (S j)))
  0 (S j) (pred n) Hj Hjj.
unfold sum_n.
rewrite H0; clear H0.
match goal with |- context [plus ?a ?b = _] =>
  assert (b = zero)
end.
* 
unfold diag_pred in *.
pose proof (@sum_n_m_ext_loc C_Ring
(fun l : nat => mult (coeff_mat zero M i l) (coeff_mat zero L l (S j))) 
(fun _ : nat => zero) (S (S j)) (pred n)).
rewrite H0; clear  H0.
rewrite sum_n_m_const_zero; auto.
intros k Hk.
assert (Hjk: (  k < n)%nat /\ (S j < n)%nat /\ k <> S j) by lia.
specialize (H k (S j) Hjk); rewrite H.
rewrite mult_zero_r; auto.
* 
rewrite H0; clear H0. 
rewrite plus_zero_r.
assert (A: (0 < S j)%nat) by lia.
assert (B: (0 <= S j)%nat) by lia.
assert (C: (j <= S j)%nat) by lia.
pose proof 
  @sum_n_m_Chasles C_Ring (fun l : nat => mult (coeff_mat zero M i l) (coeff_mat zero L l (S j)))
  0 (j) (S j) B C. 

rewrite H0; clear H0.
match goal with |- context [plus ?a ?b = _] =>
  assert (a = zero)
end.
--
unfold diag_pred in *.
pose proof (@sum_n_m_ext_loc C_Ring
(fun l : nat => mult (coeff_mat zero M i l) (coeff_mat zero L l (S j))) 
(fun _ : nat => zero) 0 j).
rewrite H0; clear  H0.
rewrite sum_n_m_const_zero; auto.
intros k Hk.
assert (Hjk: (k < n)%nat /\ ((S j) < n)%nat /\ k <>  S j) by lia.
specialize (H k (S j) Hjk); rewrite H.
rewrite mult_zero_r; auto.
-- 
rewrite H0; clear H0.
rewrite plus_zero_l.
rewrite sum_n_n.
unfold mult, Ring.mult; simpl; auto.
Qed.






(**************************)
(* MATRIX POWERS *)
(**************************)
Fixpoint Mpow (m n: nat) (M: @matrix C m m): matrix m m:=  
  match n with
    | 0 => (M_ID m) 
    | S n' => Mmult (Mpow m n' M) M  
  end.

Lemma Mpow_comm (m n : nat) (M: @matrix C m m) :
Mmult M (Mpow m n M) = Mmult (Mpow m n M) M .
Proof.
induction n.
- 
simpl.
rewrite M_ID_equiv_M1.
rewrite Mmult_one_l; auto.
rewrite Mmult_one_r; auto.
-
unfold Mpow; fold Mpow.
rewrite <- IHn at 2.
rewrite <- Mmult_assoc.
auto.
Qed.


Lemma Mpow_pows_plus (m n n': nat) (M: @matrix C m m) : 
 Mmult (Mpow m n M) (Mpow m n' M) = Mpow m (n + n') M.
Proof.
intros.
induction n.
- 
simpl.
rewrite M_ID_equiv_M1.
rewrite Mmult_one_l; auto.
-
simpl.
rewrite <- IHn.
rewrite <- Mmult_assoc.
rewrite <- Mmult_assoc.
f_equal.
apply Mpow_comm.
Qed.


Lemma Mpow_Sn_l (m n: nat) (M: @matrix C m m) :
 Mmult M (Mpow m n M) = Mpow m (S n) M.
Proof.
unfold Mpow; fold Mpow.
apply Mpow_comm.
Qed.



Lemma Mpow_mult_vec_swap (m n: nat) (M: @matrix C m m) (V: @matrix C m m) :
  Mmult M (Mmult (Mpow m n M) V) =
  Mmult (Mmult (Mpow m n M) M) V.
Proof.
induction n.
- 
simpl; auto.
rewrite M_ID_equiv_M1.
rewrite Mmult_one_l.
rewrite Mmult_one_l; auto.
-
unfold Mpow; fold Mpow.
rewrite <- IHn.
rewrite <- Mpow_comm.
rewrite <- Mmult_assoc.
rewrite <- Mmult_assoc.
f_equal.
rewrite Mmult_assoc.
rewrite  Mpow_comm.
rewrite  Mmult_assoc; auto.
Qed.


(* for diagonal D, (P D Pinv)^n = P D^n Pinv *)
Lemma Matrix_pow (m n: nat) (M: @matrix C m m) :
  forall P Pinv D : (matrix m m ),
  Mmult P Pinv = Mone -> 
  Mmult Pinv P = Mone -> 
  diag_pred m D = True -> 
  Mmult P (Mmult D Pinv) = M -> 
  Mpow m n M = Mmult P (Mmult (Mpow m n D) Pinv).
Proof.
intros.
induction n.
- simpl. replace (M_ID m) with (@Mone C_Ring m). rewrite Mmult_one_l. 
rewrite H; auto. symmetry. 
simpl; auto.
replace (M_ID m) with (@Mone C_Ring m); rewrite <- M_ID_equiv_M1; auto.
- unfold Mpow; fold Mpow.
  rewrite IHn. rewrite <- H2. 
  rewrite <- Mmult_assoc; auto.
  rewrite <- Mmult_assoc; auto.
  replace (@Mmult C_Ring m m m Pinv
          (@Mmult C_Ring m m m P
             (@Mmult C_Ring m m m D Pinv))) with
  (@Mmult C_Ring m m m (@Mmult C_Ring m m m Pinv P)
             (@Mmult C_Ring m m m D Pinv)).
  rewrite H0.
  rewrite Mmult_one_l. f_equal.
  repeat rewrite Mmult_assoc; auto.
  repeat rewrite Mmult_assoc; auto.
Qed.


Fixpoint Cpow (c: C) (n : nat) :=
  match n with 
    | 0 => C1 
    | S n' => Cmult c (Cpow c n') 
  end
.

Lemma Cpow_comm (a : C) (n : nat) :
  (a * Cpow a n)%C =  (Cpow a n * a)%C.
Proof.
destruct a, Cpow. 
cbv [Cmult fst snd].
apply pair_equal_spec; split; try nra.
Qed.

Lemma Mpow_diag_is_diag (n m : nat) (D: @matrix C m m) :
  diag_pred m D -> 
(diag_pred m (Mpow m n D)).
Proof.
intros.
induction n.
-
simpl.
apply M_ID_diag.
-
unfold Mpow; fold Mpow.
pose proof Matrix_diag_mult_diag m (Mpow m n D) D (@Mmult C_Ring m m m (Mpow m n D) D)
   IHn H eq_refl; auto.
Qed.


(* for diagonal D, D^n is coeff matrix with components d_{ii}^n *)
Lemma diag_mat_pow (m n: nat) (M: @matrix C m m) :
  forall D : (matrix m m ),
  diag_pred m D -> 
  Mpow m n D = @mk_matrix C m m (fun i j => 
      if i =? j then Cpow (@coeff_mat C m m Hierarchy.zero D i j) n else C0).
Proof.
intros.
induction n.
- 
simpl. unfold M_ID; auto.
-
assert (diag_pred m (Mpow m n D)) by (apply Mpow_diag_is_diag; auto).
unfold Mpow; fold Mpow.
rewrite IHn.
set ( D' :=
(@mk_matrix C m m
     (fun i j : nat =>
      if i =? j
      then Cpow (@coeff_mat C m m (@zero C_AbelianGroup) D i j) n
      else C0))).
replace (@Mmult C_Ring m m m D' D) with 
(@mk_matrix C m m
     (fun i j : nat =>
      if i =? j
      then (Cmult (@coeff_mat C  m m (@zero C_AbelianGroup) D' i j) 
        (@coeff_mat C m m (@zero C_AbelianGroup) D i j)) 
      else C0)).
unfold D'.
apply mk_matrix_ext => i j Hi Hj.
rewrite coeff_mat_bij; try lia.
destruct eqb.
unfold Cpow. fold Cpow; rewrite Cpow_comm; auto.
auto.
assert (diag_pred m D').
unfold diag_pred.
subst D'.
intros.
rewrite coeff_mat_bij; try lia.
destruct H1 as (A & B & C).
apply Nat.eqb_neq in C.
destruct eqb; try discriminate; cbv [C0]; auto.
pose proof Matrix_diag_mult m D' D (@Mmult C_Ring m m m D' D) H1 H eq_refl. 
apply mk_matrix_ext => ii jj Hii Hjj.
assert (Hyp: (ii = jj)%nat \/ (ii <> jj)%nat) by lia; destruct Hyp.
+
pose proof Nat.eqb_eq ii jj. 
destruct H4. specialize (H5 H3).
destruct eqb; try discriminate; subst.
assert ( (jj = 0)%nat \/ (jj <> 0)%nat) by lia.
destruct H3.
*
subst.
assert (A: (0 <= 1)%nat) by lia;
assert (B: (0 <= pred m)%nat) by lia;
pose proof
  @sum_n_m_Chasles C_Ring (fun l : nat =>
   @mult C_Ring (@coeff_mat C_Ring m m (@zero C_Ring) D' 0 l)
     (@coeff_mat C_Ring m m (@zero C_Ring) D l 0))
  0 0 (pred m) A B.
unfold sum_n.
rewrite H3; clear H3.
symmetry.
match goal with |- context [plus ?a ?b = _] =>
  assert (b = zero)
end.
-- 
unfold diag_pred in *.
pose proof (@sum_n_m_ext_loc C_Ring
  (fun l : nat =>
   @mult C_Ring (@coeff_mat C_Ring m m (@zero C_Ring) D' 0 l)
     (@coeff_mat C_Ring m m (@zero C_Ring) D l 0))
(fun _ : nat => zero) 1 (pred m)) as C.
rewrite C; clear  C.
rewrite sum_n_m_const_zero; auto.
intros k Hk.
assert (Hjk: (0 < m)%nat /\ (k < m)%nat /\ (0 <> k)%nat ) by lia.
specialize (H1 0%nat k Hjk); rewrite H1.
rewrite mult_zero_l; auto.
--
rewrite H3.
rewrite sum_n_n.
rewrite plus_zero_r.
unfold mult, Ring.mult; simpl; auto.
*
assert (Ha: (0<=S(pred jj))%nat) by lia.
assert (Hb: (pred jj <=  pred m)%nat) by lia.
pose proof
  @sum_n_m_Chasles C_Ring (fun l : nat =>
   @mult C_Ring (@coeff_mat C_Ring m m (@zero C_Ring) D' jj l)
     (@coeff_mat C_Ring m m (@zero C_Ring) D l jj ))
  0 (pred jj) (pred m) Ha Hb as Hc.
unfold sum_n.
rewrite Hc; clear Hc.
symmetry.
match goal with |- context [plus ?a ?b = _] =>
  assert (a = zero)
end.
--
unfold diag_pred in *.
pose proof (@sum_n_m_ext_loc C_Ring
  (fun l : nat =>
   @mult C_Ring (@coeff_mat C_Ring m m (@zero C_Ring) D' jj l)
     (@coeff_mat C_Ring m m (@zero C_Ring) D l jj))
(fun _ : nat => zero) 0 (pred jj)) as C.
rewrite C; clear  C.
rewrite sum_n_m_const_zero; auto.
intros k Hk.
assert (Hjk: ( jj < m)%nat /\ (k < m)%nat /\ ( jj <> k)%nat ) by lia.
specialize (H1 jj k Hjk); rewrite H1.
rewrite mult_zero_l; auto.
--
rewrite H6.
rewrite plus_zero_l.
replace (S (pred jj)) with jj by lia.
clear Ha; clear Hb.
assert (Ha: (jj <= S jj)%nat) by lia.
assert (Hb: (jj <= pred m)%nat) by lia.
pose proof
  @sum_n_m_Chasles C_Ring (fun l : nat =>
   @mult C_Ring (@coeff_mat C_Ring m m (@zero C_Ring) D' jj l)
     (@coeff_mat C_Ring m m (@zero C_Ring) D l jj ))
  jj jj (pred m)  Ha Hb as Hc.
unfold sum_n.
rewrite Hc; clear Hc.
match goal with |- context [plus ?a ?b = _] =>
  assert (b = zero)
end.
++
unfold diag_pred in *.
pose proof (@sum_n_m_ext_loc C_Ring
  (fun l : nat =>
   @mult C_Ring (@coeff_mat C_Ring m m (@zero C_Ring) D' jj l)
     (@coeff_mat C_Ring m m (@zero C_Ring) D l jj))
(fun _ : nat => zero) (S jj) (pred m)) as C.
rewrite C; clear  C.
rewrite sum_n_m_const_zero; auto.
intros k Hk.
assert (Hjk: ( jj < m)%nat /\ (k < m)%nat /\ ( jj <> k)%nat ) by lia.
specialize (H1 jj k Hjk); rewrite H1.
rewrite mult_zero_l; auto.
++
rewrite H7; clear H7.
rewrite plus_zero_r.
rewrite sum_n_n.
unfold mult, Ring.mult; simpl; auto.
+
pose proof (@sum_n_m_ext_loc C_Ring
(fun l : nat => mult (@coeff_mat C_Ring m m (@zero C_Ring) D' ii l) (@coeff_mat C_Ring m m (@zero C_Ring) D l jj)) 
(fun _ : nat => zero) 0 (pred m)).
unfold sum_n.
rewrite H4; clear H4.
*
apply Nat.eqb_neq in H3.
destruct eqb; try discriminate.
rewrite sum_n_m_const_zero.
cbv [C0] ; auto.
*
unfold diag_pred in *. 
intros.
assert (HK: ii <> k \/ jj <> k) by lia; destruct HK as [A | B].
--
assert ((ii < m)%nat /\ (k < m)%nat /\ ii <> k) as Hk1 by lia. 
specialize (H1 ii k Hk1); rewrite H1; rewrite mult_zero_l; auto.
--
assert ((k < m)%nat /\ (jj < m)%nat /\ k <> jj) as Hk2 by lia.
specialize (H k jj Hk2); rewrite H; rewrite mult_zero_r; auto.
Qed.



Close Scope R_scope. 
