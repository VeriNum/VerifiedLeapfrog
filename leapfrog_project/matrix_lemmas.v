(** matrix_lemmas.v:  Definitions and lemmas for the error analysis
  of ODE systems using matrices.
 Copyright (C) 2021-2022 and Ariel Kellison.
*)


From Coq Require Import ZArith Reals Psatz.
From Coq Require Import Arith.Arith.
Require Import real_lemmas lf_harm_real.
Require Import Init.Nat Arith.EqNat.

From Coq Require Import ssreflect. 
From Coquelicot Require Import Coquelicot.
Require Import Interval.Tactic.

Set Bullet Behavior "Strict Subproofs". 


Require Import Coq.Logic.FunctionalExtensionality.


Definition C0: C := (0,0).
Definition C1: C := (1,0).

(* the transpose of a matrix *)
Definition matrix_conj_transpose (n:nat) (M: @matrix C n n) := 
  mk_matrix n n (fun i j => Cconj (coeff_mat Hierarchy.zero M j i)).


(* complex matrix and vector with of zeros *)

Definition M0 (n:nat) : @matrix C n n := Mzero. 
Definition V0 (n:nat) : @matrix C n 1%nat := mk_matrix n 1%nat (fun _ _ => C0).

Definition M_ID (n:nat) : @matrix C n n := 
  mk_matrix n n (fun i j => if (eqb i j) then C1 else C0).

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



Lemma Mcong_transpose_zero (n: nat) (M: @matrix C n n) :
matrix_conj_transpose n M = (M0 n) <-> M = (M0 n).
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
forall i j, @coeff_mat C n n (@zero C_AbelianGroup) (M0 n) i j = 0.
Admitted.


Definition diag_pred (n: nat) (M: @matrix C n n) := 
  forall i j, (i < n)%nat /\ (j < n)%nat /\ (i <> j)%nat -> (@coeff_mat C n n Hierarchy.zero M i j) = zero.

Definition vec_to_diag (n:nat) (V: @matrix C n 1%nat) : @matrix C n n :=
  (@mk_matrix C n n (fun i j => if (eqb i j) then 
      (@coeff_mat C n 1%nat Hierarchy.zero V i 0) else C0)).  

Definition coeff_mult (a : C) (n:nat) (V: @matrix C n 1%nat) : @matrix C n n :=
  @mk_matrix C n n (fun i j => 
      Cmult a (@coeff_mat C n 1%nat Hierarchy.zero V i j)).

(* V has columns that are eigenvectors of M, and M has elements that
  are the corresponding eigenvalues *)
Definition eigenval_pred (n:nat) (M V: @matrix C n n) (L: matrix n 1%nat) : Prop := 
  let LAM:= vec_to_diag n L in 
  (Mmult M V) = (Mmult V LAM) /\ 
  (forall j, (j < n)%nat -> (exists i, (i < n)%nat /\ ((@coeff_mat C n n Hierarchy.zero V i j) <> 0 ))) /\
  (Mmult M V = M0 n <-> M = M0 n)
.  


Definition eigenvalues (n:nat) (M V: @matrix C n n) 
  (s: sig (eigenval_pred n M V)): (@matrix C n 1%nat) := proj1_sig s. 

Definition eigenvectors (n:nat) (M: @matrix C n n) (L: matrix n 1%nat) 
  (s: sig (fun x => (eigenval_pred n M x L))) : (@matrix C n n):= proj1_sig s.


Definition two_norm_pred (n:nat) (M MTM V: @matrix C n n) (L: matrix n 1%nat) (mod_lambda_max : R) := 
  MTM = Mmult (matrix_conj_transpose n M) M  /\
  eigenval_pred n MTM V L /\
  (forall i,  (i < n)%nat -> Cmod (coeff_mat Hierarchy.zero L i 0) <= mod_lambda_max) /\ 
  (exists i,  (i < n)%nat /\ mod_lambda_max = Cmod (coeff_mat Hierarchy.zero L i 0)).

Definition two_norm_sqr (n:nat) (M MTM V: @matrix C n n) (L: matrix n 1%nat):= 
  {l : R | two_norm_pred n M MTM V L l}.


(* two_norm_sqr satifies matrix norm properties *)
Lemma two_norm_sqr_pos (n:nat) (M MTM V: @matrix C n n) (L: matrix n 1%nat) :
  forall (l : two_norm_sqr n M MTM V L),
  0 <= proj1_sig l.
Proof.
intros.
destruct l. simpl.
unfold two_norm_pred in t; destruct t as (A & B & C & D).
destruct D as (i & D1 & D2).
subst.
apply Cmod_ge_0.
Qed.


Lemma Czero_sqs (x : C) :
  0<= Cmod x /\ Cmod x <= 0 -> Cmod x = 0.
Proof.
unfold Cmod.
intros.
destruct H.
apply Rle_antisym; auto.
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
rewrite <- H0; auto.
Qed.



Lemma Cmult_integral (a b : C):
  Cmult a b = C0 -> a = C0 \/ b = C0.
Admitted.


Lemma vec_to_diag_pred (n: nat) (L: matrix n 1%nat) :
  diag_pred n (vec_to_diag n L).
Proof.
unfold diag_pred, vec_to_diag; intros.
rewrite coeff_mat_bij; try lia.
destruct H as (A & B & C).
apply Nat.eqb_neq in C.
destruct eqb; auto; try discriminate.
Qed.



Lemma two_norm_M0 (n : nat) (V: @matrix C n n) (L: matrix n 1%nat):
  forall (l : two_norm_sqr n (M0 n) (M0 n) V L),
  0 = proj1_sig l.
Proof.
intros.
destruct l; simpl.
destruct t as (A & B & C & D).
destruct B as (B1 & B2 & B3).
pose proof 
  Mmult_diagonal_implies n V (vec_to_diag n L) Mzero (vec_to_diag_pred n L).
destruct D as (j &Hj &D2); subst.
specialize (B2 j Hj).
destruct B2 as (i &Hi & HV).
replace (Mmult (M0 n) V) with (@Mzero C_Ring n n) in B1 by (symmetry; apply Mmult_Mzero_l). 
assert ((i < n)%nat /\ (j < n)%nat ) by lia.
symmetry in B1.
specialize (H B1 i j H0). 
assert (@coeff_mat C_Ring n n zero Mzero i j = C0) by (apply M0_coeff_zero).
rewrite H1 in H.
symmetry in H.
pose proof (  Cmult_integral (coeff_mat zero V i j) (coeff_mat zero (vec_to_diag n L) j j) H) as P.
destruct P; try contradiction.
unfold vec_to_diag in H2.
rewrite coeff_mat_bij in H2; try lia. 
replace 0 with (Cmod C0) by (apply Cmod_0).
f_equal.
rewrite <- H2.
pose proof Nat.eqb_eq j j; destruct H3.
specialize (H4 eq_refl).
destruct eqb; try discriminate; auto.
Qed.


(* definiteness of the two-norm for invertible matrices *) 
Lemma two_norm_sqr_definite (n:nat) (M MTM V: @matrix C n n) (L: matrix n 1%nat) :
  (forall i, (@coeff_mat C n 1%nat Hierarchy.zero L i 0) <> C0) (* M is invertible iff all elements of L are non-zero *) -> 
  forall (l : two_norm_sqr n M MTM V L),
  0 = proj1_sig l <-> (forall i j, (i < n)%nat /\ (j < n)%nat -> (@coeff_mat C n n Hierarchy.zero M i j) = 0).
Proof.
intros. 
intros; split; intros.
- 
destruct l.
simpl in H0; subst.
destruct t as (A & B & C & D).
destruct D as (ii & Hii & D).
symmetry in D.
apply Cmod_eq_0 in D.
specialize (H ii).
rewrite D in H.
contradiction.
-
apply eq_M0_iff in H0. subst.
assert (MTM = M0 n).
+ destruct l; destruct t as (A & _).
replace (matrix_conj_transpose n (M0 n)) with (M0 n) in A by
  (symmetry; rewrite Mcong_transpose_zero;auto).
rewrite Mmult_Mzero_l in A; subst; auto.
+
subst.
apply two_norm_M0.
Qed.



Lemma two_norm_homogeneous (n:nat) (a : R) (M V MTM aV aMTM: @matrix C n n) (L aL: matrix n 1%nat) :
  forall (l  : two_norm_sqr n M  MTM   V  L),
  forall a,   
  let aM := mk_matrix n n (fun i j => Cmult (a,0) (@coeff_mat C n n Hierarchy.zero M i j)) in
  forall (la : two_norm_sqr n aM aMTM aV aL),
  a * proj1_sig l = proj1_sig la.
Proof.
intros.
Admitted.
(*
Lemma two_norm_triang_ineq (n:nat) (M1 M2 V12 V1 V2: @matrix C n n) (L12 L1 L2: matrix n 1%nat) :
  forall p1 p2 p3 p4 p5 p6,
    Cmod (two_norm_sqr n (Mplus M1 M2) V12 L12 p1 p2) <= 
      Cmod (two_norm_sqr n M1 V1 L1 p3 p4) + Cmod (two_norm_sqr n M2 V2 L2 p5 p6).
Proof.
intros.
Admitted.

Lemma two_norm_submultiplicative (n:nat) (M1 M2 V12 V1 V2: @matrix C n n) (L12 L1 L2: matrix n 1%nat) :
  forall p1 p2 p3 p4 p5 p6,
    Cmod (two_norm_sqr n (Mmult M1 M2) V12 L12 p1 p2) <= 
      Cmod (two_norm_sqr n M1 V1 L1 p3 p4) * Cmod (two_norm_sqr n M2 V2 L2 p5 p6).
Proof.
intros.
Admitted.


Fixpoint Mpow (m n: nat) (M: @matrix C n n): matrix n n:=  
  match m with
    | 0 => (M_ID n) 
    | S m' => Mmult (Mpow m' n M) M  
  end.

Lemma M_Id_mult_l (m n : nat) (x : @matrix C m n): 
       Mmult (M_ID m) x = x .
Proof.
Admitted.

Lemma M_Id_mult_r (m n : nat) (M : @matrix C m n): 
       Mmult M (M_ID n) = M .
Proof.
pose proof @Mmult_one_r C_Ring.

rewrite <- (mk_matrix_bij zero M).
apply mk_matrix_ext => /= i j Hi Hj.
destruct n; simpl.
- 
Admitted.

Lemma Matrix_pow (m n: nat) (M: @matrix C n n) :
  forall P Pinv D : (matrix n n),
  Mmult P Pinv = (M_ID n) -> 
  Mmult Pinv P = (M_ID n) -> 
  diag_pred n D = True -> 
  Mmult P (Mmult D Pinv) = M -> 
  Mpow m n M = Mmult P (Mmult (Mpow m n D) Pinv).
Proof.
intros.
induction m.
- simpl. rewrite M_Id_mult_l. rewrite H; auto.
- unfold Mpow; fold Mpow.
  rewrite IHm. rewrite <- H2. 
  rewrite <- Mmult_assoc; auto.
  rewrite <- Mmult_assoc; auto.
  replace (@Mmult C_Ring n n n Pinv
          (@Mmult C_Ring n n n P
             (@Mmult C_Ring n n n D Pinv))) with
  (@Mmult C_Ring n n n (@Mmult C_Ring n n n Pinv P)
             (@Mmult C_Ring n n n D Pinv)).
  rewrite H0.
  rewrite M_Id_mult_l. f_equal.
  repeat rewrite Mmult_assoc; auto.
  repeat rewrite Mmult_assoc; auto.
Qed.

Lemma Matrix_diag_pow_eig (m n: nat) (M: @matrix C n n):
  diag_pred n M ->
  forall (i: nat),
  ((i <= n)%nat -> Cmod (coeff_mat Hierarchy.zero M i 0) =  1) -> 
  (forall (m : nat),
  Cmod (coeff_mat Hierarchy.zero (Mpow m n M) i 0) =  1).
Proof.
intros. 
Admitted.

Fixpoint Cpow (n:nat) (c : C): C:=
  match n with  
  | 0 => C1
  | S n' => Cmult c (Cpow n' c)
  end.






Lemma Matrix_diag_pow (m n: nat) (M: @matrix C n n):
  diag_pred n M ->
  (Mpow m n M) = 
  mk_matrix n n (fun i j => if (eqb i j) then Cpow m (@coeff_mat C n n Hierarchy.zero M i j) else C0).
Proof.
intros.
unfold diag_pred in H.
(*destruct H.
rewrite H.
induction m.
- simpl. 
unfold Mone.
f_equal.
unfold M_ID; auto.
- unfold Mpow. fold Mpow.
rewrite IHm. *)
(* diag matrix times diag matrix is diag *)
(* Prove that the diag matrix result exists, 
substitute it *)
(* the resulting matrix should be defined as just 
diag values times each other *) 
 
Admitted.

Lemma diag_matrix_pow_eq_eigen_pow (m n: nat) (M V: @matrix C n n) (L: matrix n 1%nat) :
  diag_pred n M ->
  forall (i: nat),
  forall (m : nat),
  forall p1 p2 p3 p4,
  Cmod (two_norm_sqr n (Mpow m n M) V L p1 p2) =  (Cmod (max_eigenvalue n M V L p3 p4)) ^ m.
Proof.
intros.
unfold two_norm_sqr.
unfold diag_pred in H.
Admitted.

Lemma dig_mat_is_eigen (n: nat) (M: @matrix C n n):
  diag_pred n M ->
  forall (V: (@matrix C  n n)), 
  forall p,
    let D:= (@mk_matrix C n n (fun i j => if (eqb i j) then 
      (@coeff_mat C n 1%nat Hierarchy.zero (eigenvalues n M V p) i 0) else C0)) in M = D.
Proof.
intros.
subst D.
destruct p.
unfold eigenval_pred in e.
unfold diag_pred in H. (*
inversion H.
(* subst M is diagonal *)
subst.
f_equal. 
apply functional_extensionality; intros.
apply functional_extensionality; intros.
destruct eqb; auto.
f_equal.
unfold eigenvalues.
simpl.*)
Admitted.

(*
Lemma two_norm_unit_diag (m n: nat) (M: @matrix C n n):
  diag_pred n M ->
  forall (i: nat), (i <= n)%nat ->
  (forall (m : nat),
  Cmod (coeff_mat Hierarchy.zero (Mpow m n M) i 0) =  1) -> 
  forall V L MTM,  
  MTM = (Mmult (matrix_conj_transpose n M) M) -> 
  forall p1 p2,
  (eigenvalues n M V p)
  two_norm_sqr n M V L p1 p2 = 1.
Proof.
intros.
unfold two_norm_sqr, max_eigenvalue.
pose proof dig_mat_is_eigen n M H V.
(* diagonal matrices have eigenvalues on diag *) 
Admitted.


*)

*)


Close Scope R_scope. 
