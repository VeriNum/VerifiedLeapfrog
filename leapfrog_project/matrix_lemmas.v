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


(* matrix transpose *)
Definition matrix_conj_transpose (n:nat) (M: @matrix C n n) := 
  mk_matrix n n (fun i j => Cconj (coeff_mat Hierarchy.zero M j i))
.


(* multiply a vector by a complex number *)
Definition coeff_mult (a : C) (n:nat) (V: @matrix C n 1%nat) : @matrix C n n :=
  @mk_matrix C n n (fun i j => 
      Cmult a (@coeff_mat C n 1%nat Hierarchy.zero V i j))
.


(* complex zero matrix and zero vector *)
Definition M0 (n:nat) : @matrix C n n := Mzero. 
Definition V0 (n:nat) : @matrix C n 1%nat := mk_matrix n 1%nat (fun _ _ => C0)
.


(* identity *)
Definition M_ID (n:nat) : @matrix C n n := 
  mk_matrix n n (fun i j => if (eqb i j) then C1 else C0)
.


(* ID MATRIX & ZERO MATRIX LEMMAS*)
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
(* end ID and 0 matrix lemmas *)



(*******************)
(* DIAGONAL MATRICES *)

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




(* COMPLEX NUMBER LEMMAS *)
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
(* end complex number lemmas *)


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

Close Scope R_scope. 
