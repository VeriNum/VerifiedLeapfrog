From Coq Require Import ZArith Reals Psatz.
From Coq Require Import Arith.Arith.
From Coquelicot Require Import Coquelicot.
From Flocq3 Require Import Core.

Require Import vcfloat.RAux.

Require Import IntervalFlocq3.Tactic.

Import Coq.Logic.FunctionalExtensionality.

Set Bullet Behavior "Strict Subproofs". 


Lemma Rabs_triang_aux : 
  forall a b c : R,
  Rabs a + Rabs b <= c ->
  Rabs( a + b ) <= c.
Proof.
intros.
pose proof Rabs_triang a b.
pose proof Rle_trans _ _ _ H0 H; assumption.
Qed.


Lemma Rabs_triang_aux2 : 
  forall a b c d : R,
  Rabs a + Rabs b + Rabs c <= d ->
  Rabs (a + b) + Rabs c <= d.
Proof.
intros.
assert (Rabs (a + b) + Rabs c <= Rabs a + Rabs b + Rabs c).
pose proof Rcomplements.Rle_minus_r 
  (Rabs (a + b)) (Rabs a + Rabs b + Rabs c) (Rabs c); destruct H0. 
try apply H0; field_simplify; apply Rabs_triang.
try pose proof Rle_trans _ _ d H0 H; assumption.
Qed.

Lemma Rabs_triang_aux3 : 
  forall a b c x y z : R,
  Rabs a <= x ->
  Rabs b <= y ->
  Rabs c <= z ->
  Rabs a + Rabs b + Rabs c <= x + y +z.
Proof. intros; nra. Qed.


Lemma Rabs_triang_aux4 : 
  forall x xp v vp : R,
  Rabs ( x^2 + v^2 - (xp^2 + vp^2)) <=
  Rabs ( x + xp) * Rabs ( x - xp) + 
  Rabs ( v + vp) * Rabs ( v - vp). 
Proof.
intros.
replace (x ^ 2 + v ^ 2 - (xp ^ 2 + vp ^ 2))
with ( (x ^ 2 - xp ^ 2) + (v ^ 2 - vp^2)) by nra.
eapply Rle_trans.
+
match goal with |- context[ Rabs (?a + ?b)<= _] =>
apply Rabs_triang 
end.
+
repeat match goal with |- context[ (?a^2 - ?b^2) ] =>
replace (a^2 - b^2) with ((a+b)*(a-b)) by nra
end.
repeat rewrite Rabs_mult. nra.
Qed.

Lemma Rabs_le_aux: 
  forall w x y z a b c d : R,
  Rabs w <= a ->
  Rabs x <= b ->
  Rabs y <= c ->
  Rabs z <= d -> 
  Rabs w * Rabs x + Rabs y * Rabs z <= a * b + c * d.
Proof.
intros.
eapply Rle_trans.
eapply Rplus_le_compat_r.
eapply Rmult_le_compat_r. apply Rabs_pos. apply H. 
eapply Rle_trans.
eapply Rplus_le_compat_r.
eapply Rmult_le_compat_l. 
eapply Rle_trans. apply Rabs_pos. apply H. apply H0.
eapply Rplus_le_compat_l.
eapply Rle_trans.
eapply Rmult_le_compat_l. 
apply Rabs_pos. apply H2. 
eapply Rmult_le_compat_r.
eapply Rle_trans.
apply Rabs_pos. apply H2. assumption. 
Qed.


Lemma powerRZ_pos_sub2: 
forall (x : R) (n m : positive),
     x <> 0 ->
     x ^ Pos.to_nat n * / x ^ Pos.to_nat m = powerRZ x (Z.pos_sub n m).
Proof. 
intros; symmetry; apply powerRZ_pos_sub; auto. Qed.


Lemma mul_powerRZ (a:R) (n:Z) :
 a / powerRZ 2 n = a * powerRZ 2 (-n).
Proof.
replace (powerRZ 2 (- n)) with 
(1 / powerRZ 2 n). 
nra.
(apply neg_powerRZ); nra.
Qed.

Lemma Rminus_dist: 
  forall x y z : R,
  x - (y +z) = x - y - z.
Proof.
intros;nra.
Qed.


Lemma abs_lt:
 forall a b d: R,
 Rabs b <= d ->
 Rabs a - d <= Rabs a - Rabs b.
Proof.
intros; nra. 
Qed. 

Lemma abs_mul:
 forall a b: R,
 0 <= a ->
 Rabs (a * b) = a * Rabs b.
Proof.
intros; pose proof Rabs_mult a b. rewrite -> H0. 
pose proof Rabs_pos_eq a H; auto; nra.  
Qed. 

Lemma abs_mul2:
 forall a b: R,
 0 <= b ->
 Rabs (a * b) =  b * Rabs a.
Proof.
intros; pose proof Rabs_mult a b. rewrite -> H0. 
pose proof Rabs_pos_eq b H. auto; nra.  
Qed. 

Lemma rabs_mul_t:
forall u a b c d: R ,
u <= a * Rabs(b) + c -> Rabs(b) <= d -> 0 <a -> u <= a * d + c.
Proof.
intros. nra.
Qed.

Lemma del_eps_reduce1 : 
forall a del eps: R,
a - (a*(1+del)+eps) = -a*del - eps.
Proof.
intros; field_simplify; reflexivity.
Qed.

Lemma del_eps_reduce2 : 
forall a c d d' del eps: R,
a*(c + d) - a*((c + d')*(1+del)+eps) = a*(d - d') - a*(c + d')*del - a* eps.
Proof.
intros; field_simplify; reflexivity.
Qed.

Lemma Rabs_le_inv2 (x y :  R):
0 <= Rabs x <= y -> - y <= x <= y.
Proof.
intros.
assert (Rabs x <= y) by nra;
pose proof Rabs_le_inv x y H0; assumption.
Qed.

Lemma error_reduce a b c d :
a - (b * (1 + c) + d) = 
(a - b )  - b * c - d.
Proof.
intros.
nra.
Qed.

Lemma Rabs_mult_le_l a b c :
 0<= a ->
  Rabs b <= c -> 
  Rabs(a*b) <= a * c.
Proof.
intros.
assert (a * Rabs b <= a* c) by nra.
assert (Rabs (a * b) <= a * Rabs b). 
rewrite Rabs_mult. rewrite Rabs_pos_eq; nra.
eapply Rle_trans. apply H2. auto.
Qed.


Lemma Rle_minus_l_2 : 
  forall a b c : R, a - b <= c <-> a <= b + c . 
Proof.
intros. split. nra. nra. Qed.

Lemma Rle_plus : 
  forall a b  : R, 0<= a -> 0 <=b -> 0 <= a + b. 
Proof.
intros. nra. Qed.

Lemma Rle_mult : 
  forall a b  : R, 0<= a -> 0 <=b -> 0 <= a * b. 
Proof.
intros. nra. Qed.

Lemma Rabs_le_minus_mul : 
forall a b x y : R,
0 <= a -> 0 <= b -> 
Rabs x <= 1 -> Rabs y <= 1 ->
Rabs(a * x - b * y) <= a + b.
Proof.
intros.
eapply Rle_trans.
eapply Rabs_triang.
rewrite Rabs_Ropp.
repeat (rewrite abs_mul; try auto).
eapply Rplus_le_compat; nra.
Qed.


Lemma sqr_plus_pos a b:  
0 <= a ^ 2 + b ^ 2.
Proof.
nra.
Qed.

Lemma sqrt_plus_pos a b:  
0 <= sqrt a  + sqrt b .
Proof.
apply Rle_plus; apply sqrt_pos. 
Qed.

Lemma sqrt_triang_ineq a b:
0 <= a -> 
0 <= b ->
sqrt ( a + b ) <= sqrt(a) + sqrt(b).
Proof.
intros. 
assert (a + b  <= (sqrt a + sqrt b)^2).
simpl. field_simplify. 
repeat rewrite pow2_sqrt; auto.
rewrite Rplus_assoc.
apply Rplus_le_compat_l.
rewrite Rplus_comm. 
apply Rle_minus_l_2. field_simplify.
eapply Rle_trans.
2: apply Rmult_le_compat_l.
2: eapply Rle_trans.
3: apply Rmult_le_compat_l; try nra; try auto.
3: apply sqrt_pos; try nra.
3: apply sqrt_pos; try nra.
nra. nra.
apply sqrt_le_1 in H1; try nra.
rewrite sqrt_pow2 in H1; try nra.
apply sqrt_plus_pos.
Qed.


Lemma square_pos x:
0 <= x^2.
Proof.
pose proof Rle_0_sqr x.
unfold Rsqr in H.
unfold pow. rewrite Rmult_1_r.  
apply H.
Qed.



Lemma Rmax_pos a b :
0 <=a -> 
0<= b ->
0<= Rmax a b. 
Proof.
intros.
eapply Rle_trans.
apply H.
apply Rmax_l.
Qed.

Lemma Rmax_sqr a b :
0 <=a -> 
0<= b ->
a^2 + b^2<= 2 * Rmax a b ^2. 
Proof.
intros.
cbv [Rmax]. destruct Rle_dec.
+ eapply Rle_trans.
eapply Rplus_le_compat_r.
assert ( a ^2 <= b ^2) by nra.
apply H1. nra.
+ eapply Rle_trans.
eapply Rplus_le_compat_l.
assert ( b ^2 <= a ^2) by nra.
apply H1. nra. 
Qed.

Lemma Rabs_pos_le a b:
0 <= a -> 
0 <= b -> 
a <= b -> Rabs(a) <= Rabs(b).
Proof.
intros.
apply Rabs_pos_eq in H0.
apply Rabs_pos_eq in H.
rewrite H, H0. 
auto.
Qed.

Lemma Rabs_sqr_le a :
Rabs(a ^ 2) = Rabs(a) ^2.
Proof.
intros.
replace (a ^ 2) with ( a * a) by nra.
rewrite Rabs_mult.
nra.
Qed.

Definition Rprod : Type := R * R.
Declare Scope Rprod.
Delimit Scope Rprod with Rprod.
Bind Scope Rprod with Rprod.
  
Definition Rprod_minus (x y : Rprod) : Rprod :=
  (Rminus (fst x) (fst y), Rminus (snd x) (snd y)).

Definition Rprod_plus (x y : Rprod) : Rprod :=
  (Rplus (fst x) (fst y), Rplus (snd x) (snd y)).

Definition Rprod_norm (x : Rprod) : R  :=
  sqrt ( fst x ^ 2 +  snd x ^ 2).

Notation " L1 - L2 " := (Rprod_minus L1 L2) (at level 50, left associativity) : Rprod.

Notation " L1 + L2 " := (Rprod_plus L1 L2) (at level 50,  left associativity) : Rprod.

Notation "∥ L ∥" := (Rprod_norm L%Rprod) (at level 10, L at level 90) : R_scope.
Notation "∥·∥" := Rprod_norm (only parsing) : R_scope.

Lemma Rprod_triang_ineq x y: ∥ x + y ∥ <=  ∥ x ∥ + ∥ y ∥.
Proof.
destruct x, y.
unfold Rprod_plus, Rprod_norm, fst, snd.
assert ((r + r1) ^ 2 + (r0 + r2) ^ 2 <= 
  (sqrt (r ^ 2 + r0 ^ 2) + sqrt (r1 ^ 2 + r2 ^ 2))^2).
replace ((sqrt (r ^ 2 + r0 ^ 2) + sqrt (r1 ^ 2 + r2 ^ 2)) ^ 2)
with (r^2 + r0^2 + r1^2 + r2^2 + 2 * sqrt (r ^ 2 + r0 ^ 2)* sqrt (r1 ^ 2 + r2 ^ 2))
by 
(simpl; field_simplify; 
repeat rewrite pow2_sqrt; repeat nra).
simpl. field_simplify.
repeat rewrite Rplus_assoc.
apply Rplus_le_compat_l.
rewrite Rplus_comm.
repeat rewrite Rplus_assoc.
apply Rplus_le_compat_l.
apply Rplus_le_compat_l.
rewrite Rplus_comm.
repeat rewrite Rplus_assoc.
apply Rplus_le_compat_l.
repeat rewrite Rmult_assoc.
replace (2 * (r * r1) + 2 * (r0 * r2)) with
(2 * ((r * r1) + (r0 * r2))) by nra.
apply Rmult_le_compat_l; try nra.
repeat rewrite Rmult_1_r. 
apply sqrt_cauchy.
apply sqrt_le_1 in H.
rewrite sqrt_pow2 in H; auto.
apply sqrt_plus_pos.
apply sqr_plus_pos.  
rewrite <- Rsqr_pow2.
apply Rle_0_sqr.
Qed.

Lemma Rprod_norm_plus_minus_eq x y z:  ∥ x - y ∥ = ∥ (x - z) + (z - y) ∥.
Proof.
intros.
destruct x, y, z.
unfold Rprod_plus, Rprod_minus, Rprod_norm, fst, snd.
f_equal.
nra.
Qed.


Lemma Rnorm_pos x: 0 <= ∥ x ∥.
Proof.
unfold Rprod_norm.
apply sqrt_pos.
Qed.

Lemma Rprod_plus_assoc :
forall a b c : Rprod,  ( (a+b)+c = a+(b+c) )%Rprod. 
Proof.
intros.
unfold Rprod_plus.
simpl. f_equal; nra.
Qed.

Lemma Rprod_plus_sym :
forall a b : Rprod,  ( a + b = b + a )%Rprod.
Proof.
intros.
unfold Rprod_plus.
f_equal; nra.
Qed.

Lemma sum_pow_mult_l:
  forall a : R,
  forall n : nat,
  a * sum_f 0 n (fun m => a ^ m ) = 
  sum_f 1 (S n) (fun m => a ^ m ).
Proof.
intros.
replace (a * sum_f 0 n (fun m => a ^ m ) )
with 
( sum_f 0 n (fun m => a ^ m * a )).
+ replace (fun m : nat => a ^ m * a) with 
(fun m : nat => a ^ (m+1)).
induction n.
++ unfold sum_f. simpl. nra.
++ set (yy:=sum_f 0 (S n) (fun m : nat => a ^ (m + 1))).
rewrite sum_f_n_Sm. rewrite <- IHn. subst yy.
rewrite sum_f_n_Sm. repeat f_equal. ring. 
apply Nat.le_0_l.
rewrite <- Nat.succ_le_mono.
apply Nat.le_0_l.
++ apply functional_extensionality.
intros. replace (x+1)%nat 
  with (S x) by ring.
simpl; nra.
+  induction n.
++ unfold sum_f. simpl. nra.
++  rewrite sum_f_n_Sm. rewrite IHn.
rewrite sum_f_n_Sm. field_simplify. nra. 
apply Nat.le_0_l. apply Nat.le_0_l.
Qed.

Lemma sum_pow_mult_r : 
  forall a : R,
  forall n : nat,
  sum_f 0 n (fun m => a ^ m ) * a = 
  sum_f 1 (S n) (fun m => a ^ m ).
Proof.
intros.
rewrite Rmult_comm.
apply sum_pow_mult_l.
Qed.

Lemma sum_pow_first :
  forall a : R,
  forall n : nat,
  sum_f 0 (S n) (fun m => a ^ m ) = 
  sum_f 1 (S n) (fun m => a ^ m ) + 1.
Proof.
intros.
induction n. 
+ unfold sum_f. simpl. nra.
+ 
match goal with |-context[?a = ?b]=>
set (yy:= a)
end.
rewrite sum_f_n_Sm.
rewrite Rplus_assoc.
rewrite Rplus_comm.
rewrite Rplus_comm in IHn.
rewrite Rplus_assoc.
rewrite <- IHn.
subst yy.
rewrite sum_f_n_Sm.
rewrite IHn.
field_simplify. nra.
apply Nat.le_0_l.
rewrite <- Nat.succ_le_mono.
apply Nat.le_0_l.
Qed.

Definition error_sum error n: R:=
 match n with 
  | 0 => 0
  | S n' => sum_f 0 n' (fun m => error ^ m )
end.

Lemma error_sum_aux n (er: R):
  error_sum er n + er ^ n = error_sum er (S n).
Proof.
intros.
induction n. 
+  simpl. unfold sum_f. simpl. nra.
+ unfold error_sum.
rewrite sum_f_n_Sm; auto.
apply Nat.le_0_l.
Qed.

Lemma error_sum_aux2 er n:
  er * error_sum er n + 1  = error_sum er (S n).
Proof.
intros.
induction n. 
+  simpl. unfold sum_f. rewrite Rmult_0_r. simpl. nra.
+ unfold error_sum.
rewrite Rmult_comm.
rewrite sum_pow_mult_r.
rewrite sum_pow_first.
nra.
Qed.

Lemma Rmax_mult_le_pos a b:
0 <=a -> 
0 <= b ->  
a * b <= Rmax a b ^2.
Proof.
intros.
cbv [Rmax]. destruct Rle_dec.  
eapply Rle_trans.
apply Rmult_le_compat_r; auto.
apply r. nra.
apply Rnot_le_lt in n.
eapply Rle_trans.
apply Rmult_le_compat_l; auto.
apply Rlt_le in n.
apply n. nra.
Qed.

Lemma Rmax_mult_le_neg  a b:
a <= 0 -> 
b <= 0 ->  
a * b <= Rmin a b ^2.
Proof.
intros.
cbv [Rmin]. destruct Rle_dec.  
eapply Rle_trans.
assert (a * b <= a * a) by nra.
apply H1. nra.
apply Rnot_le_lt in n.
eapply Rle_trans.
assert (a * b <= b * b) by nra.
apply H1. nra.
Qed.

Lemma bounded_one_plus_pow:  
forall x n,
0 <= x ->
(1 + x)^n <= exp ( INR n * x).
Proof.
intros.
induction n.
+ simpl. rewrite Rmult_0_l.
rewrite exp_0; nra.
+ 
rewrite <- tech_pow_Rmult.
eapply Rle_trans.
eapply Rmult_le_compat_l; try nra.
apply IHn.
eapply Rle_trans.
pose proof exp_ineq1_le x.
eapply Rmult_le_compat_r; try nra.
pose proof exp_pos (INR n * x).
apply Rlt_le in H1; auto.
apply H0.
rewrite <- exp_plus.
rewrite S_INR.
apply Req_le.
f_equal.
nra.
Qed.

(* apparently this is already covered by Constant Coq.Reals.PartSum.tech3*)
Theorem geo_series_closed_form:
forall r k ,
r <> 1 ->
sum_f 0 k (fun m => r ^ m ) = (1-(r^(S k)))/(1-r).
Proof.
intros.
induction k.
+ unfold sum_f. simpl. field_simplify. nra. lra. 
+ rewrite sum_f_n_Sm .
++ rewrite IHk.
match goal with|- context [?a/?aa + ?b = _] =>
replace  b with 
((r ^ S k)*(1-r)/(1-r))
end.
field_simplify; try nra.
replace  (- r ^ S k * r) with
(- r ^ S (S k) ).
nra.
simpl. nra.
field_simplify; try nra.
++ apply Nat.le_0_l.
Qed.

Lemma mult_pos : 
forall a b, 0 < a * b -> 0 <= a -> 0 < b.
Proof.
intros; nra.
Qed.

Lemma is_lim_exp_pow: 
forall n ,
is_lim (fun y : R => exp (INR n * y)) 0 1.
Proof.
intros.
induction n.
+ simpl. 
apply (is_lim_ext (fun y : R => exp 0)  (fun y : R => exp (0 * y))).
intros. rewrite Rmult_0_l; auto. 
replace (exp 0) with 1.
apply is_lim_const.
field_simplify. symmetry; (apply exp_0).
+ rewrite S_INR. 
apply (is_lim_ext (fun y : R => exp ((INR n * y + y) )) 
    (fun y : R => exp ((INR n + 1) * y))).
intros. f_equal. nra.
apply ( is_lim_ext (fun y : R => exp (INR n * y) * exp y)  
    (fun y : R => exp ((INR n * y + y) ))).
intros. rewrite <- exp_plus; nra.
pose proof (is_lim_mult (fun x => exp (INR n * x)) (fun x => exp x) 0 1 1 IHn) .
assert (is_lim (fun x : R => exp x) 0 1).
pose proof Lim_exp 0. simpl in H0.
pose proof (Lim_correct) (fun y : R => exp y) 0 (ex_lim_exp 0).
rewrite exp_0 in H0.
rewrite H0 in H1; auto.
assert (ex_Rbar_mult 1 1).
unfold ex_Rbar_mult; nra.
specialize (H H0 H1).
apply (is_lim_ext (fun y : R => (fun x : R => exp (INR n * x)) y * (fun x : R => exp x) y)
    (fun y : R => exp (INR n * y) * exp y)) in H.
simpl in H. rewrite Rmult_1_l in H. apply H.
intros. f_equal.
Qed.

Lemma square_abs :
forall x : R, x ^ 2 = (Rabs x) ^ 2.
Proof.
intros. 
pose proof Rsqr_abs x.
assert (x  ^ 2 = Rsqr x).
unfold Rsqr; nra.
rewrite pow2_abs.
rewrite H0; nra.
Qed.

Lemma sqrt_le : 
forall a b, 
a ^ 2 <= b ->
Rabs a <= sqrt b.
Proof.
intros.
replace b with (sqrt b ^2) in H.
replace (a ^ 2) with (Rsqr a) in H by (unfold Rsqr; nra).
replace (sqrt b ^ 2) with (Rsqr (sqrt b)) in H by (unfold Rsqr; nra).
apply Rsqr_le_abs_0 in H. 
pose proof Rabs_pos_eq (sqrt b) (sqrt_pos b). rewrite <- H0.
auto.
apply pow2_sqrt.
eapply Rle_trans. 
2 : apply H.
apply square_pos.
Qed.

Lemma Rprod_minus_comm : forall a b, ∥ a - b ∥ = ∥ b - a ∥.
Proof.
intros. 
unfold Rprod_norm, Rprod_minus.
destruct a; destruct b; unfold fst, snd.
f_equal. simpl. nra.
Qed.

Lemma Rprod_triang_inv : forall a b, ∥a∥ - ∥b∥ <= ∥ a - b ∥.
Proof.
intros.
assert ( ∥ a ∥ = ∥ (a-b)+b ∥ ).
  - unfold Rprod_norm, Rprod_plus, Rprod_minus.
  destruct a; destruct b. f_equal. unfold fst, snd. nra.
-
rewrite H.
eapply Rle_trans.
apply Rplus_le_compat_r.
apply Rprod_triang_ineq.
apply Req_le. rewrite Rprod_minus_comm.
nra.
Qed.

Lemma error_sum_le_Sn :
  forall a n,
  0 <= a ->  
  error_sum a n <=
  error_sum a (S n).
Proof.
intros.
pose proof error_sum_aux n a.
rewrite <- H0.
rewrite Rplus_comm.
apply Rle_minus_l.
field_simplify.
apply pow_le; nra.
Qed.

Lemma error_sum_pos:
forall a n , 
0 <= a -> 
0 <=   error_sum a n.
Proof.
intros.
induction n.
+ simpl; nra.
+ pose proof (error_sum_aux n a).
rewrite <- H0.
rewrite Rplus_comm.
apply Rle_plus.
apply pow_le; auto.
apply IHn.
Qed.

Lemma error_sum_le_trans_aux :
  forall a,
  forall m n,
  (n <= m)%nat -> 
  ( 1 <= a) ->  
  error_sum a (S n) <=
  error_sum a (S m).
Proof.
intros.
pose proof (error_sum_aux m a).
rewrite <- H1.
pose proof (error_sum_aux n a).
rewrite <- H2.
clear H1 H2.
induction m.
- assert (n = 0)%nat by lia. subst; simpl; nra.
- assert ((n = S m)%nat \/ ((n < S m)%nat)) by lia.
destruct H1. 
+ subst ; apply Req_le; auto.
+ assert  (n <= m)%nat by lia.
specialize (IHm H2).
eapply Rle_trans.
apply IHm.
eapply Rle_trans.
apply Rplus_le_compat_l.
assert (m <= S m)%nat by lia.
pose proof Rle_pow a m (S m) H0 H3.
apply H4.
eapply Rle_trans.
apply Rplus_le_compat_r.
apply error_sum_le_Sn; nra.
apply Req_le.
auto.
Qed.

Lemma error_sum_le_trans :
  forall a,
  forall m n,
  (n <= m)%nat -> 
  ( 1 <= a) ->  
  error_sum a n <=
  error_sum a m.
Proof.
intros.
destruct n.
- simpl. apply error_sum_pos; nra.
- destruct m.
+ lia.
+ apply error_sum_le_trans_aux; try lia; lra.
Qed.

Lemma error_sum_GS :
forall n,
forall h,
0 < h -> 
error_sum (1 + h) n = ((1 + h) ^ n - 1) / h.
Proof.
intros.
induction n.
- simpl. nra.
- unfold error_sum.
assert (1 + h <> 1) by nra.
pose proof geo_series_closed_form (1 + h) n H0.
rewrite H1. 
replace (((1 - (1 + h) ^ S n) / (1 - (1 + h))))
with (( (1 + h) ^ S n - 1) / h).
field_simplify;
repeat nra.
set (aa:=(1 + h) ^ S n).
apply Stdlib.Rdiv_eq_reg.
nra.
all : nra.
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

Lemma h_sqrt2_lemma (h : R) : 
0 < h < sqrt 2 ->
0 < h^2  < 2.
Proof.
intros.
destruct H; split; auto.
apply pow2_gt_0; try nra.
assert ( h * h < sqrt 2  * sqrt 2) by nra.
rewrite sqrt_def in H1; try nra.
Qed.

Lemma fst_eq (a b c d: R *  R):
 a = b -> fst (a,c) = fst (b,d).
Proof.
intros.
simpl.
auto.
Qed.


Lemma sqrt_norm :
  forall x : R, sqrt (x^2) = (@norm R_AbsRing _ x).
Proof.
intros.
unfold norm.
etransitivity.
replace (x ^ 2) with (x²) .
apply sqrt_Rsqr_abs.
unfold Rsqr; simpl; nra.
simpl; auto.
Qed.
