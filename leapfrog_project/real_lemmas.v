From Coq Require Import ZArith Reals Psatz.
From Coq Require Import Arith.Arith.
From Coquelicot Require Import Coquelicot.
From Flocq Require Import Core.

Require Import vcfloat.RAux.

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


Definition Rprod_minus (x y : R * R) : R * R :=
  (Rminus (fst x) (fst y), Rminus (snd x) (snd y)).

Definition Rprod_plus (x y : R * R) : R * R :=
  (Rplus (fst x) (fst y), Rplus (snd x) (snd y)).

Definition Rprod_norm (x : R * R) : R  :=
  sqrt ( (fst x) ^ 2 +  (snd x) ^ 2).

Lemma Rprod_triang_ineq x y: 
Rprod_norm ( Rprod_plus x y) <= Rprod_norm x + Rprod_norm y.
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

Lemma Rprod_norm_plus_minus_eq x y z:
Rprod_norm ( Rprod_minus x y) = Rprod_norm ( Rprod_plus (Rprod_minus x z) (Rprod_minus z y)).
Proof.
intros.
destruct x, y, z.
unfold Rprod_plus, Rprod_minus, Rprod_norm, fst, snd.
f_equal.
nra.
Qed.


Lemma Rnorm_pos x:
0 <= Rprod_norm x.
Proof.
unfold Rprod_norm.
apply sqrt_pos.
Qed.

