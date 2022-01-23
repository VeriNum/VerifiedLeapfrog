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


