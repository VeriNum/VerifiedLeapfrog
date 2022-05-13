From vcfloat Require Import FPLang FPLangOpt RAux Rounding Reify Float_notations Automate.
Require Import IntervalFlocq3.Tactic.
From Coquelicot Require Import Coquelicot.
Import Binary.
Import List ListNotations.
Set Bullet Behavior "Strict Subproofs".

Require Import Coq.Logic.FunctionalExtensionality.

Require Import float_model real_model real_lemmas vcfloat_lemmas matrix_analysis matrix_lemmas.

Open Scope R_scope.

Section WITHNANS.

Context {NANS: Nans}.


Definition rounded_q (e0 e1 d: R) (p q : R) := 
  ((q + (1 / 32 * p + e0)) * (1 + d) + e1 + (1 / 2048 * - q + e0)) * (1 + d) + e1
.


Definition rounded_p (e0 e1 d: R) (p q : R) := 
(p +(1 / 64 * ((- q + - (((q + (1 / 32 * p + e0)) * (1 + d) + e1 + (1 / 2048 * - q + e0)) * (1 + d) + e1)) *
      (1 + d) + e1) + e0)) * (1 + d) + e1
.

Definition leapfrogF_J (e0 e1 d: R) (p q : R) := mk_matrix 2 2 (fun i j => 
  if (Nat.eqb i j && Nat.eqb i 0) then (Derive (fun p => (rounded_p e0 e1 d p q)) p) else
  if (Nat.eqb i j ) then (Derive (fun q => (rounded_q e0 e1 d p q)) q) else
  if (Nat.ltb i j ) then (Derive (fun q => (rounded_p e0 e1 d p q)) q) else
     (Derive (fun p => (rounded_q e0 e1 d p q)) p))
.

Definition leapfrogR_J (p q : R) := mk_matrix 2 2 (fun i j => 
  if (Nat.eqb i j && Nat.eqb i 0) then (Derive (fun p => fst (leapfrog_stepR h (p,q))) p) else
  if (Nat.eqb i j ) then (Derive (fun q => snd (leapfrog_stepR h (p,q))) q) else
  if (Nat.ltb i j ) then (Derive (fun q => fst (leapfrog_stepR h (p,q))) q) else
     (Derive  (fun p => snd(leapfrog_stepR h (p,q))) p))
.

Definition Omega := @mk_matrix R_Ring 2 2 (fun i j => if (Nat.eqb i j) then 0 else 
  if (Nat.ltb i j) then 1 else -1). 


Definition L1_norm (A: matrix 2 2) : R := 
  Rmax (Rabs (@coeff_mat R 2 2 0 A 0 0) + Rabs(@coeff_mat R 2 2 0 A 1 0)) 
      (Rabs (@coeff_mat R 2 2 0 A 1 0) + Rabs(@coeff_mat R 2 2 0 A 1 1)).

Definition matrix_transpose (M : @matrix R_Ring 2 2) : @matrix R_Ring 2 2 := 
  mk_matrix 2 2  (fun i j : nat => (coeff_mat zero M j i)).



Lemma leapfrog_is_symplectic:
  forall p q : R, 
  let J  := leapfrogR_J p q in
  let JT := (matrix_transpose  J) in
  (Mmult (Mmult JT Omega) J) = Omega.
Proof.
intros.
unfold Mmult, Omega, JT, matrix_transpose, J, leapfrogR_J.
apply mk_matrix_ext => i j Hi Hj.
assert (Hii: (i = 0)%nat \/ (i = 1)%nat) by lia; destruct Hii; subst;
assert (Hjj: (j = 0)%nat \/ (j = 1)%nat) by lia; destruct Hjj; subst;
simpl.
all : (
rewrite sum_Sn;
rewrite sum_O;
repeat rewrite coeff_mat_bij; try lia;
repeat rewrite sum_Sn;
repeat rewrite sum_O;
repeat rewrite coeff_mat_bij; try lia;
simpl;
unfold ω;
repeat match goal with |- context [Derive (?f) ?y] =>
let f' := fresh "f" in
set (f':= f); 
auto_derive_fun f; unfold F;
assert True as TR by auto;
let H := fresh "H" in
          intro H;
let H1 := fresh "H" in
pose proof (H y TR) as H1; clear TR; clear H ;
apply is_derive_unique in H1;
match goal with H0: Derive (?f) ?y = ?f1 |- _ =>
let H2 := fresh "H" in
assert (H2: f' = f) by
(unfold f'; apply functional_extensionality; auto);
rewrite H2; clear H2
end;
rewrite H1; clear H1
end;
replace (@plus R_Ring) with Rplus by auto;
replace (@mult R_Ring) with Rmult by auto;
field_simplify; try nra
).
Qed.




Lemma leapfrog_symp_error :
  forall (e0 e1 d p q: R),
  Rabs e0 <= / 713623846352979940529142984724747568191373312 ->
  Rabs d <= / 16777216 ->
  Rabs e1 <= / 1427247692705959881058285969449495136382746624 ->
  let J  := leapfrogF_J e0 e1 d p q in
  let JT := (matrix_transpose  J) in
  L1_norm (Mplus (Mmult (Mmult JT Omega) J) (Mopp Omega)) <= 4/10^7.
Proof.
intros.
unfold JT, matrix_transpose, J, Mmult, Mplus, Mopp.
apply Rmax_lub.
-
eapply Rle_trans.
2 : { assert (Heq:  2/ 10 ^ 7 +  2/ 10 ^ 7 = 4/ 10 ^ 7) by nra ; 
  apply Req_le ; apply Heq.
}
apply Rplus_le_compat.
+ 
apply Rabs_le; split.
*
simpl. unfold leapfrogF_J, Omega, rounded_p, rounded_q.
repeat rewrite coeff_mat_bij; try lia;
rewrite sum_Sn;
rewrite sum_O.
repeat rewrite coeff_mat_bij; try lia;
repeat rewrite sum_Sn;
repeat rewrite sum_O.
repeat rewrite coeff_mat_bij; try lia.
simpl.
repeat match goal with |- context [Derive (?f) ?y] =>
let f' := fresh "f" in
set (f':= f); 
auto_derive_fun f; unfold F;
assert True as TR by auto;
let H := fresh "H" in
          intro H;
let H1 := fresh "H" in
pose proof (H y TR) as H1; clear TR; clear H ;
apply is_derive_unique in H1;
match goal with H0: Derive (?f) ?y = ?f1 |- _ =>
let H2 := fresh "H" in
assert (H2: f' = f) by
(unfold f'; apply functional_extensionality; auto);
rewrite H2; clear H2
end;
rewrite H1; clear H1
end.
replace (@plus R_Ring) with Rplus by auto;
replace (@mult R_Ring) with Rmult by auto;
replace (@opp  R_Ring) with Ropp by auto; 
field_simplify; try interval.
*
simpl. unfold leapfrogF_J, Omega, rounded_p, rounded_q.
repeat rewrite coeff_mat_bij; try lia;
rewrite sum_Sn;
rewrite sum_O.
repeat rewrite coeff_mat_bij; try lia;
repeat rewrite sum_Sn;
repeat rewrite sum_O.
repeat rewrite coeff_mat_bij; try lia.
simpl.
repeat match goal with |- context [Derive (?f) ?y] =>
let f' := fresh "f" in
set (f':= f); 
auto_derive_fun f; unfold F;
assert True as TR by auto;
let H := fresh "H" in
          intro H;
let H1 := fresh "H" in
pose proof (H y TR) as H1; clear TR; clear H ;
apply is_derive_unique in H1;
match goal with H0: Derive (?f) ?y = ?f1 |- _ =>
let H2 := fresh "H" in
assert (H2: f' = f) by
(unfold f'; apply functional_extensionality; auto);
rewrite H2; clear H2
end;
rewrite H1; clear H1
end.
replace (@plus R_Ring) with Rplus by auto;
replace (@mult R_Ring) with Rmult by auto;
replace (@opp  R_Ring) with Ropp by auto; 
field_simplify; try interval.
+ 
simpl. unfold leapfrogF_J, Omega, rounded_p, rounded_q.
repeat rewrite coeff_mat_bij; try lia;
rewrite sum_Sn;
rewrite sum_O.
repeat rewrite coeff_mat_bij; try lia;
repeat rewrite sum_Sn;
repeat rewrite sum_O.
repeat rewrite coeff_mat_bij; try lia.
simpl.
repeat match goal with |- context [Derive (?f) ?y] =>
let f' := fresh "f" in
set (f':= f); 
auto_derive_fun f; unfold F;
assert True as TR by auto;
let H := fresh "H" in
          intro H;
let H1 := fresh "H" in
pose proof (H y TR) as H1; clear TR; clear H ;
apply is_derive_unique in H1;
match goal with H0: Derive (?f) ?y = ?f1 |- _ =>
let H2 := fresh "H" in
assert (H2: f' = f) by
(unfold f'; apply functional_extensionality; auto);
rewrite H2; clear H2
end;
rewrite H1; clear H1
end.
replace (@plus R_Ring) with Rplus by auto;
replace (@mult R_Ring) with Rmult by auto;
replace (@opp  R_Ring) with Ropp by auto.
match goal with |- context [Rabs ?e] =>
  field_simplify e
end.
try interval.
-
eapply Rle_trans.
2 : { assert (Heq:  2/ 10 ^ 7 +  2/ 10 ^ 7 = 4/ 10 ^ 7) by nra ; 
  apply Req_le ; apply Heq.
}
apply Rplus_le_compat.
+ 
apply Rabs_le; split.
*
simpl. unfold leapfrogF_J, Omega, rounded_p, rounded_q.
repeat rewrite coeff_mat_bij; try lia;
rewrite sum_Sn;
rewrite sum_O.
repeat rewrite coeff_mat_bij; try lia;
repeat rewrite sum_Sn;
repeat rewrite sum_O.
repeat rewrite coeff_mat_bij; try lia.
simpl.
repeat match goal with |- context [Derive (?f) ?y] =>
let f' := fresh "f" in
set (f':= f); 
auto_derive_fun f; unfold F;
assert True as TR by auto;
let H := fresh "H" in
          intro H;
let H1 := fresh "H" in
pose proof (H y TR) as H1; clear TR; clear H ;
apply is_derive_unique in H1;
match goal with H0: Derive (?f) ?y = ?f1 |- _ =>
let H2 := fresh "H" in
assert (H2: f' = f) by
(unfold f'; apply functional_extensionality; auto);
rewrite H2; clear H2
end;
rewrite H1; clear H1
end.
replace (@plus R_Ring) with Rplus by auto;
replace (@mult R_Ring) with Rmult by auto;
replace (@opp  R_Ring) with Ropp by auto; 
field_simplify; try interval.
*
simpl. unfold leapfrogF_J, Omega, rounded_p, rounded_q.
repeat rewrite coeff_mat_bij; try lia;
rewrite sum_Sn;
rewrite sum_O.
repeat rewrite coeff_mat_bij; try lia;
repeat rewrite sum_Sn;
repeat rewrite sum_O.
repeat rewrite coeff_mat_bij; try lia.
simpl.
repeat match goal with |- context [Derive (?f) ?y] =>
let f' := fresh "f" in
set (f':= f); 
auto_derive_fun f; unfold F;
assert True as TR by auto;
let H := fresh "H" in
          intro H;
let H1 := fresh "H" in
pose proof (H y TR) as H1; clear TR; clear H ;
apply is_derive_unique in H1;
match goal with H0: Derive (?f) ?y = ?f1 |- _ =>
let H2 := fresh "H" in
assert (H2: f' = f) by
(unfold f'; apply functional_extensionality; auto);
rewrite H2; clear H2
end;
rewrite H1; clear H1
end.
replace (@plus R_Ring) with Rplus by auto;
replace (@mult R_Ring) with Rmult by auto;
replace (@opp  R_Ring) with Ropp by auto; 
field_simplify; try interval.
+ 
simpl. unfold leapfrogF_J, Omega, rounded_p, rounded_q.
repeat rewrite coeff_mat_bij; try lia;
rewrite sum_Sn;
rewrite sum_O.
repeat rewrite coeff_mat_bij; try lia;
repeat rewrite sum_Sn;
repeat rewrite sum_O.
repeat rewrite coeff_mat_bij; try lia.
simpl.
repeat match goal with |- context [Derive (?f) ?y] =>
let f' := fresh "f" in
set (f':= f); 
auto_derive_fun f; unfold F;
assert True as TR by auto;
let H := fresh "H" in
          intro H;
let H1 := fresh "H" in
pose proof (H y TR) as H1; clear TR; clear H ;
apply is_derive_unique in H1;
match goal with H0: Derive (?f) ?y = ?f1 |- _ =>
let H2 := fresh "H" in
assert (H2: f' = f) by
(unfold f'; apply functional_extensionality; auto);
rewrite H2; clear H2
end;
rewrite H1; clear H1
end.
replace (@plus R_Ring) with Rplus by auto;
replace (@mult R_Ring) with Rmult by auto;
replace (@opp  R_Ring) with Ropp by auto.
match goal with |- context [Rabs ?e] =>
  field_simplify e
end.
try interval.
Qed.


End WITHNANS.