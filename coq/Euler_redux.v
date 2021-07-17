From Coq Require Import ZArith Reals Psatz.
From Coq Require Import Arith.Arith.
From Coq Require Import Logic.FunctionalExtensionality. 
From Coquelicot Require Import Coquelicot.

Open Scope R_scope.

Section EulerDefs.

Variable h : R.
Variable t : R.
Variable y : R -> R.
Variable F : R -> R.

Definition expansion (n: nat): (R) := 
  match n with
  | 0 => y t
  | S n => y t + sum_f_R0 (fun m => h^ (pred m) / INR (fact (S m)) * Derive_n (fun t => F (y t)) m t) n
  end.

Definition method_expansion (n m : nat): R :=
  let b:= m <=? n in
  match b with
  | true => 
    match m with 
    | 0 => expansion 0
    | S m' => expansion (S m') - expansion m' 
    end
  | false => 0
  end.

Fixpoint ytilde_dt (n : nat) : R :=
  match n with
  | 0 => 0
  | (S n as m) => Derive_n (fun t => F (y t)) m t + ytilde_dt n
  end.

Fixpoint fcoe (n: nat) (method: nat -> R) : R :=
  match n with
  | 0 => 0 
  | S n  => method ( S (S n) - ytilde_dy (S n) method - 1 / INR (fact (S n)) * ytilde_dt n 
  end
  with ytilde_dy (n' : nat) (method : nat -> R) : R :=
  match n' with 
  | 0 => 0
  | S n => 1 / INR (fact n') * Derive_n (fun x => (fcoe n method * F x)) n (y t) + (ytilde_dy n method)
  end. 

Definition Euler: nat -> R := method_expansion 1.

End EulerDefs.

Check Euler. 

Lemma Euler0 (F y: R -> R) (h t: R) : 
  (Euler h t y F) 0 = y t.
Proof.
intros. unfold Euler, method_expansion, expansion. simpl. field_simplify. auto. 
Qed.

Lemma Euler1 (F y: R -> R) (h t: R) : 
  (Euler h t y F) 1 = F (y t).
Proof.
intros. unfold Euler, method_expansion, expansion. simpl. field_simplify. auto. 
Qed.

Lemma Euler2 (F y: R -> R) (h t: R) : 
  (Euler h t y F) 2 = 0.
Proof.
intros. unfold Euler, method_expansion, expansion. simpl. field_simplify. auto. 
Qed.
  
Lemma fcoe1 (F y: R -> R) (h t: R) : 
  h > 0 -> fcoe t y F 1 (Euler h t y F) = F (y t).
Proof.
intros; unfold fcoe, Euler, method_expansion, expansion. simpl. field_simplify. auto.
Qed.

Lemma fcoe2 (F y: R -> R) (h t: R) : 
  h > 0 ->
  is_derive y t (F (y t)) -> 
  ex_derive F (y t) -> 
  fcoe t y F 2 (Euler h t y F) = -F (y t) * Derive F (y t) * (1/2).
Proof.
intros; unfold fcoe, Euler, method_expansion, expansion. simpl. field_simplify.
replace (Derive (fun x : R => F (y x)) t) with (F (y t) * Derive F (y t)).
field_simplify. auto.
symmetry. replace (F (y t)) with (Derive y t).
apply Derive_comp. auto. unfold ex_derive. exists (F (y t)). auto. apply is_derive_unique. auto.
Qed.

Definition F (x : R) := x^2.

Lemma fcoe1_explicit (y: R -> R) (h t: R) : fcoe t y F 1 (Euler h t y F) =  (y t)^2.
Proof. 
unfold fcoe, Euler, method_expansion, expansion, F.
simpl. field_simplify. nra. 
Qed. 

Lemma fcoe2_explicit (y: R -> R) (h t: R) : 
  h > 0 ->
  is_derive y t (F (y t)) -> 
  fcoe t y F 2 (Euler h t y F) = -(y t)^3.
Proof.
intros; unfold fcoe, Euler, method_expansion, expansion. simpl. field_simplify.
-replace (Derive (fun x : R => F (y x)) t) 
  with ((y t)^2 * Derive F (y t)).
unfold F.
field_simplify. 
replace (Derive (fun x : R => x ^ 2) (y t)) 
  with (2 * y t) 
  by (symmetry; apply is_derive_unique; auto_derive; nra).
nra.
symmetry. replace (y t ^ 2) with (Derive y t). apply Derive_comp.
auto_derive; auto. unfold ex_derive. exists ((y t)^2). unfold F in H. auto. 
apply is_derive_unique. auto.
Qed.

Lemma fcoe3_explicit (y: R -> R) (h t: R) : 
  h > 0 ->
  is_derive y t (F (y t)) -> 
  fcoe t y F 3 (Euler h t y F) = (y t)^4 * (3/2).
Proof.
intros; unfold fcoe, Euler, method_expansion, expansion. simpl. field_simplify.
-replace (Derive (fun x : R => F (y x)) t) 
  with ((y t)^2 * Derive F (y t)).
- replace (Derive
   (fun x : R => (y t + 1 / 1 * F (y t) - y t - 0 - 1 / 1 * 0) * F x)
   (y t)) with (Derive
   (fun x : R => F (y t) * F x)
   (y t)).
unfold F. 
replace (Derive (fun x : R => x ^ 2) (y t)) 
  with (2 * y t) 
  by (symmetry; apply is_derive_unique; auto_derive; nra).
replace (Derive (fun x : R => Derive (fun x0 : R => y x0 ^ 2) x) t) with (2 * y t). 
replace (Derive (fun x : R => y t ^ 2 * x ^ 2) (y t)) with (2 * (y t)^3). field_simplify.
Qed.


Lemma fcoe2_2 (F: R -> R) (y: R -> R) (h t: R) : 
  h > 0 ->
  is_derive y t (F (y t)) -> 
  ex_derive F (y t) ->
  fcoe h t y F 2 = -F (y t) * Derive F (y t) * (1/2).
Proof.
intros. unfold fcoe, Euler, expansion; simpl.
assert (H2: h <> 0) by (unfold Rgt in H; auto with real).
field_simplify.
replace (Derive (fun x : R => F (y x)) t) with (F (y t) * Derive F (y t)). 
field_simplify. auto. 
symmetry. replace (F (y t)) with (Derive y t).
apply Derive_comp. auto. unfold ex_derive. exists (F (y t)). auto. apply is_derive_unique. auto.

Qed.

Lemma fcoe3 (F: R -> R) (y: R -> R) (h t: R) : 
  h > 0 ->
  is_derive y t (F (y t)) -> 
  ex_derive F (y t) ->
  fcoe h t y F 3 = -F (y t) * Derive F (y t) * (1/2).
Proof.
intros. unfold fcoe, Euler; simpl.
assert (H2: h <> 0) by (unfold Rgt in H; auto with real).
field_simplify.

Lemma Euler_method (F: R -> R) (y: R -> R) (h t: R) : 
  Euler h t y F = y t + h * F (y t).
Proof.
unfold Euler, expansion; simpl; nra. 
Qed.


Lemma fcoe1 (F: R -> R) (y: R -> R) (h t: R) : h > 0 -> fcoe h t y F 1 = F (y t).
Proof. 
intros. unfold fcoe, expansion; simpl.
assert (H1: h <> 0) by (unfold Rgt in H; auto with real).
assert (H2: h / h * F (y t) = h * F (y t) / h) by (field_simplify; auto).
field_simplify. 
replace (h * F (y t) / h) with (h/h * F (y t)).
replace (h/h) with 1 by (apply Rinv_r_sym; auto). nra. 
Qed.

Lemma fcoe2 (F: R -> R) (y: R -> R) (h t: R) : 
  h > 0 ->
  is_derive y t (F (y t)) -> 
  ex_derive F (y t) ->
  fcoe h t y F 2 = F (y t) * Derive F (y t) * (1/2).
Proof.
intros. unfold fcoe, expansion; simpl.
assert (H2: h <> 0) by (unfold Rgt in H; auto with real).
field_simplify.
replace (Derive (fun x : R => F (y x)) t) with (F (y t) * Derive F (y t)).
assert (H3: h^2 / h^2 * (F (y t) * Derive F (y t))/2 = h^2 * ((F (y t) * Derive F (y t)) / (2*h^2)) )
by (field_simplify; auto).
field_simplify. all: auto.
symmetry. replace (F (y t)) with (Derive y t).
apply Derive_comp. auto. unfold ex_derive. exists (F (y t)). auto. apply is_derive_unique. auto.
Qed.

Definition F (x : R) := x^2.

Lemma expansion_eq0 (y: R -> R) (h t: R) : expansion h t y F  0 = y t.
Proof. 
unfold expansion, F. 
simpl. field_simplify. nra. 
Qed. 

Lemma expansion_eq1 (y: R -> R) (h t: R) : expansion h t y F 1 = y t + h * (y t)^2.
Proof. 
unfold expansion, F. 
simpl. field_simplify. nra. 
Qed. 

Lemma expansion_eq2 (y: R -> R) (h t: R) : 
is_derive y t (F (y t))-> 
expansion h t y F 2 - expansion h t y F 1 = h^2 * (y t)^3.
Proof. 
intros.
unfold expansion. 
simpl. field_simplify. 
-replace (Derive (fun x : R => F (y x)) t) 
  with ((y t)^2 * Derive F (y t)).
unfold F.
-replace (Derive (fun x : R => x ^ 2) (y t)) 
  with (2 * y t) 
  by (symmetry; apply is_derive_unique; auto_derive; nra).
nra.
symmetry. replace (y t ^ 2) with (Derive y t). apply Derive_comp.
auto_derive; auto. unfold ex_derive. exists ((y t)^2). unfold F in H. auto. 
apply is_derive_unique. auto.
Qed. 

