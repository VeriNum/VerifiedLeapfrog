From Coq Require Import ZArith Reals Psatz.
From Coq Require Import Arith.Arith.
From Coquelicot Require Import Coquelicot.

Open Scope R_scope.

Section EulerDefs.

Variable h : R.
Variable y : R.

Definition F := (fun y => y^2).

Definition mod_eq (f: nat -> R -> R) (n: nat) (x : R) : R :=
  match n with
  | 0 => 0 
  | 1 => 0
  | S (S n)  => h^n * (f n x) 
  end.

Fixpoint diff_y (n: nat) (t: R) (x: R) : R :=
  match n with  
  | 0 => x
  | S n => (Derive (diff_y n t) x) * t
  end.

Fixpoint fcoe (n:nat) (x: R) : R := 
  let t  := mod_eq fcoe n x in 
  match n with
  | 0 => F x
  | (S n as m) => 
    let ytilde := sum_f_R0 (fun k => (h^k * (diff_y k t x) / INR (fact k))) in 
    (ytilde m) - x - h*(F x)
  end.

Lemma foce2 :
  fcoe 2 y = h^2 * y^3.
Proof.
unfold fcoe, F; simpl. field_simplify. 
replace (Derive (fun x : R => Derive (fun x0 : R => x0) x * (1 * (y * (y * 1)))) y) with (2*y). 
replace (Derive (fun x : R => x) y) with 1. nra. 
symmetry; field_simplify;
apply is_derive_unique; auto_derive; auto; nra.
symmetry; field_simplify. 
 

