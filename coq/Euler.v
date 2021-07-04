From Coq Require Import ZArith Reals Psatz.
From Coq Require Import Arith.Arith.
From Coq Require Import Logic.FunctionalExtensionality. 
From Coquelicot Require Import Coquelicot.

Open Scope R_scope.

Section EulerDefs.

Variable h : R.
Variable y : R.
Variable F : R -> R.

Definition mod_eq (f: nat -> R -> R) (n: nat) (x : R) : R :=
  match n with
  | 0 => 0 
  | 1 => 0
  | S (S n)  => h^n * (f n x) 
  end.

Fixpoint diff_y (n: nat) (t: R -> R) (x : R) : R :=
  let t' := t x in 
  match n with  
  | 0 => x
  | S n => (Derive (diff_y n t) x) * t'
  end.

Fixpoint fcoe_fix (n:nat) (x: R) : R := 
  let t  := mod_eq fcoe_fix n in 
  match n with
  | 0 => F x
  | (S n as m) => 
    let ytilde := sum_f_R0 (fun k => (h^k * (diff_y k t x) / INR (fact k))) in 
    (ytilde m) - x - h * (F x)
  end.

Definition fcoe (n : nat) (x : R) : R := -(fcoe_fix n x) .

Definition ModEq (n: nat) (x : R) : R := sum_f_R0 (fun j => (h^(j-1) * (fcoe j x))) n.

End EulerDefs. 

Definition F y:=  y^2.

Lemma fcoe1 (h y : R) :
  fcoe h F 1 y = h * y^2.
Proof.
intros. unfold fcoe, fcoe_fix, F; simpl. field_simplify. nra. 
Qed. 

Lemma fcoe2 (h y : R) :
  fcoe h F 2 y = -h^2 * y^3.
Proof.
unfold fcoe, fcoe_fix, F; simpl. field_simplify. 
-replace (Derive (fun x : R => x) y) 
  with 1 
  by (symmetry; apply is_derive_unique; auto_derive; auto).
-replace (fun x : R => Derive (fun x0 : R => x0) x * (1 * (x * (x * 1)))) 
  with (fun x : R => Derive (fun x0 : R => x0) x * x^2)
  by (apply functional_extensionality; intros;
     replace ((1 * (x * (x * 1)))) with (x^2) by (nra);
     auto).
-replace (Derive (fun x : R => Derive (fun x0 : R => x0) x * x^2) y) 
  with (Derive (fun x : R => x^2) y).
-replace (Derive (fun x : R => x^2) y) 
  with (2*y) 
  by (symmetry; apply is_derive_unique; auto_derive; nra);
  field_simplify; auto; nra. 
apply Derive_ext; symmetry. 
replace (Derive (fun x0 : R => x0) t) with 1. nra. 
symmetry; apply is_derive_unique; auto_derive; auto.
Qed. 


