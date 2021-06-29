From Coq Require Import ZArith Reals Psatz.
From Coq Require Import Arith.Arith.
From Coquelicot Require Import Coquelicot.

Open Scope R_scope.

Section EulerDefs.

Variable h : R.
Variable F : R -> R.
Variable y : R. 

Definition fcoe (f: nat -> R -> R) (n: nat) : R :=
  match n with
  | 0 => F y 
  | S n' => 
    let ytilde := sum_f_R0 (fun k => (h^k * (f k y) / INR (fact k))) in 
    (ytilde n') - y - h*(F y)
  end.

Fixpoint diff_y (n: nat) (x: R): R :=
  let f2 := fcoe diff_y in
  match n with 
  | 0 => x
  | S n' => 
    let mod_eq := sum_f_R0 (fun j => h^j * (f2 j)) in
    (Derive (diff_y n') x) * (mod_eq n)
  end. 