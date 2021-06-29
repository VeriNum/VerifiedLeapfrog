From Coq Require Import ZArith Reals Psatz.
From Coq Require Import Arith.Arith.
From Coquelicot Require Import Coquelicot.
From Leapfrog Require Import Iterate.

Open Scope R_scope.

Section EulerDefs.

(* You can factor out common parameters like this within a Section. *)

Variable h : R.
Variable F : R -> R.
Variable y : R. 

Definition euler_step (y : R) : R :=
  let y' := y + h*y^2 in y'. 

(* This will prevent tactics like simpl from expanding leapfrog_step. If you
want to switch back use Transparent *)
Opaque euler_step.

Fixpoint euler (y : R) (n : nat) : R :=
  match n with
  | 0 => y
  | S n' =>
    let y' := euler_step y in
    euler y' n'
  end.

Fixpoint modeq (n : nat) : R :=
  match n with
  | 0 => F y 
  | (S n as m) => h^n * (fcoe n) + modeq n
  end
  with fcoe (n : nat) : R :=
  match n with
  | 0 => F y
  | (S n as m)  => (ytilde m) - y -h * F y
  end
  with ytilde (n : nat) : R :=
  match n with 
  | 0 => diff_y 0 y
  | (S n as m) => h^m (diff_y m y) / INR (fact m) + (ytilde n)
  end
  with diff_y (n: nat) (x: R): R :=
  match n with 
  | 0 => x
  | S n => (Derive (diff_y n) x) * modeq (S n)
  end. 

Definition fcoe (f: nat -> R -> R) (n: nat) : R :=
  match n with
  | 0 => F y 
  | (S n as m) => 
    let f2 := (fun k => (h^k * (f k y) / INR (fact k))) in 
    (sum_f_R0 f2 m) - y - h*(F y)
  end.

Fixpoint diff_y (n: nat) (x: R): R :=
  let f2 := fcoe diff_y in
  match n with 
  | 0 => x
  | S n => 
    let f3 := (fun j => h^j * (f2 j)) in
    (Derive (diff_y n) x) * (f3 n)
  end. 

Definition f3 := (diff_y 3). 

Print f3. 

Definition mod_eq (f: nat -> R) (n: nat) : R :=
  sum_f_R0 (fun m => h^m * (f m)) n.

Definition ytilde (f: nat -> R) (n : nat) : R := 
  sum_f_R0 (fun k => (h^k * (f k) / INR (fact k))) n.

Definition fcoe (f1: nat -> R) (n: nat) : R :=
  match n with
  | 0 => F(y)
  | (S n as m) => -y - h*(F y) + (ytilde f1 m)
  end.

Definition diff_y (f1: nat -> R) (n : nat) : R :=
  match n with
  | 0 => y 
  | S n => f1 n
  end.

Fixpoint modeq (n:nat) : R:=
  let f2 := diff_y modeq
  match n with
  | 0 => F(y)
  | (S n as m) => -y - h*(F y) + (ytilde f1 m)
  end.


Fixpoint fcoe (j : nat) { struct j } : R :=
  let f2 := mod_eq fcoe in
  match j with
  | 0 => F y
  | S j => -y - h * (F y) + yt
  end. 

Fixpoint dy  :=
  match n with
  | 0 => y 
  | S n' =>  
  end.

Fixpoint mod_eq2 (f: nat -> R) (n : nat) : R  :=
  match n with 
  | 0 => 
  | S n' =>   
  end.

Fixpoint fx (n : nat) : R :=
  match n with
  | 0 => 0
  | S n' =>
    fx n'
  end.

Definition ff := mod_eq fx.




End EulerDefs.