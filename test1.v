From Coq Require Import ZArith Reals Psatz.
From Coq Require Import Arith.Arith.
From Flocq Require Import Core Plus_error.

Open Scope R_scope.

Definition leapfrog_12 xn vn h F := 
    let vnp12 := vn + 0.5*  h* F xn in
    let xnp1  := xn + h* vnp12 in
    pair xnp1 vnp12.
    
Definition leapfrog_step x0 v0 h F := 
    let v12 := snd (leapfrog_12 x0 v0 h F) in
    let x1  := fst (leapfrog_12 x0 v0 h F) in
    let v1  := v12 + 0.5* h* F x1 in
    pair x1 v1.
    
Fixpoint leapfrog x0 v0 h F (n:nat):=
    match n with 
    | 0 => pair x0 v0
    | S n' => 
        let xn := fst (leapfrog_step x0 v0 h F) in
        let vn := snd (leapfrog_step x0 v0 h F) in
        leapfrog xn vn h F (n')
    end.

Definition F (x:R) := -1 * x.

Lemma leapfrog_fixpoint :  forall x0 v0 h F (n:nat), leapfrog x0 v0 h F (n:nat) =
    match n with 
    | 0 => pair x0 v0
    | S n' => 
        let xn := fst (leapfrog_step x0 v0 h F) in
        let vn := snd (leapfrog_step x0 v0 h F) in
        leapfrog xn vn h F (n')
    end.
Proof.
intros. induction n. 
simpl. auto.
simpl. auto. 
Qed.

Lemma leapfrog_returns_2:
    forall x0 v0 h xf vf (n:nat),
    x0 = 1 -> v0 = 0 -> h = (0.02 * 2 * PI) -> 
    xf = fst (leapfrog x0 v0 h F (S n)) -> vf = snd (leapfrog x0 v0 h F (S n)) ->
    (0.5 * xf^2 + 0.5*vf^2 ) < 0.5 .

Proof.
intros x0 v0 h xf vf n Hx Hv Hh Hxf Hvf . simpl. 
replace xf with (fst (leapfrog x0 v0 h F (S n))); 
replace vf with (snd (leapfrog x0 v0 h F (S n))). 
induction n.
simpl; unfold F; replace x0 with 1; replace v0 with 0; 
replace h with (0.02 * 2 * PI); field_simplify. psatz R 1.  



