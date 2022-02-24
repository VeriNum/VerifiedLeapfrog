(* this file containts lemmas and tactics for optimizing 
VCFloat expressions *)

From Flocq Require Import Binary Bits Core.
From compcert.lib Require Import IEEE754_extra Coqlib Floats Zbits Integers.

Require Import float_lib.
Require Import vcfloat.

Require vcfloat.Test.
Require Import vcfloat.FPLang.
Require Import vcfloat.FPLangOpt.

Ltac vcfloat_simplifications := 
  repeat change (type_of_expr _) with Tsingle;
  repeat change (type_of_expr _) with Tdouble;
  repeat change (type_lub _ _) with Tsingle; 
  repeat change (type_lub _ _) with Tdouble; 
  repeat change (cast_lub_l Tsingle Tsingle ?A) with A; 
  repeat change (cast_lub_l Tdouble Tdouble ?A) with A; 
  repeat change (cast_lub_r Tsingle Tsingle ?A) with A; 
  repeat change (cast_lub_r Tdouble Tdouble ?A) with A;
  repeat change (cast Tdouble Tdouble ?A) with A;
  repeat change (cast Tsingle Tsingle ?A) with A.

Ltac focus f :=
 match goal with |- context [f ?a] =>
  pattern (f a);
  match goal with |- ?b _ => 
    let h := fresh "out_of_focus" in set (h:=b) 
  end
 end.


Ltac vcfloat_partial_compute := 
  vcfloat_simplifications;
  cbv beta iota delta [fop_of_binop fop_of_unop fop_of_rounded_binop fop_of_rounded_unop]; 
  cbv beta iota delta [BMULT BDIV BPLUS BMINUS BINOP];
  repeat (set (z := fprec _); compute in z; subst z); 
  repeat (set (z := femax _); compute in z; subst z); 
  repeat match goal with |- context [float32_of_Z ?a] =>
    set (z := float32_of_Z a);
    hnf in z; subst z
  end.

Definition hide {T: Type} {x: T} := x.


Ltac simplify_B754_finite x :=
      let y := eval hnf in x in 
      match y with B754_finite ?prec ?emax ?sign ?m ?e ?p =>
        let sign' := eval compute in sign in
        let m' := eval compute in m in 
        let e' := eval compute in e in
        change x with  (B754_finite prec emax sign' m' e' (@hide _ p))
      end.

Ltac simplify_float_ops x :=
  let y:= eval compute in x in 
    change x with y
.

Ltac eqb_compute :=
repeat match goal with
| |- context [binop_eqb ?a  ?b] =>
      simplify_float_ops (binop_eqb a b)
| |- context [binary_float_eqb ?a  ?b] =>
      simplify_float_ops (binary_float_eqb a b)
end.

Ltac pow2_compute :=
repeat match goal with
| |- context [to_power_2 ?a] =>
      simplify_float_ops (to_power_2 a) 
| |- context [to_power_2_pos ?a] =>
      simplify_float_ops (to_power_2_pos a) 
| |- context [to_inv_power_2 ?a] =>
      simplify_float_ops (to_inv_power_2 a) 
end.

Ltac exact_inv_compute :=
repeat match goal with
| |- context [Bexact_inverse] =>  cbv [Bexact_inverse ]
| |- context [Pos.eq_dec ?a ?b] =>
      simplify_float_ops (Pos.eq_dec a b); cbv beta iota zeta
| |- context [Z_le_dec ?a ?b] =>
      simplify_float_ops (Z_le_dec a b); cbv beta iota zeta
end. 

Ltac vcfloat_compute := 
vcfloat_partial_compute;
repeat match goal with
| |- context [B754_finite ?prec ?emax ?sign ?m ?e ?p] =>
     lazymatch p with hide => fail | _ => idtac end;
      simplify_B754_finite (B754_finite prec emax sign m e p)
| |- context [Bdiv ?prec ?emax ?p1 ?p2 ?p3 ?mode ?a1 ?a2] =>
      simplify_B754_finite (Bdiv prec emax p1 p2 p3 mode a1 a2) 
| |- context [Bmult ?prec ?emax ?p1 ?p2 ?p3 ?mode ?a1 ?a2] =>
      simplify_B754_finite (Bmult prec emax p1 p2 p3 mode a1 a2)
| |- context [Bplus ?prec ?emax ?p1 ?p2 ?p3 ?mode ?a1 ?a2] =>
      simplify_B754_finite (Bplus prec emax p1 p2 p3 mode a1 a2)
| |- context [Bminus ?prec ?emax ?p1 ?p2 ?p3 ?mode ?a1 ?a2] =>
      simplify_B754_finite (Bminus prec emax p1 p2 p3 mode a1 a2) 
end.

Ltac simplify_fcval :=
 match goal with |- context [@FPLangOpt.fcval ?x1 ?x2 ?a] =>
     focus (@FPLangOpt.fcval x1 x2);
     let a' := eval hnf in a in change a with a';
     cbv beta fix iota zeta delta [FPLangOpt.fcval FPLangOpt.fcval_nonrec 
                    FPLangOpt.option_pair_of_options];
     vcfloat_compute;
     match goal with |- ?out_of_focus _ => subst out_of_focus; cbv beta end
 end.

Definition optimize_mul {V: Type} {NANS: Nans} (e: expr) : expr :=
  @fshift V NANS (@fcval V NANS e).

Definition optimize_div {V: Type} {NANS: Nans} (e: expr) : expr :=
  @fshift_div V NANS  (@fcval V NANS e).

Definition optimize_shifts {V: Type} {NANS: Nans} (e: expr) : expr :=
  @fshift_div V NANS (@fshift V NANS (@fcval V NANS e)).

Lemma optimize_mul_type {V: Type}{NANS: Nans}: 
   forall e: expr, @type_of_expr V (optimize_mul e) = @type_of_expr V e.
Proof.
intros.
apply (eq_trans (fshift_type (fcval e)) (@fcval_type V NANS e)) .
Defined.


Lemma optimize_shifts_type {V: Type} {NANS: Nans}:
  forall e : expr, @type_of_expr V (optimize_shifts e) = 
    @type_of_expr V e.
Proof.
intros;
apply (eq_trans (fshift_type_div (fshift (fcval e)))
      (eq_trans (fshift_type (fcval e)) (fcval_type e))).
Defined.

Lemma optimize_div_type {V: Type} {NANS: Nans}:
  forall e : expr, @type_of_expr V (optimize_div e) = 
    @type_of_expr V e.
Proof.
intros.
apply (eq_trans (fshift_type_div (fcval e)) (@fcval_type V NANS e)) .
Defined.

Definition optimize_mul_correct {V: Type} {NANS: Nans}: 
  forall env e,  (fval env (optimize_mul e)) = 
  eq_rect_r ftype (fval env e) (@optimize_mul_type V NANS e).
Proof.
intros.
unfold optimize_mul.
rewrite fshift_correct.
rewrite (@fcval_correct V NANS env).
unfold eq_rect_r.
rewrite rew_compose.
f_equal.
rewrite <- eq_trans_sym_distr.
f_equal.
Qed.


Lemma optimize_shifts_correct {V: Type} {NANS: Nans}:
  forall env e,
    Binary.is_nan _ _ (fval env e) = false ->
    fval env (optimize_shifts e) = 
      eq_rect_r ftype (fval env e) (@optimize_shifts_type V NANS e).
Proof.
intros. unfold optimize_shifts.
rewrite fshift_div_correct.
{ rewrite (@fshift_correct V NANS).
rewrite (@fcval_correct V NANS).
unfold eq_rect_r.
repeat rewrite rew_compose.
f_equal.
repeat rewrite <- eq_trans_sym_distr.
rewrite <- eq_trans_assoc.
f_equal.
}
{
pose proof fshift_div_correct' env (fshift (fcval e)).
pose proof fshift_correct' env (fcval e).
rewrite (@fcval_correct V NANS env e) in H1.
revert H0 H1.
generalize (fval env (fcval e)).
try rewrite (@fcval_type V NANS). intros.
revert H1 H2.
generalize (fval env (fshift (fcval e))).
try rewrite fshift_type. try rewrite (@fcval_type V NANS). intros.
pose proof binary_float_eqb_eq_rect_r
   (type_of_expr e) (type_of_expr e) f (fval env e) eq_refl .
try rewrite H2 in H3. clear H2; symmetry in H3; apply binary_float_eqb_eq in H3. subst.
revert H1.
generalize (fval env (fshift_div (fshift (fcval e)))).
try rewrite fshift_type_div. try rewrite fshift_type. try rewrite (@fcval_type V NANS). intros.
destruct (fval env e); try discriminate.
all: destruct f; simpl in H1; try contradiction; try simpl; try reflexivity.
} 
Qed.

Definition optimize_div_correct {V: Type} {NANS: Nans}: 
  forall env e,
    Binary.is_nan _ _ (fval env e) = false ->
    fval env (optimize_div e) = 
    eq_rect_r ftype (fval env e) (@optimize_div_type V NANS e).
Proof.
intros.
unfold optimize_div.
rewrite fshift_div_correct.
rewrite (@fcval_correct V NANS env).
unfold eq_rect_r.
rewrite rew_compose.
f_equal.
rewrite <- eq_trans_sym_distr.
f_equal.
{
pose proof fshift_div_correct' env (fcval e).
rewrite (@fcval_correct V NANS env e) in H0.
revert H0.
generalize (fval env (fshift_div (fcval e))).
try rewrite fshift_type_div. try rewrite (@fcval_type V NANS). intros.
destruct (fval env e);try discriminate.
all: destruct f; simpl in H; try contradiction; try simpl; try reflexivity.
} 
Qed.


Definition optimize_div_correct' {V: Type} {NANS: Nans}:
  forall env e, 
    Binary.is_nan _ _ (fval env e) = false ->
   binary_float_eqb (fval env e) (fval env (@optimize_div V NANS e)) = true.
Proof.
intros.
rewrite optimize_div_correct.
rewrite binary_float_eqb_eq_rect_r.
apply binary_float_eqb_eq. auto.
apply H.
Qed.

Ltac simplify_shift_opt E :=
  match E with 
  | optimize_mul ?e' =>
    let e:= constr:(fshift (fcval e')) in change E with e;
    match e with | @FPLangOpt.fshift ?x1 ?x2 ?a =>
        let a' := eval hnf in a in change a with a' ;
        cbv beta fix iota zeta delta [FPLangOpt.fcval FPLangOpt.fcval_nonrec 
              FPLangOpt.option_pair_of_options];
        vcfloat_compute;
        cbv beta fix iota delta [FPLangOpt.fshift FPLangOpt.fcval_nonrec ];
        vcfloat_simplifications; eqb_compute; cbv beta iota zeta;
        pow2_compute; eqb_compute; cbv beta iota zeta 
   end
end.

Ltac simplify_shifts_opt E  :=
  match E with 
    optimize_shifts ?e' =>
   let e:= constr:(fshift_div (fshift (fcval e'))) in change E with e;
   match e with | @FPLangOpt.fshift_div ?x1 ?x2 (@fshift ?x3 ?x4 ?a) =>
    let a' := eval hnf in a in change a with a' ;
    cbv beta fix iota zeta delta [FPLangOpt.fcval FPLangOpt.fcval_nonrec 
          FPLangOpt.option_pair_of_options];
    vcfloat_compute;
    cbv beta fix iota delta [FPLangOpt.fshift FPLangOpt.fcval_nonrec ];
    vcfloat_simplifications; eqb_compute; cbv beta iota zeta;
    pow2_compute; eqb_compute; cbv beta iota zeta ;
    cbv beta fix iota delta [FPLangOpt.fshift_div FPLangOpt.fcval_nonrec];
    vcfloat_simplifications; eqb_compute; cbv beta iota zeta;
    pow2_compute; vcfloat_simplifications;
    exact_inv_compute; eqb_compute; cbv beta iota zeta
  end
 end.

Ltac simplify_shift_div_opt E  :=
  match E with 
    optimize_div ?e' =>
   let e:= constr:(fshift_div (fcval e')) in change E with e;
   match e with | @FPLangOpt.fshift_div ?x1 ?x2 ?a =>
    let a' := eval hnf in a in change a with a' ;
    cbv beta fix iota zeta delta [FPLangOpt.fcval FPLangOpt.fcval_nonrec 
          FPLangOpt.option_pair_of_options];
    vcfloat_compute;
    cbv beta fix iota delta [FPLangOpt.fcval_nonrec ];
    vcfloat_simplifications; eqb_compute; cbv beta iota zeta;
    pow2_compute; eqb_compute; cbv beta iota zeta ;
    cbv beta fix iota delta [FPLangOpt.fshift_div FPLangOpt.fcval_nonrec];
    vcfloat_simplifications; eqb_compute; cbv beta iota zeta;
    pow2_compute; vcfloat_simplifications;
    exact_inv_compute; eqb_compute; cbv beta iota zeta
  end
 end.



Module TESTING.

Local Close Scope R_scope.

Local Open Scope float32_scope.

Definition F (x : float32) : float32 := - x.

(* Time step*)
Definition h := float32_of_Z 1 / float32_of_Z 32.

Definition half := float32_of_Z 1 / float32_of_Z 2.

(* Single step of the integrator*)
Definition leapfrog_step_test ( ic : float32 * float32) : float32 * float32 :=
  let x  := fst ic in let v:= snd ic in 
  let x' := (x + h * v) + ((half) * (h * h)) * F x in
  let v' :=  v +  (half * h) * (F x + F x') in 
  (x', v').

Definition leapfrog_stepx_test := fun x v => fst (leapfrog_step_test (x,v)).
Definition leapfrog_stepv_test := fun x v => snd (leapfrog_step_test (x,v)).
Definition g := fun x => F x.

Import ListNotations.
Definition _x : AST.ident := 5%positive.
Definition _v : AST.ident := 7%positive.

Definition e1 := ltac:(let e' := 
  HO_reify_float_expr constr:([_x; _v]) leapfrog_stepx_test in exact e').
Definition e :=  ltac:(let e' := 
  reify_float_expr constr:( (float32_of_Z (-1))%F32 ) in exact e').
Definition e2 := ltac:(let e' := 
  HO_reify_float_expr constr:([_x; _v]) leapfrog_stepv_test in exact e').



Goal optimize_mul e2 = Var Tsingle _x.
  simplify_shift_opt (optimize_mul e2).
Abort.

Goal optimize_div e2 = Var Tsingle _x.
  simplify_shift_div_opt (optimize_div e2).
Abort.

Goal optimize_div e1 = Var Tsingle _x.
  simplify_shift_div_opt (optimize_div e1).
Abort.


End TESTING.