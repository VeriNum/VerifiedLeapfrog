Section Iterate.

Variable A : Type.
Variable f : A -> A.

Inductive iterate_rel (x : A) : nat -> A -> Prop :=
| Iter_end : iterate_rel x 0 x
| Iter_step : forall n x',
  iterate_rel x n x' ->
  iterate_rel x (S n) (f x').

Fixpoint iterate (x : A) (n : nat) : A :=
  match n with
  | 0 => x
  | S n' => iterate (f x) n'
  end.

Lemma iterate_step:
  forall n x, iterate x (S n) = f (iterate x n).
Proof.
  induction n.
  - reflexivity.
  - intros; simpl in *; auto using IHn.
Qed.

Lemma iterate_rel_fix:
  forall n x x',
    iterate_rel x n x' <-> iterate x n = x'.
Proof.
  split; intros H.
  - induction H.
    + reflexivity.
    + subst.
      rewrite <- iterate_step.
      reflexivity.
  - generalize dependent x';
    generalize dependent x;
    induction n.
    + intros. subst. constructor.
    + intros. subst.
      rewrite iterate_step.
      constructor.
      apply IHn.
      reflexivity.
Qed.

End Iterate.
