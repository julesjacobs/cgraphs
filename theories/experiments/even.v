Inductive even : nat -> Prop :=
  | Z_even : even 0
  | double_even n : even n -> even (S (S n)).

Tactic Notation "simplify_eq" := repeat
  match goal with
  | H : ?f _ = ?f _ |- _ => progress injection H as H
  | H : ?f _ _ = ?f _ _ |- _ => progress injection H as H
  | H : ?f _ _ _ = ?f _ _ _ |- _ => progress injection H as H
  | H : ?f _ _ _ _ = ?f _ _ _ _ |- _ => progress injection H as H
  | H : ?f _ _ _ _ _ = ?f _ _ _ _ _ |- _ => progress injection H as H
  | H : ?f _ _ _ _ _ _ = ?f _ _ _ _ _ _ |- _ => progress injection H as H
  | H : ?x = ?x |- _ => clear H
  | H1 : ?o = Some ?x, H2 : ?o = Some ?y |- _ =>
    assert (y = x) by congruence; clear H2
  | _ => congruence || (progress subst)
  end.

Ltac inv H := inversion H; clear H; simplify_eq.

Lemma bar (n m k : nat) (P : nat -> nat -> nat -> Prop) :
  (n,S m) = (S k, n) -> P n m k.
Proof.
  intros H.
  simplify_eq.
Admitted.

Section foo.
  Variable x : nat.
  Lemma baz : x = x.
  Proof.
    reflexivity.
  Qed.
End foo.

Check baz.

Lemma foo n : even n -> even (S n) -> False.
Proof.
  induction 1; inversion 1; subst; auto.
Qed.