From iris.proofmode Require Export base tactics classes.

Lemma bar (P A : Prop) : ((P ∨ ¬ P) -> A) -> ¬ ¬ A.
Proof.
  intros H.
  cut ((¬ ¬ (P ∨ ¬ P) -> ¬ ¬ A)).
  - intros H2.
    eapply H2. admit.
  - intros H2 nA. eapply H2. intros Q.
    eapply nA. eapply H. apply Q.
Admitted.

Lemma bar' (A : Prop) : ((∀ P, P ∨ ¬ P) -> A) -> ¬ ¬ A.
Proof.
  intros H.
  cut (((∀ P, ¬ ¬ (P ∨ ¬ P)) -> ¬ ¬ A)).
  - admit.
  - intros H2 nA. eapply H2. intros Q.
  eapply nA. eapply H. apply Q.
Admitted.

Lemma foo (A : Prop) : ((∀ P, P ∨ ¬ P) -> A) -> ¬ ¬ A.
Proof.
  intros H.
  eapply (bar (∀ P, P ∨ ¬ P)).
  intros L.
  destruct L.
  - eauto.
  - intro. eapply H0.
  Na.



Axiom (A B C D : Prop).

Axiom ab : A -> B.
Axiom bc : B -> C.
Axiom cc : C -> C.
Axiom foo : (A -> C) -> D.

Create HintDb X.
Hint Resolve ab bc cc foo : X.

Lemma bar : D.
Proof.
  debug eauto with X.
Qed.

Print bar.

Class Y (p : Prop) := { inh : p }.

Instance yab : Y A -> Y B.
Proof.
  intros []. constructor.
  apply ab. assumption.
Qed.

Instance ybc : Y B -> Y C.
Proof.
  intros []. constructor.
  apply bc. assumption.
Qed.

Instance yfoo : (Y A -> Y C) -> Y D.
Proof.
  intros H. constructor.
  eapply foo. intro.
  destruct H.
  - constructor. assumption.
  - assumption.
Qed.

Definition f : D := inh.

Print f.

Instance ybc

Instance yab : Y A -> Y B :=
  fun H : Y A =>
  match H with
  | {| inh := x |} => {| inh := ab x |}
  end.

Instance

Print yab.
  done.