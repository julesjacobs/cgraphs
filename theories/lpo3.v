From stdpp Require Import numbers.

Definition foo_Prop := ∀ (a b : nat → Prop),
  (∀ i j, i ≤ j → a j → a i) →
  (∀ i j, i ≤ j → b j → b i) →
  (∀ i, a i ∨ b i) →
  ¬ ((∃ i, ¬ a i) ∧ (∃ i, ¬ b i)).

Lemma foo_Prop_pf : foo_Prop.
Proof.
  intros a b Ma Mb Hab [[i Hi] [j Hj]].
  specialize (Hab (max i j)) as [H|H].
  - apply Hi. eapply Ma; [|done]. lia.
  - apply Hj. eapply Mb; [|done]. lia.
Qed.

Definition foo_Prop' := ∀ (a b : nat → Prop),
  (∀ i j, i ≤ j → a j → a i) →
  (∀ i j, i ≤ j → b j → b i) →
  (∀ i, a i ∨ b i) →
  ¬¬ ((∀ i, a i) ∨ (∀ i, b i)).

Lemma foo_Prop_pf' : foo_Prop'.
Proof.
  intros a b Ma Mb Hab H.
  
  [[i Hi] [j Hj]].
  specialize (Hab (max i j)) as [H|H].
  - apply Hi. eapply Ma; [|done]. lia.
  - apply Hj. eapply Mb; [|done]. lia.
Qed.


Lemma baz1 {A} (P : A -> Prop) : 
  ¬ (∀ x, ¬ P x) -> ¬ ¬ ∃ x, P x.
Proof. eauto. Qed.

Lemma baz2 {A B} :
  ¬ (¬ A ∧ ¬ B) -> ¬ ¬ (A ∨ B).
Proof. naive_solver. Qed.

Lemma baz3 {P Q : Prop} :
  (P -> Q) -> (¬ ¬ P -> ¬ ¬ Q).
Proof. eauto. Qed.

Lemma baz4 (P A B : Prop) :
  (A ∨ B -> P) ->
  ¬ (¬ A ∧ ¬ B) -> ¬ ¬ P.
Proof. naive_solver. Qed.

Lemma baz5 (P A B : Prop) :
  (P <-> ¬ ¬ P) ->
  (A ∨ B -> P) ->
  (¬ (¬ A ∧ ¬ B) -> P).
Proof. naive_solver. Qed.

Lemma baz6 (P A B : Prop) :
  (P <-> ¬ ¬ P) ->
  (A ∨ B -> P) ->
  (¬ (¬ A ∧ ¬ B) -> P).
Proof. naive_solver. Qed.

Lemma bar (P : Prop) (a b : nat -> Prop) :
  (P <-> ¬ ¬ P) ->
  ((∀ i, ¬ ¬ a i) ∨ (∀ i, ¬ ¬ b i) -> P) ->
  ¬ ((∃ i, ¬ a i) ∧ (∃ i, ¬ b i)) -> ¬ ¬ P.
Proof.
  intros Hneg Iab.
  cut (¬ (¬ ¬ (∃ i, ¬ a i) ∧ ¬ ¬ (∃ i, ¬ b i)) -> P).
  naive_solver. intro. eapply baz6. eauto. exact Iab. 
  intro. destruct H0.
  apply H. eauto.
  rewrite Hneg.
  eapply baz6; eauto.
  intro.
  apply Iab. destruct H.
  - left. intro.

   eauto. 