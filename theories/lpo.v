From stdpp Require Import numbers.

Lemma foo {A} (P : A -> Prop): 
  ¬ (∀ x, ¬ P x) -> ¬ ¬ ∃ x, P x.
Proof.
  naive_solver.
Qed.


Definition lpo := ∀ (a : nat → bool),
  (∀ i, ¬a i) + (∃ k, a k).

Definition lpo' := ∀ (P : nat -> Prop), 
  (∀ i, Decision (P i)) -> Decision (∃ i, P i).

(* instead of nat we could also take any Countable *)

Lemma lpo_lpo' : lpo -> lpo'.
Proof.
  intros lpo P Pdec.
  destruct (lpo (fun i => bool_decide (P i))).
  - right. intros []. naive_solver.
  - left. naive_solver.
Qed.

Definition foo_Prop := ∀ (a b : nat → Prop),
  (∀ i j, i ≤ j → a j → a i) →
  (∀ i j, i ≤ j → b j → b i) →
  (∀ i, {a i} + {b i}) →
  (∀ i, a i) ∨ (∀ i, b i).

Definition sum_to_bool {A B} (x : {A} + {B}) : bool := 
  match x with
  | left _ => true
  | right _ => false
  end.

Definition LRtail (lpo : lpo') (a b : nat -> Prop) (LR : ∀ i : nat, {a i} + {b i}) :
  ∀ i, Decision (∃ j, i ≤ j ∧ sum_to_bool (LR j)).
Proof.
  intros i. apply lpo.
  intros j. 
  destruct (decide (i ≤ j)); unfold Decision.
  - destruct (decide (sum_to_bool (LR j)));[|right];naive_solver.
  - right. naive_solver.
Defined.

Lemma sum_to_bool_LR1 (lpo : lpo') (a b : nat -> Prop) (LR : ∀ i, {a i} + {b i}) (i : nat):
  sum_to_bool (LR i) -> a i.
Proof.
  destruct (LR _); simpl; naive_solver.
Qed.

Lemma sum_to_bool_LR2 (lpo : lpo') (a b : nat -> Prop) (LR : ∀ i, {a i} + {b i}) (i : nat):
  sum_to_bool (LR i) = false -> b i.
Proof.
  destruct (LR _); simpl; naive_solver.
Qed.

Lemma sum_to_bool_LRtail1 (lpo : lpo') (a b : nat -> Prop) (LR : ∀ i, {a i} + {b i}) (i : nat):
  sum_to_bool (LRtail lpo a b LR i) -> ∃ j, i ≤ j ∧ a j.
Proof.
  destruct (LRtail _) as [[j []]|H]; simpl.
  - intros _. apply sum_to_bool_LR1 in i0; naive_solver.
  - intros [].
Qed.

Lemma sum_to_bool_LRtail2 (lpo : lpo') (a b : nat -> Prop) (LR : ∀ i, {a i} + {b i}) (i : nat) :
  sum_to_bool (LRtail lpo a b LR i) = false -> ∀ j, i ≤ j -> b j.
Proof.
  destruct (LRtail _) as [[j []]|H]; simpl.
  - discriminate.
  - assert (∀ j, ¬ (i ≤ j ∧ sum_to_bool (LR j))); eauto.
    intros _ j Hij. specialize (H0 j).
    destruct (LR j); auto. simpl in *. lia.
Qed.

Lemma lpo_foo_Prop : lpo -> foo_Prop.
Proof.
  intros lpo. apply lpo_lpo' in lpo. unfold lpo' in lpo.
  intros a b Ma Mb LR.
  assert (Decision (∃ i, sum_to_bool (LRtail lpo a b LR i))).
  {
    apply lpo. intros i.
    destruct (sum_to_bool _);[left|right];naive_solver.
  }
  destruct (decide (∃ i : nat, sum_to_bool (LRtail lpo a b LR i) = false)) as [Ha|Hb].
  - right. intros j. destruct Ha as [i Ha].
    pose proof (sum_to_bool_LRtail2 lpo a b LR i Ha).
    destruct (decide (j < i)); eauto with lia.
  - left. intros i.
    assert (∃ j, i ≤ j ∧ a j).
    {
      eapply sum_to_bool_LRtail1.
      assert (∀ i, ¬ (sum_to_bool (LRtail lpo a b LR i) = false)); eauto.
      specialize (H0 i).
      apply not_false_is_true in H0. rewrite H0. done.
    }
    destruct H0 as [? []]. eauto.
Qed.