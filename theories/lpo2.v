From stdpp Require Import numbers.

Definition llpo := ∀ (a : nat -> bool),
  (∀ i, ∃ j, a (i+j)) ∨ (∃ i, ∀ j, ¬ a (i+j)).

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

Lemma lpo_foo_Prop : llpo -> foo_Prop.
Proof.
  unfold llpo. intros L a b Ma Mb LR.
  specialize (L (fun i => sum_to_bool (LR i))) as [].
  - left. intros i.
    specialize (H i) as [j ?].
    specialize (Ma i (i+j)). destruct (LR _); simpl in *; naive_solver lia.
  - right. intros i.
    destruct H as [j ?].
    specialize (H i). specialize (Mb i (j + i)). destruct (LR _); simpl in *;
     naive_solver lia.
Qed.