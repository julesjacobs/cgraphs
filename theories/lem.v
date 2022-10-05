From iris.proofmode Require Import tactics.
Require Import Coq.Logic.Classical.

Lemma aclassical_intros {A B C : Prop} : (A -> B ∨ C) -> (A -> B) ∨ C.
Proof.
  intros H.
  destruct (classic A).
  - destruct (H H0); eauto.
  - left. intros. naive_solver.
Qed.

Ltac classic_intros H := eapply aclassical_intros; intro H.

Lemma LEM {A:Prop} : (A -> False) ∨ A.
Proof.
  classic_intros H.
  right. apply H.
Qed.