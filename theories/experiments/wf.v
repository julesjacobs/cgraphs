Require Import Nat Lia.
From iris Require Import bi.

Lemma nat_wf : wf lt.
Proof.
  intros n. induction n as [|n []]; constructor; [lia|].
  intros m?. destruct (decide (m = n)); subst; eauto using Acc with lia.
Qed.

Definition bool_lt b1 b2 := b1 = false ∧ b2 = true.

Lemma bool_lt_wf : wf bool_lt.
Proof. do 2 (constructor; intros?[]). congruence. Qed.

Definition classical_well_founded {X : Type} (R : X -> X -> Prop) :=
  ∀ P, (∃ x, P x) -> ∃ t, P t ∧ ∀ y, P y -> ¬ R y t.

Lemma classical_lem :
  classical_well_founded bool_lt -> ∀ Q, Q ∨ ¬ Q.
Proof.
  unfold bool_lt. intros H Q. specialize (H (λ b, if b then true else Q)).
  destruct H as [[] []]; [exists true|specialize (H0 false)|]; naive_solver.
Qed.

Lemma wf_tc {X : Type} (R : X -> X -> Prop) :
  wf R -> wf (tc R).
Proof.
  intros H x. induction (H x). constructor. intro.
  induction 1; [|eapply IHtc]; eauto using tc_once.
Qed.

Lemma wf_no_chains {X : Type} (R: X -> X -> Prop) f :
  wf R -> ¬ ∀ i : nat, R (f (S i)) (f i).
Proof.
  intros H?. assert (∀ x, ∀ i, x ≠ f i) as G; last by eapply (G _ 0).
  intro x. induction (H x). naive_solver.
Qed.