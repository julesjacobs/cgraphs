From stdpp Require Import gmap.
From stdpp Require Import base.

Ltac qed := eauto;(repeat case_decide; (naive_solver lia || set_solver)) || solve_decision.

Lemma dec_exists_fin (P : nat → Prop) (n : nat) :
  (∀ i, P i → i < n) → (∀ i, i < n → Decision (P i)) → Decision (∃ i, P i).
Proof.
  intros Hlim Hdec.
  cut (Decision (∃ i, i < n ∧ P i)).
  { intros [|]; [left|right]; qed. }
  clear Hlim. induction n.
  - right. qed.
  - destruct IHn;[qed|..].
    + left. destruct e as [i Hi]. exists i. qed.
    + destruct (Hdec n);[qed|..].
      * left. exists n. qed.
      * right. contradict n0. destruct n0 as [i Hi].
        destruct (decide (i = n)); [|exists i]; qed.
Qed.

Definition skip (i j : nat) : nat := if decide (j < i) then j else j+1.

Lemma pigeon (n m : nat) (f : nat → nat) :
  (n > m) → (∀ i, i < n → f i < m) → ∃ i j, i < n ∧ j < n ∧ i ≠ j ∧ f i = f j.
Proof.
  revert n f; induction m; intros n f Hmn Hdom.
  { specialize (Hdom 0). qed. }

  assert (Decision (∃ i, i < n ∧ f i = m)) as [[i [Hi Hf]]|Hex]
    by (eapply dec_exists_fin; qed).
  - assert (Decision (∃ j, i ≠ j ∧ j < n ∧ f j = m)) as [[j Hj]|Hex]
      by (eapply dec_exists_fin; qed).
    { exists i,j. qed. }
    specialize (IHm (n-1) (λ j, f (skip i j))).
    destruct IHm as [j' [i' Hij']]; [qed|..].
    {
      intros j Hj.
      remember (skip i j) as j' eqn:Hj'.
      specialize (Hdom j'). unfold skip in *.
      destruct (decide (f j' = m)); [|qed].
      assert (¬ (i ≠ j' ∧ j' < n ∧ f j' = m)); qed.
    }
    exists (skip i i'),(skip i j').
    unfold skip in *. qed. 
  - specialize (IHm n f) as [i [j ?]];[qed|..|exists i,j;qed].
    { intro i. destruct (decide (f i = m)); qed. }
Qed.

From stdpp Require Import finite.

Lemma dec_exists_list {A} (P : A → Prop) (xs : list A) :
  (∀ x, P x → x ∈ xs) → (∀ x, x ∈ xs → Decision (P x)) → Decision (∃ x, P x).
Proof.
  intros HPxs Hdec.
  induction xs as [|x xs IHxs]. { right. set_solver. }
  assert (Decision (P x)) as [] by (apply Hdec; set_solver).
  { left. naive_solver. }
  apply IHxs.
  - intros x' HPx'. specialize (HPxs x' HPx').
    assert (x' = x ∨ x' ∈ xs) as []; set_solver.
  - intros ??. apply Hdec. set_solver.
Qed.

Lemma dec_forall_list {A} (P : A → Prop) (xs : list A) :
  (∀ x, P x ∨ x ∈ xs) → (∀ x, x ∈ xs → Decision (P x)) → Decision (∀ x, P x).
Proof.
  intros HPxs Hdec.
  induction xs as [|x xs IHxs]. { left. set_solver. }
  assert (Decision (P x)) as [] by (apply Hdec; set_solver);
    [|right;naive_solver].
  apply IHxs.
  - intros x'. destruct (HPxs x').
    + set_solver.
    + assert (x' = x ∨ x' ∈ xs) as []; set_solver.
  - intros ??. apply Hdec. set_solver. 
Qed.

Lemma pigeon' {A B : Type} `{FA : Finite A} `{FB : Finite B} (f : A → B) :
  card B < card A → ∃ x y, x ≠ y ∧ f x = f y.
Proof.
  assert (Decision (∃ x y : A, x ≠ y ∧ f x = f y)) as []; eauto.
  {
    destruct FA,FB. eapply dec_exists_list;[naive_solver|].
    intros ??. eapply dec_exists_list;[naive_solver|solve_decision].
  }
  assert (Inj eq eq f) as ?%inj_card
    by (intros x y; destruct (decide (x = y)); naive_solver); lia.
Qed.