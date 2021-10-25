From stdpp Require Import countable fin_sets functions.
From iris Require Import proofmode tactics.
From diris Require Import util.


Lemma big_sepS_pure_impl {PROP : bi} `{Countable A} (s : gset A) (P : A -> PROP) (Q : A -> Prop) :
  (□ ∀ i, ⌜ i ∈ s ⌝ -∗ P i -∗ ⌜ Q i ⌝) -∗
  ([∗ set] i ∈ s, P i) -∗ ⌜ set_Forall Q s ⌝.
Proof.
  iIntros "#H G".
  iApply big_sepS_pure_1.
  iApply (big_sepS_impl with "G"). Unshelve.
  iModIntro. iIntros (x HH) "Q". Unshelve. iApply "H"; eauto.
Qed.

Lemma big_sepF_pure_impl {PROP : bi} n (P : fin n -> PROP) (Q : fin n -> Prop) :
  (□ ∀ i, P i -∗ ⌜ Q i ⌝) -∗
  ([∗ set] i ∈ all_fin n, P i) -∗ ⌜ ∀ i, Q i ⌝.
Proof.
  iIntros "#H G".
  iDestruct (big_sepS_pure_impl with "[] G") as %G.
  { iModIntro. iIntros (i Hi) "Q". iApply "H". done. }
  iPureIntro. intros.
  apply G. apply all_fin_all.
Qed.