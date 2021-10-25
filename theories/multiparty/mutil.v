From stdpp Require Import countable fin_sets functions.
From iris Require Import proofmode tactics.
From diris Require Import util bi.


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

Lemma big_sepS_impl1 {PROP : bi} `{Countable A} (s : gset A) (P P' : A -> PROP) (x0 : A) :
  x0 ∈ s ->
  □ (∀ x, ⌜⌜ x ≠ x0 ⌝⌝ -∗ P x -∗ P' x) -∗
    (P x0 -∗ P' x0) -∗
    ([∗ set] x ∈ s, P x) -∗ [∗ set] x ∈ s, P' x.
Proof.
  iIntros (Hx0) "#Hr H1 H".
  rewrite big_sepS_delete //.
  iApply big_sepS_delete; first done.
  iDestruct "H" as "[H0 H]".
  iSplitL "H1 H0".
  - iApply "H1". done.
  - iApply (big_sepS_impl with "H"). iModIntro.
    iIntros (x Hx) "H".
    iApply ("Hr" with "[%] H"). set_solver.
Qed.