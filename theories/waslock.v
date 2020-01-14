From iris.base_logic.lib Require Import invariants.
From diris.heap_lang Require Import proofmode notation.

Definition newlock : val := λ: <>, ref #false.
Definition acquire : val := λ: "l", WAS "l" #false #true.
Definition release : val := λ: "l", "l" <- #false.

Section proof.
  Context `{!heapG Σ}.

  Definition lock_inv (l : loc) (R : iProp Σ) : iProp Σ :=
    (∃ b : bool, l ↦ #b ∗ if b then True else R)%I.

  Definition lockN : namespace := nroot .@ "lock".
  Definition is_lock (lk : val) (R : iProp Σ) : iProp Σ :=
    (∃ l: loc, ⌜ lk = #l ⌝ ∧ inv lockN (lock_inv l R))%I.

  Lemma newlock_spec (R : iProp Σ):
    {{{ R }}} newlock #() {{{ lk, RET lk; is_lock lk R }}}.
  Proof.
    iIntros (Φ) "HR HΦ". iApply wp_fupd.
    wp_lam. wp_alloc l as "Hl".
    iMod (inv_alloc lockN _ (lock_inv l R) with "[HR Hl]") as "#Hinv".
    { iNext. iExists false. iFrame. }
    iModIntro. iApply "HΦ". iExists l. eauto.
  Qed.

  Lemma acquire_spec lk R :
    {{{ is_lock lk R }}} acquire lk {{{ RET #(); R }}}.
  Proof.
    iIntros (Φ) "#Hl HΦ". iDestruct "Hl" as (l ->) "#Hinv".
    wp_lam.
    iInv lockN as (b) "[Hl HR]" "Hclose".
    wp_apply (wp_was with "Hl").
    - naive_solver.
    - iIntros "[% Hl]". iMod ("Hclose" with "[Hl]") as "_".
      { iNext. iExists true. iFrame. }
      iApply "HΦ". simplify_eq. iModIntro. iFrame.
  Qed.

  Lemma release_spec lk R :
    {{{ is_lock lk R ∗ R }}} release lk {{{ RET #(); True }}}.
  Proof.
    iIntros (Φ) "[#Hl HR] Post".
    wp_lam. iDestruct "Hl" as (l) "[-> Hinv]".
    iInv lockN as (b) "[Hl _]" "Hclose".
    wp_store. iMod ("Hclose" with "[Hl HR]") as "_".
    - iNext. iExists false. iFrame.
    - iApply "Post". done. 
  Qed.
End proof.
