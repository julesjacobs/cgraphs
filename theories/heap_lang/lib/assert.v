From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export lang.
From iris.heap_lang Require Import proofmode notation.
Set Default Proof Using "Type".

Definition assert : val :=
  λ: "v", if: "v" #() then #() else #0 #0. (* #0 #0 is unsafe *)
(* just below ;; *)
Notation "'assert:' e" := (assert (λ: <>, e)%E) (at level 99) : expr_scope.
Notation "'assert:' e" := (assert (λ: <>, e)%V) (at level 99) : val_scope.

Lemma twp_assert `{!heapG Σ} E (Φ : val → iProp Σ) e :
  WP e @ E [{ v, ⌜v = #true⌝ ∧ Φ #() }] -∗
  WP (assert: e)%V @ E [{ Φ }].
Proof.
  iIntros "HΦ". wp_lam.
  wp_apply (twp_wand with "HΦ"). iIntros (v) "[% ?]"; subst. by wp_if.
Qed.

Lemma wp_assert `{!heapG Σ} E (Φ : val → iProp Σ) e :
  WP e @ E {{ v, ⌜v = #true⌝ ∧ ▷ Φ #() }} -∗
  WP (assert: e)%V @ E {{ Φ }}.
Proof.
  iIntros "HΦ". wp_lam.
  wp_apply (wp_wand with "HΦ"). iIntros (v) "[% ?]"; subst. by wp_if.
Qed.
