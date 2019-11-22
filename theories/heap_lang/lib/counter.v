From iris.proofmode Require Import tactics.
From iris.algebra Require Import lib.frac_auth auth.
From iris.base_logic.lib Require Export invariants.
From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export lang.
From iris.heap_lang Require Import proofmode notation.
Set Default Proof Using "Type".

Definition newcounter : val := λ: <>, ref #0.
Definition incr : val := rec: "incr" "l" :=
    let: "n" := !"l" in
    if: CAS "l" "n" (#1 + "n") then #() else "incr" "l".
Definition read : val := λ: "l", !"l".

(** Monotone counter *)
Class mcounterG Σ := MCounterG { mcounter_inG :> inG Σ (authR mnatUR) }.
Definition mcounterΣ : gFunctors := #[GFunctor (authR mnatUR)].

Instance subG_mcounterΣ {Σ} : subG mcounterΣ Σ → mcounterG Σ.
Proof. solve_inG. Qed.

Section mono_proof.
  Context `{!heapG Σ, !mcounterG Σ} (N : namespace).

  Definition mcounter_inv (γ : gname) (l : loc) : iProp Σ :=
    (∃ n, own γ (● (n : mnat)) ∗ l ↦ #n)%I.

  Definition mcounter (l : loc) (n : nat) : iProp Σ :=
    (∃ γ, inv N (mcounter_inv γ l) ∧ own γ (◯ (n : mnat)))%I.

  (** The main proofs. *)
  Global Instance mcounter_persistent l n : Persistent (mcounter l n).
  Proof. apply _. Qed.

  Lemma newcounter_mono_spec :
    {{{ True }}} newcounter #() {{{ l, RET #l; mcounter l 0 }}}.
  Proof.
    iIntros (Φ) "_ HΦ". rewrite -wp_fupd /newcounter /=. wp_lam. wp_alloc l as "Hl".
    iMod (own_alloc (● (O:mnat) ⋅ ◯ (O:mnat))) as (γ) "[Hγ Hγ']";
      first by apply auth_both_valid.
    iMod (inv_alloc N _ (mcounter_inv γ l) with "[Hl Hγ]").
    { iNext. iExists 0%nat. by iFrame. }
    iModIntro. iApply "HΦ". rewrite /mcounter; eauto 10.
  Qed.

  Lemma incr_mono_spec l n :
    {{{ mcounter l n }}} incr #l {{{ RET #(); mcounter l (S n) }}}.
  Proof.
    iIntros (Φ) "Hl HΦ". iLöb as "IH". wp_rec.
    iDestruct "Hl" as (γ) "[#? Hγf]".
    wp_bind (! _)%E. iInv N as (c) ">[Hγ Hl]".
    wp_load. iModIntro. iSplitL "Hl Hγ"; [iNext; iExists c; by iFrame|].
    wp_pures. wp_bind (CmpXchg _ _ _).
    iInv N as (c') ">[Hγ Hl]".
    destruct (decide (c' = c)) as [->|].
    - iDestruct (own_valid_2 with "Hγ Hγf")
        as %[?%mnat_included _]%auth_both_valid.
      iMod (own_update_2 with "Hγ Hγf") as "[Hγ Hγf]".
      { apply auth_update, (mnat_local_update _ _ (S c)); auto. }
      wp_cmpxchg_suc. iModIntro. iSplitL "Hl Hγ".
      { iNext. iExists (S c). rewrite Nat2Z.inj_succ Z.add_1_l. by iFrame. }
      wp_pures. iApply "HΦ"; iExists γ; repeat iSplit; eauto.
      iApply (own_mono with "Hγf").
      (* FIXME: FIXME(Coq #6294): needs new unification *)
      apply: auth_frag_mono. by apply mnat_included, le_n_S.
    - wp_cmpxchg_fail; first (by intros [= ?%Nat2Z.inj]). iModIntro.
      iSplitL "Hl Hγ"; [iNext; iExists c'; by iFrame|].
      wp_pures. iApply ("IH" with "[Hγf] [HΦ]"); last by auto.
      rewrite {3}/mcounter; eauto 10.
  Qed.

  Lemma read_mono_spec l j :
    {{{ mcounter l j }}} read #l {{{ i, RET #i; ⌜j ≤ i⌝%nat ∧ mcounter l i }}}.
  Proof.
    iIntros (ϕ) "Hc HΦ". iDestruct "Hc" as (γ) "[#Hinv Hγf]".
    rewrite /read /=. wp_lam. iInv N as (c) ">[Hγ Hl]".
    wp_load.
    iDestruct (own_valid_2 with "Hγ Hγf")
      as %[?%mnat_included _]%auth_both_valid.
    iMod (own_update_2 with "Hγ Hγf") as "[Hγ Hγf]".
    { apply auth_update, (mnat_local_update _ _ c); auto. }
    iModIntro. iSplitL "Hl Hγ"; [iNext; iExists c; by iFrame|].
    iApply ("HΦ" with "[-]"). rewrite /mcounter; eauto 10.
  Qed.
End mono_proof.

(** Counter with contributions *)
Class ccounterG Σ :=
  CCounterG { ccounter_inG :> inG Σ (frac_authR natR) }.
Definition ccounterΣ : gFunctors :=
  #[GFunctor (frac_authR natR)].

Instance subG_ccounterΣ {Σ} : subG ccounterΣ Σ → ccounterG Σ.
Proof. solve_inG. Qed.

Section contrib_spec.
  Context `{!heapG Σ, !ccounterG Σ} (N : namespace).

  Definition ccounter_inv (γ : gname) (l : loc) : iProp Σ :=
    (∃ n, own γ (●F n) ∗ l ↦ #n)%I.

  Definition ccounter_ctx (γ : gname) (l : loc) : iProp Σ :=
    inv N (ccounter_inv γ l).

  Definition ccounter (γ : gname) (q : frac) (n : nat) : iProp Σ :=
    own γ (◯F{q} n).

  (** The main proofs. *)
  Lemma ccounter_op γ q1 q2 n1 n2 :
    ccounter γ (q1 + q2) (n1 + n2) ⊣⊢ ccounter γ q1 n1 ∗ ccounter γ q2 n2.
  Proof. by rewrite /ccounter frac_auth_frag_op -own_op. Qed.

  Lemma newcounter_contrib_spec (R : iProp Σ) :
    {{{ True }}} newcounter #()
    {{{ γ l, RET #l; ccounter_ctx γ l ∗ ccounter γ 1 0 }}}.
  Proof.
    iIntros (Φ) "_ HΦ". rewrite -wp_fupd /newcounter /=. wp_lam. wp_alloc l as "Hl".
    iMod (own_alloc (●F O%nat ⋅ ◯F 0%nat)) as (γ) "[Hγ Hγ']";
      first by apply auth_both_valid.
    iMod (inv_alloc N _ (ccounter_inv γ l) with "[Hl Hγ]").
    { iNext. iExists 0%nat. by iFrame. }
    iModIntro. iApply "HΦ". rewrite /ccounter_ctx /ccounter; eauto 10.
  Qed.

  Lemma incr_contrib_spec γ l q n :
    {{{ ccounter_ctx γ l ∗ ccounter γ q n }}} incr #l
    {{{ RET #(); ccounter γ q (S n) }}}.
  Proof.
    iIntros (Φ) "[#? Hγf] HΦ". iLöb as "IH". wp_rec.
    wp_bind (! _)%E. iInv N as (c) ">[Hγ Hl]".
    wp_load. iModIntro. iSplitL "Hl Hγ"; [iNext; iExists c; by iFrame|].
    wp_pures. wp_bind (CmpXchg _ _ _).
    iInv N as (c') ">[Hγ Hl]".
    destruct (decide (c' = c)) as [->|].
    - iMod (own_update_2 with "Hγ Hγf") as "[Hγ Hγf]".
      { apply frac_auth_update, (nat_local_update _ _ (S c) (S n)); lia. }
      wp_cmpxchg_suc. iModIntro. iSplitL "Hl Hγ".
      { iNext. iExists (S c). rewrite Nat2Z.inj_succ Z.add_1_l. by iFrame. }
      wp_pures. by iApply "HΦ".
    - wp_cmpxchg_fail; first (by intros [= ?%Nat2Z.inj]).
      iModIntro. iSplitL "Hl Hγ"; [iNext; iExists c'; by iFrame|].
      wp_pures. by iApply ("IH" with "[Hγf] [HΦ]"); auto.
  Qed.

  Lemma read_contrib_spec γ l q n :
    {{{ ccounter_ctx γ l ∗ ccounter γ q n }}} read #l
    {{{ c, RET #c; ⌜n ≤ c⌝%nat ∧ ccounter γ q n }}}.
  Proof.
    iIntros (Φ) "[#? Hγf] HΦ".
    rewrite /read /=. wp_lam. iInv N as (c) ">[Hγ Hl]". wp_load.
    iDestruct (own_valid_2 with "Hγ Hγf") as % ?%frac_auth_included_total%nat_included.
    iModIntro. iSplitL "Hl Hγ"; [iNext; iExists c; by iFrame|].
    iApply ("HΦ" with "[-]"); rewrite /ccounter; eauto 10.
  Qed.

  Lemma read_contrib_spec_1 γ l n :
    {{{ ccounter_ctx γ l ∗ ccounter γ 1 n }}} read #l
    {{{ n, RET #n; ccounter γ 1 n }}}.
  Proof.
    iIntros (Φ) "[#? Hγf] HΦ".
    rewrite /read /=. wp_lam. iInv N as (c) ">[Hγ Hl]". wp_load.
    iDestruct (own_valid_2 with "Hγ Hγf") as % <-%frac_auth_agreeL.
    iModIntro. iSplitL "Hl Hγ"; [iNext; iExists c; by iFrame|].
    by iApply "HΦ".
  Qed.
End contrib_spec.
