From iris.proofmode Require Import tactics.
From iris.algebra Require Import excl auth gset.
From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export lang.
From iris.heap_lang Require Import proofmode notation.
From iris.heap_lang.lib Require Export lock.
Set Default Proof Using "Type".
Import uPred.

Definition wait_loop: val :=
  rec: "wait_loop" "x" "lk" :=
    let: "o" := !(Fst "lk") in
    if: "x" = "o"
      then #() (* my turn *)
      else "wait_loop" "x" "lk".

Definition newlock : val :=
  λ: <>, ((* owner *) ref #0, (* next *) ref #0).

Definition acquire : val :=
  rec: "acquire" "lk" :=
    let: "n" := !(Snd "lk") in
    if: CAS (Snd "lk") "n" ("n" + #1)
      then wait_loop "n" "lk"
      else "acquire" "lk".

Definition release : val :=
  λ: "lk", (Fst "lk") <- !(Fst "lk") + #1.

(** The CMRAs we need. *)
Class tlockG Σ :=
  tlock_G :> inG Σ (authR (prodUR (optionUR (exclR natO)) (gset_disjUR nat))).
Definition tlockΣ : gFunctors :=
  #[ GFunctor (authR (prodUR (optionUR (exclR natO)) (gset_disjUR nat))) ].

Instance subG_tlockΣ {Σ} : subG tlockΣ Σ → tlockG Σ.
Proof. solve_inG. Qed.

Section proof.
  Context `{!heapG Σ, !tlockG Σ} (N : namespace).

  Definition lock_inv (γ : gname) (lo ln : loc) (R : iProp Σ) : iProp Σ :=
    (∃ o n : nat,
      lo ↦ #o ∗ ln ↦ #n ∗
      own γ (● (Excl' o, GSet (set_seq 0 n))) ∗
      ((own γ (◯ (Excl' o, GSet ∅)) ∗ R) ∨ own γ (◯ (ε, GSet {[ o ]}))))%I.

  Definition is_lock (γ : gname) (lk : val) (R : iProp Σ) : iProp Σ :=
    (∃ lo ln : loc,
       ⌜lk = (#lo, #ln)%V⌝ ∗ inv N (lock_inv γ lo ln R))%I.

  Definition issued (γ : gname) (x : nat) : iProp Σ :=
    own γ (◯ (ε, GSet {[ x ]}))%I.

  Definition locked (γ : gname) : iProp Σ := (∃ o, own γ (◯ (Excl' o, GSet ∅)))%I.

  Global Instance lock_inv_ne γ lo ln :
    NonExpansive (lock_inv γ lo ln).
  Proof. solve_proper. Qed.
  Global Instance is_lock_ne γ lk : NonExpansive (is_lock γ lk).
  Proof. solve_proper. Qed.
  Global Instance is_lock_persistent γ lk R : Persistent (is_lock γ lk R).
  Proof. apply _. Qed.
  Global Instance locked_timeless γ : Timeless (locked γ).
  Proof. apply _. Qed.

  Lemma locked_exclusive (γ : gname) : locked γ -∗ locked γ -∗ False.
  Proof.
    iDestruct 1 as (o1) "H1". iDestruct 1 as (o2) "H2".
    iDestruct (own_valid_2 with "H1 H2") as %[[] _].
  Qed.

  Lemma newlock_spec (R : iProp Σ) :
    {{{ R }}} newlock #() {{{ lk γ, RET lk; is_lock γ lk R }}}.
  Proof.
    iIntros (Φ) "HR HΦ". rewrite -wp_fupd. wp_lam.
    wp_alloc ln as "Hln". wp_alloc lo as "Hlo".
    iMod (own_alloc (● (Excl' 0%nat, GSet ∅) ⋅ ◯ (Excl' 0%nat, GSet ∅))) as (γ) "[Hγ Hγ']".
    { by apply auth_both_valid. }
    iMod (inv_alloc _ _ (lock_inv γ lo ln R) with "[-HΦ]").
    { iNext. rewrite /lock_inv.
      iExists 0%nat, 0%nat. iFrame. iLeft. by iFrame. }
    wp_pures. iModIntro. iApply ("HΦ" $! (#lo, #ln)%V γ). iExists lo, ln. eauto.
  Qed.

  Lemma wait_loop_spec γ lk x R :
    {{{ is_lock γ lk R ∗ issued γ x }}} wait_loop #x lk {{{ RET #(); locked γ ∗ R }}}.
  Proof.
    iIntros (Φ) "[Hl Ht] HΦ". iDestruct "Hl" as (lo ln ->) "#Hinv".
    iLöb as "IH". wp_rec. subst. wp_pures. wp_bind (! _)%E.
    iInv N as (o n) "(Hlo & Hln & Ha)".
    wp_load. destruct (decide (x = o)) as [->|Hneq].
    - iDestruct "Ha" as "[Hainv [[Ho HR] | Haown]]".
      + iModIntro. iSplitL "Hlo Hln Hainv Ht".
        { iNext. iExists o, n. iFrame. }
        wp_pures. case_bool_decide; [|done]. wp_if.
        iApply ("HΦ" with "[-]"). rewrite /locked. iFrame. eauto.
      + iDestruct (own_valid_2 with "Ht Haown") as % [_ ?%gset_disj_valid_op].
        set_solver.
    - iModIntro. iSplitL "Hlo Hln Ha".
      { iNext. iExists o, n. by iFrame. }
      wp_pures. case_bool_decide; [simplify_eq |].
      wp_if. iApply ("IH" with "Ht"). iNext. by iExact "HΦ".
  Qed.

  Lemma acquire_spec γ lk R :
    {{{ is_lock γ lk R }}} acquire lk {{{ RET #(); locked γ ∗ R }}}.
  Proof.
    iIntros (ϕ) "Hl HΦ". iDestruct "Hl" as (lo ln ->) "#Hinv".
    iLöb as "IH". wp_rec. wp_bind (! _)%E. simplify_eq/=. wp_proj.
    iInv N as (o n) "[Hlo [Hln Ha]]".
    wp_load. iModIntro. iSplitL "Hlo Hln Ha".
    { iNext. iExists o, n. by iFrame. }
    wp_pures. wp_bind (CmpXchg _ _ _).
    iInv N as (o' n') "(>Hlo' & >Hln' & >Hauth & Haown)".
    destruct (decide (#n' = #n))%V as [[= ->%Nat2Z.inj] | Hneq].
    - iMod (own_update with "Hauth") as "[Hauth Hofull]".
      { eapply auth_update_alloc, prod_local_update_2.
        eapply (gset_disj_alloc_empty_local_update _ {[ n ]}).
        apply (set_seq_S_end_disjoint 0). }
      rewrite -(set_seq_S_end_union_L 0).
      wp_cmpxchg_suc. iModIntro. iSplitL "Hlo' Hln' Haown Hauth".
      { iNext. iExists o', (S n).
        rewrite Nat2Z.inj_succ -Z.add_1_r. by iFrame. }
      wp_pures.
      iApply (wait_loop_spec γ (#lo, #ln) with "[-HΦ]").
      + iFrame. rewrite /is_lock; eauto 10.
      + by iNext.
    - wp_cmpxchg_fail. iModIntro.
      iSplitL "Hlo' Hln' Hauth Haown".
      { iNext. iExists o', n'. by iFrame. }
      wp_pures. by iApply "IH"; auto.
  Qed.

  Lemma release_spec γ lk R :
    {{{ is_lock γ lk R ∗ locked γ ∗ R }}} release lk {{{ RET #(); True }}}.
  Proof.
    iIntros (Φ) "(Hl & Hγ & HR) HΦ". iDestruct "Hl" as (lo ln ->) "#Hinv".
    iDestruct "Hγ" as (o) "Hγo".
    wp_lam. wp_proj. wp_bind (! _)%E.
    iInv N as (o' n) "(>Hlo & >Hln & >Hauth & Haown)".
    wp_load.
    iDestruct (own_valid_2 with "Hauth Hγo") as
      %[[<-%Excl_included%leibniz_equiv _]%prod_included _]%auth_both_valid.
    iModIntro. iSplitL "Hlo Hln Hauth Haown".
    { iNext. iExists o, n. by iFrame. }
    wp_pures.
    iInv N as (o' n') "(>Hlo & >Hln & >Hauth & Haown)".
    iApply wp_fupd. wp_store.
    iDestruct (own_valid_2 with "Hauth Hγo") as
      %[[<-%Excl_included%leibniz_equiv _]%prod_included _]%auth_both_valid.
    iDestruct "Haown" as "[[Hγo' _]|Haown]".
    { iDestruct (own_valid_2 with "Hγo Hγo'") as %[[] ?]. }
    iMod (own_update_2 with "Hauth Hγo") as "[Hauth Hγo]".
    { apply auth_update, prod_local_update_1.
      by apply option_local_update, (exclusive_local_update _ (Excl (S o))). }
    iModIntro. iSplitR "HΦ"; last by iApply "HΦ".
    iIntros "!> !>". iExists (S o), n'.
    rewrite Nat2Z.inj_succ -Z.add_1_r. iFrame. iLeft. by iFrame.
  Qed.
End proof.

Typeclasses Opaque is_lock issued locked.

Canonical Structure ticket_lock `{!heapG Σ, !tlockG Σ} : lock Σ :=
  {| lock.locked_exclusive := locked_exclusive; lock.newlock_spec := newlock_spec;
     lock.acquire_spec := acquire_spec; lock.release_spec := release_spec |}.
