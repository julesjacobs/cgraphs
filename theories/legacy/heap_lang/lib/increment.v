From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Export invariants.
From iris.program_logic Require Export atomic.
From iris.heap_lang Require Import proofmode notation atomic_heap par.
Set Default Proof Using "Type".

(** Show that implementing fetch-and-add on top of CAS preserves logical
atomicity. *)

(** First: logically atomic increment directly on top of the physical heap. *)

Section increment_physical.
  Context `{!heapG Σ}.

  Definition incr_phy : val :=
    rec: "incr" "l" :=
       let: "oldv" := !"l" in
       if: CAS "l" "oldv" ("oldv" + #1)
         then "oldv" (* return old value if success *)
         else "incr" "l".

  Lemma incr_phy_spec (l: loc) :
    <<< ∀ (v : Z), l ↦ #v >>> incr_phy #l @ ⊤ <<< l ↦ #(v + 1), RET #v >>>.
  Proof.
    iIntros (Φ) "AU". iLöb as "IH". wp_lam.
    wp_bind (!_)%E. iMod "AU" as (v) "[Hl [Hclose _]]".
    wp_load. iMod ("Hclose" with "Hl") as "AU". iModIntro.
    wp_pures. wp_bind (CmpXchg _ _ _)%E. iMod "AU" as (w) "[Hl Hclose]".
    destruct (decide (#v = #w)) as [[= ->]|Hx].
    - wp_cmpxchg_suc. iDestruct "Hclose" as "[_ Hclose]". iMod ("Hclose" with "Hl") as "HΦ".
      iModIntro. wp_pures. done.
    - wp_cmpxchg_fail. iDestruct "Hclose" as "[Hclose _]". iMod ("Hclose" with "Hl") as "AU".
      iModIntro. wp_pures. iApply "IH". done.
  Qed.
End increment_physical.

(** Next: logically atomic increment on top of an arbitrary logically atomic heap *)

Section increment.
  Context `{!heapG Σ} {aheap: atomic_heap Σ}.

  Import atomic_heap.notation.

  Definition incr : val :=
    rec: "incr" "l" :=
       let: "oldv" := !"l" in
       if: CAS "l" "oldv" ("oldv" + #1)
         then "oldv" (* return old value if success *)
         else "incr" "l".

  (** A proof of the incr specification that unfolds the definition
      of atomic accessors.  Useful for introducing them as a concept,
      but see below for a shorter proof. *)
  Lemma incr_spec_direct (l: loc) :
    <<< ∀ (v : Z), l ↦ #v >>> incr #l @ ⊤ <<< l ↦ #(v + 1), RET #v >>>.
  Proof.
    iIntros (Φ) "AU". iLöb as "IH". wp_lam.
    awp_apply load_spec.
    (* Prove the atomic update for load *)
    rewrite /atomic_acc /=. iMod "AU" as (v) "[Hl [Hclose _]]".
    iModIntro. iExists _, _. iFrame "Hl". iSplit.
    { (* abort case *) done. }
    iIntros "Hl". iMod ("Hclose" with "Hl") as "AU". iModIntro.
    (* Now go on *)
    awp_apply cas_spec; first done.
    (* Prove the atomic update for CAS *)
    rewrite /atomic_acc /=. iMod "AU" as (w) "[Hl Hclose]".
    iModIntro. iExists _. iFrame "Hl". iSplit.
    { (* abort case *) iDestruct "Hclose" as "[? _]". done. }
    iIntros "Hl". simpl. destruct (decide (#w = #v)) as [[= ->]|Hx].
    - iDestruct "Hclose" as "[_ Hclose]". iMod ("Hclose" with "Hl") as "HΦ".
      iIntros "!>". wp_if. by iApply "HΦ".
    - iDestruct "Hclose" as "[Hclose _]". iMod ("Hclose" with "Hl") as "AU".
      iIntros "!>". wp_if. iApply "IH". done.
  Qed.

  (** A proof of the incr specification that uses lemmas to avoid reasining
      with the definition of atomic accessors. *)
  Lemma incr_spec (l: loc) :
    <<< ∀ (v : Z), l ↦ #v >>> incr #l @ ⊤ <<< l ↦ #(v + 1), RET #v >>>.
  Proof.
    iIntros (Φ) "AU". iLöb as "IH". wp_lam.
    awp_apply load_spec.
    (* Prove the atomic update for load *)
    iApply (aacc_aupd_abort with "AU"); first done.
    iIntros (x) "H↦". iAaccIntro with "H↦"; first by eauto with iFrame.
    iIntros "$ !> AU !>".
    (* Now go on *)
    awp_apply cas_spec; first done.
    (* Prove the atomic update for CAS *)
    iApply (aacc_aupd with "AU"); first done.
    iIntros (x') "H↦". iAaccIntro with "H↦"; first by eauto with iFrame.
    iIntros "H↦ !>".
    simpl. destruct (decide (#x' = #x)) as [[= ->]|Hx].
    - iRight. iFrame. iIntros "HΦ !>".
      wp_if. by iApply "HΦ".
    - iLeft. iFrame. iIntros "AU !>".
      wp_if. iApply "IH". done.
  Qed.

  (** A "weak increment": assumes that there is no race *)
  Definition weak_incr: val :=
    rec: "weak_incr" "l" :=
       let: "oldv" := !"l" in
       "l" <- ("oldv" + #1);;
       "oldv" (* return old value *).

  (** Logically atomic spec for weak increment. Also an example for what TaDA
      calls "private precondition". *)
  (* TODO: Generalize to q and 1-q, based on some theory for a "maybe-mapsto"
     connective that works on [option Qp] (the type of 1-q). *)
  Lemma weak_incr_spec (l: loc) (v : Z) :
    l ↦{1/2} #v -∗
    <<< ∀ (v' : Z), l ↦{1/2} #v' >>>
      weak_incr #l @ ⊤
    <<< ⌜v = v'⌝ ∗ l ↦ #(v + 1), RET #v >>>.
  Proof.
    iIntros "Hl" (Φ) "AU". wp_lam.
    wp_apply (atomic_wp_seq $! (load_spec _) with "Hl").
    iIntros "Hl". awp_apply store_spec.
    (* Prove the atomic update for store *)
    iApply (aacc_aupd_commit with "AU"); first done.
    iIntros (x) "H↦".
    iDestruct (mapsto_agree with "Hl H↦") as %[= <-].
    iCombine "Hl" "H↦" as "Hl". iAaccIntro with "Hl".
    { iIntros "[$ $]"; eauto. }
    iIntros "$ !>". iSplit; first done.
    iIntros "HΦ !>". wp_seq. done.
  Qed.

End increment.

Section increment_client.
  Context `{!heapG Σ, !spawnG Σ}.

  Existing Instance primitive_atomic_heap.

  Definition incr_client : val :=
    λ: "x",
       let: "l" := ref "x" in
       incr "l" ||| incr "l".

  Lemma incr_client_safe (x: Z):
    WP incr_client #x {{ _, True }}%I.
  Proof using Type*.
    wp_lam. wp_alloc l as "Hl".
    iMod (inv_alloc nroot _ (∃x':Z, l ↦ #x')%I with "[Hl]") as "#Hinv"; first eauto.
    (* FIXME: I am only using persistent stuff, so I should be allowed
       to move this to the persisten context even without the additional □. *)
    iAssert (□ WP incr #l {{ _, True }})%I as "#Aupd".
    { iAlways. awp_apply incr_spec. clear x.
      iInv nroot as (x) ">H↦". iAaccIntro with "H↦"; first by eauto 10.
      iIntros "H↦ !>". iSplitL "H↦"; first by eauto 10.
      (* The continuation: From after the atomic triple to the postcondition of the WP *)
      done.
    }
    wp_apply wp_par.
    - iAssumption.
    - iAssumption.
    - iIntros (??) "_ !>". done.
  Qed.

End increment_client.
