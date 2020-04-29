From iris.proofmode Require Import tactics.
From iris.algebra Require Import gmap auth agree gset coPset.
From iris.base_logic.lib Require Import wsat.
From diris.program_logic Require Export weakestpre.
Set Default Proof Using "Type".
Import uPred.

(** This file contains the adequacy statements of the Iris program logic. First
we prove a number of auxiliary results. *)
Section adequacy.
Context `{!irisG Λ Σ ξ}.
Implicit Types e : expr Λ.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types Φs : list (val Λ → iProp Σ).

Notation wptp s j t := ([∗ list] i ↦ ef ∈ t, WP ef @ (tid_set (i+j) s); ⊤ {{ fork_post (i+j) }})%I.

Lemma wp_step s i e1 ζ σ1 κ κs e2 σ2 efs es Φ :
  tid_get s i →
  es !! i = Some e1 →
  prim_step e1 σ1 κ e2 σ2 efs →
  state_interp ζ σ1 (κ ++ κs) es -∗ WP e1 @ s; ⊤ {{ Φ }} ={⊤,∅}▷=∗
  ∃ ζ', state_interp ζ' σ2 κs (<[i:=e2]> es ++ efs) ∗ WP e2 @ s; ⊤ {{ Φ }} ∗ wptp s (length es) efs.
Proof.
  rewrite {1}wp_unfold /wp_pre. iIntros (???) "Hσ H".
  rewrite (val_stuck e1 σ1 κ e2 σ2 efs) //.
  iMod ("H" $! _ σ1 _ _ _ with "[%] Hσ") as "(_ & H)".
  { done. }
  iMod ("H" $! e2 σ2 efs with "[//]") as "H".
  by iIntros "!> !>".
Qed.

Lemma wptp_step s e1 t1 t2 κ κs σ1 σ2 Φ :
  tid_get s 0 →
  step (e1 :: t1,σ1) κ (t2, σ2) →
  (∃ ζ, state_interp ζ σ1 (κ ++ κs) (e1 :: t1)) -∗ WP e1 @ s; ⊤ {{ Φ }} -∗ wptp s 1 t1 ==∗
  ∃ e2 t2', ⌜t2 = e2 :: t2'⌝ ∗
  |={⊤,∅}▷=> ∃ ζ', state_interp ζ' σ2 κs t2 ∗ WP e2 @ s; ⊤ {{ Φ }} ∗ wptp s 1 t2'.
Proof.
  iIntros (Htid Hstep) "Hσ He Ht".
  destruct Hstep as [e1' σ1' e2' σ2' efs [|? t1'] t2' ?? Hstep]; simplify_eq/=.
  - iExists e2', (t2' ++ efs). iModIntro. iSplitR; first by eauto.
    iMod (wp_step with "Hσ He") as "H". [done..|].
    iIntros "!> !>". iMod "H" as "(Hσ & He2 & Hefs)".
    iIntros "!>". iFrame.
  - iExists e, (t1' ++ e2' :: t2' ++ efs); iSplitR; first eauto.
    iFrame "He". iDestruct "Ht" as "(Ht1 & He1 & Ht2)".
    iModIntro. iMod (wp_step with "Hσ He1") as "H".
    { by rewrite Nat.add_0_r /= lookup_app_r // Nat.sub_diag. }
    { done. }
    iIntros "!> !>". iMod "H" as "(Hσ & He2 & Hefs)". iIntros "!>".
    iSplitL "Hσ".
    { by rewrite Nat.add_0_r /= insert_app_r_alt // Nat.sub_diag /= -assoc_L. }
    iFrame "Ht1 Ht2 He2". simpl.
    iApply (big_sepL_impl with "Hefs").
    iModIntro. iIntros.
    by rewrite !app_length /= !Nat.add_succ_r !Nat.add_assoc /=.
Qed.


Lemma wptp_steps s n e1 t1 κs κs' t2 σ1 σ2 Φ :
  language.nsteps n (e1 :: t1, σ1) κs (t2, σ2) →
  state_interp σ1 (κs ++ κs') (e1 :: t1) -∗ WP e1 @ (s,0); ⊤ {{ Φ }} -∗ wptp s 1 t1
  ={⊤,∅}▷=∗^n ∃ e2 t2',
    ⌜t2 = e2 :: t2'⌝ ∗
    state_interp σ2 κs' t2 ∗
    WP e2 @ (s,0); ⊤ {{ Φ }} ∗ wptp s 1 t2'.
Proof.
  revert e1 t1 κs κs' t2 σ1 σ2; simpl.
  induction n as [|n IH]=> e1 t1 κs κs' t2 σ1 σ2 /=.
  { inversion_clear 1; iIntros "???"; iExists e1, t1; iFrame; eauto 10. }
  iIntros (Hsteps) "Hσ He Ht". inversion_clear Hsteps as [|?? [t1' σ1']].
  rewrite -(assoc_L (++)).
  iMod (wptp_step with "Hσ He Ht") as (e1' t1'' ?) ">H"; first eauto; simplify_eq.
  iIntros "!> !>". iMod "H" as "(Hσ & He & Ht)". iModIntro.
  by iApply (IH with "Hσ He Ht").
Qed.

Definition not_stuck_waiting tid e σ :=
  (⌜is_Some (to_val e) ∨ reducible e σ⌝ ∨ legally_waiting tid e σ)%I.

Lemma wp_not_stuck κs es e σ Φ i :
  es !! i = Some e ->
  state_interp σ κs es -∗
  WP e @ (NotStuck,i); ⊤ {{ Φ }} ={⊤,∅}=∗
  not_stuck_waiting i e σ ∗ |={⊤,∅}=> state_interp σ κs es.
Proof.
  rewrite wp_unfold /wp_pre /not_stuck_waiting. iIntros (?) "Hσ H".
  destruct (to_val e) as [v|] eqn:?.
  { iMod (fupd_intro_mask' ⊤ ∅); eauto 6. }
  iMod ("H" $! σ [] κs _ with "[//] Hσ") as "[[%|H] _]"; eauto.
Qed.

Lemma wptp_strong_adequacy Φ κs' s n e1 t1 κs t2 σ1 σ2 :
  language.nsteps n (e1 :: t1, σ1) κs (t2, σ2) →
  state_interp σ1 (κs ++ κs') (e1 :: t1) -∗
  WP e1 @ (s,0); ⊤ {{ Φ }} -∗
  wptp s 1 t1 ={⊤,∅}▷=∗^(S n) ∃ e2 t2',
    ⌜ t2 = e2 :: t2' ⌝ ∗
    (∀ i e, ⌜t2 !! i = Some e⌝ -∗
      ⌜s = NotStuck⌝ ={⊤,∅}=∗
      not_stuck_waiting i e σ2) ∗
    state_interp σ2 κs' t2 ∗
    from_option Φ True (to_val e2) ∗
    ([∗ list] i ↦ e ∈ t2', from_option (fork_post (1+i)) True (to_val e)).
Proof.
  iIntros (Hstep) "Hσ He Ht". rewrite Nat_iter_S_r.
  iDestruct (wptp_steps with "Hσ He Ht") as "Hwp"; first done.
  iApply (step_fupdN_wand with "Hwp").
  iDestruct 1 as (e2' t2' ?) "(Hσ & Hwp & Ht)"; simplify_eq/=.
  Check ((e2' :: t2') !! 0).

  iMod (fupd_plain_keep_l ⊤
    (∀ (i : nat) (e : expr Λ), ⌜(e2' :: t2') !! i = Some e⌝ -∗ ⌜s = NotStuck⌝ ={⊤,∅}=∗ not_stuck_waiting i e σ2)%I
    (state_interp σ2 κs' (e2' :: t2') ∗ WP e2' @ (s,0); ⊤ {{ v, Φ v }} ∗ wptp s 1 t2')%I
    with "[$Hσ $Hwp $Ht]") as "(Hsafe&Hσ&Hwp&Hvs)".
  { iIntros "(Hσ & Hwp & Ht)".
    iModIntro.
    iIntros (i e He' ->).
    destruct i as [|i].
    - simpl in He'.
    apply elem_of_cons in He' as [<-|(t1''&t2''&->)%elem_of_list_split].
    - iMod (wp_not_stuck with "Hσ Hwp") as "$"; auto.
    - iDestruct "Ht" as "(_ & He' & _)". rewrite Nat.add_0_r /=.
      iApply (wp_not_stuck with "Hσ He'").
      by rewrite /= lookup_app_r // Nat.sub_diag. }
  iApply step_fupd_fupd. iApply step_fupd_intro; first done. iNext.
  iExists _, _. iSplitL ""; first done. iFrame "Hsafe Hσ".
  iSplitL "Hwp".
  - destruct (to_val e2') as [v2|] eqn:He2'; last done.
    apply of_to_val in He2' as <-. iApply (wp_value_inv' with "Hwp").
  - clear Hstep.
    iApply big_sepL_fupd.
    iApply (big_sepL_impl with "Hvs").
    iIntros "!>" (i e ?) "He /=".
    destruct (to_val e) as [v|] eqn:He; last by auto.
    apply of_to_val in He as <-. iApply (wp_value_inv' with "He").
Qed.
End adequacy.

(** Iris's generic adequacy result *)
Theorem wp_strong_adequacy Σ Λ `{!invPreG Σ} e1 σ1 n κs t2 σ2 φ :
  (∀ `{Hinv : !invG Σ},
     (|={⊤}=> ∃
         (s: stuckness)
         (stateI : state Λ → list (observation Λ) → list (expr Λ) → iProp Σ)
         (Φ : val Λ → iProp Σ)
         (fork_post : nat → val Λ → iProp Σ),
       let _ : irisG Λ Σ := IrisG _ _ Hinv stateI fork_post in
       stateI σ1 κs [e1] ∗
       WP e1 @ (s,0); ⊤ {{ Φ }} ∗
       (∀ e2 t2',
         (* e2 is the final state of the main thread, t2' the rest *)
         ⌜ t2 = e2 :: t2' ⌝ -∗
         (* If this is a stuck-free triple (i.e. [s = NotStuck]), then all
         threads in [t2] are either done (a value) or reducible *)
         ⌜ ∀ e2, s = NotStuck → e2 ∈ t2 → not_stuck e2 σ2 ⌝ -∗
         (* The state interpretation holds for [σ2] *)
         stateI σ2 [] (e2 :: t2') -∗
         (* If the main thread is done, its post-condition [Φ] holds *)
         from_option Φ True (to_val e2) -∗
         (* For all threads that are done, their postcondition [fork_post] holds. *)
         ([∗ list] i ↦ e ∈ t2', from_option (fork_post (1+i)) True (to_val e)) -∗
         (* Under all these assumptions, and while opening all invariants, we
         can conclude [φ] in the logic. After opening all required invariants,
         one can use [fupd_intro_mask'] or [fupd_mask_weaken] to introduce the
         fancy update. *)
         |={⊤,∅}=> ⌜ φ ⌝))%I) →
  language.nsteps n ([e1], σ1) κs (t2, σ2) →
  (* Then we can conclude [φ] at the meta-level. *)
  φ.
Proof.
  intros Hwp ?.
  eapply (step_fupdN_soundness' _ (S (S n)))=> Hinv. rewrite Nat_iter_S.
  iMod Hwp as (s stateI Φ fork_post) "(Hσ & Hwp & Hφ)".
  iApply step_fupd_intro; [done|]; iModIntro.
  iApply step_fupdN_S_fupd. iApply (step_fupdN_wand with "[-Hφ]").
  { iApply (@wptp_strong_adequacy _ _ (IrisG _ _ Hinv stateI fork_post) _ []
    with "[Hσ] Hwp"); eauto; by rewrite right_id_L. }
  iIntros "Hpost". iDestruct "Hpost" as (e2 t2' ->) "(? & ? & ? & ?)".
  iApply fupd_plain_mask_empty.
  iMod ("Hφ" with "[% //] [$] [$] [$] [$]"). done.
Qed.

(** Since the full adequacy statement is quite a mouthful, we prove some more
intuitive and simpler corollaries. These lemmas are morover stated in terms of
[rtc erased_step] so one does not have to provide the trace. *)
Record adequate {Λ} (s : stuckness) (e1 : expr Λ) (σ1 : state Λ)
    (φ : val Λ → state Λ → Prop) := {
  adequate_result t2 σ2 v2 :
   rtc erased_step ([e1], σ1) (of_val v2 :: t2, σ2) → φ v2 σ2;
  adequate_not_stuck t2 σ2 e2 :
   s = NotStuck →
   rtc erased_step ([e1], σ1) (t2, σ2) →
   e2 ∈ t2 → not_stuck e2 σ2
}.

Lemma adequate_alt {Λ} s e1 σ1 (φ : val Λ → state Λ → Prop) :
  adequate s e1 σ1 φ ↔ ∀ t2 σ2,
    rtc erased_step ([e1], σ1) (t2, σ2) →
      (∀ v2 t2', t2 = of_val v2 :: t2' → φ v2 σ2) ∧
      (∀ e2, s = NotStuck → e2 ∈ t2 → not_stuck e2 σ2).
Proof. split. intros []; naive_solver. constructor; naive_solver. Qed.

(*
  This should hold in deadlock free iris.

Theorem adequate_tp_safe {Λ} (e1 : expr Λ) t2 σ1 σ2 φ :
  adequate NotStuck e1 σ1 φ →
  rtc erased_step ([e1], σ1) (t2, σ2) →
  Forall (λ e, is_Some (to_val e)) t2 ∨ ∃ t3 σ3, erased_step (t2, σ2) (t3, σ3).
Proof.
  intros Had ?.
  destruct (decide (Forall (λ e, is_Some (to_val e)) t2)) as [|Ht2]; [by left|].
  apply (not_Forall_Exists _), Exists_exists in Ht2; destruct Ht2 as (e2&?&He2).
  destruct (adequate_not_stuck NotStuck e1 σ1 φ Had t2 σ2 e2) as [?|(κ&e3&σ3&efs&?)];
    rewrite ?eq_None_not_Some; auto.
  { exfalso. eauto. }
  destruct (elem_of_list_split t2 e2) as (t2'&t2''&->); auto.
  right; exists (t2' ++ e3 :: t2'' ++ efs), σ3, κ; econstructor; eauto.
Qed.*)

Corollary wp_adequacy Σ Λ `{!invPreG Σ} s e σ φ :
  (∀ `{Hinv : !invG Σ} κs,
     (|={⊤}=> ∃
         (stateI : state Λ → list (observation Λ) → iProp Σ)
         (fork_post : nat → val Λ → iProp Σ),
       let _ : irisG Λ Σ := IrisG _ _ Hinv (λ σ κs _, stateI σ κs) fork_post in
       stateI σ κs ∗ WP e @ (s,0); ⊤ {{ v, ⌜φ v⌝ }})%I) →
  adequate s e σ (λ v _, φ v).
Proof.
  intros Hwp. apply adequate_alt; intros t2 σ2 [n [κs Hsteps]]%erased_steps_nsteps.
  eapply (wp_strong_adequacy Σ _); [|exact Hsteps]=> ?.
  iMod Hwp as (stateI fork_post) "[Hσ Hwp]".
  iExists s, (λ σ κs _, stateI σ κs), (λ v, ⌜φ v⌝%I), fork_post.
  iIntros "{$Hσ $Hwp} !>" (e2 t2' -> ?) "_ H _".
  iApply fupd_mask_weaken; [done|].
  unfold not_stuck; iSplit; [|auto].
  iIntros (v2 t2'' [= -> <-]). by rewrite to_of_val.
Qed.

Corollary wp_invariance Σ Λ `{!invPreG Σ} s e1 σ1 t2 σ2 φ :
  (∀ `{Hinv : !invG Σ} κs,
     (|={⊤}=> ∃
         (stateI : state Λ → list (observation Λ) → list (expr Λ) → iProp Σ)
         (fork_post : nat → val Λ → iProp Σ),
       let _ : irisG Λ Σ := IrisG _ _ Hinv stateI fork_post in
       stateI σ1 κs [e1] ∗ WP e1 @ (s,0); ⊤ {{ _, True }} ∗
       (stateI σ2 [] t2 -∗ ∃ E, |={⊤,E}=> ⌜φ⌝))%I) →
  rtc erased_step ([e1], σ1) (t2, σ2) →
  φ.
Proof.
  intros Hwp [n [κs Hsteps]]%erased_steps_nsteps.
  eapply (wp_strong_adequacy Σ _); [|exact Hsteps]=> ?.
  iMod (Hwp _ κs) as (stateI fork_post) "(Hσ & Hwp & Hφ)".
  iExists s, stateI, (λ _, True)%I, fork_post.
  iIntros "{$Hσ $Hwp} !>" (e2 t2' -> _) "Hσ _ _ /=".
  iDestruct ("Hφ" with "Hσ") as (E) ">Hφ".
  by iApply fupd_mask_weaken; first set_solver.
Qed.
