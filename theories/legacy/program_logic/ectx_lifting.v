(** Some derived lemmas for ectx-based languages *)
From iris.proofmode Require Import tactics.
From iris.program_logic Require Export ectx_language.
From diris.program_logic Require Export weakestpre lifting.
Set Default Proof Using "Type".

Section wp.
Context {Λ : ectxLanguage} `{!irisG Λ Σ ζ} {Hinh : Inhabited (state Λ)}.
Implicit Types s : stuckness.
Implicit Types P : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.
Hint Resolve head_prim_reducible head_reducible_prim_step : core.
(* Hint Resolve head_prim_waiting : core. *)
Hint Resolve (reducible_not_val _ inhabitant) : core.
Hint Resolve head_stuck_stuck : core.


Lemma wp_lift_head_step_fupd {s i E Φ} e1 :
  to_val e1 = None →
  (∀ σ1 κ κs es, state_interp σ1 (κ ++ κs) es ={E,∅}=∗
    ⌜head_reducible e1 σ1 ∨ head_waiting e1 σ1⌝ ∗
    ∀ e2 σ2 efs, ⌜head_step e1 σ1 κ e2 σ2 efs⌝ ={∅,∅,E}▷=∗
      state_interp σ2 κs ((<[i := e2]> es) ++ efs) ∗
      WP e2 @ (s,i); E {{ Φ }} ∗
      [∗ list] i↦ef ∈ efs, WP ef @ (s,length es + i); ⊤ {{ fork_post (length es + i) }})
  ⊢ WP e1 @ (s,i); E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_step_fupd=>//. iIntros (σ1 κ κs Qs) "Hσ".
  iMod ("H" with "Hσ") as (Hrw) "H"; iModIntro.
  iSplit.
  - destruct s; last done. iPureIntro. destruct Hrw.
    + auto.
    + right. apply head_prim_waiting. done.
  - iIntros (e2 σ2 efs ?).
    iApply "H".
    iPureIntro.
    destruct Hrw; auto.
    exfalso. eapply head_waiting_prim_step; eauto.
Qed.

Lemma wp_lift_head_step {s i E Φ} e1 :
  to_val e1 = None →
  (∀ σ1 κ κs es, state_interp σ1 (κ ++ κs) es ={E,∅}=∗
    ⌜head_reducible e1 σ1 ∨ head_waiting e1 σ1⌝ ∗
    ▷ ∀ e2 σ2 efs, ⌜head_step e1 σ1 κ e2 σ2 efs⌝ ={∅,E}=∗
      state_interp σ2 κs ((<[i := e2]> es) ++ efs) ∗
      WP e2 @ (s,i); E {{ Φ }} ∗
      [∗ list] i↦ef ∈ efs, WP ef @ (s, length es + i) ; ⊤ {{ fork_post (length es + i) }})
  ⊢ WP e1 @ (s,i); E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_head_step_fupd; [done|]. iIntros (????) "?".
  iMod ("H" with "[$]") as "[$ H]". iIntros "!>" (e2 σ2 efs ?) "!> !>". by iApply "H".
Qed.

Lemma wp_lift_head_stuck E Φ e i :
  to_val e = None →
  sub_redexes_are_values e →
  (∀ σ κs es, state_interp σ κs es ={E,∅}=∗ ⌜head_stuck e σ⌝)
  ⊢ WP e @ (MaybeStuck,i); E {{ Φ }}.
Proof.
  iIntros (??) "H". iApply wp_lift_stuck; first done.
  iIntros (σ κs n) "Hσ". iMod ("H" with "Hσ") as "%". by auto.
Qed.

Lemma wp_lift_pure_head_stuck E i Φ e :
  to_val e = None →
  sub_redexes_are_values e →
  (∀ σ, head_stuck e σ) →
  WP e @ (MaybeStuck,i); E {{ Φ }}%I.
Proof using Hinh.
  iIntros (?? Hstuck). iApply wp_lift_head_stuck; [done|done|].
  iIntros (σ κs n) "_". iMod (fupd_intro_mask' E ∅) as "_"; first set_solver.
  by auto.
Qed.

Lemma wp_lift_atomic_head_step_fupd {s i E1 E2 Φ} e1 :
  to_val e1 = None →
  (∀ σ1 κ κs es, state_interp σ1 (κ ++ κs) es ={E1}=∗
    ⌜head_reducible e1 σ1 ∨ head_waiting e1 σ1⌝ ∗
    ∀ e2 σ2 efs, ⌜head_step e1 σ1 κ e2 σ2 efs⌝ ={E1,E2}▷=∗
      state_interp σ2 κs ((<[i := e2]> es) ++ efs) ∗
      from_option Φ False (to_val e2) ∗
      [∗ list] i↦ef ∈ efs, WP ef @ (s, length es + i); ⊤ {{ fork_post (length es + i) }})
  ⊢ WP e1 @ (s,i); E1 {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_atomic_step_fupd; [done|].
  iIntros (σ1 κ κs Qs) "Hσ1". iMod ("H" with "Hσ1") as (Hrw) "H". iModIntro.
  iSplit.
  - destruct s; last done. iPureIntro. destruct Hrw.
    + auto.
    + right. apply head_prim_waiting. done.
  - iIntros (e2 σ2 efs Hstep).
    iApply "H"; eauto.
    iPureIntro.
    destruct Hrw; auto.
    exfalso. eapply head_waiting_prim_step; eauto.
Qed.

(*
Lemma wp_lift_atomic_head_step_fupd {s E1 E2 Φ} e1 :
  to_val e1 = None →
  (∀ σ1 κ κs n, state_interp σ1 (κ ++ κs) n ={E1}=∗
    ⌜head_reducible e1 σ1 ∨ waiting e1 σ1⌝ ∗
    ∀ e2 σ2 efs, ⌜head_step e1 σ1 κ e2 σ2 efs⌝ ={E1,E2}▷=∗
      state_interp σ2 κs (n ++ efs) ∗
      from_option Φ False (to_val e2) ∗
      [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ fork_post }})
  ⊢ WP e1 @ s; E1 {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_atomic_step_fupd; [done|].
  iIntros (σ1 κ κs Qs) "Hσ1". iMod ("H" with "Hσ1") as "[% H]"; iModIntro.
  iSplit; first by destruct s; naive_solver. iIntros (e2 σ2 efs Hstep).
  iApply "H"; eauto. destruct H0; auto.
Qed.
*)

Lemma wp_lift_atomic_head_step {s i E Φ} e1 :
  to_val e1 = None →
  (∀ σ1 κ κs es, state_interp σ1 (κ ++ κs) es ={E}=∗
    ⌜head_reducible e1 σ1 ∨ waiting e1 σ1⌝ ∗
    ▷ ∀ e2 σ2 efs, ⌜head_step e1 σ1 κ e2 σ2 efs⌝ ={E}=∗
      state_interp σ2 κs ((<[i := e2]> es) ++ efs) ∗
      from_option Φ False (to_val e2) ∗
      [∗ list] i↦ef ∈ efs, WP ef @ (s,length es + i); ⊤ {{ fork_post (length es + i) }})
  ⊢ WP e1 @ (s,i); E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_atomic_step; eauto.
  iIntros (σ1 κ κs Qs) "Hσ1". iMod ("H" with "Hσ1") as (Hrw) "H"; iModIntro.
  iSplit.
  - destruct s; last done. iPureIntro. destruct Hrw; auto.
  - iIntros (e2 σ2 efs Hstep).
  iApply "H".
  iPureIntro.
  destruct Hrw; auto.
  exfalso. eapply waiting_prim_step; [exact H0 | exact Hstep].
Qed.

Lemma wp_lift_atomic_head_step_no_fork_fupd {s i E1 E2 Φ} e1 :
  to_val e1 = None →
  (∀ σ1 κ κs es, state_interp σ1 (κ ++ κs) es ={E1}=∗
    ⌜head_reducible e1 σ1 ∨ head_waiting e1 σ1⌝ ∗
    ∀ e2 σ2 efs, ⌜head_step e1 σ1 κ e2 σ2 efs⌝ ={E1,E2}▷=∗
      ⌜efs = []⌝ ∗ state_interp σ2 κs es ∗ from_option Φ False (to_val e2))
  ⊢ WP e1 @ (s,i); E1 {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_atomic_head_step_fupd; [done|].
  iIntros (σ1 κ κs Qs) "Hσ1".
 iMod ("H" $! σ1 with "Hσ1") as "[$ H]"; iModIntro.
  iIntros (v2 σ2 efs Hstep).
  iMod ("H" $! v2 σ2 efs with "[# //]") as "H".
  iIntros "!> !>". iMod "H" as "(-> & ? & ?) /=". rewrite app_nil_r. iFrame.
Admitted.

Lemma wp_lift_atomic_head_step_no_fork {s i E Φ} e1 :
  to_val e1 = None →
  (∀ σ1 κ κs es, state_interp σ1 (κ ++ κs) es ={E}=∗
    ⌜head_reducible e1 σ1 ∨ waiting e1 σ1⌝ ∗
    ▷ ∀ e2 σ2 efs, ⌜head_step e1 σ1 κ e2 σ2 efs⌝ ={E}=∗
      ⌜efs = []⌝ ∗ state_interp σ2 κs es ∗ from_option Φ False (to_val e2))
  ⊢ WP e1 @ (s,i); E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_atomic_head_step; eauto.
  iIntros (σ1 κ κs Qs) "Hσ1". iMod ("H" $! σ1 with "Hσ1") as "[$ H]"; iModIntro.
  iNext; iIntros (v2 σ2 efs Hstep).
  iMod ("H" $! v2 σ2 efs with "[//]") as "(-> & ? & ?) /=". rewrite app_nil_r. iFrame.
Admitted.

Lemma wp_lift_pure_det_head_step_no_fork {s i E E' Φ} e1 e2 :
  to_val e1 = None →
  (∀ σ1, head_reducible e1 σ1) →
  (∀ σ1 κ e2' σ2 efs',
    head_step e1 σ1 κ e2' σ2 efs' → κ = [] ∧ σ2 = σ1 ∧ e2' = e2 ∧ efs' = []) →
  (|={E,E'}▷=> WP e2 @ (s,i); E {{ Φ }}) ⊢ WP e1 @ (s,i); E {{ Φ }}.
Proof using Hinh.
  intros. rewrite -(wp_lift_pure_det_step_no_fork e1 e2); eauto.
  destruct s; by auto.
Qed.

Lemma wp_lift_pure_det_head_step_no_fork' {s i E Φ} e1 e2 :
  to_val e1 = None →
  (∀ σ1, head_reducible e1 σ1) →
  (∀ σ1 κ e2' σ2 efs',
    head_step e1 σ1 κ e2' σ2 efs' → κ = [] ∧ σ2 = σ1 ∧ e2' = e2 ∧ efs' = []) →
  ▷ WP e2 @ (s,i); E {{ Φ }} ⊢ WP e1 @ (s,i); E {{ Φ }}.
Proof using Hinh.
  intros. rewrite -[(WP e1 @ (s,i); _ {{ _ }})%I]wp_lift_pure_det_head_step_no_fork //.
  rewrite -step_fupd_intro //.
Qed.
End wp.
