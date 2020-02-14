From iris.proofmode Require Import tactics.
From diris.program_logic Require Export weakestpre.
Set Default Proof Using "Type".

Section lifting.
Context `{!irisG Λ Σ}.
Implicit Types s : stuckness.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.
Implicit Types σ : state Λ.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.

Hint Resolve reducible_no_obs_reducible : core.

Lemma wp_lift_step_fupd s i E Φ e1 :
  to_val e1 = None →
  (∀ σ1 κ κs es K, state_interp σ1 (κ ++ κs) es ={E,∅}=∗
    ⌜if s is NotStuck then reducible e1 σ1 ∨ waiting e1 σ1 else True⌝ ∗
    ∀ e2 σ2 efs, ⌜prim_step e1 σ1 κ e2 σ2 efs⌝ ={∅,∅,E}▷=∗
      state_interp σ2 κs ((<[i := fill K e2]> es) ++ efs) ∗
      WP e2 @ (s,i); E {{ Φ }} ∗
      [∗ list] i ↦ ef ∈ efs, WP ef @ (s,length es + i); ⊤ {{ fork_post (length es + i) }})
  ⊢ WP e1 @ (s,i); E {{ Φ }}.
Proof.
  rewrite wp_unfold /wp_pre=>->. iIntros "H" (σ1 κ κs es K) "Hf Hσ".
  iMod ("H" with "Hσ") as "(%&H)". iModIntro. iSplit. by destruct s.
  iIntros (????). iApply "H". eauto.
Qed.

Lemma wp_lift_stuck E Φ e i :
  to_val e = None →
  (∀ σ κs es, state_interp σ κs es ={E,∅}=∗ ⌜stuck e σ⌝)
  ⊢ WP e @ (MaybeStuck,i); E {{ Φ }}.
Proof.
  rewrite wp_unfold /wp_pre=>->. iIntros "H" (σ1 κ κs es K) "Hf Hσ".
  iMod ("H" with "Hσ") as %[? Hirr]. iModIntro. iSplit; first done.
  iIntros (e2 σ2 efs ?). 
  destruct Hirr as [Hirr H1].
  by case: (Hirr κ e2 σ2 efs).
Qed.

(** Derived lifting lemmas. *)
Lemma wp_lift_step s i E Φ e1 :
  to_val e1 = None →
  (∀ σ1 κ κs es K, state_interp σ1 (κ ++ κs) es ={E,∅}=∗
    ⌜if s is NotStuck then reducible e1 σ1 ∨ waiting e1 σ1 else True⌝ ∗
    ▷ ∀ e2 σ2 efs, ⌜prim_step e1 σ1 κ e2 σ2 efs⌝ ={∅,E}=∗
      state_interp σ2 κs ((<[i := fill K e2]> es) ++ efs) ∗
      WP e2 @ (s,i); E {{ Φ }} ∗
      [∗ list] i ↦ ef ∈ efs, WP ef @ (s,length es + i); ⊤ {{ fork_post (length es + i) }})
  ⊢ WP e1 @ (s,i); E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_step_fupd; [done|]. iIntros (?????) "Hσ".
  iMod ("H" with "Hσ") as "[$ H]". iIntros "!> * % !> !>". by iApply "H".
Qed.

Lemma wp_lift_pure_step_no_fork `{!Inhabited (state Λ)} s i E E' Φ e1 :
  (∀ σ1, if s is NotStuck then reducible e1 σ1 ∨ waiting e1 σ1 else to_val e1 = None) →
  (∀ κ σ1 e2 σ2 efs, prim_step e1 σ1 κ e2 σ2 efs → κ = [] ∧ σ2 = σ1 ∧ efs = []) →
  (|={E,E'}▷=> ∀ κ e2 efs σ, ⌜prim_step e1 σ κ e2 σ efs⌝ → WP e2 @ (s,i); E {{ Φ }})
  ⊢ WP e1 @ (s,i); E {{ Φ }}.
Proof.
  iIntros (Hsafe Hstep) "H". iApply wp_lift_step.
  { specialize (Hsafe inhabitant).
    destruct s; naive_solver eauto using reducible_not_val, waiting_not_val. }
  iIntros (σ1 κ κs es K) "Hσ". iMod "H".
  iMod fupd_intro_mask' as "Hclose"; last iModIntro; first by set_solver. iSplit.
  { iPureIntro. destruct s; done. }
  iNext. iIntros (e2 σ2 efs ?).
  destruct (Hstep κ σ1 e2 σ2 efs) as (-> & <- & ->); auto.
  iMod "Hclose" as "_". iMod "H". iModIntro.
  iDestruct ("H" with "[//]") as "H". simpl. rewrite app_nil_r. iFrame.
  
Admitted.

Lemma wp_lift_pure_stuck `{!Inhabited (state Λ)} E Φ e i :
  (∀ σ, stuck e σ) →
  True ⊢ WP e @ (MaybeStuck,i); E {{ Φ }}.
Proof.
  iIntros (Hstuck) "_". iApply wp_lift_stuck.
  - destruct(to_val e) as [v|] eqn:He; last done.
    rewrite -He. by case: (Hstuck inhabitant).
  - iIntros (σ κs n) "_". by iMod (fupd_intro_mask' E ∅) as "_"; first set_solver.
Qed.

(* Atomic steps don't need any mask-changing business here, one can
   use the generic lemmas here. *)
Lemma wp_lift_atomic_step_fupd {s i E1 E2 Φ} e1 :
  to_val e1 = None →
  (∀ σ1 κ κs es K, state_interp σ1 (κ ++ κs) es ={E1}=∗
    ⌜if s is NotStuck then reducible e1 σ1 ∨ waiting e1 σ1 else True⌝ ∗
    ∀ e2 σ2 efs, ⌜prim_step e1 σ1 κ e2 σ2 efs⌝ ={E1,E2}▷=∗
      state_interp σ2 κs ((<[i := fill K e2]> es) ++ efs) ∗
      from_option Φ False (to_val e2) ∗
      [∗ list] i ↦ ef ∈ efs, WP ef @ (s,length es + i); ⊤ {{ fork_post (length es + i) }})
  ⊢ WP e1 @ (s,i); E1 {{ Φ }}.
Proof.
  iIntros (?) "H".
  iApply (wp_lift_step_fupd s i E1 _ e1) =>//; iIntros (σ1 κ κs es K) "Hσ1".
  iMod ("H" $! σ1 with "Hσ1") as "[$ H]".
  iMod (fupd_intro_mask' E1 ∅) as "Hclose"; first set_solver.
  iIntros "!>" (e2 σ2 efs ?). iMod "Hclose" as "_".
  iMod ("H" $! e2 σ2 efs with "[#]") as "H"; [done|].
  iMod (fupd_intro_mask' E2 ∅) as "Hclose"; [set_solver|]. iIntros "!> !>".
  iMod "Hclose" as "_". iMod "H" as "($ & HQ & $)".
  destruct (to_val e2) eqn:?; last by iExFalso.
  iApply wp_value; last done. by apply of_to_val.
Qed.

Lemma wp_lift_atomic_step {s i E Φ} e1 :
  to_val e1 = None →
  (∀ σ1 κ κs es K, state_interp σ1 (κ ++ κs) es ={E}=∗
    ⌜if s is NotStuck then reducible e1 σ1 ∨ waiting e1 σ1 else True⌝ ∗
    ▷ ∀ e2 σ2 efs, ⌜prim_step e1 σ1 κ e2 σ2 efs⌝ ={E}=∗
      state_interp σ2 κs ((<[i := fill K e2]> es) ++ efs) ∗
      from_option Φ False (to_val e2) ∗
      [∗ list] i ↦ ef ∈ efs, WP ef @ (s,length es + i); ⊤ {{ fork_post (length es + i) }})
  ⊢ WP e1 @ (s,i); E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_atomic_step_fupd; [done|].
  iIntros (?????) "?". iMod ("H" with "[$]") as "[$ H]".
  iIntros "!> *". iIntros (Hstep) "!> !>".
  by iApply "H".
Qed.

Lemma wp_lift_pure_det_step_no_fork `{!Inhabited (state Λ)} {s i E E' Φ} e1 e2 :
  (∀ σ1, if s is NotStuck then reducible e1 σ1 ∨ waiting e1 σ1 else to_val e1 = None) →
  (∀ σ1 κ e2' σ2 efs', prim_step e1 σ1 κ e2' σ2 efs' →
    κ = [] ∧ σ2 = σ1 ∧ e2' = e2 ∧ efs' = []) →
  (|={E,E'}▷=> WP e2 @ (s,i); E {{ Φ }}) ⊢ WP e1 @ (s,i); E {{ Φ }}.
Proof.
  iIntros (? Hpuredet) "H". iApply (wp_lift_pure_step_no_fork s i E E'); try done.
  { naive_solver. }
  iApply (step_fupd_wand with "H"); iIntros "H".
  iIntros (κ e' efs' σ (_&?&->&?)%Hpuredet); auto.
Qed.

Lemma wp_pure_step_fupd `{!Inhabited (state Λ)} s i E E' e1 e2 φ n Φ :
  PureExec φ n e1 e2 →
  φ →
  (|={E,E'}▷=>^n WP e2 @ (s,i); E {{ Φ }}) ⊢ WP e1 @ (s,i); E {{ Φ }}.
Proof.
  iIntros (Hexec Hφ) "Hwp". specialize (Hexec Hφ).
  iInduction Hexec as [e|n e1 e2 e3 [Hsafe ?]] "IH"; simpl; first done.
  iApply wp_lift_pure_det_step_no_fork.
  - intros σ. specialize (Hsafe σ). destruct s; eauto using reducible_not_val.
  - done.
  - by iApply (step_fupd_wand with "Hwp").
Qed.

Lemma wp_pure_step_later `{!Inhabited (state Λ)} s i E e1 e2 φ n Φ :
  PureExec φ n e1 e2 →
  φ →
  ▷^n WP e2 @ (s,i); E {{ Φ }} ⊢ WP e1 @ (s,i); E {{ Φ }}.
Proof.
  intros Hexec ?. rewrite -wp_pure_step_fupd //. clear Hexec.
  induction n as [|n IH]; by rewrite //= -step_fupd_intro // IH.
Qed.
End lifting.
