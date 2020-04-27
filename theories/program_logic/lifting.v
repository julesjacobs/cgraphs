Inductive natlist : Type :=
  | nil : natlist
  | cons : nat -> natlist -> natlist.

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with nil => l2 | cons x l1 => cons x (app l1 l2) end.

Fixpoint rev (l : natlist) : natlist :=
  match l with nil => nil | cons x l => app (rev l) (cons x nil) end.

Inductive palindrome : natlist -> Prop :=
  | nilp : palindrome nil
  | consp : forall x xs, palindrome xs -> palindrome (cons x (app xs (cons x nil))).

Lemma consrev l x : cons x (rev l) = rev (app l (cons x nil)).
Proof.
  induction l; simpl; auto.
  rewrite <-IHl; simpl. auto.
Qed.

Lemma prev l : palindrome l -> rev l = l.
Proof.
  induction 1; auto.
  simpl.
  rewrite<-consrev.
  rewrite IHpalindrome.
  reflexivity.
Qed.

Definition id := nat.

Inductive expr :=
| EVar (x : id) : expr
| ENat (n : nat) : expr
| EBool (b : bool) : expr
| ELet (x : id) (e1 e2 : expr) : expr
| EIf (e1 e2 e3 : expr) : expr.

Inductive val :=
  | VNat : nat -> val
  | VBool : bool -> val.

Inductive env :=
  | env_nil
  | env_snoc (E : env) (x : id) (v : val) : env.

Fixpoint env_lookup (x : id) (E : env) : option val := None.

Fixpoint interp (E : env) (e : expr) : option val :=
  match e with
  | EVar x => env_lookup x E
  | ENat n => Some (VNat n)
  | EBool b => Some (VBool b)
  | ELet x e1 e2 =>
     match interp E e1 with
     | Some v1 => interp (env_snoc E x v1) e2
     | None => None
     end
  | EIf e1 e2 e3 =>
    match interp E e1 with
    | Some (VBool true) => interp E e2
    | Some (VBool false) => interp E e3
    | _ => None
    end
  end.

Inductive big_step : expr -> val -> Prop := .


Lemma interp_big_step e v : interp env_nil e = Some v <-> big_step e v.

From iris.proofmode Require Import tactics.
From diris.program_logic Require Export weakestpre.
Set Default Proof Using "Type".

Section lifting.
Context `{!irisG Λ Σ ξ}.
Implicit Types s : ξ.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.
Implicit Types σ : state Λ.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Hint Resolve reducible_no_obs_reducible : core.

Lemma wp_lift_step_fupd s E Φ e1 :
  to_val e1 = None →
  (∀ ζ σ1 κ κs es tid,
     ⌜ tid_get s tid ∧ es !! tid = Some e1 ⌝ -∗
     state_interp ζ σ1 (κ ++ κs) es ={E,∅}=∗
       ⌜ reducible e1 σ1 ∨ stuck_valid ζ σ1 s e1 ⌝ ∧
       ∀ e2 σ2 efs,
         ⌜ prim_step e1 σ1 κ e2 σ2 efs ⌝ ={∅,∅,E}▷=∗
         ∃ ζ', state_interp ζ' σ2 κs (<[tid:=e2]> es ++ efs) ∗
          WP e2 @ s ; E {{ Φ }} ∗
          [∗ list] i ↦ ef ∈ efs,
            WP ef @ (tid_set (i + length es) s) ; ⊤ {{ fork_post (i + length es) }})
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  by rewrite wp_unfold /wp_pre=>->.
Qed.

(* Lemma wp_lift_stuck E Φ e i :
  to_val e = None →
  (∀ σ κs es, state_interp σ κs es ={E,∅}=∗ ⌜stuck e σ⌝)
  ⊢ WP e @ (MaybeStuck,i); E {{ Φ }}.
Proof.
  rewrite wp_unfold /wp_pre=>->. iIntros "H" (σ1 κ κs es) "Hf Hσ".
  iMod ("H" with "Hσ") as %[? Hirr]. iModIntro. iSplit; first done.
  iIntros (e2 σ2 efs ?).
  destruct Hirr as [Hirr H1].
  by case: (Hirr κ e2 σ2 efs).
Qed. *)

(** Derived lifting lemmas. *)
(* Lemma wp_lift_step s E Φ e1 :
  to_val e1 = None →
  (∀ σ1 κ κs es, state_interp σ1 (κ ++ κs) es ={E,∅}=∗
    ⌜if s is NotStuck then reducible e1 σ1 ∨ waiting e1 σ1 else True⌝ ∗
    ▷ ∀ e2 σ2 efs, ⌜prim_step e1 σ1 κ e2 σ2 efs⌝ ={∅,E}=∗
      state_interp σ2 κs ((<[i := e2]> es) ++ efs) ∗
      WP e2 @ (s,i); E {{ Φ }} ∗
      [∗ list] i ↦ ef ∈ efs, WP ef @ (s,length es + i); ⊤ {{ fork_post (length es + i) }})
  ⊢ WP e1 @ (s,i); E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_step_fupd; [done|]. iIntros (????) "Hσ".
  iMod ("H" with "Hσ") as "[$ H]". iIntros "!> * % !> !>". by iApply "H".
Qed. *)


(* stuck_valid : abstract_state → state Λ → A → expr Λ → Prop; *)
Lemma wp_lift_pure_step_no_fork s E E' Φ e1 :
  to_val e1 = None →
  (∀ ζ σ1, reducible e1 σ1 ∨ stuck_valid ζ σ1 s e1) →
  (∀ κ σ1 e2 σ2 efs ,
    prim_step e1 σ1 κ e2 σ2 efs →
    κ = [] ∧ σ2 = σ1 ∧ efs = [] ∧
    (∀ κs es tid ζ,
      tid_get s tid →
      state_interp ζ σ1 κs (<[tid:=e1]> es) ⊢ state_interp ζ σ2 κs (<[tid:=e2]> es))) →
  (|={E,E'}▷=> ∀ κ e2 efs σ, ⌜prim_step e1 σ κ e2 σ efs⌝ → WP e2 @ s; E {{ Φ }})
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (Hnoval Hvalid Hstep) "H".
  iApply wp_lift_step_fupd; first done.
  iIntros (ζ σ1 κ κs es tid [tidg tidh]) "Hsi".
  iMod "H".
  iMod (fupd_intro_mask' E' ∅) as "Hclose"; first by apply empty_subseteq.
  iModIntro.
  iSplit; first done.
  iIntros (e2 σ2 efs primst).
  destruct (Hstep κ σ1 e2 σ2 efs) as (-> & <- & -> & Hsi);[done..|].
  iMod "Hclose" as "_".
  iExists ζ. simpl.
  replace (state_interp ζ σ2 κs es) with (state_interp ζ σ2 κs (<[tid:=e1]> es)) by
    (rewrite list_insert_id; auto).
  rewrite app_nil_r.
  iMod (fupd_intro_mask' _ ∅) as "Hclose"; first by apply empty_subseteq.
  iModIntro. iNext.
  iMod "Hclose" as "_".
  iMod "H".
  iModIntro.
  iSplitL "Hsi"; first by iApply Hsi.
  iSplitL; last done.
  by iApply "H".
Qed.


(* iIntros (Hsafe Hstep) "H". iApply wp_lift_step.
  { specialize (Hsafe inhabitant).
    destruct s; naive_solver eauto using reducible_not_val, waiting_not_val. }
  iIntros (σ1 κ κs es) "Hσ". iMod "H".
  iMod fupd_intro_mask' as "Hclose"; last iModIntro; first by set_solver. iSplit.
  { iPureIntro. destruct s; done. }
  iNext. iIntros (e2 σ2 efs ?).
  destruct (Hstep κ σ1 e2 σ2 efs) as (-> & <- & ->); auto.
  iMod "Hclose" as "_". iMod "H". iModIntro.
  iDestruct ("H" with "[//]") as "H". simpl. rewrite app_nil_r. iFrame.
Admitted. *)

(*
Lemma wp_lift_pure_stuck `{!Inhabited (state Λ)} E Φ e i :
  (∀ σ, stuck e σ) →
  True ⊢ WP e @ (MaybeStuck,i); E {{ Φ }}.
Proof.
  iIntros (Hstuck) "_". iApply wp_lift_stuck.
  - destruct(to_val e) as [v|] eqn:He; last done.
    rewrite -He. by case: (Hstuck inhabitant).
  - iIntros (σ κs n) "_". by iMod (fupd_intro_mask' E ∅) as "_"; first set_solver.
Qed. *)

(* Atomic steps don't need any mask-changing business here, one can
   use the generic lemmas here. *)
Lemma wp_lift_atomic_step_fupd {s E1 E2 Φ} e1 :
  to_val e1 = None →
  (∀ ζ σ1 κ κs es tid,
    ⌜ tid_get s tid ∧ es !! tid = Some e1 ⌝ -∗
    state_interp ζ σ1 (κ ++ κs) es ={E1}=∗
    ⌜ reducible e1 σ1 ∨ stuck_valid ζ σ1 s e1 ⌝ ∗
    ∀ e2 σ2 efs, ⌜prim_step e1 σ1 κ e2 σ2 efs⌝ ={E1,E2}▷=∗
      ∃ ζ', state_interp ζ' σ2 κs ((<[tid := e2]> es) ++ efs) ∗
      from_option Φ False (to_val e2) ∗
      [∗ list] i ↦ ef ∈ efs, WP ef @ (tid_set (i + length es) s); ⊤ {{ fork_post (i + length es) }})
  ⊢ WP e1 @ s; E1 {{ Φ }}.
Proof.
  iIntros (?) "H".
  iApply wp_lift_step_fupd; first done.
  iIntros (ζ σ1 κ κs es tid [tidg tidh]) "Hsi".
  iMod ("H" with "[//] Hsi") as "[$ H]".
  iMod (fupd_intro_mask' E1 ∅) as "Hclose"; first by apply empty_subseteq.
  iModIntro. iIntros (e2 σ2 efs Hps).
  iMod "Hclose" as "_".
  iMod ("H" with "[//]") as "H".
  iMod (fupd_intro_mask' E2 ∅) as "Hclose"; [set_solver|]. iIntros "!> !>".
  iMod "Hclose" as "_". iMod "H" as (ζ') "(Hsi & Hfo & Hr)".
  destruct (to_val e2) eqn:?; last by iExFalso. simpl.
  iExists ζ'. iFrame.
  iApply wp_value; last done. by apply of_to_val.
Qed.

(*
Lemma wp_lift_atomic_step {s i E Φ} e1 :
  to_val e1 = None →
  (∀ σ1 κ κs es, state_interp σ1 (κ ++ κs) es ={E}=∗
    ⌜if s is NotStuck then reducible e1 σ1 ∨ waiting e1 σ1 else True⌝ ∗
    ▷ ∀ e2 σ2 efs, ⌜prim_step e1 σ1 κ e2 σ2 efs⌝ ={E}=∗
      state_interp σ2 κs ((<[i := e2]> es) ++ efs) ∗
      from_option Φ False (to_val e2) ∗
      [∗ list] i ↦ ef ∈ efs, WP ef @ (s,length es + i); ⊤ {{ fork_post (length es + i) }})
  ⊢ WP e1 @ (s,i); E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_atomic_step_fupd; [done|].
  iIntros (????) "?". iMod ("H" with "[$]") as "[$ H]".
  iIntros "!> *". iIntros (Hstep) "!> !>".
  by iApply "H".
Qed. *)


Lemma wp_lift_pure_det_step_no_fork `{!Inhabited (state Λ)} {s E E' Φ} e1 e2 :
  to_val e1 = None →
  (∀ ζ σ1, reducible e1 σ1 ∨ stuck_valid ζ σ1 s e1) →
  (∀ κ σ1 e2' σ2 efs',
    prim_step e1 σ1 κ e2' σ2 efs' →
    κ = [] ∧ σ2 = σ1 ∧ e2' = e2 ∧ efs' = [] ∧
    (∀ κs es tid ζ,
      tid_get s tid →
      state_interp ζ σ1 κs (<[tid:=e1]> es) ⊢ state_interp ζ σ2 κs (<[tid:=e2]> es))) →
  (|={E,E'}▷=> WP e2 @ s; E {{ Φ }}) ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (?? Hpuredet) "H". iApply (wp_lift_pure_step_no_fork s E E'); try done.
  { intros. edestruct Hpuredet as (? & ? & ? & ? & ?); eauto. subst. eauto. }
  iApply (step_fupd_wand with "H"); iIntros "H".
  iIntros (κ e' efs' σ Hps).
  eapply Hpuredet in Hps as (? & ? & -> & ?). done.
Qed.

Lemma wp_pure_step_fupd `{!Inhabited (state Λ)} s E E' e1 e2 φ n Φ :
  PureExec φ n e1 e2 →
  φ →
  (|={E,E'}▷=>^n WP e2 @ s; E {{ Φ }}) ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (Hexec Hφ) "Hwp". specialize (Hexec Hφ).
  iInduction Hexec as [e|n e1 e2 e3 [Hsafe ?]] "IH"; simpl; first done.
  iApply wp_lift_pure_det_step_no_fork;
    eauto using reducible_no_obs_reducible, reducible_not_val.
  -
  - eauto.
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
