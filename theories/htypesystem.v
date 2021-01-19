From stdpp Require Export gmap.
From iris.bi Require Export interface.
From iris.algebra Require Import excl gmap auth.
From iris.proofmode Require Import tactics.
Require Export diris.langdef.
Require Export diris.logic.bi.
Require Import diris.util.

Canonical Structure chan_typeO := leibnizO chan_type.

Notation heapT := (gmap endpoint chan_type).
Notation heapTUR := (gmapUR endpoint (exclR chan_typeO)).

(* ⌜ . ⌝ : Prop -> hProp
   ⌜ p ⌝ := λ Σ, p
   ⌜⌜ p ⌝⌝ := λ Σ, Σ = ∅ ∧ p *)
Notation "⌜⌜ p ⌝⌝" := (<affine> ⌜ p ⌝)%I : bi_scope.

Notation hProp := (uPred heapTUR).

Definition own (l : endpoint) (t : chan_type) : hProp :=
  uPred_ownM (◯ {[ l := Excl t ]}).

Definition own_auth (h : heapT) : hProp := uPred_ownM (● (Excl <$> h)).


Lemma own_lookup l t Σ :
  own l t ∗ own_auth Σ ⊢ ⌜ Σ !! l = Some t ⌝.
Proof. Admitted. (* Niet in model gaan *)

Lemma allocate Σ l t :
  Σ !! l = None →
  own_auth Σ ⊢ |==> own_auth (<[l:=t]> Σ) ∗ own l t.
Proof. Admitted.

Lemma deallocate Σ l t :
  own_auth Σ ∗ own l t ⊢ |==> own_auth (delete l Σ).
Proof. Admitted.

Lemma update Σ l t t' :
  own_auth Σ ∗ own l t ⊢
  |==> own_auth (<[l:=t']> Σ) ∗ own l t'.
Proof. Admitted. (* Use deallocate -> allocate *)

Lemma adequacy Σ1 φ :
  (own_auth Σ1 ⊢ |==> ∃ Σ2, own_auth Σ2 ∧ ⌜ φ Σ2 ⌝) →
  φ Σ1.
Proof. Admitted.

Fixpoint ptyped (Γ : envT) (e : expr) (t : type) : hProp :=
 match e with
  | Val v =>
      ⌜⌜ Γ = ∅ ⌝⌝ ∗ val_typed v t
  | Var x =>
      ⌜⌜ Γ = {[ x := t ]} ⌝⌝
  | App e1 e2 => ∃ t' Γ1 Γ2,
      ⌜⌜ Γ = Γ1 ∪ Γ2 ∧ Γ1 ##ₘ Γ2 ⌝⌝ ∗
      ptyped Γ1 e1 (FunT t' t) ∗
      ptyped Γ2 e2 t'
  | Lam x e => ∃ t1 t2,
      ⌜⌜ t = FunT t1 t2 ∧ Γ !! x = None ⌝⌝ ∗
      ptyped (Γ ∪ {[ x := t1 ]}) e t2
  | Send e1 e2 => ∃ r t' Γ1 Γ2,
      ⌜⌜ t = ChanT r ∧ Γ = Γ1 ∪ Γ2 ∧ Γ1 ##ₘ Γ2 ⌝⌝ ∗
      ptyped Γ1 e1 (ChanT (SendT t' r)) ∗
      ptyped Γ2 e2 t'
  | Recv e => ∃ t' r,
      ⌜⌜ t = PairT t' (ChanT r) ⌝⌝ ∗
      ptyped Γ e (ChanT (RecvT t' r))
  | Let x e1 e2 => ∃ (t' : type) (Γ1 Γ2 : envT),
      ⌜⌜ Γ = Γ1 ∪ Γ2 ∧ Γ1 ##ₘ Γ2 ∧ Γ2 !! x = None ⌝⌝ ∗
      ptyped Γ1 e1 t' ∗
      ptyped (Γ2 ∪ {[ x := t' ]}) e2 t
  | LetUnit e1 e2 => ∃ Γ1 Γ2,
      ⌜⌜ Γ = Γ1 ∪ Γ2 ∧ Γ1 ##ₘ Γ2 ⌝⌝ ∗
      ptyped Γ1 e1 UnitT ∗
      ptyped Γ2 e2 t
  | LetProd x1 x2 e1 e2 => ∃ t1 t2 Γ1 Γ2,
      ⌜⌜ x1 ≠ x2 ∧ Γ = Γ1 ∪ Γ2 ∧ Γ1 ##ₘ Γ2 ∧ Γ2 !! x1 = None ∧ Γ2 !! x2 = None  ⌝⌝ ∗
      ptyped Γ1 e1 (PairT t1 t2) ∗
      ptyped (Γ2 ∪ {[ x1 := t1 ]} ∪ {[ x2 := t2 ]}) e2 t
  | If e1 e2 e3 => ∃ Γ1 Γ2,
      ⌜⌜ Γ = Γ1 ∪ Γ2 ∧ Γ1 ##ₘ Γ2 ⌝⌝ ∗
      ptyped Γ1 e1 NatT ∗
      (ptyped Γ2 e2 t ∧ ptyped Γ2 e3 t)
  | Fork e => ∃ r,
      ⌜⌜ t = ChanT r ⌝⌝ ∗
      ptyped Γ e (FunT (ChanT (dual r)) UnitT)
  | Close e =>
      ptyped Γ e (ChanT EndT)
  end
with val_typed (v : val) (t : type) : hProp :=
  match v with
  | UnitV => ⌜⌜ t = UnitT ⌝⌝
  | NatV n => ⌜⌜ t = NatT ⌝⌝
  | PairV a b => ∃ t1 t2, ⌜⌜ t = PairT t1 t2 ⌝⌝ ∗ val_typed a t1 ∗ val_typed b t2
  | FunV x e => ∃ t1 t2, ⌜⌜ t = FunT t1 t2 ⌝⌝ ∗ ptyped {[ x := t1 ]} e t2
  | ChanV c => ∃ r, ⌜⌜ t = ChanT r ⌝⌝ ∗ own c r
  end.

Lemma typed_ptyped Γ e t : ⌜⌜ typed Γ e t ⌝⌝ -∗ ptyped Γ e t.
Proof.
  iIntros "%".
  iInduction H as [] "IH"; simpl;
  repeat iExists _;
  repeat (iSplitL || iSplit);
  (by iPureIntro || iAssumption).
Qed.

Lemma union_lr_None `{Countable K} {V} (A B C : gmap K V) x :
  C = A ∪ B ∧ A ##ₘ B ->
  C !! x = None ->
  A !! x = None ∧ B !! x = None.
Proof.
  intros [-> Hdisj] Hl.
  by apply lookup_union_None in Hl.
Qed.

Lemma union_lr_Some `{Countable K} {V} (A B C : gmap K V) x v :
  C = A ∪ B ∧ A ##ₘ B ->
  C !! x = Some v ->
  (A !! x = Some v ∧ B !! x = None) ∨ (B !! x = Some v ∧ A !! x = None).
Proof.
  intros [-> Hdisj] Hl.
  apply lookup_union_Some in Hl as []; eauto; [left | right]; split; eauto;
  rewrite ->map_disjoint_alt in Hdisj; specialize (Hdisj x);
  destruct (A !! x); naive_solver.
Qed.

Ltac foo := simpl; repeat iMatchHyp (fun H P =>
  lazymatch P with
  | ⌜⌜ _ ⌝⌝%I => iDestruct H as %?
  end); simplify_map_eq.

Lemma typed_no_var_subst e Γ t x v :
  Γ !! x = None ->
  ptyped Γ e t -∗
  ⌜ subst x v e = e ⌝.
Proof.
  iIntros (Hx) "Ht".
  iInduction e as [] "IH" forall (Γ t Hx); foo.
  - done.
  - done.
  - iDestruct "Ht" as (t' Γ1 Γ2  [-> ?]) "[H1 H2]".
    iDestruct ("IH" with "[%] H1") as %?.
    { by apply lookup_union_None in Hx as []. }
    iDestruct ("IH1" with "[%] H2") as %?.
    { by apply lookup_union_None in Hx as []. }
    by rewrite H0 H1.
  - case_decide;[done|].
    iDestruct "Ht" as (t1 t2 [-> ?]) "H".
    iDestruct ("IH" with "[%] H") as %?.
    + rewrite lookup_union. rewrite Hx lookup_singleton_ne; eauto.
    + rewrite H1. done.
  - iDestruct "Ht" as (r t' Γ1 Γ2 (-> & -> & Hdisj)) "[H1 H2]".
    iDestruct ("IH" with "[%] H1") as %?.
    { by apply lookup_union_None in Hx as []. }
    iDestruct ("IH1" with "[%] H2") as %?.
    { by apply lookup_union_None in Hx as []. }
    by rewrite H H0.
  - iDestruct "Ht" as (t' r ->) "H".
    iDestruct ("IH" with "[%] H") as %?; eauto.
    by rewrite H.
  - iDestruct "Ht" as (t' Γ1 Γ2 (-> & Hdisj & Hnone)) "[H1 H2]".
    iDestruct ("IH" with "[%] H1") as %?.
    { by apply lookup_union_None in Hx as []. }
    rewrite H.
    case_decide;[done|].
    iDestruct ("IH1" with "[%] H2") as %?.
    { rewrite lookup_union. apply lookup_union_None in Hx as [].
      rewrite H2. rewrite lookup_singleton_ne; done. }
    by rewrite H1.
  - iDestruct "Ht" as (Γ1 Γ2 (-> & Hdisj)) "[H1 H2]".
    apply lookup_union_None in Hx as [].
    iDestruct ("IH" with "[%] H1") as %?; eauto.
    iDestruct ("IH1" with "[%] H2") as %?; eauto.
    by rewrite H1 H2.
  - iDestruct "Ht" as (t1 t2 Γ1 Γ2 (Hneq & -> & Hdisj & Hs1 & Hs2)) "[H1 H2]".
    apply lookup_union_None in Hx as [].
    iDestruct ("IH" with "[%] H1") as %?; eauto.
    rewrite H1.
    case_decide;[done|].
    iDestruct ("IH1" with "[%] H2") as %?.
    { rewrite !lookup_union H0 !lookup_singleton_ne; eauto. }
    by rewrite H3.
  - iDestruct "Ht" as (Γ1 Γ2 [-> Hdisj]) "[H1 H2]".
    apply lookup_union_None in Hx as [].
    iDestruct ("IH" with "[%] H1") as %?; eauto. rewrite H1.
    clear H.
    iDestruct ("IH1" with "[%] [H2]") as %?; eauto.
    { iDestruct "H2" as "[H2 _]". done. }
    iDestruct ("IH2" with "[%] [H2]") as %?; eauto.
    { iDestruct "H2" as "[_ H2]". done. }
    by rewrite H H2.
  - iDestruct "Ht" as (r ->) "H".
    iDestruct ("IH" with "[%] H") as %?; eauto.
    by rewrite H.
  - iDestruct ("IH" with "[%] Ht") as %?; eauto.
    by rewrite H.
Qed.

Lemma delete_union_l `{Countable K} {V} (a b : gmap K V) (x : K) :
  a ##ₘ b -> b !! x = None -> delete x (a ∪ b) = delete x a ∪ b ∧ delete x a ##ₘ b.
Proof.
  intros ??.
  rewrite delete_union.
  rewrite (delete_notin b x); solve_map_disjoint.
Qed.

Lemma delete_union_r `{Countable K} {V} (a b : gmap K V) (x : K) :
  a ##ₘ b -> a !! x = None -> delete x (a ∪ b) = a ∪ delete x b ∧ a ##ₘ delete x b.
Proof.
  intros ??.
  rewrite delete_union.
  rewrite (delete_notin a x); solve_map_disjoint.
Qed.

Lemma subst_ptyped (Γ : envT) (x : string) (v : val) (vT : type) (e : expr) (eT : type) :
  Γ !! x = Some vT ->
  val_typed v vT -∗
  ptyped Γ e eT -∗
  ptyped (delete x Γ) (subst x v e) eT.
Proof.
  iIntros (H) "Hv He".
  iInduction e as [?|?|?|?|?|?|?|?|?|?|?|?] "IH" forall (eT Γ H); simpl.
  - iDestruct "He" as "[% H']". simplify_map_eq.
  - iDestruct "He" as "%". simplify_map_eq. iFrame.
    iPureIntro. apply delete_singleton.
  - iDestruct "He" as (t' Γ1 Γ2 [-> ?]) "(He1 & He2)".
    eapply lookup_union_Some' in H as [[]|[]]; last done.
    + iExists _,_,_. iSplit.
      { iPureIntro. by apply delete_union_l. }
      iSplitL "He1 Hv".
      { by iApply ("IH" with "[%] Hv"). }
      { by iDestruct (typed_no_var_subst with "He2") as %->. }
    + iExists _,_,_. iSplit.
      { iPureIntro. by apply delete_union_r. }
      iSplitR "He2 Hv".
      { by iDestruct (typed_no_var_subst with "He1") as %->. }
      { by iApply ("IH1" with "[%] Hv"). }
  - iDestruct "He" as (t1 t2 (-> & Hs)) "H".
    case_decide.
    + simplify_eq.
    + simpl. iExists _,_. iSplit.
      { iPureIntro. split; eauto. rewrite lookup_delete_None. eauto. }
      { replace (delete x Γ ∪ {[s := t1]}) with (delete x (Γ ∪ {[s := t1]})).
        iApply ("IH" with "[%] Hv H").
        - rewrite lookup_union. rewrite H. rewrite lookup_singleton_ne; eauto.
        - rewrite delete_union. rewrite delete_singleton_ne; eauto. }
  - iDestruct "He" as (r t' Γ1 Γ2 (-> & -> & ?)) "[H1 H2]".
    eapply lookup_union_Some' in H as [[]|[]]; last done.
    + iExists _,_,_,_. iSplit.
      { iPureIntro. split; eauto. by apply delete_union_l. }
      iSplitL "H1 Hv".
      { by iApply ("IH" with "[%] Hv"). }
      { by iDestruct (typed_no_var_subst with "H2") as %->. }
    + iExists _,_,_,_. iSplit.
      { iPureIntro. split; eauto. by apply delete_union_r. }
      iSplitR "H2 Hv".
      { by iDestruct (typed_no_var_subst with "H1") as %->. }
      { by iApply ("IH1" with "[%] Hv"). }
  - iDestruct "He" as (t r ->) "H".
    iExists _,_. iSplit. done.
    iApply ("IH" with "[%] Hv H"). done.
  - iDestruct "He" as (t' Γ1 Γ2 (-> & ? & ?)) "[H1 H2]".
    eapply lookup_union_Some' in H as [[]|[]]; last done.
    + repeat iExists _. iSplit.
      { iPureIntro. split. by apply delete_union_l. split; eauto.
        solve_map_disjoint. }
      iSplitL "H1 Hv".
      { by iApply ("IH" with "[%] Hv"). }
      { case_decide. done.
        iDestruct (typed_no_var_subst e2 _ _ _ v with "H2") as %?.
        - rewrite lookup_union.
          rewrite lookup_singleton_ne; last done.
          rewrite H2. done.
        - rewrite H4. done. }
    + iExists _,_,_. iSplit.
      { iPureIntro. split. by apply delete_union_r. split.
        + solve_map_disjoint.
        + rewrite lookup_delete_None. eauto. }
      iSplitR "H2 Hv".
      { by iDestruct (typed_no_var_subst with "H1") as %->. }
      { case_decide. simplify_eq.
        replace (delete x Γ2 ∪ {[s := t']}) with (delete x (Γ2 ∪ {[s := t']})).
        - iApply ("IH1" with "[%] Hv H2").
          rewrite lookup_union. rewrite H. rewrite lookup_singleton_ne; eauto.
        - rewrite delete_union. rewrite delete_singleton_ne; eauto. }
  - iDestruct "He" as (Γ1 Γ2 (-> & ?)) "[H1 H2]".
    eapply lookup_union_Some' in H as [[]|[]]; last done.
    + repeat iExists _. iSplit.
      { iPureIntro. apply delete_union_l; eauto. }
      iSplitL "H1 Hv".
      { iApply ("IH" with "[%] Hv H1"). done. }
      { iDestruct (typed_no_var_subst with "H2") as %->; eauto. }
    + repeat iExists _. iSplit.
      { iPureIntro. apply delete_union_r; eauto. }
      iSplitL "H1".
      { iDestruct (typed_no_var_subst with "H1") as %->; eauto. }
      { iApply ("IH1" with "[%] Hv H2"). done. }
  - iDestruct "He" as (t1 t2 Γ1 Γ2 (Hneq & -> & ? & ? & ?)) "[H1 H2]".
    eapply lookup_union_Some' in H as [[]|[]]; last done.
    + repeat iExists _. iSplit.
      { iPureIntro. split;eauto. split. apply delete_union_l; eauto.
        solve_map_disjoint. }
      iSplitL "H1 Hv".
      { iApply ("IH" with "[%] Hv H1"). done. }
      { case_decide.
        - done.
        - iDestruct (typed_no_var_subst with "H2") as %->; eauto.
          rewrite !lookup_union. rewrite H3.
          rewrite !lookup_singleton_ne; eauto. }
    + repeat iExists _. iSplit.
      { iPureIntro. split;eauto. split. apply delete_union_r; eauto.
        split. solve_map_disjoint.
        rewrite !lookup_delete_None. eauto. }
      iSplitL "H1".
      { iDestruct (typed_no_var_subst with "H1") as %->; eauto. }
      { case_decide.
        - destruct H4; subst; simplify_eq.
        - replace (delete x Γ2 ∪ {[s := t1]} ∪ {[s0 := t2]}) with
                  (delete x (Γ2 ∪ {[s := t1]} ∪ {[s0 := t2]})).
          { iApply ("IH1" with "[%] Hv H2").
            rewrite !lookup_union. rewrite H.
            rewrite !lookup_singleton_ne; eauto. }
          { rewrite !delete_union. rewrite !delete_singleton_ne; eauto. } }
  - iDestruct "He" as (Γ1 Γ2 (-> & ?)) "[H1 H2]".
    eapply lookup_union_Some' in H as [[]|[]]; last done.
    + repeat iExists _. iSplit.
      { iPureIntro. apply delete_union_l; eauto. }
      iSplitL "H1 Hv".
      { iApply ("IH" with "[%] Hv H1"). done. }
      { iDestruct (typed_no_var_subst e2 with "[H2]") as %->.
        - exact H1.
        - iDestruct "H2" as "[H _]". eauto.
        - iDestruct (typed_no_var_subst e3 with "[H2]") as %->.
          + exact H1.
          + iDestruct "H2" as "[_ H]". eauto.
          + done. }
    + repeat iExists _. iSplit.
      { iPureIntro. apply delete_union_r; eauto. }
      iSplitL "H1".
      { iDestruct (typed_no_var_subst with "H1") as %->; eauto. }
      { iSplit.
        - iDestruct "H2" as "[H _]".
          iApply ("IH1" with "[%] Hv H"). done.
        - iDestruct "H2" as "[_ H]".
          iApply ("IH2" with "[%] Hv H"). done. }
  - iDestruct "He" as (r ->) "H".
    iExists _. iSplit.
    { iPureIntro. done. }
    { iApply ("IH" with "[%] Hv H"). done. }
  - iApply ("IH" with "[%] Hv He"). done.
Qed.

(* Definition ctx_typed (Γ : envT) (k : expr -> expr)
                     (A : type) (B : type) : hProp :=
    (∀ e Γ',
      ⌜⌜ Γ ##ₘ Γ' ⌝⌝ -∗
      ptyped Γ' e A -∗
      ptyped (Γ ∪ Γ') (k e) B)%I.

Lemma md1 (Γ : envT) :
  Γ = ∅ ∪ Γ ∧ ∅ ##ₘ Γ.
Proof.
  rewrite left_id. solve_map_disjoint.
Qed.

Lemma md2 (Γ1 Γ2 : envT) :
  Γ1 ##ₘ Γ2 ->
  Γ1 ∪ Γ2 = Γ2 ∪ Γ1 ∧ Γ2 ##ₘ Γ1.
Proof.
  intro. rewrite map_union_comm; solve_map_disjoint.
Qed.

Ltac smd := solve_map_disjoint || (rewrite map_union_comm; solve_map_disjoint).

Lemma ctx_subst Γ1 Γ2 k A B e :
  Γ1 ##ₘ Γ2 -> ctx_typed Γ1 k A B -∗ ptyped Γ2 e A -∗ ptyped (Γ1 ∪ Γ2) (k e) B.
Proof.
  intros Hdisj.
  iIntros "Hctx Htyped".
  unfold ctx_typed.
  iApply "Hctx".
  - iPureIntro. done.
  - iFrame.
Qed. *)

(* Lemma typed_ctx1_typed Γ B k e :
  ctx1 k -> ptyped Γ (k e) B -∗
  ∃ Γ1 Γ2 A,
    ⌜⌜ Γ = Γ1 ∪ Γ2 ∧ Γ1 ##ₘ Γ2 ⌝⌝ ∗
    ctx_typed Γ1 k A B ∗ ptyped Γ2 e A.
Proof.
  intros [];
  simpl;
  iIntros "Htyped";
  repeat (iDestruct "Htyped" as (?) "Htyped");
  try iDestruct "Htyped" as "[H1 H2]";
  try iDestruct "H1" as (->) "H1"; subst;
  try destruct H; try destruct H0; subst;
  repeat iExists _; iFrame; iSplit;
  eauto using md1, md2;
  try solve [
    repeat iIntros (?); repeat iIntros "?";
    simpl; rewrite ?left_id;
    repeat iExists _; iSplit;
    iFrame; eauto using md1, md2; iPureIntro; smd
  ].
  repeat iIntros (?); repeat iIntros "?". rewrite left_id. simpl. iFrame.
Qed. *)

(* Lemma typed_ctx_typed Γ B k e :
  ctx k -> ptyped Γ (k e) B -∗
  ∃ Γ1 Γ2 A,
    ⌜⌜ Γ = Γ1 ∪ Γ2 ∧ Γ1 ##ₘ Γ2 ⌝⌝ ∗
    ctx_typed Γ1 k A B ∗ ptyped Γ2 e A.
Proof.
  intros Hctx.
  iIntros "Htyped".
  iInduction Hctx as [] "IH" forall (Γ B).
  - repeat iExists _. iFrame.
    iSplit. eauto using md1.
    repeat iIntros (?). repeat iIntros "?".
    rewrite left_id. done.
  - iDestruct (typed_ctx1_typed with "Htyped") as "H"; eauto.
    iDestruct "H" as (Γ1 Γ2 A (-> & ?)) "[H1 H2]".
    iDestruct ("IH" with "H2") as (Γ0 Γ3 A0 (-> & ?)) "[H3 H4]".
    repeat iExists _. iFrame.
    iSplit.
    + iPureIntro. split.
      * rewrite assoc. reflexivity.
      * solve_map_disjoint.
    + repeat iIntros (?). iIntros "?". unfold ctx_typed.
      replace (Γ1 ∪ Γ0 ∪ Γ') with (Γ1 ∪ (Γ0 ∪ Γ')) by (by rewrite assoc).
      iApply "H1". iPureIntro. solve_map_disjoint.
      iApply "H3". solve_map_disjoint. done.
Qed. *)

(* ptyped with empty environment *)

Fixpoint ptyped0 (e : expr) (t : type) : hProp :=
 match e with
  | Val v =>
      val_typed v t
  | Var x =>
      False
  | App e1 e2 => ∃ t',
      ptyped0 e1 (FunT t' t) ∗
      ptyped0 e2 t'
  | Lam x e => ∃ t1 t2,
      ⌜⌜ t = FunT t1 t2 ⌝⌝ ∗
      ptyped {[ x := t1 ]} e t2
  | Send e1 e2 => ∃ r t',
      ⌜⌜ t = ChanT r⌝⌝ ∗
      ptyped0 e1 (ChanT (SendT t' r)) ∗
      ptyped0 e2 t'
  | Recv e => ∃ t' r,
      ⌜⌜ t = PairT t' (ChanT r) ⌝⌝ ∗
      ptyped0 e (ChanT (RecvT t' r))
  | Let x e1 e2 => ∃ (t' : type),
      ptyped0 e1 t' ∗
      ptyped {[ x := t' ]} e2 t
  | LetUnit e1 e2 =>
      ptyped0 e1 UnitT ∗
      ptyped0 e2 t
  | LetProd x1 x2 e1 e2 => ∃ t1 t2,
      ⌜⌜ x1 ≠ x2 ⌝⌝ ∗
      ptyped0 e1 (PairT t1 t2) ∗
      ptyped ({[ x1 := t1 ]} ∪ {[ x2 := t2 ]}) e2 t
  | If e1 e2 e3 =>
      ptyped0 e1 NatT ∗
      (ptyped0 e2 t ∧ ptyped0 e3 t)
  | Fork e => ∃ r,
      ⌜⌜ t = ChanT r ⌝⌝ ∗
      ptyped0 e (FunT (ChanT (dual r)) UnitT)
  | Close e =>
      ptyped0 e (ChanT EndT)
 end.

Lemma both_emp (A B : envT) : ∅ = A ∪ B -> A = ∅ ∧ B = ∅.
Proof.
  intros H.
  symmetry in H.
  pose proof (map_positive_l _ _ H) as H'.
  subst.
  rewrite left_id in H.
  subst.
  done.
Qed.

Lemma ptyped_ptyped0 e t :
  ptyped ∅ e t -∗ ptyped0 e t.
Proof.
  iIntros "H".
  iInduction e as [] "IH" forall (t); simpl.
  - iDestruct "H" as "[_ H]". done.
  - iDestruct "H" as "%". exfalso. symmetry in H.
    eapply (map_non_empty_singleton _ _ H).
  - iDestruct "H" as (t1 Γ1 Γ2 [H1 H2]) "[H1 H2]".
    iExists t1.
    apply both_emp in H1 as [-> ->].
    iSplitL "H1".
    + iApply "IH". done.
    + iApply "IH1". done.
  - iDestruct "H" as (t1 t2 [H1 H2]) "H".
    iExists t1,t2.
    iSplit. done.
    by rewrite left_id.
  - iDestruct "H" as (r t' Γ1 Γ2 (H1 & H2 & H3)) "[H1 H2]".
    iExists r,t'.
    iSplit. done.
    apply both_emp in H2 as [-> ->].
    iSplitL "H1".
    + iApply "IH". done.
    + iApply "IH1". done.
  - iDestruct "H" as (t' r H) "H".
    iExists t',r.
    iSplit. done.
    iApply "IH". done.
  - iDestruct "H" as (t' Γ1 Γ2 ([-> ->]%both_emp & H2 & H3)) "[H1 H2]".
    iExists t'.
    iSplitL "H1".
    + iApply "IH". done.
    + rewrite left_id. done.
  - iDestruct "H" as (Γ1 Γ2 ([-> ->]%both_emp & H2)) "[H1 H2]".
    iSplitL "H1".
    + iApply "IH". done.
    + iApply "IH1". done.
  - iDestruct "H" as (t1 t2 Γ1 Γ2 (Hneq & [-> ->]%both_emp & H2 & H3)) "[H1 H2]".
    iExists t1,t2.
    iSplitL ""; eauto.
    iSplitL "H1".
    + iApply "IH". done.
    + rewrite left_id. done.
  - iDestruct "H" as (Γ1 Γ2 ([-> ->]%both_emp & H2)) "[H1 H2]".
    iSplitL "H1".
    + iApply "IH". done.
    + iSplit.
      * iDestruct "H2" as "[H _]".
        iApply "IH1". done.
      * iDestruct "H2" as "[_ H]".
        iApply "IH2". done.
  - iDestruct "H" as (r H) "H".
    iExists r.
    iSplit. done.
    iApply "IH". done.
  - iApply "IH". done.
Qed.

Lemma ptyped0_ptyped e t :
  ptyped0 e t -∗ ptyped ∅ e t.
Proof.
  iIntros "H".
  iInduction e as [] "IH" forall (t); simpl.
  - iSplit; done.
  - iDestruct "H" as "%". done.
  - iDestruct "H" as (t1) "[H1 H2]".
    iExists t1,∅,∅.
    iSplit. iPureIntro. rewrite left_id. solve_map_disjoint.
    iSplitL "H1".
    + iApply "IH". done.
    + iApply "IH1". done.
  - iDestruct "H" as (t1 t2 ->) "H".
    iExists t1,t2.
    iSplit. done.
    by rewrite left_id.
  - iDestruct "H" as (r t' ->) "[H1 H2]".
    iExists r,t',∅,∅.
    iSplit. iPureIntro. rewrite left_id. solve_map_disjoint.
    iSplitL "H1".
    + iApply "IH". done.
    + iApply "IH1". done.
  - iDestruct "H" as (t' r ->) "H".
    iExists t',r.
    iSplit. done.
    iApply "IH". done.
  - iDestruct "H" as (t') "[H1 H2]".
    iExists t',∅,∅.
    iSplit. iPureIntro. rewrite left_id. solve_map_disjoint.
    iSplitL "H1".
    + iApply "IH". done.
    + rewrite left_id. done.
  - iDestruct "H" as "[H1 H2]".
    iExists ∅,∅.
    iSplit. iPureIntro. rewrite left_id. solve_map_disjoint.
    iSplitL "H1".
    + iApply "IH". done.
    + iApply "IH1". done.
  - iDestruct "H" as (t1 t2 Hneq) "[H1 H2]".
    iExists t1,t2,∅,∅.
    iSplit. iPureIntro. rewrite left_id. solve_map_disjoint.
    iSplitL "H1".
    + iApply "IH". done.
    + rewrite left_id. done.
  - iDestruct "H" as "[H1 H2]".
    iExists ∅,∅.
    iSplit. iPureIntro. rewrite left_id. solve_map_disjoint.
    iSplitL "H1".
    + iApply "IH". done.
    + iSplit.
      * iDestruct "H2" as "[H _]".
        iApply "IH1". done.
      * iDestruct "H2" as "[_ H]".
        iApply "IH2". done.
  - iDestruct "H" as (r ->) "H".
    iExists r.
    iSplit. done.
    iApply "IH". done.
  - iApply "IH". done.
Qed.


Definition ctx_typed0 (k : expr -> expr)
                     (A : type) (B : type) : hProp :=
    ∀ e,
      ptyped0 e A -∗
      ptyped0 (k e) B.

Lemma ctx_subst0 k A B e :
  ctx_typed0 k A B -∗ ptyped0 e A -∗ ptyped0 (k e) B.
Proof.
  iIntros "Hctx Htyped".
  unfold ctx_typed0.
  iApply "Hctx". done.
Qed.

(* Lemma ctx_typed_ctx_typed0 k A B :
  ctx_typed ∅ k A B -∗ ctx_typed0 k A B.
Proof.
  iIntros "H" (e) "HH".
  iApply ptyped_ptyped0.
  unfold ctx_typed.
  replace (ptyped ∅ (k e) B) with (ptyped (∅ ∪ ∅) (k e) B) by (by rewrite left_id).
  iApply ("H" with "[%] [HH]"). solve_map_disjoint.
  iApply ptyped0_ptyped. done.
Qed. *)

Lemma typed0_ctx1_typed0 B k e :
  ctx1 k -> ptyped0 (k e) B -∗
  ∃ A, ctx_typed0 k A B ∗ ptyped0 e A.
Proof.
  iIntros (Hctx) "H".
  destruct Hctx; simpl;
  repeat iDestruct "H" as (?) "H";
  repeat iDestruct "H" as "[? H]";
  repeat iExists _; iFrame;
  try iIntros (e1) "H1"; simpl;
  repeat iExists _; iFrame;
  try iPureIntro; eauto.
Qed.

Lemma typed0_ctx_typed0 B k e :
  ctx k -> ptyped0 (k e) B -∗
  ∃ A, ctx_typed0 k A B ∗ ptyped0 e A.
Proof.
  iIntros (Hctx) "H".
  iInduction Hctx as [] "IH" forall (B).
  - iExists _. iFrame. iIntros (?) "H". iFrame.
  - iDestruct (typed0_ctx1_typed0 with "H") as (A) "[Hctx H]"; first done.
    iDestruct ("IH" with "H") as (A') "[Hctx' H]".
    iExists _. iFrame. iIntros (e') "H".
    iApply "Hctx". iApply "Hctx'". done.
Qed.

(*
  Asynchronous subtyping:
  -----------------------
  ?A.!B.R < !B.?A.R


  Nat < Int

  x : Nat ==> x : Int
*)

(*
       things that #1 sent             things that #2 sent
cT1    [v1,v2]                         [w1,w2,w3]               cT2
*)
