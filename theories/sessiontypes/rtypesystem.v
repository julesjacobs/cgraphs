From cgraphs Require Export seplogic.
From stdpp Require Export gmap.
From cgraphs.sessiontypes Require Export langdef.

Inductive object := Thread (_:nat) | Chan (_:chan).

Canonical Structure objectO := leibnizO object.

Global Instance object_eqdecision : EqDecision object.
Proof.
  intros [n|n] [m|m]; unfold Decision; destruct (decide (n = m));
  subst; eauto; right; intro; simplify_eq.
Qed.
Global Instance object_countable : Countable object.
Proof.
  refine (inj_countable' (λ l, match l with
  | Thread n => inl n
  | Chan n => inr n
  end) (λ l, match l with
  | inl n => Thread n
  | inr n => Chan n
  end) _); by intros [].
Qed.

Definition clabel : Type := bool * chan_type.

Definition clabelO := prodO boolO chan_typeO.

Notation rProp := (hProp object clabelO).

Definition own_ep (c : endpoint) (σ : chan_type) : rProp :=
  own_out (Chan c.1) (c.2,σ).

Fixpoint rtyped (Γ : envT) (e : expr) (t : type) : rProp :=
 match e with
  | Val v =>
      ⌜⌜ Γunrestricted Γ ⌝⌝ ∗ val_typed v t
  | Var x => ∃ Γ1,
      ⌜⌜ Γ ≡ Γ1 ∪ {[ x := t ]} ∧ Γ1 !! x = None ∧ Γunrestricted Γ1 ⌝⌝
  | App e1 e2 => ∃ t' Γ1 Γ2,
      ⌜⌜ Γ = Γ1 ∪ Γ2 ∧ disj Γ1 Γ2 ⌝⌝ ∗
      rtyped Γ1 e1 (FunT t' t) ∗ rtyped Γ2 e2 t'
  | Pair e1 e2 => ∃ t1 t2 Γ1 Γ2,
      ⌜⌜ t = PairT t1 t2 ∧ Γ = Γ1 ∪ Γ2 ∧ disj Γ1 Γ2 ⌝⌝ ∗
      rtyped Γ1 e1 t1 ∗ rtyped Γ2 e2 t2
  | Inj b e1 => ∃ t1 t2,
      ⌜⌜ t = SumT t1 t2 ⌝⌝ ∗
      rtyped Γ e1 (if b then t1 else t2)
  | UApp e1 e2 => ∃ t' Γ1 Γ2,
      ⌜⌜ Γ = Γ1 ∪ Γ2 ∧ disj Γ1 Γ2 ⌝⌝ ∗
      rtyped Γ1 e1 (UFunT t' t) ∗ rtyped Γ2 e2 t'
  | Lam x e => ∃ t1 t2,
      ⌜⌜ t = FunT t1 t2 ∧ Γ !! x = None ⌝⌝ ∗
      rtyped (Γ ∪ {[ x := t1 ]}) e t2
  | ULam x e => ∃ t1 t2,
      ⌜⌜ t = UFunT t1 t2 ∧ Γ !! x = None ∧ Γunrestricted Γ ⌝⌝ ∗
      □ rtyped (Γ ∪ {[ x := t1 ]}) e t2
  | Send e1 e2 => ∃ r t' Γ1 Γ2,
      ⌜⌜ t = ChanT r ∧ Γ = Γ1 ∪ Γ2 ∧ disj Γ1 Γ2 ⌝⌝ ∗
      rtyped Γ1 e1 (ChanT (SendT t' r)) ∗ rtyped Γ2 e2 t'
  | Recv e => ∃ t' r,
      ⌜⌜ t = PairT (ChanT r) t' ⌝⌝ ∗
      rtyped Γ e (ChanT (RecvT t' r))
  | Let x e1 e2 => ∃ (t' : type) (Γ1 Γ2 : envT),
      ⌜⌜ Γ = Γ1 ∪ Γ2 ∧ disj Γ1 Γ2 ∧ Γ2 !! x = None ⌝⌝ ∗
      rtyped Γ1 e1 t' ∗ rtyped (Γ2 ∪ {[ x := t' ]}) e2 t
  | LetUnit e1 e2 => ∃ Γ1 Γ2,
      ⌜⌜ Γ = Γ1 ∪ Γ2 ∧ disj Γ1 Γ2 ⌝⌝ ∗
      rtyped Γ1 e1 UnitT ∗ rtyped Γ2 e2 t
  | LetProd x1 x2 e1 e2 => ∃ t1 t2 Γ1 Γ2,
      ⌜⌜ x1 ≠ x2 ∧ Γ = Γ1 ∪ Γ2 ∧ disj Γ1 Γ2 ∧ Γ2 !! x1 = None ∧ Γ2 !! x2 = None  ⌝⌝ ∗
      rtyped Γ1 e1 (PairT t1 t2) ∗ rtyped (Γ2 ∪ {[ x1 := t1 ]} ∪ {[ x2 := t2 ]}) e2 t
  | MatchVoid e =>
      rtyped Γ e VoidT
  | MatchSum e1 x eL eR => ∃ (t1 t2 : type) (Γ1 Γ2 : envT),
      ⌜⌜ Γ = Γ1 ∪ Γ2 ∧ disj Γ1 Γ2 ∧ Γ2 !! x = None ⌝⌝ ∗
      rtyped Γ1 e1 (SumT t1 t2) ∗ (rtyped (Γ2 ∪ {[ x := t1 ]}) eL t ∧ rtyped (Γ2 ∪ {[ x := t2 ]}) eR t)
  | If e1 e2 e3 => ∃ Γ1 Γ2,
      ⌜⌜ Γ = Γ1 ∪ Γ2 ∧ disj Γ1 Γ2 ⌝⌝ ∗
      rtyped Γ1 e1 NatT ∗ (rtyped Γ2 e2 t ∧ rtyped Γ2 e3 t)
  | Fork e => ∃ r,
      ⌜⌜ t = ChanT r ⌝⌝ ∗
      rtyped Γ e (FunT (ChanT (dual r)) UnitT)
  | Close e =>
      ⌜⌜ t = UnitT ⌝⌝ ∗ rtyped Γ e (ChanT EndT)
  end
with val_typed (v : val) (t : type) : rProp :=
  match v with
  | UnitV => ⌜⌜ t = UnitT ⌝⌝
  | NatV n => ⌜⌜ t = NatT ⌝⌝
  | PairV a b => ∃ t1 t2, ⌜⌜ t = PairT t1 t2 ⌝⌝ ∗ val_typed a t1 ∗ val_typed b t2
  | InjV b a => ∃ t1 t2, ⌜⌜ t = SumT t1 t2 ⌝⌝ ∗ val_typed a (if b then t1 else t2)
  | FunV x e => ∃ t1 t2, ⌜⌜ t = FunT t1 t2 ⌝⌝ ∗ rtyped {[ x := t1 ]} e t2
  | UFunV x e => ∃ t1 t2, ⌜⌜ t = UFunT t1 t2 ⌝⌝ ∗ □ rtyped {[ x := t1 ]} e t2
  | ChanV c => ∃ r, ⌜⌜ t = ChanT r ⌝⌝ ∗ own_ep c r
  end.

Global Instance unrestricted_proper : Proper ((≡) ==> iff) unrestricted.
Proof.
  assert (∀ x y : type, x ≡ y → unrestricted x -> unrestricted y).
  { cofix IH. intros x y H Hunr.
    destruct Hunr; inversion H; subst; constructor; eauto. }
  split; eauto. symmetry in H0; eauto.
Qed.

Global Instance Γunrestricted_proper : Proper ((≡) ==> iff) Γunrestricted.
Proof. intros ???. unfold Γunrestricted.
  split; intros.
  - specialize (H x0).
    rewrite H1 in H. inversion H; subst. symmetry in H2.
    rewrite -H4; eauto.
  - specialize (H x0).
    rewrite H1 in H. inversion H; subst. symmetry in H3.
    rewrite H4; eauto.
Qed.

Global Instance disj_proper : Proper ((≡) ==> (≡) ==> iff) disj.
Proof.
  assert (∀ x x' y y',
    x ≡ x' -> y ≡ y' -> disj x y -> disj x' y').
  {
    intros x x' y y' Hx Hy Hdisj i t1 t2 H1 H2.
    pose proof (Hx i) as Hxi.
    pose proof (Hy i) as Hyi.
    rewrite H1 in Hxi.
    rewrite H2 in Hyi.
    inversion Hxi. inversion Hyi. subst.
    symmetry in H. symmetry in H4.
    specialize (Hdisj _ _ _ H H4) as [].
    rewrite -H3. split; last done.
    rewrite H0 H6 //.
  }
  intros ??????. split; eauto.
  symmetry in H0. symmetry in H1. eauto.
Qed.

Lemma rtyped_proper_impl Γ1 Γ2 t1 t2 e :
  Γ1 ≡ Γ2 -> t1 ≡ t2 -> rtyped Γ1 e t1 ⊢ rtyped Γ2 e t2
with val_typed_proper_impl t1 t2 v :
  t1 ≡ t2 -> val_typed v t1 ⊢ val_typed v t2.
Proof.
  - intros H1 H2. destruct e; simpl.
    + rewrite H1. iIntros "[? ?]". iFrame. iApply val_typed_proper_impl; eauto.
    + iIntros "H". iDestruct "H" as %[Γ0 (HH1 & HH2 & HH3)].
      iPureIntro. rewrite ->H1 in HH1. eexists. rewrite -H2. eauto.
    + iIntros "H".
      iDestruct "H" as (t0 t3 Γ0 Γ3 [-> [-> Hdisj]]) "[H1 H2]".
      inversion H2; subst.
      symmetry in H1.
      eapply map_union_equiv_eq in H1 as (y' & z' & Q1 & Q2 & Q3). subst.
      iExists _,_,_,_.
      iSplit. { iPureIntro. split_and!; eauto. rewrite Q2 Q3 //. }
      iSplitL "H1".
      * iApply rtyped_proper_impl; last done; eauto.
      * iApply rtyped_proper_impl; last done; eauto.
    + iIntros "H".
      iDestruct "H" as (t0 t3 ->) "H".
      inversion H2. subst.
      iExists _,_.
      iSplit; first done.
      iApply rtyped_proper_impl; last done; eauto.
      destruct b; eauto.
    + iIntros "H".
      iDestruct "H" as (t' Γ0 Γ3 []) "[H1 H2]".
      subst.
      symmetry in H1.
      eapply map_union_equiv_eq in H1 as (y' & z' & Q1 & Q2 & Q3). subst.
      iExists _,_,_.
      iSplit. { iPureIntro. split; first done. rewrite Q2 Q3 //. }
      iSplitL "H1".
      * iApply rtyped_proper_impl; last done; eauto.
        constructor; eauto.
      * iApply rtyped_proper_impl; last done; eauto.
    + iIntros "H".
      iDestruct "H" as (t' Γ0 Γ3 []) "[H1 H2]".
      subst.
      symmetry in H1.
      eapply map_union_equiv_eq in H1 as (y' & z' & Q1 & Q2 & Q3). subst.
      iExists _,_,_.
      iSplit. { iPureIntro. split; first done. rewrite Q2 Q3 //. }
      iSplitL "H1".
      * iApply rtyped_proper_impl; last done; eauto.
        constructor; eauto.
      * iApply rtyped_proper_impl; last done; eauto.
    + iIntros "H".
      iDestruct "H" as (t0 t3 [-> HH]) "H".
      inversion H2. subst.
      iExists _,_.
      iSplit.
      { iPureIntro. split; first done.
        specialize (H1 s). rewrite HH in H1. inversion H1. done. }
      iApply rtyped_proper_impl; last done; eauto.
      rewrite H1. rewrite H3. done.
    + iIntros "H".
      iDestruct "H" as (t0 t3 [-> [HH Hunr]]) "H".
      inversion H2. subst.
      iExists _,_.
      iSplit.
      { iPureIntro. split; first done.
        split; last first. { rewrite -H1 //. }
        specialize (H1 s). rewrite HH in H1. inversion H1. done. }
      iDestruct "H" as "#H". iModIntro.
      iApply rtyped_proper_impl; last done; eauto.
      rewrite H1. rewrite H3. done.
    + iIntros "H".
      iDestruct "H" as (r t' Γ0 Γ3 [-> [-> HH]]) "[H1 H2]".
      inversion H2. subst.
      symmetry in H1.
      eapply map_union_equiv_eq in H1 as (y' & z' & Q1 & Q2 & Q3). subst.
      iExists _,_,_,_.
      iSplit.
      { iPureIntro. split_and!; eauto.
        rewrite Q2 Q3 //. }
      iSplitL "H1".
      * iApply rtyped_proper_impl; last done; eauto.
        constructor; eauto. constructor; eauto.
      * iApply rtyped_proper_impl; last done; eauto.
    + iIntros "H".
      iDestruct "H" as (t' r ->) "H".
      inversion H2. subst. inversion H3. subst.
      iExists _,_.
      iSplit.
      { iPureIntro. done. }
      iApply rtyped_proper_impl; last done; eauto.
      do 2 constructor; eauto.
    + iIntros "H".
      iDestruct "H" as (t' Γ0 Γ3 [-> [HH1 HH2]]) "[H1 H2]".
      symmetry in H1.
      eapply map_union_equiv_eq in H1 as (y' & z' & Q1 & Q2 & Q3). subst.
      iExists _,_,_.
      iSplit.
      { iPureIntro. split_and!; eauto.
        + rewrite Q2 Q3 //.
        + specialize (Q3 s). rewrite HH2 in Q3. inversion Q3. done. }
      iSplitL "H1".
      * iApply rtyped_proper_impl; last done; eauto.
      * iApply rtyped_proper_impl; last done; eauto.
        rewrite Q3 //.
    + iIntros "H".
      iDestruct "H" as (Γ0 Γ3 [-> HH]) "[H1 H2]".
      symmetry in H1.
      eapply map_union_equiv_eq in H1 as (y' & z' & Q1 & Q2 & Q3). subst.
      iExists _,_.
      iSplit.
      { iPureIntro. split; eauto. rewrite Q2 Q3 //. }
      iSplitL "H1".
      * iApply rtyped_proper_impl; last done; eauto.
      * iApply rtyped_proper_impl; last done; eauto.
    + iIntros "H".
      iDestruct "H" as (t0 t3 Γ0 Γ3 (HH1 & -> & HH2 & HH3 & HH4)) "[H1 H2]".
      symmetry in H1.
      eapply map_union_equiv_eq in H1 as (y' & z' & Q1 & Q2 & Q3). subst.
      iExists _,_,_,_.
      iSplit.
      { iPureIntro. split_and!; eauto.
        + rewrite Q2 Q3 //.
        + specialize (Q3 s). rewrite HH3 in Q3. inversion Q3. done.
        + specialize (Q3 s0). rewrite HH4 in Q3. inversion Q3. done. }
      iSplitL "H1".
      * iApply rtyped_proper_impl; last done; eauto.
      * iApply rtyped_proper_impl; last done; eauto.
        rewrite Q3 //.
    + iIntros "H".
      iApply rtyped_proper_impl; last done; eauto.
    + iIntros "H".
      iDestruct "H" as (t0 t3 Γ0 Γ3 (HH1 & HH2 & HH3)) "[H1 H2]". subst.
      symmetry in H1.
      eapply map_union_equiv_eq in H1 as (y' & z' & Q1 & Q2 & Q3). subst.
      iExists _,_,_,_.
      iSplit.
      { iPureIntro. split; eauto. split.
        + rewrite Q2 Q3 //.
        + specialize (Q3 s). rewrite HH3 in Q3. inversion Q3. done. }
      iSplitL "H1".
      { iApply rtyped_proper_impl; last done; eauto. }
      iSplit.
      * iDestruct "H2" as "[H2 _]". iApply rtyped_proper_impl; last done; eauto. rewrite Q3 //.
      * iDestruct "H2" as "[_ H2]". iApply rtyped_proper_impl; last done; eauto. rewrite Q3 //.
    + iIntros "H".
      iDestruct "H" as (Γ0 Γ3 [-> HH]) "[H1 H2]".
      symmetry in H1.
      eapply map_union_equiv_eq in H1 as (y' & z' & Q1 & Q2 & Q3). subst.
      iExists _,_.
      iSplit.
      { iPureIntro. split; eauto. rewrite Q2 Q3 //. }
      iSplitL "H1".
      * iApply rtyped_proper_impl; last done; eauto.
      * iSplit.
        { iDestruct "H2" as "[H _]".
          iApply rtyped_proper_impl; last done; eauto. }
        { iDestruct "H2" as "[_ H]".
          iApply rtyped_proper_impl; last done; eauto. }
    + iIntros "H".
      iDestruct "H" as (r ->) "H".
      inversion H2. subst.
      iExists _.
      iSplit; first done.
      iApply rtyped_proper_impl; last done; eauto.
      do 2 constructor; eauto.
      rewrite H0 //.
    + iIntros "[-> H]".
      inversion H2. subst.
      iSplit; first done.
      iApply rtyped_proper_impl; last done; eauto.
  - intros H1. destruct v; simpl.
    + iIntros "%". subst. inversion H1. done.
    + iIntros "%". subst. inversion H1. done.
    + iIntros "H".
      iDestruct "H" as (t0 t3 ->) "[H1 H2]".
      inversion H1. subst.
      iExists _,_. iSplit; first done.
      iSplitL "H1".
      * iApply val_typed_proper_impl; eauto.
      * iApply val_typed_proper_impl; eauto.
    + iIntros "H".
      iDestruct "H" as (t0 t3 ->) "H".
      inversion H1. subst.
      iExists _,_.
      iSplit; first done.
      iApply val_typed_proper_impl; last done. by destruct b.
    + iIntros "H".
      iDestruct "H" as (t0 t3 ->) "H".
      inversion H1. subst.
      iExists _,_. iSplit; first done.
      iApply rtyped_proper_impl; last done; eauto.
      rewrite H2. done.
    + iIntros "H".
      iDestruct "H" as (t0 t3 ->) "H".
      inversion H1. subst.
      iExists _,_. iSplit; first done.
      iDestruct "H" as "#H".
      iModIntro.
      iApply rtyped_proper_impl; last done; eauto.
      rewrite H2. done.
    + iIntros "H".
      iDestruct "H" as (r ->) "H".
      inversion H1. subst.
      iExists _. iSplit; first done.
      unfold own_ep. destruct e; simpl. rewrite H0. done.
Qed.

Global Instance : Params (@val_typed) 1 := {}.
Global Instance rtyped_proper : Proper ((≡) ==> (=) ==> (≡) ==> (≡)) rtyped.
Proof.
  intros ?????????. subst. iSplit;
  iIntros "H"; iApply rtyped_proper_impl; last first; eauto.
Qed.
Global Instance val_typed_proper v : Proper ((≡) ==> (≡)) (val_typed v).
Proof.
  intros ???. iSplit;
  iIntros "H"; iApply val_typed_proper_impl; last first; eauto.
Qed.

Lemma typed_rtyped Γ e t : ⌜⌜ typed Γ e t ⌝⌝ -∗ rtyped Γ e t.
Proof.
  iIntros "%".
  iInduction H as [] "IH"; simpl; eauto;
  repeat iExists _;
  repeat (iSplitL || iSplit); eauto.
  - rewrite H1 //.
  - rewrite H //.
Qed.

Ltac foo := simpl; repeat iMatchHyp (fun H P =>
  lazymatch P with
  | ⌜⌜ _ ⌝⌝%I => iDestruct H as %?
  end); simplify_map_eq.

Lemma typed_no_var_subst e Γ t x v :
  Γ !! x = None ->
  rtyped Γ e t -∗
  ⌜ subst x v e = e ⌝.
Proof.
  iIntros (Hx) "Ht".
  iInduction e as [] "IH" forall (Γ t Hx); foo.
  - done.
  - case_decide; eauto. subst. iDestruct "Ht" as "%".
    destruct H as [? []].
    specialize (H s). rewrite Hx in H.
    rewrite lookup_union in H.
    rewrite lookup_singleton in H.
    destruct (x !! s); inversion H.
  - iDestruct "Ht" as (t1 t2 Γ1 Γ2 [-> [-> Hdisj]]) "[H1 H2]".
    iDestruct ("IH" with "[%] H1") as %?.
    { by apply lookup_union_None in Hx as []. }
    iDestruct ("IH1" with "[%] H2") as %?.
    { by apply lookup_union_None in Hx as []. }
    by rewrite H H0.
  - iDestruct "Ht" as (t1 t2 ->) "H".
    iDestruct ("IH" with "[%] H") as %?; eauto.
    iPureIntro. rewrite H //.
  - iDestruct "Ht" as (t' Γ1 Γ2  [-> ?]) "[H1 H2]".
    iDestruct ("IH" with "[%] H1") as %?.
    { by apply lookup_union_None in Hx as []. }
    iDestruct ("IH1" with "[%] H2") as %?.
    { by apply lookup_union_None in Hx as []. }
    by rewrite H0 H1.
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
  - case_decide;[done|].
    iDestruct "Ht" as (t1 t2 [-> ?]) "H".
    iDestruct ("IH" with "[%] H") as %?.
    + rewrite lookup_union. rewrite Hx lookup_singleton_ne; eauto.
    + rewrite H1. done.
  - iDestruct "Ht" as (r t' Γ1 Γ2 (-> & -> & Hdisj)) "[H1 H2]".
    apply lookup_union_None in Hx as [].
    iDestruct ("IH" with "[%] H1") as %?; first done.
    iDestruct ("IH1" with "[%] H2") as %?; first done.
    by rewrite H1 H2.
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
  - iDestruct ("IH" with "[%] Ht") as %?; eauto.
    by rewrite H.
  - iDestruct "Ht" as (t1 t2 Γ1 Γ2 (-> & Hdisj & Hs)) "[H1 H2]".
    apply lookup_union_None in Hx as [].
    iDestruct ("IH" with "[%] H1") as %?; eauto. rewrite H1.
    case_decide; eauto.
    iDestruct ("IH1" with "[%] [H2]") as %?.
    2: { iDestruct "H2" as "[H2 _]". done. }
    { rewrite lookup_union.
      rewrite H0. rewrite lookup_singleton_ne; done. }
    rewrite H3.
    iDestruct ("IH2" with "[%] [H2]") as %?.
    2: { iDestruct "H2" as "[_ H2]". done. }
    { rewrite lookup_union.
      rewrite H0. rewrite lookup_singleton_ne; done. }
    rewrite H4 //.
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
  - iDestruct "Ht" as "[_ Ht]".
    iDestruct ("IH" with "[%] Ht") as %?; eauto.
    by rewrite H.
Qed.

Lemma lookup_union_Some_S (Γ1 Γ2 : envT) x t :
  (Γ1 ∪ Γ2) !! x ≡ Some t ->
  Γ1 !! x ≡ Some t ∨ (Γ1 !! x = None ∧ Γ2 !! x ≡ Some t).
Proof.
  intros H. inversion H. subst.
  symmetry in H0.
  eapply lookup_union_Some_raw in H0 as [|[]].
  - left. rewrite H0. f_equiv. done.
  - right. split; eauto. rewrite H1. f_equiv. done.
Qed.

Lemma disj_union_Some x t Γ1 Γ2 :
  (Γ1 ∪ Γ2) !! x ≡ Some t -> disj Γ1 Γ2 ->
  (Γ1 !! x ≡ Some t ∧ Γ2 !! x = None) ∨
  (Γ1 !! x = None ∧ Γ2 !! x ≡ Some t) ∨
  (Γ1 !! x ≡ Some t ∧ Γ2 !! x ≡ Some t ∧ unrestricted t).
Proof.
  intros H1 H2.
  apply lookup_union_Some_S in H1 as [].
  - destruct (Γ2 !! x) eqn:E; eauto.
    right. right. inversion H. subst. edestruct H2; eauto.
    split_and!; eauto.
    + rewrite -H3 H1 //.
    + rewrite -H3 //.
  - destruct H. eauto.
Qed.

Lemma delete_union_l' a b x :
  disj a b -> b !! x = None -> delete x (a ∪ b) = delete x a ∪ b ∧ disj (delete x a) b.
Proof.
  intros ??.
  rewrite delete_union.
  rewrite (delete_notin b x) //.
  split; first done.
  intros ?????. eapply H; eauto.
  apply lookup_delete_Some in H1 as [].
  done.
Qed.

Lemma delete_union_r' a b x :
  disj a b -> a !! x = None -> delete x (a ∪ b) = a ∪ delete x b ∧ disj a (delete x b).
Proof.
  intros ??.
  rewrite delete_union.
  rewrite (delete_notin a x) //.
  split; first done.
  intros ?????. eapply H; eauto.
  apply lookup_delete_Some in H2 as [].
  done.
Qed.

Lemma delete_union_lr' a b x :
  disj a b -> delete x (a ∪ b) = delete x a ∪ delete x b ∧ disj (delete x a) (delete x b).
Proof.
  intros ?.
  rewrite delete_union.
  split; first done.
  intros ?????.
  apply lookup_delete_Some in H0 as [].
  apply lookup_delete_Some in H1 as [].
  eapply H; eauto.
Qed.

Definition val_typed' (v : val) (t : type) : rProp :=
  match t with
  | UnitT => ⌜⌜ v = UnitV ⌝⌝
  | VoidT => False
  | NatT => ∃ n, ⌜⌜ v = NatV n ⌝⌝
  | PairT t1 t2 => ∃ a b, ⌜⌜ v = PairV a b ⌝⌝ ∗ val_typed a t1 ∗ val_typed b t2
  | SumT t1 t2 => ∃ b a, ⌜⌜ v = InjV b a ⌝⌝ ∗ val_typed a (if b then t1 else t2)
  | FunT t1 t2 => ∃ x e, ⌜⌜ v = FunV x e ⌝⌝ ∗ rtyped {[ x := t1 ]} e t2
  | UFunT t1 t2 => ∃ x e, ⌜⌜ v = UFunV x e ⌝⌝ ∗ □ rtyped {[ x := t1 ]} e t2
  | ChanT r => ∃ c, ⌜⌜ v = ChanV c ⌝⌝ ∗ own_ep c r
  end.

Lemma val_typed_val_typed' v t :
  val_typed v t ⊣⊢ val_typed' v t.
Proof.
  destruct v,t; simpl; iSplit;
  try (iIntros "%"; simplify_eq; eauto; try destruct H; simplify_eq);
  try (iIntros "H"; iDestruct "H" as (? ? ?) "[H1 H2]"); simplify_eq;
  try (iIntros "H"; iDestruct "H" as (? ? ?) "H"); simplify_eq;
  try (iIntros "H"; iDestruct "H" as (? ?) "H"); simplify_eq;
  try (iSplit; iIntros "%"; simplify_eq); eauto; iExists _; iFrame;
  iExists _; iFrame; done.
Qed.

Lemma unrestricted_box v t :
  unrestricted t ->
  val_typed v t ⊢ □ val_typed v t.
Proof.
  revert t. induction v; simpl; [eauto|eauto|..].
  - intros. iIntros "H".
    iDestruct "H" as (t1 t2 ->) "[H1 H2]".
    inversion H. subst.
    iDestruct (IHv1 with "H1") as "H1"; eauto.
    iDestruct (IHv2 with "H2") as "H2"; eauto.
    iDestruct "H1" as "#H1".
    iDestruct "H2" as "#H2".
    iModIntro. iExists _,_. iSplit; first done.
    iSplitL; eauto.
  - intros.
    iIntros "H".
    iDestruct "H" as (t1 t2 ->) "H".
    inversion H. subst.
    iDestruct (IHv with "H") as "H".
    { by destruct b. }
    iDestruct "H" as "#H". iModIntro.
    iExists _,_. iSplit; first done. eauto.
  - intros. iIntros "H". iDestruct "H" as (t1 t2 ->) "H". inversion H.
  - intros. iIntros "H".
    iDestruct "H" as (t1 t2 ->) "#H".
    iModIntro. iExists _,_. iSplit; first done.
    iModIntro. done.
  - intros. iIntros "H".
    iDestruct "H" as (r ->) "H". inversion H.
Qed.

Lemma Γunrestricted_delete Γ x :
  Γunrestricted Γ -> Γunrestricted (delete x Γ).
Proof.
  intros ????. eapply H.
  eapply lookup_delete_Some in H0 as []. done.
Qed.

Lemma unrestricted_Some Γ x vT :
  Γunrestricted Γ -> Γ !! x ≡ Some vT -> unrestricted vT.
Proof.
  intros.
  inversion H0. subst. symmetry in H1.
  eapply H in H1. rewrite -H3 //.
Qed.

Lemma subst_rtyped (Γ : envT) (x : string) (v : val) (vT : type) (e : expr) (eT : type) :
  Γ !! x ≡ Some vT ->
  val_typed v vT -∗
  rtyped Γ e eT -∗
  rtyped (delete x Γ) (subst x v e) eT.
Proof.
  iIntros (H) "Hv He".
  iInduction e as [?|?|?|?|?|?|?|?|?|?|?|?|?|?|?|?|?|?] "IH" forall (eT Γ H); simpl.
  - iDestruct "He" as "[% H']". iFrame.
    iDestruct (unrestricted_box with "Hv") as "Hv"; eauto using unrestricted_Some.
    iPureIntro. eauto using Γunrestricted_delete.
  - iDestruct "He" as %[Γ' [H0 [H1 H2]]].
    case_decide; subst; simpl.
    + pose proof (H0 s) as HH. rewrite ->H in HH.
      rewrite lookup_union in HH.
      rewrite lookup_singleton in HH.
      rewrite H1 in HH. simpl in *.
      inversion HH. subst. rewrite H5. simpl. iFrame.
      iPureIntro. rewrite H0 delete_union delete_singleton right_id delete_notin //.
    + iExists (delete x Γ').
      assert (Γ' !! x ≡ Some vT).
      { specialize (H0 x).
        rewrite lookup_union in H0.
        rewrite lookup_singleton_ne in H0; last done.
        rewrite ->H in H0. destruct (Γ' !! x) eqn:E; simpl in *; inversion H0.
        subst. done. }
      inversion H4. subst. rewrite -H7.
      iDestruct (unrestricted_box with "Hv") as "Hv"; eauto.
      iPureIntro. rewrite H0.
      rewrite delete_union delete_singleton_ne //.
      split; eauto.
      split; eauto using Γunrestricted_delete.
      eapply lookup_delete_None; eauto.
  - iDestruct "He" as (t1 t2 Γ1 Γ2 [-> [-> Hdisj]]) "(He1 & He2)".
    eapply disj_union_Some in H as [[]|[[]|[?[]]]]; last done.
    + iExists _,_,_,_. iSplit.
      { iPureIntro. split; first done. by eapply delete_union_l'. }
      iSplitL "He1 Hv".
      { by iApply ("IH" with "[%] Hv"). }
      { by iDestruct (typed_no_var_subst with "He2") as %->. }
    + iExists _,_,_,_. iSplit.
      { iPureIntro. split; first done. by eapply delete_union_r'. }
      iSplitR "He2 Hv".
      { by iDestruct (typed_no_var_subst with "He1") as %->. }
      { by iApply ("IH1" with "[%] Hv"). }
    + iExists _,_,_,_. iSplit.
      { iPureIntro. split; first done. by eapply delete_union_lr'. }
      iDestruct (unrestricted_box with "Hv") as "Hv"; eauto.
      iDestruct "Hv" as "#Hv".
      iSplitL "He1".
      { iApply ("IH" with "[%]"); eauto. }
      { iApply ("IH1" with "[%]"); eauto. }
  - iDestruct "He" as (t1 t2 ->) "He".
    iExists _,_. iSplit; first done.
    iApply ("IH" with "[%] Hv"); eauto.
  - iDestruct "He" as (t' Γ1 Γ2 [-> ?]) "(He1 & He2)".
    eapply disj_union_Some in H as [[]|[[]|[?[]]]]; last done.
    + iExists _,_,_. iSplit.
      { iPureIntro. by eapply delete_union_l'. }
      iSplitL "He1 Hv".
      { by iApply ("IH" with "[%] Hv"). }
      { by iDestruct (typed_no_var_subst with "He2") as %->. }
    + iExists _,_,_. iSplit.
      { iPureIntro. by eapply delete_union_r'. }
      iSplitR "He2 Hv".
      { by iDestruct (typed_no_var_subst with "He1") as %->. }
      { by iApply ("IH1" with "[%] Hv"). }
    + iExists _,_,_. iSplit.
      { iPureIntro. by eapply delete_union_lr'. }
      iDestruct (unrestricted_box with "Hv") as "Hv"; eauto.
      iDestruct "Hv" as "#Hv".
      iSplitL "He1".
      { iApply ("IH" with "[%]"); eauto. }
      { iApply ("IH1" with "[%]"); eauto. }
  - iDestruct "He" as (t' Γ1 Γ2 [-> ?]) "(He1 & He2)".
    eapply disj_union_Some in H as [[]|[[]|[?[]]]]; last done.
    + iExists _,_,_. iSplit.
      { iPureIntro. by eapply delete_union_l'. }
      iSplitL "He1 Hv".
      { by iApply ("IH" with "[%] Hv"). }
      { by iDestruct (typed_no_var_subst with "He2") as %->. }
    + iExists _,_,_. iSplit.
      { iPureIntro. by eapply delete_union_r'. }
      iSplitR "He2 Hv".
      { by iDestruct (typed_no_var_subst with "He1") as %->. }
      { by iApply ("IH1" with "[%] Hv"). }
    + iExists _,_,_. iSplit.
      { iPureIntro. by eapply delete_union_lr'. }
      iDestruct (unrestricted_box with "Hv") as "Hv"; eauto.
      iDestruct "Hv" as "#Hv".
      iSplitL "He1".
      { iApply ("IH" with "[%]"); eauto. }
      { iApply ("IH1" with "[%]"); eauto. }
  - iDestruct "He" as (t1 t2 (-> & Hs)) "H".
    case_decide.
    + simplify_eq. rewrite Hs in H. inversion H.
    + simpl. iExists _,_. iSplit.
      { iPureIntro. split; eauto. rewrite lookup_delete_None. eauto. }
      { replace (delete x Γ ∪ {[s := t1]}) with (delete x (Γ ∪ {[s := t1]})).
        iApply ("IH" with "[%] Hv H").
        - rewrite lookup_union. rewrite lookup_singleton_ne; eauto.
          rewrite <-H. destruct (Γ !! x); eauto.
        - rewrite delete_union. rewrite delete_singleton_ne; eauto. }
  - iDestruct "He" as (t1 t2 (-> & [Hs Hunr])) "H".
        case_decide.
        + simplify_eq. rewrite Hs in H. inversion H.
        + simpl. iExists _,_. iSplit.
          { iPureIntro. split; eauto. rewrite lookup_delete_None.
            split; eauto. apply Γunrestricted_delete. done. }
          iDestruct "H" as "#H".
          iDestruct (unrestricted_box with "Hv") as "Hv".
          { inversion H. subst. rewrite -H3. eapply Hunr. symmetry. done. }
          iDestruct "Hv" as "#Hv".
          iModIntro.
          { replace (delete x Γ ∪ {[s := t1]}) with (delete x (Γ ∪ {[s := t1]})).
            iApply ("IH" with "[%] Hv H").
            - rewrite lookup_union. rewrite lookup_singleton_ne; eauto.
              rewrite <-H. destruct (Γ !! x); eauto.
            - rewrite delete_union. rewrite delete_singleton_ne; eauto. }
  - iDestruct "He" as (r t' Γ1 Γ2 (-> & -> & ?)) "[H1 H2]".
    eapply disj_union_Some in H as [[]|[[]|[?[]]]]; last done.
    + iExists _,_,_,_. iSplit.
      { iPureIntro. split; eauto. by apply delete_union_l'. }
      iSplitL "H1 Hv".
      { by iApply ("IH" with "[%] Hv"). }
      { by iDestruct (typed_no_var_subst with "H2") as %->. }
    + iExists _,_,_,_. iSplit.
      { iPureIntro. split; eauto. by apply delete_union_r'. }
      iSplitR "H2 Hv".
      { by iDestruct (typed_no_var_subst with "H1") as %->. }
      { by iApply ("IH1" with "[%] Hv"). }
    + iExists _,_,_,_. iSplit.
      { iPureIntro. split; first done. by eapply delete_union_lr'. }
      iDestruct (unrestricted_box with "Hv") as "Hv"; eauto.
      iDestruct "Hv" as "#Hv".
      iSplitL "H1".
      { iApply ("IH" with "[%]"); eauto. }
      { iApply ("IH1" with "[%]"); eauto. }
  - iDestruct "He" as (t r ->) "H".
    iExists _,_. iSplit. done.
    iApply ("IH" with "[%] Hv H"). done.
  - iDestruct "He" as (t' Γ1 Γ2 (-> & ? & ?)) "[H1 H2]".
    eapply disj_union_Some in H as [[]|[[]|[?[]]]]; last done.
    + repeat iExists _. iSplit.
      { iPureIntro. rewrite assoc. split; last done. by apply delete_union_l'. }
      iSplitL "H1 Hv".
      { by iApply ("IH" with "[%] Hv"). }
      { case_decide. done.
        iDestruct (typed_no_var_subst e2 _ _ _ v with "H2") as %?.
        - rewrite lookup_union.
          rewrite lookup_singleton_ne; last done.
          rewrite H2. done.
        - rewrite H4. done. }
    + iExists _,_,_. iSplit.
      { iPureIntro. rewrite assoc. split. eapply delete_union_r'; eauto.
        eapply lookup_delete_None; eauto. }
      iSplitR "H2 Hv".
      { by iDestruct (typed_no_var_subst with "H1") as %->. }
      { case_decide. { subst. rewrite H1 in H2. inversion H2. }
        replace (delete x Γ2 ∪ {[s := t']}) with (delete x (Γ2 ∪ {[s := t']})).
        - iApply ("IH1" with "[%] Hv H2").
          rewrite lookup_union. rewrite lookup_singleton_ne; eauto.
          rewrite <-H2. destruct (Γ2 !! x); done.
        - rewrite delete_union. rewrite delete_singleton_ne; eauto. }
    + iExists _,_,_. iSplit.
      { iPureIntro. rewrite assoc. split. apply delete_union_lr'; eauto.
        apply lookup_delete_None; eauto. }
      iDestruct (unrestricted_box with "Hv") as "Hv"; eauto.
      iDestruct "Hv" as "#Hv".
      iSplitL "H1".
      { iApply ("IH" with "[%]"); eauto. }
      { case_decide. { subst. rewrite H1 in H2. inversion H2. }
        replace (delete x Γ2 ∪ {[s := t']}) with (delete x (Γ2 ∪ {[s := t']})).
        - iApply ("IH1" with "[%] Hv H2").
          rewrite lookup_union. rewrite lookup_singleton_ne; eauto.
          rewrite <-H2. destruct (Γ2 !! x); done.
        - rewrite delete_union. rewrite delete_singleton_ne; eauto. }
  - iDestruct "He" as (Γ1 Γ2 (-> & ?)) "[H1 H2]".
    eapply disj_union_Some in H as [[]|[[]|[?[]]]]; last done.
    + repeat iExists _. iSplit.
      { iPureIntro. apply delete_union_l'; eauto. }
      iSplitL "H1 Hv".
      { iApply ("IH" with "[%] Hv H1"). done. }
      { iDestruct (typed_no_var_subst with "H2") as %->; eauto. }
    + repeat iExists _. iSplit.
      { iPureIntro. apply delete_union_r'; eauto. }
      iSplitL "H1".
      { iDestruct (typed_no_var_subst with "H1") as %->; eauto. }
      { iApply ("IH1" with "[%] Hv H2"). done. }
    + repeat iExists _. iSplit.
      { iPureIntro. by eapply delete_union_lr'. }
      iDestruct (unrestricted_box with "Hv") as "Hv"; eauto.
      iDestruct "Hv" as "#Hv".
      iSplitL "H1".
      { iApply ("IH" with "[%]"); eauto. }
      { iApply ("IH1" with "[%]"); eauto. }
  - iDestruct "He" as (t1 t2 Γ1 Γ2 (Hneq & -> & ? & ? & ?)) "[H1 H2]".
    eapply disj_union_Some in H as [[]|[[]|[?[]]]]; last done.
    + repeat iExists _. iSplit.
      { iPureIntro. split;eauto. rewrite assoc. split. apply delete_union_l'; eauto.
        solve_map_disjoint. }
      iSplitL "H1 Hv".
      { iApply ("IH" with "[%] Hv H1"). done. }
      { case_decide.
        - done.
        - iDestruct (typed_no_var_subst with "H2") as %->; eauto.
          rewrite !lookup_union. rewrite H3.
          rewrite !lookup_singleton_ne; eauto. }
    + repeat iExists _. iSplit.
      { iPureIntro. split;eauto. rewrite assoc. split. apply delete_union_r'; eauto.
        split. eapply lookup_delete_None; eauto.
        eapply lookup_delete_None; eauto. }
      iSplitL "H1".
      { iDestruct (typed_no_var_subst with "H1") as %->; eauto. }
      { case_decide.
        - destruct H4; subst; simplify_eq. rewrite H1 in H3. inversion H3.
          rewrite H2 in H3. inversion H3.
        - replace (delete x Γ2 ∪ {[s := t1]} ∪ {[s0 := t2]}) with
                  (delete x (Γ2 ∪ {[s := t1]} ∪ {[s0 := t2]})).
          { iApply ("IH1" with "[%] Hv H2").
            rewrite !lookup_union.
            rewrite !lookup_singleton_ne; eauto.
            rewrite <- H3. destruct (Γ2 !! x); eauto. }
          { rewrite !delete_union. rewrite !delete_singleton_ne; eauto. } }
    + repeat iExists _. iSplit.
      { iPureIntro. split;eauto. rewrite assoc. split. apply delete_union_lr'; eauto.
        split. eapply lookup_delete_None; eauto.
        eapply lookup_delete_None; eauto. }
      iDestruct (unrestricted_box with "Hv") as "Hv"; eauto.
      iDestruct "Hv" as "#Hv".
      iSplitL "H1".
      { iApply ("IH" with "[%]"); eauto. }
      { case_decide.
        - destruct H5; subst; simplify_eq. rewrite H1 in H3. inversion H3.
          rewrite H2 in H3. inversion H3.
        - replace (delete x Γ2 ∪ {[s := t1]} ∪ {[s0 := t2]}) with
                  (delete x (Γ2 ∪ {[s := t1]} ∪ {[s0 := t2]})).
          { iApply ("IH1" with "[%] Hv H2").
            rewrite !lookup_union.
            rewrite !lookup_singleton_ne; eauto.
            rewrite <- H3. destruct (Γ2 !! x); eauto. }
          { rewrite !delete_union. rewrite !delete_singleton_ne; eauto. } }
  - iApply ("IH" with "[%] Hv He"). done.
  - iDestruct "He" as (t1 t2 Γ1 Γ2 (-> & Hdisj & Hs)) "[H1 H2]".
    eapply disj_union_Some in H as [[]|[[]|[?[]]]]; last done.
    + repeat iExists _. iSplit.
      { iPureIntro. rewrite assoc. split; last done. by apply delete_union_l'. }
      iSplitL "H1 Hv".
      { by iApply ("IH" with "[%] Hv"). }
      { case_decide. done.
        iSplit.
        { iDestruct "H2" as "[H2 _]".
          iDestruct (typed_no_var_subst e2 _ _ _ v with "H2") as %?.
          { rewrite lookup_union.
            rewrite lookup_singleton_ne; last done.
            rewrite H0. done. }
          rewrite H2 //. }
        { iDestruct "H2" as "[_ H2]".
          iDestruct (typed_no_var_subst e3 _ _ _ v with "H2") as %?.
          { rewrite lookup_union.
            rewrite lookup_singleton_ne; last done.
            rewrite H0. done. }
          rewrite H2 //. } }
    + iExists _,_,_,_. iSplit.
      { iPureIntro. rewrite assoc. split. eapply delete_union_r'; eauto.
        eapply lookup_delete_None; eauto. }
      iSplitR "H2 Hv".
      { by iDestruct (typed_no_var_subst with "H1") as %->. }
      { case_decide. { subst. rewrite Hs in H0. inversion H0. }
        replace (delete x Γ2 ∪ {[s := t1]}) with (delete x (Γ2 ∪ {[s := t1]})); last first.
        { rewrite delete_union. rewrite delete_singleton_ne; eauto. }
        replace (delete x Γ2 ∪ {[s := t2]}) with (delete x (Γ2 ∪ {[s := t2]})); last first.
        { rewrite delete_union. rewrite delete_singleton_ne; eauto. }
        iSplit.
        {
          iDestruct "H2" as "[H2 _]".
          iApply ("IH1" with "[%] Hv H2").
          rewrite lookup_union. rewrite lookup_singleton_ne; eauto.
          rewrite <-H0. destruct (Γ2 !! x); done.
        }
        {
          iDestruct "H2" as "[_ H2]".
          iApply ("IH2" with "[%] Hv H2").
          rewrite lookup_union. rewrite lookup_singleton_ne; eauto.
          rewrite <-H0. destruct (Γ2 !! x); done.
        } }
    + iExists _,_,_,_. iSplit.
      { iPureIntro. rewrite assoc. split. apply delete_union_lr'; eauto.
        apply lookup_delete_None; eauto. }
      iDestruct (unrestricted_box with "Hv") as "Hv"; eauto.
      iDestruct "Hv" as "#Hv".
      iSplitL "H1".
      { iApply ("IH" with "[%]"); eauto. }
      { case_decide. { subst. rewrite Hs in H0. inversion H0. }
        replace (delete x Γ2 ∪ {[s := t1]}) with (delete x (Γ2 ∪ {[s := t1]})); last first.
        { rewrite delete_union. rewrite delete_singleton_ne; eauto. }
        replace (delete x Γ2 ∪ {[s := t2]}) with (delete x (Γ2 ∪ {[s := t2]})); last first.
        { rewrite delete_union. rewrite delete_singleton_ne; eauto. }
        iSplit.
        {
          iDestruct "H2" as "[H2 _]".
          iApply ("IH1" with "[%] Hv H2").
          rewrite lookup_union. rewrite lookup_singleton_ne; eauto.
          rewrite <-H0. destruct (Γ2 !! x); done.
        }
        {
          iDestruct "H2" as "[_ H2]".
          iApply ("IH2" with "[%] Hv H2").
          rewrite lookup_union. rewrite lookup_singleton_ne; eauto.
          rewrite <-H0. destruct (Γ2 !! x); done.
        } }
  - iDestruct "He" as (Γ1 Γ2 (-> & ?)) "[H1 H2]".
    eapply disj_union_Some in H as [[]|[[]|[?[]]]]; last done.
    + repeat iExists _. iSplit.
      { iPureIntro. apply delete_union_l'; eauto. }
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
      { iPureIntro. apply delete_union_r'; eauto. }
      iSplitL "H1".
      { iDestruct (typed_no_var_subst with "H1") as %->; eauto. }
      { iSplit.
        - iDestruct "H2" as "[H _]".
          iApply ("IH1" with "[%] Hv H"). done.
        - iDestruct "H2" as "[_ H]".
          iApply ("IH2" with "[%] Hv H"). done. }
    + repeat iExists _. iSplit.
      { iPureIntro. apply delete_union_lr'; eauto. }
      iDestruct (unrestricted_box with "Hv") as "Hv"; eauto.
      iDestruct "Hv" as "#Hv".
      iSplitL "H1".
      { iApply ("IH" with "[%]"); eauto. }
      { iSplit.
        - iDestruct "H2" as "[H _]".
          iApply ("IH1" with "[%] Hv H"). done.
        - iDestruct "H2" as "[_ H]".
          iApply ("IH2" with "[%] Hv H"). done. }
  - iDestruct "He" as (r ->) "H".
    iExists _. iSplit.
    { iPureIntro. done. }
    { iApply ("IH" with "[%] Hv H"). done. }
  - iDestruct "He" as "[% He]".
    iSplit; first done.
    iApply ("IH" with "[%] Hv He"). done.
Qed.

(* rtyped with empty environment *)

Fixpoint rtyped0 (e : expr) (t : type) : rProp :=
 match e with
  | Val v => val_typed v t
  | Var x => False
  | Pair e1 e2 => ∃ t1 t2, ⌜⌜ t = PairT t1 t2 ⌝⌝ ∗ rtyped0 e1 t1 ∗ rtyped0 e2 t2
  | Inj b e => ∃ t1 t2, ⌜⌜ t = SumT t1 t2 ⌝⌝ ∗ rtyped0 e (if b then t1 else t2)
  | App e1 e2 => ∃ t', rtyped0 e1 (FunT t' t) ∗ rtyped0 e2 t'
  | UApp e1 e2 => ∃ t', rtyped0 e1 (UFunT t' t) ∗ rtyped0 e2 t'
  | Lam x e => ∃ t1 t2, ⌜⌜ t = FunT t1 t2 ⌝⌝ ∗ rtyped {[ x := t1 ]} e t2
  | ULam x e => ∃ t1 t2, ⌜⌜ t = UFunT t1 t2 ⌝⌝ ∗ □ rtyped {[ x := t1 ]} e t2
  | Send e1 e2 => ∃ r t', ⌜⌜ t = ChanT r⌝⌝ ∗ rtyped0 e1 (ChanT (SendT t' r)) ∗ rtyped0 e2 t'
  | Recv e => ∃ t' r, ⌜⌜ t = PairT (ChanT r) t' ⌝⌝ ∗ rtyped0 e (ChanT (RecvT t' r))
  | Let x e1 e2 => ∃ t', rtyped0 e1 t' ∗ rtyped {[ x := t' ]} e2 t
  | LetUnit e1 e2 => rtyped0 e1 UnitT ∗ rtyped0 e2 t
  | LetProd x1 x2 e1 e2 => ∃ t1 t2, ⌜⌜ x1 ≠ x2 ⌝⌝ ∗ rtyped0 e1 (PairT t1 t2) ∗ rtyped ({[ x1 := t1 ]} ∪ {[ x2 := t2 ]}) e2 t
  | MatchVoid e => rtyped0 e VoidT
  | MatchSum e x eL eR => ∃ t1 t2, rtyped0 e (SumT t1 t2) ∗ (rtyped {[ x := t1 ]} eL t ∧ rtyped {[ x := t2 ]} eR t)
  | If e1 e2 e3 => rtyped0 e1 NatT ∗ (rtyped0 e2 t ∧ rtyped0 e3 t)
  | Fork e => ∃ r, ⌜⌜ t = ChanT r ⌝⌝ ∗ rtyped0 e (FunT (ChanT (dual r)) UnitT)
  | Close e => ⌜⌜ t = UnitT ⌝⌝ ∗ rtyped0 e (ChanT EndT)
 end%I.
Global Instance : Params (@rtyped0) 1 := {}.

Lemma both_emp (A B : envT) : ∅ = A ∪ B -> A = ∅ ∧ B = ∅.
Proof.
  intros H. symmetry in H.
  pose proof (map_positive_l _ _ H) as H'. subst.
  rewrite left_id in H. subst. done.
Qed.

Lemma disj_empty_l m : disj ∅ m.
Proof. intros ???. rewrite lookup_empty. intros. simplify_eq. Qed.

Lemma disj_empty_r m : disj m ∅.
Proof. intros ???. rewrite lookup_empty. intros. simplify_eq. Qed.

Lemma equiv_exists {A} (P Q : A -> rProp) :
  (∀ x, P x ⊣⊢ Q x) → (∃ x, P x) ⊣⊢ (∃ x, Q x).
Proof.
  intros H. iSplit; iIntros "H"; iDestruct "H" as (x) "H"; iExists x; rewrite H //.
Qed.

Lemma exists_unique_emp (P : envT -> envT -> rProp) :
  (∀ x y, P x y ⊢ ⌜ ∅ = x ∪ y ⌝) -> (∃ x y, P x y) ⊣⊢ P ∅ ∅.
Proof.
  intros H. iSplit; iIntros "H"; eauto.
  iDestruct "H" as (x y) "H".
  iDestruct (H with "H") as "%".
  by apply both_emp in H0 as [-> ->].
Qed.

Lemma frame_iff (P Q R : rProp) :
  Q ⊣⊢ R -> Q ∗ P ⊣⊢ R ∗ P.
Proof.
  intros H. rewrite H //.
Qed.

Lemma frame_last (P Q : rProp) :
  Q ⊣⊢ ⌜⌜ True ⌝⌝ -> Q ∗ P ⊣⊢ P.
Proof.
  intros H. rewrite H //. iSplit; eauto. iIntros "H". by iDestruct "H" as (?) "H".
Qed.

Lemma pure_iff (φ1 φ2 : Prop) :
  φ1 <-> φ2 -> ⌜⌜ φ1 ⌝⌝ ⊣⊢ (⌜⌜ φ2 ⌝⌝ : rProp).
Proof.
  by intros ->.
Qed.

Lemma refl_true {A} (x : A) :
  x = x <-> True.
Proof.
  split; eauto.
Qed.

Lemma disj_empty_true :
  disj ∅ ∅ <-> True.
Proof.
  split; eauto. intros _. eapply disj_empty_l.
Qed.

Lemma unrestricted_empty_true :
  Γunrestricted ∅ <-> True.
Proof.
  split; eauto. intros _. intros ??. rewrite lookup_empty. intro. congruence.
Qed.

Lemma rtyped_rtyped0_iff e t :
  rtyped ∅ e t ⊣⊢ rtyped0 e t.
Proof.
  revert t. induction e; intro; simpl; repeat (eapply equiv_exists; intro); rewrite -?IHe -?IHe1 -?IHe2 -?IHe3; try done;
  try rewrite exists_unique_emp; intros; try (iIntros "H"; iDestruct "H" as (H) "H"; naive_solver);
  rewrite ?left_id ?lookup_empty; repeat apply frame_iff; try (rewrite assoc; apply frame_iff); try apply frame_last;
  try apply pure_iff; rewrite ?refl_true ?disj_empty_true ?unrestricted_empty_true ?left_id ?right_id; eauto.
  iSplit; eauto. iIntros "H". iDestruct "H" as (Γ1) "%".
  destruct H as [H _]. exfalso. specialize (H s).
  revert H. rewrite lookup_union lookup_singleton lookup_empty.
  destruct (Γ1 !! s); intros H; inversion H.
Qed.

Lemma typed0_ctx1_typed0 B k e :
  ctx1 k -> rtyped0 (k e) B -∗ ∃ A, rtyped0 e A ∗ ∀ e, rtyped0 e A -∗ rtyped0 (k e) B.
Proof.
  iIntros (Hctx) "H".
  destruct Hctx; simpl;
  repeat iDestruct "H" as (?) "H";
  repeat iDestruct "H" as "[? H]";
  repeat iExists _; iFrame;
  try iIntros (e1) "H1"; simpl;
  repeat iExists _; iFrame;
  try iPureIntro; eauto.
  iIntros (ee) "H1". simpl. eauto with iFrame.
Qed.

Lemma rtyped0_ctx k e B :
  ctx k -> rtyped0 (k e) B ⊣⊢ ∃ t, rtyped0 e t ∗ ∀ e', rtyped0 e' t -∗ rtyped0 (k e') B.
Proof.
  intros Hctx.
  iSplit; iIntros "H". 2: { iDestruct "H" as (t) "[H1 H2]". by iApply "H2". }
  iInduction Hctx as [] "IH" forall (B).
  { iExists _. iFrame. iIntros (?) "H". iFrame. }
  iDestruct (typed0_ctx1_typed0 with "H") as (A) "[H Hctx]"; first done.
  iDestruct ("IH" with "H") as (A') "[Hctx' H]".
  iExists _. iFrame. iIntros (?) "?".
  iApply "Hctx". iApply "H". done.
Qed.

Lemma subst_rtyped0 (x : string) (v : val) (vT : type) (e : expr) (eT : type) :
  val_typed v vT -∗
  rtyped {[ x := vT ]} e eT -∗
  rtyped0 (subst x v e) eT.
Proof.
  iIntros "Hv Hr".
  rewrite -rtyped_rtyped0_iff.
  replace (∅ : envT) with (delete x {[ x := vT]} : envT) by (apply delete_singleton).
  iApply (subst_rtyped with "Hv Hr"). rewrite lookup_singleton //.
Qed.

Lemma pure_step_rtyped0 e e' t :
  pure_step e e' -> rtyped0 e t -∗ rtyped0 e' t.
Proof.
  intros Hps.
  iIntros "Ht".
  iInduction Hps as [] "IH"; simpl;
  repeat (iDestruct "Ht" as "[Ht Ht2]" || iDestruct "Ht" as (?) "Ht"); eauto; try destruct b; simplify_eq;
  try iApply (subst_rtyped0 with "Ht2 Ht");
  try solve [try iDestruct "Ht2" as "[_ Ht2]"; eauto; try iApply (subst_rtyped0 with "Ht Ht2")];
  try solve [try iDestruct "Ht2" as "[Ht2 _]"; eauto; try iApply (subst_rtyped0 with "Ht Ht2")].
  iDestruct "Ht" as "%".
  iDestruct "Ht2" as "[Ht2 HH]".
  iDestruct "Ht2" as (t0 t3 HH) "[Hv1 Hv2]".
  rewrite -rtyped_rtyped0_iff.
  replace (∅ : envT) with (delete x1 $ delete x2 $ (({[x1 := t1]} ∪ {[x2 := t2]})) : envT); last first.
  { rewrite delete_union delete_singleton right_id delete_singleton_ne // delete_singleton //. }
  iApply (subst_rtyped with "Hv1 [HH Hv2]"); simplify_eq.
  + rewrite delete_union delete_singleton right_id delete_singleton_ne // lookup_singleton //.
  + iApply (subst_rtyped with "Hv2 HH"). rewrite lookup_union lookup_singleton lookup_singleton_ne //.
Qed.