From cgraphs.multiparty Require Import invariant langdef.
Require Import Coq.Logic.Classical.


Definition blocked es h (x y : object) (l : clabel) : Prop :=
  ∃ i j, x = Thread i ∧ y = Chan j ∧ thread_blocked es h i j.

Lemma rtyped_inner e t :
  rtyped0 e t -∗ ⌜ (∃ v, e = Val v)  ∨
  ∃ k e0, ctx k ∧ e = k e0 ∧
    ((∃ e', pure_step e0 e') ∨
     (∃ v p, e0 = Recv p (Val v)) ∨
     (∃ v1 v2 p i, e0 = Send p (Val v1) i (Val v2)) ∨
     (∃ n f, e0 = Spawn n (Val ∘ f)) ∨
     (∃ v, e0 = Close (Val v))) ⌝.
Proof.
  iIntros "H".
  iInduction e as [] "IH" forall (t); simpl; [eauto|eauto|..].
  - iDestruct "H" as (t1 t2 ->) "[H1 H2]".
    iDestruct ("IH" with "H1") as "%". iClear "IH".
    iDestruct ("IH1" with "H2") as "%". iClear "IH1".
    destruct H as [[v ->]|(k & e0 & Hk & -> & H)].
    + destruct H0 as [[v' ->]|(k & e0 & Hk & -> & H0)].
      * iPureIntro. right. exists (λ x, x). eexists.
        split_and!; eauto.
        { constructor. }
        left. eexists.
        constructor.
      * iPureIntro. right.
        eexists (λ x, Pair (Val v) (k x)),_.
        split_and!; eauto.
        constructor; eauto. constructor.
    + iPureIntro. right.
      eexists (λ x, Pair (k x) e2),_.
      split_and!; eauto.
      eapply (Ctx_cons (λ x, Pair x e2)); eauto. constructor.
  - iDestruct "H" as (t1 t2 ->) "H".
    iDestruct ("IH" with "H") as "%". iClear "IH".
    destruct H as [[v ->]|(k & e0 & Hk & -> & H)].
    + iPureIntro. right. exists (λ x, x). eexists.
      split_and!; eauto.
      { constructor. }
      left. eexists.
      constructor.
    + iPureIntro. right.
      eexists (λ x, Inj b (k x)),_.
      split_and!; eauto.
      eapply (Ctx_cons (λ x, Inj b x)); eauto.
      constructor.
  - iDestruct "H" as (n0 f i' [-> ->]) "H".
    iDestruct ("IH" with "H") as "%". iClear "IH".
    destruct H as [[v ->]|(k & e0 & Hk & -> & H)].
    + iPureIntro. right. exists (λ x, x). eexists.
      split_and!; eauto.
      { constructor. }
      left. eexists.
      constructor.
    + iPureIntro. right.
      eexists (λ x, InjN i' (k x)),_.
      split_and!; eauto.
      eapply (Ctx_cons (λ x, InjN i' x)); eauto.
      econstructor.
  - iDestruct "H" as (t') "[H1 H2]".
    iDestruct ("IH" with "H1") as "%". iClear "IH".
    iDestruct ("IH1" with "H2") as "%". iClear "IH1".
    destruct H as [[v ->]|(k & e0 & Hk & -> & H)].
    + destruct H0 as [[v' ->]|(k & e0 & Hk & -> & H0)].
      * simpl. rewrite val_typed_val_typed'. simpl.
        iDestruct "H1" as (x e ->) "H1".
        iPureIntro. right. exists (λ x, x). eexists.
        split_and!; eauto.
        { constructor. }
        left. eexists.
        constructor.
      * iPureIntro. right.
        eexists (λ x, App (Val v) (k x)),_.
        split_and!; eauto.
        constructor; eauto. constructor.
    + iPureIntro. right.
      eexists (λ x, App (k x) e2),_.
      split_and!; eauto.
      eapply (Ctx_cons (λ x, App x e2)); eauto.
      constructor.
  - iDestruct "H" as (t') "[H1 H2]".
      iDestruct ("IH" with "H1") as "%". iClear "IH".
      iDestruct ("IH1" with "H2") as "%". iClear "IH1".
      destruct H as [[v ->]|(k & e0 & Hk & -> & H)].
      + destruct H0 as [[v' ->]|(k & e0 & Hk & -> & H0)].
        * simpl. rewrite val_typed_val_typed'. simpl.
          iDestruct "H1" as (x e ->) "H1".
          iPureIntro. right. exists (λ x, x). eexists.
          split_and!; eauto.
          { constructor. }
          left. eexists.
          constructor.
        * iPureIntro. right.
          eexists (λ x, UApp (Val v) (k x)),_.
          split_and!; eauto.
          constructor; eauto. constructor.
      + iPureIntro. right.
        eexists (λ x, UApp (k x) e2),_.
        split_and!; eauto.
        eapply (Ctx_cons (λ x, UApp x e2)); eauto.
        constructor.
  - iPureIntro. right.
    eexists (λ x, x),_.
    split_and!; [constructor|eauto|].
    left. eexists. constructor.
  - iPureIntro. right.
    eexists (λ x, x),_.
    split_and!; [constructor|eauto|].
    left. eexists. constructor.
  - iDestruct "H" as (n' r t' i [-> ->]) "[H1 H2]".
    iDestruct ("IH" with "H1") as "%". iClear "IH".
    iDestruct ("IH1" with "H2") as "%". iClear "IH1".
    iPureIntro.
    destruct H as [[v ->]|(k & e0 & Hk & -> & H)].
    + destruct H0 as [[v' ->]|(k & e0 & Hk & -> & H0)].
      * right.
        eexists (λ x, x), _.
        split_and!; [constructor|eauto 10..].
      * right.
        eexists (λ x, Send p (Val v) _ (k x)),_.
        split_and!; eauto.
        constructor; eauto. constructor.
    + right.
      eexists (λ x, Send p (k x) _ e2),_.
      split_and!; eauto.
      eapply (Ctx_cons (λ x, Send p x _ e2)); eauto.
      constructor.
  - iDestruct "H" as (n r' r Q) "H".
    iDestruct ("IH" with "H") as "%". iClear "IH".
    iPureIntro. right.
    destruct H as [[v ->]|(k & e0 & Hk & -> & H)].
    + eexists (λ x, x),_. split_and!; [constructor|eauto 10..].
    + eexists (λ x, Recv p (k x)),_. split_and!; eauto.
      constructor; eauto. constructor.
  - iDestruct "H" as (t') "[H1 H2]".
    iDestruct ("IH" with "H1") as "%". iClear "IH".
    destruct H as [[v ->]|(k & e0 & Hk & -> & H)].
    + iPureIntro. right.
      eexists (λ x, x), _. split_and!; [constructor|eauto|].
      left. eexists. constructor.
    + iPureIntro. right.
      eexists (λ x, Let s (k x) e2),_.
      split_and!; eauto.
      eapply (Ctx_cons (λ x, Let s x e2)); eauto.
      constructor.
  - iDestruct "H" as "[H1 H2]".
    iDestruct ("IH" with "H1") as "%". iClear "IH".
    destruct H as [[v ->]|(k & e0 & Hk & -> & H)].
    + simpl. rewrite val_typed_val_typed'. simpl.
      iDestruct "H1" as "->". iPureIntro. right.
      eexists (λ x, x), _. split_and!; [constructor|eauto|].
      left. eexists. constructor.
    + iPureIntro. right.
      eexists (λ x, LetUnit (k x) e2),_.
      split_and!; eauto.
      eapply (Ctx_cons (λ x, LetUnit x e2)); eauto.
      constructor.
  - iDestruct "H" as (t1 t2 Hneq) "[H1 H2]".
    iDestruct ("IH" with "H1") as "%". iClear "IH".
    destruct H as [[v ->]|(k & e0 & Hk & -> & H)].
    + simpl. rewrite val_typed_val_typed'. simpl.
      iDestruct "H1" as (a b ->) "[H11 H12]". iPureIntro. right.
      eexists (λ x, x), _. split_and!; [constructor|eauto|].
      left. eexists. constructor.
    + iPureIntro. right.
      eexists (λ x, LetProd s s0 (k x) e2),_.
      split_and!; eauto.
      eapply (Ctx_cons (λ x, LetProd s s0 x e2)); eauto.
      constructor.
  - iDestruct ("IH" with "H") as "%". iClear "IH".
    destruct H as [[v ->]|(k & e0 & Hk & -> & H)].
    + simpl. rewrite val_typed_val_typed'. simpl. iDestruct "H" as %[].
    + iPureIntro. right.
      eexists (λ x, MatchVoid (k x)),_. split_and!; eauto.
      constructor; eauto. constructor.
  - iDestruct "H" as (t1 t2) "[H1 H2]".
    iDestruct ("IH" with "H1") as "%". iClear "IH".
    destruct H as [[v ->]|(k & e0 & Hk & -> & H)].
    + simpl. rewrite val_typed_val_typed'. simpl.
      iDestruct "H1" as (b a) "[-> H]".
      iPureIntro. right.
      exists (λ x, x). eexists.
      split_and!; eauto.
      { constructor. }
      left.
      eexists. constructor.
    + iPureIntro. right.
      eexists (λ x, MatchSum (k x) s e2 e3),_.
      split_and!; eauto.
      eapply (Ctx_cons (λ x, MatchSum x s e2 e3)); eauto.
      constructor.
  - iDestruct "H" as (f) "[H1 H2]".
    iDestruct ("IH1" with "H1") as "%". iClear "IH IH1".
    destruct H as [[v ->]|(k & e0' & Hk & -> & H)].
    + simpl. rewrite val_typed_val_typed'. simpl.
      iDestruct "H1" as (i a) "[-> H1]".
      iPureIntro. right. exists (λ x, x). eexists.
      split_and!; eauto using ctx, pure_step.
    + iPureIntro. right.
      eexists (λ x, MatchSumN n (k x) e0),_.
      split_and!; eauto.
      eapply (Ctx_cons (λ x, MatchSumN n x e0)); eauto.
      constructor.
  - iDestruct "H" as "[H1 H2]".
    iDestruct ("IH" with "H1") as "%". iClear "IH".
    destruct H as [[v ->]|(k & e0 & Hk & -> & H)].
    + simpl. rewrite val_typed_val_typed'. simpl.
      iDestruct "H1" as (n) "->".
      iPureIntro. right. exists (λ x, x). eexists.
      split_and!; eauto.
      { constructor. }
      left.
      destruct (decide (n = 0)); subst; eexists.
      * eapply If_step2.
      * constructor. done.
    + iPureIntro. right.
      eexists (λ x, If (k x) e2 e3),_.
      split_and!; eauto.
      eapply (Ctx_cons (λ x, If x e2 e3)); eauto.
      constructor.
  - iDestruct "H" as (σs [Hteq Hcons]) "H".
    destruct (classic (∀ i, ∃ v, e i = Val v)) as [H|H].
    + iPureIntro. right.
      exists id, (Spawn n e).
      split; first eauto using ctx.
      split; first done.
      right. right. right. left.
      exists n.
      eapply fin_choice in H as [f Hf].
      exists f. f_equiv.
      apply functional_extensionality; eauto.
    + destruct (classic (∃ i, ∀ v, e i ≠ Val v)); last first.
      { exfalso.
        assert (∀ i, ¬ ∀ v, e i ≠ Val v) by naive_solver.
        eapply H. intros. specialize (H1 i).
        destruct (classic (∃ v, e i = Val v)); eauto.
        exfalso. eapply H1. intros ??.
        eapply H2. exists v. done. }
      destruct H0 as [i Hi].
      iRight.
      iDestruct (big_sepS_elem_of_acc with "H") as "[H1 H2]".
      { eapply all_fin_all. }
      iDestruct ("IH" with "H1") as %HH. iPureIntro.
      destruct HH; first naive_solver.
      destruct H0 as (k & e0 & Hk & He & HH).
      eexists ((λ x, Spawn n (λ j, if decide (i = j) then x else e j)) ∘ k),_.
      split_and!; eauto.
      * eapply (Ctx_cons (λ x, Spawn n (λ j, if decide (i = j) then x else e j)) k);
        eauto using ctx1.
      * simpl. f_equal. eapply functional_extensionality. intro.
        case_decide; subst; eauto.
  - iDestruct "H" as (->) "H".
    iDestruct ("IH" with "H") as "%". iClear "IH".
    iPureIntro. right.
    destruct H as [[v ->]|(k & e0 & Hk & -> & H)].
    + eexists (λ x, x),_. split_and!; [constructor|eauto 10..].
    + eexists (λ x, Close (k x)),_. split_and!; eauto.
      constructor; eauto. constructor.
  - iDestruct "H" as (σ ->) "H".
    iDestruct ("IH" with "H") as "%". iClear "IH".
    iRight.
    destruct H as [[v ->]|(k & e0 & Hk & -> & H)].
    + simpl. rewrite val_typed_val_typed'. simpl.
      iDestruct "H" as (c π ->) "H".
      iPureIntro.
      eexists (λ x, x),_.
      split_and!; eauto using ctx.
      destruct c. eauto using pure_step.
    + iPureIntro.
      eexists (λ x, Relabel p (k x)),_. split_and!; eauto.
      constructor; eauto. constructor.
Qed.

Lemma heap_fresh (h : heap) :
  ∃ i, ∀ p, h !! (i,p) = None.
Proof.
  exists (fresh (dom (gmap_curry h))).
  intro. pose proof (is_fresh (dom (gmap_curry h))).
  rewrite ->not_elem_of_dom in H.
  rewrite -lookup_gmap_curry.
  rewrite H. done.
Qed.

Lemma final_state_decision (es : list expr) (h : heap) :
  ((∃ c, is_Some (h !! c)) ∨ (∃ e, e ∈ es ∧ e ≠ Val UnitV)) ∨
  (h = ∅ ∧ ∀ e, e ∈ es -> e = Val UnitV).
Proof.
  destruct (classic ((∃ c, is_Some (h !! c)) ∨ (∃ e, e ∈ es ∧ e ≠ Val UnitV))); eauto.
  right. split.
  - apply map_eq. intros. rewrite lookup_empty.
    destruct (h !! i) eqn:E; eauto. exfalso.
    apply H. left. eexists. erewrite E. eauto.
  - intros.
    assert (¬ (e ≠ Val UnitV)) by naive_solver.
    by apply NNPP.
Qed.



Definition own_dom A : rProp := ∃ Σ, ⌜⌜ A = dom Σ ⌝⌝ ∗ own Σ.

Lemma own_dom_empty : own_dom ∅ ⊣⊢ emp.
Proof.
  iSplit; unfold own_dom; iIntros "H".
  - iDestruct "H" as (? H) "H".
    symmetry in H. apply dom_empty_iff_L in H as ->.
    by iApply own_empty.
  - iExists ∅. rewrite own_empty dom_empty_L //.
Qed.

Lemma own_dom_singleton k v : own {[ k := v ]} ⊢ own_dom {[ k ]}.
Proof.
  iIntros "H". iExists {[ k := v ]}.
  rewrite dom_singleton_L. iFrame. done.
Qed.

Lemma own_dom_union A B : own_dom A ∗ own_dom B ⊢ own_dom (A ∪ B).
Proof.
  iIntros "[H1 H2]".
  iDestruct "H1" as (Σ1 H1) "H1".
  iDestruct "H2" as (Σ2 H2) "H2". subst.
  iExists (Σ1 ∪ Σ2). rewrite dom_union_L. iSplit; eauto.
  iApply own_union. iFrame.
Qed.

Lemma own_dom_fin_gset `{Countable A} n (g : fin n -> A) (f : A -> gset object) :
  ([∗ set] p ∈ fin_gset n g, own_dom (f p)) -∗ own_dom (big_union (fin_gset n (f ∘ g))).
Proof.
  induction n.
  - rewrite !fin_gset_0 big_union_empty big_sepS_empty own_dom_empty //.
  - rewrite !fin_gset_S big_union_singleton_union.
    destruct (decide (g 0%fin ∈ fin_gset n (λ i : fin n, g (FS i)))).
    + rewrite subseteq_union_1_L; last rewrite singleton_subseteq_l //.
      rewrite subseteq_union_1_L; first apply IHn.
      eapply elem_of_fin_gset in e.
      intros ??.
      eapply elem_of_big_union.
      destruct e. simpl in *.
      rewrite -H1 in H0.
      eexists. split; last done.
      eapply elem_of_fin_gset. eauto.
    + rewrite big_sepS_insert //.
      iIntros "[H1 H2]".
      iDestruct (IHn with "H2") as "H2".
      iApply own_dom_union. iFrame.
Qed.

Lemma own_dom_fin_union n f :
  ([∗ set] p ∈ all_fin n, own_dom (f p)) ⊢ own_dom (fin_union n f).
Proof.
  iApply own_dom_fin_gset.
Qed.

Ltac model := repeat
  (setoid_rewrite pure_sep_holds || setoid_rewrite exists_holds
  || setoid_rewrite own_holds || setoid_rewrite val_typed_val_typed'
  || setoid_rewrite sep_holds).

Lemma own_dom_all {A} (f : A -> gset object) :
  (∀ i, own_dom (f i)) ⊢ ⌜ ∀ i j, f i = f j ⌝.
Proof.
  apply entails_holds.
  intros Σ H.
  rewrite pure_holds. intros.
  rewrite ->forall_holds in H.
  assert (∀ i, f i = dom Σ).
  { intros k. specialize (H k).
    eapply exists_holds in H as [].
    eapply pure_sep_holds in H as [].
    eapply own_holds in H0.
    rewrite -H0 H //. }
  rewrite !H0 //.
Qed.

Lemma own_dom_and A B :
  own_dom A ∧ own_dom B ⊢ ⌜ A = B ⌝.
Proof.
  iIntros "H".
  iAssert (∀ c:bool, own_dom (if c then A else B))%I with "[H]" as "H".
  { iIntros ([]).
    - by iDestruct "H" as "[H _]".
    - by iDestruct "H" as "[_ H]". }
  iDestruct (own_dom_all with "H") as %Q.
  specialize (Q true false). simpl in *. eauto.
Qed.

Lemma fin_union_same `{Countable A} n (s : gset A) :
  fin_union (S n) (λ i, s) = s.
Proof.
  induction n.
  - rewrite fin_union_S fin_union_0 right_id_L //.
  - rewrite fin_union_S IHn union_idemp_L //.
Qed.

Lemma rtyped_refs Γ e t :
  rtyped Γ e t ⊢ own_dom (expr_refs e)
with val_typed_refs v t :
  val_typed v t ⊢ own_dom (val_refs v).
Proof.
  - iIntros "H". destruct e; simpl; repeat (iDestruct "H" as (?) "H");
    rewrite ?val_typed_refs ?rtyped_refs ?own_dom_empty ?own_dom_union; eauto.
    + iDestruct "H" as "[H1 H2]".
      rewrite -assoc_L.
      iApply own_dom_union. iFrame.
      iDestruct (own_dom_and with "H2") as %->.
      iDestruct "H2" as "[_ H2]".
      rewrite union_idemp_L //.
    + iDestruct "H" as "[H1 H2]". iApply own_dom_union; iFrame.
      case_decide; subst. { rewrite fin_union_0 own_dom_empty //. }
      iAssert (∀ i, own_dom (expr_refs (e0 i)))%I with "[H2]" as "H".
      { iIntros (i). iApply rtyped_refs. eauto. }
      destruct n; simplify_eq.
      iDestruct (own_dom_all with "H") as %Q.
      assert (expr_refs ∘ e0 = λ i, expr_refs (e0 0%fin)) as ->.
      { apply functional_extensionality. intros. eapply Q. }
      rewrite fin_union_same. iApply "H".
    + iDestruct "H" as "[H1 [H2 _]]"; iApply own_dom_union; iFrame.
    + iApply own_dom_fin_union.
      iApply (big_sepS_impl with "H"). iModIntro.
      iIntros (x Hx) "H". simpl.
      iApply rtyped_refs. done.
  - iIntros "H". destruct v; simpl; rewrite ?own_dom_empty; eauto;
    repeat (iDestruct "H" as (?) "H"); rewrite ?val_typed_refs ?rtyped_refs ?own_dom_union; eauto.
    destruct e. by iApply own_dom_singleton.
Qed.

Lemma own_dom_map_union `{Countable A} {V V'} (ma : gmap A V) (mb : gmap A V') f :
  ([∗ map] a;b ∈ ma;mb, own_dom (f a)) -∗
  own_dom (map_union f ma).
Proof.
  revert mb; induction ma using map_ind; intros; iIntros "H".
  - iDestruct (big_sepM2_empty_r with "H") as %->.
    iClear "H". unfold map_union. rewrite map_fold_empty own_dom_empty //.
  - iDestruct (big_sepM2_lookup_iff with "H") as %Q.
    assert (is_Some (mb !! i)) as []. { rewrite -Q; smap. }
    assert (mb = <[ i := x0 ]> mb) as -> by (apply map_eq; intro; smap).
    rewrite big_sepM2_insert_delete.
    iDestruct "H" as "[H1 H2]".
    rewrite delete_notin //.
    iDestruct (IHma with "H2") as "H2".
    unfold map_union. rewrite map_fold_insert; eauto.
    { iApply own_dom_union. iFrame. }
    intros ??????. smap; intros; smap; set_solver.
Qed.

Lemma bufs_typed_refs bufss σs :
  bufs_typed bufss σs ⊢ own_dom (bufs_refs bufss).
Proof.
  iIntros "H".
  unfold bufs_typed.
  iDestruct "H" as (sbufs Hsbufs) "H".
  unfold entries_typed.
  unfold bufs_refs.
  iApply own_dom_map_union.
  iApply (big_sepM2_impl with "H"). iModIntro.
  iIntros (k x1 x2 H1 H2) "H".
  iApply own_dom_map_union.
  iApply (big_sepM2_impl with "H"). iModIntro.
  iIntros (k' l1 l2 H1' H2') "H".
  unfold buf_refs. clear.
  iInduction l1 as [] "IH" forall (l2); simpl.
  - iDestruct (big_sepL2_nil_inv_l with "H") as %->.
    rewrite own_dom_empty //.
  - destruct a.
    destruct l2.
    { iDestruct (big_sepL2_nil_inv_r with "H") as %Q. smap. }
    simpl. iDestruct "H" as "[[% H1] H2]".
    iApply own_dom_union.
    iSplitL "H1".
    + iApply val_typed_refs. eauto.
    + iApply "IH". iFrame.
Qed.

Lemma obj_refs_state_inv' es h x Δ :
  state_inv es h x Δ ⊢ own_dom (obj_refs es h x).
Proof.
  iIntros "H".
  destruct x; simpl.
  - iDestruct "H" as (?) "H". destruct (es !! n); simpl;
    rewrite -?rtyped_rtyped0_iff ?rtyped_refs ?own_dom_empty //.
  - iDestruct "H" as (σs H) "H".
    iApply bufs_typed_refs. done.
Qed.

Lemma obj_refs_state_inv es h x Δ Σ :
  holds (state_inv es h x Δ) Σ -> obj_refs es h x = dom Σ.
Proof.
  intros HH. eapply holds_entails in HH; last apply obj_refs_state_inv'.
  revert HH. model. intros (Σ' & HH1 & HH2). rewrite HH1 HH2 //.
Qed.


Lemma dom_lookup_Some_equiv `{Countable A} `{Equiv B} (m : gmap A B) (x : A) (y : B) :
  m !! x ≡ Some y -> x ∈ dom m.
Proof.
  intros HH. inversion HH. subst. eapply elem_of_dom. rewrite -H1 //.
Qed.

Lemma gmap_slice_pop_fmap `{Countable A,Countable B,Countable C} {V}
  (c : A) (p : B) (q : C) (m : bufsT B (A*C) V) :
  pop p q (gmap_slice m c) = (λ '(x,m'), (x,gmap_slice m' c)) <$> pop p (c,q) m.
Proof.
  unfold pop. rewrite gmap_slice_lookup.
  destruct (m !! (c, q)); eauto.
  destruct (g !! p); eauto.
  destruct l; eauto. simpl.
  rewrite gmap_slice_insert. smap.
Qed.

Lemma strong_progress es h x :
  invariant es h -> active es h x -> reachable es h x.
Proof.
  intros Hinv. assert (invariant es h) as Hinv'; eauto.
  revert Hinv'.
  intros (g & Hwf & Hvs). revert x.
  eapply (cgraph_ind' (blocked es h) g (λ x,
    active es h x → reachable es h x));
    [solve_proper|eauto|].
  intros x Hind_out Hind_in Hactive.
  (* Get the invariant for x *)
  pose proof (Hvs x) as Hx.
  (* Case analyze whether x is a channel or a thread *)
  destruct x as [i|c]; simpl in *.
  - (* Thread *)
    destruct Hactive as (e & He & Heneq). (* Thread is active, so must have expression in thread pool *)
    rewrite He in Hx. (* We can conclude that this expression is well-typed wrt out edges *)
    apply pure_sep_holds in Hx as [Hinl Hx].
    eapply prim_simple_adequacy in Hx as Hx'; last eapply rtyped_inner.
    (* Case analyze whether it's a value or pure step or channel op  *)
    destruct Hx' as [(v & ->)|Hx'].
    {
      (* Value *)
      eapply prim_simple_adequacy; first done.
      simpl. rewrite val_typed_val_typed'. simpl.
      iIntros (->). simplify_eq.
    }
    (* Expr in context *)
    destruct Hx' as (k' & e0 & Hctx & -> & Hcases).
    rewrite ->rtyped0_ctx in Hx; eauto.
    apply exists_holds in Hx as [t Hx].
    apply sep_holds in Hx as (Σ1&Σ2&Hout&Hdisj&Het&Hctxt).
    destruct Hcases as [H|[H|[H|[H|H]]]].
    * (* Pure step *)
      destruct H as [e' H].
      eapply Thread_step_reachable.
      eexists _,_.
      econstructor; last done.
      eauto using head_step, ctx_step.
    * (* Recv *)
      destruct H as (v & p & ->).
      revert Het.
      model.
      intros (n & t' & r & Q & [c q] & π & -> & Het). simpl in *.

      assert (out_edges g (Thread i) !! Chan c ≡ Some (q, RecvT n (π p) t' (relabelT π ∘ r))) as HH.
      {
        rewrite Hout -Het.
        erewrite lookup_union_Some_l; last first.
        - rewrite lookup_singleton. done.
        - do 2 f_equiv. apply session_type_equiv_alt. done.
      }

      pose proof (out_edges_in_labels _ _ _ _ HH) as [x Hin].

      pose proof (Hvs (Chan c)) as Hc.
      revert Hc. rewrite Hin. intros Hc.
      simpl in *.
      eapply exists_holds in Hc as [σs Hc].
      eapply pure_sep_holds in Hc as [Heq Hc].
      eapply map_to_multiset_lookup in Heq.
      (* eapply prim_simple_adequacy; first exact Hc. *)
      (* iIntros "H". *)
      (* iDestruct (bufs_typed_recv with "H") as %(bufs & buf & Hbufs & Hbuf); first done. *)
      (* iPureIntro. *)
      destruct (pop (π p) (c,q) h) as [[[]]|] eqn:E.
      {
        eapply Thread_step_reachable.
        unfold can_stepi.
        eexists _,_.
        econstructor; last done.
        econstructor; first done.
        eapply Recv_step; eauto.
      }
      assert (thread_blocked es h i c).
      { unfold thread_blocked.
        assert (is_Some (h !! (c,q))); last eauto 10.
        eapply prim_simple_adequacy; first exact Hc.
        iIntros "H".
        iDestruct (bufs_typed_recv with "H") as %QQ.
        {
          inversion Heq. simplify_eq.
          eexists. eauto.
        }
        iPureIntro. rewrite gmap_slice_lookup in QQ.
        done. }
      eapply Thread_blocked_reachable; eauto.
      eapply Hind_out. { unfold blocked; eauto. }
      eexists _,_; eauto.
      unfold active.
      exists q.
      rewrite -gmap_slice_lookup.
      eapply prim_simple_adequacy; first exact Hc.
      eapply bufs_typed_recv; eauto.
      inversion Heq. rewrite -H0. eauto.
    * (* Send *)
      destruct H as (v1 & v2 & p & i' & ->).
      revert Het. model.
      intros (j & r & t' & j' & [-> ->] & Σ3 & Σ4 & Σeq & Hdisj' & ([c b] & π & -> & Het1) & Het2).
      eapply Thread_step_reachable. eexists _,_.
      econstructor; last done.
      eauto using head_step, ctx_step.
    * (* Fork *)
      destruct H as (n & f & ->).
      destruct (heap_fresh h) as [ii HH].
      eapply Thread_step_reachable. eexists _,_.
      econstructor; last done.
      eauto using head_step, ctx_step.
    * (* Close *)
      destruct H as (v & ->).
      revert Het. model.
      intros (-> & ([c b] & π & -> & Het)).
      eapply Thread_step_reachable. eexists _,_.
      econstructor; last done.
      eauto using head_step, ctx_step.
  - (* Channel *)
    destruct Hactive as (b & Hib).
    rewrite -gmap_slice_lookup in Hib.
    apply exists_holds in Hx as [σs Hx].
    apply pure_sep_holds in Hx as [Hinl Hx].
    eapply prim_simple_adequacy; first exact Hx.
    iIntros "H".
    iDestruct (bufs_typed_progress with "H") as %[HH|Hcp].
    { rewrite HH lookup_empty in Hib. by destruct Hib. }
    iPureIntro.
    unfold can_progress in *.
    destruct Hcp as (p & σ & Hp & Hσ).
    (* destruct Hp as (σ & bufs & Hσ & Hbufs & Hrne). *)

    assert (∃ x, out_edges g x !! (Chan c) ≡ Some (p, σ)) as [y Hy].
    {
      erewrite map_to_multiset_Some in Hinl; last done.
      eapply in_labels_out_edges; eauto.
    }

    eapply (Chan_ref_reachable _ _ _ y).
    {
      erewrite obj_refs_state_inv; eauto.
      eapply dom_lookup_Some_equiv; eauto.
    }

    eapply Hind_in; eauto.
    + intros (i & c' & -> & ? & Hw). simplify_eq.
      unfold thread_blocked in Hw.
      destruct Hw as (p' & q' & k & π & Hctx & Hi & Hpres & Hpop).
      specialize (Hvs (Thread i)).
      eapply (holds_entails _ (∃ n t s, own_out (Chan c') (q', RecvT n (π p') t (relabelT π ∘ s)) ∗ True)%I) in Hvs. 2:
      {
        simpl. iIntros "[_ H]". rewrite Hi.
        rewrite rtyped0_ctx //.
        iDestruct "H" as (t) "[H1 H2]". simpl.
        iDestruct "H1" as (? t' r ? Q) "H1".
        remember (SumNT n (λ i : fin n, PairT (ChanT (r i)) (t' i))).
        inversion H; simplify_eq.
        iDestruct "H1" as (HH) "H". simplify_eq.
        iExists _,_,_. unfold own_ep. simpl.
        rewrite -(session_type_id_id (relabelT π (RecvT n p' t' r))) /=. iFrame.
      }
      apply exists_holds in Hvs as [n Hvs].
      apply exists_holds in Hvs as [tt Hvs].
      apply exists_holds in Hvs as [ss Hvs].
      assert (out_edges g (Thread i) !! Chan c' ≡ Some (q', RecvT n (π p') tt (relabelT π ∘ ss))) as Hoc'.
      {
        eapply sep_holds in Hvs as (Σ1 & Σ2 & H1 & HD & [HH _]).
        rewrite H1.
        eapply own_holds in HH.
        rewrite lookup_union -HH lookup_singleton.
        destruct (Σ2 !! Chan c') eqn:E; rewrite E; simpl; done.
      }
      revert Hoc'. rewrite Hy. intros Hoc'.
      inversion Hoc'. simplify_eq.
      (* inversion H1. simpl in *. *)
      (* inversion H0; simplify_eq. *)
      destruct Hσ as (y & bufs' & Hσ).
      rewrite gmap_slice_pop_fmap Hpop in Hσ.
      simplify_eq.
    + specialize (Hvs y).
      revert Hy Hvs. clear.
      intros Hy Hvs.
      destruct y; simpl in *.
      { eapply pure_sep_holds in Hvs as [_ Hvs].
        destruct (es !! n).
        - eexists. split; first done.
          intros ->. simpl in *.
          eapply affinely_pure_holds in Hvs as [Hvs _].
          revert Hy. rewrite Hvs lookup_empty. intros HH.
          inversion HH.
        - eapply emp_holds in Hvs. exfalso.
          revert Hy. rewrite Hvs lookup_empty. intros HH.
          inversion HH.
      }
      {
        eapply exists_holds in Hvs as [σs Hvs].
        eapply pure_sep_holds in Hvs as [_ Hvs].
        destruct (classic (∃ p : participant, is_Some (h !! (s, p)))); eauto.
        exfalso.
        assert (gmap_slice h s = ∅) as HH.
        { eapply map_eq. intros x.
          rewrite lookup_empty gmap_slice_lookup.
          destruct (h !! (s,x)) eqn:E; eauto.
          exfalso. eauto. }
        rewrite HH in Hvs.
        eapply holds_entails in Hvs; last apply bufs_typed_empty_inv.
        eapply affinely_pure_holds in Hvs as [Hvs _].
        revert Hy. rewrite Hvs lookup_empty. intros HHH.
        inversion HHH.
      }
Qed.

Lemma active_progress es h x :
  invariant es h -> active es h x -> ∃ (es' : list expr) (h' : heap), step es h es' h'.
Proof.
  intros H1 H2.
  cut (reachable es h x); eauto using strong_progress. clear.
  induction 1; eauto. destruct H as (es'&h'&?). exists es', h'. econstructor; eauto.
Qed.

Lemma inv_global_progress es h :
  invariant es h ->
  (h = ∅ ∧ ∀ e, e ∈ es -> e = Val UnitV) ∨
  (∃ es' h', step es h es' h').
Proof.
  intros H.
  destruct (final_state_decision es h) as [Hdec|Hdec]; eauto; right.
  assert (∃ x, active es h x) as [x Hactive].
  { destruct Hdec as [(x&?)|(x&?)].
    + destruct x as [c b]. exists (Chan c). simpl. eauto.
    + destruct H0. eapply elem_of_list_lookup in H0 as [].
      exists (Thread x0). simpl. eauto. }
  eapply active_progress; eauto.
Qed.

Lemma activeset_exists es h :
  ∃ s : gset object, ∀ x, active es h x -> x ∈ s.
Proof.
  exists (list_to_set (Thread <$> seq 0 (length es)) ∪
          set_map (Chan ∘ fst) (dom h)).
  intros. rewrite elem_of_union.
  rewrite elem_of_list_to_set elem_of_list_fmap elem_of_map.
  setoid_rewrite elem_of_seq.
  setoid_rewrite elem_of_dom. simpl.
  unfold active in *.
  destruct x;[left|right].
  - destruct H as (?&?&?). eapply lookup_lt_Some in H. eauto with lia.
  - destruct H as (?&?). eexists (_,_). eauto.
Qed.

Lemma obj_refs_active es h x y :
  y ∈ obj_refs es h x -> active es h x.
Proof.
  destruct x; simpl.
  - destruct (es !! n); simpl; last set_solver.
    destruct (classic (e = Val UnitV)); eauto.
    subst. simpl. set_solver.
  - destruct (decide (gmap_slice h s = ∅)) as [->|]; first set_solver.
    apply map_choose in n as (?&?&?).
    rewrite gmap_slice_lookup in H. eauto.
Qed.
