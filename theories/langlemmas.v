From iris.proofmode Require Export tactics.
Require Export diris.langdef.
Require Export diris.rtypesystem.

Lemma Γunrestricted_empty : Γunrestricted ∅.
Proof.
  intros ??. rewrite lookup_empty. intros. simplify_eq.
Qed.

Lemma pure_step_rtyped e e' t :
  pure_step e e' -> rtyped ∅ e t -∗ rtyped ∅ e' t.
Proof.
  intros Hps.
  iIntros "Ht".
  iInduction Hps as [] "IH"; simpl.
  - iDestruct "Ht" as (t1 t2 Γ1 Γ2 [-> [HH Hdisj]]) "Ht".
    iDestruct "Ht" as "((_ & Ht1) & (_ & Ht2))".
    iSplit. { iPureIntro. apply Γunrestricted_empty. }
    iExists _,_.
    iSplit; first done.
    iFrame.
  - iDestruct "Ht" as (t1 t2 -> ?) "Ht". eauto.
  - iDestruct "Ht" as (t' Γ1 Γ2 H) "Ht".
    iDestruct "Ht" as "((_ & Ht1) & (_ & Ht2))".
    iDestruct "Ht1" as (t1 t2 HH) "Ht1".
    simplify_eq.
    replace (∅ : envT) with (delete x {[ x:= t1 ]} : envT) by (by rewrite delete_singleton).
    iApply (subst_rtyped with "Ht2 Ht1").
    rewrite lookup_singleton. done.
  - iDestruct "Ht" as (t' Γ1 Γ2 H) "Ht".
    iDestruct "Ht" as "((_ & Ht1) & (_ & Ht2))".
    iDestruct "Ht1" as (t1 t2 HH) "Ht1".
    simplify_eq.
    replace (∅ : envT) with (delete x {[ x:= t1 ]} : envT) by (by rewrite delete_singleton).
    iApply (subst_rtyped with "Ht2 Ht1").
    rewrite lookup_singleton. done.
  - iSplit; first done.
    iDestruct "Ht" as (t1 t2 [-> _]) "Ht".
    iExists _,_.
    iSplit; first done. rewrite left_id. done.
  - iSplit; first done.
    iDestruct "Ht" as (t1 t2 [-> _]) "Ht".
    iExists _,_.
    iSplit; first done. rewrite left_id. done.
  - iDestruct "Ht" as (Γ1 Γ2 HH) "[_ [Ht _]]".
    assert (Γ2 = ∅).
    { destruct HH. symmetry in H0.
      assert (Γ1 = ∅). eapply map_positive_l; done. subst.
      rewrite left_id in H0. done. }
    subst. done.
  - iDestruct "Ht" as (Γ1 Γ2 H) "[_ [_ Ht]]".
    assert (Γ2 = ∅).
    { destruct H. symmetry in H.
      assert (Γ1 = ∅). eapply map_positive_l; done. subst.
      rewrite left_id in H. done. }
    subst. done.
  - iDestruct "Ht" as (t1 t2 Γ1 Γ2 (H & Hdisj & Hx)) "[[% Hv] Ht]".
    eapply both_emp in H as [-> ->].
    iDestruct "Hv" as (t0 t3 HH) "Hv". simplify_eq.
    rewrite !left_id.
    destruct b.
    + replace (∅ : envT) with (delete x {[ x := t0]} : envT); last first.
      { apply delete_singleton. }
      iDestruct "Ht" as "[Ht _]".
      iApply (subst_rtyped with "Hv Ht").
      rewrite lookup_singleton //.
    + replace (∅ : envT) with (delete x {[ x := t3]} : envT); last first.
      { apply delete_singleton. }
      iDestruct "Ht" as "[_ Ht]".
      iApply (subst_rtyped with "Hv Ht").
      rewrite lookup_singleton //.
  - iDestruct "Ht" as (t' Γ1 Γ2 H) "[[% Hv] Ht]".
    destruct H as (H & _ & _).
    subst. symmetry in H.
    assert (Γ1 = ∅) as ->. { by eapply map_positive_l. }
    rewrite left_id_L in H. subst. rewrite left_id_L.
    replace (∅ : envT) with (delete x {[ x := t']} : envT); last first.
    { apply delete_singleton. }
    iApply (subst_rtyped with "Hv Ht").
    rewrite lookup_singleton. done.
  - iDestruct "Ht" as (Γ1 Γ2 (H & Hd)) "[% Ht]".
    destruct H0.
    symmetry in H.
    assert (Γ1 = ∅) as ->. { by eapply map_positive_l. }
    rewrite left_id_L in H. subst. done.
  - iDestruct "Ht" as (t1 t2 Γ1 Γ2 (? & ? & ? & ?)) "[[% Hv] Ht]".
    iDestruct "Hv" as (t1' t2' HH) "[Hv1 Hv2]".
    simplify_eq.
    symmetry in H0.
    assert (Γ1 = ∅) as ->. { by eapply map_positive_l. }
    rewrite left_id_L in H0. subst.
    rewrite left_id.
    replace (∅ : envT) with (delete x1 $ delete x2 $ ({[x1 := t1']} ∪ {[x2 := t2']}) : envT); last first.
    { rewrite delete_union delete_singleton right_id.
      rewrite delete_singleton_ne; eauto.
      apply delete_singleton. }
    iApply (subst_rtyped with "Hv1 [Ht Hv2]").
    + rewrite delete_union delete_singleton right_id.
      rewrite delete_singleton_ne; eauto. rewrite lookup_singleton. done.
    + iApply (subst_rtyped with "Hv2 Ht").
      rewrite lookup_union lookup_singleton lookup_singleton_ne; eauto.
Qed.

Lemma pure_step_rtyped0 e e' t :
  pure_step e e' -> rtyped0 e t -∗ rtyped0 e' t.
Proof.
  iIntros (Hs) "Ht".
  iApply rtyped_rtyped0.
  iDestruct (rtyped0_rtyped with "Ht") as "Ht".
  iApply (pure_step_rtyped with "Ht"). done.
Qed.
