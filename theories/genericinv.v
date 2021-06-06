Require Export diris.cgraph.
Require Export diris.seplogic.

Section genericinv.
  Context {V : Type}.
  Context `{Countable V}.
  Context {L : Type}.

  Definition inv (f : V -> multiset L -> hProp V L) : Prop :=
    ∃ g : cgraph V L, cgraph_wf g ∧
      ∀ v : V, holds (f v (in_labels g v)) (out_edges g v).

  Lemma adequacy f (φ : V -> multiset L -> gmap V L -> Prop) :
    inv f ->
    (∀ v x, f v x ⊢ ∃ Σ, ⌜⌜ φ v x Σ ⌝⌝ ∗ own Σ) ->
    ∃ g, cgraph_wf g ∧ ∀ v, φ v (in_labels g v) (out_edges g v).
  Proof.
    intros Hinv HH.
    destruct Hinv as (g & Hwf & H1).
    exists g. split; eauto.
    intros v.
    specialize (H1 v).
    specialize (HH v (in_labels g v)).
    eapply holds_entails in H1. 2: {
      iIntros "H".
      iDestruct (HH with "H") as "H".
      iExact "H".
    }
    apply exists_holds in H1 as (Σ & H1).
    apply pure_sep_holds in H1 as (H1 & H2).
    apply own_holds in H2. subst. done.
  Qed.

  Lemma inv_impl f f' :
    (∀ v x, f v x ⊢ f' v x) ->
    inv f -> inv f'.
  Proof.
    intros Himpl (g & Hg & HH).
    exists g. eauto using holds_entails.
  Qed.

  Lemma inv_init :
    inv (λ v x, ⌜⌜ x ≡ ε ⌝⌝ ∗ emp)%I.
  Proof.
    exists ∅.
    split.
    - apply empty_wf.
    - intros v. rewrite pure_sep_holds emp_holds.
      eauto using in_labels_empty, out_edges_empty.
  Qed.

  Lemma holds_wand_insert v l P (Σ : gmap V L) :
    Σ !! v = None ->
    holds (own_out v l -∗ P) Σ ->
    holds P (<[v:=l]> Σ).
  Proof.
    intros Hd HH.
    replace (<[v:=l]> Σ) with (Σ ∪ {[ v := l ]}); last first.
    { apply map_eq. intro. rewrite lookup_union !lookup_insert_spec lookup_empty.
      sdec; destruct (Σ !! i); eauto; simplify_eq. }
    assert (holds (own_out v l) {[ v := l ]}).
    { rewrite own_holds. done. }
    pose proof (sep_combine _ _ _ _ HH H0).
    eapply holds_entails.
    { apply H1. solve_map_disjoint. }
    iIntros "[H1 H2]".
    iApply "H1". done.
  Qed.

  Lemma inv_exchange (v1 v2 : V) (f f' : V -> multiset L -> hProp V L) :
    (∀ v, Proper ((≡) ==> (⊣⊢)) (f v)) ->
    (∀ v, Proper ((≡) ==> (⊣⊢)) (f' v)) ->
    (∀ v x, v ≠ v1 ∧ v ≠ v2 -> f v x ⊢ f' v x) ->
    (∀ y, f v1 y ⊢ ∃ l,
      own_out v2 l ∗
      (∀ x,
        f v2 ({[ l ]} ⋅ x) -∗ ∃ l',
          (own_out v2 l' -∗ f' v1 y) ∗
          f' v2 ({[ l' ]} ⋅ x))) ->
    inv f -> inv f'.
  Proof.
    intros Hproperf Hproperf' Hrest Hexch Hinv.
    unfold inv in *.
    destruct Hinv as (g & Hwf & Hvs).
    pose proof (Hvs v1) as Hv1.
    specialize (Hexch (in_labels g v1)).
    eapply holds_entails in Hexch; last done.
    apply exists_holds in Hexch as (b & HH).
    apply sep_holds in HH as (Σ1 & Σ2 & HΣ12 & H1 & H2 & H3).
    apply own_holds in H2. subst.

    assert (out_edges g v1 !! v2 = Some b) as Hv1outv2. {
      rewrite HΣ12. rewrite lookup_union lookup_singleton.
      destruct (_ !! _); eauto.
    }

    pose proof (Hvs v2) as Hv2.
    assert (out_edges g v1 ##ₘ out_edges g v2) as Hdisj_out
      by eauto using edge_out_disjoint, some_edge.

    assert (Σ2 ##ₘ out_edges g v2) as Hdisj. {
      rewrite HΣ12 in Hdisj_out.
      solve_map_disjoint.
    }

    assert (∃ x, in_labels g v2 ≡ {[ b ]} ⋅ x) as [x Hx].
      by by eapply out_edges_in_labels.

    pose proof (sep_combine _ _ _ _ H3 Hv2 Hdisj) as Hcomb.
    eapply holds_entails in Hcomb. 2: {
      iIntros "[H1 H2]".
      rewrite Hx.
      iApply ("H1" with "H2").
    }

    apply exists_holds in Hcomb as [b' Hb].
    apply sep_holds in Hb as (Σ1' & Σ2' & HΣ12' & Hdisj' & H1' & H2').

    assert (v1 ≠ v2). {
      intros ->. specialize (Hdisj_out v2). by rewrite Hv1outv2 in Hdisj_out.
    }

    destruct (exchange_relabel g v1 v2 Σ1' Σ2' b b')
      as (g' & Hfw' & Hout1 & Hout2 & Hout' & Hin2 & Hin'); eauto.
    {
      rewrite HΣ12.
      rewrite delete_union.
      rewrite delete_singleton.
      rewrite left_id_L.
      rewrite delete_notin; last solve_map_disjoint.
      done.
    }
    exists g'.
    split_and!; eauto.
    intros v.
    destruct (decide (v = v1));
    destruct (decide (v = v2)); simplify_eq.
    - rewrite Hout1.
      specialize (Hin' _ n).
      eapply holds_wand_insert; eauto.
      {
        assert (Σ2 !! v2 = None) by solve_map_disjoint.
        assert (out_edges g v2 !! v2 = None).
        { eapply no_self_edge''. done. }
        assert ((Σ1' ∪ out_edges g' v2) !! v2 = None).
        { rewrite <-HΣ12'. rewrite lookup_union.
          rewrite H2 H4. done. }
        apply lookup_union_None in H5 as []. done.
      }
      eapply holds_entails; eauto.
      iIntros "H".
      rewrite Hin'. done.
    - eapply holds_entails; eauto.
      iIntros "H".
      specialize (Hin2 _ Hx).
      rewrite Hin2. done.
    - rewrite Hout'; eauto.
      eapply holds_entails; eauto.
      iIntros "H".
      rewrite Hin'; eauto.
      iApply Hrest; eauto.
  Qed.

  Lemma inv_dealloc (v1 v2 : V) (f f' : V -> multiset L -> hProp V L) :
    (∀ v, Proper ((≡) ==> (⊣⊢)) (f v)) ->
    (∀ v, Proper ((≡) ==> (⊣⊢)) (f' v)) ->
    (∀ v x, v ≠ v1 ∧ v ≠ v2 -> f v x ⊢ f' v x) ->
    (∀ y, f v1 y ⊢ ∃ l,
      own_out v2 l ∗
      (∀ x,
        f v2 ({[ l ]} ⋅ x) -∗
          f' v1 y ∗
          f' v2 x)) ->
    inv f -> inv f'.
  Proof.
    intros Hproperf Hproperf' Hrest Hexch Hinv.
    unfold inv in *.
    destruct Hinv as (g & Hwf & Hvs).
    pose proof (Hvs v1) as Hv1.
    specialize (Hexch (in_labels g v1)).
    eapply holds_entails in Hexch; last done.
    apply exists_holds in Hexch as (b & HH).
    apply sep_holds in HH as (Σ1 & Σ2 & HΣ12 & H1 & H2 & H3).
    apply own_holds in H2. subst.

    assert (out_edges g v1 !! v2 = Some b) as Hv1outv2. {
      rewrite HΣ12. rewrite lookup_union lookup_singleton.
      destruct (_ !! _); eauto.
    }

    pose proof (Hvs v2) as Hv2.
    assert (out_edges g v1 ##ₘ out_edges g v2) as Hdisj_out
      by eauto using edge_out_disjoint, some_edge.

    assert (Σ2 ##ₘ out_edges g v2) as Hdisj. {
      rewrite HΣ12 in Hdisj_out.
      solve_map_disjoint.
    }

    assert (∃ x, in_labels g v2 ≡ {[ b ]} ⋅ x) as [x Hx].
      by by eapply out_edges_in_labels.

    pose proof (sep_combine _ _ _ _ H3 Hv2 Hdisj) as Hcomb.
    eapply holds_entails in Hcomb. 2: {
      iIntros "[H1 H2]".
      rewrite Hx.
      iApply ("H1" with "H2").
    }

    apply sep_holds in Hcomb as (Σ1' & Σ2' & HΣ12' & Hdisj' & H1' & H2').

    assert (v1 ≠ v2). {
      intros ->. specialize (Hdisj_out v2). by rewrite Hv1outv2 in Hdisj_out.
    }

    assert (dealloc_valid g v1 v2 Σ1' Σ2'). {
      unfold dealloc_valid. split_and!.
      - eauto using some_edge.
      - solve_map_disjoint.
      - rewrite HΣ12.
        rewrite delete_union delete_singleton left_id_L.
        rewrite delete_notin; eauto.
        solve_map_disjoint.
    }

    exists (dealloc g v1 v2 Σ1' Σ2').
    split.
    - apply dealloc_wf; eauto.
    - intros v.
      erewrite dealloc_out_edges.
      setoid_rewrite dealloc_in_labels; eauto.
      repeat case_decide; simplify_eq; eauto.
      eapply holds_entails. 2: apply Hrest; naive_solver.
      eauto.
  Qed.

  Lemma mset_empty_to_L (x : multiset L) :
    x ≡ ε -> x = ε.
  Proof.
  Admitted.

  Lemma inv_alloc_l (v1 v2 : V) (f f' : V -> multiset L -> hProp V L) :
    v1 ≠ v2 ->
    (∀ v x, v ≠ v1 ∧ v ≠ v2 -> f v x ⊢ f' v x) ->
    (∀ x, f v2 x ⊢ ⌜⌜ x ≡ ε ⌝⌝) ->
    (∀ y, f v1 y ⊢
      ∃ l',
        (own_out v2 l' -∗ f' v1 y) ∗
        f' v2 {[ l' ]}) ->
    inv f -> inv f'.
  Proof.
    intros Hneq Hrest Hemp Hexch Hinv.
    unfold inv in *.
    destruct Hinv as (g & Hwf & Hvs).
    pose proof (Hvs v1) as Hv1.
    specialize (Hexch (in_labels g v1)).
    eapply holds_entails in Hexch; last done.
    apply exists_holds in Hexch as (b & HH).
    apply sep_holds in HH as (Σ1 & Σ2 & HΣ12 & H1 & H2 & H3).

    eapply holds_entails in Hemp; last eauto.
    eapply affinely_pure_holds in Hemp as [Hout Hin].

    assert (alloc_valid g v1 v2 Σ1 Σ2). {
      unfold alloc_valid. split_and!; eauto.
      - eauto using no_edges_no_uconn.
      - rewrite HΣ12 Hout right_id_L //.
    }

    exists (alloc g v1 v2 b Σ1 Σ2).
    split.
    - apply alloc_wf; eauto.
    - intros v.
      erewrite alloc_out_edges.
      setoid_rewrite alloc_in_labels; eauto.
      repeat case_decide; simplify_eq; eauto.
      + assert (in_labels g v2 = ε) as ->; eauto using mset_empty_to_L.
      + assert (holds (own_out v2 b) {[ v2 := b]}). { by rewrite own_holds. }
        eapply holds_entails. {
          eapply sep_combine; eauto.
          cut (Σ1 !! v2 = None); first solve_map_disjoint.
          cut (out_edges g v1 !! v2 = None). {
            rewrite HΣ12. rewrite lookup_union.
            by do 2 destruct (_ !! _).
          }
          eauto using no_in_labels_no_out_edge.
        }
        iIntros "[H1 H2]". iApply "H1". done.
      + eapply holds_entails. 2: apply Hrest; naive_solver. eauto.
  Qed.

  Lemma inv_alloc_r (v2 v3 : V) (f f' : V -> multiset L -> hProp V L) :
    v2 ≠ v3 ->
    (∀ v x, v ≠ v3 ∧ v ≠ v2 -> f v x ⊢ f' v x) ->
    (∀ x, f v3 x ⊢ ⌜⌜ x ≡ ε ⌝⌝) ->
    (∀ y, f v2 y ⊢
        ∃ l',
          (own_out v2 l' -∗ f' v3 ε) ∗
          f' v2 (y ⋅ {[ l' ]} )) ->
    inv f -> inv f'.
    Proof.
      intros Hneq Hrest Hemp Hexch Hinv.
      unfold inv in *.
      destruct Hinv as (g & Hwf & Hvs).
      pose proof (Hvs v2) as Hv2.
      specialize (Hexch (in_labels g v2)).
      eapply holds_entails in Hexch; last done.
      apply exists_holds in Hexch as (b & HH).
      apply sep_holds in HH as (Σ1 & Σ2 & HΣ12 & H1 & H2 & H3).

      eapply holds_entails in Hemp; last eauto.
      eapply affinely_pure_holds in Hemp as [Hout Hin].

      assert (alloc_valid g v3 v2 Σ1 Σ2). {
        unfold alloc_valid. split_and!; eauto.
        - intro HHH. symmetry in HHH. revert HHH.
          eapply no_edges_no_uconn; eauto.
        - rewrite HΣ12 Hout left_id_L //.
      }

      exists (alloc g v3 v2 b Σ1 Σ2).
      split.
      - apply alloc_wf; eauto.
      - intros v.
        erewrite alloc_out_edges.
        setoid_rewrite alloc_in_labels; eauto.
        repeat case_decide; simplify_eq; eauto.
        + replace ({[b]} ⋅ in_labels g v2) with (in_labels g v2 ⋅ {[b]}) by admit.
          eauto.
        + eapply mset_empty_to_L in Hin. rewrite Hin.
          assert (holds (own_out v2 b) {[ v2 := b]}). { by rewrite own_holds. }
          eapply holds_entails. {
            eapply sep_combine; eauto.
            cut (Σ1 !! v2 = None); first solve_map_disjoint.
            cut (out_edges g v2 !! v2 = None). {
              rewrite HΣ12. rewrite lookup_union.
              by do 2 destruct (_ !! _).
            }
            eauto using no_self_out_edge.
          }
          iIntros "[H1 H2]". iApply "H1". done.
        + eapply holds_entails. 2: apply Hrest; naive_solver. eauto.
  Admitted.

  Lemma inv_alloc_lr (v1 v2 v3 : V) (f f' : V -> multiset L -> hProp V L) :
    (∀ v, Proper ((≡) ==> (⊣⊢)) (f v)) ->
    v1 ≠ v2 ∧ v2 ≠ v3 ∧ v3 ≠ v1 ->
    (∀ v x, v ≠ v1 ∧ v ≠ v2 ∧ v ≠ v3 -> f v x ⊢ f' v x) ->
    (∀ x, f v2 x ⊢ ⌜⌜ x ≡ ε ⌝⌝) ->
    (∀ x, f v3 x ⊢ ⌜⌜ x ≡ ε ⌝⌝) ->
    (∀ y, f v1 y ⊢
      ∃ l1' l2',
        (own_out v2 l1' -∗ f' v1 y) ∗
        f' v2 ({[ l1' ]} ⋅ {[ l2' ]}) ∗
        (own_out v2 l2' -∗ f' v3 ε)) ->
    inv f -> inv f'.
  Proof.
    intros Hproper (Hneq1 & Hneq2 & Hneq3) Hrest H2 H3 H1 Hinv.
    assert (inv (λ v x,
      if decide (v = v1) then f' v1 x
      else if decide (v = v2) then ∃ l2', f' v2 (x ⋅ {[l2']}) ∗ (own_out v2 l2' -∗ f' v3 ε)
      else f v x))%I.
    - eapply (inv_insert_l v1 v2); last done; eauto.
      + intros. iIntros "H". repeat case_decide; naive_solver.
      + iIntros (y) "H".
        iDestruct (H1 with "H") as (l1' l2') "[H1 H2]".
        repeat case_decide; simplify_eq.
        iExists l1'. iFrame.
        iExists l2'. iFrame.
    - eapply (inv_insert_r v2 v3); last done.
      + intros. simpl. destruct H4.
        repeat case_decide; simplify_eq; eauto.
      + intros; simpl. repeat case_decide; simplify_eq; eauto.
      + intros. simpl.
        repeat case_decide; simplify_eq.
        iIntros "H".
        iDestruct "H" as (l2') "[H1 H2]".
        iExists _. iFrame.
  Qed.

End genericinv.