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
    inv (λ v x, ⌜⌜ x = ε ⌝⌝ ∗ emp)%I.
  Proof.
    exists ∅.
    split.
    - apply empty_wf.
    - intros v. rewrite pure_sep_holds emp_holds. split.
      + admit.
      + admit.
  Admitted.

  Lemma inv_exchange (v1 v2 : V) (f f' : V -> multiset L -> hProp V L) :
    (∀ v x, v ≠ v1 ∧ v ≠ v2 -> f v x ⊢ f' v x) ->
    (∀ y, f v1 y ⊢ ∃ l,
      own_out v2 l ∗
      (∀ x,
        f v2 ({[ l ]} ⋅ x) -∗ ∃ l',
          (own_out v2 l' -∗ f' v1 y) ∗
          f' v2 ({[ l' ]} ⋅ x))) ->
    inv f -> inv f'.
  Proof.
    intros Hrest Hexch Hinv.
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

    assert (∃ x, in_labels g v2 = {[ b ]} ⋅ x) as [x Hx].
    { admit. }
      (* by by eapply out_edges_in_labels. *)

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

    assert (exchange_valid g v1 v2 Σ1' Σ2'). {
      unfold exchange_valid. split_and!.
      - eauto using some_edge.
      - solve_map_disjoint.
      - rewrite HΣ12.
        rewrite delete_union delete_singleton left_id_L.
        rewrite delete_notin; eauto.
        solve_map_disjoint.
    }

    exists (exchange g v1 v2 b' Σ1' Σ2').
    split.
    - apply exchange_wf; eauto.
    - intros v.
      erewrite exchange_out_edges; erewrite exchange_in_labels; eauto; last by rewrite Hx.
      repeat case_decide; simplify_eq; eauto.
      + assert (holds (own_out v2 b') {[ v2 := b' ]}) as Hown
          by by apply own_holds.
        eapply holds_entails.
        * eapply sep_combine; eauto.
          assert (out_edges g v2 !! v2 = None). {
            specialize (Hdisj_out v2).
            rewrite Hv1outv2 in Hdisj_out.
            do 2 destruct (_ !! _); done.
          }
          assert (Σ1' ∪ Σ2' ##ₘ {[v2 := b']}); try solve_map_disjoint.
          rewrite <-HΣ12'. solve_map_disjoint.
        * iIntros "[H1 H2]". iApply "H1". done.
      + eapply holds_entails. 2: apply Hrest; naive_solver.
        eauto.
  Admitted.
End genericinv.