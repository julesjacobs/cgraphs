Require Export cgraphs.cgraphs.cgraph.
Require Export cgraphs.cgraphs.seplogic.

Section genericinv.
  Context {V : Type}.
  Context `{Countable V}.
  Context {L : ofe}.

  Definition inv (f : V -> multiset L -> hProp V L) : Prop :=
    ∃ g : cgraph V L, cgraph_wf g ∧
      ∀ v : V, holds (f v (in_labels g v)) (out_edges g v).

  Lemma adequacy f (φ : V -> multiset L -> gmap V L -> Prop)  :
    (∀ v, Proper ((≡) ==> (≡) ==> iff) (φ v)) ->
    inv f ->
    (∀ v x, f v x ⊢ ∃ Σ, ⌜⌜ φ v x Σ ⌝⌝ ∗ own Σ) ->
    ∃ g, cgraph_wf g ∧ ∀ v, φ v (in_labels g v) (out_edges g v).
  Proof.
    intros ? Hinv HH.
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
    apply own_holds in H2. rewrite ->H2 in H1. done.
  Qed.

  Lemma prim_simple_adequacy φ (P : hProp V L) Σ :
    holds P Σ -> (P ⊢ ⌜ φ ⌝) -> φ.
  Proof.
    intros HP Hφ.
    eapply holds_entails in HP; last eauto.
    eapply pure_holds; eauto.
  Qed.

  Lemma prim_empty_adequacy (P : hProp V L) Σ :
    holds P Σ -> (P ⊢ emp) -> Σ = ∅.
  Proof.
    intros HP HH.
    eapply holds_entails in HP; last eauto.
    eapply emp_holds in HP.
    by eapply map_empty_equiv_eq in HP.
  Qed.

  Lemma simple_adequacy v (φ : Prop) f :
    inv f -> (∀ x, f v x ⊢ ⌜ φ ⌝) -> φ.
  Proof.
    intros Hinv HH.
    destruct Hinv as (g & Hwf & H1).
    eapply prim_simple_adequacy; eauto.
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
    apply own_holds in H2.
    rewrite <-H2 in HΣ12.
    rewrite <-H2 in H1.
    clear H2.

    assert (out_edges g v1 !! v2 ≡ Some b) as Hv1outv2. {
      rewrite HΣ12. rewrite lookup_union lookup_singleton.
      destruct (_ !! _); eauto.
    }

    pose proof (Hvs v2) as Hv2.
    assert (out_edges g v1 ##ₘ out_edges g v2) as Hdisj_out.
      by eauto using edge_out_disjoint, some_edge.

    assert (Σ2 ##ₘ out_edges g v2) as Hdisj. {
      rewrite ->HΣ12 in Hdisj_out.
      solve_map_disjoint.
    }

    assert (∃ x, in_labels g v2 ≡ {[ b ]} ⋅ x) as [x Hx]
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
      intros ->. apply map_disjoint_self_empty in Hdisj_out.
      rewrite Hdisj_out lookup_empty in Hv1outv2. inversion Hv1outv2.
    }

    destruct (exchange_relabel_S g v1 v2 Σ1' Σ2' b b')
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
      rewrite Hin' //.
      eapply holds_wand_insert; eauto.
      simplify_map_eq.
      assert ((Σ1' ∪ Σ2') !! v2 ≡ None).
      {
        rewrite <-HΣ12'. rewrite lookup_union.
        rewrite H1.
        rewrite no_self_edge'' //.
      }
      inversion H2.
      symmetry in H5.
      apply lookup_union_None in H5 as []. done.
    - rewrite Hin2 // Hout2 //.
    - rewrite Hout' // Hin' //.
      eapply holds_entails; eauto.
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
    apply own_holds in H2.

    assert (out_edges g v1 !! v2 ≡ Some b) as Hv1outv2. {
      rewrite HΣ12. rewrite -H2. rewrite lookup_union lookup_singleton.
      destruct (_ !! _); eauto.
    }

    pose proof (Hvs v2) as Hv2.
    assert (out_edges g v1 ##ₘ out_edges g v2) as Hdisj_out
      by eauto using edge_out_disjoint, some_edge.

    assert (Σ2 ##ₘ out_edges g v2) as Hdisj. {
      rewrite ->HΣ12 in Hdisj_out.
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
      intros ->. specialize (Hdisj_out v2).
      eapply Some_equiv_eq in Hv1outv2 as (?&HH&?).
      rewrite HH in Hdisj_out. done.
    }

    edestruct (exchange_dealloc_S g v1 v2 Σ1' Σ2')
      as (g' & Hfw' & Hnuconn' & Hout1 & Hout2 & Hout' & Hin2 & Hin'); eauto.
    { rewrite HΣ12 -H2 delete_union delete_singleton left_id -HΣ12'.
      rewrite delete_notin; eauto.
      rewrite <-H2 in H1.
      solve_map_disjoint. }
    exists g'.
    split_and!; eauto.
    intros v.
    destruct (decide (v = v1));
    destruct (decide (v = v2)); simplify_eq.
    - rewrite Hin' // Hout1 //.
    - rewrite Hin2 // Hout2 //.
    - rewrite Hout' // Hin' //.
      eapply holds_entails; eauto.
  Qed.

  Lemma inv_alloc_l (v1 v2 : V) (f f' : V -> multiset L -> hProp V L) :
    (∀ v, Proper ((≡) ==> (⊣⊢)) (f v)) ->
    (∀ v, Proper ((≡) ==> (⊣⊢)) (f' v)) ->
    v1 ≠ v2 ->
    (∀ v x, v ≠ v1 ∧ v ≠ v2 -> f v x ⊢ f' v x) ->
    (∀ x, f v2 x ⊢ ⌜⌜ x ≡ ε ⌝⌝) ->
    (∀ y, f v1 y ⊢
      ∃ l',
        (own_out v2 l' -∗ f' v1 y) ∗
        f' v2 {[ l' ]}) ->
    inv f -> inv f'.
  Proof.
    intros Hproperf Hproperf' Hneq Hrest Hemp Hexch Hinv.
    unfold inv in *.
    destruct Hinv as (g & Hwf & Hvs).
    pose proof (Hvs v1) as Hv1.
    specialize (Hexch (in_labels g v1)).
    eapply holds_entails in Hexch; last done.
    apply exists_holds in Hexch as (b & HH).
    apply sep_holds in HH as (Σ1 & Σ2 & HΣ12 & H1 & H2 & H3).

    eapply holds_entails in Hemp; last eauto.
    eapply affinely_pure_holds in Hemp as [Hout Hin].

    destruct (exchange_alloc_S g v1 v2 Σ1 Σ2 b)
      as (g' & Hwf' & Hout1 & Hout2 & Hout' & Hin2 & Hin'); eauto.
    { intros H0. apply no_edges_no_uconn in H0; eauto.
      apply map_empty_equiv_eq in Hout. done. }
    { rewrite HΣ12 Hout right_id_L //. }
    exists g'. split; eauto.
    intros v.
    destruct (decide (v = v1));
    destruct (decide (v = v2)); simplify_eq.
    - rewrite Hout1 Hin' //.
      eapply holds_wand_insert; eauto.
      assert ((Σ1 ∪ out_edges g' v2) !! v2 ≡ None).
      {
        rewrite Hout2. rewrite <-HΣ12.
        destruct (out_edges g v1 !! v2) eqn:E; eauto.
        exfalso.
        eapply out_edges_in_labels_L in E as [].
        rewrite ->Hin in H0.
        apply symmetry in H0.
        eapply multiset_empty_mult in H0 as [].
        eapply multiset_empty_neq_singleton; eauto.
      }
      inversion H0. symmetry in H5.
      apply lookup_union_None in H5 as [].
      done.
    - rewrite Hin2 Hin right_id Hout2 //.
    - rewrite Hout' // Hin' //.
      eapply holds_entails; eauto.
  Qed.

  Lemma inv_alloc_r (v2 v3 : V) (f f' : V -> multiset L -> hProp V L) :
    (∀ v, Proper ((≡) ==> (⊣⊢)) (f v)) ->
    (∀ v, Proper ((≡) ==> (⊣⊢)) (f' v)) ->
    v2 ≠ v3 ->
    (∀ v x, v ≠ v3 ∧ v ≠ v2 -> f v x ⊢ f' v x) ->
    (∀ x, f v3 x ⊢ ⌜⌜ x ≡ ε ⌝⌝) ->
    (∀ y, f v2 y ⊢
        ∃ l',
          (own_out v2 l' -∗ f' v3 ε) ∗
          f' v2 (y ⋅ {[ l' ]} )) ->
    inv f -> inv f'.
  Proof.
    intros Hproperf Hproperf' Hneq Hrest Hemp Hexch Hinv.
    unfold inv in *.
    destruct Hinv as (g & Hwf & Hvs).
    pose proof (Hvs v2) as Hv2.
    specialize (Hexch (in_labels g v2)).
    eapply holds_entails in Hexch; last done.
    apply exists_holds in Hexch as (b & HH).
    apply sep_holds in HH as (Σ1 & Σ2 & HΣ12 & H1 & H2 & H3).

    eapply holds_entails in Hemp; last eauto.
    eapply affinely_pure_holds in Hemp as [Hout Hin].

    destruct (exchange_alloc_S g v3 v2 Σ1 Σ2 b)
      as (g' & Hwf' & Hout1 & Hout2 & Hout' & Hin2 & Hin'); eauto.
    { intros H0. symmetry in H0. apply no_edges_no_uconn in H0; eauto.
      apply map_empty_equiv_eq in Hout. done. }
    { rewrite HΣ12 Hout left_id_L map_union_comm;eauto. }
    exists g'. split; eauto.
    intros v.
    destruct (decide (v = v3));
    destruct (decide (v = v2)); simplify_eq.
    - rewrite Hout1 Hin' // Hin.
      eapply holds_wand_insert; eauto.
      assert ((Σ1 ∪ out_edges g' v2) !! v2 ≡ None).
      {
        rewrite Hout2.
        rewrite <-HΣ12.
        rewrite no_self_edge''; eauto.
      }
      inversion H0. symmetry in H5.
      apply lookup_union_None in H5 as [].
      done.
    - rewrite Hin2 Hout2 comm //.
    - rewrite Hout' // Hin' //.
      eapply holds_entails; eauto.
  Qed.

  (* Situation [v1 -[l1]-> v2, v3] to
     situation [v1 -[l2]-> v2, v3 -[l']-> v2] *)
  (* Need to transfer resources from v1 to v3,
     for lexical scoping of fork. *)
  Lemma inv_exchange_alloc (v1 v2 v3 : V) (f f' : V -> multiset L -> hProp V L) :
    (∀ v, Proper ((≡) ==> (⊣⊢)) (f v)) ->
    (∀ v, Proper ((≡) ==> (⊣⊢)) (f' v)) ->
    v1 ≠ v2 ∧ v1 ≠ v3 ∧ v2 ≠ v3 -> (* Some of these are unnecessary, implied by existence of edges *)
    (∀ v x, v ≠ v1 ∧ v ≠ v2 ∧ v ≠ v3 -> f v x ⊢ f' v x) ->
    (∀ x, f v3 x ⊢ ⌜⌜ x ≡ ε ⌝⌝) ->
    (∀ y, f v1 y ⊢ ∃ l,
      own_out v2 l ∗
      (∀ x,
        f v2 ({[ l ]} ⋅ x) -∗ ∃ l' l'',
          (own_out v2 l' -∗ f' v1 y) ∗
          f' v2 ({[ l' ]} ⋅ {[ l'' ]} ⋅ x) ∗
          (own_out v2 l'' -∗ f' v3 ε))) ->
    inv f -> inv f'.
  Proof.
    intros Hproper Hproper' [Hneq1 [Hneq2 Hneq3]] Hrest Hnew HH Hinv.
    (*
       We first transfer resources from v1 to v2 using the exchange rule.
       Then v2 will transfer them to v3.
       Because v3 is fresh there are no resources to be transfered
       from v3 to v1 or v2 (unlike in the barriers case).
       We also update the edge from v1 to v2 to its final state.
       After this, the remaining work should be done by the alloc rule.
       So after the first step, we should already have the final state at v1.
    *)
    set q := (λ v x,
      if decide (v = v1) then f' v1 x
      else if decide (v = v2) then
        ∃ l', f' v2 ({[ l' ]} ⋅ x) ∗ (own_out v2 l' -∗ f' v3 ε)
      else f v x)%I.
    assert (inv q) as Hinvmid; subst q.
    + eapply (inv_exchange v1 v2); last done; first apply _.
      - solve_proper.
      - intros. repeat case_decide; naive_solver.
      - iIntros (y) "H".
        iDestruct (HH with "H") as "H".
        iDestruct "H" as (l) "[Hown H]".
        iExists _. iFrame. iIntros (x) "H2".
        iDestruct ("H" with "H2") as (l' l'') "[H1 [H2 H3]]".
        iExists _.
        repeat case_decide; simplify_eq. iFrame.
        iExists l''. iFrame.
        rewrite assoc.
        assert ({[l']} ⋅ {[l'']} ≡@{multiset L} {[l'']} ⋅ {[l']}) as HC by rewrite comm //.
        rewrite HC //.
    + clear Hinv.
      eapply (inv_alloc_r v2 v3); last done.
      - solve_proper.
      - solve_proper.
      - done.
      - iIntros (v x []) "H".
        repeat case_decide; simplify_eq; eauto.
        iApply Hrest; eauto.
      - iIntros (x) "H".
        repeat case_decide; simplify_eq.
        by iApply Hnew.
      - iIntros (x) "H".
        repeat case_decide; simplify_eq.
        iDestruct "H" as (l') "[H1 H2]".
        iExists _. iFrame. rewrite comm //.
  Qed.

  Lemma inv_alloc_lr (v1 v2 v3 : V) (f f' : V -> multiset L -> hProp V L) :
    (∀ v, Proper ((≡) ==> (⊣⊢)) (f v)) ->
    (∀ v, Proper ((≡) ==> (⊣⊢)) (f' v)) ->
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
    intros Hproper Hproper' (Hneq1 & Hneq2 & Hneq3) Hrest H2 H3 H1 Hinv.
    set q := (λ v x,
      if decide (v = v1) then f' v1 x
      else if decide (v = v2) then ∃ l2', f' v2 (x ⋅ {[l2']}) ∗ (own_out v2 l2' -∗ f' v3 ε)
      else f v x)%I.
    assert (inv q); subst q.
    - eapply (inv_alloc_l v1 v2); last done; eauto.
      + solve_proper.
      + intros. iIntros "H". repeat case_decide; naive_solver.
      + iIntros (y) "H".
        iDestruct (H1 with "H") as (l1' l2') "[H1 H2]".
        repeat case_decide; simplify_eq.
        iExists l1'. iFrame.
        iExists l2'. iFrame.
    - eapply (inv_alloc_r v2 v3); last done.
      + solve_proper.
      + apply _.
      + intros; simpl. repeat case_decide; simplify_eq; eauto.
      + intros ? ? []. simpl.
        repeat case_decide; simplify_eq; eauto.
      + intros. simpl. sdec. eauto.
      + intros. simpl. sdec.
        iIntros "H".
        iDestruct "H" as (?) "[H1 H2]".
        eauto with iFrame.
  Qed.

  Lemma big_sepS_set_map `{Countable A, Countable B}
      (P : B -> hProp V L) (f : A -> B) (s : gset A) :
    Inj eq eq f ->
    ([∗ set] x ∈ set_map f s, P x) ⊢
    [∗ set] x ∈ s, P (f x).
  Proof.
    intros Hinj.
    induction s using set_ind_L.
    - rewrite !set_map_empty. eauto.
    - rewrite set_map_union_L set_map_singleton_L.
      rewrite big_sepS_delete; last first.
      { rewrite elem_of_union. left. by apply elem_of_singleton. }
      iIntros "H".
      iApply big_sepS_delete.
      { rewrite elem_of_union. left. by apply elem_of_singleton. }
      iDestruct "H" as "[? H]". iFrame.
      assert (({[x]} ∪ X) ∖ {[x]} = X) as -> by set_solver.
      assert ((({[f x]} ∪ set_map f X) ∖ {[f x]}) = set_map f X) as -> by set_solver.
      iApply IHs. done.
  Qed.

  Lemma big_sepS_incr n (P : fin (S n) -> hProp V L) :
    ([∗ set] i ∈ (all_fin (S n) ∖ {[0%fin]}), P i) ⊢
    [∗ set] i ∈ all_fin n, P (FS i).
  Proof.
    assert (all_fin (S n) ∖ {[0%fin]} = set_map FS (all_fin n)) as ->.
    { apply set_eq. intro.
      rewrite elem_of_difference elem_of_singleton elem_of_map.
      inv_fin x; naive_solver (eauto using all_fin_all). }
    eapply big_sepS_set_map. apply _.
  Qed.

  Lemma inv_alloc_rs (v1 : V) (n : nat)
    (fv : fin n -> V)
    (P P' : V -> multiset L -> hProp V L) :
    (∀ v, Proper ((≡) ==> (⊣⊢)) (P v)) ->
    (∀ v, Proper ((≡) ==> (⊣⊢)) (P' v)) ->
    Inj eq eq fv ->
    (∀ i, fv i ≠ v1) ->
    (∀ v x, v ≠ v1 ∧ (∀ i, v ≠ fv i) -> P v x ⊢ P' v x) ->
    (∀ i x, P (fv i) x ⊢ ⌜⌜ x ≡ ε ⌝⌝) ->
    (∀ y, P v1 y ⊢
      ∃ fl : fin n -> L,
        P' v1 (y ⋅ fin_multiset n fl) ∗
        ([∗ set] i ∈ all_fin n, own_out v1 (fl i) -∗ P' (fv i) ε)) ->
    inv P -> inv P'.
  Proof.
    revert fv P P'. induction n; intros.
    {
      eapply inv_impl; last done. intros.
      iIntros "H". destruct (decide (v = v1)); subst.
      + iDestruct (H6 with "H") as (fl) "[H1 H2]".
        rewrite /all_fin fin_gset_0 fin_multiset_0 right_id. iFrame.
      + iApply H4; last done.
        split; eauto. intros. inversion i.
    }
    (* Now we have the induction hypothesis *)
    set q := (λ v x,
      if decide (v = v1) then
        ∃ l : L, P' v (x ⋅ {[ l ]}) ∗ (own_out v1 l -∗ P' (fv 0%fin) ε)
      else if decide (v = fv 0%fin) then
        P v x
      else
        P' v x)%I.
    assert (inv q); subst q.
    - eapply (IHn (fv ∘ FS)); last done.
      + solve_proper.
      + solve_proper.
      + eapply compose_inj; eauto. apply _.
      + eauto.
      + iIntros (v x []) "H". sdec; eauto.
        iApply H4; last done. split; eauto. intros ??. subst.
        inv_fin i; intros; simplify_eq.
        eapply H9. eauto.
      + eauto.
      + iIntros (y) "H". sdec.
        iDestruct (H6 with "H") as (fl) "[H1 H2]".
        iExists (fl ∘ FS).
        assert (0%fin ∈ all_fin (S n)) by apply all_fin_all.
        rewrite big_sepS_delete; last done.
        iDestruct "H2" as "[H2 H3]".
        iSplitL "H1 H2".
        { iExists _. iFrame.
          rewrite fin_multiset_S.
          rewrite (comm (⋅) {[fl 0%fin]}) assoc //. }
        rewrite big_sepS_incr.
        iApply (big_sepS_impl with "H3").
        iModIntro. iIntros (x Hx).
        sdec; [exfalso;naive_solver..|].
        simpl. iIntros "H". eauto.
    - eapply (inv_alloc_r v1 (fv 0%fin)); last done; simpl.
      + solve_proper.
      + solve_proper.
      + naive_solver.
      + iIntros (v x []) "H". by sdec.
      + iIntros (x) "H".
        sdec; first naive_solver.
        iApply H5. eauto.
      + iIntros (y) "H".
        sdec. iDestruct "H" as (l) "[H1 H2]".
        eauto with iFrame.
  Qed.

  Lemma fin_dec n v (fv : fin n -> V) : Decision (∃ i, v = fv i).
  Proof.
    induction n.
    - right. intro. destruct H0. inversion x.
    - destruct (IHn (fv ∘ FS)) as [Hi|Hni].
      + left. destruct Hi. eauto.
      + destruct (decide (fv 0%fin = v)). subst.
        * left. eauto.
        * right. intros [i Hi].
          subst.
          inv_fin i; intros; simplify_eq.
          eapply Hni. eauto.
  Qed.

  Lemma inv_alloc_lrs (v1 v2 : V) (n : nat)
    (fv : fin n -> V)
    (P P' : V -> multiset L -> hProp V L) :
    (∀ v, Proper ((≡) ==> (⊣⊢)) (P v)) ->
    (∀ v, Proper ((≡) ==> (⊣⊢)) (P' v)) ->
    Inj eq eq fv ->
    v1 ≠ v2 ∧ (∀ i, fv i ≠ v1 ∧ fv i ≠ v2) ->
    (∀ v x, v ≠ v1 ∧ v ≠ v2 ∧ (∀ i, v ≠ fv i) -> P v x ⊢ P' v x) ->
    (∀ x, P v2 x ⊢ ⌜⌜ x ≡ ε ⌝⌝) ->
    (∀ i x, P (fv i) x ⊢ ⌜⌜ x ≡ ε ⌝⌝) ->
    (∀ y, P v1 y ⊢
      ∃ (l : L) (fl : fin n -> L),
        (own_out v2 l -∗ P' v1 y) ∗
        P' v2 ({[ l ]} ⋅ fin_multiset n fl) ∗
        ([∗ set] i ∈ all_fin n, own_out v2 (fl i) -∗ P' (fv i) ε)) ->
    inv P -> inv P'.
  Proof.
    intros Hproper Hproper' Hinj (Hneq1 & Hneq2) Hrest H2 H3 H1 Hinv.
    set q := (λ v x,
        if decide (v = v1) then P' v1 x
        else if decide (v = v2) then
          ∃ (fl : fin n -> L), P' v2 (x ⋅ fin_multiset n fl) ∗
            ([∗ set] i ∈ all_fin n, own_out v2 (fl i) -∗ P' (fv i) ε)
        else if fin_dec n v fv then ⌜⌜ x ≡ ε ⌝⌝ else P' v x)%I.
    assert (inv q); subst q.
    - eapply (inv_alloc_l v1 v2); last done; eauto.
      + solve_proper.
      + intros ?? []. iIntros "H". sdec.
        destruct (fin_dec n v fv) as [[? ->]|].
        { by iApply H3. }
        iApply Hrest; naive_solver.
      + iIntros (y) "H".
        iDestruct (H1 with "H") as (l fl) "[H1 [H2 H3]]".
        iExists l.
        sdec. eauto with iFrame.
    - eapply (inv_alloc_rs v2 n fv); last done.
      + solve_proper.
      + solve_proper.
      + intros; simpl. sdec. eauto.
      + naive_solver.
      + intros. simpl. destruct H4. sdec; first done.
        destruct (fin_dec n v fv) as [[? ->]|]; naive_solver.
      + intros. simpl. sdec.
        * naive_solver.
        * naive_solver.
        * destruct (fin_dec n (fv i) fv) as [[]|]; naive_solver.
      + intros. simpl. sdec. eauto.
  Qed.

End genericinv.