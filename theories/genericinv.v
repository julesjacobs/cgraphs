Require Export diris.cgraph.
Require Export diris.seplogic.

Section genericinv.
  Context {V : Type}.
  Context `{Countable V}.
  Context {L : Type}.

  (* Definition inv (g : cgraph V L) (f : V -> list L -> hProp V L) (h : V -> Prop) : Prop :=
      cgraph_wf g ∧ ∀ v : V,
      (v ∈ vertices g -> holds (f v (in_labels g v)) (out_edges g v)) ∧
      (v ∉ vertices g -> h v). *)

  Definition inv (f : gmap V (list L -> hProp V L)) : Prop :=
    ∃ g : cgraph V L, cgraph_wf g ∧ ∀ v : V,
      (v ∈ vertices g -> ∃ Q, f !! v = Some Q ∧ holds (Q (in_labels g v)) (out_edges g v)) ∧
      (v ∉ vertices g -> f !! v = None).

  Definition local_impl (q q' : option (list L -> hProp V L)) : Prop :=
    match q,q' with
    | None,None => True
    | Some P,Some P' => ∀ ins, P ins ⊢ P' ins
    | _,_ => False
    end.

  Lemma local_impl_refl X :
    local_impl X X.
  Proof.
    destruct X; simpl; eauto.
  Qed.

  Lemma inv_impl f f' :
    (∀ v, local_impl (f !! v) (f' !! v)) ->
    inv f -> inv f'.
  Proof.
    intros Himpl (g & Hg & HH).
    exists g. split; first done.
    intros v. specialize (HH v) as [H1 H2]. specialize (Himpl v).
    split.
    - intros Hv. destruct H1 as (Q & HQ1 & HQ2); first done.
      rewrite HQ1 in Himpl. simpl in *.
      destruct (f' !! v); try done.
      eexists. split; first done.
      eapply holds_entails; eauto.
    - intros Hv. rewrite H2 in Himpl; try done.
      simpl in *. destruct (f' !! v); done.
  Qed.

  Lemma inv_init :
    inv ∅.
  Proof.
    exists ∅.
    split.
    - apply empty_wf.
    - set_solver.
  Qed.

  Lemma inv_singleton v (P : list L -> hProp V L) :
    holds (P []) ∅ ->
    inv {[ v := P ]}.
  Proof.
    intros HH.
    exists {[ v := ∅ ]}. split.
    - admit. (* well formedness of graph *)
    - intros v'. split.
      + intros Hv. rewrite /vertices in Hv.
        assert (v' = v) by set_solver. subst.
        exists P. rewrite lookup_singleton.
        split; first done.
        assert (in_labels ({[v := ∅]} : gmap V (gmap V L)) v = []) as HH1 by admit. (* lemma about in_labels *)
        rewrite /out_edges. rewrite lookup_singleton. rewrite HH1. eauto.
      + rewrite /vertices. intros.
        assert (v' ≠ v); first set_solver.
        rewrite lookup_singleton_ne //.
  Admitted.

  Lemma inv_delete_vertex f (v : V) :
    (∀ Q i, f !! v = Some Q -> Q i ⊢ ⌜⌜ i = [] ⌝⌝) ->
    inv f ->
    inv (delete v f).
  Proof.
    intros HH'.
    destruct (f !! v) as [Q|] eqn:Hv; last first.
    rewrite delete_notin; eauto.
    specialize (HH' Q).
    assert (∀ i : list L, Q i -∗ ⌜⌜ i = [] ⌝⌝) as HH by set_solver.
    clear HH'.
    intros Hinv.
    unfold inv in *.
    destruct Hinv as (g & Hwf & Hg).
    pose proof (Hg v) as [Hgv1 Hgv2].
    destruct Hgv1 as (Qv & HQv1 & HQv2). { rewrite Hv in Hgv2. set_solver. }
    rewrite HQv1 in Hv.
    simplify_eq.
    eapply holds_entails in HQv2; last eauto.
    eapply affinely_pure_holds in HQv2 as [].
    exists (delete v g).
    split.
    - admit. (* well formedness of graph *)
    - intros v'.
      split.
      + intros Hv'. pose proof (Hg v') as [Hg1 Hg2].
        destruct Hg1 as (Q' & HQ'1 & HQ'2); first set_solver.
        exists Q'. split.
        * rewrite lookup_delete_ne; last set_solver. done.
        * assert (v ≠ v') by set_solver.
          assert (in_labels (delete v g) v' = in_labels g v') as -> by admit. (* lemma about in_labels *)
          assert (out_edges (delete v g) v' = out_edges g v') as -> by admit. (* lemma about in_labels *)
          done.
      + intros Hv'.
        destruct (decide (v = v')).
        * subst. apply lookup_delete.
        * assert (v' ∉ vertices g) by set_solver.
          rewrite lookup_delete_ne; eauto.
          set_solver.
  Admitted.

  (* Lemma inv_relabel f (P1 P1' Q Q' : list L -> hProp V L) v1 v2 l l' :
    f !! v1 = Some (λ i, P1 i ∗ own1 v2 l)%I ->
    f !! v2 = Some Q ->
    (∀ i, P1 i ⊢ P1' i) ->
    (∀ i, Q (l :: i) ⊢ Q' (l' :: i)) ->
    inv f ->
    inv (<[ v1 := (λ i, P1' i ∗ own1 v2 l')%I ]> $ <[ v2 := Q' ]> f).
  Proof. Admitted. *)

  Lemma inv_exchange f (P1 P1' Q Q' : list L -> hProp V L) v1 v2 l l' :
    f !! v1 = Some (λ i, P1 i ∗ own1 v2 l)%I ->
    f !! v2 = Some Q ->
    (∀ i1 i2, P1 i1 ∗ Q (l :: i2) ⊢ P1' i1 ∗ Q' (l' :: i2)) ->
    inv f ->
    inv (<[ v1 := (λ i, P1' i ∗ own1 v2 l')%I ]> $ <[ v2 := Q' ]> f).
  Proof.
    intros Hv1 Hv2 Himpl Hinv.
    unfold inv in *.
    destruct Hinv as (g & Hgwf & Hg).
    pose proof (Hg v1) as [Hgv1 Hgv1'].
    pose proof (Hg v2) as [Hgv2 Hgv2'].
    destruct Hgv1 as (Q1 & HQ1 & HQ1').
    { unfold vertices in *. rewrite Hv1 in Hgv1'. set_solver. }
    rewrite HQ1 in Hv1. simplify_eq.
    destruct Hgv2 as (Q2 & HQ2 & HQ2').
    { unfold vertices in *. rewrite Hv2 in Hgv2'. set_solver. }
    rewrite HQ2 in Hv2. simplify_eq.
    clear Hgv1' Hgv2'.
    apply sep_holds in HQ1' as (Σ1 & Σ2 & HΣ12eq & HΣ12disj & HΣ1 & HΣ2).
    apply own1_holds in HΣ2. subst.
    assert (l ∈ in_labels g v2) as Htmp. { admit. } (* lemma about in_labels *)
    eapply elem_of_Permutation in Htmp as [ls Hls].
    assert (holds (Q (l :: ls)) (out_edges g v2)) as HQ2''. { admit. } (* Need Proper for Q under permutations *)
    assert ({[ v2 := l ]} ##ₘ out_edges g v2) as Hdisj. { admit. } (* disjointness of connected vertices *)
    assert (Σ1 ##ₘ out_edges g v2) as Htmp. { admit. } (* disjointness of connected vertices *)
    pose proof (sep_combine _ _ _ _ HΣ1 HQ2'' Htmp) as HPQ. clear Htmp.
    eapply holds_entails in HPQ; last by eauto.
    eapply sep_holds in HPQ as (Σ2 & Σ3 & H23eq & H23disj & HΣ2 & HΣ3).
    (* Now we can instantiate the existential *)
    exists (<[ v1 := Σ2 ∪ {[ v2 := l' ]}]> $ <[ v2 := Σ3 ]> g).
    split.
    - admit. (* well formedness of graph *)
    - intros v. split.
      + intros Hv.
        destruct (decide (v = v1)); subst.
        {
          eexists.
          rewrite !lookup_insert_spec.
          repeat case_decide; simplify_eq.
          split; first done.
          rewrite /out_edges. rewrite lookup_insert.
          assert (in_labels (<[v1:=Σ2 ∪ {[v2 := l']}]> (<[v2:=Σ3]> g)) v1 = in_labels g v1) as Htmp.
          { admit. } (* lemma about in_labels *)
          rewrite Htmp. clear Htmp.
          rewrite sep_holds. eexists _,_.
          split; first done.
          split. {
            assert ({[ v2 := l ]} ##ₘ (Σ1 ∪ out_edges g v2)) as Htmp by solve_map_disjoint.
            rewrite H23eq in Htmp.
            solve_map_disjoint.
          }
          split; eauto.
          rewrite own_holds. done.
        }
        destruct (decide (v = v2)); subst.
        {
          eexists.
          rewrite !lookup_insert_spec.
          repeat case_decide; simplify_eq.
          split; first done.
          rewrite /out_edges. rewrite !lookup_insert_spec.
          repeat case_decide; simplify_eq.
          assert (in_labels (<[v1:=Σ2 ∪ {[v2 := l']}]> (<[v2:=Σ3]> g)) v2 = l' :: ls) as Htmp.
          { admit. } (* lemma about in_labels *)
          rewrite Htmp. clear Htmp. done.
        }
        {
          specialize (Hg v) as [Hg1 Hg2].
          destruct Hg1 as (Q2 & HQ2s & HQ2h). { unfold vertices in *. set_solver. }
          eexists.
          rewrite !lookup_insert_spec. repeat case_decide; simplify_eq.
          split; eauto.
          rewrite /out_edges. rewrite !lookup_insert_spec.
          repeat case_decide; simplify_eq.
          assert (in_labels (<[v1:=Σ2 ∪ {[v2 := l']}]> (<[v2:=Σ3]> g)) v = in_labels g v) as ->.
          { admit. } (* lemma about in_labels *)
          done.
        }
      + intros Hv.
        rewrite !lookup_insert_spec.
        unfold vertices in *.
        repeat case_decide; set_solver.
  Admitted.

  (* This version of the lemma is more convenient because unification can help us apply it *)
  Lemma inv_exchange' f (P P' Q Q' P1 P1' : list L -> hProp V L) v1 v2 l l' :
    f !! v1 = Some P ->
    f !! v2 = Some Q ->
    (∀ i, P i ⊢ P1 i ∗ own1 v2 l) ->
    (∀ i1 i2, P1 i1 ∗ Q (l :: i2) ⊢ P1' i1 ∗ Q' (l' :: i2)) ->
    (∀ i, P1' i ∗ own1 v2 l' ⊢ P' i) ->
    inv f ->
    inv (<[ v1 := P' ]> $ <[ v2 := Q' ]> f).
  Proof.
    intros.
    eapply (inv_impl _ (<[ v1 := (λ i, P1 i ∗ own1 v2 l)%I ]> f)) in H5.
    - eapply inv_impl; last first.
      + eapply inv_exchange in H5; eauto.
        * eapply lookup_insert.
        * rewrite lookup_insert_ne; eauto.
          admit. (* This goal v1 ≠ v2 follows from acyclicity and the fact that v1 owns v2, but we can also add it as a premise.
                    In our use case, v1 ≠ v2 is easy to establish because v1 is a thread and v2 is a chanel. *)
      + intros v. rewrite !lookup_insert_spec.
        repeat case_decide; subst; eauto using local_impl_refl.
    - intros v. rewrite !lookup_insert_spec.
      repeat case_decide; subst; rewrite ?H0; eauto using local_impl_refl.
  Admitted.

  (* Special case of the previous lemma where we only change the label and don't exchange resources. *)
  Lemma inv_relabel f (P P' Q Q' P1 : list L -> hProp V L) v1 v2 l l' :
    f !! v1 = Some P ->
    f !! v2 = Some Q ->
    (∀ i, P i ⊢ P1 i ∗ own1 v2 l) ->
    (∀ i, Q (l :: i) ⊢ Q' (l' :: i)) ->
    (∀ i, P1 i ∗ own1 v2 l' ⊢ P' i) ->
    inv f ->
    inv (<[ v1 := P' ]> $ <[ v2 := Q' ]> f).
  Proof.
    intros.
    eapply inv_exchange'; eauto.
    intros. iIntros "[A B]". iFrame.
    by iApply H3.
  Qed.


  Lemma inv_alloc1 (f : gmap V (list L -> hProp V L)) (P P' Q : list L -> hProp V L) (v1 v2 : V) (l : L) :
    f !! v1 = Some P ->
    f !! v2 = None ->
    (∀ i, P i ∗ own1 v2 l ⊢ P' i) ->
    (emp ⊢ Q [l]) ->
    inv f ->
    inv (<[ v1 := P' ]> $ <[ v2 := Q ]> f).
  Proof.
  Admitted.

  Lemma inv_alloc2 (f : gmap V (list L -> hProp V L)) (P P' Q : list L -> hProp V L) (v1 v2 : V) (l : L) :
    f !! v1 = Some P ->
    f !! v2 = None ->
    (∀ i, P i ⊢ P' (l :: i)) ->
    (own1 v1 l ⊢ Q []) ->
    inv f ->
    inv (<[ v1 := P' ]> $ <[ v2 := Q ]> f).
  Proof.
  Admitted.

  Lemma inv_alloc12 (f : gmap V (list L -> hProp V L)) (P P' Q R : list L -> hProp V L) (v1 v2 v3 : V) (l l' : L) :
    f !! v1 = Some P ->
    f !! v2 = None ->
    f !! v3 = None ->
    v2 ≠ v3 ->
    (∀ i, P i ∗ own1 v2 l ⊢ P' i) ->
    (emp ⊢ Q [l;l']) ->
    (own1 v2 l ⊢ R []) ->
    inv f ->
    inv (<[ v1 := P' ]> $ <[ v2 := Q ]> $ <[ v3 := R ]> f).
  Proof.
    intros.
  Admitted.

  Lemma inv_alloc12_move : True. Admitted.

End genericinv.