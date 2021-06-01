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

      (* own_in l
      own_out v l

      hProp V L := list L -> gmap V L -> Prop
      f : V -> (list L -> gmap V L -> Prop)
      f (Thread i) inlabels :=
        match es !! i with
        | Some e => ⌜⌜ inlabels = [] ⌝⌝ ∗ rtyped0 e UnitT
        | None => ⌜⌜ inlabels = [] ⌝⌝
        end
      f (Chan i) inlabels :=
        match h !! (i,true), h !! (i,false) with
        | Some b1, Some b2 => ??
        | Some b1, None | None, Some b1 => ??
        | None, None => ⌜⌜ inlabels = [] ⌝⌝
        end. *)

  Definition inv (f : V -> multiset L -> hProp V L) : Prop :=
    ∃ g : cgraph V L, cgraph_wf g ∧
      ∀ v : V, holds (f v (in_labels g v)) (out_edges g v).

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
  Admitted.
(*
  Lemma inv_exchange {v1 v2 l l'} {P1 P2 P1' P2' H1 H2 : hProp V L} {f f' : V -> hProp V L} :
    (∀ v, v ≠ v1 -> v ≠ v2 -> f v ⊢ f' v) ->
    (f v1 ⊢ ∃ l P1, own_out v2 l ∗ H1 ∗ (in_emp P1) ∗
              (□ (f v2 -∗ own_in l) -∗
                □ (P1 ∗ P2 -∗ P1' ∗ P2') ∗
                □ (own_out v2 l' ∗ H1 ∗ (in_emp P1') -∗ f' v1) ∗
                □ (own_in l' ∗ H2 ∗ (in_emp P2') -∗ f' v2)
                ->                   (*  ∗ H2 ∗ (in_emp P2)) *)
    (f v2 ⊢ own_in l ∗ H2 ∗ (in_emp P2)) ->
    (P1 ∗ P2 ⊢ P1' ∗ P2') ->
    (own_out v2 l' ∗ H1 ∗ (in_emp P1') ⊢ f' v1) ->
    (own_in l' ∗ H2 ∗ (in_emp P2') ⊢ f' v2) ->
    inv f -> inv f'.
  Proof.
    intros Himp Hsplit1 Hsplit2 Hexch Hcomb1 Hcomb2 Hinv.
  Admitted.

  Lemma inv_delete v1 v2 l (H1 H2 : hProp V L) (f f' : V -> hProp V L) :
    (∀ v, v ≠ v1 -> v ≠ v2 -> f v ⊢ f' v) ->
    (f v1 ⊢ own_out v2 l ∗ H1) ->
    (f v2 ⊢ own_in l ∗ H2) ->
    (H1 ⊢ f' v1) ->
    (H2 ⊢ f' v2) ->
    inv f -> inv f'.
  Proof.
  Admitted.

  Lemma inv_create1 {v1 v2 l} (f f' : V -> hProp V L) :
    v1 ≠ v2 ->
    (∀ v, v ≠ v1 -> v ≠ v2 -> f v ⊢ f' v) ->
    (f v2 ⊢ emp) ->
    (f v1 ∗ own_out v2 l ⊢ f' v1) ->
    (own_in l ⊢ f' v2) ->
    inv f -> inv f'.
  Proof.
  Admitted.

  Lemma inv_create2 {v2 v3 l} (f f' : V -> hProp V L) :
    v2 ≠ v3 ->
    (∀ v, v ≠ v2 -> v ≠ v3 -> f v ⊢ f' v) ->
    (f v3 ⊢ emp) ->
    (f v2 ∗ own_in l ⊢ f' v2) ->
    (own_out v2 l ⊢ f' v3) ->
    inv f -> inv f'.
  Proof.
  Admitted.

  Lemma inv_create_in_out {v1 v2 v3 l12 l32} (f f' : V -> hProp V L) :
    v1 ≠ v2 ∧ v1 ≠ v3 ∧ v2 ≠ v3 ->
    (∀ v, v ≠ v1 -> v ≠ v2 -> v ≠ v3 -> f v ⊢ f' v) ->
    (f v2 ⊢ emp) ->
    (f v3 ⊢ emp) ->
    (f v1 ∗ own_out v2 l12 ⊢ f' v1) ->
    (own_in l12 ∗ own_in l32 ⊢ f' v2) ->
    (own_out v2 l32 ⊢ f' v3) ->
    inv f -> inv f'.
  Proof.
    intros Hneq Himp Hemp2 Hemp3 H1 H2 H3 Hinv.
    assert (inv (λ v,
      if decide (v = v1) then f v1 ∗ own_out v2 l12
      else if decide (v = v2) then own_in l12
      else f v)%I) as Hinv'.
    {
      eapply (inv_create1 (v1:=v1) (v2:=v2)); last done.
      - naive_solver.
      - intros. repeat case_decide; naive_solver.
      - done.
      - case_decide; eauto. done.
      - repeat case_decide; subst; eauto; naive_solver.
    }
    clear Hinv.
    eapply (inv_create2 (v2:=v2) (v3:=v3)); last done.
    - naive_solver.
    - intros. simpl. repeat case_decide; simplify_eq; eauto.
    - simpl. repeat case_decide; simplify_eq; naive_solver.
    - simpl. repeat case_decide; simplify_eq; eauto. naive_solver.
    - eauto.
  Qed. *)

  (* Lemma inv_create_in_out_exchange {v1 v2 v3 l12 l32} (f f' : V -> hProp V L) : *)





  (* Lemma inv_singleton v (P : list L -> hProp V L) :
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
  Admitted. *)

  (* Lemma inv_dealloc f (v : V) :
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
  Admitted. *)

  (*
    De situatie die je hebt is dat:
      f v1 = (<in_emp> P) ∗ own_out v2 l
      f v2 = Q ∗ own_in l
    En je wil updaten naar:
      f v1 = (<in_emp> P') ∗ own_out v2 l'
      f v2 = Q' ∗ own_in l'
    Waarbij:
      P ∗ Q ⊢ (<in_emp> P') ∗ Q'
  *)

  (* Lemma inv_relabel f (P1 P1' Q Q' : list L -> hProp V L) v1 v2 l l' :
    f !! v1 = Some (λ i, P1 i ∗ own1 v2 l)%I ->
    f !! v2 = Some Q ->
    (∀ i, P1 i ⊢ P1' i) ->
    (∀ i, Q (l :: i) ⊢ Q' (l' :: i)) ->
    inv f ->
    inv (<[ v1 := (λ i, P1' i ∗ own1 v2 l')%I ]> $ <[ v2 := Q' ]> f).
  Proof. Admitted. *)

  (* Lemma inv_exchange f (P1 P1' Q Q' : hProp V L) v1 v2 l l' :
    f v1 = (P1 ∗ own_out v2 l)%I ->
    f v2 = Q ->
    (P1 ∗ Q ⊢ P1' ∗ Q') ->
    (* (∀ i1 i2, P1 i1 ∗ Q (l :: i2) ⊢ P1' i1 ∗ Q' (l' :: i2)) -> *)
    inv f ->
    inv (<[ v1 := (P1' ∗ own_out v2 l')%I ]> $ <[ v2 := Q' ]> f).
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
    intros Hv1 Hv2 HP HQ Hinv.
    destruct Hinv as (g & Hg & Hinv).
    exists (insert_edge (insert_vertex g v2) v1 v2 l).
    split.
    - assert (v2 ∉ vertices g).
      {
        intro.
        specialize (Hinv v2) as [(QQ & HQQ & HQQ') ?]; eauto.
        rewrite Hv2 in HQQ.
        simplify_eq.
      }
      admit. (* well formedness of graph *)
    - intros v. split.
      + intros Hv. admit.
      + intros Hv. rewrite !lookup_insert_spec.
        repeat case_decide; subst.
        * set_solver.
        * exfalso. admit. (* lemma about insert_vertex *)
        * set_solver.
  Admitted.

  Lemma inv_alloc2 (f : gmap V (list L -> hProp V L)) (P P' Q : list L -> hProp V L) (v1 v2 : V) (l : L) :
    f !! v1 = Some P ->
    f !! v2 = None ->
    (∀ i, P i ⊢ P' (l :: i)) ->
    (own1 v1 l ⊢ Q []) ->
    inv f ->
    inv (<[ v1 := P' ]> $ <[ v2 := Q ]> f).
  Proof.
    intros Hv1 Hv2 HP HQ Hinv.
    destruct Hinv as (g & Hg & Hinv).
    exists (insert_edge (insert_vertex g v2) v2 v1 l).
    split.
    - assert (v2 ∉ vertices g).
      {
        intro.
        specialize (Hinv v2) as [(QQ & HQQ & HQQ') ?]; eauto.
        rewrite Hv2 in HQQ.
        simplify_eq.
      }
      admit. (* well formedness of graph *)
    - intros v. split.
      + intros Hv. setoid_rewrite lookup_insert_spec.
        case_decide; subst;[|setoid_rewrite lookup_insert_spec]; repeat case_decide; subst; eexists.
        * split; first done. admit.
        * split; first done. admit.
        * admit.
      + intros Hv. rewrite !lookup_insert_spec.
        repeat case_decide; subst.
        * set_solver.
        * exfalso. admit. (* lemma about insert_vertex *)
        * set_solver.
  Admitted.

  Lemma inv_alloc12 (f : gmap V (list L -> hProp V L)) (P P' Q R : list L -> hProp V L) (v1 v2 v3 : V) (l l' : L) :
    f !! v1 = Some P ->
    f !! v2 = None ->
    f !! v3 = None ->
    v2 ≠ v3 ->
    (∀ i, P i ∗ own1 v2 l ⊢ P' i) ->
    (emp ⊢ Q [l';l]) ->
    (own1 v2 l' ⊢ R []) ->
    inv f ->
    inv (<[ v1 := P' ]> $ <[ v2 := Q ]> $ <[ v3 := R ]> f).
  Proof.
    intros.
    set f' := (<[ v1 := (λ i, P i ∗ own1 v2 l)%I ]> $ <[ v2 := λ i, ⌜⌜ i = [l] ⌝⌝%I ]> f).
    assert (inv f').
    { eapply inv_alloc1; eauto. }
    clear H7.
    set f'' := (<[ v2 := Q ]> $ <[ v3 := R ]> f').
    assert (f' !! v2 = Some (λ i : list L, ⌜⌜ i = [l] ⌝⌝%I)).
    {
      subst f'. rewrite !lookup_insert_spec.
      repeat case_decide; set_solver.
    }
    assert (f' !! v3 = None).
    {
      subst f'. rewrite !lookup_insert_spec.
      repeat case_decide; set_solver.
    }
    assert (inv f'').
    {
      eapply inv_alloc2; eauto. intros i. iIntros "%".
      subst. iApply H5. done.
    }
    clear H8.
    eapply inv_impl; last done.
    subst f''. subst f'.
    intros v. rewrite !lookup_insert_spec.
    repeat case_decide; simplify_eq; eauto using local_impl_refl.
  Qed.

  (* Lemma inv_alloc12_move (f : gmap V (list L -> hProp V L)) (P P' Q R : list L -> hProp V L) (v1 v2 v3 : V) (l l' : L) :
    f !! v1 = Some P ->
    f !! v2 = None ->
    f !! v3 = None ->
    v2 ≠ v3 ->
    (∀ i, P i ∗ own1 v2 l ⊢ P' i ∗ S) ->
    (emp ⊢ Q [l';l]) ->
    (own1 v2 l' ⊢ R []) ->
    inv f ->
    inv (<[ v1 := P' ]> $ <[ v2 := Q ]> $ <[ v3 := R ]> f).
  Proof.
  Qed. *) *)

End genericinv.