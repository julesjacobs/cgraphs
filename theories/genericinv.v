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
    - admit.
    - intros v'. split.
      + intros Hv. rewrite /vertices in Hv.
        assert (v' = v) by set_solver. subst.
        exists P. rewrite lookup_singleton.
        split; first done.
        assert (in_labels ({[v := ∅]} : gmap V (gmap V L)) v = []) as HH1 by admit.
        rewrite /out_edges. rewrite lookup_singleton. rewrite HH1. eauto.
      + rewrite /vertices. intros.
        assert (v' ≠ v); first set_solver.
        rewrite lookup_singleton_ne //.
  Admitted.

  Lemma inv_move f v1 v2 l W P Q :
    inv (<[ v1 := λ i, (P i ∗ own1 v2 l ∗ W)%I ]> $ <[ v2 := λ i, Q i ]> f) ->
    inv (<[ v1 := λ i, (P i ∗ own1 v2 l)%I ]> $ <[ v2 := λ i, (Q i ∗ W)%I ]> f).
  Proof. Admitted.


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
    - admit.
    - intros v'.
      split.
      + intros Hv'. pose proof (Hg v') as [Hg1 Hg2].
        destruct Hg1 as (Q' & HQ'1 & HQ'2); first set_solver.
        exists Q'. split.
        * rewrite lookup_delete_ne; last set_solver. done.
        * assert (v ≠ v') by set_solver.
          assert (in_labels (delete v g) v' = in_labels g v') as -> by admit.
          assert (out_edges (delete v g) v' = out_edges g v') as -> by admit.
          done.
      + intros Hv'.
        destruct (decide (v = v')).
        * subst. apply lookup_delete.
        * assert (v' ∉ vertices g) by set_solver.
          rewrite lookup_delete_ne; eauto.
          set_solver.
  Admitted.

    Lemma inv_exchange f (P P' Q Q' P1 P1' : list L -> hProp V L) v1 v2 l l' :
      f !! v1 = Some P ->
      f !! v2 = Some Q ->
      (∀ i, P i ⊢ P1 i ∗ own1 v2 l) ->
      (∀ i1 i2, P1 i1 ∗ Q (l :: i2) ⊢ P1' i1 ∗ Q' (l' :: i2)) ->
      (∀ i, P1' i ∗ own1 v2 l' ⊢ P' i) ->
      inv f ->
      inv (<[ v1 := P' ]> $ <[ v2 := Q' ]> f).
    Proof. Admitted.

      
(*
  Lemma inv_update f v1 v2 :
    inv' (<[ v1 := λ i, P i ∗ own v2 l ]> f) ->
    inv' (<[ v1 := λ i, P i ∗ own v2 l' ]> f)



  inv g (λ v' ins, f v' ins ∗ if decide (v1 = v') W else emp) h ->
  inv g' (λ v' ins, f v' ins ∗ if decide (v2 = v') W else emp) h. *)

  (* Lemma inv_move g f (h : V -> Prop) v1 v2 (W : hProp V L) :
    conn g v1 v2 ->
    inv g (λ v' ins, f v' ins ∗ if decide (v1 = v') W else emp) h ->
    inv g' (λ v' ins, f v' ins ∗ if decide (v2 = v') W else emp) h.
 *)
    (* We need to be able to express connectivity relationships here. *)
    (* But we need that anyway for progress. *)
    (* Think about how to handle that. *)

    (* v ↦ P ∗ V
    w ↦ Q

    v ↦ P
    w ↦ Q ∗ V *)

End genericinv.