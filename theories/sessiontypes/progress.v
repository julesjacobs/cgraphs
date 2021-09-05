From diris Require Import invariant.
Require Import Coq.Logic.Classical.


Lemma rtyped_inner e t :
  rtyped0 e t -∗ ⌜ (∃ v, e = Val v)  ∨
  ∃ k e0, ctx k ∧ e = k e0 ∧
    ((∃ e', pure_step e0 e') ∨
    (∃ v, e0 = Recv (Val v)) ∨
    (∃ v1 v2, e0 = Send (Val v1) (Val v2)) ∨
    (∃ v, e0 = Fork (Val v)) ∨
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
  - iDestruct "H" as (r t' ->) "[H1 H2]".
    iDestruct ("IH" with "H1") as "%". iClear "IH".
    iDestruct ("IH1" with "H2") as "%". iClear "IH1".
    iPureIntro.
    destruct H as [[v ->]|(k & e0 & Hk & -> & H)].
    + destruct H0 as [[v' ->]|(k & e0 & Hk & -> & H0)].
      * right.
        eexists (λ x, x), _.
        split_and!; [constructor|eauto 10..].
      * right.
        eexists (λ x, Send (Val v) (k x)),_.
        split_and!; eauto.
        constructor; eauto. constructor.
    + right.
      eexists (λ x, Send (k x) e2),_.
      split_and!; eauto.
      eapply (Ctx_cons (λ x, Send x e2)); eauto.
      constructor.
  - iDestruct "H" as (r' r ->) "H".
    iDestruct ("IH" with "H") as "%". iClear "IH".
    iPureIntro. right.
    destruct H as [[v ->]|(k & e0 & Hk & -> & H)].
    + eexists (λ x, x),_. split_and!; [constructor|eauto 10..].
    + eexists (λ x, Recv (k x)),_. split_and!; eauto.
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
  - iDestruct "H" as (r ->) "H".
    iDestruct ("IH" with "H") as "%". iClear "IH".
    iPureIntro. right.
    destruct H as [[v ->]|(k & e0 & Hk & -> & H)].
    + eexists (λ x, x),_. split_and!; [constructor|eauto 10..].
    + eexists (λ x, Fork (k x)),_. split_and!; eauto.
      constructor; eauto. constructor.
  - iDestruct "H" as (->) "H".
    iDestruct ("IH" with "H") as "%". iClear "IH".
    iPureIntro. right.
    destruct H as [[v ->]|(k & e0 & Hk & -> & H)].
    + eexists (λ x, x),_. split_and!; [constructor|eauto 10..].
    + eexists (λ x, Close (k x)),_. split_and!; eauto.
      constructor; eauto. constructor.
Qed.

Definition thread_waiting (es : list expr) (h : heap) (i j : nat) :=
  ∃ b k, ctx k ∧
    es !! i = Some (k (Recv (Val (ChanV (j,b))))) ∧
    h !! (j,b) = Some [].

Definition waiting es h (x y : object) (l : clabel) : Prop :=
  ∃ i j, x = Thread i ∧ y = Chan j ∧ thread_waiting es h i j.

Definition active (x : object) (es : list expr) (h : heap) :=
  match x with
  | Thread i => ∃ e, es !! i = Some e ∧ e ≠ Val UnitV
  | Chan i => ∃ b, is_Some (h !! (i,b))
  end.

Lemma heap_fresh (h : heap) :
  ∃ i, ∀ b, h !! (i,b) = None.
Proof.
  exists (fresh (dom (gset nat) (gmap_curry h))).
  intro. pose proof (is_fresh (dom (gset nat) (gmap_curry h))).
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

Lemma active_progress es h x :
  invariant es h -> active x es h -> ∃ (es' : list expr) (h' : heap), step es h es' h'.
Proof.
  intros H Hactive.
  destruct H as (g & Hwf & Hvs).
  revert x Hactive.
  eapply (cgraph_ind' (waiting es h) g (λ x,
    active x es h → ∃ (es' : list expr) (h' : heap), step es h es' h'));
    [solve_proper|eauto|].
  intros x Hind_out Hind_in Hactive.
  pose proof (Hvs x) as Hx.
  destruct x as [i|i]; simpl in *.
  - destruct Hactive as (e & He & Heneq).
    rewrite He in Hx.
    apply pure_sep_holds in Hx as [Hinl Hx].
    assert (holds (rtyped0 e UnitT) (out_edges g (Thread i))) as Hx' by eauto.
    eapply holds_entails in Hx'. 2: eapply rtyped_inner.
    rewrite ->pure_holds in Hx'.
    destruct Hx' as [(v & ->)|Hx'].
    + simpl in Hx. rewrite ->val_typed_val_typed' in Hx. simpl in Hx.
      eapply affinely_pure_holds in Hx as [Hx ->]. simplify_eq.
    + destruct Hx' as (k' & e0 & Hctx & -> & Hcases).
      rewrite ->rtyped0_ctx in Hx; eauto.
      apply exists_holds in Hx as [t Hx].
      apply sep_holds in Hx as (Σ1&Σ2&Hout&Hdisj&Het&Hctxt).
      destruct Hcases as [H|[H|[H|[H|H]]]].
      * destruct H as [e' H].
        eexists _,_.
        econstructor. econstructor; last done.
        econstructor; eauto.
        econstructor. done.
      * destruct H as [v ->].
        simpl in Het.
        apply exists_holds in Het as [t' Het].
        apply exists_holds in Het as [r Het].
        eapply pure_sep_holds in Het as [-> Het].
        rewrite ->val_typed_val_typed' in Het. simpl in Het.
        apply exists_holds in Het as [c Het].
        apply pure_sep_holds in Het as [-> Het].
        simpl in Het. destruct c.
        unfold own_ep in Het.
        apply own_holds in Het.
        rewrite <-Het in Hout.
        assert (out_edges g (Thread i) !! Chan c ≡ Some (b, RecvT t' r)) as HH.
        {
          rewrite Hout. erewrite lookup_union_Some_l; first done.
          rewrite lookup_singleton. done.
        }

        pose proof (out_edges_in_labels _ _ _ _ HH) as [x Hin].

        assert (∃ buf, h !! (c,b) = Some buf) as [buf Hbuf].
        {
          pose proof (Hvs (Chan c)) as Hc.
          simpl in Hc.
          apply exists_holds in Hc as [σs Hc].
          apply pure_sep_holds in Hc as [Hinlc Hc].
          eapply holds_entails in Hc; last first.
          {
            iIntros "H". iApply (bufs_typed_wlog true b with "H").
          }
          assert (σs !! b ≡ Some (RecvT t' r)) as Hσsb.
          { eapply map_to_multiset_lookup. rewrite <-Hinlc, Hin. done. }
          simplify_eq.
          rewrite ->Hσsb in Hc. simpl in Hc.
          unfold bufs_typed in Hc.
          eapply exists_holds in Hc as [rest Hc].
          eapply sep_holds in Hc as (Σ3 & Σ4 & Houtc & Hdisj' & Hc1 & Hc2).
          destruct (h !! (c,b)) eqn:E; eauto.
          simpl in Hc1. eapply false_holds in Hc1 as [].
        }

        destruct buf.
        {
          eapply Hind_out; eauto.
          - unfold waiting. eexists _,_.
            split_and!; eauto.
            unfold thread_waiting.
            eauto.
          - simpl. exists b. rewrite Hbuf. eauto.
        }

        eexists _,_.
        econstructor; econstructor; last done.
        econstructor; first done.
        eapply Recv_step. done.
      * destruct H as (v1 & v2 & ->).
        simpl in Het.
        apply exists_holds in Het as [r Het].
        apply exists_holds in Het as [t' Het].
        apply pure_sep_holds in Het as [-> Het].
        apply sep_holds in Het as (Σ3 & Σ4 & Σeq & Hdisj' & Het1 & Het2).
        rewrite ->val_typed_val_typed' in Het1. simpl in Het1.
        apply exists_holds in Het1 as [c Het1].
        apply pure_sep_holds in Het1 as [-> Het1].
        destruct c. apply own_holds in Het1.
        rewrite <-Het1 in Σeq.
        rewrite ->Σeq in Hout.
        rewrite ->Σeq in Hdisj.
        assert (out_edges g (Thread i) !! Chan c ≡ Some (b, SendT t' r)) as HH.
        {
          rewrite Hout. erewrite lookup_union_Some_l; first done.
          erewrite lookup_union_Some_l; first done.
          rewrite lookup_singleton. done.
        }

        pose proof (out_edges_in_labels _ _ _ _ HH) as [x Hin].

        assert (∃ buf, h !! (c,negb b) = Some buf) as [buf Hbuf].
        {
          pose proof (Hvs (Chan c)) as Hc.
          simpl in Hc.
          apply exists_holds in Hc as [σs Hc].
          apply pure_sep_holds in Hc as [Hinlc Hc].
          eapply holds_entails in Hc; last first.
          {
            iIntros "H". iApply (bufs_typed_wlog true b with "H").
          }
          assert (σs !! b ≡ Some (SendT t' r)) as Hσsb.
          { eapply map_to_multiset_lookup. rewrite <-Hinlc, Hin. done. }
          simplify_eq.
          rewrite ->Hσsb in Hc. simpl in Hc.
          unfold bufs_typed in Hc.
          eapply exists_holds in Hc as [rest Hc].
          eapply sep_holds in Hc as (Σ3' & Σ4' & Houtc & Hdisj'' & Hc1 & Hc2).
          destruct (h !! (c,b)) eqn:E; last first.
          { simpl in Hc1. eapply false_holds in Hc1 as []. }
          simpl in Hc1.
          assert (rest ≠ EndT).
          {
            intro. subst. destruct l; simpl in Hc1.
            - eapply affinely_pure_holds in Hc1 as [].
              inversion H0.
            - eapply false_holds in Hc1 as [].
          }
          destruct (h !! (c,negb b)) eqn:F; eauto.
          exfalso.
          simpl in Hc2.
          destruct (σs !! negb b) eqn:G.
          { eapply false_holds in Hc2 as []. }
          eapply affinely_pure_holds in Hc2 as [].
          apply H. apply dual_end_inv. done.
        }

        eexists _,_.
        econstructor; econstructor; last done.
        econstructor; first done.
        eapply Send_step. done.
      * destruct H as (v & ->).
        simpl in Het.
        apply exists_holds in Het as [r Het].
        apply pure_sep_holds in Het as [-> Het].
        rewrite ->val_typed_val_typed' in Het. simpl in Het.
        apply exists_holds in Het as [x Het].
        apply exists_holds in Het as [e Het].
        apply pure_sep_holds in Het as [-> Het].
        destruct (heap_fresh h) as [ii HH].
        eexists _,_.
        econstructor; econstructor; last done.
        econstructor; eauto.
        eapply Fork_step; eauto.
      * destruct H as (v & ->).
        simpl in Het.
        apply pure_sep_holds in Het as [-> Het].
        rewrite ->val_typed_val_typed' in Het. simpl in Het.
        apply exists_holds in Het as [c Het].
        apply pure_sep_holds in Het as [-> Het].
        destruct c. apply own_holds in Het.
        rewrite <-Het in Hout.
        assert (out_edges g (Thread i) !! (Chan c) ≡ Some (b,EndT)) as HH.
        {
          rewrite Hout. erewrite lookup_union_Some_l; eauto.
          rewrite lookup_singleton. done.
        }

        pose proof (out_edges_in_labels _ _ _ _ HH) as [x Hx].

        assert (h !! (c,b) = Some []).
        {
          pose proof (Hvs (Chan c)) as Hc.
          simpl in Hc.
          apply exists_holds in Hc as [σs Hc].
          apply pure_sep_holds in Hc as [Hinlc Hc].
          eapply holds_entails in Hc; last first.
          {
            iIntros "H". iApply (bufs_typed_wlog true b with "H").
          }
          assert (σs !! b ≡ Some EndT) as Hσsb.
          { eapply map_to_multiset_lookup. rewrite <-Hinlc, Hx. done. }
          simplify_eq.
          rewrite ->Hσsb in Hc. simpl in Hc.
          unfold bufs_typed in Hc.
          eapply exists_holds in Hc as [rest Hc].
          eapply sep_holds in Hc as (Σ3 & Σ4 & Houtc & Hdisj' & Hc1 & Hc2).
          destruct (h !! (c,b)) eqn:E; last first.
          { simpl in Hc1. eapply false_holds in Hc1 as []. }
          simpl in Hc1.
          destruct l; eauto.
          simpl in Hc1.
          eapply false_holds in Hc1 as [].
        }

        eexists _,_.
        econstructor; econstructor; last done.
        econstructor; first done.
        eapply Close_step. done.
  - destruct Hactive as (b & Hib).
    apply exists_holds in Hx as [σs Hx].
    apply pure_sep_holds in Hx as [Hinl Hx].
    eapply holds_entails in Hx; last by eapply (bufs_typed_wlog true b).
    destruct Hib as [buf Hbuf].
    rewrite Hbuf in Hx.
    destruct (σs !! b) as [σ1|] eqn:E; last first.
    { unfold bufs_typed in Hx. simpl in Hx.
      eapply exists_holds in Hx as [? Hx].
      eapply sep_holds in Hx as (? & ? & ? & ? & Hx & ?).
      eapply false_holds in Hx. done. }
    unfold bufs_typed in Hx. simpl in Hx.
    erewrite map_to_multiset_Some in Hinl; eauto.

    assert (∃ y, out_edges g y !! (Chan i) ≡ Some (b,σ1)) as [y Hy].
    {
      eapply in_labels_out_edges; eauto.
    }

    destruct y.
    + pose proof (Hvs (Thread n)) as Hn.
      simpl in Hn.
      eapply pure_sep_holds in Hn as [? Hn].
      destruct (es !! n) eqn:En; last first.
      {
        eapply emp_holds in Hn.
        eapply map_empty_equiv_eq in Hn.
        rewrite Hn in Hy. rewrite lookup_empty in Hy. inversion Hy.
      }
      destruct (classic (waiting es h (Thread n) (Chan i) (b, σ1))) as [w|n0]; last first.
      {
        eapply Hind_in; eauto.
        simpl. exists e. split; eauto.
        intros ->.
        simpl in Hn.
        eapply affinely_pure_holds in Hn as [].
        eapply map_empty_equiv_eq in H0.
        rewrite H0 in Hy.
        rewrite lookup_empty in Hy.
        inversion Hy.
      }
      unfold waiting in w.
      destruct w as (i0 & j & ? & ? & Htw). simplify_eq.
      unfold thread_waiting in Htw.
      destruct Htw as (b' & k & Hk & Hi0 & Hjb).
      rewrite Hi0 in En. simplify_eq.
      rewrite ->rtyped0_ctx in Hn; eauto.
      eapply exists_holds in Hn as [t Hn].
      eapply sep_holds in Hn as (?&?&?&?&?&?).
      simpl in H2.
      eapply exists_holds in H2 as [t' H2].
      eapply exists_holds in H2 as [r H2].
      eapply pure_sep_holds in H2 as [-> H2].
      eapply exists_holds in H2 as [r0 H2].
      eapply pure_sep_holds in H2 as [? H2]. simplify_eq.
      eapply own_holds in H2.
      assert (Some (b',RecvT t' r) ≡ Some (b,σ1)).
      {
        rewrite <- Hy.
        rewrite H0.
        rewrite <- H2.
        rewrite lookup_union lookup_singleton.
        destruct (x0 !! Chan j) eqn:Q; simpl.
        - rewrite Q. simpl. done.
        - rewrite Q. simpl. done.
      }
      inversion H4. inversion H7. simpl in *.
      apply leibniz_equiv in H8.
      simplify_eq.
      rewrite Hbuf in Hjb. simplify_eq.
      simpl in Hx.
      eapply exists_holds in Hx as [rest Hx].
      eapply pure_sep_holds in Hx as [-> Hx].
      simpl in Hx.
      destruct (h !! (j,negb b)) eqn:Q; last first.
      {
        simpl in Hx. destruct (σs !! negb b).
        - eapply false_holds in Hx as [].
        - eapply affinely_pure_holds in Hx as [].
          rewrite <-H9 in H6.
          rewrite ->dual_recv in H6. inversion H6.
      }
      simpl in Hx.
      destruct (σs !! negb b) eqn:Q2; last first.
      { eapply false_holds in Hx as []. }
      assert (delete b σs !! negb b = Some c) as HHH.
      { rewrite lookup_delete_ne //. by destruct b. }
      erewrite map_to_multiset_Some in Hinl; eauto.

      rewrite ->(comm (⋅)), <-assoc in Hinl; last apply _.

      assert (∃ z, out_edges g z !! (Chan j) ≡ Some (negb b, c)) as [z Hzout].
      {
        eapply in_labels_out_edges; eauto.
      }
      clear HHH.

      pose proof (Hvs z) as Hz.
      destruct z; simpl in Hz.
      {
        eapply pure_sep_holds in Hz as [? Hz].
        destruct (es !! n) eqn:R; last first.
        {
          eapply emp_holds in Hz.
          eapply map_empty_equiv_eq in Hz.
          rewrite Hz in Hzout. rewrite lookup_empty in Hzout.
          inversion Hzout.
        }
        destruct (classic (waiting es h (Thread n) (Chan j) (negb b, c))) as [w|n0]; last first.
        {
          eapply Hind_in; eauto.
          simpl. exists e. split; eauto.
          intros ->.
          simpl in Hz.
          eapply affinely_pure_holds in Hz as [].
          eapply map_empty_equiv_eq in H6.
          rewrite H6 in Hzout.
          rewrite lookup_empty in Hzout.
          inversion Hzout.
        }
        unfold waiting in w.
        destruct w as (? & ? & ? & ? & Htw). simplify_eq.
        unfold thread_waiting in Htw.
        destruct Htw as (b' & ? & ? & HH & Hjb).
        rewrite HH in R. simplify_eq.
        rewrite ->rtyped0_ctx in Hz; eauto.
        eapply exists_holds in Hz as [t Hz].
        eapply sep_holds in Hz as (?&?&?&?&QQ&?).
        simpl in *.
        eapply exists_holds in QQ as [? QQ].
        eapply exists_holds in QQ as [? QQ].
        eapply pure_sep_holds in QQ as [-> QQ].
        eapply exists_holds in QQ as [? QQ].
        eapply pure_sep_holds in QQ as [? QQ]. simplify_eq.
        eapply own_holds in QQ.
        assert (Some (b',RecvT x6 x7) ≡ Some (negb b,c)).
        {
          rewrite <- Hzout.
          rewrite H8.
          rewrite <- QQ.
          rewrite lookup_union lookup_singleton.
          destruct (x5 !! Chan x2) eqn:Q'; simpl.
          - rewrite Q'. simpl. done.
          - rewrite Q'. simpl. done.
        }
        inversion H12. simplify_eq.
        inversion H15. simpl in *. apply leibniz_equiv in H13.
        simplify_eq.
        rewrite Hjb in Q. simplify_eq.
        simpl in Hx.
        eapply affinely_pure_holds in Hx as [].
        inversion H7. simpl in *.
        inversion H18; simplify_eq. inversion H14.
        simplify_eq. rewrite ->dual_recv in H16. inversion H16.
      }


      pose proof (Hvs (Chan c0)) as Hc. simpl in Hc.
      eapply exists_holds in Hc as [σs' Hc].
      eapply pure_sep_holds in Hc as [Hσs' Hc].
      destruct (decide (h !! (c0,true) = None ∧ h !! (c0,false) = None)) as [[]|].
      {
        rewrite H5 in Hc. rewrite H6 in Hc.
        destruct (σs' !! true).
        { unfold bufs_typed in Hc. simpl in Hc.
          eapply exists_holds in Hc as [? Hc].
          eapply sep_holds in Hc as (?&?&?&?&?&?).
          eapply false_holds in H11 as [].
        }
        destruct (σs' !! false).
        { unfold bufs_typed in Hc. simpl in Hc.
          eapply exists_holds in Hc as [? Hc].
          eapply sep_holds in Hc as (?&?&?&?&?&?).
          eapply false_holds in H12 as [].
        }
        eapply (holds_entails _ emp%I) in Hc; last first.
        { iIntros "H". unfold bufs_typed.
          iDestruct "H" as (?) "[H1 H2]". simpl.
          iDestruct "H1" as "%".
          iDestruct "H2" as "%".
          done. }
        eapply emp_holds in Hc.
        apply map_empty_equiv_eq in Hc.
        rewrite Hc in Hzout. rewrite lookup_empty in Hzout.
        inversion Hzout.
      }
      assert (∃ b l, h !! (c0,b) = Some l) as (b' & l' & Hb).
      {
        destruct (h !! (c0,true)) eqn:Q3; eauto.
        destruct (h !! (c0,false)) eqn:Q3'; eauto.
        exfalso. eapply n. done.
      }
      eapply (Hind_in (Chan c0)).
      * rewrite Hzout. done.
      * intros (?&?&?&?). simplify_eq.
      * simpl. eauto.
    + pose proof (Hvs (Chan c)) as Hc. simpl in Hc.
      eapply exists_holds in Hc as [σs' Hc].
      eapply pure_sep_holds in Hc as [Hσs' Hc].
      destruct (decide (h !! (c,true) = None ∧ h !! (c,false) = None)) as [[]|].
      {
        rewrite H in Hc. rewrite H0 in Hc.
        destruct (σs' !! true).
        { unfold bufs_typed in Hc. simpl in Hc.
          eapply exists_holds in Hc as [? Hc].
          eapply sep_holds in Hc as (?&?&?&?&?&?).
          eapply false_holds in H3 as [].
        }
        destruct (σs' !! false).
        { unfold bufs_typed in Hc. simpl in Hc.
          eapply exists_holds in Hc as [? Hc].
          eapply sep_holds in Hc as (?&?&?&?&?&?).
          eapply false_holds in H4 as [].
        }
        eapply (holds_entails _ emp%I) in Hc; last first.
        { iIntros "H". unfold bufs_typed.
          iDestruct "H" as (?) "[H1 H2]". simpl.
          iDestruct "H1" as "%".
          iDestruct "H2" as "%".
          done. }
        eapply emp_holds in Hc.
        apply map_empty_equiv_eq in Hc.
        rewrite Hc in Hy. rewrite lookup_empty in Hy.
        inversion Hy.
      }
      assert (∃ b l, h !! (c,b) = Some l) as (b' & l & Hb).
      {
        destruct (h !! (c,true)) eqn:Q; eauto.
        destruct (h !! (c,false)) eqn:Q'; eauto.
        exfalso. eapply n. done.
      }
      eapply (Hind_in (Chan c)).
      * rewrite Hy. done.
      * intros (?&?&?&?). simplify_eq.
      * simpl. eauto.
Qed.


Lemma global_progress es h :
  invariant es h ->
  (h = ∅ ∧ ∀ e, e ∈ es -> e = Val UnitV) ∨
  (∃ es' h', step es h es' h').
Proof.
  intros H.
  destruct (final_state_decision es h) as [Hdec|Hdec]; eauto; right.
  assert (∃ x, active x es h) as [x Hactive].
  { destruct Hdec as [(x&?)|(x&?)].
    + destruct x. exists (Chan c). simpl. eauto.
    + destruct H0. eapply elem_of_list_lookup in H0 as [].
      exists (Thread x0). simpl. eauto. }
  eapply active_progress; eauto.
Qed.