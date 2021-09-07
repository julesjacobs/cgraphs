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
  intros (g & Hwf & Hvs). revert x.
  eapply (cgraph_ind' (waiting es h) g (λ x,
    active x es h → ∃ (es' : list expr) (h' : heap), step es h es' h'));
    [solve_proper|eauto|].
  intros x Hind_out Hind_in Hactive.
  (* Get the invariant for x *)
  pose proof (Hvs x) as Hx.
  (* Case analyze whether x is a channel or a thread *)
  destruct x as [i|i]; simpl in *.
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
      eexists _,_.
      econstructor. econstructor; last done.
      econstructor; eauto.
      econstructor. done.
    * (* Recv *)
      destruct H as [v ->].
      revert Het.
      Ltac model := repeat
        (setoid_rewrite pure_sep_holds || setoid_rewrite exists_holds
        || setoid_rewrite own_holds || setoid_rewrite val_typed_val_typed'
        || setoid_rewrite sep_holds).
      model.
      intros (t' & r & -> & [c b] & -> & Het). simpl in *.
      assert (out_edges g (Thread i) !! Chan c ≡ Some (b, RecvT t' r)) as HH.
      {
        rewrite Hout -Het. erewrite lookup_union_Some_l; first done.
        rewrite lookup_singleton. done.
      }

      pose proof (out_edges_in_labels _ _ _ _ HH) as [x Hin].

      assert (∃ buf, h !! (c,b) = Some buf) as [buf Hbuf].
      {
        pose proof (Hvs (Chan c)) as Hc.
        eapply prim_simple_adequacy; first done.
        iIntros "H". simpl.
        iDestruct "H" as (σs Hinlc) "H".
        iDestruct (bufs_typed_wlog true b with "H") as "H".
        assert (σs !! b ≡ Some (RecvT t' r)) as ->.
        { eapply map_to_multiset_lookup. rewrite <-Hinlc, Hin. done. }
        unfold bufs_typed.
        iDestruct "H" as (rest) "[H1 H2]".
        destruct (h !! (c,b)) eqn:E; eauto.
      }

      destruct buf.
      {
        eapply Hind_out; eauto.
        - unfold waiting, thread_waiting; eauto 10.
        - simpl. exists b. rewrite Hbuf //.
      }

      eexists _,_.
      econstructor; econstructor; last done.
      econstructor; first done.
      eapply Recv_step. done.
    * (* Send *)
      destruct H as (v1 & v2 & ->).
      revert Het. model.
      intros (r & t' & -> & Σ3 & Σ4 & Σeq & Hdisj' & ([c b] & -> & Het1) & Het2).

      assert (out_edges g (Thread i) !! Chan c ≡ Some (b, SendT t' r)) as HH.
      {
        rewrite <-Het1 in Σeq. rewrite ->Σeq in Hout. rewrite ->Σeq in Hdisj. clear Σeq.
        rewrite Hout. erewrite lookup_union_Some_l; first done.
        erewrite lookup_union_Some_l; first done.
        rewrite lookup_singleton. done.
      }

      pose proof (out_edges_in_labels _ _ _ _ HH) as [x Hin].

      assert (∃ buf, h !! (c,negb b) = Some buf) as [buf Hbuf].
      {
        pose proof (Hvs (Chan c)) as Hc.
        eapply prim_simple_adequacy; first done.
        simpl.
        iIntros "H". iDestruct "H" as (σs Hinlc) "H".
        iDestruct (bufs_typed_wlog true b with "H") as "H".
        assert (σs !! b ≡ Some (SendT t' r)) as ->.
        { eapply map_to_multiset_lookup. rewrite <-Hinlc, Hin. done. }
        unfold bufs_typed.
        iDestruct "H" as (rest) "[H1 H2]".
        destruct (h !! (c,b)) eqn:E; eauto. simpl.
        destruct (h !! (c,negb b)) eqn:F; eauto. simpl.
        destruct (σs !! negb b) eqn:G; eauto.
        iDestruct "H2" as "%". apply dual_end_inv in H. subst.
        destruct l; eauto. simpl.
        iDestruct "H1" as "%". inversion H.
      }

      eexists _,_.
      econstructor; econstructor; last done.
      econstructor; first done.
      eapply Send_step. done.
    * (* Fork *)
      destruct H as (v & ->).
      destruct (heap_fresh h) as [ii HH].
      eexists _,_.
      econstructor; econstructor; last done.
      econstructor; eauto.
      eapply Fork_step; eauto.
    * (* Close *)
      destruct H as (v & ->).
      revert Het. model.
      intros (-> & ([c b] & -> & Het)).
      assert (out_edges g (Thread i) !! (Chan c) ≡ Some (b,EndT)) as HH.
      {
        rewrite Hout -Het. erewrite lookup_union_Some_l; eauto.
        rewrite lookup_singleton. done.
      }

      pose proof (out_edges_in_labels _ _ _ _ HH) as [x Hx].

      assert (h !! (c,b) = Some []).
      {
        pose proof (Hvs (Chan c)) as Hc.
        eapply prim_simple_adequacy; first done. simpl.
        iIntros "H". iDestruct "H" as (σs Hinlc) "H".
        iDestruct (bufs_typed_wlog true b with "H") as "H".
        assert (σs !! b ≡ Some EndT) as ->.
        { eapply map_to_multiset_lookup. rewrite <-Hinlc, Hx. done. }
        unfold bufs_typed.
        iDestruct "H" as (rest) "[H1 H2]".
        destruct (h !! (c,b)) eqn:E; eauto.
        simpl. destruct l; simpl; eauto.
      }

      eexists _,_.
      econstructor; econstructor; last done.
      econstructor; first done.
      eapply Close_step. done.
  - (* Channel *)
    destruct Hactive as (b & Hib).
    apply exists_holds in Hx as [σs Hx].
    apply pure_sep_holds in Hx as [Hinl Hx].
    eapply holds_entails in Hx; last by eapply (bufs_typed_wlog true b).
    destruct Hib as [buf Hbuf].
    rewrite Hbuf in Hx.
    destruct (σs !! b) as [σ1|] eqn:E; last first.
    { eapply prim_simple_adequacy; first done.
      rewrite /bufs_typed /=. iIntros "H".
      by iDestruct "H" as (?) "[% ?]". }
    erewrite map_to_multiset_Some in Hinl; eauto.

    destruct (classic (∃ c q, out_edges g (Chan c) !! Chan i ≡ Some q)) as [(c & q & Hc)|Hnc].
    { (* This thing will handle the case of a chan-chan reference for us *)
      eapply (Hind_in (Chan c)); simpl; eauto. { rewrite /waiting. naive_solver. }
      destruct (h !! (c,true)) eqn:Q; eauto.
      destruct (h !! (c,false)) eqn:Q'; eauto.
      assert (out_edges g (Chan c) = ∅) as H.
      {
        eapply prim_empty_adequacy; first exact (Hvs (Chan c)).
        iIntros "H". simpl. rewrite Q Q' /bufs_typed /=.
        iDestruct "H" as (σs' ? ?) "[H1 H2]".
        destruct (σs' !! true),(σs' !! false); eauto.
      }
      rewrite H lookup_empty in Hc. inversion Hc.
    }
    (* Since the chan has a buffer, there exists somebody holding a ref to this chan *)
    (* If the other one is a chan, we're done *)
    assert (∃ y, out_edges g y !! (Chan i) ≡ Some (b,σ1)) as [[] Hy];
      first (eapply in_labels_out_edges; eauto); last (exfalso; eauto).
    (* The one holding the ref to the chan is a thread *)
    pose proof (Hvs (Thread n)) as Hn. simpl in Hn.
    eapply pure_sep_holds in Hn as [? Hn].
    destruct (es !! n) eqn:En; last first.
    {
      eapply emp_holds in Hn.
      eapply map_empty_equiv_eq in Hn.
      rewrite Hn in Hy. rewrite lookup_empty in Hy. inversion Hy.
    }
    destruct (classic (waiting es h (Thread n) (Chan i) (b, σ1))) as [w|n0]; last first.
    {
      (* The thread is not blocked on the chan (but could be blocked on another chan) *)
      eapply Hind_in; eauto. (* We need to show that the thread hasn't terminated with a unit value *)
      simpl. exists e. split; eauto. intros ->.
      simpl in Hn.
      eapply affinely_pure_holds in Hn as [].
      eapply map_empty_equiv_eq in H0.
      rewrite H0 lookup_empty in Hy. inversion Hy.
    }
    (* The thread is blocked on the chan *)
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
    destruct z; last (exfalso; eauto).
    pose proof (Hvs (Thread n)) as Hz. simpl in Hz.
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
Qed.

Definition chan_refs (es : list expr) (h : heap) (x : object) : gset chan. Admitted.

Inductive reachable (es : list expr) (h : heap) : object → Prop :=
  | Thread_step_reachable i : can_stepi i es h → reachable es h (Thread i)
  | Thread_waiting_reachable i c : reachable es h (Chan c) → thread_waiting es h i c → reachable es h (Thread i)
  | Chan_ref_reachable c x : c ∈ chan_refs es h x → reachable es h x → reachable es h (Chan c).

Lemma strong_progress es h x :
  invariant es h -> active x es h -> reachable es h x.
Proof.
  intros (g & Hwf & Hvs). revert x.
  eapply (cgraph_ind' (waiting es h) g (λ x,
    active x es h → reachable es h x));
    [solve_proper|eauto|].
  intros x Hind_out Hind_in Hactive.
  (* Get the invariant for x *)
  pose proof (Hvs x) as Hx.
  (* Case analyze whether x is a channel or a thread *)
  destruct x as [i|i]; simpl in *.
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
      econstructor; eauto.
      econstructor. done.
    * (* Recv *)
      destruct H as [v ->].
      revert Het.
      model.
      intros (t' & r & -> & [c b] & -> & Het). simpl in *.
      assert (out_edges g (Thread i) !! Chan c ≡ Some (b, RecvT t' r)) as HH.
      {
        rewrite Hout -Het. erewrite lookup_union_Some_l; first done.
        rewrite lookup_singleton. done.
      }

      pose proof (out_edges_in_labels _ _ _ _ HH) as [x Hin].

      assert (∃ buf, h !! (c,b) = Some buf) as [buf Hbuf].
      {
        pose proof (Hvs (Chan c)) as Hc.
        eapply prim_simple_adequacy; first done.
        iIntros "H". simpl.
        iDestruct "H" as (σs Hinlc) "H".
        iDestruct (bufs_typed_wlog true b with "H") as "H".
        assert (σs !! b ≡ Some (RecvT t' r)) as ->.
        { eapply map_to_multiset_lookup. rewrite <-Hinlc, Hin. done. }
        unfold bufs_typed.
        iDestruct "H" as (rest) "[H1 H2]".
        destruct (h !! (c,b)) eqn:E; eauto.
      }

      destruct buf.
      {
        eapply Thread_waiting_reachable; last unfold thread_waiting; eauto 10.
        eapply Hind_out; eauto.
        - unfold waiting, thread_waiting; eauto 10.
        - simpl. exists b. rewrite Hbuf //.
      }
      eapply Thread_step_reachable. eexists _,_. econstructor; last done; econstructor; first done.
      eapply Recv_step. done.
    * (* Send *)
      destruct H as (v1 & v2 & ->).
      revert Het. model.
      intros (r & t' & -> & Σ3 & Σ4 & Σeq & Hdisj' & ([c b] & -> & Het1) & Het2).

      assert (out_edges g (Thread i) !! Chan c ≡ Some (b, SendT t' r)) as HH.
      {
        rewrite <-Het1 in Σeq. rewrite ->Σeq in Hout. rewrite ->Σeq in Hdisj. clear Σeq.
        rewrite Hout. erewrite lookup_union_Some_l; first done.
        erewrite lookup_union_Some_l; first done.
        rewrite lookup_singleton. done.
      }

      pose proof (out_edges_in_labels _ _ _ _ HH) as [x Hin].

      assert (∃ buf, h !! (c,negb b) = Some buf) as [buf Hbuf].
      {
        pose proof (Hvs (Chan c)) as Hc.
        eapply prim_simple_adequacy; first done.
        simpl.
        iIntros "H". iDestruct "H" as (σs Hinlc) "H".
        iDestruct (bufs_typed_wlog true b with "H") as "H".
        assert (σs !! b ≡ Some (SendT t' r)) as ->.
        { eapply map_to_multiset_lookup. rewrite <-Hinlc, Hin. done. }
        unfold bufs_typed.
        iDestruct "H" as (rest) "[H1 H2]".
        destruct (h !! (c,b)) eqn:E; eauto. simpl.
        destruct (h !! (c,negb b)) eqn:F; eauto. simpl.
        destruct (σs !! negb b) eqn:G; eauto.
        iDestruct "H2" as "%". apply dual_end_inv in H. subst.
        destruct l; eauto. simpl.
        iDestruct "H1" as "%". inversion H.
      }
      eapply Thread_step_reachable. eexists _,_. econstructor; last done; econstructor; first done.
      eapply Send_step. done.
    * (* Fork *)
      destruct H as (v & ->).
      destruct (heap_fresh h) as [ii HH].
      eapply Thread_step_reachable. eexists _,_. econstructor; last done; econstructor; first done.
      eapply Fork_step; eauto.
    * (* Close *)
      destruct H as (v & ->).
      revert Het. model.
      intros (-> & ([c b] & -> & Het)).
      assert (out_edges g (Thread i) !! (Chan c) ≡ Some (b,EndT)) as HH.
      {
        rewrite Hout -Het. erewrite lookup_union_Some_l; eauto.
        rewrite lookup_singleton. done.
      }

      pose proof (out_edges_in_labels _ _ _ _ HH) as [x Hx].

      assert (h !! (c,b) = Some []).
      {
        pose proof (Hvs (Chan c)) as Hc.
        eapply prim_simple_adequacy; first done. simpl.
        iIntros "H". iDestruct "H" as (σs Hinlc) "H".
        iDestruct (bufs_typed_wlog true b with "H") as "H".
        assert (σs !! b ≡ Some EndT) as ->.
        { eapply map_to_multiset_lookup. rewrite <-Hinlc, Hx. done. }
        unfold bufs_typed.
        iDestruct "H" as (rest) "[H1 H2]".
        destruct (h !! (c,b)) eqn:E; eauto.
        simpl. destruct l; simpl; eauto.
      }
      eapply Thread_step_reachable. eexists _,_. econstructor; last done; econstructor; first done.
      eapply Close_step. done.
  - (* Channel *)
    destruct Hactive as (b & Hib).
    apply exists_holds in Hx as [σs Hx].
    apply pure_sep_holds in Hx as [Hinl Hx].
    eapply holds_entails in Hx; last by eapply (bufs_typed_wlog true b).
    destruct Hib as [buf Hbuf].
    rewrite Hbuf in Hx.
    destruct (σs !! b) as [σ1|] eqn:E; last first.
    { eapply prim_simple_adequacy; first done.
      rewrite /bufs_typed /=. iIntros "H".
      by iDestruct "H" as (?) "[% ?]". }
    erewrite map_to_multiset_Some in Hinl; eauto.

    destruct (classic (∃ c q, out_edges g (Chan c) !! Chan i ≡ Some q)) as [(c & q & Hc)|Hnc].
    { (* This thing will handle the case of a chan-chan reference for us *)
      eapply Chan_ref_reachable.
      { admit. }
      eapply (Hind_in (Chan c)); simpl; eauto. { rewrite /waiting. naive_solver. }
      destruct (h !! (c,true)) eqn:Q; eauto.
      destruct (h !! (c,false)) eqn:Q'; eauto.
      assert (out_edges g (Chan c) = ∅) as H.
      {
        eapply prim_empty_adequacy; first exact (Hvs (Chan c)).
        iIntros "H". simpl. rewrite Q Q' /bufs_typed /=.
        iDestruct "H" as (σs' ? ?) "[H1 H2]".
        destruct (σs' !! true),(σs' !! false); eauto.
      }
      rewrite H lookup_empty in Hc. inversion Hc.
    }
    (* Since the chan has a buffer, there exists somebody holding a ref to this chan *)
    (* If the other one is a chan, we're done *)
    assert (∃ y, out_edges g y !! (Chan i) ≡ Some (b,σ1)) as [[] Hy];
      first (eapply in_labels_out_edges; eauto); last (exfalso; eauto).
    (* The one holding the ref to the chan is a thread *)
    pose proof (Hvs (Thread n)) as Hn. simpl in Hn.
    eapply pure_sep_holds in Hn as [? Hn].
    destruct (es !! n) eqn:En; last first.
    {
      eapply emp_holds in Hn.
      eapply map_empty_equiv_eq in Hn.
      rewrite Hn in Hy. rewrite lookup_empty in Hy. inversion Hy.
    }
    destruct (classic (waiting es h (Thread n) (Chan i) (b, σ1))) as [w|n0]; last first.
    {
      (* The thread is not blocked on the chan (but could be blocked on another chan) *)
      eapply Chan_ref_reachable.
      { admit. }
      eapply Hind_in; eauto. (* We need to show that the thread hasn't terminated with a unit value *)
      simpl. exists e. split; eauto. intros ->.
      simpl in Hn.
      eapply affinely_pure_holds in Hn as [].
      eapply map_empty_equiv_eq in H0.
      rewrite H0 lookup_empty in Hy. inversion Hy.
    }
    (* The thread is blocked on the chan *)
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
    destruct z; last (exfalso; eauto).
    pose proof (Hvs (Thread n)) as Hz. simpl in Hz.
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