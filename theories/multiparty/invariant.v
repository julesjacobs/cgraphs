Require Export diris.cgraphs.genericinv.
Require Export diris.multiparty.langdef.
Require Export diris.multiparty.rtypesystem.
Require Export diris.multiparty.mutil.

Ltac sdec := repeat case_decide; simplify_eq; simpl in *; eauto; try done.
Ltac smap := repeat (rewrite lookup_alter_spec || rewrite lookup_insert_spec || sdec).

Section pushpop.

  Lemma pop_push_None `{Countable A, Countable B} {V}
      (p p' : A) (q q' : B) (x : V) (bufs : bufsT A B V) :
    p ≠ p' ∨ q ≠ q' ->
    pop p' q' bufs = None ->
    pop p' q' (push p q x bufs) = None.
  Proof.
    intros Hne Hpop.
    unfold pop,push in *.
    smap; destruct (bufs !! q'); smap;
    destruct (g !! p'); smap;
    destruct l; smap; destruct Hne; smap.
  Qed.

  Lemma pop_push_Some `{Countable A, Countable B} {V}
      (p p' : A) (q q' : B) (x x' : V) (bufs bufs' : bufsT A B V) :
    pop p' q' bufs = Some (x', bufs') ->
    pop p' q' (push p q x bufs) = Some (x', push p q x bufs').
  Proof.
    unfold pop,push.
    intros Q. smap;
    destruct (bufs !! q'); smap;
    destruct (g !! p'); smap;
    destruct l; smap; do 2 f_equal;
    apply map_eq; intro; smap;
    f_equal; apply map_eq; intro; smap.
  Qed.

  Definition is_present `{Countable A, Countable B} {V}
      p q (bufss : bufsT A B V) :=
    match bufss !! q with
    | Some bufs => match bufs !! p with Some _ => True | None => False end
    | None => False
    end.

  Lemma pop_push_single `{Countable A, Countable B} {V}
      (p : A) (q : B) (x : V) (bufs : bufsT A B V) :
    is_present p q bufs ->
    pop p q bufs = None ->
    pop p q (push p q x bufs) = Some (x, bufs).
  Proof.
    intros Hpres Hpop.
    unfold is_present,pop,push in *.
    smap; destruct (bufs !! q) eqn:E; smap;
    destruct (g !! p) eqn:F; smap;
    destruct l; smap.
    do 2 f_equal. apply map_eq; intro; smap.
    rewrite E. f_equal.
    apply map_eq. intro. smap.
  Qed.

  Lemma pop_is_present `{Countable A, Countable B} {V}
      (p p' : A) (q q' : B) (x : V) (bufs bufs' : bufsT A B V) :
    pop p' q' bufs = Some (x, bufs') ->
    is_present p q bufs -> is_present p q bufs'.
  Proof.
    intros Hpop Hpres.
    unfold pop,is_present in *.
    destruct (bufs !! q') eqn:E; smap.
    destruct (g !! p') eqn:E'; smap.
    destruct l eqn:E''; smap.
    destruct (bufs !! q) eqn:F; smap.
  Qed.

  Lemma pop_swap `{Countable A, Countable B} {V}
      (p p' : A) (q q' : B) (x y : V) (bufs bufs' bufs'' : bufsT A B V) :
    q ≠ q' ->
    pop p q bufs = Some (x, bufs') ->
    pop p' q' bufs = Some (y, bufs'') ->
    match pop p q bufs'' with
    | None => False
    | Some (z,_) => x = z
    end.
  Proof.
    unfold pop. intros.
    destruct (bufs !! q) eqn:E; smap.
    destruct (g !! p) eqn:E'; smap.
    destruct l eqn:E''; smap.
    destruct (bufs !! q') eqn:F; smap.
    destruct (g0 !! p') eqn:F'; smap.
    destruct l eqn:F''; smap.
    destruct (bufs !! q) eqn:Q; smap.
    destruct (g !! p) eqn:Q'; smap.
  Qed.

  Lemma pop_swap' `{Countable A, Countable B} {V}
      (p p' : A) (q q' : B) (x y : V) (bufs bufs' bufs'' : bufsT A B V) :
    q ≠ q' ->
    pop p q bufs = Some (x, bufs') ->
    pop p' q' bufs = Some (y, bufs'') ->
    ∃ bufs''', pop p q bufs'' = Some (x, bufs''').
  Proof.
    intros.
    eapply pop_swap in H1; eauto.
    destruct (pop p q bufs''); sdec. destruct p0. subst.
    eauto.
  Qed.

  Definition dom_valid {A} (bufss : bufsT participant participant A) (d : gset participant) :=
    ∀ p, match bufss !! p with
         | Some bufs => p ∈ d ∧ ∀ q, q ∈ d ->
            match bufs !! q with Some _ => True | None => False end
         | None => p ∉ d
         end.

  Lemma dom_valid_push {A} d p q x (bufss : bufsT participant participant A) :
    p ∈ d ->
    dom_valid bufss d ->
    dom_valid (push p q x bufss) d.
  Proof.
    intros Hin Hdom p'.
    unfold dom_valid in *.
    specialize (Hdom p').
    unfold push. smap;
    destruct (bufss !! p') eqn:E; smap.
    destruct Hdom. split; eauto.
    intros q. specialize (H0 q).
    smap. destruct (g !! q) eqn:F; smap.
  Qed.

  Lemma dom_valid_is_present {A} p q (bufs : bufsT participant participant A) d :
    dom_valid bufs d ->
    p ∈ d -> q ∈ d ->
    is_present p q bufs.
  Proof.
    intros Hdv Hp Hq.
    unfold dom_valid, is_present in *.
    specialize (Hdv q).
    destruct (bufs !! q); smap. destruct Hdv.
    specialize (H0 p).
    destruct (g !! p); smap.
  Qed.

  Lemma dom_valid_empty {A} : dom_valid (∅ : bufsT participant participant A) ∅.
  Proof.
    intros ?. rewrite lookup_empty. set_solver.
  Qed.

  Lemma dom_valid_empty_inv {A} d : dom_valid (∅ : bufsT participant participant A) d -> d = ∅.
  Proof.
    intros Hdom. cut (¬ ∃ x, x ∈ d); try set_solver.
    intros []. unfold dom_valid in *.
    specialize (Hdom x).
    rewrite lookup_empty in Hdom. set_solver.
  Qed.

  Lemma dom_valid_pop {A} p q (bufs bufs' : bufsT participant participant A) x d :
    pop p q bufs = Some (x, bufs') ->
    dom_valid bufs d ->
    dom_valid bufs' d.
  Proof.
    intros Hpop Hdom r.
    specialize (Hdom r).
    unfold pop in *.
    destruct (bufs !! q) eqn:E; smap.
    destruct (g !! p) eqn:E'; smap.
    destruct l eqn:E''; smap.
    destruct (bufs !! r) eqn:F; smap.
    destruct Hdom; split; smap.
    intros q. specialize (H0 q). smap.
  Qed.

  Lemma dom_valid_delete {A} p d (bufss : bufsT participant participant A) :
    dom_valid bufss d ->
    dom_valid (delete p bufss) (d ∖ {[ p ]}).
  Proof.
    intros Hdv.
    unfold dom_valid in *.
    intros q. specialize (Hdv q).
    rewrite lookup_delete_spec. smap; first set_solver.
    destruct (bufss !! q); smap; set_solver.
  Qed.

  Lemma pop_delete_None `{Countable A, Countable B} {V}
    (p : A) (q q' : B) (m : bufsT A B V):
    pop p q m = None ->
    pop p q (delete q' m) = None.
  Proof.
    unfold pop in *. intros.
    rewrite lookup_delete_spec. sdec.
    destruct (m !! q); sdec.
    destruct (g !! p); eauto.
    destruct l; sdec.
  Qed.

  Definition bufs_empty {A} (bufs : bufsT participant participant A) :=
    ∀ p q, pop p q bufs = None.

  Lemma bufs_empty_delete {A} (bufs : bufsT participant participant A) p :
    bufs_empty bufs -> bufs_empty (delete p bufs).
  Proof.
    intros ???. eauto using pop_delete_None.
  Qed.

  Lemma pop_delete_Some `{Countable A, Countable B} {V} (p : A) (q q' : B) (x : V) bufss bufs' :
    q ≠ q' ->
    pop p q bufss = Some (x, bufs') ->
    pop p q (delete q' bufss) = Some (x, delete q' bufs').
  Proof.
    intros ? Hpop. unfold pop in *.
    rewrite !lookup_delete_spec. smap.
    destruct (bufss !! q) eqn:E; smap.
    destruct (g !! p) eqn:F; smap.
    destruct l; smap.
    do 2 f_equal.
    apply map_eq. intro.
    smap; rewrite !lookup_delete_spec; smap.
  Qed.

End pushpop.

Section bufs_typed.

  Inductive rglobal_type : Type :=
    | MessageR n : option (fin n) -> participant -> participant ->
                  (fin n -> type) -> (fin n -> rglobal_type) -> rglobal_type
    | ContinueR : global_type -> rglobal_type.

  Inductive rproj (r : participant) : rglobal_type -> session_type -> Prop :=
    | rproj_send n q ts Gs σs :
        q ≠ r -> (∀ i, rproj r (Gs i) (σs i)) ->
          rproj r (MessageR n None r q ts Gs) (SendT n q ts σs)
    | rproj_recv n o p ts Gs σs :
        p ≠ r -> (∀ i, rproj r (Gs i) (σs i)) ->
          rproj r (MessageR n o p r ts Gs) (RecvT n p ts σs)
    | rproj_skip n p q ts Gs σ :
        p ≠ r -> q ≠ r -> (∀ i, rproj r (Gs i) σ) ->
          rproj r (MessageR (S n) None p q ts Gs) σ
    | rproj_buf_skip n i p q ts Gs σ :
        q ≠ r -> rproj r (Gs i) σ ->
          rproj r (MessageR n (Some i) p q ts Gs) σ
    | rproj_continue G σ :
        proj r G σ -> rproj r (ContinueR G) σ.


  Definition sentryT := (nat * type)%type.
  Definition sbufsT := bufsT participant participant sentryT.

  Inductive sbufprojs : rglobal_type -> sbufsT -> Prop :=
    | bp_skip n p q ts Gs bufs :
        pop p q bufs = None -> (∀ i, sbufprojs (Gs i) bufs) ->
        sbufprojs (MessageR n None p q ts Gs) bufs
    | bp_here n p q i bufs bufs' ts Gs :
        pop p q bufs = Some ((fin_to_nat i, ts i), bufs') ->
        sbufprojs (Gs i) bufs' ->
        sbufprojs (MessageR n (Some i) p q ts Gs) bufs
    | bp_end G' bufs : bufs_empty bufs -> sbufprojs (ContinueR G') bufs.

  (* Fixpoint bufprojs (G : rglobal_type) (bufs : sbufsT) : rProp :=
    match G with
    | MessageR n o p q ts Gs =>
      match o with
      | None =>
        ⌜⌜ pop p q bufs = None ⌝⌝ ∗ ∀ i, bufprojs (Gs i) bufs
      | Some i =>
        ∃ v bufs', ⌜⌜ pop p q bufs = Some ((fin_to_nat i,v), bufs') ⌝⌝ ∗
          val_typed v (ts i) ∗ bufprojs (Gs i) bufs'
      end
    | ContinueR G' => ⌜⌜ bufs_empty bufs ⌝⌝
    end. *)


  Definition sbufs_typed (bufs : bufsT participant participant sentryT)
                        (σs : gmap participant session_type) : Prop :=
    dom_valid bufs (dom (gset _) σs) ∧
    ∃ G : rglobal_type,
        (∀ p, rproj p G (default EndT (σs !! p))) ∧
        sbufprojs G bufs.


  Inductive pushUG (p q : participant) (n : nat) (i : fin n) : type -> global_type -> rglobal_type -> Prop :=
    | pushU_skip n' p' q' t ts Gs Gs' :
        p' ≠ p -> (∀ j, pushUG p q n i t (Gs j) (Gs' j)) ->
        pushUG p q n i t (Message (S n') p' q' ts Gs) (MessageR (S n') None p' q' ts Gs')
    | pushU_here ts Gs :
        pushUG p q n i (ts i) (Message n p q ts Gs) (MessageR n (Some i) p q ts (λ j, ContinueR (Gs j))).

  Inductive pushG (p q : participant) (n : nat) (i : fin n) : type -> rglobal_type -> rglobal_type -> Prop :=
    | push_skipN n' p' q' ts Gs Gs' t :
        p' ≠ p -> (∀ j, pushG p q n i t (Gs j) (Gs' j)) ->
        pushG p q n i t (MessageR (S n') None p' q' ts Gs) (MessageR (S n') None p' q' ts Gs')
    | push_skipS n' i' p' q' ts Gs Gs' t :
        pushG p q n i t (Gs i') (Gs' i') -> (∀ j, j ≠ i' -> Gs j = Gs' j) ->
        pushG p q n i t (MessageR n' (Some i') p' q' ts Gs) (MessageR n' (Some i') p' q' ts Gs')
    | push_here ts Gs :
        pushG p q n i (ts i) (MessageR n None p q ts Gs) (MessageR n (Some i) p q ts Gs)
    | push_cont G G' t : pushUG p q n i t G G' -> pushG p q n i t (ContinueR G) G'.

  Ltac inv H := inversion H; simplify_eq; clear H.

  Lemma send_pushUG p q G n ts σs i :
    proj p G (SendT n q ts σs) -> ∃ G', pushUG p q n i (ts i) G G'.
  Proof.
    intros H.
    inv H; eauto using pushUG.
    assert (∀ j, ∃ G', pushUG p q n i (ts i) (G0 j) G').
    {
      intros j.
      specialize (H2 j).
      specialize (H3 j).
      revert H2 H3.
      generalize (G0 j). clear. intros G Hproj Hoc.
      induction Hoc; inv Hproj; eauto using pushUG.
      assert (∀ i0, ∃ G' : rglobal_type, pushUG p q n i (ts i) (g i0) G').
      { eauto. }
      apply fin_choice in H1 as [].
      eauto using pushUG.
    }
    eapply fin_choice in H as []; eauto using pushUG.
  Qed.

  Lemma send_pushG p q G n ts σs i :
    rproj p G (SendT n q ts σs) -> ∃ G', pushG p q n i (ts i) G G'.
  Proof.
    intros H.
    induction G; inv H; eauto using pushG.
    - assert (∀ j, ∃ G', pushG p q n i (ts i) (r j) G') as Hc; eauto.
      apply fin_choice in Hc as [Gs' HGs'].
      eexists. constructor; eauto.
    - edestruct H0; eauto.
      eexists (MessageR _ _ _ _ _ (λ j, if decide (j = i1) then x else r j)).
      econstructor; last intros; case_decide; simplify_eq; eauto.
    - edestruct send_pushUG; eauto using pushG.
  Qed.

  Lemma pushUG_send p q n i G G' t ts σs :
    pushUG p q n i t G G' -> proj p G (SendT n q ts σs) -> rproj p G' (σs i).
  Proof.
    induction 1; intros Hproj; inv Hproj; eauto using rproj.
  Qed.

  Lemma pushG_send p q n i G G' t ts σs :
    pushG p q n i t G G' -> rproj p G (SendT n q ts σs) -> rproj p G' (σs i).
  Proof.
    induction 1; intros Hproj; inv Hproj; eauto using rproj, pushUG_send.
  Qed.

  Lemma pushUG_other p q r n i G G' σ t :
    r ≠ p -> pushUG p q n i t G G' -> proj r G σ -> rproj r G' σ.
  Proof.
    intros Hneq Hpush. revert σ; induction Hpush; intros σ Hproj;
    inv Hproj; eauto using rproj.
    - constructor.
      + intros ->. apply H2. eauto using occurs_in.
      + intros ->. apply H2. eauto using occurs_in.
      + intro. eapply H1. constructor. intros Q.
        eapply H2. eauto using occurs_in.
    - econstructor; eauto.
      { intros ->. apply H; eauto using occurs_in. }
      econstructor. constructor. intros Q.
      apply H. econstructor. eauto using occurs_in.
  Qed.

  Lemma pushG_other p q r n i G G' σ t :
    r ≠ p -> pushG p q n i t G G' -> rproj r G σ -> rproj r G' σ.
  Proof.
    intros Hneq Hpush. revert σ; induction Hpush; intros σ Hproj;
    inv Hproj; eauto using rproj, pushUG_other.
    econstructor; eauto. intros j.
    destruct (decide (j = i')); subst; eauto.
    rewrite -H; eauto.
  Qed.

  Lemma proj_consistent p q n i t G G' :
    pushG p q n i t G G' -> ¬ rproj q G EndT.
  Proof.
    induction 1; intros Hproj; inv Hproj.
    - eapply H1. eauto. Unshelve. exact 0%fin.
    - induction H; inv H1; eauto using occurs_in.
      eapply H2. econstructor. intro.
      eauto using occurs_in. Unshelve. exact 0%fin. exact 0%fin.
  Qed.



  Lemma pushUG_bufs p q n i t G G' v bufs :
    pushUG p q n i t G G' -> bufs_empty bufs -> is_present p q bufs ->
    val_typed v t ⊢ bufprojs G' (push p q (fin_to_nat i,v) bufs).
  Proof.
    intros Hpush. induction Hpush;
    iIntros (Hbe Hpres) "H"; simpl.
    - iSplit. { iPureIntro. apply pop_push_None; eauto. }
      iIntros (j). iApply H1; eauto.
    - iExists _,_. iFrame.
      iSplit; eauto. iPureIntro.
      apply pop_push_single; eauto.
  Qed.


  Lemma pushG_bufs p q n i G G' bufs v t :
    pushG p q n i t G G' -> is_present p q bufs ->
    val_typed v t ∗ bufprojs G bufs ⊢
    bufprojs G' (push p q (fin_to_nat i,v) bufs).
  Proof.
    intros Hpush. revert bufs. induction Hpush; intros bufs Hpres;
    iIntros "[Hv H]"; simpl.
    - iDestruct "H" as (Hpop) "H".
      iSplit. { iPureIntro. apply pop_push_None; eauto. }
      iIntros (j). iApply H1; eauto with iFrame.
    - iDestruct "H" as (v' bufs' Hpop) "[Hv' H]".
      iDestruct (IHHpush with "[Hv H]") as "H". 2: eauto with iFrame.
      { eauto using pop_is_present. }
      iExists _,_. iFrame.
      iPureIntro.
      by apply pop_push_Some.
    - iDestruct "H" as (Hpop) "H".
      iExists _,_. iFrame.
      iSplit; last eauto.
      iPureIntro.
      apply pop_push_single; eauto.
    - iDestruct "H" as %Hemp.
      iApply pushUG_bufs; eauto.
  Qed.





  Lemma bufs_typed_push' (bufss : bufsT participant participant entryT)
                        (σs : gmap participant session_type)
                        (n : nat) (i : fin n) (p q : participant) ts ss v :
    σs !! p = Some (SendT n q ts ss) ->
    val_typed v (ts i) ∗ bufs_typed bufss σs ⊢
        bufs_typed (push p q (fin_to_nat i,v) bufss) (<[p:=ss i]> σs).
  Proof.
    iIntros (Hp) "[Hv H]".
    iDestruct "H" as (Hdom G Hprojs) "H".
    iSplit. { iPureIntro. rewrite dom_insert_lookup_L; eauto.
     apply dom_valid_push; eauto. apply elem_of_dom; eauto. }
    pose proof (Hprojs p) as Hproj. rewrite Hp in Hproj. simpl in *.
    edestruct send_pushG as [G' H]; first done.
    iExists G'.
    iSplit.
    - iPureIntro. intros r. rewrite lookup_insert_spec.
      case_decide; subst; simpl; last eauto using pushG_other.
      eapply pushG_send; eauto.
    - iApply pushG_bufs; eauto with iFrame.
      eapply dom_valid_is_present; eauto; apply elem_of_dom.
      + rewrite ?Hp; eauto.
      + specialize (Hprojs q).
        destruct (σs !! q); eauto.
        simpl in *. exfalso. eapply proj_consistent; eauto.
  Qed.

  Inductive popG (p q : participant) (n : nat) (i : fin n) : type -> rglobal_type -> rglobal_type -> Prop :=
    | pop_skipN n' p' q' ts Gs Gs' t :
        q' ≠ q -> (∀ j, popG p q n i t (Gs j) (Gs' j)) ->
        popG p q n i t (MessageR (S n') None p' q' ts Gs) (MessageR (S n') None p' q' ts Gs')
    | pop_skipS n' i' p' q' ts Gs Gs' t :
        q' ≠ q -> popG p q n i t (Gs i') (Gs' i') -> (∀ j, j ≠ i' -> Gs j = Gs' j) ->
        popG p q n i t (MessageR n' (Some i') p' q' ts Gs) (MessageR n' (Some i') p' q' ts Gs')
    | pop_here ts Gs :
        popG p q n i (ts i) (MessageR n (Some i) p q ts Gs) (Gs i).


  Lemma bufprojs_popG (G : rglobal_type)
    (bufs bufs' : bufsT participant participant entryT)
    (n : nat) (p q : participant) v i ts ss :
    rproj q G (RecvT n p ts ss) ->
    pop p q bufs = Some((i,v),bufs') ->
    bufprojs G bufs ⊢ ⌜ ∃ G' i', i = fin_to_nat i' ∧ popG p q n i' (ts i') G G' ⌝.
  Proof.
    iIntros (Hp Hpop) "H".
    iInduction G as [] "IH" forall (bufs bufs' Hpop); first destruct o; simpl.
    - iDestruct "H" as (v0 bufs'0 Hpop') "[Hv H]".
      inv Hp.
      + iExists _,_. iSplit; first done.
        iPureIntro. eapply pop_here.
      + assert (∃ bufs'', pop p q bufs'0 = Some (i, v, bufs'')) as []; eauto using pop_swap'.
        iDestruct ("IH" with "[%] [%] H") as "H"; eauto.
        iDestruct "H" as %(G' & i' & -> & HpopG).
        iPureIntro.
        eexists (MessageR _ _ _ _ _ (λ i, if decide (i = t0) then G' else r i)),_.
        split; eauto. econstructor; eauto. sdec.
        intros. sdec.
    - iDestruct "H" as (Hpop') "H".
      inv Hp.
      iAssert ⌜ ∀ j, ∃ G' i', i = fin_to_nat i' ∧ popG p q n i' (ts i') (r j) G' ⌝%I with "[H]" as "%".
      {
        iIntros (j). iDestruct ("IH" with "[%] [%] [H]") as "H"; eauto.
      }
      apply fin_choice in H as [].
      iPureIntro.
      destruct (H 0%fin) as [j []]. subst.
      eexists _,_. split; eauto. econstructor; eauto.
      intros. edestruct H as [? []]. simplify_eq. eauto.
    - iDestruct "H" as %Hemp.
      rewrite Hemp in Hpop. sdec.
  Qed.

  Lemma popG_recv p q n i G G' t ts σs :
    popG p q n i t G G' -> rproj q G (RecvT n p ts σs) -> rproj q G' (σs i).
  Proof.
    induction 1; intros Hproj; inv Hproj; eauto using rproj.
  Qed.

  Lemma popG_other p q r n i G G' σ t :
    r ≠ q -> popG p q n i t G G' -> rproj r G σ -> rproj r G' σ.
  Proof.
    intros Hneq Hpush. revert σ; induction Hpush; intros σ Hproj;
    inv Hproj; eauto using rproj.
    econstructor; eauto.
    intros j. destruct (decide (j = i')); sdec.
    rewrite -H0; eauto.
  Qed.

  Lemma popG_bufprojs p q n bufs bufs' v i t G G' :
    popG p q n i t G G' ->
    pop p q bufs = Some (fin_to_nat i, v, bufs') ->
    bufprojs G bufs ⊢ val_typed v t ∗ bufprojs G' bufs'.
  Proof.
    intros HpopG. revert bufs bufs'. induction HpopG; simpl; iIntros (bufs bufs' Hpop) "H".
    - iDestruct "H" as (Hpop') "H". rewrite comm -assoc. iSplit. { admit. }
      rewrite comm.
      iAssert (∀ j, val_typed v t ∗ bufprojs (Gs' j) bufs')%I with "[H]" as "H".
      { iIntros (j). iApply H1; eauto. }
      admit.
    - iDestruct "H" as (w bufs'' Hpop') "[Hv H]".
      iDestruct (IHHpopG with "H") as "[Hv' H]"; eauto. admit.
      iFrame. iExists _,_. iFrame. admit.
    - admit.
  Admitted.


  Lemma bufs_typed_pop' (σs : gmap participant session_type)
    (bufs bufs' : bufsT participant participant entryT)
    (n : nat) (p q : participant) v i ts ss :
    σs !! q = Some (RecvT n p ts ss) ->
    pop p q bufs = Some((i,v),bufs') ->
    bufs_typed bufs σs ⊢ ∃ i', ⌜⌜ i = fin_to_nat i' ⌝⌝ ∗
      val_typed v (ts i') ∗ bufs_typed bufs' (<[ q := ss i' ]> σs).
  Proof.
    iIntros (Hp Hpop) "H".
    iDestruct "H" as (Hdom G Hprojs) "H".
    pose proof (Hprojs q) as Hproj. rewrite Hp in Hproj. simpl in *.
    iDestruct (bufprojs_popG with "H") as %(G' & i' & Q & HpopG); eauto.
    iExists i'. iSplit; first done.
    unfold bufs_typed. rewrite comm -assoc. subst.
    iSplit. { iPureIntro. rewrite dom_insert_lookup_L; eauto.
      eapply dom_valid_pop; eauto. }
    iDestruct (popG_bufprojs with "H") as "[Hv H]"; eauto. iFrame.
    iExists G'. iFrame. iPureIntro.
    intros r. smap; eauto using popG_other, popG_recv.
  Qed.

  Lemma bufs_typed_push (bufss : bufsT participant participant entryT)
    (σs : gmap participant session_type)
    (n : nat) (i : fin n) (p q : participant) ts ss v :
    σs !! p ≡ Some (SendT n q ts ss) ->
    val_typed v (ts i) ∗ bufs_typed bufss σs ⊢
      bufs_typed (push p q (fin_to_nat i,v) bufss) (<[p:=ss i]> σs).
  Proof.
    iIntros (H) "[H1 H2]".
    inversion H. remember (SendT n q ts ss).
    inversion H2; simplify_eq.
    rewrite -(H4 i).
    iApply bufs_typed_push'; first done. iFrame.
    rewrite (H3 i) //.
  Qed.

  Lemma bufs_typed_pop (σs : gmap participant session_type)
    (bufs bufs' : bufsT participant participant entryT)
    (n : nat) (p q : participant) v i ts ss :
    σs !! q ≡ Some (RecvT n p ts ss) ->
    pop p q bufs = Some((i,v),bufs') ->
    bufs_typed bufs σs ⊢ ∃ i', ⌜⌜ i = fin_to_nat i' ⌝⌝ ∗
      val_typed v (ts i') ∗ bufs_typed bufs' (<[ q := ss i' ]> σs).
  Proof.
    intros H. inversion H. simplify_eq.
    remember (RecvT n p ts ss).
    inversion H2; simplify_eq. symmetry in H0.
    intros.
    eapply bufs_typed_pop' in H0; last done.
    iIntros "H".
    iDestruct (H0 with "H") as (j ->) "[Hv H]".
    iExists _. iSplit; first done.
    rewrite -(H1 j) -(H3 j) //. iFrame.
  Qed.


  Lemma bufs_typed_dealloc bufss σs p :
    σs !! p ≡ Some EndT ->
    bufs_typed bufss σs ⊢
    bufs_typed (delete p bufss) (delete p σs).
  Proof.
    iIntros (Hpp) "H".
    assert (σs !! p = Some EndT) as Hp.
    { inversion Hpp. inversion H1. simplify_eq. rewrite H //. }
    clear Hpp.
    iDestruct "H" as (Hdom) "H".
    iSplit. { iPureIntro. rewrite dom_delete_L. eapply dom_valid_delete; done. }
    iDestruct "H" as (G Hprojs) "H".
    assert (rproj p G EndT) as Hprojp.
    { specialize (Hprojs p). rewrite Hp in Hprojs. done. }
    iExists G. iSplit.
    { iPureIntro. intros p'. rewrite lookup_delete_spec.
      case_decide; subst; eauto. }
    clear Hp Hdom Hprojs.
    iInduction G as [] "IH" forall (bufss); inv Hprojp; simpl.
    - iDestruct "H" as (Hpop) "H".
      iSplit; first eauto using pop_delete_None.
      iIntros (i). iApply ("IH" with "[%] [H]"); eauto.
    - iDestruct "H" as (v bufs' Hpop) "[Hv H]".
      iExists _,_.
      iSplit; first eauto using pop_delete_Some. iFrame.
      iApply ("IH" with "[%] H"). eauto.
    - iDestruct "H" as "%". eauto using bufs_empty_delete.
  Qed.


  Lemma bufs_typed_empty :
    emp ⊢ bufs_typed ∅ ∅.
  Proof.
    iIntros "_".
    iSplit. { iPureIntro. rewrite dom_empty_L. apply dom_valid_empty. }
    iExists (ContinueR EndG).
    iSplit.
    - iPureIntro. intros.
      rewrite lookup_empty /=.
      constructor. constructor. intros H.
      inversion H.
    - simpl. iPureIntro.
      intros ??. unfold pop. rewrite lookup_empty //.
  Qed.



  Lemma bufs_typed_empty_inv σs :
    bufs_typed ∅ σs ⊢ ⌜⌜ σs = ∅ ⌝⌝.
  Proof.
    iIntros "[% H]".
    iDestruct "H" as (G Hprojs) "H".
    apply dom_valid_empty_inv in H.
    apply dom_empty_iff_L in H. subst.
    setoid_rewrite lookup_empty in Hprojs. simpl in *.
    assert (G = ContinueR EndG) as ->.
    { destruct G.
      - specialize (Hprojs p0); inversion Hprojs; simplify_eq.
      - destruct g; eauto.
        specialize (Hprojs p0); inversion Hprojs; simplify_eq.
        inversion H0; simplify_eq.
        exfalso. apply H. eauto using occurs_in. }
    simpl. eauto.
  Qed.

  Lemma dom_valid_init n d :
    (∀ k, k ∈ d <-> k < n) ->
    dom_valid (init_chans n) d.
  Proof.
    intros Hd.
    unfold dom_valid. intros p. unfold init_chans.
  Admitted.

  Lemma bufs_empty_init_chans n :
    bufs_empty (init_chans n).
  Proof.
  Admitted.

  Lemma bufs_typed_init n σs :
    consistent n σs ->
    emp ⊢ bufs_typed (init_chans n) (fin_gmap n σs).
  Proof.
    iIntros (Hcons) "_".
    unfold bufs_typed.
    iSplit; first by eauto using dom_valid_init, fin_gmap_dom.
    destruct Hcons as [G [Hprosj Hocc]].
    iExists (ContinueR G).
    iSplit; eauto using bufs_empty_init_chans.
    iPureIntro. intros. econstructor.
    destruct (decide (p < n)).
    + rewrite <-(fin_to_nat_to_fin _ _ l).
      rewrite fin_gmap_lookup. simpl. eauto.
    + rewrite fin_gmap_lookup_ne; eauto with lia.
  Qed.

  Lemma bufs_typed_recv bufss σs p q n t σ :
    σs !! p ≡ Some (RecvT n q t σ) ->
    bufs_typed bufss σs ⊢ ⌜ is_Some (bufss !! p) ⌝.
  Proof.
    iIntros (Q) "[% H]".
    iPureIntro.
    unfold dom_valid in *.
    specialize (H p).
    destruct (bufss !! p); eauto.
    exfalso. apply H. apply elem_of_dom. inv Q. rewrite -H0. eauto.
  Qed.

  Definition can_progress
    (bufs : bufsT participant participant entryT)
    (σs : gmap participant session_type) := ∃ p σ,
      σs !! p = Some σ ∧
      match σ with
      | RecvT n q _ _ => ∃ y bufs', pop p q bufs = Some(y,bufs')
      | _ => True
      end.

  Lemma bufs_typed_progress bufss σs :
    bufs_typed bufss σs ⊢ ⌜ bufss = ∅ ∨ can_progress bufss σs ⌝.
  Proof.
  Admitted.
    (* iIntros "[% H]".
    iDestruct "H" as (G Hprojs) "H".
    destruct G; simpl.
    - iPureIntro. right.
      unfold can_progress.
      specialize (Hprojs p).
      exists p.
      destruct (σs !! p); last (inversion Hprojs; simplify_eq).
      eexists _; split; first done.
      destruct s; eauto. simpl in *.
      inversion Hprojs; simplify_eq.
    - specialize (Hprojs p0).
      iRight. unfold can_progress.
      iExists p0.
      destruct (σs !! p0); last (inversion Hprojs; simplify_eq). simpl in *.
      iExists s. iSplit; eauto.
      destruct s; eauto.
      iDestruct "H" as (v bufs' Hpop) "[Hv H]".
      inversion Hprojs; simplify_eq.
      eauto.
    - destruct (classic (bufss = ∅)) as [|Q]; eauto.
      eapply map_choose in Q as [p [x Hp]].
      iRight. iDestruct "H" as %Q.
      iPureIntro.
      unfold can_progress.
      destruct g.
      + specialize (Hprojs p0).
        exists p0.
        destruct (σs !! p0); simpl in *.
        * inversion Hprojs; subst.
          remember (Message n p0 p1 t g).
          inversion H1; simplify_eq.
          { eexists. split; eauto. simpl. eauto. }
          exfalso. eauto using occurs_in.
        * inversion Hprojs; simplify_eq. inversion H1; simplify_eq.
          exfalso. eauto using occurs_in.
      + specialize (Hprojs p).
        exists p.
        destruct (σs !! p) eqn:E; last first.
        { apply not_elem_of_dom in E.
          exfalso. apply E.
          rewrite -H.
          apply elem_of_dom. rewrite Hp. eauto. }
        eexists. split; first done.
        destruct s; eauto.
        simpl in *.
        inversion Hprojs; simplify_eq.
        inversion H1; simplify_eq.
  Qed. *)

End bufs_typed.

Section invariant.
  Definition state_inv (es : list expr) (h : heap) (x : object) (in_l : multiset clabel) : rProp :=
    match x with
    | Thread n =>
      ⌜⌜ in_l ≡ ε ⌝⌝ ∗ (* rtyped (default UnitV (es !! n)) UnitT *)
      match es !! n with
      | Some e => rtyped0 e UnitT
      | None => emp
      end
    | Chan n => ∃ σs : gmap participant session_type,
      ⌜⌜ in_l ≡ map_to_multiset σs ⌝⌝ ∗
      bufs_typed (gmap_slice h n) σs
    end%I.

  Definition invariant (es : list expr) (h : heap) := inv (state_inv es h).
End invariant.

Instance state_inv_proper es h v : Proper ((≡) ==> (⊣⊢)) (state_inv es h v).
Proof. solve_proper_prepare. destruct v; [solve_proper|by setoid_rewrite H]. Qed.
Instance state_inv_params : Params (@state_inv) 3. Defined.

Lemma gmap_slice_push `{Countable A,Countable B,Countable C} {V}
    (p : A) (c : B) (q : C) (x : V) (m : bufsT A (B*C) V) :
  gmap_slice (push p (c, q) x m) c = push p q x (gmap_slice m c).
Proof.
  unfold push. rewrite gmap_slice_alter. case_decide; simplify_eq. done.
Qed.

Lemma gmap_slice_pop `{Countable A,Countable B,Countable C} {V}
    (p : A) (c : B) (q : C) (x : V) (m m' : bufsT A (B*C) V) :
  pop p (c,q) m = Some(x,m') ->
  pop p q (gmap_slice m c) = Some(x,gmap_slice m' c).
Proof.
  unfold pop. intros. rewrite gmap_slice_lookup.
  destruct (m !! (c, q)); smap.
  destruct (g !! p); smap.
  destruct l; smap. do 2 f_equal.
  apply map_eq. intro. smap;
  rewrite gmap_slice_insert; smap.
Qed.

Lemma gmap_slice_pop_ne `{Countable A,Countable B,Countable C} {V}
    (p : A) (c c' : B) (q : C) (x : V) (m m' : bufsT A (B*C) V) :
  c ≠ c' ->
  pop p (c,q) m = Some(x,m') ->
  gmap_slice m c' = gmap_slice m' c'.
Proof.
  unfold pop. intros.
  destruct (m !! (c, q)); smap.
  destruct (g !! p); smap.
  destruct l; smap.
  rewrite gmap_slice_insert. smap.
Qed.

Lemma preservation (threads threads' : list expr) (chans chans' : heap) :
  step threads chans threads' chans' ->
  invariant threads chans ->
  invariant threads' chans'.
Proof.
  unfold invariant.
  intros [i H]. destruct H.
  destruct H as [????????HH].
  intros Hinv.
  destruct HH; rewrite ?right_id.
  - (* Pure step *)
    eapply inv_impl; last done.
    iIntros ([] x) "H"; simpl; eauto.
    iDestruct "H" as "[H1 H2]". iFrame.
    rewrite list_lookup_insert_spec. case_decide; eauto.
    destruct H2. subst. rewrite H0.
    iDestruct (rtyped0_ctx with "H2") as (t) "[H1 H2]"; eauto.
    iApply "H2". iApply pure_step_rtyped0; eauto.
  - (* Send *)
    eapply (inv_exchange (Thread i) (Chan c)); last done; try apply _.
    + intros v x []. iIntros "H".
      destruct v; simpl.
      * rewrite list_lookup_insert_spec. case_decide; naive_solver.
      * setoid_rewrite gmap_slice_alter. case_decide; naive_solver.
    + iIntros (y0) "H". simpl. rewrite H0.
      iDestruct "H" as (HH) "H".
      iDestruct (rtyped0_ctx with "H") as (t) "[H1 H2]"; eauto. simpl.
      iDestruct "H1" as (n r t' i' [-> ->]) "[H1 H1']".
      iDestruct "H1" as (r0 ?) "H1". simplify_eq.
      iExists _. iFrame.
      iIntros (x) "H". simpl in *.
      iDestruct "H" as (σs Hσs) "H".
      iExists (p,r i').
      rewrite list_lookup_insert; last by eapply lookup_lt_Some.
      iSplitL "H2".
      * iIntros "H1".
        iSplit; eauto.
        iApply "H2". simpl. eauto.
      * iExists (<[ p := r i' ]> σs).
        iSplit.
        -- iPureIntro. eapply map_to_multiset_update. done.
        -- rewrite gmap_slice_push.
           eapply map_to_multiset_lookup in Hσs.
           iApply bufs_typed_push; eauto with iFrame.
  - (* Receive *)
    eapply (inv_exchange (Thread i) (Chan c)); last done; try apply _.
    + intros v x []. iIntros "H".
      destruct v; simpl.
      * rewrite list_lookup_insert_spec. case_decide; naive_solver.
      * iDestruct "H" as (σs) "H". iExists σs.
        erewrite gmap_slice_pop_ne; last done; eauto.
    + iIntros (y0) "H". simpl. rewrite H0.
      iDestruct "H" as (HH) "H".
      iDestruct (rtyped0_ctx with "H") as (t) "[H1 H2]"; eauto. simpl.
      iDestruct "H1" as (n t' r Q) "H1".
      iDestruct "H1" as (r0 HH') "H1". simplify_eq.
      iExists _. iFrame.
      iIntros (x) "H". simpl.
      iDestruct "H" as (σs Hσs) "H".
      eapply map_to_multiset_lookup in Hσs as Hp.
      apply gmap_slice_pop in H1.
      iDestruct (bufs_typed_pop with "H") as (i' ?) "[Hv H]"; eauto.
      subst. rewrite list_lookup_insert; last by eapply lookup_lt_Some.
      iExists (q, r i').
      iSplitL "H2 Hv".
      * iIntros "H1".
        iSplit; eauto.
        iApply "H2". simpl. simplify_eq.
        remember (SumNT n (λ i : fin n, PairT (ChanT (r i)) (t' i))).
        inversion Q; simplify_eq.
        iExists _,_,_. iSplit; first done.
        specialize (H2 i'). simpl in *.
        inversion H2; simplify_eq.
        iExists _,_. iSplit; first done.
        rewrite -H7. iFrame.
        inversion H6. simplify_eq.
        iExists _. iSplit; first done. unfold own_ep. simpl. rewrite H8 //.
      * iExists (<[ q := r i' ]> σs). iFrame. iPureIntro.
        by eapply map_to_multiset_update.
  - (* Close *)
    eapply (inv_dealloc (Thread i) (Chan c)); last done; try apply _.
    + intros v x []. iIntros "H".
      destruct v; simpl.
      * rewrite list_lookup_insert_spec. case_decide; naive_solver.
      * setoid_rewrite gmap_slice_delete. case_decide; naive_solver.
    + iIntros (y0) "H". simpl. rewrite H0.
      iDestruct "H" as (HH) "H".
      iDestruct (rtyped0_ctx with "H") as (t) "[H1 H2]"; eauto. simpl.
      iDestruct "H1" as (->) "H1".
      iDestruct "H1" as (r0 HH') "H1". simplify_eq.
      iExists _. iFrame. simpl.
      iIntros (x) "H".
      iDestruct "H" as (σs Hσs) "H".
      rewrite list_lookup_insert; last by eapply lookup_lt_Some.
      iSplitL "H2".
      * iSplit; eauto. by iApply "H2".
      * iExists (delete p σs).
        iSplit.
        -- iPureIntro. by eapply map_to_multiset_delete.
        -- rewrite gmap_slice_delete. case_decide; simplify_eq.
           apply map_to_multiset_lookup in Hσs.
           by iApply bufs_typed_dealloc.
  - (* Fork *)
    eapply (inv_alloc_lrs (Thread i) (Chan c)
              n (λ i, Thread (length es + fin_to_nat i))); last done;
      first apply _; first apply _.
    + intros m1 m2. intro HH. simplify_eq.
      eapply fin_to_nat_inj. lia.
    + split_and!; eauto. intros m. split_and; eauto.
      intros HH. simplify_eq.
      apply lookup_lt_Some in H0. lia.
    + intros v' x (Hn1 & Hn2 & Hn3). iIntros "H".
      destruct v'; simpl.
      * iDestruct "H" as "[? H]". iFrame.
        rewrite lookup_app list_lookup_insert_spec list.insert_length.
        case_decide.
        { destruct H3. simplify_eq. }
        destruct (es !! n0) eqn:E; eauto.
        unfold init_threads.
        rewrite fin_list_lookup_ne; eauto.
        cut (n0 - length es < n -> False); try lia.
        intros HH.
        specialize (Hn3 (nat_to_fin HH)). eapply Hn3.
        f_equal. rewrite fin_to_nat_to_fin.
        eapply lookup_ge_None in E. lia.
      * iDestruct "H" as (σs Hσs) "H".
        iExists σs. iSplit; eauto.
        rewrite gmap_slice_union gmap_slice_unslice.
        case_decide; simplify_eq.
        rewrite left_id //.
    + iIntros (x) "H". simpl.
      iDestruct "H" as (σs Hσs) "H".
      assert (gmap_slice h c = ∅) as ->.
      {
        eapply map_eq. intro. rewrite gmap_slice_lookup H1 lookup_empty //.
      }
      iDestruct (bufs_typed_empty_inv with "H") as "H".
      iDestruct "H" as %HH.
      iPureIntro. subst. rewrite map_to_multiset_empty in Hσs. done.
    + iIntros (m x) "H". simpl.
      iDestruct "H" as "[H1 H]". iFrame.
      destruct (es !! (length es + m)) eqn:E; eauto.
      eapply lookup_lt_Some in E. lia.
    + iIntros (y0) "H". simpl. rewrite H0.
      iDestruct "H" as (HH) "H".
      iDestruct (rtyped0_ctx with "H") as (t) "[H1 H2]"; eauto. simpl.
      iDestruct "H1" as (σs [Hteq Hcons]) "H1".
      iExists (0, σs 0%fin).
      iExists (λ m, (S (fin_to_nat m), σs (FS m))).
      iSplitL "H2".
      {
        rewrite lookup_app list_lookup_insert; eauto using lookup_lt_Some.
        iIntros "H".
        iSplit; eauto. iApply "H2". simpl.
        remember (ChanT (σs 0%fin)).
        inversion Hteq; simplify_eq.
        iExists _. iSplit; first done.
        rewrite -H3 //.
      }
      iSplitR.
      {
        iExists (fin_gmap (S n) σs).
        rewrite gmap_slice_union.
        assert (gmap_slice h c = ∅) as ->.
        { eapply map_eq. intro. rewrite gmap_slice_lookup lookup_empty //. }
        iSplit.
        { iPureIntro. rewrite <-fin_multiset_gmap.
          rewrite fin_multiset_S //. }
        rewrite gmap_slice_unslice. case_decide; simplify_eq.
        rewrite right_id.
        iApply bufs_typed_init; eauto.
      }
      iApply (big_sepS_impl with "H1"). iModIntro.
      iIntros (m _) "Ht Ho".
      iSplit; eauto.
      rewrite lookup_app_r. 2: { rewrite list.insert_length. lia. }
      rewrite list.insert_length.
      replace (length es + m - length es) with (fin_to_nat m) by lia.
      rewrite fin_list_lookup H2.
      simpl.
      remember (ChanT (σs 0%fin)).
      inversion Hteq; simplify_eq.
      eauto with iFrame.
Qed.

Lemma preservationN (threads threads' : list expr) (chans chans' : heap) :
  steps threads chans threads' chans' ->
  invariant threads chans ->
  invariant threads' chans'.
Proof. induction 1; eauto using preservation. Qed.

Lemma invariant_init (e : expr) :
  typed ∅ e UnitT -> invariant [e] ∅.
Proof.
  intros H.
  eapply inv_impl; last eauto using inv_init.
  intros. simpl. iIntros "[% H]".
  unfold state_inv. destruct v.
  - destruct n; simpl.
    + subst. iSplit; eauto.
      iApply rtyped_rtyped0_iff.
      iApply typed_rtyped. done.
    + subst. iFrame. eauto.
  - iExists ∅.
    iSplit; first done. rewrite gmap_slice_empty.
    by iApply bufs_typed_empty.
Qed.

Lemma invariant_holds e threads chans :
  typed ∅ e UnitT -> steps [e] ∅ threads chans -> invariant threads chans.
Proof. eauto using invariant_init, preservationN. Qed.