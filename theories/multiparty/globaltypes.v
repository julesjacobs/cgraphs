From cgraphs.multiparty Require Export invariant.

(* Global types *)
(* ============ *)

(* This is section 6 in the paper. *)
(* This file contains definitions and theorems to show consistency of multiparty session types using global types. *)
(* In particular, we define the notion of global type consistency (the consistent_gt predicate), *)
(* and show that it implies the consistency notion used in the typing rules (the consistent predicate). *)

CoInductive global_type : Type :=
  | Message n : participant -> participant ->
                (fin n -> type) -> (fin n -> global_type) -> global_type
  | EndG : global_type.

Inductive occurs_in (r : participant) : global_type -> Prop :=
  | oi_here_sender n q t g : occurs_in r (Message n r q t g)
  | oi_here_receiver n p t g : occurs_in r (Message n p r t g)
  | oi_later n p q t g i : occurs_in r (g i) -> occurs_in r (Message n p q t g).

Inductive guarded (r : participant) : global_type -> Prop :=
  | gu_here_sender n q t g : guarded r (Message n r q t g)
  | gu_here_receiver n p t g : guarded r (Message n p r t g)
  | gu_later n p q t g : (∀ i, guarded r (g i)) -> guarded r (Message n p q t g).


CoInductive proj (r : participant) : global_type -> session_type -> Prop :=
  | proj_send n q t G σ :
      r ≠ q -> (∀ i, proj r (G i) (σ i)) ->
        proj r (Message n r q t G) (SendT n q t σ)
  | proj_recv n p t G σ :
      r ≠ p -> (∀ i, proj r (G i) (σ i)) ->
        proj r (Message n p r t G) (RecvT n p t σ)
  | proj_skip n p q t G σ :
      r ≠ p -> r ≠ q -> (∀ i, proj r (G i) σ) -> (∀ i, guarded r (G i)) ->
        proj r (Message (S n) p q t G) σ
  | proj_end G :
      ¬ occurs_in r G -> proj r G EndT.

Definition consistent_gt n (σs : fin n -> session_type) :=
  ∃ G : global_type,
    (∀ i, proj (fin_to_nat i) G (σs i)) ∧
    (∀ j, j >= n -> proj j G EndT).



(* Proof that [consistent_gt n σs] implies [consistent n σs] *)
(* ========================================================= *)

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

Inductive sbufprojs : rglobal_type -> sbufsT -> Prop :=
  | bp_skip n p q ts Gs bufs :
      pop p q bufs = None -> (∀ i, sbufprojs (Gs i) bufs) ->
      sbufprojs (MessageR n None p q ts Gs) bufs
  | bp_here n p q i bufs bufs' ts Gs :
      pop p q bufs = Some ((fin_to_nat i, ts i), bufs') ->
      sbufprojs (Gs i) bufs' ->
      sbufprojs (MessageR n (Some i) p q ts Gs) bufs
  | bp_end G' bufs : bufs_empty bufs -> sbufprojs (ContinueR G') bufs.


Definition sbufs_typed_gt (bufs : bufsT participant participant sentryT)
                      (σs : gmap participant session_type) :=
  dom_valid bufs (dom σs) ∧
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

Lemma pushUG_bufs p q n i t G G' bufs :
  pushUG p q n i t G G' -> bufs_empty bufs -> is_present p q bufs ->
  sbufprojs G' (push p q (fin_to_nat i,t) bufs).
Proof.
  induction 1; eauto using pop_push_None, pop_push_single, sbufprojs.
Qed.

Lemma pushG_bufs p q n i G G' bufs t :
  pushG p q n i t G G' -> is_present p q bufs ->
  sbufprojs G bufs ->
  sbufprojs G' (push p q (fin_to_nat i,t) bufs).
Proof.
  intros Hpush. revert bufs. induction Hpush; intros bufs Hpres Hsb; inv Hsb;
  eauto using sbufprojs, pushUG_bufs, pop_push_single, pop_is_present, pop_push_Some, pop_push_None.
Qed.



Lemma sbufs_typed_gt_push (bufss : bufsT participant participant sentryT)
                      (σs : gmap participant session_type)
                      (n : nat) (i : fin n) (p q : participant) ts ss :
  σs !! p = Some (SendT n q ts ss) ->
  sbufs_typed_gt bufss σs ->
  sbufs_typed_gt (push p q (fin_to_nat i,ts i) bufss) (<[p:=ss i]> σs).
Proof.
  intros Hp [Hdb [G [Hprojs Hsb]]].
  split. { rewrite dom_insert_lookup_L; eauto.
            apply dom_valid_push; eauto. apply elem_of_dom; eauto. }
  pose proof (Hprojs p) as Hproj. rewrite Hp in Hproj. simpl in *.
  edestruct send_pushG as [G' H]; first done.
  exists G'. split.
  - intros r. rewrite lookup_insert_spec.
    case_decide; subst; simpl; last eauto using pushG_other.
    eapply pushG_send; eauto.
  - eapply pushG_bufs; eauto.
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

Lemma sbufprojs_popG (G : rglobal_type)
  (bufs bufs' : bufsT participant participant sentryT)
  (n : nat) (p q : participant) t i ts ss :
  rproj q G (RecvT n p ts ss) ->
  pop p q bufs = Some((i,t),bufs') ->
  sbufprojs G bufs -> ∃ G' i', i = fin_to_nat i' ∧ popG p q n i' (ts i') G G'.
Proof.
  intros Hp. revert bufs bufs'. induction G; intros bufs bufs' Hpop Hsb; inv Hsb.
  - inv Hp.
    assert (∀ j, ∃ G' i', i = fin_to_nat i' ∧ popG p q n i' (ts i') (r j) G') as Q.
    { intros. edestruct H; eauto. }
    apply fin_choice in Q as [Gs' HG].
    destruct (HG 0%fin) as [j []]. subst.
    eexists _,_; split; eauto.
    econstructor; eauto. intros. edestruct HG as [? []].
    simplify_eq. eauto.
  - inv Hp.
    + eexists _,_. rewrite Hpop in H7. simplify_eq.
      split; eauto using pop_here.
    + assert (∃ bufs'', pop p q bufs'0 = Some (i, t, bufs'')) as []; eauto using pop_swap'.
      edestruct H as [G' [i' [-> HG]]]; eauto.
      eexists (MessageR _ _ _ _ _ (λ i, if decide (i = i1) then G' else r i)),_.
      split; eauto. econstructor; eauto. sdec. intros. sdec.
  - rewrite H0 in Hpop. sdec.
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

Lemma popG_sbufprojs p q n bufs bufs' t t' i G G' :
  popG p q n i t G G' ->
  pop p q bufs = Some (fin_to_nat i, t', bufs') ->
  sbufprojs G bufs -> t = t' ∧ sbufprojs G' bufs'.
Proof.
  intros HpopG. revert bufs bufs'. induction HpopG; simpl; intros bufs bufs' Hpop Hsb;
  inv Hsb; eauto using sbufprojs.
  - edestruct H1; eauto. clear H3. subst.
    split; eauto.
    econstructor; eauto using pop_pop_None.
    intros. edestruct H1; eauto.
  - assert (∃ bufs'' : sbufsT, pop p q bufs'0 = Some (fin_to_nat i,t', bufs'')) as []
      by eauto using pop_swap'.
    edestruct IHHpopG; [|eauto|]; eauto. subst.
    split; eauto. econstructor; eauto using pop_commute.
    Unshelve. exact 0%fin.
Qed.

Lemma sbufs_typed_gt_pop (σs : gmap participant session_type)
  (bufs bufs' : bufsT participant participant sentryT)
  (n : nat) (p q : participant) t i ts ss :
  σs !! q = Some (RecvT n p ts ss) ->
  pop p q bufs = Some((i,t),bufs') ->
  sbufs_typed_gt bufs σs -> ∃ i', i = fin_to_nat i' ∧ t = ts i' ∧
    sbufs_typed_gt bufs' (<[ q := ss i' ]> σs).
Proof.
  intros Hp Hpop [Hdv [G [Hprojs Hsb]]].
  pose proof (Hprojs q) as Hproj. rewrite Hp in Hproj. simpl in *.
  edestruct sbufprojs_popG as (G' & i' & Q & HpopG); eauto. subst.
  eexists; split; eauto.
  edestruct popG_sbufprojs; eauto. subst.
  split; eauto.
  split. { rewrite dom_insert_lookup_L; eauto. eapply dom_valid_pop; eauto. }
  exists G'. split; eauto.
  intros r. smap; eauto using popG_other, popG_recv.
Qed.

Lemma sbufs_gt_Some_present σs p q n ts ss sbufs (i : fin n) :
  σs !! p = Some (SendT n q ts ss) ->
  sbufs_typed_gt sbufs σs ->
  is_present p q sbufs.
Proof.
  intros Hp [Hdv [G [Hprojs bufs]]].
  pose proof (Hprojs p) as Hproj.
  rewrite Hp in Hproj. simpl in *.
  eapply send_pushG in Hproj as [G' HpushG]. Unshelve. 2: eauto.
  assert (¬ rproj q G EndT); eauto using proj_consistent.
  destruct (σs !! q) eqn:E.
  {
    eapply dom_valid_is_present; eauto; apply elem_of_dom; rewrite ?E ?Hp; eauto.
  }
  specialize (Hprojs q).
  rewrite E in Hprojs. done.
Qed.


Lemma sbufs_typed_gt_dealloc sbufs σs p :
  σs !! p = Some EndT ->
  sbufs_typed_gt sbufs σs ->
  sbufs_typed_gt (delete p sbufs) (delete p σs).
Proof.
  intros Hp [Hdv [G [Hprojs Hsbufs]]].
  split. { rewrite dom_delete_L. eapply dom_valid_delete; done. }
  exists G.
  assert (rproj p G EndT) as Hprojp.
  { specialize (Hprojs p). rewrite Hp in Hprojs. done. }
  split. {intros p'. rewrite lookup_delete_spec. case_decide; subst; eauto. }
  clear Hp Hdv Hprojs σs.
  revert sbufs Hsbufs. induction G; intros; inv Hprojp; inv Hsbufs;
  eauto using sbufprojs,pop_delete_None,pop_delete_Some,bufs_empty_delete.
Qed.

Lemma sbufs_typed_gt_end_empty σs p bufs :
  σs !! p = Some EndT ->
  sbufs_typed_gt bufs σs ->
  buf_empty bufs p.
Proof.
  intros Hp [Hdv [G [Hprojs Hsb]]].
  specialize (Hprojs p).
  rewrite Hp in Hprojs. simpl in *.
  clear Hdv.
  induction Hsb; inv Hprojs; eauto using bufs_empty_buf_empty,buf_empty_pop.
  Unshelve. exact 0%fin.
Qed.

Lemma sbufs_typed_gt_empty : sbufs_typed_gt ∅ ∅.
Proof.
  split. { rewrite dom_empty_L. apply dom_valid_empty. }
  exists (ContinueR EndG). split.
  - intros p. rewrite lookup_empty /=.
    constructor. constructor. intros H. inversion H.
  - econstructor. intros ??. unfold pop. rewrite lookup_empty //.
Qed.

Lemma sbufs_typed_gt_empty_inv σs :
  sbufs_typed_gt ∅ σs -> σs = ∅.
Proof.
  intros [Hdv [G [Hprojs Hsbufs]]].
  apply dom_valid_empty_inv in Hdv.
  apply dom_empty_iff_L in Hdv. done.
Qed.

Lemma sbufs_typed_gt_progress bufss σs :
  sbufs_typed_gt bufss σs -> bufss = ∅ ∨ can_progress bufss σs.
Proof.
  intros [Hdv [G [Hprojs Hsbufs]]].
  inv Hsbufs.
  - right.
    unfold can_progress.
    specialize (Hprojs p).
    exists p.
    destruct (σs !! p); last (inversion Hprojs; simplify_eq).
    eexists _; split; first done.
    destruct s; eauto. simpl in *.
    inversion Hprojs; simplify_eq.
  - right.
    specialize (Hprojs q).
    unfold can_progress.
    exists q.
    destruct (σs !! q); last (inversion Hprojs; simplify_eq). simpl in *.
    exists s. split; eauto.
    destruct s; eauto.
    inv Hprojs; eauto.
  - destruct (classic (bufss = ∅)) as [|Q]; eauto.
    eapply map_choose in Q as [p [x Hp]].
    right. unfold can_progress.
    destruct G'.
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
        eapply dom_valid_same_dom; eauto. }
      eexists. split; first done.
      destruct s; eauto.
      simpl in *.
      inversion Hprojs; simplify_eq.
      inversion H1; simplify_eq.
Qed.

Lemma sbufs_typed_gt_recv bufss σs p :
  is_Some (σs !! p) ->
  sbufs_typed_gt bufss σs -> is_Some (bufss !! p).
Proof.
  intros Hp [Hdv [G [Hprojs Hsbufs]]].
  eapply dom_valid_same_dom; eauto.
  apply elem_of_dom. done.
Qed.

Lemma sbufs_typed_gt_dom bufss σs :
  sbufs_typed_gt bufss σs -> dom bufss = dom σs.
Proof.
  intros [Hdv [G [Hprojs Hsbufs]]].
  eapply set_eq. intros.
  eapply dom_valid_same_dom in Hdv. rewrite -Hdv.
  rewrite elem_of_dom. done.
Qed.

Lemma sbufs_typed_gt_subufs_typed bufs σs :
  sbufs_typed_gt bufs σs -> sbufs_typed bufs σs.
Proof.
  revert bufs σs.
  cofix IH.
  intros bufs σs H.
  constructor.
  - intros. split.
    + eapply sbufs_gt_Some_present; eauto.
    + eapply IH. eapply sbufs_typed_gt_push; eauto.
  - intros. edestruct sbufs_typed_gt_pop as (?&?&?&?); eauto.
  (* - intros. eapply sbufs_gt_Some_present; eauto. *)
  - intros. split.
    + eapply sbufs_typed_gt_end_empty; eauto.
    + eapply IH. eapply sbufs_typed_gt_dealloc; eauto.
  - eapply sbufs_typed_gt_progress; eauto.
  - eapply sbufs_typed_gt_dom. done.
Qed.

Lemma sbufs_typed_gt_init n σs :
  consistent_gt n σs ->
  sbufs_typed_gt (init_chans n) (fin_gmap n σs).
Proof.
  intros Hcons.
  destruct Hcons as [G [Hprojs1 Hprojs2]].
  split; first by eauto using dom_valid_init, fin_gmap_dom.
  exists (ContinueR G).
  split.
  - intros p.
    destruct (decide (p < n)).
    + rewrite -(fin_to_nat_to_fin _ _ l).
      rewrite fin_gmap_lookup. simpl.
      eauto using rproj.
    + rewrite fin_gmap_lookup_ne; last lia.
      simpl. eauto using rproj with lia.
  - econstructor. eapply bufs_empty_init_chans.
Qed.


Lemma consistent_gt_consistent n σs :
  consistent_gt n σs -> consistent n σs.
Proof.
  intros H. unfold consistent.
  by eapply sbufs_typed_gt_subufs_typed, sbufs_typed_gt_init.
Qed.

(*
consistent_gt:
l0: ![1]nat.?[1]string.End
l1: ?[0]nat.![0]string.End

with this global type:
G: [1->0]nat.[0->1]string.End

this is not consistent_gt, but it is consistent:
l0: ![1]nat.?[1]string.End
l1: ![0]string.?[0]nat.End

Actris supports this.
*)
