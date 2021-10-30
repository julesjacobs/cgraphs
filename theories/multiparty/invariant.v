Require Export diris.cgraphs.genericinv.
Require Export diris.multiparty.langdef.
Require Export diris.multiparty.rtypesystem.
Require Export diris.multiparty.mutil.

Section bufs_typed.

  Inductive rglobal_type : Type :=
    | MessageR n : participant -> participant ->
                  (fin n -> type) -> (fin n -> rglobal_type) -> rglobal_type
    | BufMessageR n : fin n -> participant -> participant ->
                  (fin n -> type) -> (fin n -> rglobal_type) -> rglobal_type
    | ContinueR : global_type -> rglobal_type.

  Inductive roccurs_in (r : participant) : rglobal_type -> Prop :=
    | roi_here_sender n q t g : roccurs_in r (MessageR n r q t g)
    | roi_here_receiver n p t g : roccurs_in r (MessageR n p r t g)
    | roi_buf_receiver n i p t g : roccurs_in r (BufMessageR n i p r t g)
    | roi_later n p q t g :
        r ≠ p -> r ≠ q -> (∀ i, roccurs_in r (g i)) -> roccurs_in r (MessageR n p q t g)
    | roi_buf_later n i p q t g :
        r ≠ q -> (∀ i, roccurs_in r (g i)) -> roccurs_in r (BufMessageR n i p q t g).

  Inductive rproj (r : participant) : rglobal_type -> session_type -> Prop :=
    | rproj_send n q t G σ :
        r ≠ q -> (∀ i, rproj r (G i) (σ i)) ->
          rproj r (MessageR n r q t G) (SendT n q t σ)
    | rproj_recv n p t G σ :
        r ≠ p -> (∀ i, rproj r (G i) (σ i)) ->
          rproj r (MessageR n p r t G) (RecvT n p t σ)
    | rproj_buf_recv n i p t G σ :
        r ≠ p -> (∀ i, rproj r (G i) (σ i)) ->
          rproj r (BufMessageR n i p r t G) (RecvT n p t σ)
    | rproj_skip n p q t G σ :
        r ≠ p -> r ≠ q -> (∀ i, rproj r (G i) σ) ->
          rproj r (MessageR n p q t G) σ
    | rproj_buf_skip n i p q t G σ :
        r ≠ q -> rproj r (G i) σ ->
          rproj r (BufMessageR n i p q t G) σ
    | rproj_continue G σ :
        proj r G σ -> rproj r (ContinueR G) σ.

  Definition bufs_empty (bufs : bufsT participant participant entryT) :=
    ∀ p q, pop p q bufs = None.

  Fixpoint bufprojs (G : rglobal_type) (bufs : bufsT participant participant entryT) : rProp :=
    match G with
    | MessageR n p q t G' =>
        ⌜⌜ pop p q bufs = None ⌝⌝ ∗ ∀ i, bufprojs (G' i) bufs
    | BufMessageR n i p q t G' =>
        ∃ v bufs', ⌜⌜ pop q p bufs = Some ((fin_to_nat i,v), bufs') ⌝⌝ ∗
          val_typed v (t i) ∗ bufprojs (G' i) bufs'
    | ContinueR G' => ⌜⌜ bufs_empty bufs ⌝⌝
    end.

  Definition bufs_typed (bufs : bufsT participant participant entryT)
                        (σs : gmap participant session_type) : rProp :=
    ⌜⌜ dom (gset _) bufs = dom (gset _) σs ⌝⌝ ∗      (* ugly... *)
    ∃ G : rglobal_type,
         ⌜⌜ ∀ p, rproj p G (default EndT (σs !! p)) ⌝⌝ ∗
         bufprojs G bufs.

  (* Definition bufs_typed (bufs : gmap participant (gmap participant bufT))
                        (σs : gmap participant session_type) : rProp :=
    ∃ G : rglobal_type,
      ⌜⌜ ∀ p, roccurs_in p G -> is_Some (bufs !! p) ⌝⌝ ∗
      [∗ map] p ↦ buf;σ ∈ bufs;σs, ⌜⌜ rproj p G σ ⌝⌝ ∗ bufproj p G buf. *)


  (* Definition bufs_typed (bufs : gmap participant (gmap participant bufT))
                        (σs : gmap participant session_type) : rProp :=
    ∃ G : rglobal_type,
      ⌜⌜ dom (gset _) bufs = dom (gset _) σs ∧           (* ugly *)
         ∀ p, rproj p G (default EndT (σs !! p)) ⌝⌝ ∗
         [∗ map] p ↦ buf ∈ bufs, bufproj p G buf. *)

  (*
  Global Instance bufs_typed_params : Params (@bufs_typed) 2 := {}.
  Global Instance bufs_typed_proper b1 b2 : Proper ((≡) ==> (≡) ==> (≡)) (bufs_typed b1 b2).
  Proof. solve_proper. Qed.
  *)

  Lemma bufs_typed_push (bufss : bufsT participant participant entryT)
                        (σs : gmap participant session_type)
                        (n : nat) (i : fin n) (p q : participant) t r v :
    σs !! p ≡ Some (SendT n q t r) ->
    val_typed v (t i) ∗ bufs_typed bufss σs ⊢
    bufs_typed (push q p (fin_to_nat i,v) bufss)
               (<[p:=r i]> σs).
  Proof.
  Admitted.

  Lemma bufs_typed_pop (σs : gmap participant session_type)
    (bufs bufs' : bufsT participant participant entryT)
    (n : nat) (p q : participant) v i t r :
    σs !! p ≡ Some (RecvT n q t r) ->
    pop p q bufs = Some((i,v),bufs') ->
    bufs_typed bufs σs ⊢ ∃ i', ⌜⌜ i = fin_to_nat i' ⌝⌝ ∗
      val_typed v (t i') ∗
      bufs_typed bufs' (<[ p := r i' ]> σs).
  Proof.
    iIntros (Hp Hpop) "H".
    iDestruct "H" as (Hdom G Hprojs) "H".
    iInduction G as [] "IH" forall (bufs Hpop Hdom Hprojs); simpl.
    - admit.
    - iDestruct "H" as (v0 bufs'0 Hpop') "[Hv H]".
      admit.
    - iDestruct "H" as %Hemp. rewrite Hemp in Hpop. simplify_eq.
  Admitted.

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
    iSplit. { iPureIntro. rewrite !dom_delete_L Hdom //. }
    iDestruct "H" as (G Hprojs) "H".
    assert (rproj p G EndT) as Hprojp.
    { specialize (Hprojs p). rewrite Hp in Hprojs. done. }
    iExists G. iSplit.
    { iPureIntro. intros p'. rewrite lookup_delete_spec.
      case_decide; subst; eauto. }
    clear Hp Hdom Hprojs.
    iInduction G as [] "IH" forall (bufss); simpl.
    - iDestruct "H" as (Hpop) "H".
      iSplit; first admit.
      iIntros (i).
      iApply ("IH" with "[%] [H]"); eauto.
      admit.
    - iDestruct "H" as (v bufs' Hpop) "[Hv H]".
      remember (BufMessageR n t p0 p1 t0 r).
      inversion Hprojp; simplify_eq.
      iExists _,_.
      iDestruct ("IH" with "[%] H") as "H". { done. }
      iFrame. admit.
    - iDestruct "H" as %Hbe. iPureIntro.
      admit.
  Admitted.

  Lemma bufs_typed_empty  :
    emp ⊢ bufs_typed ∅ ∅.
  Proof.
    iIntros "_".
    iSplit. { rewrite !dom_empty_L //. }
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
    rewrite dom_empty_L in H.
    symmetry in H.
    apply dom_empty_iff_L in H. subst.
    setoid_rewrite lookup_empty in Hprojs. simpl in *.
    assert (G = ContinueR EndG) as ->.
    { destruct G.
      - specialize (Hprojs p0); inversion Hprojs; simplify_eq.
      - specialize (Hprojs p0); inversion Hprojs; simplify_eq.
      - destruct g; eauto.
        specialize (Hprojs p0); inversion Hprojs; simplify_eq.
        inversion H0; simplify_eq.
        exfalso. apply H. eauto using occurs_in. }
    simpl. eauto.
  Qed.

  Lemma bufs_typed_init n σs :
    consistent n σs ->
    emp ⊢ bufs_typed (init_chans n) (fin_gmap n σs).
  Proof.
    iIntros (Hcons) "_".
    unfold bufs_typed.
    iSplit. { admit. }
    destruct Hcons as [G [Hprosj Hocc]].
    iExists (ContinueR G).
    iSplit.
    - iPureIntro. intros. econstructor.
      destruct (decide (p < n)).
      + rewrite <-(fin_to_nat_to_fin _ _ l).
        rewrite fin_gmap_lookup. simpl. eauto.
      + rewrite fin_gmap_lookup_ne; last lia. simpl.
        econstructor. eauto with lia.
    - simpl. admit.
  Admitted.

  Lemma bufs_typed_recv bufss σs p q n t σ :
    σs !! p ≡ Some (RecvT n q t σ) ->
    bufs_typed bufss σs ⊢ ⌜ ∃ bufs buf,
      bufss !! p = Some bufs ∧
      bufs !! q = Some buf ⌝.
  Proof.
  Admitted.

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
    iIntros "[% H]".
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
  Qed.

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

(*
L ::=(coind)  ![p]t.L | ?[p]t.L | End
G ::=(coind)  [p -> q]t.G | End

consistent L_1 L_2 ... L_n :=
  ∃ G, ∀ i, proj G i L_i       " proj(G,i) = L_i "


global type:        [p -> r]t1 [p -> q]t2 [r -> p]t3 ...

projection onto p:  ![r]t1.    ![q]t2.    ?[r]t3. ...


G_r ::=(ind)  [p -> q]t G_r | [p => q]t G_r | G

L = ![q] ?[p] ![q] ?[p] ![q] ?[p] ...

G |->{r} L


[p -> q] [p -> r] [a => b]t ... [a => b]t' [p -> q] [p -> r] [p -> q] [p -> r] [p -> q] [p -> r]

(a,b) : [v, v', ...]
         v : t, v' : t'
*)

(* (h !! (c,b)) !! a *)
Lemma gmap_slice_push `{Countable A,Countable B,Countable C} {V}
  (c : A) (p : B) (q : C) (x : V) (m : bufsT (A*B) C V) :
  gmap_slice (push (c, p) q x m) c = push p q x (gmap_slice m c).
Proof.
  unfold push. rewrite gmap_slice_alter. case_decide; simplify_eq. done.
Qed.

Lemma gmap_slice_pop `{Countable A,Countable B,Countable C} {V}
  (c : A) (p : B) (q : C) (x : V) (m m' : bufsT (A*B) C V) :
  pop (c,p) q m = Some(x,m') ->
  pop p q (gmap_slice m c) = Some(x,gmap_slice m' c).
Proof.
  unfold pop. intros. rewrite gmap_slice_lookup.
  destruct (m !! (c, p)); last simplify_eq.
  destruct (g !! q); last simplify_eq.
  destruct l; simplify_eq.
  rewrite gmap_slice_insert. case_decide; simplify_eq. done.
Qed.

Lemma gmap_slice_pop_ne `{Countable A,Countable B,Countable C} {V}
  (c c' : A) (p : B) (q : C) (x : V) (m m' : bufsT (A*B) C V) :
  c ≠ c' ->
  pop (c,p) q m = Some(x,m') ->
  gmap_slice m c' = gmap_slice m' c'.
Proof.
  unfold pop. intros.
  destruct (m !! (c, p)); last simplify_eq.
  destruct (g !! q); last simplify_eq.
  destruct l; simplify_eq.
  rewrite gmap_slice_insert.
  case_decide; simplify_eq. done.
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
      iExists (p, r i').
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
      * iExists (<[ p := r i' ]> σs). iFrame. iPureIntro.
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