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
    (* | rproj_buf_skip n i q r t G σ :
        p ≠ r -> (∀ i, rproj p (G i) σ) -> (∀ i, roccurs_in p (G i)) ->
          rproj p (BufMessageR n i q r t G) σ *)
    | rproj_continue G σ :
        proj r G σ -> rproj r (ContinueR G) σ.
(*
  Fixpoint bufproj (r : participant) (G : rglobal_type) (buf : gmap participant bufT) : rProp :=
    match G with
    | MessageR n p q t G' =>
        ⌜⌜ r = q -> buf !!  ∀ i, bufproj r (G' i) buf
    | BufMessageR n i p q t G' =>
        if decide (r = q) then
          ∃ v, ⌜⌜ True ⌝⌝ ∗ val_typed v (t i) ∗ bufproj r (G' i) buf
        else
          bufproj r (G' i) buf
    | ContinueR G' => ⌜⌜ ∀ p, buf !! p = None ∨ buf !! p = Some [] ⌝⌝
                              (* (¬ occurs_in p G' -> buf !! p = None) ⌝⌝ *)
    end.

  Fixpoint bufprojs (G : rglobal_type) (bufs : gmap participant (gmap participant bufT)) : rProp :=
    match G with
    | MessageR n p q t G' => True
    | BufMessageR n i p q t G' => True
    | ContinueR G' => True
    end.

  Definition bufs_typed (bufs : gmap participant (gmap participant bufT))
                        (σs : gmap participant session_type) : rProp :=
    ∃ G : rglobal_type,
      ⌜⌜ ∀ p, roccurs_in p G -> is_Some (bufs !! p) ⌝⌝ ∗
      [∗ map] p ↦ buf;σ ∈ bufs;σs, ⌜⌜ rproj p G σ ⌝⌝ ∗ bufproj p G buf.

  Definition bufs_typed' (bufs : gmap participant (gmap participant bufT))
                        (σs : gmap participant session_type) : rProp :=
    ∃ G : rglobal_type,
      ⌜⌜ dom (gset _) bufs = dom (gset _) σs ∧           (* ugly *)
         ∀ p, rproj p G (default EndT (σs !! p)) ⌝⌝ ∗
         bufprojs G bufs.

  Definition bufs_typed'' (bufs : gmap participant (gmap participant bufT))
                        (σs : gmap participant session_type) : rProp :=
    ∃ G : rglobal_type,
      ⌜⌜ dom (gset _) bufs = dom (gset _) σs ∧           (* ugly *)
         ∀ p, rproj p G (default EndT (σs !! p)) ⌝⌝ ∗
         [∗ map] p ↦ buf ∈ bufs, bufproj p G buf.

 *)

  Definition bufs_typed (bufs : bufsT participant participant entryT)
                        (σs : gmap participant session_type) : rProp.
  Admitted.
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
    bufs_typed (alter (alter (λ buf, buf ++ [(fin_to_nat i,v)]) p) q bufss)
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
  Admitted.

  Lemma bufs_typed_dealloc bufss σs p :
    σs !! p ≡ Some EndT ->
    bufs_typed bufss σs ⊢
    bufs_typed (delete p bufss) (delete p σs).
  Proof.
  Admitted.

  Lemma bufs_typed_empty  :
    emp ⊢ bufs_typed ∅ ∅.
  Proof.
  Admitted.

  Lemma bufs_typed_empty_inv σs :
    bufs_typed ∅ σs ⊢ ⌜⌜ σs = ∅ ⌝⌝.
  Proof.
  Admitted.

  Lemma bufs_typed_init n σs :
    consistent n σs ->
    emp ⊢ bufs_typed (init_chans n) (fin_gmap n σs).
  Proof.
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
  Admitted.

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
        -- rewrite gmap_slice_alter.
           case_decide;simplify_eq.
           eapply map_to_multiset_lookup in Hσs.
           iApply bufs_typed_push; eauto with iFrame.
  - (* Receive *)
    eapply (inv_exchange (Thread i) (Chan c)); last done; try apply _.
    + intros v x []. iIntros "H".
      destruct v; simpl.
      * rewrite list_lookup_insert_spec. case_decide; naive_solver.
      * setoid_rewrite gmap_slice_insert. case_decide; naive_solver.
    + iIntros (y0) "H". simpl. rewrite H0.
      iDestruct "H" as (HH) "H".
      iDestruct (rtyped0_ctx with "H") as (t) "[H1 H2]"; eauto. simpl.
      iDestruct "H1" as (n t' r Q) "H1".
      iDestruct "H1" as (r0 HH') "H1". simplify_eq.
      iExists _. iFrame.
      iIntros (x) "H". simpl.
      iDestruct "H" as (σs Hσs) "H".
      eapply map_to_multiset_lookup in Hσs as Hp.
      iDestruct (bufs_typed_pop with "H") as (i' ?) "[Hv H]"; eauto.
      { rewrite gmap_slice_lookup //. }
      subst. rewrite list_lookup_insert; last by eapply lookup_lt_Some.
      iExists (p, r i').
      iSplitL "H2 Hv".
      * iIntros "H1".
        iSplit; eauto.
        iApply "H2". simpl. simplify_eq.
        remember (SumNT n (λ i : fin n, PairT (ChanT (r i)) (t' i))).
        inversion Q; simplify_eq.
        iExists _,_,_. iSplit; first done.
        specialize (H3 i'). simpl in *.
        inversion H3; simplify_eq.
        iExists _,_. iSplit; first done.
        rewrite -H8. iFrame.
        inversion H7. simplify_eq.
        iExists _. iSplit; first done. unfold own_ep. simpl. rewrite H9 //.
      * iExists (<[ p := r i' ]> σs).
        rewrite gmap_slice_insert. case_decide; simplify_eq.
        iFrame. iPureIntro.
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