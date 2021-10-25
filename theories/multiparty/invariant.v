Require Export diris.cgraphs.genericinv.
Require Export diris.multiparty.langdef.
Require Export diris.multiparty.rtypesystem.
Require Export diris.multiparty.mutil.

Section bufs_typed.

  Definition bufs_typed (bufs : gmap participant (gmap participant (list val)))
                        (σs : gmap participant session_type) : rProp.
  Admitted.
  (* Idea: finish the proof while admitting all lemmas about bufs_typed. *)
  (* Figure out bufs_typed later. *)
  (* We need lemmas for preservation and a lemma for progress. *)
  (* For progress we need that everyone receiving on empty buffers can't happen. *)
  (* Might be able to get a tighter result: even a partial deadlock within
     a single multiparty session cannot happen. *)

  (*
  Lemma for initialization:
    If consistent σs then emp ⊢ bufs_typed empty_bufs σs

  Lemma for close:
    If σs is all end, then bufs_typed bufs σs ⊢ emp

  Lemma for send:
    If some type is a send, and we put something in that buffer, then it preserves bufs_typed

  Lemma for receive:
    If some type is a recv, and we take something out of that buffer, then it preserves bufs_typed

  Lemma for progress:
    If there is a buffer still allocated, then there is a participant that
    does not have type recv and that buffer is empty.

  *)

    (* ∃ σs', ⌜⌜ consistent σs' ⌝⌝ ∗ big_sepM3 (λ _, buf_typed) bufs σs' σs. *)

  (*
  Global Instance bufs_typed_params : Params (@bufs_typed) 2 := {}.
  Global Instance bufs_typed_proper b1 b2 : Proper ((≡) ==> (≡) ==> (≡)) (bufs_typed b1 b2).
  Proof. solve_proper. Qed.
  *)
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



Lemma bufs_typed_push (bufss : gmap participant (gmap participant (list val)))
                      (σs : gmap participant session_type)
                      (p q : participant) (t : type) r v :
  σs !! p ≡ Some (SendT q t r) ->
  val_typed v t ∗ bufs_typed bufss σs ⊢
  bufs_typed (alter (alter (λ buf, buf ++ [v]) p) q bufss) (<[p:=r]> σs).
Proof.
Admitted.

Lemma bufs_typed_pop (σs : gmap participant session_type)
  (bufss : gmap participant (gmap participant (list val)))
  (bufs : gmap participant (list val))
  (buf : list val) (p q : participant) (v : val) (t : type) (s : session_type) :
  σs !! p ≡ Some (RecvT q t s) ->
  bufss !! p = Some bufs ->
  bufs !! q = Some (v :: buf) ->
  bufs_typed bufss σs ⊢ val_typed v t ∗
  bufs_typed (<[ p := <[ q := buf ]> bufs ]> bufss) (<[ p := s ]> σs).
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

Lemma init_threads_lookup (c : session) n (f : fin n -> val) (i : fin n) :
  init_threads c n f !! fin_to_nat i =
    Some (App (Val (f i)) (Val (ChanV (c, fin_to_nat i)))).
Proof. Admitted.

Lemma init_threads_lookup_ne (c : session) n (f : fin n -> val) (i : nat) :
  i >= n -> init_threads c n f !! i = None.
Proof. Admitted.

Lemma gmap_slice_init_chans_ne c c' n :
  c ≠ c' -> gmap_slice (init_chans c n) c' = ∅.
Proof. Admitted.

Lemma fin_multiset_gmap {A:ofe} n (f : fin n -> A) :
  fin_multiset n (λ m, (fin_to_nat m, f m)) ≡ map_to_multiset (fin_gmap n f).
Proof.
Admitted.

Lemma bufs_typed_init n i σs :
  consistent n σs ->
  emp ⊢ bufs_typed (gmap_slice (init_chans i n) i) (fin_gmap n σs).
Proof.
Admitted.

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
      iDestruct "H1" as (r t' ->) "[H1 H1']".
      iDestruct "H1" as (r0 ?) "H1". simplify_eq.
      iExists _. iFrame.
      iIntros (x) "H". simpl in *.
      iDestruct "H" as (σs Hσs) "H".
      iExists (p,r).
      rewrite list_lookup_insert; last by eapply lookup_lt_Some.
      iSplitL "H2".
      * iIntros "H1".
        iSplit; eauto.
        iApply "H2". simpl. eauto.
      * iExists (<[ p := r ]> σs).
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
      iDestruct "H1" as (t' r ->) "H1".
      iDestruct "H1" as (r0 HH') "H1". simplify_eq.
      iExists _. iFrame.
      iIntros (x) "H". simpl.
      iDestruct "H" as (σs Hσs) "H".
      iExists (p, r).
      rewrite list_lookup_insert; last by eapply lookup_lt_Some.
      eapply map_to_multiset_lookup in Hσs as Hp.
      iDestruct (bufs_typed_pop with "H") as "[Hv H]"; eauto.
      { rewrite gmap_slice_lookup //. }
      iSplitL "H2 Hv".
      * iIntros "H1".
        iSplit; eauto.
        iApply "H2". simpl.
        iExists _,_. iSplit; first done.
        eauto with iFrame.
      * iExists (<[ p := r ]> σs).
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
    eapply (inv_alloc_lrs (Thread i) (Chan i0)
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
        rewrite lookup_app list_lookup_insert_spec insert_length.
        case_decide.
        { destruct H3. simplify_eq. }
        destruct (es !! n0) eqn:E; eauto.
        rewrite init_threads_lookup_ne; eauto.
        cut (n0 - length es < n -> False); try lia.
        intros HH.
        specialize (Hn3 (nat_to_fin HH)). eapply Hn3.
        f_equal. rewrite fin_to_nat_to_fin.
        eapply lookup_ge_None in E. lia.
      * iDestruct "H" as (σs Hσs) "H".
        iExists σs. iSplit; eauto.
        rewrite gmap_slice_union gmap_slice_init_chans_ne ?left_id //.
        intros ->. simplify_eq.
    + iIntros (x) "H". simpl.
      iDestruct "H" as (σs Hσs) "H".
      assert (gmap_slice h i0 = ∅) as ->.
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
      iDestruct "H1" as (σs [-> Hcons]) "H1".
      iExists (λ m, (fin_to_nat m, σs m)).
      iSplitL "H2".
      {
        rewrite lookup_app list_lookup_insert; eauto using lookup_lt_Some.
        iSplit; eauto. iApply "H2". done.
      }
      iSplitR.
      {
        iExists (fin_gmap n σs).
        rewrite gmap_slice_union.
        assert (gmap_slice h i0 = ∅) as ->.
        { eapply map_eq. intro. rewrite gmap_slice_lookup lookup_empty //. }
        rewrite right_id fin_multiset_gmap.
        iSplit; first done.
        iApply bufs_typed_init; eauto.
      }
      iApply (big_sepS_impl with "H1"). iModIntro.
      iIntros (m _) "Ht Ho".
      iSplit; eauto.
      rewrite lookup_app_r. 2: { rewrite insert_length. lia. }
      rewrite insert_length.
      replace (length es + m - length es) with (fin_to_nat m) by lia.
      rewrite init_threads_lookup H2.
      simpl. eauto with iFrame.
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