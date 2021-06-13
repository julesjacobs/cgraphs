Require Export diris.langdef.
Require Export diris.cgraph.
Require Export diris.seplogic.
Require Export diris.rtypesystem.
Require Export diris.langlemmas.
Require Export diris.genericinv.

Section bufs_typed.
  Fixpoint buf_typed (buf : list val) (ct : chan_type) (rest : chan_type) : rProp :=
    match buf, ct with
                              (* add owner here *)
    | v::buf', RecvT t ct' => val_typed v t ∗ buf_typed buf' ct' rest
    (* | v::buf', SendT t ct' => ??? *)
    (* Add a rule for this to support asynchrous subtyping *)
    | [], ct => ⌜⌜ rest = ct ⌝⌝
    | _,_ => False
    end.

  Lemma dual_dual σ : dual (dual σ) = σ.
  Proof.
    induction σ; simpl; rewrite ?IHσ; eauto.
  Qed.

  Definition buf_typed' (buf' : option (list val)) (ct' : option chan_type) (rest : chan_type) : rProp :=
    match buf', ct' with
    | Some buf, Some ct => buf_typed buf ct rest
    | None, None => ⌜⌜ rest = EndT ⌝⌝
    | _, _ => False
    end.

  Definition bufs_typed (b1' b2' : option (list val)) (σ1' σ2' : option chan_type) : rProp :=
    ∃ rest,
      buf_typed' b1' σ1' rest ∗
      buf_typed' b2' σ2' (dual rest).
End bufs_typed.

Section invariant.
  Definition opt_to_singleton {T:ofe} (b:bool) (x : option T) : multiset (bool*T) :=
    match x with
    | Some a => {[ (b,a) ]}
    | None => ε
    end.

  Definition mset_σs (σs : gmap bool chan_type) : multiset clabel :=
    opt_to_singleton true (σs !! true) ⋅ opt_to_singleton false (σs !! false).

  Definition state_inv (es : list expr) (h : heap) (x : object) (in_l : multiset clabel) : rProp :=
    match x with
    | Thread n =>
      ⌜⌜ in_l ≡ ε ⌝⌝ ∗
      match es !! n with
      | Some e => rtyped0 e UnitT
      | None => emp
      end
    | Chan n => ∃ σs : gmap bool chan_type,
      ⌜⌜ in_l ≡ mset_σs σs ⌝⌝ ∗
      bufs_typed (h !! (n,true)) (h !! (n,false)) (σs !! true) (σs !! false)
    end%I.

  Definition invariant (es : list expr) (h : heap) := inv (state_inv es h).
End invariant.

Instance state_inv_proper es h v : Proper ((≡) ==> (⊣⊢)) (state_inv es h v).
Proof.
  solve_proper_prepare.
  destruct v.
  - solve_proper.
  - setoid_rewrite H. done.
Qed.
Instance state_inv_params : Params (@state_inv) 3. Defined.

Lemma bufs_typed_sym' b1' b2' σ1' σ2' :
  bufs_typed b1' b2' σ1' σ2' ⊢
  bufs_typed b2' b1' σ2' σ1'.
Proof.
  iIntros "H". unfold bufs_typed.
  iDestruct "H" as (rest) "[H1 H2]".
  iExists (dual rest). rewrite dual_dual. iFrame.
Qed.

Lemma bufs_typed_wlog b b' (h : heap) (σs : gmap bool chan_type) n :
  bufs_typed (h !! (n,b)) (h !! (n,negb b)) (σs !! b) (σs !! negb b) ⊢
  bufs_typed (h !! (n,b')) (h !! (n,negb b')) (σs !! b') (σs !! negb b').
Proof.
  destruct (decide (b = b')); subst; first eauto.
  assert (negb b = b') as ->. { by destruct b,b'. }
  assert (negb b' = b) as ->. { by destruct b,b'. }
  by rewrite bufs_typed_sym'.
Qed.

(* Lemma foo σs b :
  opt_to_singleton true (σs !! true) ⋅ opt_to_singleton false (σs !! false) ≡
  opt_to_singleton true (σs !! b) ⋅ opt_to_singleton false (σs !! negb b). *)


Lemma mset_delete σs b r x :
  {[(b, r):clabel]} ⋅ x ≡ mset_σs σs ->
  x ≡ mset_σs (delete b σs).
Proof.
  intros H. unfold mset_σs in *.
  destruct b; last admit.
  eapply mset_xsplit in H as (e11 & e12 & e21 & e22 & H1 & H2 & H3 & H4).
  simplify_map_eq.
  rewrite H4.
  simplify_map_eq.
  do 2 destruct (_ !! _); simpl in *.
  -  rewrite left_id.

Admitted.

Lemma mset_lookup σs b r x :
  {[(b, r):clabel]} ⋅ x ≡ mset_σs σs ->
  σs !! b = Some r.
Proof.
  intros.
  pose proof (mset_delete _ _ _ _ H).
  assert (b = true) as -> by admit.
  unfold mset_σs in *.
  rewrite lookup_delete in H0.
  rewrite lookup_delete_ne in H0; eauto.
Admitted.

Lemma mset_insert σs x b r r' :
  {[(b, r):clabel]} ⋅ x ≡ mset_σs σs ->
  {[(b, r'):clabel]} ⋅ x ≡ mset_σs (<[b:=r']> σs).
Proof.
  intros H%mset_delete. rewrite H.
  unfold mset_σs.
  rewrite !lookup_delete_spec.
  rewrite !lookup_insert_spec.
  destruct b; simpl.
  - destruct (_ !! _); simpl; eauto.
  - destruct (_ !! _); simpl; eauto.
    rewrite comm. done.
Qed.

Lemma mset_empty :
  mset_σs ∅ = ε.
Proof.
  unfold mset_σs. rewrite !lookup_empty. simpl. done.
Qed.

Lemma mset_empty' σs :
  (∀ b, σs !! b = None) ->
  mset_σs σs = ε.
Proof.
  intros H.
  assert (σs = ∅) as -> by by apply map_empty.
  apply mset_empty.
Qed.

Lemma buf_typed_push v buf t r c :
  val_typed v t ∗
  buf_typed buf c (RecvT t r) ⊢
  buf_typed (buf ++ [v]) c r.
Proof.
  iIntros "[H1 H2]".
  iInduction buf as [] "IH" forall (r c); simpl.
  - iDestruct "H2" as "<-". iFrame. done.
  - destruct c; eauto. iDestruct "H2" as "[H2 H3]".
    iFrame. iApply ("IH" with "H1"). done.
Qed.

Lemma bufs_typed_push b1' t v buf σ2' r :
  val_typed v t ∗
  bufs_typed b1' (Some buf) (Some (SendT t r)) σ2' ⊢
  bufs_typed b1' (Some (buf ++ [v])) (Some r) σ2'.
Proof.
  iIntros "[H1 H2]".
  unfold bufs_typed.
  iDestruct "H2" as (rest) "[H2 H3]".
  destruct b1'; simpl; eauto.
  destruct σ2'; eauto. simpl. destruct l; eauto. simpl.
  iDestruct "H2" as "%". subst. simpl.
  iExists r. iSplit; eauto.
  iApply buf_typed_push. iFrame.
Qed.

Lemma bufs_typed_pop b1 b2' σ1 σ2' (v : val) t :
  bufs_typed (Some (v :: b1)) b2' (Some (RecvT t σ1)) σ2' -∗
  val_typed v t ∗ bufs_typed (Some b1) b2' (Some σ1) σ2'.
Proof.
  iIntros "H".
  iDestruct "H" as (rest) "[H1 H2]". simpl.
  iDestruct "H1" as "[H1 H3]". iFrame.
  iExists rest. iFrame.
Qed.

Lemma bufs_typed_dealloc b2' σ2 :
  bufs_typed (Some []) b2' (Some EndT) σ2 ⊢
  bufs_typed None b2' None σ2.
Proof.
  iIntros "H".
  iDestruct "H" as (rest) "[% H2]". subst.
  iExists _. iFrame. done.
Qed.

Lemma bufs_typed_None σ1 σ2 :
  bufs_typed None None σ1 σ2 ⊢ ⌜⌜ σ1 = None ∧ σ2 = None ⌝⌝.
Proof.
  iIntros "H".
  iDestruct "H" as (rest) "[H1 H2]".
  destruct σ1,σ2; eauto.
Qed.

Lemma bufs_typed_init r :
  emp ⊢ bufs_typed (Some []) (Some []) (Some r) (Some (dual r)).
Proof.
  iIntros "H".
  unfold bufs_typed.
  iExists r; simpl; eauto.
Qed.

Lemma preservation (threads threads' : list expr) (chans chans' : heap) :
  step threads chans threads' chans' ->
  invariant threads chans ->
  invariant threads' chans'.
Proof.
  unfold invariant.
  intros [].
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
    eapply (inv_exchange (Thread i) (Chan c.1)); last done; first apply _; first apply _.
    + intros v x []. iIntros "H".
      destruct v; simpl.
      * rewrite list_lookup_insert_spec. case_decide; naive_solver.
      * setoid_rewrite lookup_insert_spec. repeat case_decide; eauto; destruct c; simpl in *; simplify_eq.
    + iIntros (y0) "H". simpl. rewrite H0.
      iDestruct "H" as (HH) "H".
      iDestruct (rtyped0_ctx with "H") as (t) "[H1 H2]"; eauto. simpl.
      iDestruct "H1" as (r t' ->) "[H1 H1']".
      iDestruct "H1" as (r0 HH') "H1". simplify_eq.
      destruct c. simpl.
      iExists _. iFrame.
      iIntros (x) "H".
      iExists (b, r).
      rewrite list_lookup_insert; last by eapply lookup_lt_Some.
      iSplitL "H2".
      * iIntros "H1".
        iSplit; eauto.
        iApply "H2". simpl.
        eauto with iFrame.
      * iDestruct "H" as (σs H2) "H".
        iExists (<[ b := r ]> σs).
        iSplit.
        -- iPureIntro. by eapply mset_insert.
        -- iApply (bufs_typed_wlog b true).
           iDestruct (bufs_typed_wlog true b with "H") as "H".
           assert (σs !! b = Some (SendT t' r)) as ->
             by by eapply mset_lookup.
           rewrite !lookup_insert_spec.
           repeat case_decide; simplify_eq; try solve [by destruct b].
           rewrite H1.
           iApply bufs_typed_push. iFrame.
  - (* Receive *)
    eapply (inv_exchange (Thread i) (Chan c.1)); last done; first apply _; first apply _.
    + intros v x []. iIntros "H".
      destruct v; simpl.
      * rewrite list_lookup_insert_spec. case_decide; naive_solver.
      * setoid_rewrite lookup_insert_spec. repeat case_decide; eauto; destruct c; simpl in *; simplify_eq.
    + iIntros (y0) "H". simpl. rewrite H0.
      iDestruct "H" as (HH) "H".
      iDestruct (rtyped0_ctx with "H") as (t) "[H1 H2]"; eauto. simpl.
      iDestruct "H1" as (t' r ->) "H1".
      iDestruct "H1" as (r0 HH') "H1". simplify_eq.
      destruct c. simpl.
      iExists _. iFrame.
      iIntros (x) "H".
      iExists (b, r).
      rewrite list_lookup_insert; last by eapply lookup_lt_Some.
      iDestruct "H" as (σs H2) "H".
      iDestruct (bufs_typed_wlog true b with "H") as "H".
      assert (σs !! b = Some (RecvT t' r)) as ->
             by by eapply mset_lookup.
      rewrite H1.
      iDestruct (bufs_typed_pop with "H") as "[Hv H]".
      iSplitL "H2 Hv".
      * iIntros "H1".
        iSplit; eauto.
        iApply "H2". simpl.
        iExists _,_. iSplit; first done.
        eauto with iFrame.
      * iExists (<[ b := r ]> σs).
        iSplit.
        -- iPureIntro. by eapply mset_insert.
        -- iApply (bufs_typed_wlog b true).
           rewrite !lookup_insert_spec.
           repeat case_decide; simplify_eq; try solve [by destruct b].
  - (* Close *)
    eapply (inv_dealloc (Thread i) (Chan c.1)); last done; first apply _; first apply _.
    + intros v x []. iIntros "H".
      destruct v; simpl.
      * rewrite list_lookup_insert_spec. case_decide; naive_solver.
      * setoid_rewrite lookup_delete_spec. repeat case_decide; eauto; destruct c; simpl in *; simplify_eq.
    + iIntros (y0) "H". simpl. rewrite H0.
      iDestruct "H" as (HH) "H".
      iDestruct (rtyped0_ctx with "H") as (t) "[H1 H2]"; eauto. simpl.
      iDestruct "H1" as (->) "H1".
      iDestruct "H1" as (r0 HH') "H1". simplify_eq.
      destruct c. simpl.
      iExists _. iFrame.
      iIntros (x) "H".
      iDestruct "H" as (σs Hσs) "H".
      iDestruct (bufs_typed_wlog true b with "H") as "H".
      rewrite H1.
      assert (σs !! b = Some EndT) as ->
             by by eapply mset_lookup.
      rewrite list_lookup_insert; last by eapply lookup_lt_Some.
      (* iDestruct (bufs_typed_pop with "H") as "[Hv H]". *)
      iSplitL "H2".
      * iSplit; eauto. by iApply "H2".
      * iExists (delete b σs).
        iSplit.
        -- iPureIntro. by eapply mset_delete.
        -- iApply (bufs_typed_wlog b true).
           rewrite !lookup_delete_spec.
           repeat case_decide; simplify_eq; try solve [by destruct b].
  - (* Fork *)
    eapply (inv_alloc_lr (Thread i) (Chan i0) (Thread (length es))); last done;
      first apply _; first apply _.
    + split_and!; eauto. intro. simplify_eq.
      apply lookup_lt_Some in H0. lia.
    + intros v' x []. iIntros "H".
      destruct v'; simpl.
      * rewrite lookup_app_lr.
        rewrite list_lookup_insert_spec.
        rewrite list_lookup_singleton_spec.
        repeat case_decide.
        -- naive_solver.
        -- naive_solver.
        -- destruct H4. exfalso. apply H7.
           f_equal. rewrite insert_length in H6.
           rewrite insert_length in H5. lia.
        -- destruct H4.
           rewrite insert_length in H6.
           rewrite insert_length in H5.
           assert (n > length es) by lia.
           rewrite lookup_ge_None_2; eauto. lia.
      * setoid_rewrite lookup_insert_spec.
        repeat case_decide; simplify_eq.
        destruct H4; simplify_eq.
        rewrite !lookup_insert_ne //.
        intro. simplify_eq.
    + iIntros (x) "H". simpl.
      iDestruct "H" as (σs Hσs) "H".
      rewrite H1 H2.
      iDestruct (bufs_typed_None with "H") as "H".
      iDestruct "H" as "%". iPureIntro.
      rewrite Hσs.
      rewrite mset_empty'; first done.
      intros []; naive_solver.
    + iIntros (x) "[H1 H2]". simpl.
      iFrame. destruct (es !! length es) eqn:E; eauto.
      exfalso.
      eapply lookup_lt_Some in E. lia.
    + iIntros (y0) "H". simpl. rewrite H0.
      iDestruct "H" as (HH) "H".
      iDestruct (rtyped0_ctx with "H") as (t) "[H1 H2]"; eauto. simpl.
      iDestruct "H1" as (r ->) "H1".
      iExists (true,r),(false,dual r).
      iSplitL "H2".
      * iIntros "H". iSplit; eauto.
        rewrite lookup_app_l. 2: {
          rewrite insert_length.
          eapply lookup_lt_Some; eauto.
        }
        rewrite list_lookup_insert; eauto using lookup_lt_Some.
        iApply "H2". simpl.
        eauto.
      * iSplitL "".
        -- iExists {[ true := r; false := dual r ]}.
           iSplit; eauto.
           rewrite !lookup_insert.
           rewrite lookup_insert_ne; eauto.
           rewrite !lookup_insert.
           rewrite lookup_insert_ne; eauto.
           rewrite !lookup_insert.
           by iApply bufs_typed_init.
        -- iIntros "H".
           iSplit; eauto.
           rewrite lookup_app_r. 2: {
             by rewrite insert_length.
           }
           rewrite insert_length.
           replace (length es - length es) with 0 by lia. simpl.
           iExists _. iFrame. eauto.
Qed.


Lemma preservationN (threads threads' : list expr) (chans chans' : heap) :
  steps threads chans threads' chans' ->
  invariant threads chans ->
  invariant threads' chans'.
Proof.
  induction 1; eauto using preservation.
Qed.

Lemma invariant_init (e : expr) :
  typed ∅ e UnitT -> invariant [e] ∅.
Proof.
  intros H.
  eapply inv_impl; last eauto using inv_init.
  intros. simpl. iIntros "[% H]".
  unfold state_inv. destruct v.
  - destruct n; simpl.
    + subst. iSplit; eauto.
      iApply rtyped_rtyped0.
      iApply typed_rtyped. done.
    + subst. iFrame. eauto.
  - rewrite !lookup_empty.
    iExists ∅. unfold bufs_typed. simpl. rewrite !lookup_empty. iFrame.
    iSplit.
    + iPureIntro. subst. unfold mset_σs.
      rewrite !lookup_empty. simpl. done.
    + iExists EndT. done.
Qed.

Lemma invariant_holds e threads chans :
  typed ∅ e UnitT -> steps [e] ∅ threads chans -> invariant threads chans.
Proof.
  eauto using invariant_init, preservationN.
Qed.