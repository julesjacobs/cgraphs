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

  Definition bufs_typed (b1 b2 : list val) (σ1 σ2 : chan_type) : rProp :=
    ∃ rest, buf_typed b1 σ1 rest ∗
            buf_typed b2 σ2 (dual rest).

  Lemma dual_dual σ : dual (dual σ) = σ.
  Proof.
    induction σ; simpl; rewrite ?IHσ; eauto.
  Qed.

  Lemma bufs_typed_sym b1 b2 σ1 σ2 :
    bufs_typed b1 b2 σ1 σ2 -∗
    bufs_typed b2 b1 σ2 σ1.
  Proof.
    iIntros "H". unfold bufs_typed.
    iDestruct "H" as (rest) "[H1 H2]".
    iExists (dual rest).
    rewrite dual_dual. iFrame.
  Qed.

  Lemma bufs_typed_push b1 b2 σ1 σ2 v t :
    bufs_typed b1 b2 (SendT t σ1) σ2 -∗
    val_typed v t -∗
    ⌜⌜ b1 = [] ⌝⌝ ∗ bufs_typed [] (b2 ++ [v]) σ1 σ2.
  Proof.
    iIntros "Hb Hv".
    unfold bufs_typed. destruct b1. simpl.
    - iSplitL ""; first done.
      iDestruct "Hb" as (rest ->) "H2".
      iExists σ1. iSplitL ""; first done. simpl.
      iInduction b2 as [] "IH" forall (σ2) ""; simpl.
      + iDestruct "H2" as "%". subst. iFrame. done.
      + destruct σ2; eauto.
        iDestruct "H2" as "[H1 H2]". iFrame.
        iApply ("IH" with "H2"). iFrame.
    - iExFalso.
      iDestruct "Hb" as (rest) "[H1 H2]".
      simpl. done.
  Qed.

  Lemma bufs_typed_pop b1 b2 σ1 σ2 (v : val) t :
    bufs_typed (v :: b1) b2 (RecvT t σ1) σ2 -∗
    val_typed v t ∗ bufs_typed b1 b2 σ1 σ2.
  Proof.
    iIntros "H".
    iDestruct "H" as (rest) "[H1 H2]". simpl.
    iDestruct "H1" as "[H1 H3]". iFrame.
    iExists rest. iFrame.
  Qed.

  Definition buf_typed' (buf' : option (list val)) (ct' : option chan_type) (rest : chan_type) : rProp :=
    match buf', ct' with
    | Some buf, Some ct => buf_typed buf ct rest
    | None, None => emp%I
    | _, _ => False
    end.

  Definition both (f : bool -> rProp) : rProp := f true ∗ f false.

  Definition bufs_typed' (b1' b2' : option (list val)) (σ1' σ2' : option chan_type) : rProp :=
    ∃ rest,
      buf_typed' b1' σ1' rest ∗
      buf_typed' b2' σ2' (dual rest).
End bufs_typed.

Section invariant.
  (* Definition thread_inv (es : list expr) (n : nat) (in_l : multiset clabel) : rProp := *)

  Definition opt_to_singleton {T:ofe} (b:bool) (x : option T) : multiset (bool*T) :=
    match x with
    | Some a => {[ (b,a) ]}
    | None => ε
    end.

  Definition mset_σs (σs : gmap bool chan_type) : multiset clabel :=
    opt_to_singleton true (σs !! true) ⋅ opt_to_singleton false (σs !! false).

  (* Definition chan_inv (h : heap) (n : nat) (in_l : multiset clabel) : rProp := *)

  Definition state_inv (es : list expr) (h : heap) (x : object) (in_l : multiset clabel) : rProp :=
    match x with
    | Thread n =>
      ⌜⌜ in_l ≡ ε ⌝⌝ ∗
      match es !! n with
      | Some e => rtyped0 e UnitT
      | None => emp
      end
    | Chan n => ∃ σs,
      ⌜⌜ in_l ≡ mset_σs σs ⌝⌝ ∗
      bufs_typed' (h !! (n,true)) (h !! (n,false)) (σs !! true) (σs !! false)
    end%I.

  Definition invariant (es : list expr) (h : heap) :=
    inv (state_inv es h).
End invariant.

Lemma bufs_typed_sym' b1' b2' σ1' σ2' :
  bufs_typed' b1' b2' σ1' σ2' ⊢
  bufs_typed' b2' b1' σ2' σ1'.
Proof.
  iIntros "H". unfold bufs_typed'.
  iDestruct "H" as (rest) "[H1 H2]".
  iExists (dual rest). rewrite dual_dual. iFrame.
Qed.

Lemma bufs_typed_wlog (h : heap) (σs : gmap bool chan_type) n b b' :
  bufs_typed' (h !! (n,b)) (h !! (n,negb b)) (σs !! b) (σs !! negb b) ⊢
  bufs_typed' (h !! (n,b')) (h !! (n,negb b')) (σs !! b') (σs !! negb b').
Proof.
  destruct (decide (b = b')); subst; eauto.
  assert (negb b = b') as ->. { by destruct b,b'. }
  assert (negb b' = b) as ->. { by destruct b,b'. }
  by rewrite bufs_typed_sym'.
Qed.

Lemma preservation (threads threads' : list expr) (chans chans' : heap) :
  step threads chans threads' chans' ->
  invariant threads chans ->
  invariant threads' chans'.
Proof.
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
    eapply (inv_exchange (Thread i) (Chan c.1)); last done.
    + intros v x []. iIntros "H".
      destruct v; simpl.
      * rewrite list_lookup_insert_spec. case_decide; naive_solver.
      * unfold chan_inv, bufs_typed'. setoid_rewrite lookup_insert_spec. repeat case_decide; eauto; destruct c; simpl in *; simplify_eq.
    + iIntros (y0) "H". simpl. rewrite H0. simpl.
      iDestruct "H" as (HH) "H".
      iDestruct (typed0_ctx_typed0 with "H") as "H"; eauto.
      iDestruct "H" as (t) "[H1 H2]". simpl.
      iDestruct "H2" as (r t' ->) "[H2 H2']".
      iDestruct "H2" as (r0 HH') "H2". simplify_eq.
      unfold own_ep. destruct c. simpl.
      iExists _. iFrame.
      iIntros (x) "H".
      iExists (b, r).
      rewrite list_lookup_insert; last by eapply lookup_lt_Some.
      iSplitL "H1".
      * iIntros "H2".
        unfold thread_inv. iSplit; eauto. simpl.
        iApply (ctx_subst0 with "H1"). simpl. eauto.
      * unfold chan_inv.
       rewrite !lookup_insert_spec; repeat case_decide; destruct b; simplify_eq.
        -- simpl in *. rewrite H1.
           unfold chan_inv in *.
           iDestruct "H" as (b1 b2 σ1 σ2 HH2) "H".
           admit.
        -- admit.


    (* Need to figure out that the channel is actually in the heap and
       that we therefore have an invariant with a Σ for it.
       We'll use this Σ in the exchange. *)
    (* exchange (g : cgraph V L) v1 v2 l' e1 e2 := *)
    (* pose proof (Hvs (Chan c.1)) as Hc.
    simpl in Hc.

    eexists (exchange g (Thread i) (Chan c.1) (c.2, σ) _ _).
    simpl in *.
    apply exists_holds in H1 as (r & HH).
    apply exists_holds in HH as (t' & HH).
    apply pure_sep_holds in HH as (-> & HH).
    apply sep_holds in HH.
    destruct c.
    eapply (inv_exchange (v1 := Thread i) (v2 := Chan c)); last done.
    + intros. iIntros "H". destruct v; simpl.
      * rewrite list_lookup_insert_spec. case_decide; naive_solver.
      * unfold maybe_own_σ_in. rewrite !lookup_insert_spec. admit.
    + simpl. rewrite H0. simpl.
      iIntros "H".
      iDestruct (typed0_ctx_typed0 with "H") as (t) "[Hctx Ht]"; eauto.
      simpl.
      iDestruct "Ht" as (r t' ->) "[H1 Hv]".
      iDestruct "H1" as (r0 Heq) "H". simplify_eq.
      iSplitL "H". iFrame. iExact "H". iFrame.

      iDestruct (typed0_ct)
    admit. *)
  - (* Receive *)
    admit.
  - (* Close *)
    destruct (decide (h !! other c = None)).
    + admit.
    + admit.
  - (* Fork *)
    admit.
Admitted.


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
    + admit.
    + unfold thread_inv. simpl. iSplit; eauto.
      iPureIntro. subst. done.
  - rewrite !lookup_empty. unfold chan_inv.
    admit.
Admitted.