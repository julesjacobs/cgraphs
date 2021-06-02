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
End bufs_typed.

Section bufs_typed'.
  Definition link_opt (b' : option (list val)) (σ' : option chan_type) :=
    match b',σ' with
    | Some b, Some σ => Some (b,σ)
    | None, None => Some ([], EndT)
    | _, _ => None
    end.

  Definition bufs_typed' (b1' b2' : option (list val)) (σ1' σ2' : option chan_type) : rProp :=
    ∃ b1 b2 σ1 σ2,
      ⌜⌜ link_opt b1' σ1' = Some (b1,σ1) ∧
        link_opt b2' σ2' = Some (b2,σ2) ⌝⌝ ∗
      bufs_typed b1 b2 σ1 σ2.
(*
  Lemma bufs_typed_push'
"H2'" : val_typed y t'
"H" : chan_inv (Some buf) (h !! (c, false)) ({[(false, SendT t' r)]} ⋅ x)
--------------------------------------∗
chan_inv (Some (buf ++ [y])) (h !! (c, false)) ({[(false, r)]} ⋅ x)
 *)
End bufs_typed'.

Section invariant.
  Definition thread_inv (e : expr) (in_l : multiset clabel) : rProp :=
    ⌜⌜ in_l ≡ ε ⌝⌝ ∗ rtyped0 e UnitT.

  Inductive link_σs : option chan_type -> option chan_type -> multiset clabel -> Prop :=
    | link_left r : link_σs (Some r) None {[ (true,r):clabel ]}
    | link_right r : link_σs None (Some r) {[ (false,r):clabel ]}
    | link_left_right r1 r2 x : x ≡ {[ (true,r1):clabel ]} ⋅ {[ (false,r2):clabel ]} ->
          link_σs (Some r1) (Some r2) x.

  Definition chan_inv (b1' b2' : option (list val)) (in_l : multiset clabel) : rProp :=
    ∃ σ1' σ2',
      ⌜⌜ link_σs σ1' σ2' in_l ⌝⌝ ∗
      bufs_typed' b1' b2' σ1' σ2'.

  Global Instance thread_inv_proper e : Proper ((≡) ==> (⊣⊢)) (thread_inv e).
  Proof. solve_proper. Qed.
  Instance thread_inv_params : Params (@thread_inv) 1. Qed.

  Global Instance link_σs_proper σ1' σ2' : Proper ((≡) ==> (iff)) (link_σs σ1' σ2').
  Proof. solve_proper_prepare. Admitted.
  Instance link_σs_params : Params (@link_σs) 2. Qed.

  Global Instance chan_inv_proper b1' b2' : Proper ((≡) ==> (⊣⊢)) (chan_inv b1' b2').
  Proof. Fail solve_proper. Admitted.
  Instance chan_inv_params : Params (@chan_inv) 2. Qed.

  Definition state_inv (es : list expr) (h : heap) (x : object) (in_l : multiset clabel) : rProp :=
    match x with
    | Thread n =>
        thread_inv (default (Val $ UnitV) (es !! n)) in_l
    | Chan n =>
        chan_inv (h !! (n,true)) (h !! (n,false)) in_l
    end.

  Definition invariant (es : list expr) (h : heap) :=
    inv (state_inv es h).
End invariant.

Lemma preservation (threads threads' : list expr) (chans chans' : heap) :
  step threads chans threads' chans' ->
  invariant threads chans ->
  invariant threads' chans'.
Proof.
  intros [].
  destruct H as [????????HH].
  intros Hinv.
  (* unfold invariant in *.
  destruct Hinv as (g & Hwf & Hvs).
  pose proof (Hvs (Thread i)) as Hthr. simpl in Hthr.
  rewrite H0 in Hthr. simpl in Hthr.
  destruct Hthr as [Hthr_in Hthr].
  assert (∃ t Σ1 Σ2, Σ1 ##ₘ Σ2 ∧ (Σ1 ∪ Σ2 = out_edges g (Thread i)) ∧
    holds (rtyped0 e t) Σ1 ε ∧ holds (ctx_typed0 k t UnitT) Σ2 ε)
    as (t & Σ1 & Σ2 & HΣdisj & HΣ & H1 & H2).
  { admit. } *)

  (* (* The following doesn't work since we don't know yet
    what the resources for the thread should become.
    We only know this after destructing HH. *)
  cut (∃ g', cgraph_wf g' ∧
    in_labels g' (Thread i) = ε ∧
    holds (rtyped0 e' t) (out_edges g' (Thread i)) ε ∧
    ∀ v, v ≠ Thread i ->
      state_inv (<[i:=k e']> es ++ ts) h' v (in_labels g' v) (out_edges g' v)).
  {
    intros (g' & Hwf' & Hthr_in' & Hthr' & Hvs').
    exists g'. split; eauto.
    intros v'.
    destruct (decide (v' = Thread i)); last by eauto.
    subst. simpl.
    assert (i < length es) by (eapply lookup_lt_Some; eauto).
    rewrite lookup_app_l; last by rewrite insert_length.
    rewrite list_lookup_insert_spec. case_decide; last naive_solver.
    simpl. split; first done.
    eapply (holds_entails (rtyped0 e' t ∗ ctx_typed0 k t UnitT)).
    - rewrite sep_holds.
      admit.
    - iIntros "[H1 H2]".
      iApply (ctx_subst0 with "H2"). done.
  }
  clear H H2 Hthr H0. *)

  destruct HH; rewrite ?right_id.
  - (* Pure step *)
    admit.
    (* exists g. split; first done. intros v.
    specialize (Hvs v).
    destruct v; simpl in *; eauto.
    rewrite list_lookup_insert_spec. case_decide; eauto.
    destruct H4; subst.
    simpl. split; eauto.
    eapply (holds_entails (rtyped0 e' t ∗ ctx_typed0 k t UnitT)).
    + admit.
    + iIntros "[H1 H2]".
      by iApply (ctx_subst0 with "H2"). *)
  - (* Send *)
    eapply (inv_exchange (Thread i) (Chan c.1)); last done.
    + intros v x []. iIntros "H".
      destruct v; simpl.
      * rewrite list_lookup_insert_spec. case_decide; naive_solver.
      * rewrite !lookup_insert_spec. repeat case_decide; eauto; destruct c; simpl in *; simplify_eq.
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
      * rewrite !lookup_insert_spec; repeat case_decide; destruct b; simplify_eq.
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