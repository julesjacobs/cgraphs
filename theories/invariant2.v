Require Export diris.langdef.
Require Export diris.cgraph.
Require Export diris.seplogic.
Require Export diris.rtypesystem.
Require Export diris.langlemmas.
(* Require Export diris.genericinv. *)

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

Definition qProp := multiset clabel -> gmap object clabel -> Prop.

Definition thread_inv (e : expr) (in_l : multiset clabel) (out_e : gmap object clabel) :=
  in_l = ε ∧ holds (rtyped0 e UnitT) out_e ε.

(* Inductive link_σ : bool -> option (list val) -> list val -> chan_type -> multiset clabel -> Prop :=
  | link_present (which : bool) buf (σ : chan_type) : link_σ which (Some buf) buf σ {[ (which,σ) : clabel ]}
  | link_absent which : link_σ which None [] EndT ε. *)

Definition link_σ (which : bool) (b' : option (list val)) (b : list val) (σ : chan_type) (x : multiset clabel) :=
  (b' = Some b ∧ x = {[ (which, σ) : clabel]}) ∨ (b' = None ∧ b = [] ∧ σ = EndT ∧ x = ε).

Definition chan_inv (b1' b2' : option (list val)) (in_l : multiset clabel) (out_e : gmap object clabel) :=
  ∃ b1 b2 σ1 σ2 x1 x2,
    in_l ≡ x1 ⋅ x2 ∧
    link_σ true b1' b1 σ1 x1 ∧
    link_σ false b2' b2 σ2 x2 ∧
    holds (bufs_typed b1 b2 σ1 σ2) out_e ε.

Definition state_inv (es : list expr) (h : heap) (x : object) : qProp :=
  match x with
  | Thread n =>
      thread_inv (default (Val $ UnitV) (es !! n))
  | Chan n =>
      chan_inv (h !! (n,true)) (h !! (n,false))
  end.

(*
  ∃ σ1 σ2 b1 b2,
      maybe_have_σ_in h (n,true) b1 σ1 ∗
      maybe_have_σ_in h (n,false) b2 σ2 ∗
      bufs_typed b1 b2 σ1 σ2
  end. *)

Definition invariant (es : list expr) (h : heap) :=
  ∃ g, cgraph_wf g ∧
    ∀ v, state_inv es h v (in_labels g v) (out_edges g v).


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



Lemma preservation (threads threads' : list expr) (chans chans' : heap) :
  step threads chans threads' chans' ->
  invariant threads chans ->
  invariant threads' chans'.
Proof.
  intros [].
  destruct H as [????????HH].
  intros Hinv.
  unfold invariant in *.
  destruct Hinv as (g & Hwf & Hvs).
  pose proof (Hvs (Thread i)) as Hthr. simpl in Hthr.
  rewrite H0 in Hthr. simpl in Hthr.
  destruct Hthr as [Hthr_in Hthr].
  assert (∃ t Σ1 Σ2, Σ1 ##ₘ Σ2 ∧ (Σ1 ∪ Σ2 = out_edges g (Thread i)) ∧
    holds (rtyped0 e t) Σ1 ε ∧ holds (ctx_typed0 k t UnitT) Σ2 ε)
    as (t & Σ1 & Σ2 & HΣdisj & HΣ & H1 & H2).
  { admit. }

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
    exists g. split; first done. intros v.
    specialize (Hvs v).
    destruct v; simpl in *; eauto.
    rewrite list_lookup_insert_spec. case_decide; eauto.
    destruct H4; subst.
    simpl. split; eauto.
    eapply (holds_entails (rtyped0 e' t ∗ ctx_typed0 k t UnitT)).
    + admit.
    + iIntros "[H1 H2]".
      by iApply (ctx_subst0 with "H2").
  - (* Send *)
    assert (∃ Σ1' σ tv,
      t = ChanT σ ∧
      Σ1 = Σ1' ∪ {[ Chan c.1 := (c.2,SendT tv σ) ]} ∧
      holds (val_typed y tv) Σ1' ε
      ) as (Σ1' & σ & t' & -> & -> & HH).
    { admit. }
    (* Need to figure out that the channel is actually in the heap and
       that we therefore have an invariant with a Σ for it.
       We'll use this Σ in the exchange. *)
    (* exchange (g : cgraph V L) v1 v2 l' e1 e2 := *)
    pose proof (Hvs (Chan c.1)) as Hc.
    simpl in *.

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
    admit.
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