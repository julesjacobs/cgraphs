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

Lemma preservation (threads threads' : list expr) (chans chans' : heap) :
  step threads chans threads' chans' ->
  invariant threads chans ->
  invariant threads' chans'.
Proof.
  intros [].
  destruct H as [????????HH].
  intros Hinv.
  unfold invariant in *.
  destruct HH; rewrite ?right_id.
  - (* Pure step *)
    eapply inv_impl; last done.
    iIntros (v) "H". destruct v; simpl; eauto.
    rewrite list_lookup_insert_spec. case_decide; eauto.
    destruct H2; subst. rewrite H0. simpl.
    iDestruct (typed0_ctx_typed0 with "H") as (t) "[Hctx Ht]"; eauto.
    iApply (ctx_subst0 with "Hctx").
    iApply pure_step_rtyped0; eauto.
  - (* Send *)

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