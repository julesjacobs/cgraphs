Require Export diris.langdef.
Require Export diris.cgraph.
Require Export diris.seplogic.
Require Export diris.rtypesystem.
Require Export diris.langlemmas.
Require Export diris.genericinv.

Definition state_inv (es : list expr) (h : heap) (x : object) : hProp :=
  match x with
  | Thread n =>
    match es !! n with
    | Some e => rtyped0 e UnitT
    | None => emp
    end
  | Chan n =>
    maybe_own_σ_in (h !! (n,true)) true
    match h !! (n,true), h !! (n,false) with
    | Some b1, Some b2 => ∃ σ1 σ2, own_in σ1 ∗ own_in σ2 ∗ bufs_typed ???
    | Some b1, None => ???
    | None, Some b2 => ???
    | None, None => emp
    end
  end.

Definition thread_inv (e : expr) (inlabels : list clabel) : hProp object clabel :=
    ⌜⌜ inlabels = [] ⌝⌝ ∗ rtyped0 e UnitT.

Fixpoint buf_typed (buf : list val) (ct : chan_type) (rest : chan_type) : rProp :=
  match buf, ct with
                            (* add owner here *)
  | v::buf', RecvT t ct' => val_typed v t ∗ buf_typed buf' ct' rest
  (* | v::buf', SendT t ct' => ??? *)
  (* Add a rule for this to support asynchrous subtyping *)
  | [], ct => ⌜⌜ rest = ct ⌝⌝
  | _,_ => False
  end.

Definition buf_typed' (bufq : option (list val)) (ctq : option chan_type) (rest : chan_type) : rProp :=
    match bufq, ctq with
    | Some buf, Some ct => buf_typed buf ct rest
    | None, None => ⌜⌜ rest = EndT ⌝⌝
    | _,_ => False
    end.

Definition bufs_typed (b1 b2 : option (list val)) (σ1 σ2 : option chan_type) : rProp :=
  ∃ rest, buf_typed' b1 σ1 rest ∗
          buf_typed' b2 σ2 (dual rest).

Inductive in_to_σ12 : list clabel -> option chan_type -> option chan_type -> Prop :=
  | in_to_σ12_both σ1 σ2 labs : labs ≡ₚ [(true,σ1);(false,σ2)] -> in_to_σ12 labs (Some σ1) (Some σ2)
  | in_to_σ12_left σ1 : in_to_σ12 [(true,σ1)] (Some σ1) None
  | in_to_σ12_right σ2 : in_to_σ12 [(false,σ2)] None (Some σ2).

Definition chan_inv (b1 b2 : option (list val)) (inlabels : list clabel) : rProp :=
  ∃ σ1 σ2, ⌜⌜ in_to_σ12 inlabels σ1 σ2 ⌝⌝ ∗ bufs_typed b1 b2 σ1 σ2.

(* Definition threads_inv (g : conngraph) (es : list expr) :=
  ∀ i e, es !! i = Some e -> thread_inv e (in_labels g (Thread i)) (out_edges g (Thread i)).

Definition chans_inv (g : conngraph) (h : heap) :=
  ∀ i, chan_inv (h !! (i,true)) (h !! (i,false)) (in_labels g (Chan i)) (out_edges g (Chan i)). *)

Definition threads_inv (es : list expr) : gmap object (list clabel -> rProp) :=
  map_kmap Thread (map_seq 0 (thread_inv <$> es)).

Definition chans_inv (h : heap) : gmap object (list clabel -> rProp). Admitted.

Definition state_inv (es : list expr) (h : heap) : gmap object (list clabel -> rProp) :=
  threads_inv es ∪ chans_inv h.

Definition invariant (es : list expr) (h : heap) :=
  inv (state_inv es h).

Lemma state_inv_lookup_thread es h i :
  state_inv es h !! (Thread i) = thread_inv <$> (es !! i).
Proof. Admitted.

Lemma state_inv_lookup_chan es h i :
  state_inv es h !! (Chan i) = chans_inv h !! (Chan i).
Proof. Admitted.

Lemma state_inv_insert_thread es h i e :
  state_inv (<[ i := e ]> es) h = <[ Thread i := thread_inv e ]> (state_inv es h).
Proof. Admitted.


Lemma preservation (threads threads' : list expr) (chans chans' : heap) :
  step threads chans threads' chans' ->
  invariant threads chans ->
  invariant threads' chans'.
Proof.
  intros [].
  destruct H as [????????HH?].
  intros Hinv.
  unfold invariant in *.

  (* destruct Hinv as (g & Hwf & Hom & Hthr & Hch).
  pose proof (Hthr i (k e) H0) as Hti.
  destruct Hti as [Htin Hti'].
  unfold thread_inv in *.
  setoid_rewrite typed0_ctx_typed0 in Hti'; eauto.
  apply exists_holds in Hti' as [b Hti'].
  apply sep_holds in Hti' as (Σ1 & Σ2 & Hout & Hdisj & Hctx & He).
  unfold invariant. *)

  destruct HH; rewrite ?right_id.
  - (* Pure step *)
    eapply inv_impl; last done.
    intros v.
    destruct (decide (v = Thread i)).
    + subst. rewrite !state_inv_lookup_thread.
      rewrite list_lookup_insert. 2: { by eapply lookup_lt_Some. }
      rewrite !H0. simpl.
      intros ins.
      iIntros "H".
      admit.
    + admit.
  - (* Send *)
    rewrite state_inv_insert_thread.
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