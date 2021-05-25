Require Export diris.langdef.
Require Export diris.cgraph.
Require Export diris.seplogic.
Require Export diris.rtypesystem.
Require Export diris.langlemmas.

Definition conngraph := cgraph object clabel.
Definition edges := gmap object clabel.

Definition objects_match (g : conngraph) (es : list expr) (h : heap) : Prop. Admitted.

Definition thread_inv (e : expr) (inlabels : list clabel) (outedges : edges) : Prop :=
    inlabels = [] ∧ holds (rtyped0 e UnitT) outedges.



Fixpoint buf_typed (buf : list val) (ct : chan_type) (rest : chan_type) : hProp :=
  match buf, ct with
                            (* add owner here *)
  | v::buf', RecvT t ct' => val_typed v t ∗ buf_typed buf' ct' rest
  (* | v::buf', SendT t ct' => ??? *)
  (* Add a rule for this to support asynchrous subtyping *)
  | [], ct => ⌜⌜ rest = ct ⌝⌝
  | _,_ => False
  end.

Definition buf_typed' (bufq : option (list val)) (ctq : option chan_type) (rest : chan_type) : hProp :=
    match bufq, ctq with
    | Some buf, Some ct => buf_typed buf ct rest
    | None, None => ⌜⌜ rest = EndT ⌝⌝
    | _,_ => False
    end.

Definition bufs_typed (b1 b2 : option (list val)) (σ1 σ2 : option chan_type) : hProp :=
  ∃ rest, buf_typed' b1 σ1 rest ∗
          buf_typed' b2 σ2 (dual rest).

Inductive in_to_σ12 : list clabel -> option chan_type -> option chan_type -> Prop :=
  | in_to_σ12_both σ1 σ2 labs : labs ≡ₚ [(true,σ1);(false,σ2)] -> in_to_σ12 labs (Some σ1) (Some σ2)
  | in_to_σ12_left σ1 : in_to_σ12 [(true,σ1)] (Some σ1) None
  | in_to_σ12_right σ2 : in_to_σ12 [(false,σ2)] None (Some σ2).

Definition chan_inv (b1 b2 : option (list val)) (inlabels : list clabel) (outedges : edges) : Prop :=
  ∃ σ1 σ2, in_to_σ12 inlabels σ1 σ2 ∧ holds (bufs_typed b1 b2 σ1 σ2) outedges.

Definition threads_inv (g : conngraph) (es : list expr) :=
  ∀ i e, es !! i = Some e -> thread_inv e (in_labels g (Thread i)) (out_edges g (Thread i)).

Definition chans_inv (g : conngraph) (h : heap) :=
  ∀ i, chan_inv (h !! (i,true)) (h !! (i,false)) (in_labels g (Chan i)) (out_edges g (Chan i)).

Definition invariant (es : list expr) (h : heap) :=
  ∃ g : conngraph, cgraph_wf g ∧
    objects_match g es h ∧ threads_inv g es ∧ chans_inv g h.


Lemma preservation (threads threads' : list expr) (chans chans' : heap) :
  step threads chans threads' chans' ->
  invariant threads chans ->
  invariant threads' chans'.
Proof.
  intros [].
  destruct H as [????????HH?].
  intros Hinv.
  destruct Hinv as (g & Hwf & Hom & Hthr & Hch).
  pose proof (Hthr i (k e) H0) as Hti.
  destruct Hti as [Htin Hti'].
  unfold thread_inv in *.
  setoid_rewrite typed0_ctx_typed0 in Hti'; eauto.
  apply exists_holds in Hti' as [b Hti'].
  apply sep_holds in Hti' as (Σ1 & Σ2 & Hout & Hdisj & Hctx & He).
  unfold invariant.

  destruct HH; rewrite ?right_id.
  - exists g. split_and!; eauto.
    + admit.
    + intros ???. apply list_lookup_insert_Some in H2 as [(-> & <- & Hlt)|(Hne & Hsome)].
      * unfold thread_inv. split; eauto.
        rewrite-> pure_step_rtyped0 in He; eauto.
        eapply (holds_entails (ctx_typed0 k b UnitT ∗ rtyped0 e' b)%I).
        { rewrite sep_holds. eauto 6. }
        iIntros "[H1 H2]". iApply (ctx_subst0 with "H1 H2").
      * apply Hthr. done.
  - simpl in He.
    apply exists_holds in He as (?&He).
    apply exists_holds in He as (?&He).
    apply sep_holds in He as (?&?&?&?&?&?He).
    apply sep_holds in He as (?&?&?&?&?&?He).
    apply exists_holds in H7 as (?&H7).
    apply sep_holds in H7 as (?&?&?&?&?&?H7).
    apply affinely_pure_holds in H4 as [].
    apply affinely_pure_holds in H9 as [].
    apply own_holds in H10.
    simplify_eq.
    simplify_map_eq.
    rewrite !left_id_L in Hout.
    assert (∃ g', cgraph_wf g' ∧
      (∀ j, out_edges g' (Thread j) =
        if decide (i = j)
        then Σ1 ∪ {[Chan c.1 := (c.2, x)]}
        else out_edges g (Thread j)) ∧
      (∀ j, in_labels g' (Thread j) = in_labels g (Thread j)))
    as (g' & Hwf' & Hthrout' & Hthrin').
    {
      admit.
    }
    exists g'.
    split; eauto. split_and!.
    + admit.
    + unfold threads_inv. intros.
      specialize (Hthrout' i0).
      specialize (Hthrin' i0).
      rewrite Hthrout'.
      rewrite Hthrin'.
      case_decide.
      * subst. unfold thread_inv. split; eauto. rewrite list_lookup_insert in H2.
        2: {
          by eapply lookup_lt_Some.
        }
        simplify_eq.
        assert (holds (rtyped0 (Val (ChanV c)) (ChanT x)) {[Chan c.1 := (c.2, x)]}).
        {
          simpl. apply exists_holds. eexists.
          apply pure_sep_holds.
          split; eauto.
          apply own_holds. done.
        }
        pose proof (sep_combine _ _ _ _ Hctx H2) as HH.
        assert (Σ1 ##ₘ {[Chan c.1 := (c.2, x)]}) by solve_map_disjoint.
        specialize (HH H3).
        eapply (holds_entails _ _ _ HH).
        iIntros "[A B]".
        iApply (ctx_subst0 with "A"). iFrame.
      * apply Hthr. rewrite list_lookup_insert_ne in H2; eauto.
    + intros ?. rewrite !lookup_insert_spec. admit.
    admit.
  - simpl in He.
    apply exists_holds in He as (?&He).
    apply exists_holds in He as (?&He).
    apply sep_holds in He as (?&?&?&?&?&?He).
    apply exists_holds in He as (?&He).
    apply sep_holds in He as (?&?&?&?&?&?He).
    apply affinely_pure_holds in H4 as [].
    apply affinely_pure_holds in H7 as [].
    apply own_holds in He.
    simplify_eq.
    simplify_map_eq.
    rewrite !left_id_L in Hout.
    admit.
  - simpl in He.
    apply sep_holds in He as (?&?&?&?&?&?He).
    apply exists_holds in He as (?&He).
    apply sep_holds in He as (?&?&?&?&?&?He).
    apply affinely_pure_holds in H4 as [].
    apply affinely_pure_holds in H7 as [].
    apply own_holds in He.
    simplify_eq.
    simplify_map_eq.
    rewrite !left_id_L in Hout.
    admit.
  - simpl in He.
    apply exists_holds in He as (?&He).
    apply sep_holds in He as (?&?&?&?&?&?He).
    apply affinely_pure_holds in H5 as [].
    simplify_eq.
    simplify_map_eq.
    rewrite !left_id_L in Hout.
    admit.
Admitted.


Lemma preservationN (threads threads' : list expr) (chans chans' : heap) :
  steps threads chans threads' chans' ->
  invariant threads chans ->
  invariant threads' chans'.
Proof.
  induction 1; eauto using preservation.
Qed.