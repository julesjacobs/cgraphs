Require Export diris.langdef.
Require Export diris.cgraph.
Require Export diris.seplogic.
Require Export diris.rtypesystem.



Definition clabel : Type := bool * chan_type.

Definition conngraph := cgraph (V := object) (L := clabel).
Definition edges := gmap object clabel.

Definition objects_match (g : conngraph) (es : list expr) (h : heap) : Prop. Admitted.

Definition thread_inv (e : expr) (in_edges : edges) (out_edges : edges) : Prop. Admitted.
    (* in_edges = ∅ ∧ holds (rtyped0 e UnitT) out_edges. *)

Definition buf := list val.
Definition chan_inv (b1 b2 : option buf) (in_edges : edges) (out_edges : edges) : Prop. Admitted.

Definition invariant (es : list expr) (h : heap) :=
  ∃ g : cgraph (V := object) (L := clabel), cgraph_wf g ∧
    objects_match g es h ∧
    (∀ i e, es !! i = Some e -> thread_inv e (c_out g (Thread i)) (c_in g (Thread i))) ∧
    (∀ i, chan_inv (h !! (i,true)) (h !! (i,false)) (c_out g (Chan i)) (c_in g (Chan i))).


Lemma preservation (threads threads' : list expr) (chans chans' : heap) :
  step threads chans threads' chans' ->
  invariant threads chans ->
  invariant threads' chans'.
Proof.
  intros [].
  destruct H as [????????HH?].
  intros Hinv.
  destruct Hinv as (g & Hwf & Hom & Hthr & Hch).
  pose proof (Hthr i (k e) H0).

  destruct HH; rewrite ?right_id.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
Admitted.


Lemma preservationN (threads threads' : list expr) (chans chans' : heap) :
  steps threads chans threads' chans' ->
  invariant threads chans ->
  invariant threads' chans'.
Proof.
  induction 1; eauto using preservation.
Qed.