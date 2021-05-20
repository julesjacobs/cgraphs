Require Export diris.langdef.
Require Export diris.cgraph.

Inductive object :=
  | Thread : nat -> object
  | Chan : chan -> object.

Instance object_eqdecision : EqDecision object.
Proof.
  intros [n|n] [m|m]; unfold Decision; destruct (decide (n = m));
  subst; eauto; right; intro; simplify_eq.
Qed.
Instance object_countable : Countable object.
Proof.
  refine (inj_countable' (λ l, match l with
  | Thread n => inl n
  | Chan n => inr n
  end) (λ l, match l with
  | inl n => Thread n
  | inr n => Chan n
  end) _); by intros [].
Qed.

Definition clabel : Type := bool * chan_type.

Definition conngraph := cgraph (V := object) (L := clabel).
Definition edges := gmap object clabel.

Definition objects_match (g : conngraph) (es : list expr) (h : heap) : Prop. Admitted.

Definition thread_inv (e : expr) (in_edges : edges) (out_edges : edges) : Prop. Admitted.

Definition buf := list val.
Definition chan_inv (b1 : option buf) (b2 : option buf) (in_edges : edges) (out_edges : edges) : Prop. Admitted.

Definition invariant (es : list expr) (h : heap) :=
  ∃ g : cgraph (V := object) (L := clabel), cgraph_wf g ∧
    objects_match g es h ∧
    (∀ i e, es !! i = Some e -> thread_inv e (c_out g (Thread i)) (c_in g (Thread i))) ∧
    (∀ i, chan_inv (h !! (i,true)) (h !! (i,false)) (c_out g (Chan i)) (c_in g (Chan i))).
