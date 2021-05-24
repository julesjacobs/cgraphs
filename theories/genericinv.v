Require Export diris.cgraph.
Require Export diris.seplogic.

Section genericinv.
  Context {V : Type}.
  Context `{Countable V}.
  Context {L : Type}.

  Definition inv (g : cgraph V L) (f : V -> list L -> hProp V L) (h : V -> Prop) : Prop :=
      cgraph_wf g ∧ ∀ v : V,
      (v ∈ vertices g -> holds (f v (in_labels g v)) (out_edges g v)) ∧
      (v ∉ vertices g -> h v).

  Lemma inv_impl g f f' (h h' : V -> Prop) :
    (∀ v ins, f v ins ⊢ f' v ins) ->
    (∀ v, h v -> h' v) ->
    inv g f h -> inv g f' h'.
  Proof.
    intros Hf Hh (Hg & HH).
    split; first done.
    intros v. split; last naive_solver.
    intros Hv.
    specialize (HH v) as [HH ?].
    eauto using holds_entails.
  Qed.

  Lemma inv_init f (h : V -> Prop) :
    (∀ v, h v) -> inv ∅ f h.
  Proof.
    intros HH.
    split.
    - apply empty_wf.
    - set_solver.
  Qed.

  Lemma inv_singleton f (h : V -> Prop) (v : V) :
    holds (f v []) ∅ ->
    (∀ v', v' ≠ v -> h v') ->
    inv {[ v := ∅ ]} f h.
  Proof.
    intros HH.
    split.
    - admit.
    - intros v'. split.
      + intros Hv. rewrite /vertices in Hv.
        assert (v' = v) by set_solver. subst.
        assert (in_labels ({[v := ∅]} : gmap V (gmap V L)) v = []) as HH1 by admit.
        rewrite /out_edges. rewrite lookup_singleton. rewrite HH1. eauto.
      + rewrite /vertices. set_solver.
  Admitted.

  (* Lemma inv_move f (h : V -> Prop) :
    inv f h -> *)
    (* We need to be able to express connectivity relationships here. *)
    (* But we need that anyway for progress. *)
    (* Think about how to handle that. *)
End genericinv.