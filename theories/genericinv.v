Require Export diris.cgraph.
Require Export diris.seplogic.

Section genericinv.
  Context {V : Type}.
  Context `{Countable V}.
  Context {L : Type}.

  (* Definition inv (g : cgraph V L) (f : V -> list L -> hProp V L) (h : V -> Prop) : Prop :=
      cgraph_wf g ∧ ∀ v : V,
      (v ∈ vertices g -> holds (f v (in_labels g v)) (out_edges g v)) ∧
      (v ∉ vertices g -> h v). *)

  Definition inv (f : gmap V (list L -> hProp V L)) : Prop :=
    ∃ g : cgraph V L ,cgraph_wf g ∧ ∀ v : V,
      (v ∈ vertices g -> ∃ Q, f !! v = Some Q -> holds (Q (in_labels g v)) (out_edges g v)) ∧
      (v ∉ vertices g -> f !! v = None).
(*
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
  Admitted. *)

  Lemma inv_move f v1 v2 l W P Q :
    inv (<[ v1 := λ i, (P i ∗ own1 v2 l ∗ W)%I ]> $ <[ v2 := λ i, Q i ]> f) ->
    inv (<[ v1 := λ i, (P i ∗ own1 v2 l)%I ]> $ <[ v2 := λ i, (Q i ∗ W)%I ]> f).
  Proof. Admitted.

  Lemma inv_delete f v :
    f !! v = Some (λ i, ⌜ i = [] ⌝%I) ->
    inv f ->
    inv (delete v f).
  Proof.
  Admitted.
(*
  Lemma inv_update f v1 v2 :
    inv' (<[ v1 := λ i, P i ∗ own v2 l ]> f) ->
    inv' (<[ v1 := λ i, P i ∗ own v2 l' ]> f)



  inv g (λ v' ins, f v' ins ∗ if decide (v1 = v') W else emp) h ->
  inv g' (λ v' ins, f v' ins ∗ if decide (v2 = v') W else emp) h. *)

  (* Lemma inv_move g f (h : V -> Prop) v1 v2 (W : hProp V L) :
    conn g v1 v2 ->
    inv g (λ v' ins, f v' ins ∗ if decide (v1 = v') W else emp) h ->
    inv g' (λ v' ins, f v' ins ∗ if decide (v2 = v') W else emp) h.
 *)
    (* We need to be able to express connectivity relationships here. *)
    (* But we need that anyway for progress. *)
    (* Think about how to handle that. *)

    (* v ↦ P ∗ V
    w ↦ Q

    v ↦ P
    w ↦ Q ∗ V *)

End genericinv.