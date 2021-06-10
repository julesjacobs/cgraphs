From diris Require Import invariant.
(*
  Global progress: if the invariant holds for (es,h) then either:
  - all e ∈ es are unit, and h = ∅
  - the configuration can step
*)

Lemma is_unit_decision e :
  Decision (e = Val UnitV).
Proof.
  destruct e; try solve [right; intro; simplify_eq].
  destruct v; try solve [right; intro; simplify_eq].
  left. done.
Qed.

Lemma exprs_decision (es : list expr) :
  Decision (∃ e, e ∈ es ∧ e ≠ Val UnitV).
Proof.
  eapply (dec_exists_list _ es).
  - intros ? []; eauto.
  - intros.
    destruct (is_unit_decision x); subst.
    + right. intros []. apply H1. done.
    + left. eauto.
Qed.

Lemma heap_decision (h : heap) :
  Decision (∃ c, is_Some (h !! c)).
Proof.
  destruct (decide (h = ∅)).
  - right. intros []. subst. rewrite lookup_empty in H.
    destruct H. simplify_eq.
  - left. destruct (map_to_list h) eqn:E.
    { apply map_to_list_empty_inv in E. subst. exfalso.
      apply n. done. }
    destruct p.
    exists e.
    assert ((e,l0) ∈ map_to_list h).
    { rewrite E. rewrite elem_of_cons. eauto. }
    apply elem_of_map_to_list in H. rewrite H. eauto.
Qed.

Lemma final_state_decision (es : list expr) (h : heap) :
  {(∃ c, is_Some (h !! c)) ∨ (∃ e, e ∈ es ∧ e ≠ Val UnitV)} +
  {h = ∅ ∧ ∀ e, e ∈ es -> e = Val UnitV}.
Proof.
  destruct (heap_decision h); [left; eauto|].
  destruct (exprs_decision es); [left; eauto|].
  right. split.
  - assert (∀ c, ¬ is_Some (h !! c)) by naive_solver.
    assert (∀ c, h !! c = None).
    { intros. destruct (h !! c) eqn:E; eauto.
      exfalso. eapply H. erewrite E. eauto. }
    apply map_empty. eauto.
  - intros.
    assert (∀ e, ¬ (e ∈ es ∧ e ≠ Val UnitV)) by naive_solver.
    specialize (H0 e).
    destruct (is_unit_decision e); eauto.
    exfalso.
    apply H0; eauto.
Qed.

Definition is_val e := ∃ v, e = Val v.

Definition all_subexprs_are_values e :=
  ∀ k e', ctx k -> e = k e' -> e ≠ e' -> is_val e'.

Lemma decompose_ctx e :
  is_val e ∨ (∃ k e', ctx k ∧ e = k e' ∧ e ≠ e' ∧ all_subexprs_are_values e').
Proof.
Admitted.

Lemma rtyped_inner e t :
  all_subexprs_are_values e ->
  rtyped0 e t -∗
  ⌜ is_val e ∨
    (∃ e', pure_step e e') ∨
    (∃ v, e = Recv (Val v)) ∨
    (∃ v1 v2, e = Send (Val v1) (Val v2)) ∨
    (∃ v, e = Fork (Val v)) ∨
    (∃ v, e = Close (Val v)) ⌝.
Proof.
  iIntros (He) "Ht".
  destruct e; simpl in *.
Admitted.

Definition thread_waiting (es : list expr) (h : heap) (i j : nat) :=
  ∃ k b, ctx k ∧
    es !! i = Some (Recv (Val (ChanV (j,b)))) ∧
    h !! (j,b) = Some [].

Definition waiting es h (x y : object) : Prop :=
  match x,y with
  | Thread i, Chan j => thread_waiting es h i j
  | Chan i, Thread j => ¬ thread_waiting es h j i
  | Chan i, Chan j => True (* Problem: not antisymmetric!!! *)
  | Thread i, Thread j => False
  end.

Definition active (x : object) (es : list expr) (h : heap) :=
  match x with
  | Thread i => ∃ e, es !! i = Some e ∧ e ≠ Val UnitV
  | Chan i => ∃ b, is_Some (h !! (i,b))
  end.

(* This property is currently false, need to change approach *)
Lemma waiting_asym es h : asym (waiting es h).
Proof.
  intros ??.
  destruct x,y; unfold waiting; simpl.
Admitted.

Lemma mset_wlog b σs :
  mset_σs σs ≡
    opt_to_singleton b (σs !! b) ⋅
    opt_to_singleton (negb b) (σs !! (negb b)).
Proof.
  destruct b; try done.
  rewrite (comm (⋅)). simpl. done.
Qed.

Lemma global_progress es h :
  invariant es h ->
  (h = ∅ ∧ ∀ e, e ∈ es -> e = Val UnitV) ∨
  (∃ es' h', step es h es' h').
Proof.
  intros H.
  destruct (final_state_decision es h) as [Hdec|Hdec]; eauto; right.
  assert (∃ x, active x es h) as [x Hactive].
  { destruct Hdec as [(x&?)|(x&?)].
    + destruct x. exists (Chan c). simpl. eauto.
    + destruct H0. eapply elem_of_list_lookup in H0 as [].
      exists (Thread x0). simpl. eauto. }
  clear Hdec.
  destruct H as (g & Hwf & Hvs).
  revert x Hactive.
  eapply (cgraph_ind (waiting es h) g (λ x,
    active x es h → ∃ (es' : list expr) (h' : heap), step es h es' h'));
    eauto using waiting_asym.
  intros x Hind Hactive.
  pose proof (Hvs x) as Hx.
  destruct x as [i|i]; simpl in *.
  - destruct Hactive as (e & He & Heneq).
    rewrite He in Hx.
    apply pure_sep_holds in Hx as [Hinl Hx].
    admit.
  - destruct Hactive as (b & Hib).
    apply exists_holds in Hx as [σs Hx].
    apply pure_sep_holds in Hx as [Hinl Hx].
    eapply holds_entails in Hx; last by eapply (bufs_typed_wlog true b).
    destruct Hib as [buf Hbuf].
    rewrite Hbuf in Hx.
    destruct (σs !! b) as [σ1|] eqn:E; last first.
    { unfold bufs_typed in Hx. simpl in Hx.
      eapply exists_holds in Hx as [? Hx].
      eapply sep_holds in Hx as (? & ? & ? & ? & Hx & ?).
      eapply false_holds in Hx. done. }
    unfold bufs_typed in Hx. simpl in Hx.
    rewrite ->(mset_wlog b) in Hinl.
    rewrite E in Hinl. simpl in Hinl.
    assert (∃ y, out_edges g y !! (Chan i) = Some (b,σ1)) as [y Hy].
    { admit. }
    destruct buf; last first.
    {
      eapply (Hind y); admit.
    }
    simpl in Hx.
    eapply exists_holds in Hx as [? Hx].
    eapply pure_sep_holds in Hx as [-> Hx].
    admit.
Admitted.