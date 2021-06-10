From diris Require Import invariant.
(*
  Local progress: if e is well typed, then in all heaps that are well typed
   (and consistent with the heap typing for e), then either:
   - e can take a step in that heap
   - e is a value
   - e is waiting to receive on a channel with an empty buffer
*)

Lemma local_progress : True. Admitted.

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

Definition waiting (x y : object) : Prop. Admitted.
Definition active (x : object) (es : list expr) (h : heap) :=
  match x with
  | Thread i => ∃ e, es !! i = Some e ∧ e ≠ Val UnitV
  | Chan i => ∃ b, is_Some (h !! (i,b))
  end.

Lemma waiting_asym : asym waiting.
Proof. Admitted.

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
  eapply (cgraph_ind waiting g (λ x,
    active x es h → ∃ (es' : list expr) (h' : heap), step es h es' h'));
    eauto using waiting_asym.
  intros x Hind Hactive.
  destruct x as [i|i]; simpl in *.
  - destruct Hactive as (e & He & Heneq).
    admit.
  - destruct Hactive as (b & Hib).
    admit.
Admitted.