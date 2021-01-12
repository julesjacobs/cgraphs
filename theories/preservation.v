From stdpp Require Import gmap.
From iris.bi Require Import interface.
From iris.proofmode Require Import tactics.
Require Import diris.langdef.
Require Import diris.hprop.
Require Import diris.util.
Require Import diris.htypesystem.

(*
  This predicate says that the types of the receives at the start of ct
  match the values in buf, and the rest of ct is equal to rest.
*)
Fixpoint buf_typed (buf : list val) (ct : chan_type) (rest : chan_type) : hProp :=
  match buf, ct with
  | v::buf', RecvT t ct' => val_typed v t ∗ buf_typed buf' ct' rest
  (* | v::buf', SendT t ct' => ??? *)
  (* Add a rule for this to support asynchrous subtyping *)
  | [], ct => ⌜⌜ rest = ct ⌝⌝
  | _,_ => False
  end.

(*
  This predicate says two buffers and two channel types are in a consistent state.
  If the buffers are empty this says that they must be dual.
  If the buffers are not empty then the types are not necessarily dual, but
  they are "dual up to the values in the buffers".
*)
(* Definition bufs_typed (bufs : list val * list val) (ct1 ct2 : chan_type) : hProp :=
  ∃ rest:chan_type,
     buf_typed (snd bufs) ct1 rest ∗
     buf_typed (fst bufs) ct2 (dual rest).

Definition bufs_typed' (buf1 buf2 : list val) (ct1 ct2 : chan_type) : hProp :=
  ∃ rest:chan_type,
      buf_typed buf1 ct1 rest ∗
      buf_typed buf2 ct2 (dual rest).

Definition invariantΣ (Σ : heapT)
      (threads : list expr) (chans : heap) : hProp :=
  ([∗ list] e∈threads, ptyped ∅ e UnitT) ∗
  ∃ rest : nat -> chan_type,
    ([∗ map] ep↦buf;ct∈chans;Σ,
      buf_typed buf ct (if ep.2 then (rest ep.1) else dual (rest (ep.1)))
    ) *)

Definition heap_chans (Σ : heapT) : gset nat := set_map fst (dom (gset endpoint) Σ).

Definition buf_typed' (bufq : option (list val)) (ctq : option chan_type) (rest : chan_type) : hProp :=
    match bufq, ctq with
    | Some buf, Some ct => buf_typed buf ct rest
    | None, None => ⌜⌜ rest = EndT ⌝⌝
    | _,_ => False
    end.

Definition bufs_typed (chans : heap) (Σ : heapT) (i : chan) : hProp :=
  ∃ rest, buf_typed' (chans !! (i,true)) (Σ !! (i,true)) rest ∗
          buf_typed' (chans !! (i,false)) (Σ !! (i,false)) (dual rest).

Definition heap_typed (chans : heap) (Σ : heapT) : hProp :=
   ([∗ set] i∈heap_chans Σ, bufs_typed chans Σ i)%I.

Definition invariant (chans : heap) (threads : list expr) : hProp :=
  ∃ Σ, own Σ ∗ (* should become own_auth *)
      ([∗ list] e∈threads, ptyped0 e UnitT) ∗
      heap_typed chans Σ.

(*
Previously:
===========

invariant chans threads : Prop :=
  ∃ Σ, own Σ ⊢ ...

hProp := heapT -> Prop

P ⊢ Q := ∀ Σ, P Σ -> Q Σ

(P ∗ Q) Σ := ∃ Σ1 Σ2, Σ = Σ1 ∪ Σ2 ∧ Σ1 ##ₘ Σ2 ∧ P Σ1 ∧ Q Σ2

(P -∗ Q) Σ := ∀ Σ', Σ ##ₘ Σ' -> P Σ' -> Q (Σ ∪ Σ')

(own Σ) Σ' := (Σ = Σ')


Now:
====

invariant chans threads : hProp :=
  ∃ Σ, know Σ ∗ ...

hProp := (heapT * heapT) -> Prop

P ⊢ Q := ∀ Σ Σ', P (Σ,Σ') -> Q (Σ,Σ')

(|=> Q) (Σg,Σl) = ∃ Σ', Q (Σ',Σ')

(P ∗ Q) (Σg,Σl) := ∃ Σl1 Σl2, Σl = Σl1 ∪ Σl2 ∧ Σl1 ##ₘ Σl2 ∧ P (Σg,Σl1) ∧ Q (Σg,Σl2)

(P -∗ Q) (Σg,Σl) := ∀ Σl', Σl ##ₘ Σl' -> P (Σg,Σl') -> Q (Σg, Σl ∪ Σl')

We want: (P ∗ Q) -∗ R ⊣⊢ P -∗ (Q -∗ R)

(own Σ) (Σg,Σl) := (Σ = Σl)
(know Σ) (Σg,Σl) := (Σ ⊆ Σg ∧ Σl = ∅)

Lemma preservation threads chans threads' chans' :
  step threads chans threads' chans' ->
    invariant threads chans -∗ |=> invariant threads' chans'

*)



Lemma buf_typed_push buf t ct rest v :
  val_typed v t -∗
  buf_typed buf ct (RecvT t rest) -∗
  buf_typed (buf ++ [v]) ct rest.
Proof.
  iIntros "Hv Hb".
  iInduction buf as [] "IH" forall (ct rest); simpl.
  - iDestruct "Hb" as "<-". iFrame. done.
  - destruct ct; eauto.
    iDestruct "Hb" as "[Hv' H]".
    iDestruct ("IH" with "Hv H") as "HH". iFrame.
Qed.

Lemma buf_typed_pop buf t ct rest v :
  buf_typed (v::buf) (RecvT t ct) rest -∗
  buf_typed buf ct rest ∗ val_typed v t.
Proof.
  iIntros "[? ?]". simpl. iFrame.
Qed.

Lemma heap_chans_Some { Σ i b } :
  is_Some (Σ !! (i,b)) ->
  i ∈ heap_chans Σ.
Proof.
  intros H.
  rewrite elem_of_map.
  exists (i,b); simpl. split; first done.
  rewrite elem_of_dom. done.
Qed.

Lemma heap_chans_in i Σ :
  i ∈ heap_chans Σ ->
  ∃ b, is_Some (Σ !! (i,b)).
Proof.
  unfold heap_chans.
  rewrite elem_of_map.
  intros [x [H H']].
  setoid_rewrite elem_of_dom in H'.
  destruct x. eexists. simplify_eq. done.
Qed.

Lemma dual_dual ct :
  dual (dual ct) = ct.
Proof.
  induction ct; simpl; f_equal; eauto.
Qed.

Lemma other_other ep :
  other (other ep) = ep.
Proof.
  by destruct ep as [? []].
Qed.

Lemma bufs_typed_alt (chans : heap) (Σ : heapT) (ep : endpoint) :
  bufs_typed chans Σ ep.1 ⊣⊢
  ∃ rest, buf_typed' (chans !! ep) (Σ !! ep) rest ∗
          buf_typed' (chans !! other ep) (Σ !! other ep) (dual rest).
Proof.
  destruct ep as [n b].
  iSplit.
  - iIntros "H".
    iDestruct "H" as (rest) "[H1 H2]".
    destruct b; simpl; iExists _; iFrame. rewrite dual_dual. iFrame.
  - iIntros "H".
    iDestruct "H" as (rest) "[H1 H2]".
    simpl. unfold bufs_typed.
    destruct b; simpl; iExists _; iFrame. rewrite dual_dual. iFrame.
Qed.


(* Lemma bufs_typed_other chans Σ ep :
  bufs_typed chans Σ ep ⊣⊢ bufs_typed chans Σ (other ep).
Proof.
  revert ep.
  wlog: / (∀ ep, bufs_typed chans Σ ep ⊢ bufs_typed chans Σ (other ep)); last first.
  { intros H ep.
    iSplit.
    - iIntros "H". iApply H. done.
    - destruct ep as [i []]; simpl; iIntros "H";
      iDestruct (H with "H") as "H"; simpl; done. }
  intros H ep. apply H. clear H ep. intros ep.
  iIntros "H".
  iDestruct "H" as (rest) "[H1 H2]".
  iExists (dual rest).
  rewrite dual_dual other_other.
  iFrame.
Qed. *)

(* Lemma bufs_typed_wlog  chans Σ ep b :
  bufs_typed chans Σ (ep.1, b) ⊢ bufs_typed chans Σ ep.
Proof.
  destruct ep as [i b']; simpl.
  destruct (decide (b = b')); simplify_eq; eauto.
  iIntros "H".
  rewrite bufs_typed_other.
  destruct b,b';simpl;simplify_eq;eauto.
Qed. *)

Lemma heap_chans_delete Σ ep :
  heap_chans (delete ep $ delete (other ep) Σ) = heap_chans Σ ∖ {[ep.1]}.
Proof.
  unfold heap_chans.
  rewrite !dom_delete_L.
  apply elem_of_equiv_L. intros n.
  rewrite elem_of_difference.
  rewrite !elem_of_map.
  split.
  - intros [x [H1 H2]].
    rewrite-> !elem_of_difference in H2.
    destruct H2 as [[H2 H3] H4].
    destruct x,ep; simpl in *; simplify_eq.
    assert (c ≠ c0).
    {
      destruct (decide (b = b0)); intro; subst.
      - apply H4. apply elem_of_singleton. done.
      - assert (b = (negb b0)).
        { destruct b,b0; simpl; simplify_eq; done. }
        subst. apply H3. apply elem_of_singleton. done.
    }
    rewrite not_elem_of_singleton. split;eauto.
    exists (c,b); simpl. split; eauto.
  - intros [[x [H1 H2]] H].
    destruct ep,x; simpl in *. subst.
    rewrite -> not_elem_of_singleton in H.
    exists (c0,b0). simpl. split; eauto.
    rewrite !elem_of_difference.
    repeat split; eauto;
    rewrite-> not_elem_of_singleton;
    intro; simplify_eq.
Qed.

Lemma bufs_typed_relevant Σ Σ' chans chans' i :
  (∀ b, Σ !! (i,b) = Σ' !! (i,b)) -> (∀ b, chans !! (i,b) = chans' !! (i,b)) ->
  bufs_typed Σ chans i -∗ bufs_typed Σ' chans' i.
Proof.
  iIntros (H1 H2) "H".
  iDestruct "H" as (rest) "[H1 H2]".
  iExists rest.
  rewrite !H1 !H2. iFrame.
Qed.

Lemma lookup_delete `{Countable K} {V} (x y : K) (m : gmap K V) :
  delete x m !! y = if (decide (x = y)) then None else m !! y.
Proof.
  case_decide.
  - subst. rewrite lookup_delete. done.
  - rewrite lookup_delete_ne; done.
Qed.

Lemma delete_both {A} (x : chan) (b : bool) (ep : endpoint) (m : gmap endpoint A) :
  x ≠ ep.1 ->
  (delete ep (delete (other ep) m)) !! (x,b) = m !! (x,b).
Proof.
  intros H.
  rewrite !lookup_delete. destruct ep,b; simpl in *;
  repeat case_decide; simplify_eq; done.
Qed.

Lemma heap_typed_Some_split Σ ep chans :
  is_Some (Σ !! ep) ->
  heap_typed chans Σ ⊣⊢
  heap_typed (delete ep $ delete (other ep) chans)
             (delete ep $ delete (other ep) Σ) ∗
  bufs_typed chans Σ ep.1.
Proof.
  intros HSome.
  iSplit.
  - iIntros "H".
    unfold heap_typed.
    pose proof (heap_chans_Some HSome) as Hin.
    iDestruct (big_sepS_delete with "H") as "[Hep H]"; first done.
    rewrite heap_chans_delete. iFrame.
    iApply (big_sepS_impl with "H").
    iModIntro.
    iIntros (x H) "H".
    rewrite-> elem_of_difference, elem_of_singleton in H.
    destruct H.
    iApply (bufs_typed_relevant with "H"); intros b;
    rewrite delete_both; eauto.
  - iIntros "[H H2]".
    unfold heap_typed.
    rewrite heap_chans_delete.
    iApply big_sepS_delete.
    { eapply heap_chans_Some.
      replace (ep) with (ep.1, ep.2) in HSome; first done.
      destruct ep; done. }
    iFrame.
    rewrite <-!heap_chans_delete.
    iApply (big_sepS_impl with "H").
    iModIntro.
    iIntros (x H) "H".
    assert (x ≠ ep.1).
    {
      rewrite heap_chans_delete //= in H.
      apply elem_of_difference in H as [? H].
      intro. apply H. apply elem_of_singleton. done.
    }
    iApply (bufs_typed_relevant with "H"); intros b;
    rewrite delete_both; eauto.
Qed.

Lemma bufs_typed_is_Some Σ chans ep :
  bufs_typed chans Σ ep.1 -∗
  ⌜ is_Some (chans !! ep) <-> is_Some (Σ !! ep) ⌝.
Proof.
  iIntros "H".
  unfold bufs_typed.
  iDestruct "H" as (rest) "[H1 H2]".
  destruct ep; simpl.
  destruct b.
  - destruct (chans !! (c,true)),(Σ !! (c,true)); simpl;
    rewrite !is_Some_alt; eauto.
  - destruct (chans !! (c,false)),(Σ !! (c,false)); simpl;
    rewrite !is_Some_alt; eauto.
Qed.

Lemma heap_typed_send chans Σ t v ep ct :
  Σ !! ep = Some (SendT t ct) ->
  val_typed v t -∗
  heap_typed chans Σ -∗
  ∃ buf, ⌜⌜  chans !! other ep = Some buf ⌝⌝ ∗
    heap_typed (<[ other ep := buf ++ [v] ]> chans) (<[ ep := ct ]> Σ).
Proof.
  iIntros (HΣ) "Hv H".
  assert (is_Some (Σ !! ep)).
  { eexists. done. }
  rewrite heap_typed_Some_split; last done.
  iDestruct "H" as "[H Hb]".
  iAssert (⌜ is_Some (chans !! ep) ⌝)%I as "%".
  { rewrite bufs_typed_is_Some. iDestruct "Hb" as "%". iPureIntro. rewrite H0. done. }
  destruct H0 as [buf Hbuf].
  rewrite bufs_typed_alt.
  iDestruct "Hb" as (rest) "[H1 H2]".
  rewrite HΣ Hbuf. simpl.
  destruct buf; simpl; eauto.
  iDestruct "H1" as "%". subst. simpl.
  destruct (chans !! other ep) eqn:E; simpl;
  destruct (Σ !! other ep) eqn:F; simpl; eauto; last first.
  { iDestruct "H2" as "%". simplify_eq. }
  iExists _. iSplit; first done.
  setoid_rewrite heap_typed_Some_split at 2; last first.
  { erewrite lookup_insert. eexists. done. }
  rewrite !delete_insert_delete.
  rewrite (delete_commute (<[ep:=ct]> Σ)).
  rewrite !delete_insert_delete.
  rewrite (delete_commute Σ). iFrame.
  (* push onto buffer *)
  rewrite bufs_typed_alt.
  iExists _.
  rewrite !lookup_insert !lookup_insert_ne; last first.
  { destruct ep. destruct b; simpl; intro; simplify_eq. }
  { destruct ep. destruct b; simpl; intro; simplify_eq. }
  rewrite Hbuf F. simpl.
  iSplit; last first.
  - iApply (buf_typed_push with "Hv"). done.
  - done.
Qed.

(*
(* TODO:
  move premise chans !! other ep = Some buf to conclusion using an existential -> DONE
 *)

Lemma heap_typed_send chans Σ t v ep ct buf :
  chans !! other ep = Some buf ->
  Σ !! ep = Some (SendT t ct) ->
  val_typed v t -∗
  heap_typed chans Σ -∗
  heap_typed (<[ other ep := buf ++ [v] ]> chans) (<[ ep := ct ]> Σ).
Proof.
  iIntros (Hc HΣ) "Hv Ht".
  iDestruct "Ht" as (Hchans) "Ht".
  iSplit.
  - iPureIntro.
    intros ep'.
    (* Search is_Some insert.
    rewrite !lookup_insert_is_Some.
    destruct (decide (ep = ep')).
    + subst. rewrite Hchans HΣ !is_Some_alt.
      destruct ep'. *)

    destruct (decide (ep = ep')).
    + subst. rewrite !lookup_insert.
      rewrite lookup_insert_ne. rewrite Hchans. rewrite HΣ.
      rewrite !is_Some_alt. done. destruct ep'. simpl. destruct b; eauto.
    + rewrite lookup_insert_ne; eauto. rewrite <-Hchans.
      destruct (decide (ep' = other ep)).
      * subst. rewrite lookup_insert. rewrite Hc. rewrite !is_Some_alt. done.
      * rewrite lookup_insert_ne; eauto.
  - assert (heap_chans (<[ep:=ct]> Σ) = heap_chans Σ) as -> by admit.
    assert (ep.1 ∈ heap_chans Σ) by admit.
    iApply big_sepS_delete; first done.
    iDestruct (big_sepS_delete with "Ht") as "[Hep H]"; first done.
    iSplitL "Hep Hv".
    + iDestruct "Hep" as (rest) "[Hl Hr]".
      iExists rest.
      destruct ep as [x b]. simpl.
      destruct b; simpl in *.
      * rewrite !lookup_insert.
        rewrite !lookup_insert_ne; eauto.
        iFrame. simpl. rewrite Hc. simpl. rewrite HΣ. simpl.
        admit.
      * rewrite !lookup_insert.
        rewrite !lookup_insert_ne; eauto.
        iFrame. simpl. rewrite Hc. simpl. rewrite HΣ. simpl.
        admit.
    + iApply (big_sepS_impl with "H").
      iModIntro.
      iIntros (x HH) "H".
      iDestruct "H" as (rest) "[Hl Hr]".
      iExists _.
      destruct ep as [x' b']. assert (x ≠ x') by admit.
      rewrite !lookup_insert_ne; [iFrame|..]; intro; simplify_eq.
Admitted. *)

Lemma heap_typed_recv chans Σ t v ep ct buf :
  chans !! ep = Some (v::buf) ->
  Σ !! ep = Some (RecvT t ct) ->
  heap_typed chans Σ -∗
  heap_typed (<[ ep := buf ]> chans) (<[ ep := ct ]> Σ) ∗ val_typed v t.
Proof.
Admitted.

Lemma heap_typed_close chans Σ ep :
  Σ !! ep = Some EndT ->
  heap_typed chans Σ -∗
  ⌜⌜ chans !! ep = Some [] ⌝⌝ ∗ heap_typed (delete ep chans) (delete ep Σ).
Proof.
Admitted.

Lemma heap_typed_fork chans Σ i ct :
  chans !! (i,true) = None ->
  chans !! (i,false) = None ->
  heap_typed chans Σ -∗
  heap_typed (<[ (i,true) := [] ]> $ <[ (i,false) := [] ]> chans)
             (<[ (i,true) := ct ]> $ <[ (i,false) := dual ct ]> Σ).
Proof.
Admitted.

Lemma heap_typed_consistent chans Σ ep ct :
  Σ !! ep = Some ct ->
  heap_typed chans Σ -∗
  ∃ buf, ⌜ chans !! ep = Some buf ⌝.
Proof.
Admitted.

Lemma heap_typed_emp chans :
  heap_typed chans ∅ -∗ ⌜ chans = ∅ ⌝.
Proof.
Admitted.

Lemma heap_typed_init :
  ⊢ heap_typed ∅ ∅.
Proof.
Admitted.



(*
  ([∗ list] i↦bufs∈chans,
    bufs_typed bufs (default EndT (Σ !! (i,true))) (default EndT (Σ !! (i,false)))).
    (* Add condition that the domain of Σ is a subset of chans. *)
    (* ∀ i b, is_Some (Σ !! (i,b)) -> is_Some (chans !! i) *)
*)

Definition invariant (threads : list expr) (chans : heap) : Prop :=
  ∃ Σ, own Σ ⊢ invariantΣ Σ threads chans.

  (* ∃ Σ, invariantΣ Σ threads chans Σ *)
  (* own Σ : hProp := λ Σ', Σ = Σ' *)

(*
  own {[ c := r ]} ∗ know {[ c := r' ]} -∗ ⌜ r = r' ⌝
*)

(*
Do we want:
  hProp := gset endpoint -> Prop
???

  hProp := option (gset endpoint * (endpoint -> chan_type)) -> Prop
*)

(*
  Σ --> Σ1,Σ2     Σ1 ∪ Σ2 = Σ ∧ Σ1 ##ₘ Σ2

  (Σl,Σg) --> (Σl1,Σg1),(Σl2,Σg2)

      Σl1 ∪ Σl2 = Σl ∧ Σl1 ##ₘ Σl2
      Σg1 ⊆ Σg ∧ Σg2 ⊆ Σg

      Σl ⊆ Σg

      (⋅) : A -> A -> A
      ✓ : A -> Prop

      R : A -> A -> A -> Prop
      R Σ Σ1 Σ2 := Σ = Σ1 ∪ Σ2 ∧ Σ1 ##ₘ Σ2
      (P ∗ Q)(a) := ∃ a1 a2, R a a1 a2 ∧ P(a1) ∧ Q(a2)

      P : A -> Prop
      Q : A -> Prop
      (P ∗ Q)(a) := ∃ a1 a2, ✓ (a1⋅a2) ∧ a1⋅a2 = a ∧ P(a1) ∧ Q(a2)

      for hProp we have A := option (heapT)
        Σ1⋅Σ2 := Σ1 ∪ Σ2
        None⋅Σ2 := None
        Σ1⋅None := None
        (Some Σ1)⋅(Some Σ2) := if Σ1 ##ₘ Σ2 then Some (Σ1 ∪ Σ2) else None

        ✓ None := False
        ✓ (Some Σ) := True
*)

(* Which lemma's do we need for own? *)
(*
  We need to instantiate the existential, then we have:
  own Σ -∗ invariant Σ es h
  -------------------------
  own Σ' -∗ invariant Σ' es' h'

  We want to transform this so that we have the same own Σ'' in top and bottom,
  so that we can get a goal of the worm invariant (?) (?) -∗ invariant (?') (?').
*)

Lemma foo (A B : Type) (P : A -> Prop) :
  A = B -> (∃ x:A, P x).
  intros Heq.
  (* rewrite Heq. *)
  subst.
Admitted.

Lemma bar (n m : nat) :
  (∀ x, x + m = x + n) -> (λ x, x+m) = (λ x, x+n).
  intros Heq.
  (* rewrite Heq. *)
Admitted.

Lemma baz (A B : Type) (P : (A -> A) -> Prop) :
  A = B -> P (λ (x : A), x).
  intros Heq.
  (* rewrite Heq. *)
  subst.
Admitted.

Lemma pure_step_ptyped e e' t :
  pure_step e e' -> ptyped ∅ e t -∗ ptyped ∅ e' t.
Proof.
  intros Hps.
  iIntros "Ht".
  iInduction Hps as [] "IH"; simpl.
  - iDestruct "Ht" as (t' Γ1 Γ2 H) "Ht".
    iDestruct "Ht" as "((_ & Ht1) & (_ & Ht2))".
    iDestruct "Ht1" as (t1 t2 HH) "Ht1".
    simplify_eq.
    replace (∅ : envT) with (delete x {[ x:= t1 ]} : envT) by (by rewrite delete_singleton).
    iApply (subst_ptyped with "Ht2 Ht1").
    rewrite lookup_singleton. done.
  - iSplit; first done.
    iDestruct "Ht" as (t1 t2 [-> _]) "Ht".
    iExists _,_.
    iSplit; first done. rewrite left_id. done.
  - iDestruct "Ht" as (Γ1 Γ2 HH) "[_ [Ht _]]".
    assert (Γ2 = ∅) by admit. subst. done.
  - iDestruct "Ht" as (Γ1 Γ2 H) "[_ [_ Ht]]".
    assert (Γ2 = ∅) by admit. subst. done.
  - iDestruct "Ht" as (t' Γ1 Γ2 H) "[[% Hv] Ht]".
    destruct H as (H & _ & _).
    subst. rewrite left_id in H. subst. rewrite left_id.
    replace (∅ : envT) with (delete x {[ x := t']} : envT) by admit.
    iApply (subst_ptyped with "Hv Ht").
    rewrite lookup_singleton. done.
  - iDestruct "Ht" as (Γ1 Γ2 (H & Hd)) "[% Ht]".
    destruct H0. subst. rewrite left_id in H. subst. done.
  - iDestruct "Ht" as (t1 t2 Γ1 Γ2 (? & ? & ? & ?)) "[[% Hv] Ht]".
    iDestruct "Hv" as (t1' t2' HH) "[Hv1 Hv2]".
    subst.
    rewrite left_id in H. subst.
    rewrite left_id.
    replace (∅ : envT) with (delete x1 $ delete x2 $ ({[x1 := t1]} ∪ {[x2 := t2]}) : envT)
      by admit.
    iApply (subst_ptyped with "Hv1 [Ht Hv2]").
    + admit.
    + iApply (subst_ptyped with "Hv2 Ht").
      admit.
Admitted.

Definition ct_tail (ct : chan_type) : chan_type :=
    match ct with
    | RecvT v ct' => ct'
    | SendT v ct' => ct'
    | EndT => EndT
    end.

Lemma own_distr (A B : heapT) :
  A ##ₘ B -> own (A ∪ B) -∗ own A ∗ own B.
Proof. Admitted.

  (*
ct = (SendT vt ct')

Hinv: own (delete c Σ) ∗ own {[ c := ct ]} -∗ invariantΣ Σ es h
Hinv: own (delete c Σ) -∗ own {[ c := ct ]} -∗ invariantΣ Σ es h



"HΣ1" : own {[ c := ct ]} -∗ invariantΣ Σ es h
"HΣ2" : own {[ c := ct' ]}
--------------------------------------∗
invariantΣ (delete c Σ ∪ {[c := ct']}) (<[i:=k (Val (Chan c))]> es)
  (set_recv h c (buf ++ [y]))



  *)

Lemma big_opL_insert_override {A} (l : list A) (k : nat) (y y' : A)
                     (P : nat -> A -> hProp) :
  l !! k = Some y ->
  (P k y -∗ P k y') -∗
  ([∗ list] i↦x∈l, P i x) -∗
  ([∗ list] i↦x∈(<[ k := y' ]> l), P i x).
Proof.
  iIntros (?) "HP H".
  iDestruct (big_sepL_insert_acc with "H") as "[Hy H]"; first done.
  iApply "H". iApply "HP". done.
Qed.

Lemma own_adequacy Σ P :
  (own Σ ⊢ ⌜ P ⌝) -> P.
Proof.
Admitted.


(*
(own Σ ⊢ own Σ' ∗ P) -> Σ' ⊆ Σ ∧ (own (Σ ∖ Σ') ⊢ P)
*)

(*
Lemma preservation (threads threads' : list expr) (chans chans' : heap) :
  step threads chans threads' chans' ->
  invariant threads chans |==>
  invariant threads' chans'.
Proof.
*)

Lemma preservation (threads threads' : list expr) (chans chans' : heap) :
  invariant threads chans ->
  step threads chans threads' chans' ->
  invariant threads' chans'.
Proof.
  intros Hinv Hstep. unfold invariant in *.
  destruct Hinv as [Σ Hinv].
  destruct Hstep.
  destruct H.
  destruct H1.
  (* TODO: Need to extract type info here *)
  - exists Σ. iIntros "HΣ".
    iDestruct (Hinv with "HΣ") as "Hinv".
    unfold invariantΣ.
    rewrite right_id.
    iDestruct "Hinv" as "[Htyped Hbufs]". iFrame.
    iApply big_opL_insert_override; eauto.
    iIntros "H".
    iApply pure_step_ptyped; eauto.
    admit.
  - assert (invariantΣ Σ es h -∗ ⌜ ∃ vt ct', Σ !! c = Some (SendT vt ct') ⌝) by admit.

    (* chan_lits : expr -> list endpoint

    es !! i = Some (k (Val (Chan c))) ->
    invariantΣ Σ es h -∗
      invariantΣ (delete c Σ) (delete i es) h ∗ ptyped ∅ e UnitT *)

  (* Make separation logic over auth of Σ
     What's the adequacy statement for that logic?
        ((own (auth ∅)) ⊢ |=> ⌜ P ⌝) -> P
        (own (auth ∅) ⊢ invariant es h) -> ???
     *)


    assert (invariantΣ Σ es h -∗ ∃ vt ct', own {[c := ct ]} ∗ ⌜ Σ !! c = Some (SendT vt ct') ⌝) by admit.
    assert (∃ vt ct', Σ !! c = Some (SendT vt ct')) as (vt & ct' & HH).
    {
      eapply (own_adequacy Σ). rewrite Hinv. done.
    }
    exists (<[ c := ct' ]> Σ).
    iIntros "HΣ".
    rewrite right_id_L.
    replace ((<[c:=ct']> Σ)) with (delete c Σ ∪ {[ c := ct' ]}) by admit.
    assert (delete c Σ ##ₘ {[c := ct']}) by admit.
    iDestruct (own_distr with "HΣ") as "[HΣ1 HΣ2]"; eauto.

    admit.
  - admit.
  - exists (delete c Σ).
    admit.
  - admit.
Admitted.





  (*
  invariant : list expr -> heap -> Prop
  invariant' : list expr -> heap -> hProp
  invariant es h := ∃ Σ, invariant' es h Σ

  init : typed ∅ e UnitT -> invariant [e] []
  preservation : step es1 h1 es2 h2 -> invariant es1 h1 -> invariant es2 h2
  progress : invariant es1 h1 -> (final es1 h1) ∨ ∃ es2 h2, step es1 h1 es2 h2
  final es h := (∀ e, e∈es -> is_value e) ∧ ∀ b, b∈h -> b = []

  GOAL:
  type_safety :
    typed ∅ e UnitT ->
    steps [e] [] es h ->
    (final es h) ∨ ∃ es2 h2, step es h es2 h2

  1. Deadlock freedom for session types
  2. Deadlock freedom for locks + session types
  3. Program logic for deadlock freedom
     a) 1&2 als logical relation
     b) put forests in the hProp

  Conferences: LICS, ICFP, POPL
  *)