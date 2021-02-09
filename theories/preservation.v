From iris.proofmode Require Import tactics.
Require Import diris.util.
Require Export diris.htypesystem.

(*
  This predicate says that the types of the receives at the start of ct
  match the values in buf, and the rest of ct is equal to rest.
*)
Fixpoint buf_typed (buf : list val) (ct : chan_type) (rest : chan_type) : hProp :=
  match buf, ct with
                            (* add owner here *)
  | v::buf', RecvT t ct' => val_typed v t ∗ buf_typed buf' ct' rest
  (* | v::buf', SendT t ct' => ??? *)
  (* Add a rule for this to support asynchrous subtyping *)
  | [], ct => ⌜⌜ rest = ct ⌝⌝
  | _,_ => False
  end.

Definition dom_chans {V} (Σ : gmap endpoint V) : gset nat := set_map fst (dom (gset endpoint) Σ).

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
   ([∗ set] i∈dom_chans Σ ∪ dom_chans chans, bufs_typed chans Σ i)%I.

Definition invariant (chans : heap) (threads : list expr) : hProp :=
  ∃ Σ, own_auth Σ ∗ (* acyclic Σ ∗ *)
       ([∗ list] id↦e∈threads, ptyped0 e UnitT) ∗ (* add (Thread id) as owner *)
       heap_typed chans Σ.

Lemma elem_of_dom_chans_alt {A} (i : nat) (Σ : gmap endpoint A) :
  i ∈ dom_chans Σ <-> ∃ b, is_Some (Σ !! (i,b)).
Proof.
  unfold dom_chans.
  rewrite elem_of_map.
  setoid_rewrite elem_of_dom.
  split; intros H.
  + destruct H as [[c b] [H1 [x Hx]]]. simpl in *. subst.
    exists b. rewrite Hx. eexists. done.
  + destruct H as [b [x Hx]].
    exists (i,b). simpl. split;auto.
    rewrite Hx. eexists. done.
Qed.

Lemma not_elem_of_dom_chans_alt {A} (i : nat) (Σ : gmap endpoint A) :
  i ∉ dom_chans Σ <-> ∀ b, Σ !! (i,b) = None.
  unfold not. rewrite elem_of_dom_chans_alt.
  Proof.
  split; intros.
  - destruct (Σ !! (i,b)) eqn:E; naive_solver.
  - destruct H0 as [b Hb].
    rewrite H in Hb.
    destruct Hb. simplify_eq.
Qed.

Lemma dom_chans_Some {A : Type} { i : nat} { b : bool }  { Σ : gmap endpoint A } :
  is_Some (Σ !! (i,b)) ->
  i ∈ dom_chans Σ.
Proof.
  intros H.
  rewrite elem_of_map.
  exists (i,b); simpl. split; first done.
  rewrite elem_of_dom. done.
Qed.

Lemma dom_chans_in {A} (i : nat) (Σ : gmap endpoint A) :
  i ∈ dom_chans Σ ->
  ∃ b, is_Some (Σ !! (i,b)).
Proof.
  unfold dom_chans.
  rewrite elem_of_map.
  intros [x [H H']].
  setoid_rewrite elem_of_dom in H'.
  destruct x. eexists. simplify_eq. done.
Qed.

Lemma dom_chans_empty {A} :
  dom_chans (V:=A) ∅ = ∅.
Proof.
  apply elem_of_equiv_L. intros n.
  setoid_rewrite elem_of_dom_chans_alt.
  rewrite elem_of_empty.
  setoid_rewrite lookup_empty.
  setoid_rewrite is_Some_alt.
  split; intros []. done.
Qed.

Lemma dom_chans_None_delete {A} (Σ : gmap endpoint A) ep :
  Σ !! other ep = None ->
  dom_chans Σ ∖ {[ep.1]} = dom_chans (delete ep Σ).
Proof.
  intros H.
  apply elem_of_equiv_L.
  intros n.
  rewrite elem_of_difference.
  rewrite !elem_of_dom_chans_alt.
  rewrite not_elem_of_singleton.
  split.
  - intros [[b Hb] Hn]. exists b.
    rewrite lookup_delete_ne; eauto.
    destruct ep; simpl in *; intro; simplify_eq.
  - intros [b Hb].
    apply lookup_delete_is_Some in Hb as [].
    split; eauto.
    intro. destruct ep. simpl in *. simplify_eq.
    assert (b0 ≠ b) by naive_solver.
    destruct b,b0; simpl in *; eauto.
    + rewrite H in H1. destruct H1. simplify_eq.
    + rewrite H in H1. destruct H1. simplify_eq.
Qed.

Lemma lookup_delete_lr `{Countable K} {V} (x y : K) (m : gmap K V) :
  delete x m !! y = if (decide (x = y)) then None else m !! y.
Proof.
  case_decide.
  - subst. rewrite lookup_delete. done.
  - rewrite lookup_delete_ne; done.
Qed.

Lemma dom_chans_Some_delete {A} (Σ : gmap endpoint A) ep c :
  Σ !! other ep = Some c ->
  dom_chans (delete ep Σ) = dom_chans Σ.
Proof.
  intros H.
  apply elem_of_equiv_L.
  intros n.
  rewrite !elem_of_dom_chans_alt.
  split; intros HH.
  - destruct HH as [b [x Hx]].
    exists b. rewrite lookup_delete_lr in Hx.
    case_decide; simplify_eq. rewrite Hx. eexists. done.
  - destruct HH as [b [x Hx]].
    destruct ep.
    destruct (decide (n = c0)).
    + subst. exists (negb b0). simpl in *.
      rewrite lookup_delete_ne. rewrite H. eexists. done.
      destruct b0; naive_solver.
    + exists b.
      rewrite lookup_delete_ne.
      rewrite Hx. eexists. done.
      naive_solver.
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

Lemma heap_typed_doms_eq chans Σ :
  heap_typed chans Σ -∗ ∀ ep, ⌜ is_Some (Σ !! ep) <-> is_Some (chans !! ep) ⌝.
Proof.
  iIntros "H" (ep).
  unfold heap_typed.
  destruct (Σ !! ep) eqn:E; destruct (chans !! ep) eqn:F;
  rewrite !is_Some_alt; eauto.
  + assert (ep.1 ∈ dom_chans Σ).
    { rewrite elem_of_dom_chans_alt. exists ep.2. destruct ep.
      simpl. rewrite E. by eexists. }
    assert (ep.1 ∈ (dom_chans Σ ∪ dom_chans chans)).
    { apply elem_of_union. eauto. }
    clear H.
    iDestruct (big_sepS_delete with "H") as "[H _]"; first done.
    iDestruct (bufs_typed_is_Some with "H") as "%".
    rewrite E F in H.
    rewrite-> !is_Some_alt in H. done.
  + assert (ep.1 ∈ dom_chans chans).
    { rewrite elem_of_dom_chans_alt. exists ep.2. destruct ep.
      simpl. rewrite F. by eexists. }
    assert (ep.1 ∈ (dom_chans Σ ∪ dom_chans chans)).
    { apply elem_of_union. eauto. }
    clear H.
    iDestruct (big_sepS_delete with "H") as "[H _]"; first done.
    iDestruct (bufs_typed_is_Some with "H") as "%".
    rewrite E F in H.
    rewrite-> !is_Some_alt in H. done.
Qed.

Lemma dom_chans_mono {A B : Type} (a : gmap endpoint A) (b : gmap endpoint B) :
  (∀ ep, is_Some (a !! ep) -> is_Some (b !! ep)) -> dom_chans a ⊆ dom_chans b.
Proof.
  intros H.
  unfold dom_chans.
  apply set_map_mono; first done.
  apply elem_of_subseteq.
  intros x.
  rewrite !elem_of_dom.
  naive_solver.
Qed.

Lemma dom_chans_union {A B : Type} (a : gmap endpoint A) (b : gmap endpoint B) :
  (∀ ep, is_Some (b !! ep) -> is_Some (a !! ep)) -> dom_chans a ∪ dom_chans b = dom_chans a.
Proof.
  intros H. apply dom_chans_mono in H.
  rewrite-> subseteq_union_L in H.
  rewrite (comm_L union). done.
Qed.

Lemma heap_typed_dom_union chans Σ :
  heap_typed chans Σ -∗ ⌜ dom_chans Σ ∪ dom_chans chans = dom_chans Σ ⌝.
Proof.
  iIntros "H".
  iDestruct (heap_typed_doms_eq with "H") as "%".
  iPureIntro. apply dom_chans_union. intro. rewrite H. done.
Qed.

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


Lemma other_neq ep :
  ep ≠ other ep.
Proof.
  by destruct ep,b.
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

Lemma dom_chans_delete {A} (Σ : gmap endpoint A) ep :
  dom_chans (delete ep $ delete (other ep) Σ) = dom_chans Σ ∖ {[ep.1]}.
Proof.
  unfold dom_chans.
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



Lemma delete_both {A} (x : chan) (b : bool) (ep : endpoint) (m : gmap endpoint A) :
  x ≠ ep.1 ->
  (delete ep (delete (other ep) m)) !! (x,b) = m !! (x,b).
Proof.
  intros H.
  rewrite !lookup_delete_lr. destruct ep,b; simpl in *;
  repeat case_decide; simplify_eq; done.
Qed.

Lemma heap_typed_Some_split { Σ ep chans } :
  is_Some (Σ !! ep) ->
  heap_typed chans Σ ⊣⊢
  heap_typed (delete ep $ delete (other ep) chans)
             (delete ep $ delete (other ep) Σ) ∗
  bufs_typed chans Σ ep.1.
Proof.
  intros HSome.
  iSplit.
  - iIntros "H".
    iDestruct (heap_typed_doms_eq with "H") as "%".
    pose proof (dom_chans_Some HSome) as Hin.
    unfold heap_typed.
    rewrite dom_chans_union; last naive_solver.
    iDestruct (big_sepS_delete with "H") as "[Hep H]"; first done.
    assert (dom_chans (delete ep (delete (other ep) Σ))
      ∪ dom_chans (delete ep (delete (other ep) chans)) =
      dom_chans (delete ep (delete (other ep) Σ))) as ->.
    {
      apply dom_chans_union. intros ep'.
      rewrite !lookup_delete_lr.
      repeat case_decide; simplify_eq; rewrite is_Some_alt; try done.
      destruct (chans !! ep') eqn:E; rewrite E; try done. intros _.
      rewrite H. rewrite E. by eexists.
    }
    rewrite dom_chans_delete. iFrame.
    iApply (big_sepS_impl with "H").
    iModIntro.
    iIntros (x HH) "H".
    rewrite-> elem_of_difference, elem_of_singleton in HH.
    destruct HH.
    iApply (bufs_typed_relevant with "H"); intros b;
    rewrite delete_both; eauto.
  - iIntros "[H H2]".
    iDestruct (heap_typed_doms_eq with "H") as "%".
    unfold heap_typed.
    rewrite dom_chans_union; last naive_solver.
    rewrite dom_chans_delete.
    iApply big_sepS_delete.
    { apply elem_of_union. left.
      eapply dom_chans_Some.
      replace (ep) with (ep.1, ep.2) in HSome; first done.
      destruct ep; done. }
    iFrame.
    assert ((dom_chans Σ ∪ dom_chans chans) ∖ {[ep.1]} =
        dom_chans Σ ∖ {[ep.1]}) as HH.
    {
      rewrite difference_union_distr_l_L.
      rewrite (comm_L union).
      apply subseteq_union_L.
      rewrite elem_of_subseteq. intros x.
      rewrite <- !dom_chans_delete.
      rewrite !elem_of_dom_chans_alt.
      intros [b Hb].
      exists b. rewrite H. done.
    }
    rewrite HH.
    rewrite <-!dom_chans_delete.
    iApply (big_sepS_impl with "H").
    iModIntro.
    iIntros (x HHH) "H".
    assert (x ≠ ep.1).
    {
      rewrite dom_chans_delete //= in HHH.
      apply elem_of_difference in HHH as [? HHH].
      intro. apply HHH. apply elem_of_singleton. done.
    }
    iApply (bufs_typed_relevant with "H"); intros b;
    rewrite delete_both; eauto.
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
  - assert (dom_chans (<[ep:=ct]> Σ) = dom_chans Σ) as -> by admit.
    assert (ep.1 ∈ dom_chans Σ) by admit.
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
  iIntros (Hc HΣ) "H".
  assert (is_Some (Σ !! ep)).
  { eexists. done. }
  rewrite heap_typed_Some_split; last done.
  iDestruct "H" as "[H Hb]".
  assert (is_Some (<[ep:=ct]> Σ !! ep)).
  { rewrite lookup_insert. eexists. done. }
  rewrite (heap_typed_Some_split (Σ := <[ep:=ct]> Σ)); last done.
  rewrite <-(delete_commute (<[ep:=buf]> chans)).
  rewrite delete_insert_delete.
  rewrite <-(delete_commute (<[ep:=ct]> Σ)).
  rewrite delete_insert_delete.
  rewrite delete_commute.
  rewrite (delete_commute chans).
  iFrame.
  rewrite !bufs_typed_alt.
  iDestruct "Hb" as (rest) "[H1 H2]".
  rewrite Hc HΣ. simpl.
  iDestruct "H1" as "[Hv H1]". iFrame.
  iExists _.
  rewrite !lookup_insert. simpl. iFrame.
  rewrite !lookup_insert_ne; try iFrame;
  destruct ep; destruct b; intro; simplify_eq.
Qed.

Lemma heap_typed_close chans Σ ep :
  Σ !! ep = Some EndT ->
  heap_typed chans Σ -∗
  ⌜⌜ chans !! ep = Some [] ⌝⌝ ∗ heap_typed (delete ep chans) (delete ep Σ).
Proof.
  iIntros (HΣ) "H".
  assert (is_Some (Σ !! ep)).
  { eexists. done. }
  iDestruct (heap_typed_Some_split with "H") as "[H Hb]"; first done.
  iAssert (⌜ is_Some (chans !! ep) ⌝)%I as "%".
  { rewrite bufs_typed_is_Some. iDestruct "Hb" as "%". iPureIntro. rewrite H0. done. }
  destruct H0 as [buf Hbuf].
  rewrite bufs_typed_alt.
  iDestruct "Hb" as (rest) "[H1 H2]".
  rewrite HΣ Hbuf. simpl.
  destruct buf; simpl; eauto.
  iDestruct "H1" as "%". subst.
  iSplit; eauto.
  unfold heap_typed.
  rewrite !dom_chans_delete.
  destruct (chans !! other ep) eqn:E.
  - destruct (Σ !! other ep) eqn:F;simpl; eauto.
    erewrite dom_chans_Some_delete; eauto.
    pose proof (dom_chans_Some_delete _ _ _ E).
    rewrite H0.
    assert (ep.1 ∈ dom_chans Σ ∪ dom_chans chans).
    { apply elem_of_union. left.
      destruct ep. simpl in *. eapply dom_chans_Some. done.  }
    iApply big_sepS_delete; first done.
    iSplitL "H2".
    + rewrite bufs_typed_alt.
      iExists _.
      rewrite !lookup_delete. simpl.
      iSplit; first done.
      simpl.
      rewrite !lookup_delete_ne; auto using other_neq.
      rewrite E F. simpl. done.
    + rewrite difference_union_distr_l_L.
      iApply (big_sepS_impl with "H").
      iModIntro.
      iIntros (x HH) "H".
      apply elem_of_union in HH.
      assert (x ≠ ep.1).
      { intro. subst.
        destruct HH;
        apply elem_of_difference in H2 as [? H3];
        apply H3; subst; apply elem_of_singleton; done. }
      iApply (bufs_typed_relevant with "H"); intro b;
      rewrite delete_both; eauto; destruct ep; simpl in *;
      rewrite lookup_delete_ne; auto; intro; simplify_eq.
  - simpl. destruct (Σ !! other ep) eqn:F; eauto.
    iClear "H2".
    rewrite !dom_chans_None_delete; eauto.
    rewrite (delete_notin chans (other ep)); eauto.
    rewrite !(delete_notin Σ (other ep)); eauto.
Qed.

Lemma heap_typed_fork chans Σ i ct :
  chans !! (i,true) = None ->
  chans !! (i,false) = None ->
  heap_typed chans Σ -∗
  heap_typed (<[ (i,true) := [] ]> $ <[ (i,false) := [] ]> chans)
             (<[ (i,true) := ct ]> $ <[ (i,false) := dual ct ]> Σ).
Proof.
  iIntros (H1 H2) "H".
  assert (is_Some ((<[(i, true):=ct]> (<[(i, false):=dual ct]> Σ) !! (i,true)))).
  { rewrite lookup_insert. eexists. done. }
  rewrite (heap_typed_Some_split H); simpl.
  iSplitL "H".
  - rewrite delete_commute.
    rewrite !delete_insert_delete.
    rewrite delete_commute.
    rewrite !delete_insert_delete.
    rewrite (delete_commute (<[(i, true):=[]]> (<[(i, false):=[]]> chans))).
    rewrite !delete_insert_delete.
    rewrite (delete_commute (<[(i, false):=[]]> chans)).
    rewrite !delete_insert_delete.
    rewrite (delete_notin chans); eauto.
    rewrite (delete_notin chans); eauto.
    clear H ct.
    unfold heap_typed.
    destruct (decide (i ∈ dom_chans Σ ∪ dom_chans chans)).
    + iDestruct (big_sepS_delete with "H") as "H"; first done.
      iDestruct "H" as "[Hb H]".
      rewrite dom_chans_delete. simpl.
      iDestruct "Hb" as (rest) "[H1 H2]".
      rewrite H1 H2. simpl.
      destruct (Σ !! (i,true)) eqn:E; eauto.
      destruct (Σ !! (i,false)) eqn:F; eauto.
      iClear "H1 H2".
      assert ((dom_chans Σ ∖ {[i]} ∪ dom_chans chans) =
        ((dom_chans Σ ∪ dom_chans chans) ∖ {[i]})) as ->.
      {
        rewrite difference_union_distr_l_L. f_equal.
        rewrite<- (dom_chans_delete _ (i,true)). simpl.
        rewrite !delete_notin; eauto.
      }
      iApply (big_sepS_impl with "H").
      iModIntro.
      iIntros (x H) "H".
      iApply (bufs_typed_relevant with "H"); intro; eauto.
      apply elem_of_difference in H as [].
      assert (x ≠ i).
      { intro. apply H0. apply elem_of_singleton. done. }
      rewrite !lookup_delete_ne; first done; intro; simplify_eq.
    + rewrite-> not_elem_of_union in n.
      destruct n as [n n'].
      rewrite-> not_elem_of_dom_chans_alt in n.
      rewrite !delete_notin; eauto.
  - unfold bufs_typed. iExists ct.
    rewrite !lookup_insert.
    rewrite lookup_insert_ne; last naive_solver.
    rewrite !lookup_insert.
    rewrite lookup_insert_ne; last naive_solver.
    rewrite !lookup_insert. simpl. done.
Qed.

Lemma heap_typed_emp chans :
  heap_typed chans ∅ -∗ ⌜ chans = ∅ ⌝.
Proof.
  iIntros "H".
  iDestruct (heap_typed_doms_eq with "H") as "%".
  iPureIntro.
  apply map_empty.
  intros ep.
  specialize (H ep).
  destruct (chans !! ep) eqn:E; auto.
  exfalso.
  rewrite lookup_empty in H.
  rewrite-> is_Some_alt in H.
  rewrite H. by eexists.
Qed.

Lemma heap_typed_init :
  ⊢ heap_typed ∅ ∅.
Proof.
  unfold heap_typed. rewrite !dom_chans_empty.
  rewrite left_id_L.
  iIntros. iApply big_sepS_empty. done.
Qed.

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
    assert (Γ2 = ∅).
    { destruct HH. symmetry in H0.
      assert (Γ1 = ∅). eapply map_positive_l; done. subst.
      rewrite left_id in H0. done. }
    subst. done.
  - iDestruct "Ht" as (Γ1 Γ2 H) "[_ [_ Ht]]".
    assert (Γ2 = ∅).
    { destruct H. symmetry in H.
      assert (Γ1 = ∅). eapply map_positive_l; done. subst.
      rewrite left_id in H. done. }
    subst. done.
  - iDestruct "Ht" as (t' Γ1 Γ2 H) "[[% Hv] Ht]".
    destruct H as (H & _ & _).
    subst. rewrite left_id in H. subst. rewrite left_id.
    replace (∅ : envT) with (delete x {[ x := t']} : envT); last first.
    { apply delete_singleton. }
    iApply (subst_ptyped with "Hv Ht").
    rewrite lookup_singleton. done.
  - iDestruct "Ht" as (Γ1 Γ2 (H & Hd)) "[% Ht]".
    destruct H0. subst. rewrite left_id in H. subst. done.
  - iDestruct "Ht" as (t1 t2 Γ1 Γ2 (? & ? & ? & ?)) "[[% Hv] Ht]".
    iDestruct "Hv" as (t1' t2' HH) "[Hv1 Hv2]".
    simplify_eq.
    rewrite left_id in H0. subst.
    rewrite left_id.
    replace (∅ : envT) with (delete x1 $ delete x2 $ ({[x1 := t1']} ∪ {[x2 := t2']}) : envT); last first.
    { rewrite delete_union delete_singleton right_id.
      rewrite delete_singleton_ne; eauto.
      apply delete_singleton. }
    iApply (subst_ptyped with "Hv1 [Ht Hv2]").
    + rewrite delete_union delete_singleton right_id.
      rewrite delete_singleton_ne; eauto. rewrite lookup_singleton. done.
    + iApply (subst_ptyped with "Hv2 Ht").
      rewrite lookup_union lookup_singleton lookup_singleton_ne; eauto.
Qed.

Lemma pure_step_ptyped0 e e' t :
  pure_step e e' -> ptyped0 e t -∗ ptyped0 e' t.
Proof.
  iIntros (Hs) "Ht".
  iApply ptyped_ptyped0.
  iDestruct (ptyped0_ptyped with "Ht") as "Ht".
  iApply (pure_step_ptyped with "Ht"). done.
Qed.

Definition ct_tail (ct : chan_type) : chan_type :=
    match ct with
    | RecvT v ct' => ct'
    | SendT v ct' => ct'
    | EndT => EndT
    end.

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

Lemma typed0_ctx_typed0_iff B k e :
  ctx k -> ptyped0 (k e) B ⊣⊢
  ∃ A, ctx_typed0 k A B ∗ ptyped0 e A.
Proof.
  intros Hk.
  iIntros.
  iSplit.
  - iApply typed0_ctx_typed0. done.
  - iIntros "H". iDestruct "H" as (A) "[Hct Ht]".
    iApply (ctx_subst0 with "Hct"). done.
Qed.

Lemma rw_helper1 {T} (P Q : T -> hProp) (R : hProp) :
  (∃ x, P x ∗ R ∗ Q x) ⊣⊢ R ∗ ∃ x, P x ∗ Q x.
Proof.
  iIntros.
  iSplit; iIntros "H".
  - iDestruct "H" as (x) "(H1 & H2 & H3)". iFrame.
    iExists x. iFrame.
  - iDestruct "H" as "[H1 H2]".
    iDestruct "H2" as (x) "[H2 H3]".
    iExists x. iFrame.
Qed.

Lemma rw_helper2 {T} (P : T -> hProp) (Q : hProp) :
  (∃ x, P x) ∗ Q ⊣⊢ ∃ x, P x ∗ Q.
Proof.
  iIntros.
  iSplit; iIntros "H".
  - iDestruct "H" as "[H1 H2]".
    iDestruct "H1" as (x) "H1".
    iExists x. iFrame.
  - iDestruct "H" as (x) "[H1 H2]". iFrame.
    iExists x. iFrame.
Qed.

Lemma rw_helper3 (P : hProp) :
  P ∗ emp ⊣⊢ P.
Proof.
  rewrite right_id. done.
Qed.

Lemma preservation (threads threads' : list expr) (chans chans' : heap) :
  step threads chans threads' chans' ->
  invariant chans threads ==∗
  invariant chans' threads'.
Proof.
  iIntros (Hstep) "Hinv".
  destruct Hstep.
  destruct H.
  iDestruct "Hinv" as (Σ) "(Hown & Hthreads & Hheap)".
  rewrite big_sepL_delete; last done.
  iDestruct "Hthreads" as "[Ht Hthreads]".
  iDestruct (typed0_ctx_typed0 with "Ht") as (t) "[Hct Ht]"; first done.
  unfold invariant.
  rewrite rw_helper1.
  rewrite big_sepL_app.
  rewrite (big_sepL_delete _ (<[i:=k e']> es) i (k e')); last first.
  { apply list_lookup_insert. eapply lookup_lt_Some. done. }
  iDestruct (big_opL_insert_override _ _ _ (k e') _ H0 with "[] Hthreads") as "Hthreads".
  { iIntros "H". case_decide; iFrame. done. }
  iFrame.
  rewrite typed0_ctx_typed0_iff; last done.
  rewrite rw_helper2.
  rewrite rw_helper2.
  iExists t. iFrame.
  rewrite (comm (∗)%I).
  rewrite rw_helper2.

  revert H1. clear. intros Hstep. (* clean up the goal *)

  destruct Hstep;
  try (setoid_rewrite big_sepL_nil; setoid_rewrite rw_helper3).
  - iExists Σ. iFrame. iModIntro. by iApply (pure_step_ptyped0 with "Ht").
  - simpl. iDestruct "Ht" as (r t' ->) "[H Hv]".
    iDestruct "H" as (r0) "[% H]". simplify_eq.
    iDestruct (own_lookup with "[Hown H]") as "%"; first iFrame.
    iDestruct (heap_typed_send _ _ _ _ _ _ H0 with "Hv Hheap") as (buf' HH) "Hsend".
    iExists (<[ c := r ]> Σ).
    rewrite H in HH. simplify_eq. iFrame.
    iMod (update with "[Hown H]") as "[H1 H2]"; first iFrame.
    iFrame. iExists r. iFrame. done.
  - simpl. iDestruct "Ht" as (t' r ->) "Ht".
    iDestruct "Ht" as (r0 HH) "H". simplify_eq.
    iDestruct (own_lookup with "[Hown H]") as "%"; first iFrame.
    iDestruct (heap_typed_recv _ _ _ _ _ _ _ H with "Hheap") as "[Hheap Hv]"; first done.
    iExists _. iFrame.
    iMod (update with "[Hown H]") as "[H1 H2]"; iFrame. iModIntro.
    iExists _,_. iFrame.
    iSplit. done.
    iExists _. iSplit; done.
  - simpl. iDestruct "Ht" as (r r' HH) "H". simplify_eq.
    iDestruct (own_lookup with "[Hown H]") as "%"; first iFrame.
    iDestruct (heap_typed_close _ _ _ H0 with "Hheap") as (HH) "Hheap".
    iExists (delete c Σ).
    iMod (deallocate with "[Hown H]"); iFrame.
    done.
  - simpl. iDestruct "Ht" as (r ->) "Hv".
    iAssert (⌜ ∀ x,  Σ !! x = None <-> h !! x = None ⌝)%I as "%".
    { iDestruct (heap_typed_doms_eq with "Hheap") as "%".
      iPureIntro. intros x. rewrite !eq_None_not_Some. naive_solver. }
    iDestruct (heap_typed_fork _ _ _ _ H H0 with "Hheap") as "H".
    iExists _. iFrame. rewrite right_id.
    iMod (allocate with "Hown") as "[Hown H1]".
    { rewrite H1. exact H0. }
    iMod (allocate with "Hown") as "[Hown H2]".
    { rewrite lookup_insert_ne. rewrite H1. exact H. done. }
    iModIntro. iFrame.
    iSplitL "H2". { iExists _. iFrame. done. }
    iExists _. iFrame.
    iExists _. iFrame.
    done.
Qed.

(*
What is leak freedom? (Coq)
What is type safety? (uPred)
What is type safety? (Coq)
What is progress? (uPred)
*)



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