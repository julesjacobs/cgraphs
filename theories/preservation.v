From iris.proofmode Require Import tactics.
Require Import diris.util.
Require Export diris.htypesystem.

(*
  This predicate says that the types of the receives at the start of ct
  match the values in buf, and the rest of ct is equal to rest.
*)
Fixpoint buf_typed (buf : list val) (ct : chan_type) (rest : chan_type) : oProp :=
  match buf, ct with
                            (* add owner here *)
  | v::buf', RecvT t ct' => val_typed v t ∗ buf_typed buf' ct' rest
  (* | v::buf', SendT t ct' => ??? *)
  (* Add a rule for this to support asynchrous subtyping *)
  | [], ct => ⌜⌜ rest = ct ⌝⌝
  | _,_ => False
  end.

Definition dom_chans {V} (Σ : gmap endpoint V) : gset nat := set_map fst (dom (gset endpoint) Σ).

Definition buf_typed' (bufq : option (list val)) (ctq : option chan_type) (rest : chan_type) : oProp :=
    match bufq, ctq with
    | Some buf, Some ct => buf_typed buf ct rest
    | None, None => ⌜⌜ rest = EndT ⌝⌝
    | _,_ => False
    end.

Definition bufs_typed (chans : heap) (Σ : heapT) (i : chan) : oProp :=
  ∃ rest, buf_typed' (chans !! (i,true)) (Σ !! (i,true)) rest ∗
          buf_typed' (chans !! (i,false)) (Σ !! (i,false)) (dual rest).

Definition heap_typed (chans : heap) (Σ : heapT) : iProp :=
   ([∗ set] i∈dom_chans Σ ∪ dom_chans chans, owned (Chan i) (bufs_typed chans Σ i))%I.

Definition invariant (chans : heap) (threads : list expr) : iProp :=
  ∃ Σ, own_auth Σ ∗
       ([∗ list] id↦e∈threads, owned (Thread id) (ptyped0 e UnitT)) ∗
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

Lemma buf_typed_push buf t ct rest v o :
  val_typed v t o -∗
  buf_typed buf ct (RecvT t rest) o -∗
  buf_typed (buf ++ [v]) ct rest o.
Proof.
  iIntros "Hv Hb".
  iInduction buf as [] "IH" forall (ct rest); simpl.
  - iDestruct "Hb" as "<-". iFrame. done.
  - destruct ct; eauto.
    iDestruct "Hb" as "[Hv' H]".
    iDestruct ("IH" with "Hv H") as "HH". iFrame.
Qed.

Lemma buf_typed_pop buf t ct rest v o :
  buf_typed (v::buf) (RecvT t ct) rest o -∗
  buf_typed buf ct rest o ∗ val_typed v t o.
Proof.
  iIntros "[? ?]". simpl. iFrame.
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
  ∃ rest, buf_typed' (chans !! ep) (Σ !! ep) rest (Chan ep.1) ∗
          buf_typed' (chans !! other ep) (Σ !! other ep) (dual rest) (Chan ep.1).
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
  val_typed v t (Chan ep.1) -∗
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

Lemma heap_typed_recv chans Σ t v ep ct buf :
  chans !! ep = Some (v::buf) ->
  Σ !! ep = Some (RecvT t ct) ->
  heap_typed chans Σ -∗
  heap_typed (<[ ep := buf ]> chans) (<[ ep := ct ]> Σ) ∗ val_typed v t (Chan ep.1).
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

Lemma pure_step_ptyped e e' t o :
  pure_step e e' -> ptyped ∅ e t o -∗ ptyped ∅ e' t o.
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

Lemma pure_step_ptyped0 e e' t o :
  pure_step e e' -> ptyped0 e t o -∗ ptyped0 e' t o.
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
                     (P : nat -> A -> iProp) :
  l !! k = Some y ->
  (P k y -∗ P k y') -∗
  ([∗ list] i↦x∈l, P i x) -∗
  ([∗ list] i↦x∈(<[ k := y' ]> l), P i x).
Proof.
  iIntros (?) "HP H".
  iDestruct (big_sepL_insert_acc with "H") as "[Hy H]"; first done.
  iApply "H". iApply "HP". done.
Qed.

Lemma typed0_ctx_typed0_iff B k e o:
  ctx k -> ptyped0 (k e) B o ⊣⊢
  ∃ A, ctx_typed0 k A B o ∗ ptyped0 e A o.
Proof.
  intros Hk.
  iIntros.
  iSplit.
  - iApply typed0_ctx_typed0. done.
  - iIntros "H". iDestruct "H" as (A) "[Hct Ht]".
    iApply (ctx_subst0 with "Hct"). done.
Qed.

Lemma rw_helper1 {T} (P Q : T -> iProp) (R : iProp) :
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

Lemma rw_helper2 {T} (P : T -> iProp) (Q : iProp) :
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

Fixpoint val_typed' (v : val) (t : type) (o : owner) : iProp := (* extra argument: owner*)
  match t with
  | UnitT => ⌜⌜ v = UnitV ⌝⌝
  | NatT => ∃ n, ⌜⌜ v = NatV n ⌝⌝
  | PairT t1 t2 => ∃ a b, ⌜⌜ v = PairV a b ⌝⌝ ∗ val_typed' a t1 o ∗ val_typed' b t2 o
  | FunT t1 t2 => ∃ x e, ⌜⌜ v = FunV x e ⌝⌝ ∗ ptyped {[ x := t1 ]} e t2 o
  | ChanT r => ∃ c, ⌜⌜ v = ChanV c ⌝⌝ ∗ own c r o
  end.

Lemma val_typed_switch v t o :
  val_typed v t o ⊣⊢ val_typed' v t o.
Proof.
  iIntros. iSplit; iIntros "H".
  - iInduction t as [] "IH" forall (v); simpl; destruct v; simpl;
    repeat iDestruct "H" as (?) "H"; try iDestruct "H" as "%";
    simplify_eq; repeat iExists _; try done; iSplit; try done.
    iDestruct "H" as "[H1 H2]".
    iSplitL "H1". { by iApply "IH". }
    by iApply "IH1".
  - iInduction t as [] "IH" forall (v); simpl; destruct v; simpl;
    repeat iDestruct "H" as (?) "H"; try iDestruct "H" as "%";
    simplify_eq; repeat iExists _; try done; iSplit; try done.
    iDestruct "H" as "[H1 H2]".
    iSplitL "H1". { by iApply "IH". }
    by iApply "IH1".
Qed.

Lemma val_typed_move_tc Σ c v t i t' :
  own_auth Σ ∗
  own c t (Thread i) ∗
  val_typed v t' (Thread i)
  ==∗
  own_auth Σ ∗
  own c t (Thread i) ∗
  val_typed v t' (Chan c.1)
with ptyped_move_tc Γ Σ c e t i t' :
  own_auth Σ ∗
  own c t (Thread i) ∗
  ptyped Γ e t' (Thread i)
  ==∗
  own_auth Σ ∗
  own c t (Thread i) ∗
  ptyped Γ e t' (Chan c.1).
Proof.
  - iIntros "(Hown & H & Hv)". rewrite !val_typed_switch.
    iInduction t' as [] "IH" forall (v); simpl.
    + by iFrame.
    + by iFrame.
    + iDestruct "Hv" as (a b ->) "[Hv1 Hv2]".
      iMod ("IH" with "Hown H Hv1") as "(Hown & H & Hv1)".
      iMod ("IH1" with "Hown H Hv2") as "(Hown & H & Hv2)".
      iFrame. iModIntro. iExists _,_.
      iSplit; first done. iFrame.
    + iDestruct "Hv" as (x e ->) "He".
      iMod (ptyped_move_tc with "[Hown H He]") as "(Hown & H & He)"; first by iFrame.
      iFrame. iModIntro. iExists _,_. iSplit; first done. iFrame.
    + iDestruct "Hv" as (c' ->) "Hv".
      iMod (own_move_tc with "[Hown Hv H]") as "(Hown & Hv & H)"; first by iFrame.
      iFrame. eauto.
  - iIntros "(Hown & H & Hv)".
    iInduction e as [] "IH" forall (t' Γ); simpl.
    + iDestruct "Hv" as (->) "Hv".
      iMod (val_typed_move_tc with "[Hown H Hv]") as "(Hown & H & Hv)"; first by iFrame.
      iFrame. done.
    + by iFrame.
    + iDestruct "Hv" as (? ? ?) "(? & He1 & He2)".
      iMod ("IH" with "Hown H He1") as "(Hown & H & He1)".
      iMod ("IH1" with "Hown H He2") as "(Hown & H & He2)".
      iFrame. iModIntro. iExists _,_,_. iFrame.
    + iDestruct "Hv" as (? ?) "(? & He)".
      iMod ("IH" with "Hown H He") as "(Hown & H & He)".
      iFrame. iModIntro. iExists _,_. iFrame.
    + iDestruct "Hv" as (? ? ? ?) "(? & He1 & He2)".
      iMod ("IH" with "Hown H He1") as "(Hown & H & He1)".
      iMod ("IH1" with "Hown H He2") as "(Hown & H & He2)".
      iFrame. iModIntro. repeat iExists _. iFrame.
    + iDestruct "Hv" as (? ?) "(? & He)".
      iMod ("IH" with "Hown H He") as "(Hown & H & He)".
      iFrame. iModIntro. repeat iExists _. iFrame.
    + iDestruct "Hv" as (? ? ?) "(? & He1 & He2)".
      iMod ("IH" with "Hown H He1") as "(Hown & H & He1)".
      iMod ("IH1" with "Hown H He2") as "(Hown & H & He2)".
      iFrame. iModIntro. repeat iExists _. iFrame.
    + iDestruct "Hv" as (? ?) "(? & He1 & He2)".
      iMod ("IH" with "Hown H He1") as "(Hown & H & He1)".
      iMod ("IH1" with "Hown H He2") as "(Hown & H & He2)".
      iFrame. iModIntro. repeat iExists _. iFrame.
    + iDestruct "Hv" as (? ? ? ?) "(? & He1 & He2)".
      iMod ("IH" with "Hown H He1") as "(Hown & H & He1)".
      iMod ("IH1" with "Hown H He2") as "(Hown & H & He2)".
      iFrame. iModIntro. repeat iExists _. iFrame.
    + iDestruct "Hv" as (? ?) "(? & He1 & He2)".
      iMod ("IH" with "Hown H He1") as "(Hown & H & He1)".
      admit.
    + iDestruct "Hv" as (?) "(? & He)".
      iMod ("IH" with "Hown H He") as "(Hown & H & He)".
      iFrame. iModIntro. repeat iExists _. iFrame.
    + iDestruct "Hv" as "[? Hv]".
      iMod ("IH" with "Hown H Hv") as "(Hown & H & Hv)".
      by iFrame.
 Admitted.

Lemma val_typed_move_ct Σ c v t i t' :
  own_auth Σ ∗
  own c t (Thread i) ∗
  val_typed v t' (Chan c.1)
  ==∗
  own_auth Σ ∗
  own c t (Thread i) ∗
  val_typed v t' (Thread i).
Proof. Admitted.

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

  revert H1 H0. clear. intros Hstep Hi. (* clean up the goal *)

  destruct Hstep; simpl;
  repeat (setoid_rewrite (right_id emp%I (∗)%I)).
  - iExists Σ. iFrame. iModIntro. by iApply (pure_step_ptyped0 with "Ht").
  - iDestruct "Ht" as (r t' ->) "[H Hv]".
    iDestruct "H" as (r0 [=<-]) "H".
    iDestruct (own_lookup with "[$Hown $H]") as "%".
    iMod (val_typed_move_tc with "[Hown H Hv]") as "(Hown & H & Hv)"; first by iFrame.
    iDestruct (heap_typed_send with "Hv Hheap") as (buf' HH) "Hsend"; first done.
    iExists (<[ c := r ]> Σ).
    simplify_eq. iFrame.
    iMod (own_mutate with "[$Hown $H]") as "[$ H2]"; eauto.
  - iDestruct "Ht" as (t' r ->) "Ht".
    iDestruct "Ht" as (r0 HH) "H". simplify_eq.
    iDestruct (own_lookup with "[Hown H]") as "%"; first iFrame.
    iDestruct (heap_typed_recv with "Hheap") as "[Hheap Hv]"; [done..|].
    iMod (val_typed_move_ct with "[Hown H Hv]") as "(Hown & H & Hv)"; first by iFrame.
    iExists _.
    iMod (own_mutate with "[Hown H]") as "[H1 H2]"; iFrame. iModIntro.
    iExists _,_. iFrame.
    iSplit. done.
    iExists _. iSplit; done.
  - iDestruct "Ht" as (r r' HH) "H". simplify_eq.
    iDestruct (own_lookup with "[Hown H]") as %HΣc; first iFrame.
    iDestruct (heap_typed_close with "Hheap") as (HH) "Hheap"; first done.
    iExists (delete c Σ).
    iMod (own_dealloc with "[Hown H]"); iFrame.
    done.
  - iDestruct "Ht" as (r ->) "Hv".
    iAssert (⌜ ∀ x,  Σ !! x = None <-> h !! x = None ⌝)%I as "%".
    { iDestruct (heap_typed_doms_eq with "Hheap") as "%".
      iPureIntro. intros x. rewrite !eq_None_not_Some. naive_solver. }
    iDestruct (heap_typed_fork _ _ _ _ H H0 with "Hheap") as "H".
    iExists _. iFrame "H".
    iMod (own_alloc _ _ (i0,true) Σ r (dual r) with "Hown") as "(Hown & H1 & H2)"; try (by rewrite H1); first last.
    {
      (* Move the closure over the channel *)
      iMod (val_typed_move_tc with "[Hown H1 Hv]") as "(Hown & H1 & Hv)"; simpl; first by iFrame.
      iMod (val_typed_move_ct with "[Hown H2 Hv]") as "(Hown & H2 & Hv)"; simpl; first by iFrame.
      (* Build up the invariant again *)
      iFrame "Hown". simpl.
      iModIntro.
      iSplitL "H1"; first by eauto with iFrame.
      iExists (ChanT (dual r)).
      iSplitL "Hv"; eauto.
    }
    rewrite insert_length.
    apply lookup_lt_Some in Hi. lia.
Qed.

Lemma preservationN (threads threads' : list expr) (chans chans' : heap) :
  steps threads chans threads' chans' ->
  invariant chans threads ==∗
  invariant chans' threads'.
Proof.
  iIntros (Hsteps) "Hinv".
  iInduction Hsteps as [] "IH"; last done.
  iMod (preservation with "Hinv") as "H"; eauto.
  iMod ("IH" with "H"). done.
Qed.

Lemma invariant_init (e : expr) :
  typed ∅ e UnitT -> own_auth ∅ ⊢ invariant ∅ [e].
Proof.
  iIntros (H) "H".
  iExists ∅. iFrame. simpl.
  iSplit.
  - rewrite right_id.
    iApply ptyped_ptyped0.
    iApply typed_ptyped.
    iPureIntro. done.
  - unfold heap_typed.
    unfold dom_chans.
    rewrite !dom_empty_L.
    rewrite set_map_empty.
    rewrite left_id_L.
    rewrite big_sepS_empty.
    done.
Qed.

Definition is_val (e : expr) :=
  ∃ v, e = Val v.
Definition head_waiting (e : expr) (h : heap) :=
  ∃ c, e = Recv (Val (ChanV c)) ∧ h !! c = Some [].
Definition waiting (e : expr) (h : heap) :=
  ∃ e' k, e = k e' ∧ ctx k ∧ head_waiting e' h.
Definition head_reducible (e : expr) (h : heap) :=
  ∃ e' h' ts, head_step e h e' h' ts.
Definition reducible (e : expr) (h : heap) :=
  ∃ e' h' ts, ctx_step e h e' h' ts.
Definition waiting_or_reducible e h :=
  waiting e h ∨ reducible e h.

Lemma wr_head_step e h e' h' ts :
  head_step e h e' h' ts ->
  waiting_or_reducible e h.
Proof.
  intros H.
  right.
  exists e', h', ts.
  eapply (Ctx_step id). { constructor. }
  done.
Qed.

Lemma wr_ctx k e h :
  ctx1 k ->
  waiting_or_reducible e h ->
  waiting_or_reducible (k e) h.
Proof.
  intros Hk Hwr.
  unfold waiting_or_reducible in *.
  destruct Hwr.
  - left. unfold waiting in *.
    destruct H as (e' & k' & -> & Hk' & Hw).
    exists e', (k ∘ k').
    repeat split; eauto.
    apply (Ctx_cons k); done.
  - right. unfold reducible in *.
    destruct H as (e' & h' & ts & Hcs).
    destruct Hcs.
    do 3 eexists.
    apply (Ctx_step (k ∘ k0)); last done.
    apply (Ctx_cons k); done.
Qed.

Lemma heap_fresh (h : heap) :
  ∃ i, ∀ b, h !! (i,b) = None.
Proof.
  exists (fresh $ set_map (D:=gset nat) fst (dom (gset (nat*bool)) h)). intros b.
  pose proof (is_fresh (set_map (D:=gset nat) fst (dom (gset (nat * bool)) h))) as H.
  remember (fresh $ set_map (D:=gset nat) fst (dom (gset (nat*bool)) h)) as i.
  clear Heqi.
  destruct (h !! (i,b)) eqn:E; last done.
  exfalso. apply H. clear H.
  apply elem_of_map. exists (i,b).
  simpl; split; eauto.
  apply elem_of_dom. by eexists.
Qed.

Lemma heap_typed_send_info Σ c t r h :
  Σ !! c = Some (SendT t r) ->
  heap_typed h Σ -∗
  ⌜∃ buf : list val, h !! other c = Some buf⌝.
Proof.
  iIntros (H) "H".
  iDestruct (heap_typed_Some_split with "H") as "[_ H]";
    first (erewrite H; by eexists).
  rewrite bufs_typed_alt.
  iDestruct "H" as (rest) "[H1 H2]".
  destruct (h !! other c) eqn:E; simpl; first eauto.
  destruct (Σ !! other c) eqn:F; first eauto.
  iDestruct "H2" as %G. destruct rest; simplify_eq.
  destruct (h !! c) eqn:E';
  destruct (Σ !! c) eqn:F'; eauto.
  simplify_eq. simpl.
  destruct l; simpl; eauto.
  iDestruct "H1" as "%".
  simplify_eq.
Qed.

Lemma heap_typed_close_info Σ c h :
  Σ !! c = Some EndT ->
  heap_typed h Σ -∗
  ⌜h !! c = Some []⌝.
Proof.
  iIntros (H) "H".
  iDestruct (heap_typed_Some_split with "H") as "[_ H]";
    first (erewrite H; by eexists).
  rewrite bufs_typed_alt.
  iDestruct "H" as (rest) "[H1 H2]".
  rewrite H.
  destruct (h !! c) eqn:E; simpl; eauto.
  iClear "H2".
  destruct l; simpl; eauto.
Qed.

Ltac fin := done || by constructor.

Lemma progress1 Σ h e t o :
  own_auth Σ -∗
  heap_typed h Σ -∗
  ptyped0 e t o -∗
  ⌜is_val e ∨ waiting_or_reducible e h⌝.
Proof.
  iIntros "Hown Hheap Ht".
  iDestruct (heap_typed_doms_eq with "Hheap") as %E.
  iInduction e as [] "IH" forall (t); simpl.
  - iPureIntro. left. by eexists.
  - done.
  - iDestruct "Ht" as (t') "[H1 H2]".
    iDestruct ("IH" with "Hown Hheap H1") as %H1.
    iDestruct ("IH1" with "Hown Hheap H2") as %H2.
    iRight.
    destruct H1 as [[v1 ->]|H1].
    + destruct H2 as [[v2 ->]|H2].
      * simpl. rewrite val_typed_switch /=.
        iDestruct "H1" as (x e ->) "H1".
        iPureIntro. eapply wr_head_step.
        constructor. constructor.
      * iPureIntro. apply (wr_ctx (λ x, App _ x)); fin.
    + iPureIntro. apply (wr_ctx (λ x, App x _)); fin.
  - iPureIntro. right.
    eapply wr_head_step.
    constructor. constructor.
  - iRight.
    iDestruct "Ht" as (r t' ->) "[H1 H2]".
    iDestruct ("IH" with "Hown Hheap H1") as %H1.
    iDestruct ("IH1" with "Hown Hheap H2") as %H2.
    destruct H1 as [[v1 ->]|H1].
    + destruct H2 as [[v2 ->]|H2].
      * simpl. rewrite val_typed_switch /=.
        iDestruct "H1" as (c ->) "H1".
        iDestruct (own_lookup with "[$Hown $H1]") as %H.
        iDestruct (heap_typed_send_info with "Hheap") as %[buf Hbuf]; first done.
        iPureIntro. eapply wr_head_step.
        eapply Send_step. done.
      * iPureIntro. apply (wr_ctx (λ x, Send _ x)); fin.
    + iPureIntro. apply (wr_ctx (λ x, Send x _)); fin.
  - iRight.
    iDestruct "Ht" as (t' r ->) "H".
    iDestruct ("IH" with "Hown Hheap H") as %H.
    destruct H as [[v ->]|H].
    + simpl. rewrite val_typed_switch /=.
      iDestruct "H" as (c ->) "H".
      iDestruct (own_lookup with "[$Hown $H]") as %H.
      assert (is_Some (h !! c)) as [buf Hbuf]. { rewrite <-E. by eexists. }
      destruct buf.
      * iPureIntro. left. exists (Recv (Val (ChanV c))), id.
        split; first done.
        split; first by constructor.
        unfold head_waiting. eauto.
      * iPureIntro. eapply wr_head_step.
        eapply Recv_step. done.
    + iPureIntro. apply (wr_ctx (λ x, Recv x)); fin.
  - iRight.
    iDestruct "Ht" as (t') "[H1 H2]".
    iDestruct ("IH" with "Hown Hheap H1") as %H1.
    destruct H1 as [[v1 ->]|H1].
    + iPureIntro. eapply wr_head_step.
      constructor. constructor.
    + iPureIntro. apply (wr_ctx (λ x, Let _ x _)); fin.
  - iRight.
    iDestruct "Ht" as "[H1 H2]".
    iDestruct ("IH" with "Hown Hheap H1") as %H1.
    destruct H1 as [[v1 ->]|H1].
    + simpl. rewrite val_typed_switch /=.
      iDestruct "H1" as %->.
      iPureIntro. eapply wr_head_step.
      constructor. constructor.
    + iPureIntro. apply (wr_ctx (λ x, LetUnit x _)); fin.
  - iRight.
    iDestruct "Ht" as (t1 t2 HH) "[H1 H2]".
    iDestruct ("IH" with "Hown Hheap H1") as %H1.
    destruct H1 as [[v1 ->]|H1].
    + simpl. rewrite val_typed_switch /=.
      iDestruct "H1" as (a b ->) "[H1 H3]".
      iPureIntro. eapply wr_head_step.
      constructor. constructor.
    + iPureIntro. apply (wr_ctx (λ x, LetProd _ _ x _)); fin.
  - iRight.
    iDestruct "Ht" as "[H H2]".
    iDestruct ("IH" with "Hown Hheap H") as %H.
    destruct H as [[v ->]|H].
    + simpl. rewrite val_typed_switch /=.
      iDestruct "H" as %[n ->].
      iPureIntro. destruct n; eapply wr_head_step; constructor.
      * apply If_step2.
      * constructor. lia.
    + iPureIntro. apply (wr_ctx (λ x, If x _ _)); fin.
  - iRight.
    iDestruct "Ht" as (r ->) "H".
    iDestruct ("IH" with "Hown Hheap H") as %H.
    destruct H as [[v ->]|H].
    + simpl. rewrite val_typed_switch /=.
      iDestruct "H" as (x e ->) "H".
      iPureIntro.
      pose proof (heap_fresh h) as [i H].
      eapply wr_head_step. eapply Fork_step; eauto.
    + iPureIntro. apply (wr_ctx (λ x, Fork x)); fin.
  - iRight.
    iDestruct "Ht" as (->) "H".
    iDestruct ("IH" with "Hown Hheap H") as %H.
    destruct H as [[v ->]|H].
    + simpl. rewrite val_typed_switch /=.
      iDestruct "H" as (c ->) "H".
      iDestruct (own_lookup with "[$Hown $H]") as %H.
      iDestruct (heap_typed_close_info with "Hheap") as %HH; first done.
      iPureIntro. eapply wr_head_step.
      eapply Close_step. done.
    + iPureIntro. apply (wr_ctx (λ x, Close x)); fin.
Qed.

Lemma progress (threads : list expr) (h : heap) e :
  e ∈ threads ->
  invariant h threads -∗
  ⌜ e = Val UnitV ∨ waiting_or_reducible e h ⌝.
Proof.
  iIntros ([i Hi]%elem_of_list_lookup).
  iDestruct 1 as (Σ) "(Hown & Hthreads & Hheap)".
  iDestruct (big_sepL_delete with "Hthreads") as "[Htyped _]"; first done.
  iDestruct (progress1 with "Hown Hheap Htyped") as %H.
  destruct H; eauto.
  destruct H. destruct e; simplify_eq. simpl.
  destruct x; simpl; eauto;
  repeat iDestruct "Htyped" as (?) "Htyped"; simplify_eq.
  iDestruct "Htyped" as "%". simplify_eq.
Qed.

Lemma safety (e0 : expr) (es : list expr) (h : heap) :
  typed ∅ e0 UnitT ->
  steps [e0] ∅ es h ->
  ∀ e, e ∈ es -> e = Val UnitV ∨ waiting_or_reducible e h.
Proof.
  intros Htypes Hsteps e' He'.
  apply simple_adequacy.
  iIntros "Hown".
  iApply progress; first done.
  iApply preservationN; first done.
  iApply invariant_init; eauto.
Qed.

Definition final (es : list expr) (h : heap) :=
  (∀ e, e ∈ es -> e = Val UnitV) ∧ h = ∅.
Definition can_step (es : list expr) (h : heap) :=
  ∃ es' h', step es h es' h'.
Definition stopped (es : list expr) (h : heap) :=
  ∀ e, e ∈ es -> waiting e h ∨ e = Val UnitV.
Definition deadlock (es : list expr) (h : heap) :=
  stopped es h ∧ ∃ e, e ∈ es ∧ waiting e h.

Instance val_unit_eq_decision e : Decision (e = Val UnitV).
Proof.
  destruct e; first (destruct v); first (left; done); right; intro; simplify_eq.
Qed.
Instance waiting_decision e h : Decision (waiting e h).
Proof.
Admitted.
Instance stopped_decision es h : Decision (stopped es h).
Proof.
  unfold stopped. eapply dec_forall_list.
Admitted.
Instance deadlock_decision es h : Decision (deadlock es h).
Proof. Admitted.


Lemma list_dec {A} (xs : list A) (P : A -> Prop) :
  (∀ x, Decision (P x)) ->
  (∀ x, x ∈ xs -> P x) ∨ (∃ x, x ∈ xs ∧ ¬ P x).
Proof.
  intros Hdec.
  assert (Decision (∃ x, x ∈ xs ∧ ¬ P x)) as [H|H]; eauto.
  { eapply dec_exists_list. naive_solver.
    intros x. specialize (Hdec x). intro.
    destruct Hdec.
    - right. intros []. done.
    - left. done. }
  left. intros x Hx.
  destruct (decide (P x)); eauto.
  exfalso. apply H. eauto.
Qed.

Lemma invariant_implies_stopped_or_can_step h es :
  invariant h es -∗
  ⌜ stopped es h ∨ can_step es h ⌝.
Proof.
  iIntros "Hinv".
  destruct (decide (stopped es h)) as [H|H]; eauto.
  unfold stopped in H.
  assert (∃ e, e∈es ∧ ¬ waiting e h ∧ e ≠ Val UnitV) as HH.
  { destruct (list_dec es (λ e, waiting e h ∨ e = Val UnitV));
    (solve_decision || naive_solver). }
  destruct HH as (e & Hes & Hw & Hv).
  iDestruct (progress with "Hinv") as %HH; eauto.
  destruct HH as [?|[?|HH]]; simplify_eq; eauto.
  iPureIntro. right.
  unfold reducible in HH.
  destruct HH as (e' & h' & ts & Hs).
  rewrite ->elem_of_list_lookup in Hes.
  destruct Hes as (i & Hi).
  unfold can_step.
  exists (<[ i := e' ]> es ++ ts), h'.
  econstructor; eauto.
Qed.

Lemma deadlock_and_leak_freedom (e0 : expr) (es : list expr) (h : heap) :
  typed ∅ e0 UnitT ->
  steps [e0] ∅ es h ->
  final es h ∨ can_step es h.
Proof.

Admitted.