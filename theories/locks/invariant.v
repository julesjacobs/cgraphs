From diris.locks Require Export rtypesystem.
From diris.locks Require Export definitions.

Definition Mlen (m : multiset labelO) : nat := length (multiset_car m).

Global Instance Mlen_Proper : Proper ((≡) ==> (≡)) Mlen.
Proof.
  intros ???.
  destruct x,y.
  rewrite /Mlen /=. destruct H as [x [H1 H2]].
  simpl in *.
  rewrite -H2 H1 //.
Qed.

Lemma Mlen_mult x y : Mlen (x ⋅ y) = Mlen x + Mlen y.
Proof.
  unfold Mlen. destruct x,y; simpl.
  rewrite app_length //.
Qed.

Lemma Mlen_unit : Mlen ε = 0.
Proof. done. Qed.

Lemma Mlen_singleton l : Mlen {[ l ]} = 1.
Proof. done. Qed.

  Lemma Mpermute1 (a b c : multiset labelO) :
  a ⋅ b ⋅ c ≡ c ⋅ a ⋅ b.
Proof.
  rewrite comm assoc //.
Qed.

Lemma Mpermute2 (a b c : multiset labelO) :
  a ⋅ b ⋅ c ≡ b ⋅ a ⋅ c.
Proof.
  rewrite comm. symmetry.
  rewrite comm. f_equiv. rewrite comm //.
Qed.

Lemma Mlen_zero_inv a :
  Mlen a = 0 -> a = ε.
Proof.
  destruct a; rewrite /Mlen /=;
  destruct multiset_car; rewrite //=.
Qed.

Lemma Mlen_nonzero_inv a :
  Mlen a ≠ 0 -> ∃ l a', a ≡ {[ l ]} ⋅ a'.
Proof.
  destruct a; rewrite /Mlen /=;
  destruct multiset_car; rewrite //=.
  intros _. exists o.
  exists (MultiSet multiset_car).
  done.
Qed.


Record lock_relM (refcnt : nat) (o : option val) (t : type) (x : multiset labelO) : Prop := {
  ls_owner : lockstate;
  x_closed : multiset labelO;
  x_opened : multiset labelO;
  lr_split : x ≡ {[ LockLabel (Owner,ls_owner) t ]} ⋅ x_closed ⋅ x_opened;
  lr_closed : ∀ l x_closed', x_closed ≡ {[ l ]} ⋅ x_closed' -> l = LockLabel (Client,Closed) t;
  lr_openedclosed : match o with
    | None => (ls_owner = Opened ∧ x_opened = ε) ∨
              (ls_owner = Closed ∧ x_opened ≡ {[ LockLabel (Client,Opened) t]})
    | Some _ => ls_owner = Closed ∧ x_opened = ε
  end;
  lr_refcount : Mlen x_closed + Mlen x_opened = refcnt;
}.

Global Instance lock_relM_Proper refcnt o t : Proper ((≡) ==> (≡)) (lock_relM refcnt o t).
Proof.
  intros ???.
  split; intros []; econstructor; eauto.
  - rewrite -H //.
  - rewrite H //.
Qed.

Lemma lock_relM_newlock v t :
  lock_relM 0 (Some v) t {[LockLabel (Owner, Closed) t]}.
Proof.
  eexists Closed ε ε; eauto.
  intros l x_closed' H.
  symmetry in H.
  eapply multiset_op_unit in H as [].
  eapply multiset_singleton_not_unit in H as [].
Qed.

Lemma multiset_unit_empty_mult l (a : multiset labelO) :
  ε ≡ {[ l ]} ⋅ a -> False.
Proof.
  intros H.
  symmetry in H.
  eapply multiset_empty_mult in H as []. subst.
  eapply multiset_empty_neq_singleton in H as [].
Qed.

Lemma lock_relM_same_type refcnt o t t' l x :
  lock_relM refcnt o t ({[LockLabel l t']} ⋅ x) -> t' = t.
Proof.
  intros [].
  eapply mset_xsplit in lr_split. simp.
  eapply multiset_singleton_mult in H3.
  eapply mset_xsplit in H5. simp.
  destruct H3; simp.
  - eapply multiset_unit_equiv_eq in H13. subst.
    symmetry in H12. eapply multiset_empty_mult in H12 as [].
    subst. rewrite left_id in H10.
    rewrite left_id in H11.
    rewrite H15 in H7. rewrite <-H10 in H14.
    destruct o.
    { destruct lr_openedclosed. subst.
      eapply multiset_unit_empty_mult in H7 as []. }
    destruct lr_openedclosed; simp.
    { eapply multiset_unit_empty_mult in H7 as []. }
    rewrite H6 in H7.
    symmetry in H7.
    eapply multiset_singleton_mult' in H7 as [].
    subst.
    inv H. done.
  - rewrite H15 left_id in H7.
    rewrite -H7 in H4.
    rewrite H13 in H12.
    clear H15 H1.
    clear H13 H.
    rewrite H14 in H4.
    clear H0 H14.
    setoid_rewrite H11 in lr_closed.
    clear H11 x_closed.
    clear H2 H7.
    clear H4 x.
    clear lr_openedclosed x_opened.
    eapply multiset_singleton_mult in H12 as []; simp.
    + setoid_rewrite H1 in lr_closed.
      assert (LockLabel l t' = LockLabel (Client, Closed) t).
      { eapply lr_closed. done. }
      simp.
    + rewrite H0 in H10. symmetry in H10.
      eapply multiset_singleton_mult' in H10. simp.
Qed.

Lemma lock_relM_drop refcnt o t x :
  lock_relM (S refcnt) o t ({[LockLabel (Client, Closed) t]} ⋅ x) ->
  lock_relM refcnt o t x.
Proof.
  intros [].
  eapply mset_xsplit in lr_split. simp.
  setoid_subst.
  rewrite H7 in lr_refcount.
  eapply multiset_singleton_mult in H3 as []; simp.
  - setoid_subst. rewrite left_id in H5.
    exfalso. destruct o; simp.
    + eauto using multiset_unit_empty_mult.
    + destruct lr_openedclosed; simp; eauto using multiset_unit_empty_mult.
      rewrite H7 in H3. eapply multiset_singleton_mult' in H3 as []; simp.
  - setoid_subst. rewrite left_id in H7. setoid_subst.
    rewrite left_id in lr_refcount.
    eapply mset_xsplit in H5. simp. setoid_subst.
    eapply multiset_singleton_mult in H6 as []; simp; setoid_subst.
    + rewrite left_id in H4. setoid_subst.
      eexists _ _ _; first done; eauto.
      intros. setoid_subst. eapply lr_closed. rewrite comm -assoc. done.
    + symmetry in H4. eapply multiset_singleton_mult' in H4. simp.
Qed.

(* Version that assumes wlog that l2 <= l3 for some order. *)
Lemma lock_relM_split' l l2 l3 refcnt o t x :
  ((l2.1 = Owner -> l3.1 = Owner) ∧
  (l2.1 = l3.1 -> l2.2 = Closed -> l3.2 = Closed)) ->
  lockcap_split l l2 l3 ->
  lock_relM refcnt o t ({[LockLabel l t]} ⋅ x) ->
  lock_relM (S refcnt) o t ({[LockLabel l3 t]} ⋅ {[LockLabel l2 t]} ⋅ x).
Proof.
  intros [HQ1 HQ2] Hsplit [].
  eapply mset_xsplit in lr_split; simp. setoid_subst.
  eapply multiset_singleton_mult in H3 as []; simp; setoid_subst.
  - rewrite left_id in H5. setoid_subst.
    destruct o.
    { simp. eapply multiset_unit_empty_mult in H7 as []. }
    destruct lr_openedclosed.
    { simp. eapply multiset_unit_empty_mult in H7 as []. }
    simp. setoid_subst.
    symmetry in H7.
    eapply multiset_singleton_mult' in H7. simp.
    rewrite right_id.
    inv Hsplit. simpl in *.
    destruct l2,l3.
    inv H; simp.
    inv H0; simp. { naive_solver. }
    eexists _ _ _.
    {
      assert ({[LockLabel (Client, Closed) t]} ⋅
              {[LockLabel (Client, Opened) t]} ⋅
              ({[LockLabel (Owner, Closed) t]} ⋅ x_closed)
              ≡
              {[LockLabel (Owner, Closed) t]} ⋅
              ({[LockLabel (Client, Closed) t]} ⋅ x_closed) ⋅
              {[LockLabel (Client, Opened) t]}); eauto.
      rewrite Mpermute1. f_equiv. rewrite -assoc. f_equiv. rewrite comm //.
    }
    + intros. eapply mset_xsplit in H. simp. setoid_subst.
      eapply multiset_singleton_mult in H5 as []; simp; setoid_subst.
      * rewrite left_id in H3. setoid_subst. eauto.
      * symmetry in H3. eapply multiset_singleton_mult' in H3. simp.
    + eauto.
    + rewrite Mlen_mult !Mlen_singleton. lia.
  - rewrite left_id in H7. setoid_subst.
    destruct l2,l3. simpl in *.
    eapply mset_xsplit in H5. simp.
    setoid_subst.
    eapply multiset_singleton_mult in H4 as []; simp; setoid_subst.
    + rewrite left_id in H6. setoid_subst.
      assert (LockLabel l t = LockLabel (Client, Closed) t) by eauto. simp.
      destruct Hsplit as [R1 R2]. simpl in *.
      inv R1. inv R2.
      eexists _ _ _.
      {
        assert ({[LockLabel (Client, Closed) t]} ⋅
                {[LockLabel (Client, Closed) t]} ⋅
                ({[LockLabel (Owner, ls_owner) t]} ⋅ H3 ⋅ x_opened)
                ≡
                {[LockLabel (Owner, ls_owner) t]} ⋅
                ({[LockLabel (Client, Closed) t]} ⋅ {[LockLabel (Client, Closed) t]} ⋅ H3) ⋅
                x_opened); eauto.
        rewrite Mpermute1. rewrite -!assoc. f_equiv.
        rewrite !assoc. rewrite Mpermute1. rewrite -!assoc.
        f_equiv. rewrite assoc Mpermute1 -assoc //.
      }
      ++ intros. eapply mset_xsplit in H. simp. setoid_subst.
         eapply multiset_singleton_mult in H6 as []; simp; setoid_subst.
         * rewrite left_id in H4. setoid_subst. eapply lr_closed.
           rewrite assoc Mpermute1 Mpermute1 -assoc //.
         * symmetry in H4. eapply multiset_xsplit_singleton in H4 as []; simp.
      ++ eauto.
      ++ rewrite !Mlen_mult !Mlen_singleton. unfold Mlen. lia.
    + symmetry in H6. eapply multiset_singleton_mult' in H6. simp.
      destruct Hsplit as [R1 R2]. simpl in *.
      inv R1; simp; last naive_solver.
      clear HQ1 HQ2.
      assert (ε ⋅ H3 = H3) as HH.
      { unfold op. unfold multiset_op_instance.
        simpl. destruct H3. done. }
      rewrite HH. rewrite HH in lr_closed.
      rewrite assoc.
      destruct l1.
      {
        inv R2.
        destruct o; simp. destruct lr_openedclosed; simp.
        rewrite Mlen_unit right_id.
        rewrite Mpermute2 -assoc. rewrite comm.
        eexists _ _ _; first done; eauto.
        rewrite Mlen_singleton. lia.
      }
      {
        assert (
          {[LockLabel (Owner, l3) t]} ⋅ {[LockLabel (Client, Closed) t]} ⋅ H3 ⋅ x_opened ≡
          {[LockLabel (Owner, l3) t]} ⋅ ({[LockLabel (Client, Closed) t]} ⋅ H3) ⋅ x_opened
        ) as -> by rewrite assoc //.
        eexists _ _ _; first done; eauto.
        - intros. eapply mset_xsplit in H. simp. clear HH. setoid_subst.
          eapply multiset_singleton_mult in H6 as []; simp; setoid_subst.
          + rewrite left_id in H4. setoid_subst. eauto.
          + symmetry in H4. eapply multiset_singleton_mult' in H4. simp.
        - destruct o; simp; inv R2; eauto.
      }
Qed.

Lemma lock_relM_split l l2 l3 refcnt o t x :
  lockcap_split l l2 l3 ->
  lock_relM refcnt o t ({[LockLabel l t]} ⋅ x) ->
  lock_relM (S refcnt) o t ({[LockLabel l3 t]} ⋅ {[LockLabel l2 t]} ⋅ x).
Proof.
  intros [H1 H2] H.
  destruct l,l2,l3. simpl in *.
  inv H1; inv H2;
  try solve [
    eapply lock_relM_split'; last done; simpl;
    [naive_solver | split; simpl; eauto using lockownership_split, lockstate_split]
  ]; rewrite Mpermute2;
  try solve [
    eapply lock_relM_split'; last done; simpl;
    [naive_solver | split; simpl; eauto using lockownership_split, lockstate_split]
  ].
Qed.

Lemma lock_relM_open_close refcnt v t lo x :
  lock_relM refcnt (Some v) t ({[LockLabel (lo, Closed) t]} ⋅ x) <->
  lock_relM refcnt None t ({[LockLabel (lo, Opened) t]} ⋅ x).
Proof.
  split; intros [].
  {
    simp.
    rewrite right_id in lr_split.
    rewrite Mlen_unit.
    eapply mset_xsplit in lr_split. simp. setoid_subst.
    eapply multiset_singleton_mult in H3 as []; simp; setoid_subst.
    - rewrite left_id in H5. setoid_subst.
      assert (LockLabel (lo, Closed) t = LockLabel (Client, Closed) t) by eauto. simp.
      assert (
        {[LockLabel (Client, Opened) t]} ⋅ ({[LockLabel (Owner, Closed) t]} ⋅ H2) ≡
        {[LockLabel (Owner, Closed) t]} ⋅ H2 ⋅ {[LockLabel (Client, Opened) t]}
      ) as ->.
      {
        rewrite assoc Mpermute1 Mpermute1 //.
      }
      econstructor; first done; eauto.
      + intros. setoid_subst. eapply lr_closed.
        rewrite assoc Mpermute1 Mpermute1 -assoc. done.
      + rewrite Mlen_singleton. destruct H2; simpl.
        unfold Mlen. simpl. lia.
    - symmetry in H5. eapply multiset_singleton_mult' in H5. simp.
      assert ({[LockLabel (Owner, Opened) t]} ⋅ (ε ⋅ H2) ≡ {[LockLabel (Owner, Opened) t]} ⋅ H2 ⋅ ε) as ->.
      {
        rewrite left_id right_id comm //.
      }
      econstructor; first done; eauto.
  }
  {
    simp. eapply mset_xsplit in lr_split. simp; setoid_subst.
    eapply multiset_singleton_mult in H3 as []; simp; setoid_subst.
    - rewrite left_id in H5. setoid_subst.
      destruct lr_openedclosed; simp.
      symmetry in H7.
      eapply multiset_empty_mult in H7. simp.
      setoid_subst. symmetry in H7.
      eapply multiset_singleton_mult' in H7. simp.
      rewrite right_id.
      assert (
        {[LockLabel (Client, Closed) t]} ⋅ ({[LockLabel (Owner, Closed) t]} ⋅ x_closed) ≡
        {[LockLabel (Owner, Closed) t]} ⋅ ({[LockLabel (Client, Closed) t]} ⋅ x_closed) ⋅ ε
      ) as ->.
      {
        rewrite assoc. rewrite right_id.
        rewrite assoc.
        rewrite Mpermute1 Mpermute1.
        rewrite -!assoc. f_equiv.
        rewrite comm //.
      }
      econstructor; first done; eauto.
      + intros. eapply mset_xsplit in H. simp. setoid_subst.
        eapply multiset_singleton_mult in H5 as []; simp; setoid_subst.
        * rewrite left_id in H3. setoid_subst. eauto.
        * symmetry in H3. eapply multiset_singleton_mult' in H3. simp.
      + rewrite Mlen_mult !Mlen_singleton Mlen_unit. lia.
    - rewrite left_id in H7. setoid_subst.
      eapply mset_xsplit in H5. simp. setoid_subst.
      eapply multiset_singleton_mult in H6 as []; simp; setoid_subst.
      { assert (LockLabel (lo, Opened) t = LockLabel (Client, Closed) t) by eauto. simp. }
      symmetry in H4.
      eapply multiset_singleton_mult' in H4. simp.
      destruct lr_openedclosed; simp.
      rewrite Mlen_mult.
      rewrite left_id.
      rewrite assoc.
      rewrite Mlen_unit. simpl.
      econstructor; first done; eauto.
  }
Qed.

Lemma lock_relM_only_owner v t x :
  lock_relM 0 (Some v) t ({[LockLabel (Owner, Closed) t]} ⋅ x) -> x = ε.
Proof.
  intros [].
  destruct lr_openedclosed. subst.
  rewrite Mlen_unit in lr_refcount.
  assert (Mlen x_closed = 0) as ->%Mlen_zero_inv by lia.
  rewrite !right_id in lr_split.
  eapply multiset_singleton_mult' in lr_split as [].
  done.
Qed.

Lemma lock_relM_progress refcnt o t x :
  lock_relM refcnt o t x -> ∃ l x',
    x ≡ {[ LockLabel l t ]} ⋅ x' ∧
    l = match o with
    | None => (l.1,Opened)
    | Some _ =>
      match refcnt with
      | 0 => (Owner,Closed)
      | S _ => (Client,Closed)
      end
    end.
Proof.
  intros [].
  destruct o.
  - destruct lr_openedclosed. destruct refcnt; subst.
    + eexists _,_; split; last done.
      rewrite -assoc in lr_split. done.
    + exists (Client,Closed).
      rewrite Mlen_unit in lr_refcount.
      assert (Mlen x_closed ≠ 0) as H by lia.
      eapply Mlen_nonzero_inv in H.
      destruct H as [l [x_closed' Hxcl]].
      specialize (lr_closed _ _ Hxcl) as ->.
      rewrite Hxcl in lr_split.
      eexists ({[LockLabel (Owner, Closed) t]} ⋅ x_closed'). split; last done.
      rewrite lr_split.
      rewrite !assoc right_id Mpermute2 //.
  - destruct lr_openedclosed as [[]|[]]; subst.
    + exists (Owner,Opened), x_closed.
      split; last done.
      rewrite lr_split right_id //.
    + exists (Client,Opened),({[LockLabel (Owner, Closed) t]} ⋅ x_closed).
      split; last done.
      rewrite assoc. rewrite -Mpermute1 lr_split H0 //.
Qed.

Definition linv (ρ : cfg) (v : nat) (in_l : multiset labelO) : rProp :=
  match ρ !! v with
  | Some (Thread e) => ⌜⌜ in_l ≡ ε ⌝⌝ ∗ rtyped0 e UnitT
  | Some Barrier => ⌜⌜ ∃ t1 t2 : type,
      in_l ≡ {[ BarrierLabel false t1 t2 ]} ⋅
             {[ BarrierLabel false t2 t1 ]} ⌝⌝
  | Some (Lock refcnt o) => ∃ t,
      ⌜⌜ lock_relM refcnt o t in_l ⌝⌝ ∗
      match o with
      | Some v => vtyped v t
      | None => emp
      end
      (* Precisely one owner and k clients *)
      (* if o is Some then one Opened and rest Closed,
         if o is None then all Closed *)
  | None => ⌜⌜ in_l ≡ ε ⌝⌝
  end%I.

Global Instance lin_Proper ρ v : Proper ((≡) ==> (≡)) (linv ρ v).
Proof. solve_proper. Qed.

Definition ginv ρ := inv (linv ρ).

Lemma lookup_union_spec `{Countable K} {V} (m1 m2 : gmap K V) (x : K) :
  (m1 ∪ m2) !! x = from_option Some (m2 !! x) (m1 !! x).
Proof.
  rewrite lookup_union.
  destruct (m1 !! x),(m2 !! x); simpl; eauto.
Qed.

Ltac sdec := repeat (progress simp || case_decide || done || eauto).
Ltac smap := repeat (
  rewrite lookup_union_spec ||
  rewrite lookup_alter_spec ||
  rewrite lookup_insert_spec ||
  rewrite lookup_delete_spec ||
  rewrite lookup_empty || sdec).


Lemma preservation i ρ ρ' :
  step i ρ ρ' -> ginv ρ -> ginv ρ'.
Proof.
  intros H Hinv.
  destruct H as [ρ ρ' ρf D1 D2 i H].
  destruct H.
  - eapply inv_impl; last done.
    iIntros (n x) "H". unfold linv. smap.
    iDestruct "H" as "[? H]". iFrame.
    iDestruct (replacement with "H") as (t) "[H Q]"; first done.
    iApply "Q". iApply pure_preservation; done.
  - eapply inv_impl; last done.
    iIntros (n x) "H". unfold linv. smap; iDestr "H";
    assert (ρf !! n = None) as -> by solve_map_disjoint; eauto.
    destruct H. eauto.
  - eapply (inv_alloc_lr i0 n j);
    last done; first apply _; first apply _.
    + naive_solver.
    + iIntros (? ? ?) "H". unfold linv. smap.
    + iIntros (?) "H". unfold linv. smap.
      assert (ρf !! n = None) as -> by solve_map_disjoint; eauto.
    + iIntros (?) "H". unfold linv. smap.
      assert (ρf !! j = None) as -> by solve_map_disjoint; eauto.
    + iIntros (?) "H". unfold linv. smap. iDestr "H".
      iDestruct (replacement with "H") as (t) "[H Q]"; first done. simpl.
      iDestr "H". simp.
      iExists (BarrierLabel false t1 t2), (BarrierLabel false t2 t1).
      iSplitL "Q".
      * iIntros "H". iSplit; first done.
        iApply "Q". simpl. eauto.
      * iSplit; eauto.
        iIntros "Q". iSplit; eauto 10 with iFrame.
  - assert (inv (λ k x,
      if decide (k = i0) then
        ⌜⌜ x ≡ ε ⌝⌝ ∗ ∃ t1 t2, own_out n (BarrierLabel true t1 t2) ∗ ∀ e' : expr, rtyped0 e' t2 -∗ rtyped0 (k1 e') UnitT
      else if decide (k = n) then
        ∃ t1 t2, ⌜⌜ x ≡ {[ BarrierLabel true t1 t2 ]} ⋅ {[ BarrierLabel false t2 t1 ]} ⌝⌝ ∗
        vtyped v1 t1
      else if decide (k = j) then
        ⌜⌜ x ≡ ε ⌝⌝ ∗ rtyped0 (k2 (App (Val (BarrierV n)) (Val v2))) UnitT
      else linv ρf k x
        )%I) as Hinv'.
    {
      eapply (inv_exchange i0 n); last done; [solve_proper|solve_proper|..].
      - simp. smap; unfold linv; smap.
      - simp. smap. unfold linv. smap.
        iIntros "[% H]".
        rewrite replacement; last done.
        iDestruct "H" as (t1) "[H1 H2]". simpl.
        iDestruct "H1" as (t2 l) "[H1 H3]".
        iDestruct "H1" as (t1' t2' ?) "H1". simplify_eq.
        iExists _. iFrame. iIntros (x [t1 [t2 ?]]) "".
        eapply multiset_xsplit_singleton in H8 as [[]|[]]; simplify_eq.
        + iExists _. iSplitL "H2".
          * iIntros "H". iSplit; eauto. iExists _,_. iFrame.
          * iExists _,_. iFrame. setoid_subst. eauto.
        + iExists _. iSplitL "H2".
          * iIntros "H". iSplit; eauto. iExists _,_. iFrame.
          * iExists _,_. iFrame. setoid_subst. eauto.
    } clear Hinv.

    assert (inv (λ k x,
      if decide (k = i0) then
        ⌜⌜ x ≡ ε ⌝⌝ ∗ ∃ t1 t2, own_out n (BarrierLabel true t1 t2) ∗ ∀ e' : expr, rtyped0 e' t2 -∗ rtyped0 (k1 e') UnitT
      else if decide (k = n) then
        ∃ t1 t2, ⌜⌜ x ≡ {[ BarrierLabel true t1 t2 ]} ⌝⌝ ∗
        vtyped v2 t2
      else if decide (k = j) then
        ⌜⌜ x ≡ ε ⌝⌝ ∗ rtyped0 (k2 (Val v1)) UnitT
      else linv ρf k x
        )%I) as Hinv''.
    {
      eapply (inv_dealloc j n); last done; [solve_proper|solve_proper|..].
      - simp. smap.
      - simp. smap.
        iIntros "[% H]".
        rewrite replacement; last done.
        iDestruct "H" as (t1) "[H1 H2]". simpl.
        iDestruct "H1" as (t2 l) "[H3 H4]".
        iDestruct "H3" as (t1' t2' ?) "H". simplify_eq.
        iExists _. iFrame. iIntros (?) "H".
        iDestruct "H" as (t1 t2 ?) "H".
        eapply multiset_xsplit_singleton in H8 as [[]|[]]; simplify_eq.
        iSplitL "H H2".
        + iSplit; eauto. iApply "H2". done.
        + iExists _,_. iFrame. eauto.
    } clear Hinv'.

    eapply (inv_dealloc i0 n); last done; [solve_proper|solve_proper|..].
    + simp. smap; unfold linv; smap.
    + simp. smap.
      iIntros "[% H]".
      iDestruct "H" as (t1 t2) "[H1 H2]".
      iExists _. iFrame. iIntros (?) "H".
      iDestruct "H" as (t1' t2' ?) "H".
      eapply multiset_singleton_mult' in H6 as []. simplify_eq.
      unfold linv. smap.
      assert (ρf !! n = None) as -> by solve_map_disjoint.
      iSplit; eauto. iSplit; eauto.
      iApply "H2". simpl. done.
  - eapply (inv_alloc_l i0 n);
    last done; first apply _; first apply _.
    + done.
    + iIntros (? ? ?) "H". unfold linv. smap.
    + iIntros (?) "H". unfold linv. smap.
      assert (ρf !! n = None) as -> by solve_map_disjoint; eauto.
    + iIntros (?) "H". unfold linv. smap. iDestr "H".
      iDestruct (replacement with "H") as (t) "[H Q]"; first done. simpl.
      iDestr "H". simp.
      iExists (LockLabel (Owner,Closed) t').
      iSplitL "Q".
      * iIntros "H". iSplit; first done.
        iApply "Q". simpl. eauto.
      * iExists t'. iFrame. iPureIntro. eapply lock_relM_newlock.
  - eapply (inv_exchange_alloc i0 n j); last done; first apply _; first apply _.
    + done.
    + iIntros (? ? ?) "H". unfold linv. smap.
    + iIntros (?) "H". unfold linv. smap.
      assert (ρf !! j = None) as -> by solve_map_disjoint; eauto.
    + iIntros (?) "H". unfold linv. smap. iDestr "H".
      iDestruct (replacement with "H") as (t) "[H Q]"; first done. simpl.
      iDestr "H". simp. iDestruct "H" as "[H1 H2]". iDestr "H1". simp.
      iExists _. iFrame.
      iIntros (?) "H". iDestr "H".
      assert (t'0 = t) as -> by eauto using lock_relM_same_type.
      iExists (LockLabel l3 t),(LockLabel l2 t).
      iSplitL "Q".
      {
        iIntros "H". iSplit; first done. iApply "Q". simpl.
        iExists _,_. iSplit; done.
      }
      iSplitL "H".
      * iExists _. iFrame. iPureIntro.
        by eapply lock_relM_split.
      * iIntros "H". eauto 10 with iFrame.
  - eapply (inv_exchange i0 n);
    last done; first apply _; first apply _.
    + iIntros (? ? ?) "H". unfold linv. smap.
    + iIntros (?) "H". unfold linv. smap. iDestr "H".
      iDestruct (replacement with "H") as (t) "[H Q]"; first done. simpl.
      iDestr "H". simp.
      iExists _. iFrame. iIntros (x) "H". iDestr "H".
      assert (t'0 = t) as -> by eauto using lock_relM_same_type.
      iExists (LockLabel _ _).
      iSplitL "Q H".
      * iIntros "H'". iSplit; first done.
        iApply "Q". simpl. iExists _,_.
        iSplit; first done. iFrame. iExists _,_. eauto.
      * iExists t. iPureIntro. split; last done.
        by eapply lock_relM_open_close.
  - eapply (inv_exchange i0 n);
    last done; first apply _; first apply _.
    + iIntros (? ? ?) "H". unfold linv. smap.
    + iIntros (?) "H". unfold linv. smap. iDestr "H".
      iDestruct (replacement with "H") as (t) "[H Q]"; first done. simpl.
      iDestr "H". simp. iDestruct "H" as "[H1 H2]".
      iDestr "H1". simp.
      iExists _. iFrame. iIntros (x) "H". iDestr "H".
      assert (t'0 = t) as -> by eauto using lock_relM_same_type.
      iExists (LockLabel _ _).
      iSplitL "Q H".
      * iIntros "H'". iSplit; first done.
        iApply "Q". simpl. iExists _,_.
        iSplit; first done. iFrame.
      * iExists t. iFrame. iPureIntro.
        by eapply lock_relM_open_close.
  - eapply (inv_dealloc i0 n);
    last done; first apply _; first apply _.
    + iIntros (? ? ?) "H". unfold linv. smap.
    + iIntros (?) "H". unfold linv. smap. iDestr "H".
      iDestruct (replacement with "H") as (t) "[H Q]"; first done. simpl.
      iDestr "H". simp.
      iExists _. iFrame. iIntros (x) "H". iDestr "H".
      assert (t' = t) as -> by eauto using lock_relM_same_type.
      assert (ρf !! n = None) as -> by solve_map_disjoint.
      iSplit; first iSplit; first done.
      * iApply "Q". done.
      * iPureIntro. eapply multiset_unit_equiv_eq.
        by eapply lock_relM_only_owner.
  - eapply (inv_dealloc i0 n);
    last done; first apply _; first apply _.
    + iIntros (? ? ?) "H". unfold linv. smap.
    + iIntros (?) "H". unfold linv. smap. iDestr "H".
      iDestruct (replacement with "H") as (t) "[H Q]"; first done. simpl.
      iDestr "H". simp.
      iExists _. iFrame. iIntros (x) "H". iDestr "H".
      assert (t'0 = t) as -> by eauto using lock_relM_same_type.
      iSplitL "Q".
      * iSplit; first done. iApply "Q". done.
      * iExists _. iSplit; last done.
        iPureIntro. by eapply lock_relM_drop.
Qed.


Lemma cfg_fresh1 (ρ : cfg) :
  ∃ j, ρ !! j = None.
Proof.
  exists (fresh (dom ρ)).
  apply not_elem_of_dom.
  apply is_fresh.
Qed.

Lemma fresh2 (s : gset nat) :
  ∃ x y, x ∉ s ∧ y ∉ s ∧ x ≠ y.
Proof.
  exists (fresh s), (fresh (s ∪ {[ fresh s ]})).
  split; first apply is_fresh.
  pose proof (is_fresh (s ∪ {[ fresh s ]})).
  set_solver.
Qed.

Lemma cfg_fresh2 (ρ : cfg) :
  ∃ j1 j2, ρ !! j1 = None ∧ ρ !! j2 = None ∧ j1 ≠ j2.
Proof.
  destruct (fresh2 (dom ρ)) as (j1 & j2 & H1 & H2 & H3).
  exists j1,j2. split_and!; last done;
  apply not_elem_of_dom; done.
Qed.

Lemma linv_out_Some i j Σ l ρ x :
  holds (linv ρ j x) Σ ->
  Σ !! i ≡ Some l ->
  ∃ e, ρ !! j = Some e ∧ e ≠ Barrier.
Proof.
  unfold linv.
  destruct (ρ !! j) as [[]|]; eauto;
  rewrite affinely_pure_holds;
  intros [H ?] Q; specialize (H i);
  rewrite H lookup_empty in Q; simplify_eq.
Qed.

Definition own_dom A : rProp := ∃ Σ, ⌜⌜ A = dom Σ ⌝⌝ ∗ own Σ.

Lemma own_dom_empty : own_dom ∅ ⊣⊢ emp.
Proof.
  iSplit; unfold own_dom; iIntros "H".
  - iDestruct "H" as (? H) "H".
    symmetry in H. apply dom_empty_iff_L in H as ->.
    by iApply own_empty.
  - iExists ∅. rewrite own_empty dom_empty_L //.
Qed.

Lemma own_dom_singleton k v : own {[ k := v ]} ⊢ own_dom {[ k ]}.
Proof.
  iIntros "H". iExists {[ k := v ]}.
  rewrite dom_singleton_L. iFrame. done.
Qed.

Lemma own_dom_union A B : own_dom A ∗ own_dom B ⊢ own_dom (A ∪ B).
Proof.
  iIntros "[H1 H2]".
  iDestruct "H1" as (Σ1 H1) "H1".
  iDestruct "H2" as (Σ2 H2) "H2". subst.
  iExists (Σ1 ∪ Σ2). rewrite dom_union_L. iSplit; eauto.
  iApply own_union. iFrame.
Qed.

Lemma own_dom_fin_gset `{Countable A} n (g : fin n -> A) (f : A -> gset vertex) :
  ([∗ set] p ∈ fin_gset n g, own_dom (f p)) -∗ own_dom (big_union (fin_gset n (f ∘ g))).
Proof.
  induction n.
  - rewrite !fin_gset_0 big_union_empty big_sepS_empty own_dom_empty //.
  - rewrite !fin_gset_S big_union_singleton_union.
    destruct (decide (g 0%fin ∈ fin_gset n (λ i : fin n, g (FS i)))).
    + rewrite subseteq_union_1_L; last rewrite singleton_subseteq_l //.
      rewrite subseteq_union_1_L; first apply IHn.
      eapply elem_of_fin_gset in e.
      intros ??.
      eapply elem_of_big_union.
      destruct e. simpl in *.
      rewrite -H1 in H0.
      eexists. split; last done.
      eapply elem_of_fin_gset. eauto.
    + rewrite big_sepS_insert //.
      iIntros "[H1 H2]".
      iDestruct (IHn with "H2") as "H2".
      iApply own_dom_union. iFrame.
Qed.

Lemma own_dom_fin_union n f :
  ([∗ set] p ∈ all_fin n, own_dom (f p)) ⊢ own_dom (fin_union n f).
Proof.
  iApply own_dom_fin_gset.
Qed.

Lemma own_dom_all {A} (f : A -> gset vertex) :
  (∀ i, own_dom (f i)) ⊢ ⌜ ∀ i j, f i = f j ⌝.
Proof.
  apply entails_holds.
  intros Σ H.
  rewrite pure_holds. intros.
  rewrite ->forall_holds in H.
  assert (∀ i, f i = dom Σ).
  { intros k. specialize (H k).
    eapply exists_holds in H as [].
    eapply pure_sep_holds in H as [].
    eapply own_holds in H0.
    rewrite -H0 H //. }
  rewrite !H0 //.
Qed.

Lemma own_dom_and A B :
  own_dom A ∧ own_dom B ⊢ ⌜ A = B ⌝.
Proof.
  iIntros "H".
  iAssert (∀ c:bool, own_dom (if c then A else B))%I with "[H]" as "H".
  { iIntros ([]).
    - by iDestruct "H" as "[H _]".
    - by iDestruct "H" as "[_ H]". }
  iDestruct (own_dom_all with "H") as %Q.
  specialize (Q true false). simpl in *. eauto.
Qed.

Lemma fin_union_same `{Countable A} n (s : gset A) :
  fin_union (S n) (λ i, s) = s.
Proof.
  induction n.
  - rewrite fin_union_S fin_union_0 right_id_L //.
  - rewrite fin_union_S IHn union_idemp_L //.
Qed.

Lemma rtyped_refs Γ e t :
  rtyped Γ e t ⊢ own_dom (expr_refs e)
with val_typed_refs v t :
  vtyped v t ⊢ own_dom (val_refs v).
Proof.
  - iIntros "H". destruct e; simpl; repeat (iDestruct "H" as (?) "H"); try destruct l;
    rewrite ?val_typed_refs ?rtyped_refs ?own_dom_empty ?own_dom_union; eauto.
    iDestruct "H" as "[H1 H]". iApply own_dom_union; iFrame.
    case_decide; subst. { rewrite fin_union_0 own_dom_empty //. }
    setoid_rewrite rtyped_refs.
    iDestruct (own_dom_all with "H") as %Q.
    destruct n; simplify_eq.
    assert (expr_refs ∘ e0 = λ i, expr_refs (e0 0%fin)) as ->.
    { apply functional_extensionality. intros. eapply Q. }
    rewrite fin_union_same. iApply "H".
  - iIntros "H". destruct v; simpl; rewrite ?own_dom_empty; eauto;
    repeat (iDestruct "H" as (?) "H"); try destruct l;
    rewrite ?val_typed_refs ?rtyped_refs ?own_dom_union; eauto;
    by iApply own_dom_singleton.
Qed.

Lemma expr_refs_linv ρ j e x Σ :
  ρ !! j = Some (Thread e) ->
  holds (linv ρ j x) Σ ->
  expr_refs e = dom Σ.
Proof.
  intros H1 H2.
  unfold linv in *.
  rewrite H1 in H2.
  eapply pure_sep_holds in H2 as [_ H2].
  rewrite -rtyped_rtyped0 in H2.
  eapply holds_entails in H2; last eapply rtyped_refs.
  unfold own_dom in *.
  eapply exists_holds in H2 as [Σ' H2].
  eapply pure_sep_holds in H2 as [-> H2].
  eapply own_holds in H2. rewrite H2 //.
Qed.

Lemma own_dom_same A B :
  holds (own_dom A) B -> A = dom B.
Proof.
  intros H.
  unfold own_dom in *.
  eapply exists_holds in H as [Σ H].
  eapply pure_sep_holds in H as [-> H].
  eapply own_holds in H.
  rewrite H. done.
Qed.

Lemma obj_refs_linv ρ i x Δ Σ :
  ρ !! i = Some x ->
  holds (linv ρ i Δ) Σ -> obj_refs x = dom Σ.
Proof.
  intros Hi Hinv.
  unfold obj_refs.
  unfold linv in *.
  rewrite Hi in Hinv. clear Hi.
  destruct x.
  - eapply pure_sep_holds in Hinv as [_ Hinv].
    rewrite -rtyped_rtyped0 in Hinv.
    eapply holds_entails in Hinv; last apply rtyped_refs.
    eapply own_dom_same in Hinv. done.
  - eapply affinely_pure_holds in Hinv as [t1 H].
    simp. rewrite dom_empty_L //.
  - eapply exists_holds in Hinv as [t H].
    eapply pure_sep_holds in H as [_ H].
    destruct o.
    + eapply holds_entails in H; last apply val_typed_refs.
      eapply own_dom_same in H. done.
    + eapply emp_holds in H. simp.
      rewrite dom_empty_L //.
Qed.

Definition blocked (ρ : cfg) i j :=
  ∃ e, ρ !! i = Some (Thread e) ∧ expr_waiting e j.

Lemma out_edge_active Σ v v' a ρ x :
  Σ !! v' ≡ Some a ->
  holds (linv ρ v x) Σ ->
  inactive ρ v -> False.
Proof.
  intros Hedge Hinv Hina.
  unfold inactive in *.
  unfold linv in *.
  rewrite Hina in Hinv.
  eapply affinely_pure_holds in Hinv as [].
  rewrite H in Hedge. simp.
Qed.

Lemma rewrite_with_del `{Countable K} {V} (ρ : gmap K V) (i : K) (x : V) :
  ρ !! i = Some x ->
  ρ = {[ i := x ]} ∪ delete i ρ.
Proof.
  intros. apply map_eq. smap.
Qed.

Lemma label_unique `{Countable K} {V : ofe} (Σ : gmap K V) j l1 :
  Σ !! j ≡ Some l1 ->
  holds (∃ l2, own_out j l2 ∗ ⌜ l1 ≢ l2 ⌝) Σ ->
  False.
Proof.
  intros H1 H2.
  eapply exists_holds in H2 as [l2 H2].
  eapply sep_holds in H2 as (Σ1 & Σ2 & HΣ & Hdisj & Q1 & Q2).
  unfold own_out in Q1. eapply own_holds in Q1.
  rewrite pure_holds in Q2.
  eapply Q2. rewrite -Q1 in HΣ.
  rewrite HΣ in H1. revert H1. smap. inv H1. done.
Qed.

Lemma label_unique' `{Countable K} {V : ofe} (Σ : gmap K V) j l1 (φ : Prop) :
  Σ !! j ≡ Some l1 ->
  holds (∃ l2, own_out j l2 ∗ ⌜ l1 ≡ l2 -> φ ⌝) Σ ->
  φ.
Proof.
  intros H1 H2.
  eapply exists_holds in H2 as [l2 H2].
  eapply sep_holds in H2 as (Σ1 & Σ2 & HΣ & Hdisj & Q1 & Q2).
  unfold own_out in Q1. eapply own_holds in Q1.
  rewrite pure_holds in Q2.
  eapply Q2. rewrite -Q1 in HΣ.
  rewrite HΣ in H1. revert H1. smap. inv H1. done.
Qed.

Lemma full_reachability ρ :
  ginv ρ -> fully_reachable ρ.
Proof.
  intros Hinv.
  destruct Hinv as [g [Hwf Hinv]].
  unfold fully_reachable.
  eapply (cgraph_ind' (λ a b l, blocked ρ a b)); eauto; first solve_proper.
  intros i IH1 IH2.
  classical_right.
  rewrite /inactive in H.
  pose proof (Hinv i) as Q.
  unfold linv in Q.
  destruct (ρ !! i) eqn:E; simplify_eq. clear H.
  destruct o.
  - apply pure_sep_holds in Q as [Q1 Q2]. assert (Q2' := Q2).
    eapply holds_entails in Q2; last apply pure_progress.
    assert (ρ = {[ i := Thread e ]} ∪ delete i ρ) as HH.
    { apply map_eq. intro. smap. } rewrite HH.
    apply pure_holds in Q2 as [[v ->]|Q].
    + constructor. exists (∅ ∪ delete i ρ).
      assert (v = UnitV) as ->.
      { eapply pure_holds. eapply holds_entails; first done.
        iIntros "H". destruct v; eauto; iDestr "H"; simp. }
      econstructor; last constructor; last solve_map_disjoint.
      intro x. smap. destruct (_!!x); done.
    + destruct Q as (k & e0 & Hk & -> & [[e0' Hpstep]|Himpure]).
      * constructor. eexists ({[ i := Thread (k e0') ]} ∪ delete i ρ).
        constructor; [intro j; smap; by destruct (_!!j)..|].
        constructor; eauto.
      * destruct Himpure.
        -- destruct (cfg_fresh2 ρ) as (j & n & Hj & Hn & Hjn).
           constructor. eexists.
           constructor; last eapply Fork_step; last done; last apply Hjn;
           try intros ->; simplify_eq;
           intro x; smap; by destruct (_!!x).
        -- destruct (cfg_fresh1 ρ) as (j & Hj).
           constructor. eexists.
           assert (i ≠ j). { intros ->. smap. }
           constructor; last eapply NewLock_step; try done;
           intro x; smap; destruct (_!!x); try done.
        -- rewrite -HH.
           assert (∃ l, out_edges g i !! i0 ≡ Some l) as [l Hl].
           {
             assert (holds ((∃ l, own_out i0 l) ∗ True) (out_edges g i)) as QQ.
             {
               eapply holds_entails; first exact Q2'.
               iIntros "H".
               rewrite replacement; last done.
               iDestruct "H" as (t) "[H1 H2]".
               simpl.
               destruct H; simpl; iDestr "H1";
               try iDestruct "H1" as "[H1 H12]";
               try iDestr "H1"; iSplitL "H1"; eauto with iFrame.
             }
             eapply sep_holds in QQ as (Σ1 & Σ2 & H12 & Hdisj & Hout & HP).
             eapply exists_holds in Hout as [l Hout].
             unfold own_out in Hout.
             eapply own_holds in Hout.
             exists l. rewrite H12.
             rewrite -Hout.
             smap.
           }
           assert (is_Some (ρ !! i0)) as [x F].
           {
             eapply out_edges_in_labels in Hl as [x Hx].
             specialize (Hinv i0).
             rewrite Hx in Hinv.
             eapply pure_holds.
             eapply holds_entails; first exact Hinv.
             iIntros "H".
             unfold linv.
             destruct (ρ !! i0) as [[]|]; eauto.
             iDestruct "H" as %HEF.
             eapply multiset_empty_mult in HEF as [HEF HEF'].
             exfalso. eapply multiset_empty_neq_singleton. done.
           }
           assert (blocked ρ i i0). {
             unfold blocked. rewrite E.
             eexists. split; first done.
             unfold expr_waiting; eauto.
           }
           assert (reachable ρ i0). {
             edestruct (IH1 i0); eauto.
             unfold inactive in *. simplify_eq.
           }
           eapply Waiting_reachable; last done.
           unfold waiting.
           left. rewrite E.
           eexists. split; first done.
           unfold expr_waiting. eauto.
  - clear IH1.
    eapply affinely_pure_holds in Q as [Q1 [t1 [t2 Q2]]].
    (* Need to check whether both threads are trying to sync. *)
    (* If so, then can_step *)
    (* Otherwise, use IH *)
    apply in_labels_out_edges2 in Q2 as (j1 & j2 & Hj12 & Hj1 & Hj2).

    edestruct (linv_out_Some i j1) as [e1 [He1 He1']]; eauto.
    edestruct (linv_out_Some i j2) as [e2 [He2 He2']]; eauto.

    destruct (classic (blocked ρ j1 i)) as [HB1|HB1]; last first.
    {
      destruct (IH2 _ _ Hj1 HB1) as [H|H].
      - exfalso. eauto using out_edge_active.
      - eapply Waiting_reachable; last done.
        unfold waiting.
        unfold blocked in HB1.
        right. eexists. split; first done.
        split.
        + erewrite obj_refs_linv; last eauto; last eauto.
          eapply elem_of_dom. inv Hj1; eauto.
        + intros ???. eapply HB1. subst; eauto.
    }

    destruct (classic (blocked ρ j2 i)) as [HB2|HB2]; last first.
    {
      destruct (IH2 _ _ Hj2 HB2) as [H|H].
      - exfalso. eauto using out_edge_active.
      - eapply Waiting_reachable; last done.
        unfold waiting.
        unfold blocked in HB2.
        right. eexists. split; first done.
        split.
        + erewrite obj_refs_linv; last eauto; last eauto.
          eapply elem_of_dom. inv Hj1; eauto.
        + intros ???. eapply HB2. subst; eauto.
    }

    eapply Can_step_reachable.
    destruct HB1 as (e1' & Hρ1 & Hw1).
    destruct HB2 as (e2' & Hρ2 & Hw2).
    clear He1 He1' He2 He2' e1 e2.
    destruct Hw1 as (k1 & ee1' & Hk1 & -> & Hw1).
    destruct Hw2 as (k2 & ee2' & Hk2 & -> & Hw2).

    pose proof (Hinv j1) as Hinvj1.
    unfold linv in Hinvj1.
    rewrite Hρ1 in Hinvj1.
    eapply pure_sep_holds in Hinvj1 as [_ Htyped1].

    destruct Hw1; try solve [
      exfalso;
      eapply label_unique; first exact Hj1;
      eapply holds_entails; eauto;
      iIntros "H"; rewrite replacement; last done;
      iDestr "H"; iDestruct "H" as "[H1 H2]";
      simpl; iDestr "H1"; eauto with iFrame;
      iDestruct "H1" as "[Q1 Q2]";
      iDestr "Q1"; eauto with iFrame
    ].
    clear Htyped1.

    pose proof (Hinv j2) as Hinvj2.
    unfold linv in Hinvj2.
    rewrite Hρ2 in Hinvj2.
    eapply pure_sep_holds in Hinvj2 as [_ Htyped2].

    destruct Hw2; try solve [
      exfalso;
      eapply label_unique; first exact Hj2;
      eapply holds_entails; eauto;
      iIntros "H"; rewrite replacement; last done;
      iDestr "H"; iDestruct "H" as "[H1 H2]";
      simpl; iDestr "H1"; eauto with iFrame;
      iDestruct "H1" as "[Q1 Q2]";
      iDestr "Q1"; eauto with iFrame
    ].

    assert (ρ = {[
      j1 := Thread (k1 (App (Val (BarrierV j)) (Val v)));
      j2 := Thread (k2 (App (Val (BarrierV j)) (Val v0)));
      j := Barrier ]} ∪ (delete j1 $ delete j2 $ delete j ρ)).
    { apply map_eq. intro. smap. }
    rewrite H.
    econstructor. econstructor; last econstructor; eauto;
    try intros ->; smap; intro; smap; destruct (ρ !! i) eqn:EE; rewrite EE; smap.
  - eapply exists_holds in Q as [t Q].
    eapply pure_sep_holds in Q as [Hrel Q].
    eapply lock_relM_progress in Hrel as (lc & x' & Hinl & Hlc).
    eapply in_labels_out_edges in Hinl as  [j Hj].
    destruct (classic (blocked ρ j i)) as [HB|HB]; last first.
    {
      destruct (IH2 _ _ Hj HB) as [H|H].
      - exfalso. eauto using out_edge_active.
      - eapply Waiting_reachable; last done.
        unfold waiting.
        unfold blocked in HB.
        right.
        edestruct (linv_out_Some i j) as [e1 [He1 He1']]; eauto.
        eexists. split; first done.
        split.
        + erewrite obj_refs_linv; last eauto; last eauto.
          eapply elem_of_dom. inv Hj; eauto.
        + intros ???. eapply HB. subst; eauto.
    }
    eapply Can_step_reachable.
    destruct HB as (e & Hρ & Hw).
    clear x'. destruct lc as [lo ls]. simpl in *.
    destruct Hw as (k & e' & Hk & -> & Hw).

    pose proof (Hinv j) as Hinvj.
    unfold linv in Hinvj.
    rewrite Hρ in Hinvj.
    eapply pure_sep_holds in Hinvj as [_ Htyped].

    destruct Hw.
    + exfalso. eapply label_unique; first exact Hj.
      eapply holds_entails; eauto.
      iIntros "H". rewrite replacement; last done.
      iDestr "H". iDestruct "H" as "[H1 H2]".
      simpl. iDestr "H1".
      iDestruct "H1" as "[Q1 Q2]".
      iDestr "Q1"; eauto with iFrame.
    + assert (ρ = {[
        j := Thread (k (ForkLock (Val (LockV j0)) (Val v)));
        j0 := Lock refcnt o
        ]} ∪ (delete j $ delete j0 ρ)) as Hcfg.
      { apply map_eq. intro. smap. }
      rewrite Hcfg.
      destruct (cfg_fresh1 ρ) as (i & Hi).
      assert (j ≠ i). { intro. smap. }
      assert (i ≠ j0). { intro. smap. }
      assert (j ≠ j0). { intro. smap. }
      do 2 econstructor; last econstructor; last done; last exact H0; eauto;
      intro; smap; destruct (ρ !! i0) eqn:EE; rewrite EE; eauto; smap.
    + assert (ls = Closed) as ->.
      {
        eapply label_unique'; first exact Hj.
        eapply holds_entails; eauto.
        iIntros "H".
        iDestruct (replacement with "H") as (t') "[H1 H2]"; first done.
        simpl. iDestr "H1". simp.
        iExists _. iFrame. iPureIntro.
        intros HQ. inv HQ. done.
      }
      destruct o; simp.
      assert (ρ = {[
        j := Thread (k (Acquire (Val (LockV j0))));
        j0 := Lock refcnt (Some v)
      ]} ∪ (delete j $ delete j0 ρ)) as Hcfg.
      { apply map_eq. intro. smap. }
      rewrite Hcfg.
      do 2 econstructor; last econstructor; eauto; intro; smap;
      destruct (ρ !! i) eqn:EE; rewrite EE; eauto.
    + assert (ls = Opened) as ->.
      {
        eapply label_unique'; first exact Hj.
        eapply holds_entails; eauto.
        iIntros "H".
        iDestruct (replacement with "H") as (t') "[H1 H2]"; first done.
        simpl. iDestr "H1". simp.
        iDestruct "H1" as "[Q1 Q2]". iDestr "Q1". simp.
        iExists _. iFrame. iPureIntro.
        intros HQ. inv HQ. done.
      }
      destruct o. { destruct refcnt; simp. }
      assert (ρ = {[
        j := Thread (k (Release (Val (LockV j0)) (Val v)));
        j0 := Lock refcnt None
      ]} ∪ (delete j $ delete j0 ρ)) as Hcfg.
      { apply map_eq. intro. smap. }
      rewrite Hcfg.
      do 2 econstructor; last econstructor; eauto; intro; smap;
      destruct (ρ !! i) eqn:EE; rewrite EE; eauto.
    + assert (lo = Owner ∧ ls = Closed) as [-> ->].
      {
        eapply label_unique'; first exact Hj.
        eapply holds_entails; eauto.
        iIntros "H".
        iDestruct (replacement with "H") as (t') "[H1 H2]"; first done.
        simpl. iDestr "H1". simp.
        iExists _. iFrame. iPureIntro.
        intros HQ. inv HQ. done.
      }
      destruct o; simp.
      destruct refcnt; simp.
      assert (ρ = {[
        j := Thread (k (Wait (Val (LockV j0))));
        j0 := Lock 0 (Some v)
      ]} ∪ (delete j $ delete j0 ρ)) as Hcfg.
      { apply map_eq. intro. smap. }
      rewrite Hcfg.
      do 2 econstructor; last econstructor; eauto; intro; smap;
      destruct (ρ !! i) eqn:EE; rewrite EE; eauto.
    + assert (lo = Client ∧ ls = Closed) as [-> ->].
      {
        eapply label_unique'; first exact Hj.
        eapply holds_entails; eauto.
        iIntros "H".
        iDestruct (replacement with "H") as (t') "[H1 H2]"; first done.
        simpl. iDestr "H1". simp.
        iExists _. iFrame. iPureIntro.
        intros HQ. inv HQ. done.
      }
      destruct o; simp.
      destruct refcnt; simp.
      assert (ρ = {[
        j := Thread (k (Drop (Val (LockV j0))));
        j0 := Lock (S refcnt) (Some v)
      ]} ∪ (delete j $ delete j0 ρ)) as Hcfg.
      { apply map_eq. intro. smap. }
      rewrite Hcfg.
      do 2 econstructor; last econstructor; eauto; intro; smap;
      destruct (ρ !! i) eqn:EE; rewrite EE; eauto.
Qed.

Lemma initialization e :
  typed ∅ e UnitT -> ginv {[ 0 := Thread e ]}.
Proof.
  intros H.
  unfold ginv, linv.
  eapply inv_impl; last eauto using inv_init.
  intros. simpl.
  iIntros "[% _]".
  smap. iSplit; eauto.
  rewrite -rtyped_rtyped0.
  iApply typed_rtyped. eauto.
Qed.