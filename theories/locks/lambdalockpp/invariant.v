From cgraphs.locks.lambdalockpp Require Export rtypesystem.
From cgraphs.locks.lambdalockpp Require Export definitions.

Definition Mlen {A:ofe} (m : multiset A) : nat := length (multiset_car m).

Global Instance Mlen_Proper {A} : Proper ((≡) ==> (≡)) (@Mlen A).
Proof.
  intros ???.
  destruct x,y.
  rewrite /Mlen /=. destruct H as [x [H1 H2]].
  simpl in *.
  rewrite -H2 H1 //.
Qed.

Lemma Mlen_mult {A:ofe} (x y : multiset A) : Mlen (x ⋅ y) = Mlen x + Mlen y.
Proof.
  unfold Mlen. destruct x,y; simpl.
  rewrite app_length //.
Qed.

Lemma Mlen_unit {A:ofe} : Mlen (ε : multiset A) = 0.
Proof. done. Qed.

Lemma Mlen_singleton {A : ofe} (l : A) : Mlen {[ l ]} = 1.
Proof. done. Qed.

Lemma Mpermute1 {A:ofe} (a b c : multiset A) :
  a ⋅ b ⋅ c ≡ c ⋅ a ⋅ b.
Proof.
  rewrite comm assoc //.
Qed.

Lemma Mpermute2 {A:ofe} (a b c : multiset A) :
  a ⋅ b ⋅ c ≡ b ⋅ a ⋅ c.
Proof.
  rewrite comm. symmetry.
  rewrite comm. f_equiv. rewrite comm //.
Qed.

Lemma Mlen_zero_inv {A:ofe} (a : multiset A) :
  Mlen a = 0 -> a = ε.
Proof.
  destruct a; rewrite /Mlen /=;
  destruct multiset_car; rewrite //=.
Qed.

Lemma Mlen_nonzero_inv {A:ofe} (a : multiset A) :
  Mlen a ≠ 0 -> ∃ l a', a ≡ {[ l ]} ⋅ a'.
Proof.
  destruct a; rewrite /Mlen /=;
  destruct multiset_car; rewrite //=.
  intros _. exists o.
  exists (MultiSet multiset_car).
  done.
Qed.

Definition labelO':ofe := leibnizO (lockcap*type).

Record lockrel (refcnt : nat) (o : option val) (t : type) (x : multiset labelO') : Prop := {
  ls_owner : lockstate;
  x_closed : multiset labelO';
  x_opened : multiset labelO';
  lr_split : x ≡ {[ ((Owner,ls_owner),t):labelO' ]} ⋅ x_closed ⋅ x_opened;
  lr_closed : ∀ l x_closed', x_closed ≡ {[ l ]} ⋅ x_closed' -> l = ((Client,Closed,t):labelO');
  lr_openedclosed : match o with
    | None => (ls_owner = Opened ∧ x_opened = ε) ∨
              (ls_owner = Closed ∧ x_opened ≡ {[ (Client,Opened,t):labelO' ]})
    | Some _ => ls_owner = Closed ∧ x_opened = ε
  end;
  lr_refcount : Mlen x_closed + Mlen x_opened = refcnt;
}.

Global Instance lockrel_Proper refcnt o t : Proper ((≡) ==> (≡)) (lockrel refcnt o t).
Proof.
  intros ???.
  split; intros []; econstructor; eauto.
  - rewrite -H //.
  - rewrite H //.
Qed.

Definition extract1 (jj : nat) (ls : list (nat * (lockcap * type))) : multiset labelO' :=
  list_to_multiset ((filter (λ '(jj',c), jj = jj') ls).*2).

Definition extract (i : nat) (x : multiset labelO) : multiset labelO' :=
  list_to_multiset (flat_map (λ l,
    match l with LockLabel xs => multiset_car (extract1 i xs) | _ => [] end) (multiset_car x)).

Lemma flat_map_permute {A B} (f : A -> list B) xs ys :
  xs ≡ₚ ys -> flat_map f xs ≡ₚ flat_map f ys.
Proof.
  induction 1; simpl; eauto.
  - eapply Permutation_app; eauto.
  - rewrite !assoc_L. f_equiv.
    eapply Permutation_app_swap.
  - etrans; eauto.
Qed.

Global Instance extract_Proper i :
  Proper ((≡) ==> (≡)) (extract i).
Proof.
  intros ???. unfold extract. destruct x,y; simpl.
  eapply list_to_multiset_proper.
  eapply flat_map_permute.
  inversion H. simpl in *. simp.
Qed.

Definition mset_in {A:ofe} (a : A) (x : multiset A) := ∃ x', x ≡ {[ a ]} ⋅ x'.

Definition mset_forall {A:ofe} (P : A -> Prop) (x : multiset A) :=
  ∀ a x', x ≡ {[ a ]} ⋅ x' -> P a.

Lemma mset_forall_op {A:ofe} (P : A -> Prop) (x1 x2 : multiset A) :
  mset_forall P (x1 ⋅ x2) <-> mset_forall P x1 ∧ mset_forall P x2.
Proof.
  split; intros H.
  - split.
    + intros ???. eapply H. rewrite H0. rewrite -assoc. done.
    + intros ???. eapply H. rewrite comm. rewrite H0. rewrite -assoc. done.
  - intros ???.
    eapply mset_xsplit in H0. simp.
    eapply multiset_singleton_mult in H7 as []; simp.
    + eapply H2. rewrite H6 H10 //.
    + eapply H1. rewrite H5 H8 //.
Qed.

Lemma mset_forall_singleton {A:ofe} `{@LeibnizEquiv A (ofe_equiv A)} (P : A -> Prop) (a : A) :
  mset_forall P {[ a ]} <-> P a.
Proof.
  split; intros H'.
  - eapply (H' a ε). rewrite right_id //.
  - intros ???. symmetry in H0. eapply multiset_singleton_mult' in H0 as []; simp.
Qed.

Record lockrelG' (order : list nat) (refcnt : nat) (xs : locksbundle) (ts : gmap nat type) (x : multiset labelO) : Prop := {
  order_NoDup : NoDup order;
  order_dom : list_to_set order = dom xs;
  order_subsequences : mset_forall (λ l, ∃ xs, l = LockLabel xs ∧ sublist (xs.*1) order) x;
  lr_lockrel : ∀ i, match xs !! i, ts !! i with
    | Some (refcounti, o), Some t => lockrel refcounti o t (extract i x)
    | None, None => True
    | _, _ => False
    end;
  lr_refcount : Mlen x = refcnt;
}.

Definition lockrelG refcnt xs ts x := ∃ order, lockrelG' order refcnt xs ts x.

Global Instance mset_forall_Proper {A:ofe} : Proper (((≡) ==> iff) ==> (≡) ==> (≡)) (@mset_forall A).
Proof.
  intros ??????.
  split.
  { intros ????. eapply H; eauto. eapply H1. rewrite H0. done. }
  { intros ????. eapply H; eauto. eapply H1. rewrite -H0. done. }
Qed.

Global Instance lockrelG_Proper refcnt xs :
  Proper ((≡) ==> (≡) ==> (≡)) (lockrelG refcnt xs).
Proof.
  intros ??????.
  split.
  {
    intros [order []]. ofe_subst. do 2 econstructor; first done; eauto;
    try rewrite -H0; eauto.
    intros. specialize (lr_lockrel0 i).
    destruct (xs!!i); eauto. destruct p. destruct (y!!i); eauto.
    eapply lockrel_Proper; last done. rewrite H0 //.
  }
  {
    intros [order []]. ofe_subst. do 2 econstructor; first done; eauto;
    try rewrite H0; eauto.
    intros. specialize (lr_lockrel0 i).
    destruct (xs!!i); eauto. destruct p. destruct (y!!i); eauto.
    eapply lockrel_Proper; last done. rewrite H0 //.
  }
Qed.

Lemma lockrel_newlock v t :
  lockrel 0 (Some v) t {[ (Owner, Closed, t) : labelO' ]}.
Proof.
  eexists Closed ε ε; eauto.
  intros l x_closed' H.
  symmetry in H.
  eapply multiset_op_unit in H as [].
  eapply multiset_singleton_not_unit in H as [].
Qed.

Lemma lockrel_newlock' t :
  lockrel 0 None t {[ (Owner, Opened, t) : labelO' ]}.
Proof.
  eexists Opened ε ε; eauto.
  intros l x_closed' H.
  symmetry in H.
  eapply multiset_op_unit in H as [].
  eapply multiset_singleton_not_unit in H as [].
Qed.

Lemma multiset_unit_empty_mult {A:ofe} l (a : multiset A) :
  ε ≡ {[ l ]} ⋅ a -> False.
Proof.
  intros H.
  symmetry in H.
  eapply multiset_empty_mult in H as []. subst.
  eapply multiset_empty_neq_singleton in H as [].
Qed.

Lemma lockrel_same_type refcnt o t t' l x :
  lockrel refcnt o t ({[ (l, t'):labelO' ]} ⋅ x) -> t' = t.
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
      assert ((l,t') = (Client, Closed,t)).
      { eapply lr_closed. done. }
      simp.
    + rewrite H0 in H10. symmetry in H10.
      eapply multiset_singleton_mult' in H10. simp.
Qed.

Lemma lockrel_drop refcnt o t x :
  lockrel (S refcnt) o t ({[ (Client, Closed, t):labelO' ]} ⋅ x) ->
  lockrel refcnt o t x.
Proof.
  intros [].
  eapply mset_xsplit in lr_split. simp.
  setoid_subst.
  rewrite H7 in lr_refcount0.
  eapply multiset_singleton_mult in H3 as []; simp.
  - setoid_subst. rewrite left_id in H5.
    exfalso. destruct o; simp.
    + eauto using multiset_unit_empty_mult.
    + destruct lr_openedclosed; simp; eauto using multiset_unit_empty_mult.
      rewrite H7 in H3. eapply multiset_singleton_mult' in H3 as []; simp.
  - setoid_subst. rewrite left_id in H7. setoid_subst.
    rewrite left_id in lr_refcount0.
    eapply mset_xsplit in H5. simp. setoid_subst.
    eapply multiset_singleton_mult in H6 as []; simp; setoid_subst.
    + rewrite left_id in H4. setoid_subst.
      eexists _ _ _; first done; eauto.
      intros. setoid_subst. eapply lr_closed. rewrite comm -assoc. done.
    + symmetry in H4. eapply multiset_singleton_mult' in H4. simp.
Qed.

(* Version that assumes wlog that l2 <= l3 for some order. *)
Lemma lockrel_split' l l2 l3 refcnt o t x :
  ((l2.1 = Owner -> l3.1 = Owner) ∧
  (l2.1 = l3.1 -> l2.2 = Closed -> l3.2 = Closed)) ->
  lockcap_split l l2 l3 ->
  lockrel refcnt o t ({[(l,t):labelO']} ⋅ x) ->
  lockrel (S refcnt) o t ({[(l3,t):labelO']} ⋅ {[(l2,t):labelO']} ⋅ x).
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
      assert ({[ (Client, Closed, t):labelO' ]} ⋅
              {[ (Client, Opened, t):labelO' ]} ⋅
              ({[ (Owner, Closed, t):labelO' ]} ⋅ x_closed)
              ≡
              {[ (Owner, Closed, t):labelO' ]} ⋅
              ({[ (Client, Closed, t):labelO' ]} ⋅ x_closed) ⋅
              {[ (Client, Opened, t):labelO' ]}); eauto.
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
      assert ((l, t) = (Client, Closed, t)) by eauto. simp.
      destruct Hsplit as [R1 R2]. simpl in *.
      inv R1. inv R2.
      eexists _ _ _.
      {
        assert ({[ (Client, Closed, t):labelO']} ⋅
                {[ (Client, Closed, t):labelO']} ⋅
                ({[ (Owner, ls_owner, t):labelO']} ⋅ H3 ⋅ x_opened)
                ≡
                {[ (Owner, ls_owner, t):labelO']} ⋅
                ({[ (Client, Closed, t):labelO']} ⋅ {[(Client, Closed, t):labelO']} ⋅ H3) ⋅
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
          {[ (Owner, l3, t):labelO']} ⋅ {[ (Client, Closed, t):labelO']} ⋅ H3 ⋅ x_opened ≡
          {[ (Owner, l3, t):labelO']} ⋅ ({[ (Client, Closed, t):labelO']} ⋅ H3) ⋅ x_opened
        ) as -> by rewrite assoc //.
        eexists _ _ _; first done; eauto.
        - intros. eapply mset_xsplit in H. simp. clear HH. setoid_subst.
          eapply multiset_singleton_mult in H6 as []; simp; setoid_subst.
          + rewrite left_id in H4. setoid_subst. eauto.
          + symmetry in H4. eapply multiset_singleton_mult' in H4. simp.
        - destruct o; simp; inv R2; eauto.
      }
Qed.

Lemma lockrel_split l l2 l3 refcnt o t x :
  lockcap_split l l2 l3 ->
  lockrel refcnt o t ({[ (l, t):labelO']} ⋅ x) ->
  lockrel (S refcnt) o t ({[ (l3, t):labelO']} ⋅ {[ (l2, t):labelO']} ⋅ x).
Proof.
  intros [H1 H2] H.
  destruct l,l2,l3. simpl in *.
  inv H1; inv H2;
  try solve [
    eapply lockrel_split'; last done; simpl;
    [naive_solver | split; simpl; eauto using lockownership_split, lockstate_split]
  ]; rewrite Mpermute2;
  try solve [
    eapply lockrel_split'; last done; simpl;
    [naive_solver | split; simpl; eauto using lockownership_split, lockstate_split]
  ].
Qed.

Lemma lockrel_open_close refcnt v t lo x :
  lockrel refcnt (Some v) t ({[ (lo, Closed, t):labelO']} ⋅ x) <->
  lockrel refcnt None t ({[ (lo, Opened, t):labelO']} ⋅ x).
Proof.
  split; intros [].
  {
    simp.
    rewrite right_id in lr_split.
    rewrite Mlen_unit.
    eapply mset_xsplit in lr_split. simp. setoid_subst.
    eapply multiset_singleton_mult in H3 as []; simp; setoid_subst.
    - rewrite left_id in H5. setoid_subst.
      assert ( (lo, Closed, t) =  (Client, Closed, t)) by eauto. simp.
      assert (
        {[ (Client, Opened, t):labelO']} ⋅ ({[ (Owner, Closed, t):labelO']} ⋅ H2) ≡
        {[ (Owner, Closed, t):labelO']} ⋅ H2 ⋅ {[ (Client, Opened, t):labelO']}
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
      assert ({[ (Owner, Opened, t):labelO']} ⋅ (ε ⋅ H2) ≡ {[ (Owner, Opened, t):labelO']} ⋅ H2 ⋅ ε) as ->.
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
        {[ (Client, Closed, t):labelO']} ⋅ ({[ (Owner, Closed, t):labelO']} ⋅ x_closed) ≡
        {[ (Owner, Closed, t):labelO']} ⋅ ({[ (Client, Closed, t):labelO']} ⋅ x_closed) ⋅ ε
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
      { assert ( (lo, Opened, t) = (Client, Closed, t)) by eauto. simp. }
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

Lemma lockrel_only_owner v t x :
  lockrel 0 (Some v) t ({[ (Owner, Closed, t):labelO']} ⋅ x) -> x = ε.
Proof.
  intros [].
  destruct lr_openedclosed. subst.
  rewrite Mlen_unit in lr_refcount0.
  assert (Mlen x_closed = 0) as ->%Mlen_zero_inv by lia.
  rewrite !right_id in lr_split.
  eapply multiset_singleton_mult' in lr_split as [].
  done.
Qed.

Lemma lockrel_progress refcnt o t x :
  lockrel refcnt o t x -> ∃ l x',
    x ≡ {[ (l, t):labelO' ]} ⋅ x' ∧
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
      rewrite Mlen_unit in lr_refcount0.
      assert (Mlen x_closed ≠ 0) as H by lia.
      eapply Mlen_nonzero_inv in H.
      destruct H as [l [x_closed' Hxcl]].
      specialize (lr_closed _ _ Hxcl) as ->.
      rewrite Hxcl in lr_split.
      eexists ({[ (Owner, Closed, t):labelO']} ⋅ x_closed'). split; last done.
      rewrite lr_split.
      rewrite !assoc right_id Mpermute2 //.
  - destruct lr_openedclosed as [[]|[]]; subst.
    + exists (Owner,Opened), x_closed.
      split; last done.
      rewrite lr_split right_id //.
    + exists (Client,Opened),({[ (Owner, Closed, t):labelO']} ⋅ x_closed).
      split; last done.
      rewrite assoc. rewrite -Mpermute1 lr_split H0 //.
Qed.


Definition linv (ρ : cfg) (v : nat) (in_l : multiset labelO) : rProp :=
  match ρ !! v with
  | Some (Thread e) => ⌜⌜ in_l ≡ ε ⌝⌝ ∗ rtyped0 e UnitT
  | Some Barrier => ⌜⌜ ∃ t1 t2 : type,
      in_l ≡ {[ BarrierLabel false t1 t2 ]} ⋅
             {[ BarrierLabel false t2 t1 ]} ⌝⌝
  | Some (LockG refcnt xs) => ∃ ts,
      ⌜⌜ lockrelG refcnt xs ts in_l ⌝⌝ ∗
      [∗ map] i↦x;t ∈ xs;ts,
        match x.2 with
        | Some v => vtyped v t
        | None => emp
        end
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

Lemma lockcaps_split_length xs1 xs2 xs3 :
  lockcaps_split xs1 xs2 xs3 -> length xs1 = length xs2 ∧ length xs1 = length xs3.
Proof.
  intros H. unfold lockcaps_split in *.
  eauto using Forall3_length_lr, Forall3_length_lm.
Qed.

Lemma extract_op jj x1 x2 :
  extract jj (x1 ⋅ x2) = extract jj x1 ⋅ extract jj x2.
Proof.
  unfold extract. unfold op. simpl.
  rewrite !flat_map_app; eauto.
Qed.

Lemma extract_singleton jj a :
  extract jj {[ a ]} = match a with
    | LockLabel xs => extract1 jj xs
    | _ => ε
    end.
Proof.
  unfold extract. simpl. destruct a; simpl; try done.
  rewrite right_id_L //.
Qed.

Lemma extract1_cons jj jj' p xs :
  extract1 jj ((jj',p)::xs) =
    if decide (jj = jj')
    then {[ p:labelO' ]} ⋅ extract1 jj xs
    else extract1 jj xs.
Proof.
  unfold extract1.
  rewrite !filter_cons.
  case_decide; simp; case_decide; simp.
Qed.

Lemma extract1_Some ii i l ls xs :
  ls !! ii = Some i ->
  xs !! ii = Some l ->
  extract1 i (zip ls xs) ≡ {[ l:labelO' ]} ⋅ extract1 i (zip (delete ii ls) (delete ii xs)).
Proof.
  revert ii xs.
  induction ls; simpl; first set_solver.
  intros. destruct xs; simp.
  destruct ii; simpl in *; simp.
  - unfold extract1 at 1.
    rewrite filter_cons. case_decide; simp.
  - rewrite !extract1_cons.
    case_decide; simp; eauto.
    rewrite IHls; eauto.
    rewrite comm.
    rewrite (comm _ {[ p:labelO' ]}).
    rewrite assoc //.
Qed.

Lemma extract_Some ii jj xs1 a b t2 ls :
  ls !! ii = Some jj ->
  xs1 !! ii = Some (a, b, t2) -> ∃ x',
  extract1 jj (zip ls xs1) ≡ {[ (a,b,t2):labelO' ]} ⋅ x'.
Proof.
  intros H1 H2.
  eexists.
  rewrite extract1_Some; eauto.
Qed.

Lemma lockrelG_types_same refcnt xs ts ls xs1 x ii jj a b t1 t2 :
  lockrelG refcnt xs ts ({[LockLabel (zip ls xs1)]} ⋅ x) ->
  ls !! ii = Some jj ->
  ts !! jj = Some t1 ->
  xs1 !! ii = Some (a, b, t2) ->
  t1 = t2.
Proof.
  intros [order []] ???.
  specialize (lr_lockrel0 jj). rewrite H0 in lr_lockrel0.
  destruct (xs !! jj); last done. destruct p.
  rewrite extract_op in lr_lockrel0.
  rewrite extract_singleton in lr_lockrel0.
  edestruct extract_Some; eauto.
  rewrite H2 in lr_lockrel0.
  rewrite -assoc in lr_lockrel0.
  eapply lockrel_same_type in lr_lockrel0.
  subst. done.
Qed.

Lemma extract1_ne_Some ii i ls xs :
  ls !! ii ≠ Some i ->
  extract1 i (zip ls xs) = extract1 i (zip (delete ii ls) (delete ii xs)).
Proof.
  revert ii xs.
  induction ls; simpl; first set_solver.
  intros. destruct xs; simp.
  destruct ii; simpl in *; simp.
  - destruct ls; done.
  - rewrite extract1_cons.
    destruct ii; simp; case_decide; simp;
    rewrite extract1_cons; case_decide; try done; eauto.
    f_equal. eauto.
Qed.

Lemma list_delete_insert_delete {A} i (a:A) (xs:list A) :
  delete i (<[ i := a ]> xs) = delete i xs.
Proof.
  revert i; induction xs; simpl; first done.
  intros []; simpl; first done.
  f_equal. done.
Qed.

Lemma lockrelG_Release ls ii jj xs refcntii xs1 a t' x refcnt ts v :
  length ls = length xs1 ->
  ls !! ii = Some jj ->
  xs !! jj = Some (refcntii, None) ->
  xs1 !! ii = Some (a, Opened, t') ->
  lockrelG refcnt xs ts ({[LockLabel (zip ls xs1)]} ⋅ x) ->
  lockrelG refcnt (<[jj:=(refcntii, Some v)]> xs) ts
    ({[LockLabel (zip ls (<[ii:=(a, Closed, t')]> xs1))]} ⋅ x).
Proof.
  intros ???? [order []].
  do 2 econstructor; eauto.
  - rewrite dom_insert_lookup_L //.
  - rewrite mset_forall_op. rewrite mset_forall_op in order_subsequences0.
    destruct order_subsequences0 as []. split; eauto.
    rewrite mset_forall_singleton. rewrite mset_forall_singleton in H3.
    simp. eexists. split; first done.
    rewrite fst_zip in H7; last lia.
    rewrite fst_zip; first done.
    rewrite insert_length. lia.
  - intro. specialize (lr_lockrel0 i). smap.
    + rewrite H1 in lr_lockrel0.
      destruct (ts !! i); eauto.
      revert lr_lockrel0.
      rewrite !extract_op !extract_singleton.
      erewrite extract1_Some; eauto.
      intros lr.
      erewrite extract1_Some; eauto; last first.
      { rewrite list_lookup_insert; first done. by eapply lookup_lt_Some. }
      rewrite list_delete_insert_delete.
      rewrite -assoc. rewrite -assoc in lr.
      assert (t'=t) as -> by eauto using lockrel_same_type.
      eapply lockrel_open_close. done.
    + destruct (xs !! i) eqn:E; rewrite E; last first.
      { destruct (ts !! i); done. }
      destruct p. destruct (ts !! i); eauto.
      revert lr_lockrel0.
      rewrite !extract_op !extract_singleton.
      assert (ls !! ii ≠ Some i). { congruence. }
      erewrite extract1_ne_Some; last done. intros lr.
      erewrite extract1_ne_Some; last done.
      rewrite list_delete_insert_delete //.
Qed.

Lemma lockrelG_Acquire ls ii jj xs refcntii v t' x xs1 a ts refcnt :
  length ls = length xs1 ->
  ls !! ii = Some jj ->
  xs !! jj = Some (refcntii, Some v) ->
  xs1 !! ii = Some (a, Closed, t') ->
  lockrelG refcnt xs ts ({[LockLabel (zip ls xs1)]} ⋅ x) ->
  lockrelG refcnt (<[jj:=(refcntii, None)]> xs) ts
    ({[LockLabel (zip ls (<[ii:=(a, Opened, t')]> xs1))]} ⋅ x).
Proof.
  intros ???? [order []].
  do 2 econstructor; eauto.
  - rewrite dom_insert_lookup_L //.
  - rewrite mset_forall_op. rewrite mset_forall_op in order_subsequences0.
    destruct order_subsequences0 as []. split; eauto.
    rewrite mset_forall_singleton. rewrite mset_forall_singleton in H3.
    simp. eexists. split; first done.
    rewrite fst_zip in H7; last lia.
    rewrite fst_zip; first done.
    rewrite insert_length. lia.
  - intro. specialize (lr_lockrel0 i). smap.
    + rewrite H1 in lr_lockrel0.
      destruct (ts !! i); eauto.
      revert lr_lockrel0.
      rewrite !extract_op !extract_singleton.
      erewrite extract1_Some; eauto.
      intros lr.
      erewrite extract1_Some; eauto; last first.
      { rewrite list_lookup_insert; first done. by eapply lookup_lt_Some. }
      rewrite list_delete_insert_delete.
      rewrite -assoc. rewrite -assoc in lr.
      assert (t'=t) as -> by eauto using lockrel_same_type.
      eapply lockrel_open_close. done.
    + destruct (xs !! i) eqn:E; rewrite E; last first.
      { destruct (ts !! i); done. }
      destruct p. destruct (ts !! i); eauto.
      revert lr_lockrel0.
      rewrite !extract_op !extract_singleton.
      assert (ls !! ii ≠ Some i). { congruence. }
      erewrite extract1_ne_Some; last done. intros lr.
      erewrite extract1_ne_Some; last done.
      rewrite list_delete_insert_delete //.
Qed.

Lemma sublist_filter {A} (xs ys : list A) P `{∀ x, Decision (P x)} :
  xs `sublist_of` ys ->
  filter P xs `sublist_of` filter P ys.
Proof.
  induction 1.
  - rewrite filter_nil. constructor.
  - rewrite !filter_cons. case_decide.
    + constructor. done.
    + done.
  - rewrite !filter_cons. case_decide.
    + econstructor. done.
    + done.
Qed.

Lemma delete_NoDup_filter (ls : list nat) ii jj :
  NoDup ls ->
  ls !! ii = Some jj ->
  delete ii ls = filter (λ x0 : vertex, x0 ≠ jj) ls.
Proof.
  intros H1 H2.
  revert ii H2.
  induction ls; intros ii H2. { revert H2. smap. }
  revert H2. destruct ii. smap.
  + rewrite filter_cons. case_decide; try done.
    apply NoDup_cons in H1 as [H1 H2].
    symmetry. clear H2 IHls H.
    induction ls; first done.
    rewrite filter_cons.
    apply not_elem_of_cons in H1 as [].
    case_decide; try done.
    f_equal. apply IHls. done.
  + simpl. rewrite filter_cons. intros H.
    case_decide.
    * f_equal. eapply IHls; eauto.
      eapply NoDup_cons; done.
    * subst. exfalso.
      eapply NoDup_cons in H1 as [HH ?].
      eapply HH. eapply elem_of_list_lookup_2. done.
Qed.

Lemma NoDup_sublist {A} (xs ys : list A) :
  NoDup xs ->
  ys `sublist_of` xs ->
  NoDup ys.
Proof.
  intros H1. induction 1.
  - eapply NoDup_nil. done.
  - eapply NoDup_cons. eapply NoDup_cons in H1 as [].
    split; eauto.
    intros HH. eapply H0. eapply sublist_elem_of; eauto.
  - eapply NoDup_cons in H1 as []; eauto.
Qed.

Lemma order_delete order ls ii jj :
  NoDup order ->
  ls !! ii = Some jj ->
  ls `sublist_of` order ->
  delete ii ls `sublist_of` filter (λ x0 : vertex, x0 ≠ jj) order.
Proof.
  intros H1 H2 H3.
  erewrite delete_NoDup_filter; eauto using NoDup_sublist.
  eapply sublist_filter. done.
Qed.

Lemma flat_map_nil {A B} (f : A -> list B) xs :
  flat_map f xs = nil -> ∀ x, x ∈ xs -> f x = nil.
Proof.
  induction xs; first set_solver.
  simpl. rewrite app_nil. simp.
  eapply elem_of_cons in H0 as []; simp.
  eauto.
Qed.

Lemma extract_empty i x :
  extract i x = ε ->
  mset_forall (λ l, ∀ xs, l = LockLabel xs -> i ∉ xs.*1) x.
Proof.
  intros H?????. simp.
  inv H0. simp.
  unfold extract in H.
  destruct x; simpl in *. inv H.
  intro HH.
  eapply elem_of_list_fmap in HH. simp.
  eapply (flat_map_permute (λ l : label,
  match l with
  | BarrierLabel _ _ _ => []
  | LockLabel xs => (filter (λ '(jj', _), H.1 = jj') xs).*2
  end)) in H0.
  rewrite H2 in H0. simpl in H0.
  eapply Permutation_nil in H0.
  eapply app_nil in H0. simp.
  eapply fmap_nil_inv in H1. clear H3 H2.
  assert (H ∉ xs); eauto.
  eapply filter_nil_not_elem_of; eauto. simpl.
  destruct H. done.
Qed.

Lemma mset_forall_impl {A:ofe} (P Q : A -> Prop) x :
  mset_forall P x -> (∀ a, P a -> Q a) -> mset_forall Q x.
Proof.
  intros H1 H2 a x' Hx'.
  eapply H2. eapply H1. done.
Qed.

Lemma mset_forall_and {A:ofe} (P Q : A -> Prop) x :
  mset_forall P x -> mset_forall Q x ->
  mset_forall (λ a, P a ∧ Q a) x.
Proof.
  intros H1 H2 a x' Hx'.
  split; [eapply H1|eapply H2]; eauto.
Qed.

Lemma filter_id {A} (xs : list A) (P : A -> Prop) `{∀ x, Decision (P x)} :
  (∀ x, x ∈ xs -> P x) ->
  filter P xs = xs.
Proof.
  induction xs; eauto. intro.
  rewrite filter_cons.
  case_decide; rewrite IHxs; eauto; intros.
  - eapply H0, elem_of_cons; eauto.
  - exfalso. eapply H1, H0, elem_of_cons; eauto.
  - eapply H0, elem_of_cons; eauto.
Qed.

Lemma filter_sublist {A} (xs ys : list A) (P : A -> Prop) `{∀ x, Decision (P x)} :
  xs `sublist_of` ys ->
  (∀ x, x ∈ xs -> P x) ->
  xs `sublist_of` filter P ys.
Proof.
  induction 1; intros HH; eauto using sublist;
  rewrite filter_cons; case_decide; eauto using sublist.
  - econstructor. eapply IHsublist.
    intros. eapply HH, elem_of_cons; eauto.
  - exfalso. eapply H1, HH, elem_of_cons; eauto.
  - econstructor. eapply IHsublist. eauto.
Qed.

Lemma extract1_delete ls ii jj i xs1 :
  ls !! ii = Some jj ->
  jj ≠ i ->
  extract1 i (zip (delete ii ls) (delete ii xs1)) = extract1 i (zip ls xs1).
Proof.
  intros.
  symmetry. eapply extract1_ne_Some.
  intro. smap.
Qed.

Lemma lockrelG_Wait ls ii jj xs v xs1 t' ts x refcnt :
  length ls = length xs1 ->
  ls !! ii = Some jj ->
  xs !! jj = Some (0, Some v) ->
  xs1 !! ii = Some (Owner, Closed, t') ->
  ts !! jj = Some t' ->
  lockrelG refcnt xs ts ({[LockLabel (zip ls xs1)]} ⋅ x) ->
  lockrelG refcnt (delete jj xs) (delete jj ts)
    ({[LockLabel (zip (delete ii ls) (delete ii xs1))]} ⋅ x).
Proof.
  intros HH????[order []].
  eexists (filter (λ x, x ≠ jj) order). econstructor.
  - eapply NoDup_filter; eauto.
  - rewrite dom_delete_L.
    eapply set_eq. intro.
    rewrite elem_of_list_to_set elem_of_list_filter.
    set_solver.
  - revert order_subsequences0.
    rewrite !mset_forall_op !mset_forall_singleton. simp.
    rewrite fst_zip in H7; last lia.
    split.
    + eexists. split; eauto.
      rewrite fst_zip. { eapply order_delete; eauto. }
      rewrite !length_delete; eauto.
      lia.
    + pose proof (lr_lockrel0 jj) as Q.
      rewrite H0 H2 extract_op extract_singleton in Q.
      erewrite extract1_Some in Q; eauto.
      rewrite -assoc in Q.
      eapply lockrel_only_owner in Q.
      assert (extract1 jj (zip (delete ii ls) (delete ii xs1)) ⋅ extract jj x ≡ ε) as Q'.
      { rewrite Q //. }
      eapply multiset_empty_mult in Q' as [].
      epose proof (extract_empty jj x H5).
      eapply mset_forall_impl.
      { eapply mset_forall_and. eapply H4. eapply H6. }
      intros ?[]. simp.
      eexists. split; eauto.
      eapply filter_sublist; eauto.
      intros ???. subst. eapply H9; eauto.
  - intros i. specialize (lr_lockrel0 i).
    smap. destruct (xs !! i) eqn:E; rewrite E; eauto.
    destruct p. destruct (ts !! i); eauto.
    revert lr_lockrel0. rewrite !extract_op !extract_singleton.
    intros lr.
    erewrite extract1_delete; eauto.
  - revert lr_refcount0. rewrite !Mlen_mult !Mlen_singleton. lia.
Qed.

Lemma extract1_empty i : extract1 i [] = ε.
Proof.
  done.
Qed.

Lemma lockrelG_DropGroup refcnt xs ts x :
  lockrelG (S refcnt) xs ts ({[LockLabel []]} ⋅ x) ->
  lockrelG refcnt xs ts x.
Proof.
  intros [order []].
  exists order; econstructor; eauto.
  apply mset_forall_op in order_subsequences0 as []. done.
Qed.

Lemma lockrelG_NewGroup : lockrelG 1 ∅ ∅ {[LockLabel []]}.
Proof.
  exists []. econstructor.
  - by eapply NoDup_nil.
  - rewrite list_to_set_nil dom_empty_L //.
  - rewrite mset_forall_singleton. exists []. done.
  - intro. smap.
  - done.
Qed.

Lemma lockrelG_empty_inv x : lockrelG 0 ∅ ∅ x -> x = ε.
Proof.
  intros [order []]. by eapply Mlen_zero_inv.
Qed.

Lemma list_to_set_insert2 ii jj (xs : list nat) :
  (list_to_set (insert2 ii jj xs) : gset nat) = {[jj]} ∪ list_to_set xs.
Proof.
  revert ii; induction xs; intros []; simpl; eauto.
  rewrite IHxs. set_solver.
Qed.

Lemma insert2_nil {A} ii jj :
  insert2 ii jj [] = [jj:A].
Proof.
  destruct ii; simpl; done.
Qed.

Lemma extract1_insert2_ne i ls xs1 ii jj c :
  length ls = length xs1 ->
  jj ≠ i ->
  extract1 i (zip ls xs1) ≡ extract1 i (zip (insert2 ii jj ls) (insert2 ii c xs1)).
Proof.
  intros H1 H2.
  unfold extract1.
  f_equiv. f_equal.
  revert jj i xs1 ii H1 H2. induction ls; intros; simpl in *.
  - destruct xs1; simp. rewrite filter_nil !insert2_nil.
    rewrite filter_cons filter_nil.
    case_decide; try done.
  - destruct xs1; simp.
    destruct ii; simpl.
    + rewrite !filter_cons.
      repeat case_decide; simp.
    + rewrite !filter_cons; repeat case_decide; simp.
      * f_equal. eauto.
      * eauto.
Qed.

Lemma extract_empty_inv i order x :
  i ∉ order ->
  mset_forall
        (λ l : labelO,
            ∃ xs : list (vertex * (lockcap * type)),
              l = LockLabel xs ∧ xs.*1 `sublist_of` order) x ->
  extract i x = ε.
Proof.
  unfold extract.
  destruct ((flat_map
  (λ l : label,
     match l with
     | BarrierLabel _ _ _ => []
     | LockLabel xs => multiset_car (extract1 i xs)
     end) (multiset_car x))) eqn:E; eauto.
  intros. exfalso.
  assert (In o (o :: l)); eauto using in_eq.
  rewrite -E in_flat_map in H1. simp.
  destruct H2. { inv H4. }
  eapply elem_of_list_In in H4.
  eapply elem_of_list_fmap in H4.
  simp.
  eapply elem_of_list_filter in H5. simp.
  destruct H2. simp.
  eapply elem_of_list_In in H1.
  assert (∃ x', x ≡ {[ LockLabel ls : labelO ]} ⋅ x').
  { eapply elem_of_list_lookup in H1. simp.
    exists (list_to_multiset (delete H2 (multiset_car x))).
    eapply delete_Permutation in H3.
    econstructor. split; first exact H3.
    done. }
  simp. rewrite H5 in H0.
  rewrite mset_forall_op mset_forall_singleton in H0. simp.
  eapply H, sublist_elem_of; eauto.
  eapply elem_of_list_fmap. eexists. split; eauto. simpl. done.
Qed.

Lemma extract1_insert2 i ii ls t' xs1 :
  length ls = length xs1 ->
  extract1 i (zip (insert2 ii i ls) (insert2 ii (Owner, Opened, t') xs1))
  ≡ {[ (Owner, Opened, t'):labelO' ]} ⋅ extract1 i (zip ls xs1).
Proof.
  revert xs1 ls. induction ii; simpl; intros.
  - rewrite extract1_cons. case_decide; simp.
  - destruct ls,xs1; simp; rewrite ?extract1_cons; case_decide; simp;
    rewrite IHii // !assoc.
    f_equiv. apply comm, _.
Qed.

Lemma extract1_empty' i ls xs1 :
  i ∉ ls ->
  extract1 i (zip ls xs1) = ε.
Proof.
  unfold extract1.
  revert xs1. induction ls; simpl; eauto; intros.
  eapply not_elem_of_cons in H as [].
  destruct xs1; eauto.
  rewrite filter_cons. case_decide; eauto. done.
Qed.

Fixpoint find_index (a : nat) (xs : list nat) :=
  match xs with
  | [] => None
  | a' :: xs' => if decide(a = a') then Some 0 else S <$> find_index a xs'
  end.

Lemma find_index_Some a xs i :
  find_index a xs = Some i -> xs !! i = Some a.
Proof.
  revert i; induction xs; simpl; simp.
  case_decide; destruct i; simp; eauto.
  - destruct find_index; try discriminate.
  - rewrite IHxs; eauto.
    destruct find_index; try discriminate. inv H. done.
Qed.

Lemma find_index_None a xs :
  find_index a xs = None -> a ∉ xs.
Proof.
  induction xs; simpl; try set_solver.
  case_decide; simp.
  eapply not_elem_of_cons. split; eauto.
  destruct find_index; try discriminate. eauto.
Qed.

Definition insert_at (ii jj:nat) (ls order:list nat) : list nat :=
  match ls !! ii with
  | Some a =>
    match find_index a order with
    | Some i => insert2 i jj order
    | None => order ++ [jj]
    end
  | None => order ++ [jj]
  end.

Lemma insert2_lookup_None {A} (ls : list A) ii jj :
  ls !! ii = None ->
  insert2 ii jj ls = ls ++ [jj].
Proof.
  revert ii ls. induction ii; simpl.
  - intros. destruct ls; simp.
  - intros. destruct ls; simp. f_equal. eauto.
Qed.

Lemma sublist_insert2_corr {A} (ls : list A) ii ii' jj order n :
  NoDup order ->
  ls !! ii = Some n ->
  order !! ii' = Some n ->
  ls `sublist_of` order ->
  insert2 ii jj ls `sublist_of` insert2 ii' jj order.
Proof.
  intros HND H1 H2 HH. revert H1 H2. revert ii ii'.
  induction HH; simp.
  - destruct ii; simp.
    + destruct ii'; simp.
      * do 2 econstructor. done.
      * eapply NoDup_cons in HND. simp.
        eapply elem_of_list_lookup_2 in H2. exfalso.
        eapply H. eauto.
    + destruct ii'; simpl in *; simp.
      * eapply NoDup_cons in HND. simp.
        eapply elem_of_list_lookup_2 in H1. exfalso.
        eapply H. eapply sublist_elem_of; eauto.
      * econstructor. eapply IHHH; eauto.
        eapply NoDup_cons; eauto.
  - destruct ii'; simp.
    * eapply NoDup_cons in HND. simp.
      eapply elem_of_list_lookup_2 in H1. exfalso.
      eapply H. eapply sublist_elem_of; eauto.
    * econstructor. eapply IHHH; eauto. eapply NoDup_cons. eauto.
Qed.

Lemma insert_at_sublist ls order ii jj :
  NoDup order ->
  ls `sublist_of` order ->
  insert2 ii jj ls `sublist_of` insert_at ii jj ls order.
Proof.
  unfold insert_at.
  destruct (ls!!ii) eqn:E.
  - destruct (find_index n order) eqn:F.
    + eapply find_index_Some in F.
      intros HH. eapply sublist_insert2_corr; eauto.
    + eapply find_index_None in F. intros. exfalso.
      eapply F, sublist_elem_of; eauto.
      eapply elem_of_list_lookup. eauto.
  - intros.
    rewrite insert2_lookup_None //.
    eapply sublist_app; eauto.
Qed.

Lemma insert_at_NoDup ii jj ls order :
  NoDup order ->
  jj ∉ order ->
  NoDup (insert_at ii jj ls order).
Proof.
  intros.
  unfold insert_at.
  destruct (ls!!ii).
  - destruct find_index.
    + eauto using insert2_NoDup_2.
    + eapply NoDup_app; split; eauto.
      split. set_solver. apply NoDup_singleton.
  - eapply NoDup_app; split; eauto.
    split. set_solver. apply NoDup_singleton.
Qed.

Lemma list_to_set_insert_at ii jj ls order:
  (list_to_set (insert_at ii jj ls order) : gset nat) = {[ jj ]} ∪ list_to_set order.
Proof.
  unfold insert_at.
  destruct lookup.
  - destruct find_index.
    + rewrite list_to_set_insert2 //.
    + set_solver.
  - set_solver.
Qed.

Lemma insert2_sublist_mono {A} (ls : list A) order ii jj :
  ls `sublist_of` order ->
  ls `sublist_of` insert2 ii jj order.
Proof.
  intros H.
  revert ii. induction H; destruct ii; simpl;
  try econstructor; try econstructor; eauto.
Qed.

Lemma insert_at_sublist_mono ii jj ls ls' order :
  ls' `sublist_of` order ->
  ls' `sublist_of` insert_at ii jj ls order.
Proof.
  unfold insert_at; intros.
  destruct lookup.
  - destruct find_index.
    + eapply insert2_sublist_mono. done.
    + eapply sublist_inserts_r. done.
  - eapply sublist_inserts_r. done.
Qed.

Lemma lockrelG_NewLock refcnt xs ts ls xs1 x t' ii jj :
  length ls = length xs1 ->
  xs !! jj = None ->
  lockrelG refcnt xs ts ({[LockLabel (zip ls xs1)]} ⋅ x) ->
  lockrelG refcnt (<[jj:=(0, None)]> xs) (<[jj:=t']> ts)
    ({[LockLabel (zip (insert2 ii jj ls) (insert2 ii (Owner, Opened, t') xs1))]} ⋅ x).
Proof.
  intros HH H [order []].
  exists (insert_at ii jj ls order). econstructor.
  - eapply insert_at_NoDup; eauto.
    assert (jj ∉ dom xs) as Q. { eapply not_elem_of_dom. done. }
    rewrite -order_dom0 in Q.
    eapply not_elem_of_list_to_set in Q.
    done.
  - rewrite dom_insert_L -order_dom0 list_to_set_insert_at //.
  - revert order_subsequences0. rewrite !mset_forall_op !mset_forall_singleton.
    intros os. simp.
    rewrite fst_zip in H4; last lia.
    split.
    + eexists. split; first done.
      rewrite fst_zip. 2: { rewrite !insert2_length. lia. }
      eapply insert_at_sublist; done.
    + eapply mset_forall_impl; eauto. simpl. intros. simp.
      eexists. split; eauto.
      eapply insert_at_sublist_mono; done.
  - intros i. specialize (lr_lockrel0 i).
    smap.
    + rewrite extract_op extract_singleton.
      rewrite H in lr_lockrel0.
      destruct (ts !! i) eqn:E; try done.
      assert ((extract1 i (zip (insert2 ii i ls) (insert2 ii (Owner, Opened, t') xs1))
        ⋅ extract i x) ≡ {[ (Owner, Opened, t'):labelO' ]}) as ->; eauto using lockrel_newlock'.
      rewrite mset_forall_op mset_forall_singleton in order_subsequences0. simp.
      rewrite fst_zip in H4; try lia.
      assert (extract i x = ε) as ->.
      {
        assert (i ∉ order).
        {
           intros QQ.
           assert (i ∈ dom xs).
           {
            rewrite -order_dom0. eapply elem_of_list_to_set. done.
           }
           eapply elem_of_dom in H0 as []. rewrite H in H0. congruence.
        }
        eapply extract_empty_inv; eauto.
      }
      rewrite right_id extract1_insert2 // extract1_empty'; first apply right_id, _.
      intros QQ.
      eapply sublist_elem_of in QQ; eauto.
      assert (i ∈ dom xs).
      {
        rewrite -order_dom0. eapply elem_of_list_to_set. done.
      }
      eapply elem_of_dom in H0 as []. rewrite H in H0. done.
    + destruct (xs !! i) eqn:E; rewrite E; eauto.
      destruct p. destruct (ts !! i); eauto.
      revert lr_lockrel0. rewrite !extract_op !extract_singleton.
      intros lr.
      assert ((extract1 i (zip ls xs1) ⋅ extract i x) ≡
        (extract1 i (zip (insert2 ii jj ls) (insert2 ii (Owner, Opened, t') xs1))⋅ extract i x)) as <-; eauto.
      f_equiv. eapply extract1_insert2_ne; eauto.
  - revert lr_refcount0. rewrite !Mlen_mult !Mlen_singleton. lia.
Qed.

Lemma lockrelG_same_dom_empty refcnt xs ts x i :
  lockrelG refcnt xs ts x ->
  xs !! i = None <-> ts !! i = None.
Proof.
  intros [order []].
  specialize (lr_lockrel0 i).
  destruct (xs !! i),(ts!!i); try done.
  destruct p;done.
Qed.

Lemma lockrelG_DropLock refcnt xs ts ls xs1 x t' ii jj refcntii o :
  length ls = length xs1 ->
  ls !! ii = Some jj ->
  xs !! jj = Some (S refcntii, o) ->
  xs1 !! ii = Some (Client, Closed, t') ->
  lockrelG refcnt xs ts ({[LockLabel (zip ls xs1)]} ⋅ x) ->
  lockrelG refcnt (<[jj:=(refcntii, o)]> xs) ts
    ({[LockLabel (zip (delete ii ls) (delete ii xs1))]} ⋅ x).
Proof.
  intros ????[order []].
  econstructor; eauto; econstructor; eauto.
  - rewrite dom_insert_lookup_L //.
  - rewrite mset_forall_op. rewrite mset_forall_op in order_subsequences0.
    destruct order_subsequences0 as []. split; eauto.
    rewrite mset_forall_singleton. rewrite mset_forall_singleton in H3.
    simp. eexists. split; first done.
    rewrite fst_zip in H7; last lia.
    rewrite fst_zip.
    + etrans; last done. apply sublist_delete.
    + rewrite !length_delete; eauto. lia.
  - intro. specialize (lr_lockrel0 i). smap.
    + rewrite H1 in lr_lockrel0.
      destruct (ts !! i); eauto.
      revert lr_lockrel0.
      rewrite !extract_op !extract_singleton.
      erewrite extract1_Some; eauto.
      intros lr.
      rewrite -assoc in lr.
      assert (t'=t) as -> by eauto using lockrel_same_type.
      eapply lockrel_drop in lr. done.
    + destruct (xs !! i) eqn:E; rewrite E; last first.
      { destruct (ts !! i); done. }
      destruct p. destruct (ts !! i); eauto.
      revert lr_lockrel0.
      rewrite !extract_op !extract_singleton.
      assert (ls !! ii ≠ Some i). { congruence. }
      erewrite extract1_ne_Some; last done. done.
Qed.

Lemma extract1_notin xs {ls i} :
  i ∉ ls ->
  extract1 i (zip ls xs) = ε.
Proof.
  revert ls. induction xs; intros []; [simpl..|];
  rewrite ?extract1_empty; eauto.
  intros H.
  eapply not_elem_of_cons in H as [].
  erewrite <-(extract1_delete _ 0); eauto.
Qed.

Lemma NoDup_delete_notin {A} (ls : list A) ii i :
  NoDup ls ->
  ls !! ii = Some i ->
  i ∉ delete ii ls.
Proof.
  intros ???.
  eapply elem_of_list_lookup_1 in H1 as [? ?].
  rewrite lookup_delete_lr in H1.
  case_decide.
  - assert (x = ii); last lia.
    eapply NoDup_lookup; eauto.
  - assert (S x = ii); last lia.
    eapply NoDup_lookup; eauto.
Qed.

Lemma extract1_Some_NoDup ii i l ls xs :
  NoDup ls ->
  ls !! ii = Some i ->
  xs !! ii = Some l ->
  extract1 i (zip ls xs) ≡ {[ l:labelO' ]}.
Proof.
  intros. erewrite extract1_Some; eauto.
  rewrite extract1_notin. { rewrite right_id //. }
  eapply NoDup_delete_notin; eauto.
Qed.

Lemma incr_all_refcounts_lookup xs ls i :
  NoDup ls ->
  incr_all_refcounts xs ls !! i =
  match xs !! i with
  | None => None
  | Some (refcnt,o) =>
      Some (if decide (i ∈ ls) then S refcnt else refcnt, o)
  end.
Proof.
  intros Hls.
  unfold incr_all_refcounts.
  revert xs i. induction ls; intros; simpl.
  { destruct (xs!!i); eauto. destruct p; eauto. }
  smap.
  - eapply NoDup_cons in Hls as [].
    rewrite IHls //.
    destruct (xs !! i); eauto.
    destruct p. simpl. case_decide; do 2 f_equal; (done||lia).
  - set_solver.
  - eapply NoDup_cons in Hls as [].
    rewrite IHls //.
    destruct (xs !! i); eauto. smap.
    eapply elem_of_cons in H0 as []; smap.
  - eapply NoDup_cons in Hls as [].
    rewrite IHls //.
    destruct (xs !! i); eauto. smap.
    set_solver.
Qed.

Lemma incr_all_refcounts_dom xs ls :
  dom (incr_all_refcounts xs ls) = dom xs.
Proof.
  unfold incr_all_refcounts.
  revert xs. induction ls; simpl; eauto.
  intros. rewrite dom_alter_L IHls //.
Qed.

Lemma lockrelG_ForkLock xs1 xs2 xs3 ls x refcnt xs ts :
  length ls = length xs1 ->
  lockcaps_split xs1 xs2 xs3 ->
  lockrelG refcnt xs ts ({[LockLabel (zip ls xs1)]} ⋅ x) ->
  lockrelG (S refcnt) (incr_all_refcounts xs ls) ts
    ({[LockLabel (zip ls xs3)]} ⋅ {[LockLabel (zip ls xs2)]} ⋅ x).
Proof.
  intros HH H [order []].
  exists order; eauto. econstructor; eauto.
  - revert order_subsequences0. rewrite !mset_forall_op !mset_forall_singleton.
    intros []. simp.
    rewrite fst_zip in H4; last lia.
    eapply lockcaps_split_length in H.
    rewrite incr_all_refcounts_dom //.
  - revert order_subsequences0.
    rewrite !mset_forall_op !mset_forall_singleton.
    simp.
    rewrite fst_zip in H4; last lia.
    split; eauto.
    eapply lockcaps_split_length in H as [].
    split; eexists; split; eauto; rewrite fst_zip; eauto; lia.
  - intros i. specialize (lr_lockrel0 i).
    rewrite mset_forall_op mset_forall_singleton in order_subsequences0.
    simp. rewrite fst_zip in H4; last lia.
    rewrite incr_all_refcounts_lookup; eauto using NoDup_sublist.
    destruct (xs !! i); eauto. destruct p.
    destruct (ts !! i); eauto.
    revert lr_lockrel0.
    rewrite !extract_op !extract_singleton. intro.
    assert (NoDup ls); eauto using NoDup_sublist.
    case_decide; last first.
    {
      revert lr_lockrel0.
      do 3 (erewrite extract1_notin; eauto).
    }
    eapply elem_of_list_lookup_1 in H2 as [ii Hii].
    assert (ii < length ls); eauto using lookup_lt_is_Some_1.
    destruct (lockcaps_split_length _ _ _ H).
    assert (is_Some (xs1 !! ii)) as []; eauto using lookup_lt_is_Some_2 with lia.
    assert (is_Some (xs2 !! ii)) as []; eauto using lookup_lt_is_Some_2 with lia.
    assert (is_Some (xs3 !! ii)) as []; eauto using lookup_lt_is_Some_2 with lia.
    rewrite extract1_Some_NoDup; eauto.
    rewrite extract1_Some_NoDup; eauto.
    rewrite extract1_Some_NoDup in lr_lockrel0; eauto.
    destruct x0, x1, x2.
    unfold lockcaps_split in *.
    eapply Forall3_lookup_lmr in H; eauto. simpl in *. simp.
    assert (t2 = t) as ->.
    { eapply lockrel_same_type; eauto. }
    eapply lockrel_split; eauto.
  - revert lr_refcount0. rewrite !Mlen_mult !Mlen_singleton. intro. lia.
Qed.

Lemma big_sepM_dom' `{Countable K} {V} (m : gmap K V) (P : K -> V -> rProp) :
  ([∗ map] k↦v ∈ m, P k v)%I ⊣⊢ [∗ set] k∈dom m, from_option (P k) True (m!!k).
Proof.
  induction m using map_ind.
  - rewrite dom_empty_L big_sepM_empty big_sepS_empty //.
  - rewrite big_sepM_insert; eauto.
    rewrite dom_insert_L.
    rewrite big_sepS_union; last first.
    {
      intros ???. assert (x0 = i) as -> by set_solver.
      apply elem_of_dom in H2 as []. congruence.
    }
    rewrite IHm.
    rewrite big_sepS_singleton. smap.
    iSplit; iIntros "[? H]"; iFrame; iApply (big_sepS_impl with "H");
    iModIntro; iIntros (? ?); smap; eapply elem_of_dom in H1 as []; congruence.
Qed.

Lemma incr_all_refcounts_proj xs x x0 x2 ls :
  xs !! x = Some x0 ->
  incr_all_refcounts xs ls !! x = Some x2 ->
  x0.2 = x2.2.
Proof.
  destruct x0, x2.
  revert xs x n o n0 o0; induction ls; intros; simpl in *; try congruence.
  rewrite lookup_alter_spec in H0. smap.
  destruct (incr_all_refcounts xs ls !! x) as [[]|] eqn:E.
  - rewrite E in H0. smap.
  - rewrite E in H0. smap.
Qed.

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
  - (* NewGroup *)
    eapply (inv_alloc_l i0 n);
    last done; first apply _; first apply _.
    + done.
    + iIntros (? ? ?) "H". unfold linv. smap.
    + iIntros (?) "H". unfold linv. smap.
      assert (ρf !! n = None) as -> by solve_map_disjoint; eauto.
    + iIntros (?) "H". unfold linv. smap. iDestr "H".
      iDestruct (replacement with "H") as (t) "[H Q]"; first done. simpl.
      iDestr "H". simp.
      iExists (LockLabel []).
      iSplitL "Q".
      * iIntros "H". iSplit; first done.
        iApply "Q". simpl. eauto.
      * iExists ∅. iSplit; last done.
        iPureIntro. eapply lockrelG_NewGroup.
  - (* DeleteGroup *)
    eapply inv_impl; last done.
    iIntros (m x) "H". unfold linv. smap; iDestr "H";
    assert (ρf !! m = None) as -> by solve_map_disjoint; eauto.
    iDestruct (big_sepM2_empty_r with "H") as %->.
    rewrite big_sepM2_empty. iPureIntro.
    apply lockrelG_empty_inv in H. subst. done.
  - (* DropGroup *)
    eapply (inv_dealloc i0 n);
    last done; first apply _; first apply _.
    + iIntros (? ? ?) "H". unfold linv. smap.
    + iIntros (?) "H". unfold linv. smap. iDestr "H".
      iDestruct (replacement with "H") as (t) "[H Q]"; first done. simpl.
      iDestr "H". simp.
      iExists _. iFrame. iIntros (x) "H". iDestr "H".
      iSplitL "Q".
      * iSplit; first done. iApply "Q". done.
      * iExists _. iSplit; last done.
        iPureIntro. eapply lockrelG_DropGroup; eauto.
    - (* NewLock *)
      eapply (inv_exchange i0 n);
      last done; first apply _; first apply _.
      + iIntros (? ? ?) "H". unfold linv. smap.
      + iIntros (?) "H". unfold linv. smap. iDestr "H".
        iDestruct (replacement with "H") as (t) "[H Q]"; first done. simpl.
        iDestr "H". simp.
        iExists _. iFrame. iIntros (x) "H". iDestr "H".
        iExists _.
        iSplitL "Q".
        * iIntros "H'". iSplit; first done.
          iApply "Q". simpl. iExists _. iFrame.
          iPureIntro. split; first done.
          rewrite !insert2_length. f_equal. done.
        * iExists (<[ jj := t' ]> ts).
          iSplit.
          ** iPureIntro.
              About lockrelG_NewLock.
             eapply lockrelG_NewLock; eauto.
          ** rewrite big_sepM2_insert; simpl; eauto.
             eapply lockrelG_same_dom_empty; eauto.
    - (* DropLock *)
      eapply (inv_exchange i0 n);
      last done; first apply _; first apply _.
      + iIntros (? ? ?) "H". unfold linv. smap.
      + iIntros (?) "H". unfold linv. smap. iDestr "H".
        iDestruct (replacement with "H") as (t) "[H Q]"; first done. simpl.
        iDestr "H". simp.
        iExists _. iFrame. iIntros (x) "H". iDestr "H".
        iExists _.
        iSplitL "Q".
        * iIntros "H'". iSplit; first done.
          iApply "Q". simpl. iExists _. iFrame.
          iPureIntro. split; first done.
          rewrite !length_delete; eauto.
        * iExists ts.
          iSplit.
          ** iPureIntro. eapply lockrelG_DropLock; eauto.
          ** iApply big_sepM2_delete_l; first smap.
             rewrite big_sepM2_delete_l; last done.
             iDestr "H". iDestruct "H" as "[H1 H2]".
             iExists _. iFrame. rewrite delete_insert_delete.
             iSplit; eauto.
    - (* Acquire *)
      eapply (inv_exchange i0 n);
      last done; first apply _; first apply _.
      + iIntros (? ? ?) "H". unfold linv. smap.
      + iIntros (?) "H". unfold linv. smap. iDestr "H".
        iDestruct (replacement with "H") as (t) "[H Q]"; first done. simpl.
        iDestr "H". simp.
        iExists _. iFrame. iIntros (x) "H". iDestr "H".
        iExists _.
        (* Need to split "H" into value we need and rest *)
        rewrite big_sepM2_delete_l; last done.
        simpl. iDestr "H".
        assert (x2 = t') as -> by eauto using lockrelG_types_same.
        iDestruct "H" as "[Hv H]".
        iSplitL "Q Hv".
        * iIntros "H'". iSplit; first done.
          iApply "Q". simpl. iExists _,_. iSplit; first done.
          iSplitL "H'"; iFrame.
          iExists _. iFrame.
          iPureIntro. split; first done.
          rewrite insert_length //.
        * iExists ts. iSplit.
          { iPureIntro. eapply lockrelG_Acquire; eauto. }
          iApply big_sepM2_delete_l; first smap.
          iExists _. smap. iSplit; eauto. iSplit; eauto.
          rewrite delete_insert_delete //.
  - (* Release *)
    eapply (inv_exchange i0 n);
    last done; first apply _; first apply _.
    + iIntros (? ? ?) "H". unfold linv. smap.
    + iIntros (?) "H". unfold linv. smap. iDestr "H".
      iDestruct (replacement with "H") as (t) "[H Q]"; first done. simpl.
      iDestr "H". simp. iDestruct "H" as "[H1 H2]". iDestr "H1".
      iExists _. iFrame. iIntros (x) "H". iDestr "H".
      iExists _. simp.
      iSplitL "Q".
      * iIntros "H'". iSplit; first done.
        iApply "Q". simpl. iExists _. iFrame.
        iPureIntro. split; first done. simp.
        rewrite insert_length //.
      * iExists ts. iSplit.
        { iPureIntro. eapply lockrelG_Release; eauto. }
        rewrite big_sepM2_delete_l; last done. simpl.
        iApply big_sepM2_delete_l; first smap.
        iDestr "H". iDestruct "H" as "[_ H]".
        iExists _. iSplit; first done. simpl.
        assert (x2 = t') as -> by eauto using lockrelG_types_same.
        iFrame. rewrite delete_insert_delete //.
  - (* Wait *)
    eapply (inv_exchange i0 n);
    last done; first apply _; first apply _.
    + iIntros (? ? ?) "H". unfold linv. smap.
    + iIntros (?) "H". unfold linv. smap. iDestr "H".
      iDestruct (replacement with "H") as (t) "[H Q]"; first done. simpl.
      iDestr "H". simp. iExists _. iFrame.
      iIntros (x) "H". iDestr "H".
      iExists _.
      (* Need to split "H" into value we need and rest *)
      rewrite big_sepM2_delete_l; last done.
      simpl. iDestr "H".
      assert (x2 = t') as -> by eauto using lockrelG_types_same.
      iDestruct "H" as "[Hv H]".
      iSplitL "Q Hv".
      * iIntros "H'". iSplit; first done.
        iApply "Q". simpl. iExists _,_. iSplit; first done.
        iFrame.
        iExists _. iFrame.
        iPureIntro. split; first done.
        rewrite !length_delete //.
        f_equal. done.
      * iExists (delete jj ts). iSplit; last done.
        iPureIntro. eapply lockrelG_Wait; eauto.
  - (* ForkLock *)
    eapply (inv_exchange_alloc i0 n j); last done; first apply _; first apply _.
    + done.
    + iIntros (? ? ?) "H". unfold linv. smap.
    + iIntros (?) "H". unfold linv. smap.
      assert (ρf !! j = None) as -> by solve_map_disjoint; eauto.
    + iIntros (?) "H". unfold linv. smap. iDestr "H".
      iDestruct (replacement with "H") as (t) "[H Q]"; first done. simpl.
      iDestr "H". simp. iDestruct "H" as "[H1 H2]". iDestr "H1". simp.
      iExists _. iFrame.
      iIntros (?) "H". iDestr "H".
      (* assert (t'0 = t) as -> by eauto using lockrel_same_type. *)
      (* iExists (LockLabel l3 t),(LockLabel l2 t). *)
      iExists (LockLabel (zip ls xs3)),(LockLabel (zip ls xs2)).
      edestruct lockcaps_split_length as []; first done.
      iSplitL "Q".
      {
        iIntros "H". iSplit; first done. iApply "Q". simpl.
        iExists _. iFrame. iPureIntro. split; first done. lia.
      }
      iSplitL "H".
      * iExists ts. iSplit.
        { iPureIntro. eapply lockrelG_ForkLock; eauto. } clear.
        rewrite !big_sepM2_alt.
        iDestruct "H" as "[% H2]".
        iSplit. { iPureIntro. intro. specialize (H k). revert H.
                  rewrite -!elem_of_dom incr_all_refcounts_dom //. }
        rewrite !big_sepM_dom'.
        rewrite !dom_map_zip_with_L incr_all_refcounts_dom.
        iApply (big_sepS_impl with "H2").
        iModIntro. iIntros (x HH) "H".
        eapply elem_of_intersection in HH as [].
        eapply elem_of_dom in H0 as [].
        eapply elem_of_dom in H1 as [].
        assert (map_zip xs ts !! x = Some (x0,x1)) as ->.
        { eapply map_lookup_zip_Some. eauto. }
        simpl.
        assert (is_Some (incr_all_refcounts xs ls !! x)) as [].
        {
          apply elem_of_dom. rewrite incr_all_refcounts_dom.
          apply elem_of_dom. eauto.
        }
        assert (map_zip (incr_all_refcounts xs ls) ts !! x = Some (x2,x1)) as ->.
        { eapply map_lookup_zip_Some. eauto. }
        simpl. eapply incr_all_refcounts_proj in H2 as ->; eauto.
      * iIntros "H". iSplit; first done.
        iExists _,_. iFrame.
        iExists _. iFrame.
        iPureIntro. split; first done. lia.
Qed.

Lemma cfg_fresh1 (ρ : cfg) :
  ∃ j, ρ !! j = None.
Proof.
  exists (fresh (dom ρ)).
  apply not_elem_of_dom.
  apply is_fresh.
Qed.

Lemma map_fresh1 {V} (ρ : gmap nat V) :
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

Lemma big_sepM2_own_dom `{Countable K} {V1 V2} (m1 : gmap K V1) (m2 : gmap K V2) f :
  ([∗ map] x;y ∈ m1;m2, own_dom (f x)) ⊢ own_dom (gmap_union f m1).
Proof.
  unfold gmap_union.
  revert m2.
  induction m1 using map_ind; intros m2.
  { rewrite map_fold_empty.
    rewrite own_dom_empty.
    iIntros "H".
    destruct (decide (m2 = ∅)).
    - subst. rewrite big_sepM2_empty //.
    - iExFalso. rewrite big_sepM2_empty_r. iDestruct "H" as %Q. done. }
  rewrite map_fold_insert; eauto; last first.
  { smap. rewrite -!assoc_L. f_equal. rewrite comm_L //. }
  iIntros "H".
  rewrite big_sepM2_delete_l; last smap.
  iDestr "H". iDestruct "H" as "[H1 H2]".
  rewrite delete_insert; last done.
  rewrite -own_dom_union. iFrame.
  iApply IHm1. done.
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
    eapply own_dom_same.
    eapply holds_entails; first done.
    iIntros "H".
    iApply big_sepM2_own_dom.
    Search big_sepM2.
    iApply (big_sepM2_impl with "H").
    iModIntro. iIntros (?????) "H".
    destruct x1. simpl. destruct o; simpl.
    + iApply val_typed_refs; done.
    + iApply own_dom_empty; done.
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

Fixpoint acquire_progress (lcks : locksbundle) (ls : list (vertex * (lockcap * type))) :=
  match ls with
  | (n, ((lo, Closed), t))::ls' =>
      acquire_progress lcks ls' ∧
      ∃ refcnt v, lcks !! n = Some (refcnt, Some v)
  | _ => True
  end.

Lemma acquire_progress_alt (lcks : locksbundle) (ls : list (vertex * (lockcap * type))) :
  acquire_progress lcks ls <->
  ∀ i, (∀ j, j < i -> ∃ lo t n, ls !! j = Some (n, ((lo, Closed), t))) ->
    ∀ lo t n, ls !! i = Some (n, ((lo, Closed), t)) ->
       ∃ refcnt v, lcks !! n = Some (refcnt, Some v).
Proof.
  split.
  - induction ls; simpl.
    { intros. simp. }
    intros HH.
    destruct a. destruct p. destruct l. intros.
    destruct i; simp.
    eapply IHls in H0; eauto.
    + specialize (H 0). destruct l0.
      * edestruct H; first lia. simp.
      * simp.
    + intros. specialize (H (S j)); simpl in *. eapply H. lia.
  - intros. induction ls; simpl; eauto.
    destruct a. destruct p. destruct l. destruct l0; eauto.
    split.
    + eapply IHls; intros. eapply (H (S i)); simp.
      destruct j; simp; eauto. eapply H0. lia.
    + eapply (H 0); simp. lia.
Qed.

Fixpoint wait_progress0 (lcks : locksbundle) (ls : list (vertex * (lockcap * type))) :=
  match ls with
  | (n, ((Owner, Closed), t))::ls' =>
      wait_progress0 lcks ls' ∧
      ∃ v, lcks !! n = Some (0, Some v)
  | _ => True
  end.

Definition wait_progress lcks ls :=
  (∀ x, x ∈ ls -> x.2.1.2 = Closed) -> wait_progress0 lcks ls.

Lemma wait_progress_alt (lcks : locksbundle) (ls : list (vertex * (lockcap * type))) :
  wait_progress lcks ls <->
  ∀ i:nat,
    (∀ j n lown lstate t, ls !! j = Some (n, ((lown, lstate), t)) -> lstate = Closed ∧ (j < i -> lown = Owner)) ->
    (∀ (t:type) n, ls !! i = Some (n, ((Owner, Closed), t)) -> ∃ v, lcks !! n = Some (0, Some v)).
Proof.
  split.
  - induction ls; simpl.
    { intros. simp. }
    intros. unfold wait_progress in H. simpl in *.
    destruct a. destruct p. destruct l.
    destruct i; simp.
    + edestruct H; eauto.
      intros. eapply elem_of_cons in H1 as []; simp.
      eapply elem_of_list_lookup in H1 as [].
      destruct x as [? [[] ?]].
      simpl. edestruct (H0 (S x0)); simp.
    + eapply IHls;eauto.
      * unfold wait_progress. intros.
        specialize (H0 0). simpl in *. edestruct H0; eauto.
        simp. assert (l = Owner) as ->; eauto with lia.
        edestruct H; eauto. intros.
        eapply elem_of_cons in H3 as []; simp; eauto.
      * intros. edestruct (H0 (S j)); eauto with lia.
  - intros ??. induction ls; simpl; eauto.
    destruct a. destruct p. destruct l.
    destruct l; simp. destruct l0; simp.
    split.
    + eapply IHls.
      * intros. eapply (H (S i)); eauto.
        intros. destruct j; simp; eauto.
        edestruct H1; eauto. split; eauto with lia.
      * intros. eapply H0. eapply elem_of_cons; eauto.
    + eapply (H 0); eauto. intros.
      destruct j; simp; eauto with lia.
      edestruct H0.
      { apply elem_of_list_lookup. eexists (S j). eauto. }
      simpl. eauto with lia.
Qed.

Record can_progress (refcnt : nat) (lcks : locksbundle)
                    (ls : list (vertex * (lockcap * type))) : Prop := {
  cp_acquire : acquire_progress lcks ls;
  cp_wait : wait_progress lcks ls;
}.

(*
Case #1: all the locks are closed

    0,   0,   0,   3,   0,   5,  ...

                   Client

Proof of case #1:
Acquire progress is okay.
Check if first column has a client, if so, choose that row.
If first column has only owner, use IH.
Then if IH returns same row as owner, prepend the first column.
Otherwise, we are also good.


Case #2: there is a lock that is opened => then we select the row with an opened

    Some v1, Some v2, Some v3, None, None, Some v4,  ...

                               Opened, ??

Proof of case #2:
First, check if there is an opened in the first column, if so, we are done.
Now the first column has only closed.
Then there must be an opened in the remainder of the matrix, so IH applies.
So IH gives us a row with acquire_progress and wait_progress and an opened in the row.
Done.

*)
(*
1. Keep track of index i into lock order, and do some kind of induction on that
2. Do induction on lock order list directly
*)

Definition all_closed x := mset_forall (λ lab,
  ∃ ls, lab = LockLabel ls ∧ ∀ x, x ∈ ls -> x.2.1.2 = Closed) x.

Definition delcol (i : nat) (x : multiset labelO) : multiset labelO. Admitted.

Definition melem_of {A:ofe} (a:A) (x:multiset A) := ∃ x', x ≡ {[ a ]} ⋅ x'.

Lemma mset_empty_or_not {A:ofe} (x:multiset A) :
  x = ε ∨ ∃ a, melem_of a x.
Proof.
  destruct x; simp. destruct multiset_car; simp; eauto.
  right. exists o.
  unfold melem_of.
  exists (list_to_multiset multiset_car). simp.
Qed.

Definition mset_exists {A:ofe} (P : A -> Prop) (x : multiset A) :=
  ∃ a, melem_of a x ∧ P a.

Lemma melem_of_forall {A:ofe} P (x:multiset A) a :
  mset_forall P x -> melem_of a x -> P a.
Proof.
  intros H1 H2.
  unfold mset_forall in *.
  destruct H2.
  specialize (H1 _ _ H).
  done.
Qed.

Lemma lockrelG'_empty refcnt lcks t x :
  lockrelG' [] refcnt lcks t x -> lcks = ∅.
Proof.
  intros [].
  simpl in *.
  symmetry in order_dom0.
  apply dom_empty_iff_L in order_dom0. simp.
Qed.

Lemma lock_relG'_del a order refcnt lcks t x :
  lockrelG' (a :: order) refcnt lcks t x ->
  lockrelG' order refcnt (delete a lcks) (delete a t) (delcol a x).
Proof.
Admitted.

Lemma all_closed_del x a :
  all_closed x -> all_closed (delcol a x).
Proof.
Admitted.




Lemma lockrelG_open_progress order refcnt lcks t x :
  lockrelG' order refcnt lcks t x ->
  ¬ all_closed x ->
  refcnt = 0 ∧ lcks = ∅
  ∨ (∃ ls : list (vertex * (lockcap * type)),
      melem_of (LockLabel ls) x ∧
      can_progress refcnt lcks ls ∧
      ∃ l, l ∈ ls ∧ l.2.1.2 = Opened).
Proof.
  intros.
  cut (refcnt = 0 ∧ lcks = ∅
      ∨ (∃ ls : list (vertex * (lockcap * type)),
          melem_of (LockLabel ls) x ∧
          acquire_progress lcks ls ∧
          ∃ l, l ∈ ls ∧ l.2.1.2 = Opened)).
  {
    intros []. simp; eauto.
    simp. right. eexists.
    split_and!; eauto.
    split; eauto.
    intro. specialize (H6 H4). simp.
    congruence.
  }
  revert refcnt lcks t x H H0. induction order; intros.
  - left. split; eauto using lockrelG'_empty.
    admit.
  -
      (* First, check if there is an opened in the first column, if so, we are done. *)
      (* Now the first column has only closed. *)
      (* Then there must be an opened in the remainder of the matrix, so IH applies. *)
      (* So IH gives us a row with acquire_progress and wait_progress and an opened in the row. *)
      (* Done. *)
Admitted.


Lemma all_closed_acquire_progress order refcnt lcks t x ls :
  all_closed x ->
  lockrelG' order refcnt lcks t x ->
  melem_of (LockLabel ls) x ->
  acquire_progress lcks ls.
Proof.
  intros H1 H2 H3.
  assert (∀ l, l ∈ ls -> ∃ rc v, lcks !! l.1 = Some(rc, Some v)).
  {
    intros l H.
    destruct H2.
    assert(is_Some(lcks !! l.1)) as [].
    {
      eapply melem_of_forall in H3; eauto. simp.
      destruct l; simp.
      assert (n ∈ H0.*1).
      { eapply elem_of_fmap. eexists. split; eauto. simp. }
      eapply sublist_elem_of in H4; eauto.
      eapply elem_of_list_to_set in H4.
      assert (n ∈ dom lcks); eauto.
      { rewrite -order_dom0. done. }
      eapply elem_of_dom in H3. done.
    }
    specialize (lr_lockrel0 l.1).
    rewrite H0 in lr_lockrel0. destruct x0.
    destruct (t !! l.1); simp.
    destruct o; eauto.
    exfalso.
    destruct lr_lockrel0.

    admit.
  }
  clear H3 H2 H1.
  induction ls; simpl; eauto.
  destruct a. destruct p. destruct l. destruct l0; eauto.
  split.
  - eapply IHls. intros. eapply H. eapply elem_of_cons. eauto.
  - edestruct H. { eapply elem_of_cons. left. done. }
    simp. eauto.
Admitted.

Lemma lockrel_nonempty n o t :
  ¬ lockrel n o t ε.
Proof.
  intros [].
  symmetry in lr_split.
  eapply multiset_empty_mult in lr_split. simp.
Qed.

Lemma lockrelG'_refcnt_0 order lcks t x :
  lockrelG' order 0 lcks t x -> order = [].
Proof.
  intros [].
  eapply Mlen_zero_inv in lr_refcount0. simp.
  destruct order; simp. exfalso.
  specialize (lr_lockrel0 n).
  destruct (lcks !! n) eqn:E.
  - destruct p. destruct (t !! n); simp.
    assert (extract n ε = ε) by done.
    rewrite H in lr_lockrel0.
    eapply lockrel_nonempty; eauto.
  - assert (n ∈ dom lcks) by set_solver.
    eapply elem_of_dom in H as [].
    rewrite E in H. congruence.
Qed.

Lemma lockrelG'_empty_elem refcnt lcks t x :
  lockrelG' [] (S refcnt) lcks t x ->
  melem_of (LockLabel []) x.
Proof.
  intros [].
  destruct (mset_empty_or_not x); simp.
  destruct H0; simp.
  { eapply melem_of_forall in H1; eauto. simp. }
  destruct ls; simp.
  eapply melem_of_forall in H1; eauto. simp.
  inv H2.
Qed.

Lemma lockrelG_progress refcnt lcks t x :
  lockrelG refcnt lcks t x ->
  (refcnt=0 ∧ lcks=∅) ∨ ∃ ls,
    melem_of (LockLabel ls) x ∧ can_progress refcnt lcks ls.
Proof.
  intros [order H].
  destruct (classic (all_closed x)) as [Hx|Hx].
  {
    revert Hx H.
    revert t x lcks refcnt.
    induction order; intros.
    - assert (lcks = ∅) as -> by eauto using lockrelG'_empty.
      destruct refcnt; eauto.
      right. exists []. split; eauto using lockrelG'_empty_elem.
      split; simpl; eauto. intro. done.
    - right.
      (* Check if first column has a client, if so, choose that row. *)
      destruct (classic (mset_exists (λ l, ∃ ls y,
        l = LockLabel ((a,y)::ls) ∧ y.1.1 = Client) x)).
      + destruct H0. simp. eexists. split; first done.
        split; eauto using all_closed_acquire_progress.
        intro. simpl. destruct H2 as [[] ?]. simp.
      + (* If first column has only owner, use IH. *)
        edestruct IHorder; first apply all_closed_del; eauto using lock_relG'_del.
        { simp. apply lockrelG'_refcnt_0 in H. simp. }
        (* Then if IH returns same row as owner, prepend the first column. *)
        simp.
        admit.
  }
  {
    eapply lockrelG_open_progress in H; eauto.
    naive_solver.
  }
Admitted.

Lemma lockrelG_refcount refcnt lcks t l x :
  lockrelG refcnt lcks t ({[ l ]} ⋅ x) -> refcnt > 0.
Proof.
  intros [].
  rewrite Mlen_mult Mlen_singleton in lr_refcount0. lia.
Qed.

Lemma lockrel_Client n o t t' x' :
  lockrel n o t ({[(Client, Closed, t'):labelO']} ⋅ x') -> n > 0.
Proof.
  intros [].
  eapply mset_xsplit in lr_split. simp.
  eapply multiset_singleton_mult in H3 as []; simp.
  - destruct o; simp.
    + symmetry in H7. eapply multiset_empty_mult in H7. simp.
      symmetry in H8. eapply multiset_singleton_not_unit in H8. done.
    + rewrite H8 in H7.
      destruct lr_openedclosed; simp.
      * symmetry in H7. eapply multiset_empty_mult in H7. simp.
      * rewrite H10 in H7. symmetry in H7.
        eapply multiset_singleton_mult' in H7. simp.
  - rewrite H6 in H5.
    eapply mset_xsplit in H5. simp. rewrite H12.
    eapply multiset_singleton_mult in H13 as []; simp.
    + rewrite H16 Mlen_mult Mlen_singleton. lia.
    + rewrite H14 in H11. symmetry in H11.
      eapply multiset_singleton_mult' in H11. simp.
Qed.


Lemma lockrelG_refcounti ls i n refcnt lcks t xs x' t' :
  length ls = length xs ->
  xs !! i = Some (Client, Closed, t') ->
  ls !! i = Some n ->
  lockrelG refcnt lcks t ({[LockLabel (zip ls xs)]} ⋅ x') ->
  ∃ refcnt' o, lcks !! n = Some (S refcnt',o).
Proof.
  intros Hlen Hxs HH [].
  rewrite mset_forall_op mset_forall_singleton in order_subsequences.
  simp.
  rewrite fst_zip in H3; last lia.
  assert (n ∈ dom lcks).
  {
    rewrite -order_dom.
    eapply elem_of_list_to_set.
    eapply sublist_elem_of; eauto.
    eapply elem_of_list_lookup. eauto.
  }
  eapply elem_of_dom in H as [[] H].
  specialize (lr_lockrel0 n).
  rewrite H in lr_lockrel0.
  destruct (t !! n) eqn:E; simp.
  rewrite extract_op extract_singleton in lr_lockrel0.
  rewrite extract1_Some in lr_lockrel0; eauto.
  rewrite -assoc in lr_lockrel0.
  eapply lockrel_Client in lr_lockrel0. destruct n0; try lia.
  eauto.
Qed.

Lemma lockrel_Opened n o t t' x' lo :
  lockrel n o t ({[(lo, Opened, t'):labelO']} ⋅ x') -> o = None.
Proof.
  intros [].
  eapply mset_xsplit in lr_split. simp.
  eapply multiset_singleton_mult in H3 as []; simp.
  - destruct o; simp.
    symmetry in H7. eapply multiset_empty_mult in H7. simp.
    symmetry in H8. eapply multiset_singleton_not_unit in H8. done.
  - destruct o;eauto. simp. rewrite H6 in H5.
    eapply mset_xsplit in H5. simp.
    eapply multiset_singleton_mult in H11 as []; simp.
    + setoid_subst. rewrite left_id in H13. setoid_subst.
      specialize (lr_closed (lo, Opened, t') H10).
      assert ((lo, Opened, t') = (Client, Closed, t)); eauto || done.
    + setoid_subst. symmetry in H13. eapply multiset_singleton_mult' in H13. simp.
Qed.

Lemma lockrelG_refcounti_Opened ls i n refcnt a lcks t t' xs x' :
  length ls = length xs ->
  ls !! i = Some n ->
  xs !! i = Some (a, Opened, t') ->
  lockrelG refcnt lcks t ({[LockLabel (zip ls xs)]} ⋅ x') ->
  ∃ refcnt', lcks !! n = Some (refcnt',None).
Proof.
  intros Hlen Hxs HH [].
  rewrite mset_forall_op mset_forall_singleton in order_subsequences.
  simp.
  rewrite fst_zip in H3; last lia.
  assert (n ∈ dom lcks).
  {
    rewrite -order_dom.
    eapply elem_of_list_to_set.
    eapply sublist_elem_of; eauto.
    eapply elem_of_list_lookup. eauto.
  }
  eapply elem_of_dom in H as [[] H].
  specialize (lr_lockrel0 n).
  rewrite H in lr_lockrel0.
  destruct (t !! n) eqn:E; simp.
  rewrite extract_op extract_singleton in lr_lockrel0.
  rewrite extract1_Some in lr_lockrel0; eauto.
  rewrite -assoc in lr_lockrel0.
  eapply lockrel_Opened in lr_lockrel0. simp.
  eauto.
Qed.

Lemma lookup_zip {A B} (xs:list A) (ys:list B) i :
  zip xs ys !! i = match xs !! i, ys !! i with
                   | Some a, Some b => Some (a,b)
                   | _,_ => None
                   end.
Proof.
  revert xs ys. induction i; intros [] []; simpl; eauto.
  destruct (l!!i); done.
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
           constructor; last eapply NewGroup_step; try done;
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
  - (* Barrier *)
    clear IH1.
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
  - (* Lock group *)
    eapply exists_holds in Q as [t Q].
    eapply pure_sep_holds in Q as [Hrel Q].
    assert (HH := Hrel).
    eapply lockrelG_progress in HH.
    destruct HH as [HH|HH].
    {
      (* Delete the group *)
      simp. eapply Can_step_reachable.
      assert (ρ = {[
        i := LockG 0 ∅
      ]} ∪ delete i ρ) as ->.
      { eapply map_eq. smap. }
      eexists. econstructor; last econstructor.
      - intro. smap. destruct (_!!i0); try done.
      - solve_map_disjoint.
    }
    destruct HH as (ls&x'&Hinl&Hprog).
    assert (Hinl' := Hinl).
    eapply in_labels_out_edges in Hinl' as  [j Hj].
    destruct (classic (blocked ρ j i)) as [HB|HB]; last first.
    {
      (* Not blocked, so use IH to go there *)
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
      iDestr "Q1"; simp; eauto with iFrame.
    + assert (ρ = {[
        j := Thread (k (ForkLock (Val (LockGV j0 ls0)) (Val v)));
        j0 := LockG refcnt lcks
        ]} ∪ (delete j $ delete j0 ρ)) as ->.
      { apply map_eq. intro. smap. }
      destruct (cfg_fresh1 ρ) as (i & Hi).
      assert (j ≠ i). { intro. smap. }
      assert (i ≠ j0). { intro. smap. }
      do 2 econstructor; last econstructor; last done; last exact H0; eauto;
      intro; smap; destruct (ρ !! i0) eqn:EE; rewrite EE; eauto; smap.
    + eapply label_unique'; eauto. eapply holds_entails; eauto.
      iIntros "H". rewrite replacement; last done.
      iDestr "H". iDestruct "H" as "[H _]".
      iDestr "H". simp. iExists _. iFrame. iPureIntro. simp.
      eassert (ρ = {[
        j := Thread _;
        j0 := LockG _ _
        ]} ∪ (delete j $ delete j0 ρ)) as ->.
      { apply map_eq. intro. smap. }
      destruct Hprog as [Haprog Hwprog].
      rewrite acquire_progress_alt in Haprog.
      destruct (ls0 !! i) eqn:QQ; last first.
      {
        eapply lookup_ge_None in QQ.
        eapply lookup_lt_Some in H.
        rewrite H2 in H. lia.
      }
      edestruct (Haprog i) as [refcnt' [v HP]].
      {
        intros. destruct (ls0 !! j1) eqn:FF.
        - destruct (xs0 !! j1) eqn:EE.
          + destruct p. destruct l.
            assert (l0 = Closed) as ->; eauto.
            do 3 eexists. rewrite lookup_zip FF EE //.
          + eapply lookup_ge_None in EE.
            eapply lookup_lt_Some in H.
            assert (i < i); try lia.
            { eapply Nat.lt_le_trans; eauto.
              etrans; eauto. lia. }
        - eapply lookup_ge_None in FF.
          eapply lookup_lt_Some in H.
          rewrite H2 in H. lia.
      }
      {
        rewrite lookup_zip QQ H //.
      }
      do 2 econstructor; last econstructor; eauto;
      try intro; smap; try destruct (ρ !! i0) eqn:EE; rewrite ?EE //.
    + eapply label_unique'; eauto. eapply holds_entails; first done.
      iIntros "H". rewrite replacement; last done.
      iDestruct "H" as (tt) "[H1 _]".
      simpl. iDestr "H1". simp.
      iDestruct "H1" as "[H1 H2]".
      iDestr "H1". simp. iExists _.
      iFrame. iPureIntro. simp.
      destruct (ls0 !! i) eqn:EE; last first.
      { eapply lookup_lt_Some in H1.
        eapply lookup_ge_None in EE.
        rewrite -H2 in EE.
        assert (i < i). eapply Nat.lt_le_trans; eauto. lia. }
      rewrite Hinl in Hrel.
      eapply lockrelG_refcounti_Opened in Hrel; eauto. simp.
      eassert (ρ = {[
        j := Thread _;
        j0 := LockG _ _
        ]} ∪ (delete j $ delete j0 ρ)) as ->.
      { apply map_eq. intro. smap. }
      do 2 econstructor; last econstructor; eauto;
      intro; smap; destruct (ρ !! i0) eqn:FF; rewrite FF //.
    + eapply label_unique'; eauto. eapply holds_entails; first done.
      iIntros "H". rewrite replacement; last done.
      iDestruct "H" as (tt) "[H1 H2]".
      simpl. iDestr "H1". simp.
      iExists _. iFrame. iPureIntro. simp.
      eassert (ρ = {[
        j := Thread _;
        j0 := LockG _ _
        ]} ∪ (delete j $ delete j0 ρ)) as ->.
      { apply map_eq. intro. smap. }
      destruct Hprog as [Haprog Hwprog].
      rewrite wait_progress_alt in Hwprog.
      destruct (ls0 !! i) eqn:EE; last first.
      {
        eapply lookup_ge_None in EE.
        eapply lookup_lt_Some in H.
        rewrite H2 in H. lia.
      }
      edestruct (Hwprog i).
      { intros. rewrite lookup_zip in H0.
        destruct (ls0 !! j1) eqn:FF; simp.
        destruct (xs0 !! j1) eqn:FF'; simp; last first.
        { eapply lookup_ge_None in FF'.
          eapply lookup_lt_Some in FF.
          rewrite H2 in FF'. lia. }
        rewrite FF' in H0. simp.
        eapply H4 in FF'. simp. }
      { rewrite lookup_zip EE H //. }
      do 2 econstructor; last econstructor; eauto;
      intro; smap; destruct (ρ !! i0) eqn:FF; rewrite FF //.
    + assert (ρ = {[
        j := Thread (k (NewLock i (Val (LockGV j0 ls0))));
        j0 := LockG refcnt lcks
        ]} ∪ (delete j $ delete j0 ρ)) as ->.
      { apply map_eq. intro. smap. }
      destruct (map_fresh1 lcks) as (ii & Hii).
      do 2 econstructor; last econstructor; last done; eauto.
      * intro. smap. destruct (ρ!!i0) eqn:EE; rewrite EE; done.
      * intro. smap. destruct (ρ!!i0) eqn:EE; rewrite EE; done.
      * intro. smap.
    + eapply label_unique'; eauto. eapply holds_entails; first done.
      iIntros "H". rewrite replacement; last done.
      iDestruct "H" as (tt) "[H1 H2]".
      simpl. iDestr "H1". simp. iExists _. iFrame.
      iPureIntro. simp.
      eassert (ρ = {[
        j := Thread _;
        j0 := LockG _ _
        ]} ∪ (delete j $ delete j0 ρ)) as ->.
      { apply map_eq. intro. smap. }
      destruct (ls0 !! i) eqn:EE; last first.
      { eapply lookup_lt_Some in H3.
        eapply lookup_ge_None in EE.
        rewrite -H2 in EE.
        assert (i < i). eapply Nat.lt_le_trans; eauto. lia. }
      rewrite Hinl in Hrel.
      eapply lockrelG_refcounti in Hrel; eauto. simp.
      do 2 econstructor; last econstructor; eauto;
      intro; smap; destruct (ρ !! i0) eqn:FF; rewrite FF //.
    + eapply label_unique'; eauto. eapply holds_entails; first done.
      iIntros "H". rewrite replacement; last done.
      iDestruct "H" as (tt) "[H1 H2]".
      simpl. iDestr "H1". simp. iExists _. iFrame. iPureIntro. simp.
      destruct ls0; simp.
      rewrite Hinl in Hrel.
      eapply lockrelG_refcount in Hrel.
      eassert (ρ = {[
        j := Thread _;
        j0 := LockG _ _
        ]} ∪ (delete j $ delete j0 ρ)) as ->.
      { apply map_eq. intro. smap. }
      destruct refcnt; try lia.
      do 2 econstructor; last econstructor; eauto;
      intro; smap; destruct (ρ !! i) eqn:EE; rewrite EE //.
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