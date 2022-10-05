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

(*
labelO : labels for lock groups = list (nat, cap, t)
labelO' : labels for individual locks : (cap, t)

extract : nat -> multiset labelO -> multiset labelO'
*)

(*
Physical state of the lock: (refcnt : nat) (xs : locksT)
Incoming labels: (x : multiset labelO)
Consistent with each other: lock_relMG (refcnt : nat) (xs : locksT) (x : multiset labelO)

Physical state:
  refcnt = 4
  xs = {#a ↦ (2,Some(v)), #b ↦ (1,None), #c ↦ (2,None)}

Physical references:
  <9| >
  <9|#a,#c>
  <9|#a,#b>
  <9|#c>

Incoming labels:
  x = {
    [                                                        ],
    [(#a, (1,0), string),                    (#c, (1,1), nat)],
    [(#a, (0,0), string),  (#b, (1,1), nat)                  ],
    [                                        (#c, (0,0), nat)]
  }

Invariant state:
  order = [#a,#b,#c]

Invariant properties:
  order is permutation of dom(xs)
  the first projections of each row is a subsequence of order
  for each column, the single lock invariant holds
  the refcount of the lock group is equal to the height of the matrix

Progress algorithm:
1. If all locks are closed, pick the one with highest client reference.
2. If some lock is opened, pick the one with highest opened lock.

Progress lemma:
Guarantees existence of somebody (called l), such that either:
1. l has a client reference and all higher locks have refcount 0
2. l has an opened reference, and all higher locks are closed
*)

Definition labelO':ofe := leibnizO (lockcap*type).

Record lock_relM (refcnt : nat) (o : option val) (t : type) (x : multiset labelO') : Prop := {
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

Global Instance lock_relM_Proper refcnt o t : Proper ((≡) ==> (≡)) (lock_relM refcnt o t).
Proof.
  intros ???.
  split; intros []; econstructor; eauto.
  - rewrite -H //.
  - rewrite H //.
Qed.

Definition extract (i : nat) (x : multiset labelO) : multiset labelO'. Admitted.

Global Instance extract_Proper i :
  Proper ((≡) ==> (≡)) (extract i).
Proof.
Admitted.

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

Record lock_relMG (refcnt : nat) (xs : locksbundle) (ts : gmap nat type) (x : multiset labelO) : Prop := {
  order : list nat;
  order_NoDup : NoDup order;
  order_dom : list_to_set order = dom xs;
  order_subsequences : mset_forall (λ l, ∃ xs, l = LockLabel xs ∧ sublist (xs.*1) order) x;
  lr_lock_relM : ∀ i, match xs !! i, ts !! i with
    | Some (refcounti, o), Some t => lock_relM refcounti o t (extract i x)
    | None, None => True
    | _, _ => False
    end;
  lr_refcount : Mlen x = refcnt;
}.

Global Instance mset_forall_Proper {A:ofe} : Proper (((≡) ==> iff) ==> (≡) ==> (≡)) (@mset_forall A).
Proof.
  intros ??????.
  split.
  { intros ????. eapply H; eauto. eapply H1. rewrite H0. done. }
  { intros ????. eapply H; eauto. eapply H1. rewrite -H0. done. }
Qed.

Global Instance lock_relMG_Proper refcnt xs :
  Proper ((≡) ==> (≡) ==> (≡)) (lock_relMG refcnt xs).
Proof.
  intros ??????.
  split.
  {
    intros []. ofe_subst. econstructor; first done; eauto;
    try rewrite -H0; eauto.
    intros. specialize (lr_lock_relM0 i).
    destruct (xs!!i); eauto. destruct p. destruct (y!!i); eauto.
    eapply lock_relM_Proper; last done. rewrite H0 //.
  }
  {
    intros []. ofe_subst. econstructor; first done; eauto;
    try rewrite H0; eauto.
    intros. specialize (lr_lock_relM0 i).
    destruct (xs!!i); eauto. destruct p. destruct (y!!i); eauto.
    eapply lock_relM_Proper; last done. rewrite H0 //.
  }
Qed.

Lemma lock_relM_newlock v t :
  lock_relM 0 (Some v) t {[ (Owner, Closed, t) : labelO' ]}.
Proof.
  eexists Closed ε ε; eauto.
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

Lemma lock_relM_same_type refcnt o t t' l x :
  lock_relM refcnt o t ({[ (l, t'):labelO' ]} ⋅ x) -> t' = t.
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

Lemma lock_relM_drop refcnt o t x :
  lock_relM (S refcnt) o t ({[ (Client, Closed, t):labelO' ]} ⋅ x) ->
  lock_relM refcnt o t x.
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
Lemma lock_relM_split' l l2 l3 refcnt o t x :
  ((l2.1 = Owner -> l3.1 = Owner) ∧
  (l2.1 = l3.1 -> l2.2 = Closed -> l3.2 = Closed)) ->
  lockcap_split l l2 l3 ->
  lock_relM refcnt o t ({[(l,t):labelO']} ⋅ x) ->
  lock_relM (S refcnt) o t ({[(l3,t):labelO']} ⋅ {[(l2,t):labelO']} ⋅ x).
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

Lemma lock_relM_split l l2 l3 refcnt o t x :
  lockcap_split l l2 l3 ->
  lock_relM refcnt o t ({[ (l, t):labelO']} ⋅ x) ->
  lock_relM (S refcnt) o t ({[ (l3, t):labelO']} ⋅ {[ (l2, t):labelO']} ⋅ x).
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
  lock_relM refcnt (Some v) t ({[ (lo, Closed, t):labelO']} ⋅ x) <->
  lock_relM refcnt None t ({[ (lo, Opened, t):labelO']} ⋅ x).
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

Lemma lock_relM_only_owner v t x :
  lock_relM 0 (Some v) t ({[ (Owner, Closed, t):labelO']} ⋅ x) -> x = ε.
Proof.
  intros [].
  destruct lr_openedclosed. subst.
  rewrite Mlen_unit in lr_refcount0.
  assert (Mlen x_closed = 0) as ->%Mlen_zero_inv by lia.
  rewrite !right_id in lr_split.
  eapply multiset_singleton_mult' in lr_split as [].
  done.
Qed.

Lemma lock_relM_progress refcnt o t x :
  lock_relM refcnt o t x -> ∃ l x',
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
      ⌜⌜ lock_relMG refcnt xs ts in_l ⌝⌝ ∗
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
Admitted.

Definition extract1 (jj : nat) (ls : list (nat * (lockcap * type))) : multiset labelO'. Admitted.

Lemma extract_singleton jj a :
  extract jj {[ a ]} = match a with
    | LockLabel xs => extract1 jj xs
    | _ => ε
    end.
Proof.
Admitted.

Lemma extract_Some ii jj xs1 a b t2 ls :
  ls !! ii = Some jj ->
  xs1 !! ii = Some (a, b, t2) -> ∃ x',
  extract1 jj (zip ls xs1) ≡ {[ (a,b,t2):labelO' ]} ⋅ x'.
Proof.
Admitted.

Lemma lock_relMG_types_same refcnt xs ts ls xs1 x ii jj a b t1 t2 :
  lock_relMG refcnt xs ts ({[LockLabel (zip ls xs1)]} ⋅ x) ->
  ls !! ii = Some jj ->
  ts !! jj = Some t1 ->
  xs1 !! ii = Some (a, b, t2) ->
  t1 = t2.
Proof.
  intros [] ???.
  specialize (lr_lock_relM0 jj). rewrite H0 in lr_lock_relM0.
  destruct (xs !! jj); last done. destruct p.
  rewrite extract_op in lr_lock_relM0.
  rewrite extract_singleton in lr_lock_relM0.
  edestruct extract_Some; eauto.
  rewrite H2 in lr_lock_relM0.
  rewrite -assoc in lr_lock_relM0.
  eapply lock_relM_same_type in lr_lock_relM0.
  subst. done.
Qed.

Lemma extract1_Some ii i l ls xs :
  ls !! ii = Some i ->
  xs !! ii = Some l ->
  extract1 i (zip ls xs) = {[ l:labelO' ]} ⋅ extract1 i (zip (delete ii ls) (delete ii xs)).
Proof.
Admitted.

Lemma extract1_ne_Some ii i ls xs :
  ls !! ii ≠ Some i ->
  extract1 i (zip ls xs) = extract1 i (zip (delete ii ls) (delete ii xs)).
Proof.
Admitted.


Lemma list_delete_insert_delete {A} i (a:A) (xs:list A) :
  delete i (<[ i := a ]> xs) = delete i xs.
Proof.
  revert i; induction xs; simpl; first done.
  intros []; simpl; first done.
  f_equal. done.
Qed.

Lemma lock_relMG_Release ls ii jj xs refcntii xs1 a t' x refcnt ts v :
  length ls = length xs1 ->
  ls !! ii = Some jj ->
  xs !! jj = Some (refcntii, None) ->
  xs1 !! ii = Some (a, Opened, t') ->
  lock_relMG refcnt xs ts ({[LockLabel (zip ls xs1)]} ⋅ x) ->
  lock_relMG refcnt (<[jj:=(refcntii, Some v)]> xs) ts
    ({[LockLabel (zip ls (<[ii:=(a, Closed, t')]> xs1))]} ⋅ x).
Proof.
  intros ???? [].
  econstructor; eauto.
  - rewrite dom_insert_lookup_L //.
  - rewrite mset_forall_op. rewrite mset_forall_op in order_subsequences.
    destruct order_subsequences as []. split; eauto.
    rewrite mset_forall_singleton. rewrite mset_forall_singleton in H3.
    simp. eexists. split; first done.
    rewrite fst_zip in H7; last lia.
    rewrite fst_zip; first done.
    rewrite insert_length. lia.
  - intro. specialize (lr_lock_relM0 i). smap.
    + rewrite H1 in lr_lock_relM0.
      destruct (ts !! i); eauto.
      revert lr_lock_relM0.
      rewrite !extract_op !extract_singleton.
      erewrite extract1_Some; eauto.
      intros lr.
      erewrite extract1_Some; eauto; last first.
      { rewrite list_lookup_insert; first done. by eapply lookup_lt_Some. }
      rewrite list_delete_insert_delete.
      rewrite -assoc. rewrite -assoc in lr.
      assert (t'=t) as -> by eauto using lock_relM_same_type.
      eapply lock_relM_open_close. done.
    + destruct (xs !! i) eqn:E; rewrite E; last first.
      { destruct (ts !! i); done. }
      destruct p. destruct (ts !! i); eauto.
      revert lr_lock_relM0.
      rewrite !extract_op !extract_singleton.
      assert (ls !! ii ≠ Some i). { congruence. }
      erewrite extract1_ne_Some; last done. intros lr.
      erewrite extract1_ne_Some; last done.
      rewrite list_delete_insert_delete //.
Qed.

Lemma lock_relMG_Acquire ls ii jj xs refcntii v t' x xs1 a ts refcnt :
  length ls = length xs1 ->
  ls !! ii = Some jj ->
  xs !! jj = Some (refcntii, Some v) ->
  xs1 !! ii = Some (a, Closed, t') ->
  lock_relMG refcnt xs ts ({[LockLabel (zip ls xs1)]} ⋅ x) ->
  lock_relMG refcnt (<[jj:=(refcntii, None)]> xs) ts
    ({[LockLabel (zip ls (<[ii:=(a, Opened, t')]> xs1))]} ⋅ x).
Proof.
  intros ???? [].
  econstructor; eauto.
  - rewrite dom_insert_lookup_L //.
  - rewrite mset_forall_op. rewrite mset_forall_op in order_subsequences.
    destruct order_subsequences as []. split; eauto.
    rewrite mset_forall_singleton. rewrite mset_forall_singleton in H3.
    simp. eexists. split; first done.
    rewrite fst_zip in H7; last lia.
    rewrite fst_zip; first done.
    rewrite insert_length. lia.
  - intro. specialize (lr_lock_relM0 i). smap.
    + rewrite H1 in lr_lock_relM0.
      destruct (ts !! i); eauto.
      revert lr_lock_relM0.
      rewrite !extract_op !extract_singleton.
      erewrite extract1_Some; eauto.
      intros lr.
      erewrite extract1_Some; eauto; last first.
      { rewrite list_lookup_insert; first done. by eapply lookup_lt_Some. }
      Search list delete insert.
      rewrite list_delete_insert_delete.
      rewrite -assoc. rewrite -assoc in lr.
      assert (t'=t) as -> by eauto using lock_relM_same_type.
      eapply lock_relM_open_close. done.
    + destruct (xs !! i) eqn:E; rewrite E; last first.
      { destruct (ts !! i); done. }
      destruct p. destruct (ts !! i); eauto.
      revert lr_lock_relM0.
      rewrite !extract_op !extract_singleton.
      assert (ls !! ii ≠ Some i). { congruence. }
      erewrite extract1_ne_Some; last done. intros lr.
      erewrite extract1_ne_Some; last done.
      rewrite list_delete_insert_delete //.
Qed.

Lemma lock_relMG_Wait ls ii jj xs v xs1 t' ts x refcnt :
  length ls = length xs1 ->
  ls !! ii = Some jj ->
  xs !! jj = Some (0, Some v) ->
  xs1 !! ii = Some (Owner, Closed, t') ->
  ts !! jj = Some t' ->
  lock_relMG refcnt xs ts ({[LockLabel (zip ls xs1)]} ⋅ x) ->
  lock_relMG refcnt (delete jj xs) (delete jj ts)
    ({[LockLabel (zip (delete ii ls) (delete ii xs1))]} ⋅ x).
Proof.
  intros HH????[].
  eexists (filter (λ x, x ≠ jj) order).
  - eapply NoDup_filter; eauto.
  - rewrite dom_delete_L.
    eapply set_eq. intro.
    rewrite elem_of_list_to_set elem_of_list_filter.
    set_solver.
  - revert order_subsequences.
    rewrite !mset_forall_op !mset_forall_singleton. simp.
    rewrite fst_zip in H7; last lia.
    split.
    + eexists. split; eauto.
      rewrite fst_zip; last admit.
      admit.
    + pose proof (lr_lock_relM0 jj) as Q.
      rewrite H0 H2 in Q.
      admit.
  - intros i. specialize (lr_lock_relM0 i).
    smap. destruct (xs !! i) eqn:E; rewrite E; eauto.
    destruct p. destruct (ts !! i); eauto.
    revert lr_lock_relM0. rewrite !extract_op !extract_singleton.
    intros lr.
    admit.
  - revert lr_refcount0. rewrite !Mlen_mult !Mlen_singleton. lia.
Admitted.

Lemma extract1_empty i : extract1 i [] = ε.
Proof.
Admitted.

Lemma lock_relMG_DropGroup refcnt xs ts x :
  lock_relMG (S refcnt) xs ts ({[LockLabel []]} ⋅ x) ->
  lock_relMG refcnt xs ts x.
Proof.
  intros [].
  exists order; eauto.
  - apply mset_forall_op in order_subsequences as []. done.
  - intros i. specialize (lr_lock_relM0 i).
    destruct (xs !! i); eauto. destruct p.
    destruct (ts !! i); eauto.
    rewrite extract_op extract_singleton extract1_empty left_id in lr_lock_relM0.
    done.
Qed.

Lemma lock_relMG_NewGroup : lock_relMG 1 ∅ ∅ {[LockLabel []]}.
Proof.
  exists [].
  - by eapply NoDup_nil.
  - rewrite list_to_set_nil dom_empty_L //.
  - rewrite mset_forall_singleton. exists []. done.
  - intro. smap.
  - done.
Qed.

Lemma lock_relMG_empty_inv x : lock_relMG 0 ∅ ∅ x -> x = ε.
Proof.
  intros []. by eapply Mlen_zero_inv.
Qed.

Lemma list_to_set_insert2 ii jj (xs : list nat) :
  (list_to_set (insert2 ii jj xs) : gset nat) = {[jj]} ∪ list_to_set xs.
Proof.
  revert ii; induction xs; intros []; simpl; eauto.
  rewrite IHxs. set_solver.
Qed.

Lemma lock_relMG_NewLock refcnt xs ts ls xs1 x t' ii jj :
  length ls = length xs1 ->
  xs !! jj = None ->
  lock_relMG refcnt xs ts ({[LockLabel (zip ls xs1)]} ⋅ x) ->
  lock_relMG refcnt (<[jj:=(0, None)]> xs) (<[jj:=t']> ts)
    ({[LockLabel (zip (insert2 ii jj ls) (insert2 ii (Owner, Closed, t') xs1))]} ⋅ x).
Proof.
  intros HH H [].
  exists (insert2 ii jj order).
  - eapply insert2_NoDup_2; eauto.
    assert (jj ∉ dom xs) as Q. { eapply not_elem_of_dom. done. }
    rewrite -order_dom in Q.
    eapply not_elem_of_list_to_set in Q.
    done.
  - rewrite dom_insert_L -order_dom list_to_set_insert2 //.
  - revert order_subsequences. rewrite !mset_forall_op !mset_forall_singleton.
    intros os. simp.
    rewrite fst_zip in H4; last admit.
    split.
    + eexists. split; first done.
      rewrite fst_zip. 2: { rewrite !insert2_length. lia. }
      admit.
    + admit.
  - intros i. specialize (lr_lock_relM0 i).
    smap.
    + admit.
    + destruct (xs !! i) eqn:E; rewrite E; eauto.
      destruct p. destruct (ts !! i); eauto.
      revert lr_lock_relM0. rewrite !extract_op !extract_singleton.
      intros lr.
      admit.
  - revert lr_refcount0. rewrite !Mlen_mult !Mlen_singleton. lia.
Admitted.

Lemma lock_relMG_same_dom_empty refcnt xs ts x i :
  lock_relMG refcnt xs ts x ->
  xs !! i = None <-> ts !! i = None.
Proof.
  intros [].
  specialize (lr_lock_relM0 i).
  destruct (xs !! i),(ts!!i); try done.
  destruct p;done.
Qed.

Lemma lock_relMG_DropLock refcnt xs ts ls xs1 x t' ii jj refcntii o :
  length ls = length xs1 ->
  ls !! ii = Some jj ->
  xs !! jj = Some (S refcntii, o) ->
  xs1 !! ii = Some (Client, Closed, t') ->
  lock_relMG refcnt xs ts ({[LockLabel (zip ls xs1)]} ⋅ x) ->
  lock_relMG refcnt (<[jj:=(refcntii, o)]> xs) ts
    ({[LockLabel (zip (delete ii ls) (delete ii xs1))]} ⋅ x).
Proof.
  intros ????[].
  econstructor; eauto.
  - rewrite dom_insert_lookup_L //.
  - rewrite mset_forall_op. rewrite mset_forall_op in order_subsequences.
    destruct order_subsequences as []. split; eauto.
    rewrite mset_forall_singleton. rewrite mset_forall_singleton in H3.
    simp. eexists. split; first done.
    rewrite fst_zip in H7; last lia.
    rewrite fst_zip.
    + etrans; last done. apply sublist_delete.
    + rewrite !length_delete; eauto. lia.
  - intro. specialize (lr_lock_relM0 i). smap.
    + rewrite H1 in lr_lock_relM0.
      destruct (ts !! i); eauto.
      revert lr_lock_relM0.
      rewrite !extract_op !extract_singleton.
      erewrite extract1_Some; eauto.
      intros lr.
      rewrite -assoc in lr.
      assert (t'=t) as -> by eauto using lock_relM_same_type.
      eapply lock_relM_drop in lr. done.
    + destruct (xs !! i) eqn:E; rewrite E; last first.
      { destruct (ts !! i); done. }
      destruct p. destruct (ts !! i); eauto.
      revert lr_lock_relM0.
      rewrite !extract_op !extract_singleton.
      assert (ls !! ii ≠ Some i). { congruence. }
      erewrite extract1_ne_Some; last done. done.
Qed.

Lemma lock_relMG_ForkLock xs1 xs2 xs3 ls x refcnt xs ts :
  length ls = length xs1 ->
  lockcaps_split xs1 xs2 xs3 ->
  lock_relMG refcnt xs ts ({[LockLabel (zip ls xs1)]} ⋅ x) ->
  lock_relMG (S refcnt) xs ts
    ({[LockLabel (zip ls xs3)]} ⋅ {[LockLabel (zip ls xs2)]} ⋅ x).
Proof.
  intros HH H [].
  exists order; eauto.
  - revert order_subsequences. rewrite !mset_forall_op !mset_forall_singleton.
    intros []. simp. rewrite fst_zip in H4; last admit. repeat split; eauto.
    + eexists. split; first done.
      rewrite fst_zip; last admit. done.
    + eexists. split; first done.
      rewrite fst_zip; last admit. done.
  - intros i. specialize (lr_lock_relM0 i).
    destruct (xs !! i); eauto. destruct p.
    destruct (ts !! i); eauto.
    revert lr_lock_relM0.
    rewrite !extract_op !extract_singleton. intro.
    unfold lockcaps_split in *.
    Search lock_relM.
    admit.
  - revert lr_refcount0. rewrite !Mlen_mult !Mlen_singleton. intro. lia.
Admitted.

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
        iPureIntro. eapply lock_relMG_NewGroup.
  - (* DeleteGroup *)
    eapply inv_impl; last done.
    iIntros (m x) "H". unfold linv. smap; iDestr "H";
    assert (ρf !! m = None) as -> by solve_map_disjoint; eauto.
    iDestruct (big_sepM2_empty_r with "H") as %->.
    rewrite big_sepM2_empty. iPureIntro.
    apply lock_relMG_empty_inv in H. subst. done.
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
        iPureIntro. eapply lock_relMG_DropGroup; eauto.
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
             eapply lock_relMG_NewLock; eauto.
          ** rewrite big_sepM2_insert; simpl; eauto.
             eapply lock_relMG_same_dom_empty; eauto.
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
          ** iPureIntro. eapply lock_relMG_DropLock; eauto.
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
        assert (x2 = t') as -> by eauto using lock_relMG_types_same.
        iDestruct "H" as "[Hv H]".
        iSplitL "Q Hv".
        * iIntros "H'". iSplit; first done.
          iApply "Q". simpl. iExists _,_. iSplit; first done.
          iSplitL "H'"; iFrame.
          iExists _. iFrame.
          iPureIntro. split; first done.
          rewrite insert_length //.
        * iExists ts. iSplit.
          { iPureIntro. eapply lock_relMG_Acquire; eauto. }
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
        { iPureIntro. eapply lock_relMG_Release; eauto. }
        rewrite big_sepM2_delete_l; last done. simpl.
        iApply big_sepM2_delete_l; first smap.
        iDestr "H". iDestruct "H" as "[_ H]".
        iExists _. iSplit; first done. simpl.
        assert (x2 = t') as -> by eauto using lock_relMG_types_same.
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
      assert (x2 = t') as -> by eauto using lock_relMG_types_same.
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
        iPureIntro. eapply lock_relMG_Wait; eauto.
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
      (* assert (t'0 = t) as -> by eauto using lock_relM_same_type. *)
      (* iExists (LockLabel l3 t),(LockLabel l2 t). *)
      iExists (LockLabel (zip ls xs3)),(LockLabel (zip ls xs2)).
      edestruct lockcaps_split_length as []; first done.
      iSplitL "Q".
      {
        iIntros "H". iSplit; first done. iApply "Q". simpl.
        iExists _. iFrame. iPureIntro. split; first done. lia.
      }
      iSplitL "H".
      * iExists ts. iFrame. iPureIntro. eapply lock_relMG_ForkLock; eauto.
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
Admitted.
    (*
    Progress lemma:
    Guarantees existence of somebody (called l), such that either:
    1. l has an opened reference, and all lower locks are really closed
    2. all locks are really closed, and
       l has a client reference and all lower locks have refcount 0
    3. all locks are owners and all are closed
    4. lockgroup is empty but its refcount is nonzero
    5. lockgroup is empty and its refcount is zero
    *)
    (* assert (∀ refcnt lckx t x, lock_relMG refcnt lckx t x ->
      ∃ x', x ≡ {[ }] ⋅ x' ∧ ) as lock_relMG_progress.
    eapply lock_relMG_progress in Hrel as (lc & x' & Hinl & Hlc). clear lock_relMG_progress.
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
Qed. *)

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