From stdpp Require Export gmap.
From iris.bi Require Export interface.
From iris.algebra Require Import excl gmap auth.
From iris.proofmode Require Export tactics.
Require Export diris.langdef.
Require Export diris.logic.bi.
Require Export diris.util.
Require Export diris.logic.bupd.
Ltac inv H := inversion H; clear H; simpl in *; simplify_eq.

Lemma other_neq ep :
  ep ≠ other ep.
Proof.
  by destruct ep,b.
Qed.

Inductive owner :=
  | Thread : nat -> owner
  | Chan : chan -> owner.

Instance owner_eqdecision : EqDecision owner.
Proof.
  intros [n|n] [m|m]; unfold Decision; destruct (decide (n = m));
  subst; eauto; right; intro; simplify_eq.
Qed.
Instance owner_countable : Countable owner.
Proof.
  refine (inj_countable' (λ l, match l with
  | Thread n => inl n
  | Chan n => inr n
  end) (λ l, match l with
  | inl n => Thread n
  | inr n => Chan n
  end) _); by intros [].
Qed.

Canonical Structure ownerO := leibnizO owner.
Canonical Structure chan_typeO := leibnizO chan_type.

Notation heapT := (gmap endpoint chan_type).
Notation heapTO := (gmap endpoint (chan_type * owner)).
Notation heapT_UR := (gmapUR endpoint (exclR chan_typeO)).
Notation heapTO_UR := (gmapUR endpoint (exclR (prodO chan_typeO ownerO))).

Notation oProp := (uPred heapT_UR).
Notation iProp := (uPred (authUR heapTO_UR)).

Notation "⌜⌜ p ⌝⌝" := (<affine> ⌜ p ⌝)%I : bi_scope.

Definition attach_owner (o : owner) (h : heapT) : heapTO := (λ t, (t,o)) <$> h.

Section attach_owner.
  Lemma attach_owner_empty o : attach_owner o ∅ = ∅.
  Proof. rewrite /attach_owner fmap_empty //. Qed.
  Lemma attach_owner_union o m1 m2 :
    attach_owner o (m1 ∪ m2) = attach_owner o m1 ∪ attach_owner o m2.
  Proof. rewrite /attach_owner map_fmap_union //. Qed.
  Lemma fmap_map_disjoint `{Countable K} {V1 V2} (f : V1 -> V2) (m1 m2 : gmap K V1) :
    m1 ##ₘ m2 <-> f <$> m1 ##ₘ f <$> m2.
  Proof.
    split.
    - intros HH.
      intros x. rewrite !lookup_fmap.
      specialize (HH x).
      destruct (m1 !! x); destruct (m2 !! x); try done.
    - intros HH.
      intros x. specialize (HH x).
      rewrite !lookup_fmap in HH.
      destruct (m1 !! x); destruct (m2 !! x); try done.
  Qed.
  Lemma attach_owner_disj o m1 m2 :
    m1 ##ₘ m2 <-> attach_owner o m1 ##ₘ attach_owner o m2.
  Proof. apply fmap_map_disjoint. Qed.
End attach_owner.

Definition map_Excl `{Countable K} {V} (m : gmap K V) : gmap K (excl V) := Excl <$> m.

Section map_Excl.
  Context `{Countable K} {V : ofeT} `{!LeibnizEquiv V}.
  Implicit Type m : gmap K V.
  Lemma map_Excl_valid m : ✓ (map_Excl m).
  Proof. intros i. rewrite /map_Excl lookup_fmap. destruct (m !! i); done. Qed.
  Lemma map_Excl_empty : map_Excl ∅ = (ε : gmap K (excl V)).
  Proof. rewrite /map_Excl fmap_empty. done. Qed.
  Lemma map_Excl_insert m k v :
    map_Excl (<[ k := v ]> m) = <[ k := Excl v ]> $ map_Excl m.
  Proof.
    rewrite /map_Excl fmap_insert //.
  Qed.
  Lemma map_Excl_insert_op m k v :
    m !! k = None ->
    map_Excl (<[ k := v ]> m) = {[ k := Excl v ]} ⋅ map_Excl m.
  Proof.
    intros HH.
    rewrite /map_Excl fmap_insert insert_singleton_op //
            lookup_fmap HH //.
  Qed.
  Lemma map_Excl_union m1 m2 :
    m1 ##ₘ m2 -> map_Excl (m1 ∪ m2) = map_Excl m1 ⋅ map_Excl m2.
  Proof.
    induction m1 using map_ind; intros; decompose_map_disjoint.
    - by rewrite map_Excl_empty !left_id_L.
    - assert ((m ∪ m2) !! i = None).
      { rewrite lookup_union H0 H1 //. }
      rewrite -insert_union_l !map_Excl_insert_op // IHm1 // assoc_L //.
  Qed.
  Lemma map_Excl_singleton_op_inv m me k x :
    map_Excl m = {[ k := Excl x ]} ⋅ me ->
    ∃ m', m = <[ k := x ]> m' ∧ me = map_Excl m' ∧ m' !! k = None.
  Proof.
    rewrite /map_Excl. intros HH.
    exists (delete k m).
    assert (m !! k = Some x).
    { rewrite ->map_eq_iff in HH.
      specialize (HH k).
      revert HH. rewrite lookup_fmap lookup_op lookup_singleton.
      case: (m!!k); case:(me!!k); simpl; intros; inversion HH. done. }
    rewrite !map_eq_iff.
    rewrite-> map_eq_iff in HH.
    split_and!.
    - intros i.
      destruct (decide (k = i)); subst.
      + rewrite lookup_insert //.
      + rewrite lookup_insert_ne // lookup_delete_ne //.
    - intros i.
      specialize (HH i).
      destruct (decide (k = i)); subst.
      + rewrite lookup_fmap lookup_delete.
        revert HH. rewrite !lookup_fmap lookup_op lookup_singleton H0 /=.
        case: (me !! i); eauto.
        intros a HH. inversion HH.
      + rewrite lookup_fmap lookup_delete_ne //.
        revert HH. rewrite lookup_fmap lookup_op lookup_singleton_ne //.
        case: (me !! i); simpl; intros; rewrite HH //.
    - rewrite lookup_delete //.
  Qed.
  Lemma map_Excl_union_inv m me1 me2 :
    map_Excl m = me1 ⋅ me2 ->
    ∃ m1 m2, m = m1 ∪ m2 ∧ me1 = map_Excl m1 ∧ me2 = map_Excl m2 ∧ m1 ##ₘ m2.
  Proof.
    revert m. induction me1 as [|k xe me1 Hx IH] using map_ind; intros m.
    - rewrite left_id_L. intros <-.
      exists ∅,m.
      rewrite left_id_L map_Excl_empty. split_and!; solve_map_disjoint.
    - rewrite insert_singleton_op // -assoc_L.
      destruct xe as [x|].
      + intros (m' & -> & ? & ?)%map_Excl_singleton_op_inv.
        destruct (IH m') as (m1 & m2 & -> & -> & -> & ?); first done.
        exists (<[ k := x]> m1),m2.
        apply lookup_union_None in H1 as [].
        repeat split.
        * by rewrite insert_union_l.
        * rewrite map_Excl_insert_op //.
        * by apply map_disjoint_insert_l.
      + intros Hm. assert (✓ (ExclBot : excl V)) as [].
        eapply (singleton_valid k), (cmra_valid_op_l _ (me1 ⋅ me2)).
        rewrite -Hm. apply map_Excl_valid.
  Qed.
  Lemma map_Excl_disjoint m1 m2 :
    m1 ##ₘ m2 <-> map_Excl m1 ##ₘ map_Excl m2.
  Proof. apply fmap_map_disjoint. Qed.
End map_Excl.

Definition owned (o : owner) (P : oProp) : iProp :=
  ∃ (h : heapT),
    ⌜⌜ uPred_holds P (map_Excl h) ⌝⌝ ∗
    uPred_ownM (◯ (map_Excl $ attach_owner o h)).

Lemma owned_mono (P Q : oProp) o :
  (P ⊢ Q) → owned o P ⊢ owned o Q.
Proof.
  iIntros (H) "H". unfold owned.
  iDestruct "H" as (h H1) "H".
  iExists h. iFrame. iPureIntro.
  apply H; last done.
  intros i. rewrite lookup_fmap. case: (h !! i); done.
Qed.

Instance owned_proper_vdash o : Proper ((⊢) ==> (⊢)) (owned o).
Proof. intros ???. by apply owned_mono. Qed.
Instance owned_proper_flip_vdash o : Proper (flip (⊢) ==> flip (⊢)) (owned o).
Proof. intros ???. simpl in *. by apply owned_mono. Qed.
Instance: Params (owned) 1 := {}.
Instance owned_proper_equiv o : Proper ((≡) ==> (≡)) (owned o).
Proof.
  intros P1 P2 [HP1 HP2]%bi.equiv_spec; apply bi.equiv_spec. split.
    - by rewrite HP1.
    - by rewrite HP2.
Qed.

(*
Talk to Robbert about these Coq issues,
and being stuck on stupid stuff => frustration => low motivation
*)
Section uPred_lemmas.
  Context {A : ucmraT}.
  Implicit Types P Q : uPred A.
  Arguments uPred_holds {_} !_/.
  Lemma owned_emp_helper (x : A) : ✓ x -> (uPred_ownM x ⊢ emp) -> x ≡ ε.
  Proof.
    uPred.unseal. intros ? [H]. apply H; simpl; done.
  Qed.

  Lemma uPred_emp_holds x :
    (emp%I : uPred A) x <-> x ≡ ε.
  Proof. by uPred.unseal. Qed.
  Lemma uPred_emp_holds_L `{!LeibnizEquiv A} x :
    (emp%I : uPred A) x <-> x = ε.
  Proof. unfold_leibniz. apply uPred_emp_holds. Qed.

  Lemma uPred_sep_holds P Q x :
    (P ∗ Q)%I x <-> ∃ x1 x2, x ≡ x1 ⋅ x2 ∧ P x1 ∧ Q x2.
  Proof. by uPred.unseal. Qed.
  Lemma uPred_sep_holds_L `{!LeibnizEquiv A} P Q x :
    (P ∗ Q)%I x <-> ∃ x1 x2, x = x1 ⋅ x2 ∧ P x1 ∧ Q x2.
  Proof. unfold_leibniz. apply uPred_sep_holds. Qed.

  Lemma uPred_and_holds P Q x :
    (P ∧ Q)%I x <-> P x ∧ Q x.
  Proof. by uPred.unseal. Qed.
  Lemma uPred_pure_holds φ x :
    (⌜ φ ⌝ : uPred A)%I x <-> φ.
  Proof. by uPred.unseal. Qed.
  Lemma uPred_exists_holds {B} (Φ : B -> uPred A) x :
    (∃ b, Φ b)%I x <-> ∃ b, Φ b x.
  Proof. by uPred.unseal. Qed.
  Lemma uPred_affinely_pure_holds φ x :
    (⌜⌜ φ ⌝⌝ : uPred A)%I x <-> x ≡ ε ∧ φ.
  Proof. rewrite /bi_affinely uPred_and_holds uPred_pure_holds uPred_emp_holds. done. Qed.
  Lemma uPred_affinely_pure_holds_L `{!LeibnizEquiv A} φ x :
    (⌜⌜ φ ⌝⌝ : uPred A)%I x <-> x = ε ∧ φ.
  Proof. unfold_leibniz. apply uPred_affinely_pure_holds. Qed.
End uPred_lemmas.

Lemma owned_pure φ o :
  owned o ⌜⌜ φ ⌝⌝ ⊣⊢ ⌜⌜ φ ⌝⌝.
Proof.
  rewrite /owned.
  setoid_rewrite uPred_affinely_pure_holds_L.
  iSplit.
  - iIntros "H". iDestruct "H" as (h []) "H".
    apply (fmap_empty_inv Excl h) in H as ->.
    rewrite attach_owner_empty map_Excl_empty uPred.ownM_unit //.
  - iIntros (H). iExists ∅.
    iSplit.
    + iPureIntro. rewrite map_Excl_empty //.
    + rewrite attach_owner_empty map_Excl_empty uPred.ownM_unit //.
Qed.

Lemma owned_emp o :
  owned o emp ⊣⊢ emp.
Proof.
  Search emp%I (<affine> emp)%I.
  rewrite -bi.affinely_emp.
  rewrite -bi.affinely_True_emp.
  rewrite owned_pure.
  rewrite bi.affinely_True_emp.
  rewrite bi.affinely_emp.
  done.
Qed.

Lemma uPred_ownM_disjoint (m1 m2 : heapTO) :
  uPred_ownM (◯ (map_Excl m1)) -∗ uPred_ownM (◯ (map_Excl m2)) -∗ ⌜ m1 ##ₘ m2 ⌝.
Proof.
  iIntros "H1 H2".
  iDestruct (uPred.ownM_op with "[H1 H2]") as "H"; first iFrame.
  rewrite -auth_frag_op.
  rewrite uPred_primitive.ownM_valid.
  rewrite auth_frag_valid.
  iDestruct "H" as "%". iPureIntro.
  apply map_Excl_disjoint.
  intros x. specialize (H x).
  rewrite lookup_op in H.
  destruct (_ !! x);
  destruct (_ !! x); done.
Qed.

Lemma owned_sep (P Q : oProp) o :
  owned o (P ∗ Q) ⊣⊢ owned o P ∗ owned o Q.
Proof.
  unfold owned.
  setoid_rewrite uPred_sep_holds_L.
  iSplit; iIntros "H".
  - iDestruct "H" as (h H) "H".
    destruct H as (x1 & x2 & H1 & H2 & H3).
    apply map_Excl_union_inv in H1 as (m1 & m2 & -> & -> & -> & Hdisj).
    erewrite attach_owner_disj in Hdisj.
    rewrite attach_owner_union map_Excl_union // auth_frag_op.
    rewrite uPred.ownM_op.
    iDestruct "H" as "[H1 H2]".
    iSplitL "H1"; iExists _; iFrame; done.
  - iDestruct "H" as "[H1 H2]".
    iDestruct "H1" as (h1 H1) "H1".
    iDestruct "H2" as (h2 H2) "H2".
    iAssert ⌜ h1 ##ₘ h2 ⌝%I as %Hdisj.
    {
      iDestruct (uPred_ownM_disjoint with "H1 H2") as "H".
      rewrite attach_owner_disj //.
    }
    iExists (h1 ∪ h2).
    iSplitL "".
    + iPureIntro. exists (map_Excl h1),(map_Excl h2).
      repeat split; try done.
      apply map_Excl_union. done.
    + eapply attach_owner_disj in Hdisj.
      rewrite attach_owner_union map_Excl_union // auth_frag_op uPred.ownM_op.
      iFrame.
Qed.

Lemma owned_exists {A} (P : A -> oProp) o :
  (∃ x, owned o (P x)) ⊣⊢ owned o (∃ x, P x).
Proof.
  unfold owned.
  setoid_rewrite uPred_exists_holds.
  iSplit; iIntros "H".
  - iDestruct "H" as (x h H) "H".
    iExists _. iFrame. iPureIntro. eauto.
  - iDestruct "H" as (h [x H]) "H".
    iExists _,_. iFrame. done.
Qed.
















(*
  =================================
  TREES, OWN_AUTH, OWNI, OWNΔ, ETC.
  =================================
*)

Definition G : Type. Admitted.
Definition acyclic : G -> Prop. Admitted.
Definition mk_graph : gmap endpoint owner -> G. Admitted.

Section graph_lemmas.
  Lemma acyclic_mk_delete Π l :
    acyclic (mk_graph Π) -> acyclic (mk_graph (delete l Π)).
  Proof.
  Admitted.
End graph_lemmas.

Definition owners_valid (Δ : heapTO) (Σ : heapT) : Prop :=
  Σ = fst <$> Δ ∧ acyclic (mk_graph $ snd <$> Δ).

Section owners_valid.
  Lemma owners_valid_lookup Δ Σ l t o :
    owners_valid Δ Σ -> Δ !! l = Some (t,o) -> Σ !! l = Some t.
  Proof.
    intros [-> H].
    rewrite lookup_fmap. intros ->. done.
  Qed.

  Lemma owners_valid_lookup_None Δ Σ l :
    owners_valid Δ Σ ->
    Δ !! l = None <-> Σ !! l = None.
  Proof.
    intros [-> H].
    rewrite lookup_fmap.
    destruct (Δ !! l) eqn:E; simpl; done.
  Qed.

  Lemma owners_valid_mutate Δ Σ l t t' o :
    Δ !! l = Some (t, o) ->
    owners_valid Δ Σ ->
    owners_valid (<[l:=(t', o)]> Δ) (<[l:=t']> Σ).
  Proof.
    intros Hl [-> H].
    split.
    - rewrite fmap_insert. simpl. done.
    - rewrite fmap_insert. simpl.
      assert (<[l:=o]>(snd <$> Δ) = snd <$> Δ) as ->; last done.
      apply insert_id.
      rewrite lookup_fmap Hl. done.
  Qed.

  Lemma owners_valid_delete Δ Σ l t o :
    Δ !! l = Some (t, o) ->
    owners_valid Δ Σ ->
    owners_valid (delete l Δ) (delete l Σ).
  Proof.
    intros Hl [-> H].
    split.
    - rewrite fmap_delete. done.
    - rewrite fmap_delete. apply acyclic_mk_delete. done.
  Qed.
End owners_valid.

Definition ownΔ (Δ : heapTO) : iProp := uPred_ownM (● (map_Excl Δ)).

Definition own_auth (h : heapT) : iProp :=
  ∃ Δ, ⌜⌜ owners_valid Δ h ⌝⌝ ∗ ownΔ Δ.

Definition ownI (l : endpoint) (t : chan_type) (o : owner) : iProp :=
  uPred_ownM (◯ {[ l := Excl (t,o) ]}).

Definition ownO (l : endpoint) (t : chan_type) : oProp :=
  uPred_ownM {[ l := Excl t ]}.

Arguments uPred_holds {_} !_/.

Lemma fmap_singleton_inv `{Countable K} {V1 V2} (f : V1 -> V2) (x : gmap K V1) (k : K) (v : V2) :
  f <$> x = {[ k := v ]} -> ∃ v' : V1, x = {[ k := v' ]}.
Proof.
  intros HH.
  rewrite ->map_eq_iff in HH.
  pose proof (HH k) as H'.
  rewrite lookup_fmap in H'.
  rewrite lookup_singleton in H'.
  destruct (x !! k) eqn:E; simpl in *; simplify_eq.
  exists v0.
  rewrite map_eq_iff.
  intros. specialize (HH i).
  rewrite lookup_fmap in HH.
  destruct (decide (i = k)).
  - subst. rewrite lookup_singleton in HH. rewrite lookup_singleton.
    destruct (x !! k); simplify_eq. done.
  - rewrite lookup_singleton_ne in HH; eauto.
    rewrite lookup_singleton_ne; eauto.
    destruct (x !! i); simplify_eq. done.
Qed.

Lemma singleton_eq_iff `{Countable K} {V} (k1 k2 : K) (v1 v2 : V) :
  ({[ k1 := v1 ]} : gmap K V) = {[ k2 := v2 ]} <-> k1 = k2 ∧ v1 = v2.
Proof.
  split; last naive_solver.
  intros HH.
  rewrite ->map_eq_iff in HH.
  specialize (HH k1).
  rewrite lookup_singleton in HH.
  destruct (decide (k1 = k2)); subst.
  - rewrite lookup_singleton in HH. simplify_eq; done.
  - rewrite lookup_singleton_ne in HH. simplify_eq. done.
Qed.

Lemma owned_own l t o :
  ownI l t o ⊣⊢ owned o (ownO l t).
Proof.
  rewrite /ownI /owned /ownO.
  iSplit.
  - iIntros "H". iExists {[ l := t]}.
    rewrite /attach_owner /map_Excl !map_fmap_singleton . iFrame.
    iPureIntro. uPred.unseal. done.
  - iIntros "H". iDestruct "H" as (h H) "H".
    revert H. uPred.unseal. intros H.
    rewrite -> leibniz_equiv_iff in H.
    symmetry in H.
    destruct (fmap_singleton_inv _ _ _ _ H) as [v' H'].
    subst.
    rewrite /map_Excl in H.
    rewrite map_fmap_singleton in H.
    apply singleton_eq_iff in H as []. simplify_eq.
    rewrite /attach_owner /map_Excl !map_fmap_singleton //.
Qed.

Lemma ownI_lookup Δ l t o :
  ownΔ Δ -∗ ownI l t o -∗ ⌜Δ !! l = Some (t, o)⌝.
Proof.
  iIntros "H1 H2".
  iDestruct (uPred.ownM_op with "[H2 H1]") as "H"; first iFrame.
  iDestruct (uPred.ownM_valid with "H") as "%".
  iPureIntro.
  apply auth_both_valid_discrete in H as [].
  pose proof @singleton_included_exclusive_l.
  specialize (H1 endpoint _ _ _ (Excl <$> Δ) l (Excl (t, o)) _ H0).
  rewrite ->H1 in H.
  rewrite lookup_fmap in H.
  destruct (Δ !! l) eqn:E; simpl in *; simplify_eq. done.
Qed.

Lemma own_lookup Σ l t o :
  own_auth Σ ∗ ownI l t o -∗ ⌜ Σ !! l = Some t ⌝.
Proof.
  iIntros "[H1 H2]".
  iDestruct "H1" as (Δ HΔ) "H1".
  iDestruct (ownI_lookup with "H1 H2") as %H.
  iPureIntro.
  eapply owners_valid_lookup; done.
Qed.

Lemma auth_update (a b a' b' : heapTO_UR) :
  (a,b) ~l~> (a',b') → auth_global_update (● a ⋅ ◯ b) (● a' ⋅ ◯ b').
Proof.
  assert (Cancelable a) as Hcancel. { apply _. }
  intros Hl.
  rewrite ->local_update_unital in Hl.
  rewrite /auth_global_update.
  intros [[[q z1]|] z2] [H1 H2].
  - rewrite view.view_valid_eq /= in H1.
    destruct H1 as [H _].
    apply Qp_not_add_le_l in H as [].
  - rewrite view.view_valid_eq /= in H1.
    destruct H1 as [_ H1].
    specialize (H1 0). simpl in *.
    destruct H1 as (x & ?%(inj _) & [z3 ?] & ?). simpl in *.
    apply (inj Some) in H2 as [_ ?%(inj to_agree)]; simpl in *.
    ofe_subst x.
    assert (z3 ≡ ε).
    {
      eapply discrete; first apply _.
      eapply Hcancel; first done.
      rewrite {2}H0 right_id. done.
    }
    setoid_subst.
    clear H0.
    rewrite-> (right_id _ _) in H1.
    destruct (Hl 0 z2); first done. { rewrite left_id. done. }
    split.
    + rewrite view.view_valid_eq /=.
      split; first done.
      exists a'.
      split; first done.
      split; last done.
      rewrite left_id. apply discrete in H0; last apply _. setoid_subst. done.
    + simpl in *.
      do 2 constructor; simpl; first done.
      f_equiv.
      apply discrete in H0; last apply _.
      by rewrite left_id.
Qed.

Lemma auth_update_alloc (a a' b' : heapTO_UR) :
  (a,ε) ~l~> (a',b') → auth_global_update (● a) (● a' ⋅ ◯ b').
Proof.
  intros H.
  assert (● a ≡ ● a ⋅ ε) as ->.
  { rewrite right_id. done. }
  by eapply auth_update.
Qed.

Definition change_owner (o : owner) (h : heapT) (Δ : heapTO) : heapTO. Admitted.

(* Lemma owners_valid_chang_owner o o' :
  connectedΔ Δ o o'
  owners_valid Δ Σ ->
  owners_valid (change_owner o h Δ) Σ *)

Lemma own_move_tc Σ c t i P :
  own_auth Σ ∗
  ownI c t (Thread i) ∗
  owned (Thread i) P
  ==∗
  own_auth Σ ∗
  ownI c t (Thread i) ∗
  owned (Chan c.1) P.
Proof.
  iIntros "(H1 & H2 & H3)".
  rewrite /own_auth.
  iDestruct "H1" as (Δ Hov) "H1".
  iDestruct (ownI_lookup with "H1 H2") as %H.
  rewrite /owned.
  iDestruct "H3" as (h Hh) "H3".
  iDestruct (uPred.ownM_op with "[H3 H1]") as "H"; first iFrame.
  iMod (bupd_ownM_update with "H") as "H".
  {
    eapply (auth_update _ _
        (map_Excl (change_owner (Chan c.1) h Δ))
        (map_Excl (attach_owner (Chan c.1) h))).
    rewrite /attach_owner.
    admit.
    (* eapply (auth_update _ _ (Excl <$> (<[ l := (t',o) ]> Δ)) {[l := Excl (t', o)]}). *)
  }
  iFrame.
  rewrite uPred.ownM_op.
  iDestruct "H" as "[H1 H3]".
  iModIntro.
  iSplitL "H1".
  - iExists _. iFrame. iPureIntro.

    admit.
  - iExists _. iFrame. iPureIntro. done.
Admitted.

Lemma own_move_ct Σ c t i P :
  own_auth Σ ∗
  ownI c t (Thread i) ∗
  owned (Chan c.1) P
  ==∗
  own_auth Σ ∗
  ownI c t (Thread i) ∗
  owned (Thread i) P.
Proof. Admitted.

Lemma own_alloc (i i' : nat) (l : endpoint) (Σ : heapT) (t t' : chan_type) :
  i ≠ i' →
  Σ !! l = None →
  Σ !! other l = None →
  own_auth Σ ==∗
     own_auth (<[l:=t]> $ <[other l:=t']> Σ) ∗
     ownI l t (Thread i) ∗ ownI (other l) t' (Thread i').
Proof.
  iIntros (Hi H1 H2) "H".
  rewrite /own_auth.
  iDestruct "H" as (Δ Hov) "H".
  rewrite /ownΔ.
  rewrite <-owners_valid_lookup_None in H1; last done.
  rewrite <-owners_valid_lookup_None in H2; last done.
  iMod (bupd_ownM_update with "H") as "H".
  {
    assert (● map_Excl Δ ≡ ● map_Excl Δ ⋅ ε) as ->.
    { rewrite right_id. done. }
    eapply auth_update.
    assert (map_Excl Δ !! l = None).
    { rewrite /map_Excl lookup_fmap H1. done. }
    assert (map_Excl Δ !! other l = None).
    { rewrite /map_Excl lookup_fmap H2. done. }
    eapply transitivity.
    - eapply (alloc_local_update _ _ l (Excl (t,Thread i))); try done.
    - eapply (alloc_local_update _ _ (other l) (Excl (t',Thread i'))); try done.
      rewrite /map_Excl lookup_insert_ne //.
      destruct l. simpl. destruct b; done.
  }
  rewrite /ownI.
  rewrite -!map_Excl_insert.
  rewrite !map_Excl_insert_op //.
  2: { rewrite lookup_insert_ne //. apply other_neq. }
  rewrite insert_singleton_op.
  2: { rewrite lookup_insert_ne //. apply other_neq. }
  rewrite insert_empty.
  rewrite auth_frag_op.
  rewrite !uPred.ownM_op.
  iDestruct "H" as "(H1 & H2 & H3)". iFrame.
  rewrite -!map_Excl_insert_op //.
  2: { rewrite lookup_insert_ne //. apply other_neq. }
  iModIntro. iExists _. iFrame.
  iPureIntro.
  (* Need to track which threads are fresh in Δ:
      own_auth Σ -> own_auth Σ k
     where k is the current number of threads.
     Then this lemma does own_auth Σ k -> own_auth Σ' (k + 1) *)
  admit.
Admitted.

Lemma own_mutate Σ l t t' o :
  own_auth Σ ∗ ownI l t o ==∗ own_auth (<[l:=t']> Σ) ∗ ownI l t' o.
Proof.
  iIntros "[H1 H2]".
  iDestruct "H1" as (Δ Hov) "H1".
  iDestruct (ownI_lookup with "H1 H2") as %Hl.
  iDestruct (uPred.ownM_op with "[H2 H1]") as "H"; first iFrame.
  iMod (bupd_ownM_update with "H") as "H".
  { eapply (auth_update _ _ (Excl <$> (<[ l := (t',o) ]> Δ)) {[l := Excl (t', o)]}).
    rewrite !fmap_insert.
    assert ({[l := Excl (t', o)]} = <[ l:= Excl (t',o) ]> ({[l := Excl (t, o)]} : gmap _ _)).
    { rewrite insert_singleton. done. }
    rewrite H.
    eapply insert_local_update.
    - rewrite lookup_fmap. rewrite Hl. simpl. done.
    - rewrite lookup_singleton. done.
    - by apply exclusive_local_update.
  }
  iModIntro.
  rewrite /ownI /own_auth. iFrame.
  rewrite uPred.ownM_op.
  iDestruct "H" as "[H1 H2]".
  iFrame.
  iExists _.
  iFrame.
  iPureIntro.
  eapply owners_valid_mutate; eauto.
Qed.

Lemma own_dealloc Σ l t o :
  own_auth Σ ∗ ownI l t o ==∗ own_auth (delete l Σ).
Proof.
  iIntros "[H1 H2]".
  iDestruct "H1" as (Δ Hov) "H1".
  iDestruct (ownI_lookup with "H1 H2") as %Hl.
  iDestruct (uPred.ownM_op with "[H2 H1]") as "H"; first iFrame.
  iMod (bupd_ownM_update with "H") as "H".
  {
    eapply (auth_update _ _ (Excl <$> (delete l Δ)) ∅).
    rewrite fmap_delete.
    eapply delete_singleton_local_update.
    apply _.
  }
  iModIntro.
  rewrite uPred_primitive.ownM_op.
  iDestruct "H" as "[H1 H2]".
  rewrite uPred.ownM_unit.
  iExists _. iFrame.
  iPureIntro.
  eapply owners_valid_delete; done.
Qed.


(*
Lemma strong_adequacy {A : ucmraT} (φ : A -> A -> Prop) :
  (uPred_ownM (● ε) ⊢ |==> ∃ x y, uPred_ownM (● x ⋅ ◯ y) ∧ ⌜ φ x y ⌝) → ∃ x, φ x x.
Proof.
Admitted.

Lemma P_to_own_frag {A : ucmraT} (x : A) (P : uPred A) :
  uPred_ownM (● x) ∗ P ⊢ ∃ y, uPred_ownM (● x ⋅ ◯ y).
Proof.
Admitted.
 *)

(* Lemma allocate Σ l t o :
  Σ !! l = None →
  own_auth Σ ⊢ |==> own_auth (<[l:=(t,o)]> Σ) ∗ own l t o.
Proof.
  intros H.
  rewrite own_ownM.
  apply uPred.bupd_ownM_update.
  apply auth_update_alloc; first apply _.
  rewrite fmap_insert.
Admitted. *)
  (* Check alloc_singleton_local_update.
  apply alloc_singleton_local_update; last done.
  by rewrite lookup_fmap H.
Qed. *)

(* Lemma auth_update_dealloc {A:ucmraT} (a b a' : A) :
  Cancelable a →
  (a,b) ~l~> (a',ε) → uPred_primitive.auth_global_update (● a ⋅ ◯ b) (● a').
Proof.
  intros Hcancel Hl.
  eapply uPred_primitive.auth_global_update_proper, auth_update, Hl; auto.
  rewrite (_ : (◯ ε) = ε); last done.
  by rewrite right_id.
Qed. *)

(* Lemma deallocate Σ l t o :
  own_auth Σ ∗ own l t o ⊢ |==> own_auth (delete l Σ).
Proof.
  iIntros "H".
  iDestruct (own_lookup with "H") as "%".
  iStopProof.
  rewrite own_ownM.
  apply uPred.bupd_ownM_update.
  apply auth_update_dealloc; first apply _.
  rewrite fmap_delete.
Admitted.
  apply delete_singleton_local_update_cancelable; first apply _.
  rewrite lookup_fmap. rewrite H. done.
Qed. *)

(* Lemma update Σ l t t' :
  own_auth Σ ∗ own l t ⊢
  |==> own_auth (<[l:=t']> Σ) ∗ own l t'.
Proof.
  iIntros "[H1 H2]".
  iApply bupd_trans.
  replace (<[l:=t']> Σ) with (<[l := t']> (delete l Σ))
    by apply fin_maps.insert_delete.
  iApply allocate. { apply lookup_delete. }
  iApply deallocate. iFrame.
Qed. *)


(* Lemma adequacy φ :
  (own_auth ∅ ⊢ |==> ∃ Σ2, own_auth Σ2 ∧ ⌜ φ Σ2 ⌝) → φ ∅.
Proof.
  unfold own_auth.
  intros HH.
  destruct (uPred.ownM_soundness (M:= heapTUR) (● ε)
    (λ x, ∃ y, x ≡ ● (Excl <$> y) ∧ φ y)) as [x [H1 [y [H2 H3]]]].
  - apply _.
  - split; last done.
    by apply auth_auth_validN.
  - iIntros "H".
    iMod (HH with "[H]") as (Σ) "[H %]".
    + by rewrite fmap_empty.
    + iExists (● (Excl <$> Σ)). iFrame.
      iModIntro. iSplit; first done.
      iPureIntro.
      by exists Σ.
  - unfold uPred_primitive.auth_global_updateN in H1.
    destruct (H1 ε) as [R1 R2].
    { split. rewrite right_id. by apply auth_auth_validN.
      simpl. by rewrite !right_id. }
    simpl in *.
    rewrite right_id in R2.
    rewrite-> H2 in R2.
    simpl in *.
    apply (inj Some) in R2 as [_ R2]. simpl in *.
    apply (inj to_agree) in R2.
    rewrite-> (left_id _ _) in R2.
    apply (discrete _) in R2.
    apply leibniz_equiv_iff in R2.
    by apply (fmap_empty_inv Excl) in R2 as ->.
Qed. *)

(* Lemma auth_global_valid_auth {A : ucmraT} n :
  auth_global_valid n (● (ε : A)).
Proof.
  split; last done.
  apply auth_auth_validN. apply ucmra_unit_validN.
Qed.

Lemma simple_adequacy φ :
  (own_auth ∅ ⊢ |==> ⌜ φ ⌝) → φ.
Proof. Admitted. *)
  (* unfold own_auth.
  apply uPred.ownM_simple_soundness.
  rewrite fmap_empty.
  apply: auth_global_valid_auth.
Qed. *)