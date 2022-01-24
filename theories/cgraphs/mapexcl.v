From iris.algebra Require Import excl gmap.

Definition map_Excl `{Countable K} {V} (m : gmap K V) : gmap K (excl V) :=
  Excl <$> m.

Global Instance : Params (@map_Excl) 4 := {}.

Section map_Excl.
  Context `{Countable K} {V : ofe}.
  Implicit Type m : gmap K V.

  Global Instance map_excl_proper : Proper ((≡) ==> (≡)) (map_Excl (K:=K) (V:=V)).
  Proof. solve_proper. Qed.

  Lemma map_Excl_valid m : ✓ (map_Excl m).
  Proof. intros i. rewrite /map_Excl lookup_fmap. destruct (m !! i); done. Qed.
  Lemma map_Excl_empty : map_Excl ∅ = (ε : gmap K (excl V)).
  Proof. rewrite /map_Excl fmap_empty. done. Qed.
  Lemma map_Excl_empty_inv m : map_Excl m ≡ ∅ -> m = ∅.
  Proof.
    rewrite /map_Excl. intros G.
    apply map_empty_equiv_eq in G.
    eapply fmap_empty_iff. done.
  Qed.

  Lemma map_Excl_injective m1 m2 :
    map_Excl m1 ≡ map_Excl m2 -> m1 ≡ m2.
  Proof.
    rewrite /map_Excl.
    intros Hm i.
    specialize (Hm i).
    rewrite !lookup_fmap in Hm.
    destruct (m1 !! i),(m2 !! i); simpl in *; inversion Hm; subst; try done.
    inversion H2. subst. rewrite H3. done.
  Qed.
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
    m1 ##ₘ m2 -> map_Excl (m1 ∪ m2) ≡ map_Excl m1 ⋅ map_Excl m2.
  Proof.
    induction m1 using map_ind; intros; decompose_map_disjoint.
    - by rewrite map_Excl_empty !left_id_L.
    - assert ((m ∪ m2) !! i = None).
      { rewrite lookup_union H0 H1 //. }
      rewrite -insert_union_l !map_Excl_insert_op // IHm1 // assoc //.
  Qed.
  Lemma map_Excl_valid_op m1 m2 : ✓ (map_Excl m1 ⋅ map_Excl m2) ↔ m1 ##ₘ m2.
  Proof.
    split; last first.
    { intros. rewrite -map_Excl_union //. apply map_Excl_valid. }
    induction m1 as [|k x m1 Hm1 IH] using map_ind.
    { intros _. apply map_disjoint_empty_l. }
    rewrite map_Excl_insert_op // -assoc. intros Hvalid.
    apply map_disjoint_insert_l_2; last by eapply IH, cmra_valid_op_r.
    apply eq_None_not_Some; intros [x' Hm2].
    move: (Hvalid k).
    by rewrite !lookup_op /map_Excl lookup_singleton !lookup_fmap Hm1 Hm2.
  Qed.
  Lemma map_Excl_singleton_op_inv m me k x :
    map_Excl m ≡ {[ k := Excl x ]} ⋅ me ->
    ∃ m', m ≡ <[ k := x ]> m' ∧ me ≡ map_Excl m' ∧ m' !! k = None.
  Proof.
    rewrite /map_Excl. intros HH.
    exists (delete k m).
    assert (m !! k ≡ Some x).
    { specialize (HH k).
      revert HH. rewrite lookup_fmap lookup_op lookup_singleton.
      case: (m!!k); case:(me!!k); simpl; intros; inversion HH; subst;
      inversion H2; subst. rewrite H3. done. }
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
        intros a HH. inversion HH. subst. inversion H3.
      + rewrite lookup_fmap lookup_delete_ne //.
        revert HH. rewrite lookup_fmap lookup_op lookup_singleton_ne //.
        case: (me !! i); simpl; intros; inversion HH; subst; eauto.
        rewrite H3. done.
    - rewrite lookup_delete //.
  Qed.
  Lemma map_Excl_union_inv m me1 me2 :
    map_Excl m ≡ me1 ⋅ me2 ->
    ∃ m1 m2, m ≡ m1 ∪ m2 ∧ me1 ≡ map_Excl m1 ∧ me2 ≡ map_Excl m2 ∧ m1 ##ₘ m2.
  Proof.
    revert m. induction me1 as [|k xe me1 Hx IH] using map_ind; intros m.
    - rewrite left_id_L. intros Hr1.
      exists ∅,m.
      rewrite left_id_L map_Excl_empty. split_and!; try solve_map_disjoint.
    - rewrite insert_singleton_op // -assoc.
      destruct xe as [x|].
      + intros (m' & Hr1 & ? & ?)%map_Excl_singleton_op_inv.
        setoid_rewrite Hr1.
        destruct (IH m') as (m1 & m2 & Hr2 & Hr3 & Hr4 & ?); first done.
        exists (<[ k := x]> m1),m2.
        assert (m' !! k ≡ None) as H1'. { rewrite H1 //. }
        rewrite ->Hr2 in H1'.
        apply None_equiv_eq in H1'.
        apply lookup_union_None in H1' as [].
        repeat split.
        * rewrite Hr2. rewrite insert_union_l //.
        * rewrite map_Excl_insert_op //. rewrite Hr3 //.
        * done.
        * by apply map_disjoint_insert_l.
      + intros Hm. assert (✓ (ExclBot : excl V)) as [].
        eapply (singleton_valid k), (cmra_valid_op_l _ (me1 ⋅ me2)).
        rewrite -Hm. apply map_Excl_valid.
  Qed.
  Lemma map_Excl_disjoint m1 m2 :
    m1 ##ₘ m2 <-> map_Excl m1 ##ₘ map_Excl m2.
  Proof.
    split; first apply map_disjoint_fmap.
    unfold map_Excl. intros G ?. specialize (G i).
    rewrite !lookup_fmap in G.
    destruct (m1 !! i),(m2 !! i); done.
  Qed.
  Lemma map_Excl_singleton (a : K) (b : V) :
    map_Excl {[ a := b ]} = {[ a := Excl b ]}.
  Proof.
    rewrite /map_Excl map_fmap_singleton //.
  Qed.
  Lemma map_Excl_singleton_inv a b m :
    map_Excl m ≡ {[ a := Excl b ]} -> m ≡ {[ a := b ]}.
  Proof.
    intros HH.
    intros i.
    specialize (HH i).
    destruct (decide (i = a)); subst.
    - rewrite lookup_singleton. rewrite lookup_fmap in HH.
      rewrite lookup_singleton in HH.
      inversion HH. subst. inversion H2. subst.
      destruct (m !! a) eqn:E; simpl in *.
      + inversion HH; subst.
        inversion H5; subst. rewrite H6. done.
      + inversion HH.
    - rewrite lookup_singleton_ne //.
      rewrite lookup_singleton_ne // in HH.
      unfold map_Excl in HH.
      rewrite lookup_fmap in HH.
      inversion HH. symmetry in H1.
      apply fmap_None in H1. rewrite H1 //.
  Qed.
End map_Excl.