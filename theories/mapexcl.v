From stdpp Require Export gmap.
From iris.bi Require Export interface.
From iris.algebra Require Import excl gmap auth.
From iris.proofmode Require Export tactics.
Require Export diris.util.


Definition map_Excl `{Countable K} {V} (m : gmap K V) : gmap K (excl V) := Excl <$> m.

Section map_Excl.
  Context `{Countable K} {V : ofe} `{!LeibnizEquiv V}.
  Implicit Type m : gmap K V.
  Lemma map_Excl_valid m : ✓ (map_Excl m).
  Proof. intros i. rewrite /map_Excl lookup_fmap. destruct (m !! i); done. Qed.
  Lemma map_Excl_empty : map_Excl ∅ = (ε : gmap K (excl V)).
  Proof. rewrite /map_Excl fmap_empty. done. Qed.
  Lemma map_Excl_empty_inv Σ : map_Excl Σ = (∅ : gmap K (excl V)) -> Σ = ∅.
  Proof.
    rewrite /map_Excl. intros G. apply fmap_empty_inv in G. done.
  Qed.

  Lemma map_Excl_injective m1 m2 :
    map_Excl m1 = map_Excl m2 -> m1 = m2.
  Proof.
    rewrite /map_Excl.
    intros HH.
  Admitted.
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
  Proof.
    split; first apply fmap_map_disjoint.
    unfold map_Excl. intros G ?. specialize (G i).
    rewrite !lookup_fmap in G.
    destruct (m1 !! i),(m2 !! i); done.
  Qed.
End map_Excl.

Lemma map_Excl_singleton `{Countable K} {V} (a : K) (b : V) :
  map_Excl {[ a := b ]} = {[ a := Excl b ]}.
Proof.
  rewrite /map_Excl map_fmap_singleton //.
Qed.
Lemma map_Excl_singleton_inv `{Countable K} {V} a b (Σ : gmap K V) :
  map_Excl Σ = {[ a := Excl b ]} -> Σ = {[ a := b ]}.
Proof.
  intros HH.
  pose proof (fmap_singleton_inv _ _ _ _ HH).
  destruct H0 as [? ->]. rewrite map_Excl_singleton in HH.
  apply singleton_eq_iff in HH. destruct HH. simplify_eq. done.
Qed.