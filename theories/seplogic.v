From stdpp Require Export gmap.
From iris.bi Require Export interface.
From iris.algebra Require Import excl gmap auth.
From iris.proofmode Require Export tactics.
Require Export diris.langdef.
Require Export diris.logic.bi.
Require Export diris.util.
(* Require Export diris.logic.bupd. *)


Canonical Structure chan_typeO := leibnizO chan_type.

Notation heapT := (gmap endpoint chan_type).
Notation heapT_UR := (gmapUR endpoint (exclR chan_typeO)).

Notation hProp := (uPred heapT_UR).

Definition own (l : endpoint) (t : chan_type) : hProp :=
  uPred_ownM {[ l := Excl t ]}.

Notation "⌜⌜ p ⌝⌝" := (<affine> ⌜ p ⌝)%I : bi_scope.


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

Section uPred_lemmas.
  Context {A : ucmra}.
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

Definition holds (P : hProp) (Σ : heapT) := uPred_holds P (map_Excl Σ).

Lemma sep_holds (P Q : hProp) Σ :
  holds (P ∗ Q) Σ <-> ∃ Σ1 Σ2, Σ = Σ1 ∪ Σ2 ∧ Σ1 ##ₘ Σ2 ∧ holds P Σ1 ∧ holds Q Σ2.
Proof.
  unfold holds.
  rewrite uPred_sep_holds_L. split.
  - intros (?&?&?&?&?). apply map_Excl_union_inv in H.
    destruct H as (?&?&?&?&?&?). subst. eauto 6.
  - intros (?&?&?&?&?&?). subst. eexists _,_. split_and!; eauto.
    apply map_Excl_union. done.
Qed.

Lemma emp_holds Σ :
  holds emp%I Σ <-> Σ = ∅.
Proof.
  unfold holds. rewrite uPred_emp_holds_L. split.
  - intros H. apply map_Excl_empty_inv in H. done.
  - intros ->. apply map_Excl_empty.
Qed.

Lemma pure_holds Σ φ:
  holds ⌜ φ ⌝ Σ <-> φ.
Proof.
  unfold holds. rewrite uPred_pure_holds. done.
Qed.

Lemma affinely_pure_holds Σ φ:
  holds ⌜⌜ φ ⌝⌝ Σ <-> Σ = ∅ ∧ φ.
Proof.
  unfold holds. rewrite uPred_affinely_pure_holds_L. split.
  - intros []. split; eauto. apply map_Excl_empty_inv. done.
  - intros []. subst. split; eauto. apply map_Excl_empty.
Qed.

Lemma exists_holds {B} (Φ : B -> hProp) Σ :
  holds (∃ b, Φ b)%I Σ <-> ∃ b, holds (Φ b) Σ.
Proof.
   unfold holds. rewrite uPred_exists_holds. done.
Qed.

Lemma and_holds (P Q : hProp) Σ :
  holds (P ∧ Q) Σ <-> holds P Σ ∧ holds Q Σ.
Proof.
  rewrite /holds uPred_and_holds. done.
Qed.