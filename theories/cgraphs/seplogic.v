From stdpp Require Export gmap.
From iris.bi Require Export interface.
From iris.algebra Require Import excl gmap auth.
From iris.proofmode Require Export tactics.
Require Export cgraphs.cgraphs.bi.
Require Export cgraphs.cgraphs.util.
Require Export cgraphs.cgraphs.mapexcl.
Require Export cgraphs.cgraphs.multiset.

Notation heapT_UR V L := (gmapUR V (exclR L)).
Notation hProp V L := (uPred (heapT_UR V L)).
Notation hPropI V L := (uPredI (heapT_UR V L)).

Definition own `{Countable V} {L:ofe} (Σ : gmap V L) : hProp V L :=
  uPred_ownM (map_Excl Σ).

Global Instance : Params (@own) 4 := {}.

Definition own_out `{Countable V} {L:ofe} (v : V) (l : L) := own {[ v := l ]}.

Global Instance : Params (@own) 5 := {}.

Definition holds `{Countable V} {L:ofe} (P : hProp V L) (Σ : gmap V L) :=
  uPred_holds P (map_Excl Σ).

Global Instance : Params (@holds) 4 := {}.

Section seplogic.
  Context `{Countable V}.
  Context {L : ofe}.

  Implicit Types P Q : hProp V L.

  Global Instance own_proper : Proper ((≡) ==> (≡)) (own (V:=V) (L:=L)).
  Proof. solve_proper. Qed.

  Global Instance own_out_proper v : Proper ((≡) ==> (≡)) (own_out (V:=V) (L:=L) v).
  Proof. solve_proper. Qed.

  Lemma own_empty : own ∅ ⊣⊢@{hPropI V L} emp.
  Proof.
    unfold own. rewrite map_Excl_empty. apply uPred.ownM_unit.
  Qed.

  Lemma own_union Σ1 Σ2 : own Σ1 ∗ own Σ2 ⊢@{hPropI V L} own (Σ1 ∪ Σ2).
  Proof.
    rewrite /own. iIntros "H". iDestruct (uPred.ownM_op with "H") as "H".
    iDestruct (uPred_primitive.ownM_valid with "H") as %valid.
    rewrite map_Excl_union; first done. by apply map_Excl_valid_op.
  Qed.

  Global Instance holds_proper : Proper ((⊣⊢) ==> (≡) ==> (iff)) (holds (V:=V) (L:=L)).
  Proof.
    intros P1 P2 HP m1 m2 Hm.
    trans (holds P1 m2).
    - apply uPred_proper. by rewrite Hm.
    - apply HP. apply map_Excl_valid.
  Qed.

  Lemma sep_holds P Q Σ :
    holds (P ∗ Q) Σ <-> ∃ Σ1 Σ2, Σ ≡ Σ1 ∪ Σ2 ∧ Σ1 ##ₘ Σ2 ∧ holds P Σ1 ∧ holds Q Σ2.
  Proof.
    unfold holds.
    rewrite uPred_sep_holds. split.
    - intros (?&?&HH&?&?). apply map_Excl_union_inv in HH.
      destruct HH as (?&?&?&?&?&?). setoid_rewrite H2.
      exists x1,x2.
      split_and!; eauto.
      + rewrite <-H3; done.
      + rewrite <-H4; done.
    - intros (?&?&?&?&?&?). subst. eexists _,_. split_and!; eauto.
      rewrite H0. apply map_Excl_union. done.
  Qed.

  Lemma sep_combine P Q Σ1 Σ2 :
    holds P Σ1 -> holds Q Σ2 -> Σ1 ##ₘ Σ2 -> holds (P ∗ Q) (Σ1 ∪ Σ2).
  Proof.
    intros.
    apply sep_holds.
    eauto 6.
  Qed.

  Lemma emp_holds Σ :
    holds (L:=L) (V:=V) emp Σ <-> Σ ≡ ∅.
  Proof.
    unfold holds. rewrite uPred_emp_holds. split.
    - intros HH. apply map_Excl_empty_inv in HH.
      eapply map_empty_equiv_eq. done.
    - intros ->. rewrite map_Excl_empty. done.
  Qed.

  Lemma pure_holds Σ φ:
    holds (L:=L) (V:=V) ⌜ φ ⌝ Σ <-> φ.
  Proof.
    unfold holds. rewrite uPred_pure_holds. done.
  Qed.

  Lemma affinely_pure_holds Σ φ:
    holds (L:=L) (V:=V) ⌜⌜ φ ⌝⌝ Σ <-> Σ ≡ ∅ ∧ φ.
  Proof.
    unfold holds. rewrite uPred_affinely_pure_holds. split.
    - intros []. split; eauto. eapply map_empty_equiv_eq. apply map_Excl_empty_inv. done.
    - intros []. split; eauto. rewrite H0. rewrite map_Excl_empty //.
  Qed.

  Lemma exists_holds {B} (Φ : B -> hProp V L) Σ :
    holds (∃ b, Φ b) Σ <-> ∃ b, holds (Φ b) Σ.
  Proof.
    unfold holds. rewrite uPred_exists_holds. done.
  Qed.

  Lemma forall_holds {B} (Φ : B -> hProp V L) Σ :
    holds (∀ b, Φ b) Σ <-> ∀ b, holds (Φ b) Σ.
  Proof.
    unfold holds. rewrite uPred_forall_holds. done.
  Qed.

  Lemma and_holds (P Q : hProp V L) Σ :
    holds (P ∧ Q) Σ <-> holds P Σ ∧ holds Q Σ.
  Proof.
    rewrite /holds uPred_and_holds. done.
  Qed.

  Lemma own_holds (Σ1 Σ2 : gmap V L) :
    holds (own Σ1) Σ2 <-> Σ1 ≡ Σ2.
  Proof.
    unfold holds, own. simpl.
    rewrite uPred_ownM_holds.
    split.
    - eapply map_Excl_injective.
    - by intros ->.
  Qed.

  Lemma pure_sep_holds φ P Σ :
    holds (⌜⌜ φ ⌝⌝ ∗ P) Σ <-> φ ∧ holds P Σ.
  Proof.
    rewrite sep_holds.
    split.
    - intros (?&?&->&?&HH&?).
      apply affinely_pure_holds in HH as [Q1 Q2].
      rewrite Q1.
      split; eauto.
      rewrite left_id. eauto.
    - intros [].
      eexists ∅,Σ.
      rewrite left_id.
      split; eauto. split; first solve_map_disjoint.
      split; eauto.
      apply affinely_pure_holds. split; eauto.
  Qed.

  Lemma holds_entails P Q Σ :
    holds P Σ -> (P ⊢ Q) -> holds Q Σ.
  Proof.
    unfold holds.
    intros. eapply uPred_in_entails; eauto.
    apply map_Excl_valid.
  Qed.

  Fixpoint unexcl (l : list (V * exclR L)) : list (V * L) :=
    match l with
    | [] => []
    | (v,Excl x)::r => (v,x)::unexcl r
    | _::r => unexcl r
    end.

  Lemma elem_of_unexcl (l : list (V * exclR L)) (x : V * L) :
    x ∈ unexcl l <-> (x.1, Excl x.2) ∈ l.
  Proof.
    induction l; simpl.
    - rewrite !elem_of_nil. done.
    - destruct a. destruct c;
      rewrite !elem_of_cons !IHl; last set_solver.
      split; intros []; simplify_eq; simpl; eauto.
      destruct x; eauto.
  Qed.

  Lemma map_eq' : ∀ (m1 m2 : gmap V (exclR L)), (∀ i, m1 !! i = m2 !! i) -> m1 = m2.
  Proof. apply map_eq. Qed.

  Lemma valid_map_Excl_inv (x : heapT_UR V L) : ✓ x -> ∃ Σ, x = map_Excl Σ.
  Proof.
    unfold heapT_UR in *.
    unfold valid. unfold cmra_valid. simpl.
    unfold ucmra_valid.
    unfold gmap_valid_instance. unfold valid.
    unfold cmra_valid. simpl.
    unfold option_valid_instance. unfold valid.
    unfold cmra_valid. simpl.
    unfold excl_valid_instance.
    intros HH.
    exists (list_to_map (unexcl (map_to_list x))).
    apply map_eq'. intros i.
    rewrite lookup_fmap.
    specialize (HH i).
    destruct (list_to_map (unexcl (map_to_list x)) !! i) eqn:E.
    - apply elem_of_list_to_map_2 in E. simpl.
      apply elem_of_unexcl in E. simpl in *.
      revert E.
      rewrite elem_of_map_to_list'. intros. simpl in *. done.
    - apply not_elem_of_list_to_map_2 in E. simpl.
      rewrite ->elem_of_list_fmap in E.
      setoid_rewrite elem_of_unexcl in E.
      destruct (x !! i) eqn:F; eauto.
      rewrite F in HH.
      destruct c eqn:G; try done.
      exfalso.
      apply E. eexists (i,o). simpl.
      split; eauto.
      rewrite elem_of_map_to_list'. simpl. done.
  Qed.

  Lemma entails_holds P Q :
    (∀ Σ, holds P Σ -> holds Q Σ) -> P ⊢ Q.
  Proof.
    intros HH.
    eapply Build_uPred_entails.
    intros.
    apply valid_map_Excl_inv in H0 as [Σ ->].
    unfold holds in *. eauto.
  Qed.

  Lemma false_holds (Σ : gmap V L) :
    holds (False%I) Σ -> False.
  Proof. apply uPred_false_holds. Qed.

  Definition own_dom A : hProp V L := ∃ Σ, ⌜⌜ A = dom Σ ⌝⌝ ∗ own Σ.

  Lemma own_dom_empty : own_dom ∅ ⊣⊢ emp.
  Proof.
    iSplit; unfold own_dom; iIntros "H".
    - iDestruct "H" as (? Q) "H".
      symmetry in Q. apply dom_empty_iff_L in Q as ->.
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
End seplogic.