From stdpp Require Export gmap.
From iris.bi Require Export interface.
From iris.algebra Require Import excl gmap auth.
From iris.proofmode Require Export tactics.
Require Export diris.langdef.
Require Export diris.logic.bi.
Require Export diris.util.
Require Export diris.mapexcl.


Section seplogic.
  Context {V : Type}.
  Context `{Countable V}.
  Context {L : Type}.

  Canonical Structure LO := leibnizO L.

  Notation heapT := (gmap V L).
  Notation heapT_UR := (gmapUR V (exclR LO)).

  Notation hProp' := (uPred heapT_UR).
  Definition hProp_internal := hProp'.

  Definition own (Σ : gmap V L) : hProp' :=
    uPred_ownM (map_Excl Σ).

  Definition own1 (v : V) (l : L) : hProp' :=
    own {[ v := l ]}.

  Notation "⌜⌜ p ⌝⌝" := (<affine> ⌜ p ⌝)%I : bi_scope.

  Section uPred_lemmas.
    Context {A : ucmra}.
    Implicit Types P Q : uPred A.
    Arguments uPred_holds {_} !_/.
    Lemma owned_emp_helper (x : A) : ✓ x -> (uPred_ownM x ⊢ emp) -> x ≡ ε.
    Proof.
      uPred.unseal. intros ? [HH]. apply HH; simpl; done.
    Qed.

    Lemma uPred_emp_holds x :
      (emp%I : uPred A) x <-> x ≡ ε.
    Proof. by uPred.unseal. Qed.
    Lemma uPred_emp_holds_L `{!LeibnizEquiv A} x :
      (emp%I : uPred A) x <-> x = ε.
    Proof. unfold_leibniz. apply uPred_emp_holds. Qed.

    Lemma uPred_ownM_holds x y :
      (uPred_ownM x : uPred A) y <-> x ≡ y.
    Proof.
      by uPred.unseal.
    Qed.
    Lemma uPred_ownM_holds_L `{!LeibnizEquiv A} x y :
      (uPred_ownM x : uPred A) y <-> x = y.
    Proof.
      unfold_leibniz. apply uPred_ownM_holds.
    Qed.

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

  Definition holds (P : hProp') (Σ : heapT) := uPred_holds P (map_Excl Σ).

  Lemma sep_holds (P Q : hProp') Σ :
    holds (P ∗ Q) Σ <-> ∃ Σ1 Σ2, Σ = Σ1 ∪ Σ2 ∧ Σ1 ##ₘ Σ2 ∧ holds P Σ1 ∧ holds Q Σ2.
  Proof.
    unfold holds.
    rewrite uPred_sep_holds_L. split.
    - intros (?&?&HH&?&?). apply map_Excl_union_inv in HH.
      destruct HH as (?&?&?&?&?&?). subst. eauto 6.
    - intros (?&?&?&?&?&?). subst. eexists _,_. split_and!; eauto.
      apply map_Excl_union. done.
  Qed.

  Lemma sep_combine (P Q : hProp') Σ1 Σ2 :
    holds P Σ1 -> holds Q Σ2 -> Σ1 ##ₘ Σ2 -> holds (P ∗ Q) (Σ1 ∪ Σ2).
  Proof.
    intros.
    apply sep_holds.
    eauto 6.
  Qed.

  Lemma emp_holds Σ :
    holds emp%I Σ <-> Σ = ∅.
  Proof.
    unfold holds. rewrite uPred_emp_holds_L. split.
    - intros HH. apply map_Excl_empty_inv in HH. done.
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

  Lemma exists_holds {B} (Φ : B -> hProp') Σ :
    holds (∃ b, Φ b)%I Σ <-> ∃ b, holds (Φ b) Σ.
  Proof.
    unfold holds. rewrite uPred_exists_holds. done.
  Qed.

  Lemma and_holds (P Q : hProp') Σ :
    holds (P ∧ Q) Σ <-> holds P Σ ∧ holds Q Σ.
  Proof.
    rewrite /holds uPred_and_holds. done.
  Qed.

  Lemma own_holds Σ1 Σ2 :
    holds (own Σ1) Σ2 <-> Σ1 = Σ2.
  Proof.
    unfold holds, own. simpl.
    rewrite uPred_ownM_holds_L. split; intro HH; subst; eauto.
    eapply map_Excl_injective; eauto.
  Qed.

  Lemma own1_holds v l Σ :
    holds (own1 v l) Σ <-> Σ = {[ v := l ]}.
  Proof.
    unfold own1. rewrite own_holds. naive_solver.
  Qed.

  Lemma pure_sep_holds φ P Σ :
    holds (⌜⌜ φ ⌝⌝ ∗ P) Σ <-> φ ∧ holds P Σ.
  Proof.
    rewrite sep_holds.
    split.
    - intros (?&?&?&?&HH&?).
      apply affinely_pure_holds in HH as [].
      subst. split; eauto.
      rewrite left_id. eauto.
    - intros [].
      eexists ∅,Σ.
      rewrite left_id.
      split; eauto. split; first solve_map_disjoint.
      split; eauto.
      apply affinely_pure_holds. split; eauto.
  Qed.

  Lemma holds_entails (P Q : hProp') Σ :
    holds P Σ -> (P ⊢ Q) -> holds Q Σ.
  Proof.
    unfold holds.
    intros. eapply uPred_in_entails; eauto.
    apply map_Excl_valid.
  Qed.

  Instance holds_mono : Proper (uPred_entails ==> (=) ==> impl) holds.
  Proof.
    intros ??????. subst. intro. eapply holds_entails; eauto.
  Qed.

  Instance holds_iff : Proper (uPred_equiv ==> (=) ==> iff) holds.
  Proof.
    intros ?? HH ???. subst. destruct HH. unfold holds.
    rewrite uPred_in_equiv; eauto.
    apply map_Excl_valid.
  Qed.
End seplogic.

Definition hProp (V L : Type) `{Countable V} := hProp_internal (V:=V) (L:=L).