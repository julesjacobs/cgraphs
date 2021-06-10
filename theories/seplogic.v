From stdpp Require Export gmap.
From iris.bi Require Export interface.
From iris.algebra Require Import excl gmap auth.
From iris.proofmode Require Export tactics.
Require Export diris.langdef.
Require Export diris.logic.bi.
Require Export diris.util.
Require Export diris.mapexcl.
Require Export diris.multiset.

Notation heapT_UR V L := (gmapUR V (exclR L)).
Notation hProp V L := (uPred (heapT_UR V L)).

Definition own `{Countable V} {L:ofe} (Σ : gmap V L) : hProp V L :=
  uPred_ownM (map_Excl Σ).

Instance : Params (@own) 4 := {}.

Definition own_out `{Countable V} {L:ofe} (v : V) (l : L) := own {[ v := l ]}.

Instance : Params (@own) 5 := {}.

Definition holds `{Countable V} {L:ofe} (P : hProp V L) (Σ : gmap V L) :=
  uPred_holds P (map_Excl Σ).

Instance : Params (@holds) 4 := {}.

Section seplogic.
  Context `{Countable V}.
  Context {L : ofe}.

  Implicit Types P Q : hProp V L.

  Global Instance own_proper : Proper ((≡) ==> (≡)) (own (V:=V) (L:=L)).
  Proof. solve_proper. Qed.

  Global Instance own_out_proper v : Proper ((≡) ==> (≡)) (own_out (V:=V) (L:=L) v).
  Proof. solve_proper. Qed.

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
      destruct HH as (?&?&?&?&?&?). subst. eauto 6.
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
    - intros HH. apply map_Excl_empty_inv in HH. done.
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
    - intros []. split; eauto. apply map_Excl_empty_inv. done.
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

End seplogic.


