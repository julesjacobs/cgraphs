From stdpp Require Export gmap.
From iris.bi Require Export interface.
From iris.algebra Require Import excl gmap auth.
From iris.proofmode Require Export tactics.
Require Export diris.langdef.
Require Export diris.logic.bi.
Require Export diris.util.
Require Export diris.mapexcl.
Require Export diris.multiset.

(*
P Q : hProp V L
Σ Σ1 Σ2 : gmap V L
ls ls1 ls2 : list L
φ : Prop
l : L
v : V

ls1 ≡ₚ ls2 → (⊢ P) (Σ,ls1) → (⊢ P) (Σ,ls2)
(⊢ own (Σ1,ls1)) (Σ1,ls2) ↔ Σ1 = Σ2 ∧ ls1 ≡ₚ ls2
(⊢ P ∗ Q) (Σ,ls) ↔ ∃ Σ1 Σ2 ls1 ls2, Σ = Σ1 ∪ Σ2 ∧ Σ1 ##ₘ Σ2 ∧ ls ≡ₚ ls1 ++ ls2 ∧ (⊢ P) (Σ1,ls1) ∧ (⊢ Q) (Σ2,ls2)
(⊢ P ∧ Q) (Σ,ls) ↔ (⊢ P) (Σ,ls) ∧ (⊢ Q) (Σ,ls)
(⊢ ⌜ φ ⌝) (Σ,ls) ↔ φ
(⊢ ⌜⌜ φ ⌝⌝) (Σ,ls) ↔ φ ∧ Σ = ∅ ∧ ls = []
own (Σ1,ls1) ∗ own (Σ2,ls2) ⊣⊢ ⌜⌜ Σ1 ##ₘ Σ2 ⌝⌝ ∗ own (Σ1 ∪ Σ2) (ls1 ++ ls2)
ls1 ≡ₚ ls2 → own (Σ,ls1) ⊢ own (Σ,ls2)


derived lemmas:

(⊢ ⌜⌜ φ ⌝⌝ ∗ P) (Σ,ls) ↔ φ ∧ (⊢ P) (Σ,ls)
Σ1 ##ₘ Σ2 → (⊢ P) (Σ1,ls1) → (⊢ Q) (Σ2,ls2) → (⊢ P ∗ Q) (Σ1 ∪ Σ2) (ls1 ++ ls2)

derived definitions:

own_ins ls := own (∅,ls)
own_outs ∅ := own (Σ,[])
own_in l := own_ins [l]
own_outs v l := own_outs {[ v := l ]}

adequacy lemma:

(⊢ ∃ Σ ls, own (Σ,ls) ∗ ⌜⌜ φ v (Σ,ls) ⌝⌝) (Σ',ls') → φ (Σ',ls')
P ⊢ ⊢ ∃ Σ ls, ⌜⌜ φ v (Σ,ls) ⌝⌝

(∀ v, f v ⊢ ⊢ ∃ Σ ls, ⌜⌜ φ v (Σ,ls) ⌝⌝ ∗ own (Σ,ls)) → inv f →
∃ g, cgraph_wf g ∧ ∀ v, φ v (in_labels g v) (out_edges g v)

Verder was ik aan het nadenken over progress. High level gaat het argument als volgt:
We willen laten zien dat één van de volgende twee altijd geldt:
1. Alle threads zijn unit en de heap is leeg.
2. Er is een thread die kan stappen.
Omdat (1) decidable is kunnen we bewijzen (not (1) => (2)).
We nemen dus aan dat er een thread is die niet unit is, of een buffer in de heap.
We gaan vervolgens stapjes zetten in de connectivity graph, beginnend bij de thread of channel die er is.
Er zijn de volgende mogelijkheden:
1. We zitten bij een thread.
  a. De thread is aan het receiven op een channel met een lege buffer.
  b. De thread is niet aan het receiven op een channel met een lege buffer.
2. We zitten bij een channel.
  a. Beide buffers zijn leeg / er bestaat nog maar 1 buffer en die is leeg.
  b. Er is een buffer die niet leeg is

Bij 1a stappen we naar het desbetreffende channel.
Bij 1b weten we uit de invariant dat de thread getypeerd is, en dan uit local progress dat die thread een stapje kan zetten.
Bij 2a weten we uit de invariant dat de session types duaal zijn, en stappen we naar degene die niet een receive is (dus een send of end, dat kan ivm dualiteit).
Bij 2b stappen we naar de vertex die het endpoint heeft van de buffer die niet leeg is (die bestaat omdat we ivm de invariant weten dat het channel dan een inkomende edge heeft van die buffer).

Als we kunnen bewijzen dat dit proces niet direct terug stapt waar het vandaan kwam dan geeft een uforest lemma dat het proces termineert (dus bij case 1b).
Als we tussen twee channels heen en weer stappen dan hebben ze beide een edge naar elkaar, en dat kan niet ivm cycles.
Tussen twee threads heen en weer stappen kan ook niet, want een thread stapt altijd naar een channel.
Tussen een thread en een channel heen en weer stappen betekent dat de thread staat te wachten op het channel omdat hij een receive wil doen maar de buffer leeg is. In dit geval zal het channel niet terug stappen naar de thread, omdat een channel altijd stapt naar een endpoint van een niet-lege buffer, of als beide buffers leeg zijn dan stapt hij naar de kant die geen receive vooraan zijn session type heeft.
*)

Section seplogic.
  Context {V : Type}.
  Context `{Countable V}.
  Context {L : Type}.

  Canonical Structure LO := leibnizO L.

  Notation heapT := (gmap V L).
  Notation heapT_UR := (gmapUR V (exclR LO)).

  Notation hProp' := (uPred heapT_UR).
  Definition hProp_internal := hProp'.
  Definition heapT_UR_internal := heapT_UR.

  Definition own (Σ : gmap V L) : hProp' :=
    uPred_ownM (map_Excl Σ).

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
    Lemma uPred_forall_holds {B} (Φ : B -> uPred A) x :
      (∀ b, Φ b)%I x <-> ∀ b, Φ b x.
    Proof. by uPred.unseal. Qed.
    Lemma uPred_affinely_pure_holds φ x :
      (⌜⌜ φ ⌝⌝ : uPred A)%I x <-> x ≡ ε ∧ φ.
    Proof. rewrite /bi_affinely uPred_and_holds uPred_pure_holds uPred_emp_holds. done. Qed.
    Lemma uPred_affinely_pure_holds_L `{!LeibnizEquiv A} φ x :
      (⌜⌜ φ ⌝⌝ : uPred A)%I x <-> x = ε ∧ φ.
    Proof. unfold_leibniz. apply uPred_affinely_pure_holds. Qed.
  End uPred_lemmas.

  Definition holds (P : hProp') (Σ : gmap V L) := uPred_holds P (map_Excl Σ).

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

  Lemma forall_holds {B} (Φ : B -> hProp') Σ :
    holds (∀ b, Φ b)%I Σ <-> ∀ b, holds (Φ b) Σ.
  Proof.
    unfold holds. rewrite uPred_forall_holds. done.
  Qed.

  Lemma and_holds (P Q : hProp') Σ :
    holds (P ∧ Q) Σ <-> holds P Σ ∧ holds Q Σ.
  Proof.
    rewrite /holds uPred_and_holds. done.
  Qed.

  Lemma own_holds (Σ1 Σ2 : gmap V L) :
    holds (own Σ1) Σ2 <-> Σ1 = Σ2.
  Proof.
    unfold holds, own. simpl.
    rewrite uPred_ownM_holds_L. split; intro HH; subst; eauto.
    eapply map_Excl_injective; eauto.
  Qed.

  (* Lemma own1_holds v l Σ :
    holds (own1 v l) Σ <-> Σ = {[ v := l ]}.
  Proof.
    unfold own1. rewrite own_holds. naive_solver.
  Qed. *)

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

  Definition own_out (v : V) (l : L) := own {[ v := l ]}.
End seplogic.

Notation hProp V L := (hProp_internal (V:=V) (L:=L)).
Notation "⌜⌜ p ⌝⌝" := (<affine> ⌜ p ⌝)%I : bi_scope.
Bind Scope bi_scope with hProp.