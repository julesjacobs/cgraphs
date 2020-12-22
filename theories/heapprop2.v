From stdpp Require Import gmap.
From iris.bi Require Import interface.
From iris.proofmode Require Import tactics.
Import diris.util.

(** This file constructs a simple non step-indexed linear separation logic as
predicates over heaps (modeled as maps from integer locations to integer values).
It shows that Iris's [bi] canonical structure can be inhabited, and the Iris
proof mode can be used to prove lemmas in this separation logic. *)
Definition loc := Z.
Definition val := Z.

Definition heapProp := gmap loc val → Prop.

Section ofe.
  Inductive heapProp_equiv' (P Q : heapProp) : Prop :=
    { heapProp_in_equiv : ∀ σ, P σ ↔ Q σ }.
  Instance heapProp_equiv : Equiv heapProp := heapProp_equiv'.
  Instance heapProp_equivalence : Equivalence (≡@{heapProp}).
  Proof. split; repeat destruct 1; constructor; naive_solver. Qed.
  Canonical Structure heapPropO := discreteO heapProp.
End ofe.

(** logical entailement *)
Definition heapProp_entails (P Q : heapProp) : Prop := ∀ σ, P σ → Q σ.

(** logical connectives *)
Definition heapProp_emp : heapProp := λ σ, σ = ∅.

Definition heapProp_pure (φ : Prop) : heapProp := λ _, φ.

Definition heapProp_and (P Q : heapProp) : heapProp := λ σ, P σ ∧ Q σ.

Definition heapProp_or (P Q : heapProp) : heapProp := λ σ, P σ ∨ Q σ.

Definition heapProp_impl (P Q : heapProp) : heapProp := λ σ, P σ → Q σ.

Definition heapProp_forall {A} (Ψ : A → heapProp) : heapProp := λ σ, ∀ a, Ψ a σ.

Definition heapProp_exist {A} (Ψ : A → heapProp) : heapProp := λ σ, ∃ a, Ψ a σ.

Definition heapProp_sep (P Q : heapProp) : heapProp :=
  λ σ, ∃ σ1 σ2, σ = σ1 ∪ σ2 ∧ σ1 ##ₘ σ2 ∧ P σ1 ∧ Q σ2.

Definition heapProp_wand (P Q : heapProp) : heapProp :=
  λ σ, ∀ σ', σ ##ₘ σ' → P σ' → Q (σ ∪ σ').

Definition heapProp_persistently (P : heapProp) : heapProp := λ σ, P ∅.

(** Iris's [bi] class requires the presence of a later modality, but for non
step-indexed logics, it can be defined as the identity. *)
Definition heapProp_later (P : heapProp) : heapProp := P.

Ltac unfold_heapProp :=
    unfold heapProp_emp, heapProp_pure, heapProp_and, heapProp_or, heapProp_impl,
      heapProp_forall, heapProp_exist, heapProp_sep, heapProp_wand, heapProp_persistently,
      heapProp_later, heapProp_entails in *.

Section mixins.
  Lemma heapProp_bi_mixin :
    BiMixin
      heapProp_entails heapProp_emp heapProp_pure heapProp_and heapProp_or
      heapProp_impl (@heapProp_forall) (@heapProp_exist)
      heapProp_sep heapProp_wand heapProp_persistently.
  Proof.
    split.
    - (* [PreOrder heapProp_entails] *)
      split; intro; unfold_heapProp; naive_solver.
    - (* [P ≡ Q ↔ (P ⊢ Q) ∧ (Q ⊢ P)] *)
      intros P Q; split; unfold_heapProp.
      + intros [HPQ]; split; naive_solver.
      + intros [??]. split. naive_solver.
    - (* [Proper (iff ==> dist n) bi_pure] *)
      split; naive_solver.
    - (* [NonExpansive2 bi_and] *)
      intros n P1 P2 [HP] Q1 Q2 [HQ]; unfold_heapProp; split; naive_solver.
    - (* [NonExpansive2 bi_or] *)
      intros n P1 P2 [HP] Q1 Q2 [HQ]; unfold_heapProp; split; naive_solver.
    - (* [NonExpansive2 bi_impl] *)
      intros n P1 P2 [HP] Q1 Q2 [HQ]; unfold_heapProp; split; naive_solver.
    - (* [Proper (pointwise_relation _ (dist n) ==> dist n) (bi_forall A)] *)
      intros A n Φ1 Φ2 HΦ; split=> σ /=; split=> ? x; by apply HΦ.
    - (* [Proper (pointwise_relation _ (dist n) ==> dist n) (bi_exist A)] *)
      intros A n Φ1 Φ2 HΦ; split=> σ /=; split=> -[x ?]; exists x; by apply HΦ.
    - (* [NonExpansive2 bi_sep] *)
      intros n P1 P2 [HP] Q1 Q2 [HQ]; unfold_heapProp; split; naive_solver.
    - (* [NonExpansive2 bi_wand] *)
      intros n P1 P2 [HP] Q1 Q2 [HQ]; unfold_heapProp; split; naive_solver.
    - (* [NonExpansive2 bi_persistently] *)
      intros n P1 P2 [HP]; split; unfold_heapProp; naive_solver.
    - (* [φ → P ⊢ ⌜ φ ⌝] *)
      unfold_heapProp.
      intros φ P ?; by done.
    - (* [(φ → True ⊢ P) → ⌜ φ ⌝ ⊢ P] *)
      intros φ P HP; split=> σ ?. by apply HP.
    - (* [P ∧ Q ⊢ P] *)
      intros P Q. split=> σ ??. unfold_heapProp; done.
    - (* [P ∧ Q ⊢ Q] *)
      intros P Q; split=> σ [??]; done.
    - (* [(P ⊢ Q) → (P ⊢ R) → P ⊢ Q ∧ R] *)
      intros P Q. unfold heapProp_entails. R HPQ HPR. split=> σ; split; auto.
    - (* [P ⊢ P ∨ Q] *)
      intros P Q; split=> σ; by left.
    - (* [Q ⊢ P ∨ Q] *)
      intros P Q; split=> σ; by right.
    - (* [(P ⊢ R) → (Q ⊢ R) → P ∨ Q ⊢ R] *)
      intros P Q R [HPQ] [HQR]; split=> σ [?|?]; auto.
    - (* [(P ∧ Q ⊢ R) → P ⊢ Q → R] *)
      intros P Q R HPQR; split=> σ ??. by apply HPQR.
    - (* [(P ⊢ Q → R) → P ∧ Q ⊢ R] *)
      intros P Q R HPQR; split=> σ [??]. by apply HPQR.
    - (* [(∀ a, P ⊢ Ψ a) → P ⊢ ∀ a, Ψ a] *)
      intros A P Ψ HPΨ; split=> σ ? a. by apply HPΨ.
    - (* [(∀ a, Ψ a) ⊢ Ψ a] *)
      intros A Ψ a; split=> σ ?; done.
    - (* [Ψ a ⊢ ∃ a, Ψ a] *)
      intros A Ψ a; split=> σ ?. by exists a.
    - (* [(∀ a, Φ a ⊢ Q) → (∃ a, Φ a) ⊢ Q] *)
      intros A Φ Q HΦQ; split=> σ [a ?]. by apply (HΦQ a).
    - (* [(P ⊢ Q) → (P' ⊢ Q') → P ∗ P' ⊢ Q ∗ Q'] *)
      intros P P' Q Q' [HPQ] [HP'Q']; split; naive_solver.
    - (* [P ⊢ emp ∗ P] *)
      intros P; split=> σ ? /=. eexists ∅, σ. rewrite left_id_L.
      split_and!; done || apply map_disjoint_empty_l.
    - (* [emp ∗ P ⊢ P] *)
      intros P; split; intros ? (?&σ&->&?&->&?). by rewrite left_id_L.
    - (* [P ∗ Q ⊢ Q ∗ P] *)
      intros P Q; split; intros ? (σ1&σ2&->&?&?&?).
      exists σ2, σ1. by rewrite map_union_comm.
    - (* [(P ∗ Q) ∗ R ⊢ P ∗ (Q ∗ R)] *)
      intros P Q R; split; intros ? (?&σ3&->&?&(σ1&σ2&->&?&?&?)&?).
      exists σ1, (σ2 ∪ σ3). split_and!; [by rewrite assoc_L|solve_map_disjoint|done|].
      exists σ2, σ3; split_and!; [done|solve_map_disjoint|done..].
    - (* [(P ∗ Q ⊢ R) → P ⊢ Q -∗ R] *)
      intros P Q R [HPQR]; split=> σ1 ? σ2 ??. apply HPQR. by exists σ1, σ2.
    - (* [(P ⊢ Q -∗ R) → P ∗ Q ⊢ R] *)
      intros P Q R [HPQR]; split; intros ? (σ1&σ2&->&?&?&?). by apply HPQR.
    - (* [(P ⊢ Q) → <pers> P ⊢ <pers> Q] *)
      intros P Q [HPQ]; split=> σ. apply HPQ.
    - (* [<pers> P ⊢ <pers> <pers> P] *)
      intros P; split=> σ; done.
    - (* [emp ⊢ <pers> emp] *)
      unseal; split=> σ; done.
    - (* [(∀ a, <pers> (Ψ a)) ⊢ <pers> (∀ a, Ψ a)] *)
      intros A Ψ; split=> σ; done.
    - (* [<pers> (∃ a, Ψ a) ⊢ ∃ a, <pers> (Ψ a)] *)
      intros A Ψ; split=> σ; done.
    - (* [<pers> P ∗ Q ⊢ <pers> P] *)
      intros P Q; split; intros ? (σ1&σ2&->&?&?&?); done.
    - (* [<pers> P ∧ Q ⊢ P ∗ Q] *)
      intros P Q; split=> σ [??]. eexists ∅, σ. rewrite left_id_L.
      split_and!; done || apply map_disjoint_empty_l.
  Qed.

  Lemma heapProp_bi_later_mixin :
    BiLaterMixin
      heapProp_entails heapProp_pure heapProp_or heapProp_impl
      (@heapProp_forall) (@heapProp_exist)
      heapProp_sep heapProp_persistently heapProp_later.
  Proof. eapply bi_later_mixin_id; [done|apply heapProp_bi_mixin]. Qed.
End mixins.

Canonical Structure heapPropI : bi :=
  {| bi_ofe_mixin := ofe_mixin_of heapProp;
     bi_bi_mixin := heapProp_bi_mixin; bi_bi_later_mixin := heapProp_bi_later_mixin |}.

(* Instance heapProp_pure_forall : BiPureForall heapPropI. *)
(* Proof. intros A φ. rewrite /bi_forall /bi_pure /=. unseal. by split. Qed. *)

Lemma heapProp_proofmode_test {A} (P Q R : heapProp) (Φ Ψ : A → heapProp) :
  P ∗ Q -∗
  □ R -∗
  □ (R -∗ ∃ x, Φ x) -∗
  ∃ x, Φ x ∗ Φ x ∗ P ∗ Q.
Proof.
  iIntros "[HP HQ] #HR #HRΦ".
  iDestruct ("HRΦ" with "HR") as (x) "#HΦ".
  iExists x. iFrame. by iSplitL.
Qed.
