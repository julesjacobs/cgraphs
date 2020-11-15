From stdpp Require Import gmap.
From iris.bi Require Import interface.
From iris.proofmode Require Import tactics.

(** This file constructs a simple non step-indexed linear separation logic as
predicates over heaps (modeled as maps from integer locations to integer values).
It shows that Iris's [bi] canonical structure can be inhabited, and the Iris
proof mode can be used to prove lemmas in this separation logic. *)
Definition loc := Z.
Definition val := Z.

Record heapProp := HeapProp {
  heapProp_holds :> gmap loc val → Prop;
}.
Arguments heapProp_holds : simpl never.
Add Printing Constructor heapProp.

Section ofe.
  Inductive heapProp_equiv' (P Q : heapProp) : Prop :=
    { heapProp_in_equiv : ∀ σ, P σ ↔ Q σ }.
  Instance heapProp_equiv : Equiv heapProp := heapProp_equiv'.
  Instance heapProp_equivalence : Equivalence (≡@{heapProp}).
  Proof. split; repeat destruct 1; constructor; naive_solver. Qed.
  Canonical Structure heapPropO := discreteO heapProp.
End ofe.

(** logical entailement *)
Inductive heapProp_entails (P Q : heapProp) : Prop :=
  { heapProp_in_entails : ∀ σ, P σ → Q σ }.

(** logical connectives *)
Definition heapProp_emp_def : heapProp :=
  {| heapProp_holds σ := σ = ∅ |}.
Definition heapProp_emp_aux : seal (@heapProp_emp_def). Proof. by eexists. Qed.
Definition heapProp_emp := unseal heapProp_emp_aux.
Definition heapProp_emp_eq :
  @heapProp_emp = @heapProp_emp_def := seal_eq heapProp_emp_aux.

Definition heapProp_pure_def (φ : Prop) : heapProp :=
  {| heapProp_holds _ := φ |}.
Definition heapProp_pure_aux : seal (@heapProp_pure_def). Proof. by eexists. Qed.
Definition heapProp_pure := unseal heapProp_pure_aux.
Definition heapProp_pure_eq :
  @heapProp_pure = @heapProp_pure_def := seal_eq heapProp_pure_aux.

Definition heapProp_and_def (P Q : heapProp) : heapProp :=
  {| heapProp_holds σ := P σ ∧ Q σ |}.
Definition heapProp_and_aux : seal (@heapProp_and_def). Proof. by eexists. Qed.
Definition heapProp_and := unseal heapProp_and_aux.
Definition heapProp_and_eq:
  @heapProp_and = @heapProp_and_def := seal_eq heapProp_and_aux.

Definition heapProp_or_def (P Q : heapProp) : heapProp :=
  {| heapProp_holds σ := P σ ∨ Q σ |}.
Definition heapProp_or_aux : seal (@heapProp_or_def). Proof. by eexists. Qed.
Definition heapProp_or := unseal heapProp_or_aux.
Definition heapProp_or_eq:
  @heapProp_or = @heapProp_or_def := seal_eq heapProp_or_aux.

Definition heapProp_impl_def (P Q : heapProp) : heapProp :=
  {| heapProp_holds σ := P σ → Q σ |}.
Definition heapProp_impl_aux : seal (@heapProp_impl_def). Proof. by eexists. Qed.
Definition heapProp_impl := unseal heapProp_impl_aux.
Definition heapProp_impl_eq :
  @heapProp_impl = @heapProp_impl_def := seal_eq heapProp_impl_aux.

Definition heapProp_forall_def {A} (Ψ : A → heapProp) : heapProp :=
  {| heapProp_holds σ := ∀ a, Ψ a σ |}.
Definition heapProp_forall_aux : seal (@heapProp_forall_def). Proof. by eexists. Qed.
Definition heapProp_forall {A} := unseal heapProp_forall_aux A.
Definition heapProp_forall_eq :
  @heapProp_forall = @heapProp_forall_def := seal_eq heapProp_forall_aux.

Definition heapProp_exist_def {A} (Ψ : A → heapProp) : heapProp :=
  {| heapProp_holds σ := ∃ a, Ψ a σ |}.
Definition heapProp_exist_aux : seal (@heapProp_exist_def). Proof. by eexists. Qed.
Definition heapProp_exist {A} := unseal heapProp_exist_aux A.
Definition heapProp_exist_eq :
  @heapProp_exist = @heapProp_exist_def := seal_eq heapProp_exist_aux.

Definition heapProp_sep_def (P Q : heapProp) : heapProp :=
  {| heapProp_holds σ := ∃ σ1 σ2, σ = σ1 ∪ σ2 ∧ σ1 ##ₘ σ2 ∧ P σ1 ∧ Q σ2 |}.
Definition heapProp_sep_aux : seal (@heapProp_sep_def). Proof. by eexists. Qed.
Definition heapProp_sep := unseal heapProp_sep_aux.
Definition heapProp_sep_eq:
  @heapProp_sep = @heapProp_sep_def := seal_eq heapProp_sep_aux.

Definition heapProp_wand_def (P Q : heapProp) : heapProp :=
  {| heapProp_holds σ := ∀ σ', σ ##ₘ σ' → P σ' → Q (σ ∪ σ') |}.
Definition heapProp_wand_aux : seal (@heapProp_wand_def). Proof. by eexists. Qed.
Definition heapProp_wand := unseal heapProp_wand_aux.
Definition heapProp_wand_eq:
  @heapProp_wand = @heapProp_wand_def := seal_eq heapProp_wand_aux.

Definition heapProp_persistently_def (P : heapProp) : heapProp :=
  {| heapProp_holds σ := P ∅ |}.
Definition heapProp_persistently_aux : seal (@heapProp_persistently_def).
Proof. by eexists. Qed.
Definition heapProp_persistently := unseal heapProp_persistently_aux.
Definition heapProp_persistently_eq:
  @heapProp_persistently = @heapProp_persistently_def := seal_eq heapProp_persistently_aux.

(** Iris's [bi] class requires the presence of a later modality, but for non
step-indexed logics, it can be defined as the identity. *)
Definition heapProp_later (P : heapProp) : heapProp := P.

Definition unseal_eqs :=
  (heapProp_emp_eq, heapProp_pure_eq, heapProp_and_eq, heapProp_or_eq,
   heapProp_impl_eq, heapProp_forall_eq, heapProp_exist_eq,
   heapProp_sep_eq, heapProp_wand_eq, heapProp_persistently_eq).
Ltac unseal := rewrite !unseal_eqs /=.

Section mixins.
  (** Enable [simpl] locally, which is useful for proofs in the model. *)
  Local Arguments heapProp_holds !_ _ /.

  Lemma heapProp_bi_mixin :
    BiMixin
      heapProp_entails heapProp_emp heapProp_pure heapProp_and heapProp_or
      heapProp_impl (@heapProp_forall) (@heapProp_exist)
      heapProp_sep heapProp_wand heapProp_persistently.
  Proof.
    split.
    - (* [PreOrder heapProp_entails] *)
      split; repeat destruct 1; constructor; naive_solver.
    - (* [P ≡ Q ↔ (P ⊢ Q) ∧ (Q ⊢ P)] *)
      intros P Q; split.
      + intros [HPQ]; split; split; naive_solver.
      + intros [[HPQ] [HQP]]; split; naive_solver.
    - (* [Proper (iff ==> dist n) bi_pure] *)
      unseal=> n φ1 φ2 Hφ; split; naive_solver.
    - (* [NonExpansive2 bi_and] *)
      unseal=> n P1 P2 [HP] Q1 Q2 [HQ]; split; naive_solver.
    - (* [NonExpansive2 bi_or] *)
      unseal=> n P1 P2 [HP] Q1 Q2 [HQ]; split; naive_solver.
    - (* [NonExpansive2 bi_impl] *)
      unseal=> n P1 P2 [HP] Q1 Q2 [HQ]; split; naive_solver.
    - (* [Proper (pointwise_relation _ (dist n) ==> dist n) (bi_forall A)] *)
      unseal=> A n Φ1 Φ2 HΦ; split=> σ /=; split=> ? x; by apply HΦ.
    - (* [Proper (pointwise_relation _ (dist n) ==> dist n) (bi_exist A)] *)
      unseal=> A n Φ1 Φ2 HΦ; split=> σ /=; split=> -[x ?]; exists x; by apply HΦ.
    - (* [NonExpansive2 bi_sep] *)
      unseal=> n P1 P2 [HP] Q1 Q2 [HQ]; split; naive_solver.
    - (* [NonExpansive2 bi_wand] *)
      unseal=> n P1 P2 [HP] Q1 Q2 [HQ]; split; naive_solver.
    - (* [NonExpansive2 bi_persistently] *)
      unseal=> n P1 P2 [HP]; split; naive_solver.
    - (* [φ → P ⊢ ⌜ φ ⌝] *)
      unseal=> φ P ?; by split.
    - (* [(φ → True ⊢ P) → ⌜ φ ⌝ ⊢ P] *)
      unseal=> φ P HP; split=> σ ?. by apply HP.
    - (* [P ∧ Q ⊢ P] *)
      unseal=> P Q; split=> σ [??]; done.
    - (* [P ∧ Q ⊢ Q] *)
      unseal=> P Q; split=> σ [??]; done.
    - (* [(P ⊢ Q) → (P ⊢ R) → P ⊢ Q ∧ R] *)
      unseal=> P Q R [HPQ] [HPR]; split=> σ; split; auto.
    - (* [P ⊢ P ∨ Q] *)
      unseal=> P Q; split=> σ; by left.
    - (* [Q ⊢ P ∨ Q] *)
      unseal=> P Q; split=> σ; by right.
    - (* [(P ⊢ R) → (Q ⊢ R) → P ∨ Q ⊢ R] *)
      unseal=> P Q R [HPQ] [HQR]; split=> σ [?|?]; auto.
    - (* [(P ∧ Q ⊢ R) → P ⊢ Q → R] *)
      unseal=> P Q R HPQR; split=> σ ??. by apply HPQR.
    - (* [(P ⊢ Q → R) → P ∧ Q ⊢ R] *)
      unseal=> P Q R HPQR; split=> σ [??]. by apply HPQR.
    - (* [(∀ a, P ⊢ Ψ a) → P ⊢ ∀ a, Ψ a] *)
      unseal=> A P Ψ HPΨ; split=> σ ? a. by apply HPΨ.
    - (* [(∀ a, Ψ a) ⊢ Ψ a] *)
      unseal=> A Ψ a; split=> σ ?; done.
    - (* [Ψ a ⊢ ∃ a, Ψ a] *)
      unseal=> A Ψ a; split=> σ ?. by exists a.
    - (* [(∀ a, Φ a ⊢ Q) → (∃ a, Φ a) ⊢ Q] *)
      unseal=> A Φ Q HΦQ; split=> σ [a ?]. by apply (HΦQ a).
    - (* [(P ⊢ Q) → (P' ⊢ Q') → P ∗ P' ⊢ Q ∗ Q'] *)
      unseal=> P P' Q Q' [HPQ] [HP'Q']; split; naive_solver.
    - (* [P ⊢ emp ∗ P] *)
      unseal=> P; split=> σ ? /=. eexists ∅, σ. rewrite left_id_L.
      split_and!; done || apply map_disjoint_empty_l.
    - (* [emp ∗ P ⊢ P] *)
      unseal=> P; split; intros ? (?&σ&->&?&->&?). by rewrite left_id_L.
    - (* [P ∗ Q ⊢ Q ∗ P] *)
      unseal=> P Q; split; intros ? (σ1&σ2&->&?&?&?).
      exists σ2, σ1. by rewrite map_union_comm.
    - (* [(P ∗ Q) ∗ R ⊢ P ∗ (Q ∗ R)] *)
      unseal=> P Q R; split; intros ? (?&σ3&->&?&(σ1&σ2&->&?&?&?)&?).
      exists σ1, (σ2 ∪ σ3). split_and!; [by rewrite assoc_L|solve_map_disjoint|done|].
      exists σ2, σ3; split_and!; [done|solve_map_disjoint|done..].
    - (* [(P ∗ Q ⊢ R) → P ⊢ Q -∗ R] *)
      unseal=> P Q R [HPQR]; split=> σ1 ? σ2 ??. apply HPQR. by exists σ1, σ2.
    - (* [(P ⊢ Q -∗ R) → P ∗ Q ⊢ R] *)
      unseal=> P Q R [HPQR]; split; intros ? (σ1&σ2&->&?&?&?). by apply HPQR.
    - (* [(P ⊢ Q) → <pers> P ⊢ <pers> Q] *)
      unseal=> P Q [HPQ]; split=> σ. apply HPQ.
    - (* [<pers> P ⊢ <pers> <pers> P] *)
      unseal=> P; split=> σ; done.
    - (* [emp ⊢ <pers> emp] *)
      unseal; split=> σ; done.
    - (* [(∀ a, <pers> (Ψ a)) ⊢ <pers> (∀ a, Ψ a)] *)
      unseal=> A Ψ; split=> σ; done.
    - (* [<pers> (∃ a, Ψ a) ⊢ ∃ a, <pers> (Ψ a)] *)
      unseal=> A Ψ; split=> σ; done.
    - (* [<pers> P ∗ Q ⊢ <pers> P] *)
      unseal=> P Q; split; intros ? (σ1&σ2&->&?&?&?); done.
    - (* [<pers> P ∧ Q ⊢ P ∗ Q] *)
      unseal=> P Q; split=> σ [??]. eexists ∅, σ. rewrite left_id_L.
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

Instance heapProp_pure_forall : BiPureForall heapPropI.
Proof. intros A φ. rewrite /bi_forall /bi_pure /=. unseal. by split. Qed.

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
