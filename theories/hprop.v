From stdpp Require Import gmap.
From iris.bi Require Import interface.
From iris.proofmode Require Import tactics.
Require Import diris.langdef.
Require Import diris.util.

(** This file constructs a simple non step-indexed linear separation logic as
predicates over heaps (modeled as maps from integer locations to integer values).
It shows that Iris's [bi] canonical structure can be inhabited, and the Iris
proof mode can be used to prove lemmas in this separation logic. *)

Record hProp := h_Prop {
  hProp_holds :> gmap endpoint chan_type → Prop;
}.
Arguments hProp_holds : simpl never.
Add Printing Constructor hProp.

Section ofe.
  Inductive hProp_equiv' (P Q : hProp) : Prop :=
    { hProp_in_equiv : ∀ σ, P σ ↔ Q σ }.
  Instance hProp_equiv : Equiv hProp := hProp_equiv'.
  Instance hProp_equivalence : Equivalence (≡@{hProp}).
  Proof. split; repeat destruct 1; constructor; naive_solver. Qed.
  Canonical Structure hPropO := discreteO hProp.
End ofe.

(** logical entailement *)
Inductive hProp_entails (P Q : hProp) : Prop :=
  { hProp_in_entails : ∀ σ, P σ → Q σ }.

(** logical connectives *)
Definition hProp_emp_def : hProp :=
  {| hProp_holds σ := σ = ∅ |}.
Definition hProp_emp_aux : seal (@hProp_emp_def). Proof. by eexists. Qed.
Definition hProp_emp := unseal hProp_emp_aux.
Definition hProp_emp_eq :
  @hProp_emp = @hProp_emp_def := seal_eq hProp_emp_aux.

Definition hProp_has_type_def (l : endpoint) (t : chan_type) : hProp :=
  {| hProp_holds σ := σ = {[ l := t ]} |}.
Definition hProp_has_type_aux : seal (@hProp_has_type_def). Proof. by eexists. Qed.
Definition hProp_has_type := unseal hProp_has_type_aux.
Definition hProp_has_type_eq :
  @hProp_has_type = @hProp_has_type_def := seal_eq hProp_has_type_aux.

Definition hProp_pure_def (φ : Prop) : hProp :=
  {| hProp_holds _ := φ |}.
Definition hProp_pure_aux : seal (@hProp_pure_def). Proof. by eexists. Qed.
Definition hProp_pure := unseal hProp_pure_aux.
Definition hProp_pure_eq :
  @hProp_pure = @hProp_pure_def := seal_eq hProp_pure_aux.

Definition hProp_and_def (P Q : hProp) : hProp :=
  {| hProp_holds σ := P σ ∧ Q σ |}.
Definition hProp_and_aux : seal (@hProp_and_def). Proof. by eexists. Qed.
Definition hProp_and := unseal hProp_and_aux.
Definition hProp_and_eq:

@hProp_and = @hProp_and_def := seal_eq hProp_and_aux.
Definition hProp_or_def (P Q : hProp) : hProp :=
  {| hProp_holds σ := P σ ∨ Q σ |}.
Definition hProp_or_aux : seal (@hProp_or_def). Proof. by eexists. Qed.
Definition hProp_or := unseal hProp_or_aux.
Definition hProp_or_eq:
  @hProp_or = @hProp_or_def := seal_eq hProp_or_aux.

Definition hProp_impl_def (P Q : hProp) : hProp :=
  {| hProp_holds σ := P σ → Q σ |}.
Definition hProp_impl_aux : seal (@hProp_impl_def). Proof. by eexists. Qed.
Definition hProp_impl := unseal hProp_impl_aux.
Definition hProp_impl_eq :
  @hProp_impl = @hProp_impl_def := seal_eq hProp_impl_aux.

Definition hProp_forall_def {A} (Ψ : A → hProp) : hProp :=
  {| hProp_holds σ := ∀ a, Ψ a σ |}.
Definition hProp_forall_aux : seal (@hProp_forall_def). Proof. by eexists. Qed.
Definition hProp_forall {A} := unseal hProp_forall_aux A.
Definition hProp_forall_eq :
  @hProp_forall = @hProp_forall_def := seal_eq hProp_forall_aux.

Definition hProp_exist_def {A} (Ψ : A → hProp) : hProp :=
  {| hProp_holds σ := ∃ a, Ψ a σ |}.
Definition hProp_exist_aux : seal (@hProp_exist_def). Proof. by eexists. Qed.
Definition hProp_exist {A} := unseal hProp_exist_aux A.
Definition hProp_exist_eq :
  @hProp_exist = @hProp_exist_def := seal_eq hProp_exist_aux.

Definition hProp_sep_def (P Q : hProp) : hProp :=
  {| hProp_holds σ := ∃ σ1 σ2, σ = σ1 ∪ σ2 ∧ σ1 ##ₘ σ2 ∧ P σ1 ∧ Q σ2 |}.
Definition hProp_sep_aux : seal (@hProp_sep_def). Proof. by eexists. Qed.
Definition hProp_sep := unseal hProp_sep_aux.
Definition hProp_sep_eq:
  @hProp_sep = @hProp_sep_def := seal_eq hProp_sep_aux.

Definition hProp_wand_def (P Q : hProp) : hProp :=
  {| hProp_holds σ := ∀ σ', σ ##ₘ σ' → P σ' → Q (σ ∪ σ') |}.
Definition hProp_wand_aux : seal (@hProp_wand_def). Proof. by eexists. Qed.
Definition hProp_wand := unseal hProp_wand_aux.
Definition hProp_wand_eq:
  @hProp_wand = @hProp_wand_def := seal_eq hProp_wand_aux.

Definition hProp_persistently_def (P : hProp) : hProp :=
  {| hProp_holds σ := P ∅ |}.
Definition hProp_persistently_aux : seal (@hProp_persistently_def).
Proof. by eexists. Qed.
Definition hProp_persistently := unseal hProp_persistently_aux.
Definition hProp_persistently_eq:
  @hProp_persistently = @hProp_persistently_def := seal_eq hProp_persistently_aux.

(** Iris's [bi] class requires the presence of a later modality, but for non
step-indexed logics, it can be defined as the identity. *)
Definition hProp_later (P : hProp) : hProp := P.

Definition unseal_eqs :=
  (hProp_emp_eq, hProp_pure_eq, hProp_and_eq, hProp_or_eq,
   hProp_impl_eq, hProp_forall_eq, hProp_exist_eq,
   hProp_sep_eq, hProp_wand_eq, hProp_persistently_eq).
Ltac unseal := rewrite !unseal_eqs /=.

Section mixins.
  (** Enable [simpl] locally, which is useful for proofs in the model. *)
  Local Arguments hProp_holds !_ _ /.

  Lemma hProp_bi_mixin :
    BiMixin
      hProp_entails hProp_emp hProp_pure hProp_and hProp_or
      hProp_impl (@hProp_forall) (@hProp_exist)
      hProp_sep hProp_wand hProp_persistently.
  Proof.
    split.
    - (* [PreOrder hProp_entails] *)
      split; repeat destruct 1; constructor; naive_solver.
    - (* [P ≡ Q ↔ (P ⊢ Q) ∧ (Q ⊢ P)] *)
      intros P Q; split.
      + intros [HPQ]; split; split; naive_solver.
      + intros [[HPQ] [HQP]]; split; naive_solver.
    - (* [Proper (iff ==> dist n) bi_pure] *)
      unseal=> n φ1 φ2 Hφ; split; naive_solver.
    - (* [NonExpansive2 bi_and] *)
      unseal=> n P1 P2 [HP] Q1 Q2 [HQ]; split. naive_solver.
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

  Lemma hProp_bi_later_mixin :
    BiLaterMixin
      hProp_entails hProp_pure hProp_or hProp_impl
      (@hProp_forall) (@hProp_exist)
      hProp_sep hProp_persistently hProp_later.
  Proof. eapply bi_later_mixin_id; [done|apply hProp_bi_mixin]. Qed.
End mixins.

Canonical Structure hPropI : bi :=
  {| bi_ofe_mixin := ofe_mixin_of hProp;
     bi_bi_mixin := hProp_bi_mixin; bi_bi_later_mixin := hProp_bi_later_mixin |}.

Instance hProp_pure_forall : BiPureForall hPropI.
Proof. intros A φ. rewrite /bi_forall /bi_pure /=. unseal. by split. Qed.

Lemma hProp_proofmode_test {A} (P Q R : hProp) (Φ Ψ : A → hProp) :
  P ∗ Q -∗
  □ R -∗
  □ (R -∗ ∃ x, Φ x) -∗
  ∃ x, Φ x ∗ Φ x ∗ P ∗ Q.
Proof.
  iIntros "[HP HQ] #HR #HRΦ".
  iDestruct ("HRΦ" with "HR") as (x) "#HΦ".
  iExists x. iFrame. by iSplitL.
Qed.
