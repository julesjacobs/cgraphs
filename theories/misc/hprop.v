From stdpp Require Import gmap.
From iris.bi Require Import interface.
From iris.proofmode Require Import tactics.
Require Import diris.langdef.
Require Import diris.util.

(** This file constructs a simple non step-indexed linear separation logic as
predicates over heaps (modeled as maps from integer locations to integer values).
It shows that Iris's [bi] canonical structure can be inhabited, and the Iris
proof mode can be used to prove lemmas in this separation logic. *)

Record iProp := h_Prop {
  iProp_holds :> heapT → Prop;
}.
Bind Scope bi_scope with iProp.
Arguments iProp_holds : simpl never.
Add Printing Constructor iProp.

Section ofe.
  Inductive iProp_equiv' (P Q : iProp) : Prop :=
    { iProp_in_equiv : ∀ σ, P σ ↔ Q σ }.
  Instance iProp_equiv : Equiv iProp := iProp_equiv'.
  Instance iProp_equivalence : Equivalence (≡@{iProp}).
  Proof. split; repeat destruct 1; constructor; naive_solver. Qed.
  Canonical Structure iPropO := discreteO iProp.
End ofe.

(** logical entailement *)
Inductive iProp_entails (P Q : iProp) : Prop :=
  { iProp_in_entails : ∀ σ, P σ → Q σ }.

(** logical connectives *)
Definition iProp_emp_def : iProp :=
  {| iProp_holds σ := σ = ∅ |}.
Definition iProp_emp_aux : seal (@iProp_emp_def). Proof. by eexists. Qed.
Definition iProp_emp := unseal iProp_emp_aux.
Definition iProp_emp_eq :
  @iProp_emp = @iProp_emp_def := seal_eq iProp_emp_aux.

Definition iProp_has_type_def (l : endpoint) (t : chan_type) : iProp :=
  {| iProp_holds σ := σ = {[ l := t ]} |}.
Definition iProp_has_type_aux : seal (@iProp_has_type_def). Proof. by eexists. Qed.
Definition iProp_has_type := unseal iProp_has_type_aux.
Definition iProp_has_type_eq :
  @iProp_has_type = @iProp_has_type_def := seal_eq iProp_has_type_aux.

Definition iProp_pure_def (φ : Prop) : iProp :=
  {| iProp_holds _ := φ |}.
Definition iProp_pure_aux : seal (@iProp_pure_def). Proof. by eexists. Qed.
Definition iProp_pure := unseal iProp_pure_aux.
Definition iProp_pure_eq :
  @iProp_pure = @iProp_pure_def := seal_eq iProp_pure_aux.

Definition iProp_own_def (σ : gmap endpoint chan_type) : iProp :=
  {| iProp_holds σ' := σ' = σ |}.
Definition iProp_own_aux : seal (@iProp_own_def). Proof. by eexists. Qed.
Definition iProp_own := unseal iProp_own_aux.
Definition iProp_own_eq :
  @iProp_own= @iProp_own_def := seal_eq iProp_own_aux.

Definition own (σ : gmap endpoint chan_type) : iProp := iProp_own_def σ.

Definition iProp_and_def (P Q : iProp) : iProp :=
  {| iProp_holds σ := P σ ∧ Q σ |}.
Definition iProp_and_aux : seal (@iProp_and_def). Proof. by eexists. Qed.
Definition iProp_and := unseal iProp_and_aux.
Definition iProp_and_eq:

@iProp_and = @iProp_and_def := seal_eq iProp_and_aux.
Definition iProp_or_def (P Q : iProp) : iProp :=
  {| iProp_holds σ := P σ ∨ Q σ |}.
Definition iProp_or_aux : seal (@iProp_or_def). Proof. by eexists. Qed.
Definition iProp_or := unseal iProp_or_aux.
Definition iProp_or_eq:
  @iProp_or = @iProp_or_def := seal_eq iProp_or_aux.

Definition iProp_impl_def (P Q : iProp) : iProp :=
  {| iProp_holds σ := P σ → Q σ |}.
Definition iProp_impl_aux : seal (@iProp_impl_def). Proof. by eexists. Qed.
Definition iProp_impl := unseal iProp_impl_aux.
Definition iProp_impl_eq :
  @iProp_impl = @iProp_impl_def := seal_eq iProp_impl_aux.

Definition iProp_forall_def {A} (Ψ : A → iProp) : iProp :=
  {| iProp_holds σ := ∀ a, Ψ a σ |}.
Definition iProp_forall_aux : seal (@iProp_forall_def). Proof. by eexists. Qed.
Definition iProp_forall {A} := unseal iProp_forall_aux A.
Definition iProp_forall_eq :
  @iProp_forall = @iProp_forall_def := seal_eq iProp_forall_aux.

Definition iProp_exist_def {A} (Ψ : A → iProp) : iProp :=
  {| iProp_holds σ := ∃ a, Ψ a σ |}.
Definition iProp_exist_aux : seal (@iProp_exist_def). Proof. by eexists. Qed.
Definition iProp_exist {A} := unseal iProp_exist_aux A.
Definition iProp_exist_eq :
  @iProp_exist = @iProp_exist_def := seal_eq iProp_exist_aux.

Definition iProp_sep_def (P Q : iProp) : iProp :=
  {| iProp_holds σ := ∃ σ1 σ2, σ = σ1 ∪ σ2 ∧ σ1 ##ₘ σ2 ∧ P σ1 ∧ Q σ2 |}.
Definition iProp_sep_aux : seal (@iProp_sep_def). Proof. by eexists. Qed.
Definition iProp_sep := unseal iProp_sep_aux.
Definition iProp_sep_eq:
  @iProp_sep = @iProp_sep_def := seal_eq iProp_sep_aux.

Definition iProp_wand_def (P Q : iProp) : iProp :=
  {| iProp_holds σ := ∀ σ', σ ##ₘ σ' → P σ' → Q (σ ∪ σ') |}.
Definition iProp_wand_aux : seal (@iProp_wand_def). Proof. by eexists. Qed.
Definition iProp_wand := unseal iProp_wand_aux.
Definition iProp_wand_eq:
  @iProp_wand = @iProp_wand_def := seal_eq iProp_wand_aux.

Definition iProp_persistently_def (P : iProp) : iProp :=
  {| iProp_holds σ := P ∅ |}.
Definition iProp_persistently_aux : seal (@iProp_persistently_def).
Proof. by eexists. Qed.
Definition iProp_persistently := unseal iProp_persistently_aux.
Definition iProp_persistently_eq:
  @iProp_persistently = @iProp_persistently_def := seal_eq iProp_persistently_aux.

(** Iris's [bi] class requires the presence of a later modality, but for non
step-indexed logics, it can be defined as the identity. *)
Definition iProp_later (P : iProp) : iProp := P.

Definition unseal_eqs :=
  (iProp_emp_eq, iProp_pure_eq, iProp_and_eq, iProp_or_eq,
   iProp_impl_eq, iProp_forall_eq, iProp_exist_eq,
   iProp_sep_eq, iProp_wand_eq, iProp_persistently_eq).
Ltac unseal := rewrite !unseal_eqs /=.

Section mixins.
  (** Enable [simpl] locally, which is useful for proofs in the model. *)
  Local Arguments iProp_holds !_ _ /.

  Lemma iProp_bi_mixin :
    BiMixin
      iProp_entails iProp_emp iProp_pure iProp_and iProp_or
      iProp_impl (@iProp_forall) (@iProp_exist)
      iProp_sep iProp_wand iProp_persistently.
  Proof.
    split.
    - (* [PreOrder iProp_entails] *)
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

  Lemma iProp_bi_later_mixin :
    BiLaterMixin
      iProp_entails iProp_pure iProp_or iProp_impl
      (@iProp_forall) (@iProp_exist)
      iProp_sep iProp_persistently iProp_later.
  Proof. eapply bi_later_mixin_id; [done|apply iProp_bi_mixin]. Qed.
End mixins.

Canonical Structure iPropI : bi :=
  {| bi_ofe_mixin := ofe_mixin_of iProp;
     bi_bi_mixin := iProp_bi_mixin; bi_bi_later_mixin := iProp_bi_later_mixin |}.

Instance iProp_pure_forall : BiPureForall iPropI.
Proof. intros A φ. rewrite /bi_forall /bi_pure /=. unseal. by split. Qed.

Lemma iProp_proofmode_test {A} (P Q R : iProp) (Φ Ψ : A → iProp) :
  P ∗ Q -∗
  □ R -∗
  □ (R -∗ ∃ x, Φ x) -∗
  ∃ x, Φ x ∗ Φ x ∗ P ∗ Q.
Proof.
  iIntros "[HP HQ] #HR #HRΦ".
  iDestruct ("HRΦ" with "HR") as (x) "#HΦ".
  iExists x. iFrame. by iSplitL.
Qed.
