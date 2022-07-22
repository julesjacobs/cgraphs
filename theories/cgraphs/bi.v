From iris.bi Require Export derived_connectives.
From cgraphs.cgraphs Require Export upred.
From iris.prelude Require Import options.
From iris Require Import bi.extensions.
Import uPred_primitive.

(** BI instances for [uPred], and re-stating the remaining primitive laws in
terms of the BI interface. This file does *not* unseal. *)

Notation "⌜⌜ p ⌝⌝" := (<affine> ⌜ p ⌝)%I : bi_scope.

Local Existing Instance entails_po.

Lemma uPred_bi_mixin (M : ucmra) :
  BiMixin
    uPred_entails uPred_emp uPred_pure uPred_and uPred_or uPred_impl
    (@uPred_forall M) (@uPred_exist M) uPred_sep uPred_wand
    uPred_persistently.
Proof.
  split.
  - exact: entails_po.
  - exact: equiv_spec.
  - exact: pure_ne.
  - exact: and_ne.
  - exact: or_ne.
  - exact: impl_ne.
  - exact: forall_ne.
  - exact: exist_ne.
  - exact: sep_ne.
  - exact: wand_ne.
  - exact: persistently_ne.
  - exact: pure_intro.
  - exact: pure_elim'.
  - exact: and_elim_l.
  - exact: and_elim_r.
  - exact: and_intro.
  - exact: or_intro_l.
  - exact: or_intro_r.
  - exact: or_elim.
  - exact: impl_intro_r.
  - exact: impl_elim_l'.
  - exact: @forall_intro.
  - exact: @forall_elim.
  - exact: @exist_intro.
  - exact: @exist_elim.
  - exact: sep_mono.
  - exact: emp_sep_1.
  - exact: emp_sep_2.
  - exact: sep_comm'.
  - exact: sep_assoc'.
  - exact: wand_intro_r.
  - exact: wand_elim_l'.
  - exact: persistently_mono.
  - exact: persistently_idemp_2.
  - exact: persistently_emp_2.
  - exact: persistently_and_2.
  - exact: @persistently_exist_1.
  - exact: persistently_absorbing.
  - exact: persistently_and_sep_elim.
Qed.

Definition uPred_later {M : ucmra} (P : uPred M) := P.

Lemma uPred_bi_later_mixin (M : ucmra) :
  BiLaterMixin
    uPred_entails uPred_pure uPred_or uPred_impl
    (@uPred_forall M) (@uPred_exist M) uPred_sep uPred_persistently uPred_later.
Proof.
  eapply bi_later_mixin_id; eauto.
  apply uPred_bi_mixin.
Qed.

Canonical Structure uPredI (M : ucmra) : bi :=
  {| bi_ofe_mixin := ofe_mixin_of (uPred M);
     bi_bi_mixin := uPred_bi_mixin M;
     bi_bi_later_mixin := uPred_bi_later_mixin M |}.

Global Instance uPred_pure_forall M : BiPureForall (uPredI M).
Proof. exact: @pure_forall_2. Qed.

(** Re-state/export lemmas about Iris-specific primitive connectives (own, valid) *)

Module uPred.

Section restate.
Context {M : ucmra}.
Implicit Types φ : Prop.
Implicit Types P Q : uPred M.
Implicit Types A : Type.

(* Force implicit argument M *)
Notation "P ⊢ Q" := (bi_entails (PROP:=uPredI M) P%I Q%I).
Notation "P ⊣⊢ Q" := (equiv (A:=uPredI M) P%I Q%I).


(** Consistency/soundness statement *)
Lemma pure_soundness φ : (⊢@{uPredI M} ⌜ φ ⌝) → φ.
Proof. apply pure_soundness. Qed.

Global Instance ownM_proper : Proper ((≡) ==> (≡)) (@uPred_ownM M).
Proof. apply ownM_proper. Qed.

Lemma ownM_unit : uPred_ownM ε ⊣⊢ emp.
Proof. apply ownM_unit. Qed.

Lemma ownM_op (a1 a2 : M) :
  uPred_ownM (a1 ⋅ a2) ⊣⊢ uPred_ownM a1 ∗ uPred_ownM a2.
Proof. apply ownM_op. Qed.

Lemma ownM_valid (x : M) :
  uPred_ownM x ⊢ ⌜ ✓ x ⌝.
Proof. apply ownM_valid. Qed.

End restate.

(** New unseal tactic that also unfolds the BI layer.
    This is used by [base_logic.bupd_alt].
    TODO: Can we get rid of this? *)
Ltac unseal := (* Coq unfold is used to circumvent bug #5699 in rewrite /foo *)
  unfold bi_emp, bi_pure,
    bi_and, bi_or, bi_impl, bi_forall, bi_exist,
    bi_sep, bi_wand, bi_persistently, bi_later; simpl;
  unfold uPred_later; simpl;
  uPred_primitive.unseal.

End uPred.

(* Should go to upred primitive *)
Section upred_lemmas.
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
Lemma uPred_false_holds x :
  (False : uPred A)%I x -> False.
Proof. by uPred.unseal. Qed.
End upred_lemmas.