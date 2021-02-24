From iris.proofmode Require Import tactics.
Require Import Autosubst.Autosubst.

Inductive term :=
  | YN (x : bool)
  | Var (x : var)
  | App (a b : term)
  | Lam (a : {bind term}).

Instance Ids_term : Ids term. derive. Defined.
Instance Rename_term : Rename term. derive. Defined.
Instance Subst_term : Subst term. derive. Defined.
Instance SubstLemmas_term : SubstLemmas term. derive. Qed.

Inductive step : term -> term -> Prop :=
  | Step_beta a b x :
      a.[x/] = b -> step (App (Lam a) x) b
  | Step_appL a b x :
      step a b -> step (App a x) (App b x)
  | Step_appR a b x :
      step a b -> step (App x a) (App x b)
  | Step_lam a b :
      step a b -> step (Lam a) (Lam b).

Lemma subst_step a b :
  step a b -> ∀ σ, step a.[σ] b.[σ].
Proof. induction 1; constructor; subst; autosubst. Qed.

Inductive type := T2 | TFun (a b : type).

Inductive ty : (var -> type) -> term -> type -> Prop :=
  | Typ_var Γ x A :
      Γ x = A ->
      ty Γ (Var x) A
  | Ty_lam Γ e A B :
      ty (A .: Γ) e B ->
      ty Γ (Lam e) (TFun A B)
  | Ty_app Γ e1 e2 A B :
      ty Γ e1 (TFun A B) ->
      ty Γ e2 A ->
      ty Γ (App e1 e2) B.

Lemma ty_rename Γ e A :
  ty Γ e A -> ∀ Δ ξ,
  Γ = ξ >>> Δ ->
  ty Δ e.[ren ξ] A.
Proof.
  induction 1; intros; subst; eauto using ty.
  econstructor. asimpl. eapply IHty. autosubst.
Qed.

Lemma ty_subst Γ e A :
  ty Γ e A -> ∀ σ Δ,
  (∀ x, ty Δ (σ x) (Γ x)) ->
  ty Δ e.[σ] A.
Proof.
  induction 1; simpl; intros; subst; eauto using ty.
  econstructor. eapply IHty. intros []; asimpl; eauto using ty, ty_rename.
Qed.

Lemma ty_preservation Γ e A :
  ty Γ e A -> ∀ e',
  step e e' ->
  ty Γ e' A.
Proof.
  induction 1; intros e' H_step; inversion H_step; ainv; eauto using ty.
  eapply ty_subst; [|intros []]; eauto using ty.
Qed.

Definition neutral (e : term) := False.

(* We need to do this with notation because Coq doesn't like the
   mutual recursion. *)
Notation HTe H e T := (∃ e', rtc step e e' ∧ H e' T).

Fixpoint HTv e T := neutral e ∨
  match T with
  | T2 => ∃ b, e = YN b
  | TFun A B => ∃ e', e = Lam e' ∧
      ∀ x, HTe HTv x A -> HTe HTv (e'.[x/]) B
  end.

Definition env_HT (γ : var -> term) (Γ : var -> type) :=
  ∀ x, HTe HTv (γ x) (Γ x).

Lemma main Γ e T : ty Γ e T -> ∀ γ, env_HT γ Γ -> HTe HTv (e.[γ]) T.
Proof.
  induction 1; subst; intros; asimpl.
  - apply H.
  - edestruct IHty. admit.
  - edestruct IHty1; eauto.
    edestruct IHty2; eauto.
    simpl in *.


