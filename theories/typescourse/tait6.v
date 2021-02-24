From iris.proofmode Require Import tactics.
Ltac inv H := inversion H; clear H; simplify_eq; simpl in *.
Axiom funext : ∀ A B (f g : A -> B), (∀ a, f a = g a) -> f = g.

Inductive expr :=
  | YN : bool -> expr
  | Var : nat -> expr (* De Bruijn *)
  | App : expr -> expr -> expr
  | Lam : expr -> expr.

(* We use σ-calculus to handle substitution *)

Definition liftR σ :=
  λ n,
    match n with
    | 0 => 0
    | S n => S (σ n)
    end.

Fixpoint rename σ e :=
  match e with
  | YN b => YN b
  | Var n => Var (σ n)
  | App e1 e2 => App (rename σ e1) (rename σ e2)
  | Lam e => Lam (rename (liftR σ) e)
  end.

Lemma liftR_comp σ1 σ2 :
  liftR (σ1 ∘ σ2) = liftR σ1 ∘ liftR σ2.
Proof.
  apply funext. by intros [].
Qed.

Lemma rename_rename σ1 σ2 e :
  rename σ1 (rename σ2 e) = rename (σ1 ∘ σ2) e.
Proof.
  revert σ1 σ2. induction e; intros;
  rewrite /= ?IHe1 ?IHe2 // IHe liftR_comp //.
Qed.

Definition shift e (γ : nat -> expr) n :=
  match n with
  | 0 => e
  | S n => γ n
  end.

Definition lift γ := shift (Var 0) (rename S ∘ γ).

Fixpoint subst (γ : nat -> expr) (e : expr) : expr :=
  match e with
  | YN b => YN b
  | Var n => γ n
  | App e1 e2 => App (subst γ e1) (subst γ e2)
  | Lam e => Lam (subst (lift γ) e)
  end.

Lemma rename_subst σ :
  rename σ = subst (Var ∘ σ).
Proof.
  apply funext. intros e.
  revert σ. induction e; intros;
  rewrite /= ?IHe1 ?IHe2 // IHe /lift.
  do 2 f_equal. apply funext. by intros [].
Qed.

Lemma lift_Var : lift Var = Var.
Proof.
  apply funext. by intros [].
Qed.

Lemma subst_Var :
  subst Var = id.
Proof.
  apply funext. intros e. induction e;
  rewrite /= ?IHe1 ?IHe2 // lift_Var IHe //.
Qed.

Lemma rename_subst_comp γ σ e :
  subst γ (rename σ e) = subst (γ ∘ σ) e.
Proof.
  revert γ σ. induction e; intros;
  rewrite /= // ?IHe1 ?IHe2 // IHe.
  do 2 f_equal. apply funext. by intros [].
Qed.

Lemma subst_rename_comp γ σ e :
  rename σ (subst γ e) = subst (rename σ ∘ γ) e.
Proof.
  revert γ σ. induction e; intros;
  rewrite /= // ?IHe1 ?IHe2 // IHe.
  do 2 f_equal. apply funext. intros [];
  rewrite /= // !rename_rename //.
Qed.

Lemma comp_subst γ1 γ2 :
  subst (subst γ1 ∘ γ2) = subst γ1 ∘ subst γ2.
Proof.
  apply funext. intros e. simpl.
  revert γ1 γ2. induction e; intros;
  rewrite /= ?IHe1 ?IHe2 // -IHe.
  do 2 f_equal. apply funext. intros [];
  rewrite // /= rename_subst_comp subst_rename_comp //.
Qed.

Inductive step : expr -> expr -> Prop :=
  | Step_beta x e e':
      e' = subst (shift x Var) e ->
      step (App (Lam e) x) e'
  | Step_App_l x x' e :
      step x x' ->
      step (App x e) (App x' e)
  | Step_App_r x x' e :
      step x x' ->
      step (App e x) (App e x')
  | Step_Lam x x' :
      step x x' ->
      step (Lam x) (Lam x').

Lemma subst_comp_shift e γ1 γ2 :
  subst γ1 ∘ (shift e γ2) = shift (subst γ1 e) (subst γ1 ∘ γ2).
Proof.
  apply funext. by intros [].
Qed.

Lemma subst_shift_Var0 e γ :
  subst (shift e γ) (Var 0) = e.
Proof. done. Qed.

Lemma shift_comp_up e γ :
  subst (shift e γ) ∘ up = γ.
Proof.
  done.
Qed.

Lemma subst_comp_subst γ1 γ2 :
  subst γ1 ∘ subst γ2 = subst (subst γ1 ∘ γ2).
Proof.
Admitted.

Lemma comp_assoc' {A B C D} (γ3 : A -> B) (γ2 : B -> C) (γ1 : C -> D) :
  γ1 ∘ (γ2 ∘ γ3) = (γ1 ∘ γ2) ∘ γ3.
Proof.
  done.
Qed.

Lemma subst_Var_comp_l (γ : nat -> expr) :
  subst Var ∘ γ = γ.
Proof.
  by rewrite subst_Var.
Qed.

Lemma subst_Var_comp_r γ :
  subst γ ∘ Var = γ.
Proof.
  done.
Qed.

Lemma step_subst x x' :
  step x x' -> ∀ γ, step (subst γ x) (subst γ x').
Proof.
  induction 1; constructor; subst; fold subst; eauto.
  unfold lift. rewrite !subst_subst.
  rewrite !subst_comp_shift.
  rewrite subst_shift_Var0.
  rewrite inc_subst.
  rewrite comp_assoc'.
  rewrite subst_comp_subst.
  rewrite shift_comp_up.
  rewrite subst_Var_comp_l.
  rewrite subst_Var_comp_r.
  done.
Qed.