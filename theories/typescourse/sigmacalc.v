From iris.proofmode Require Import tactics.
Ltac inv H := inversion H; clear H; simplify_eq; simpl in *.

Inductive expr :=
  | Var : nat -> expr
  | App : expr -> expr -> expr
  | Lam : expr -> expr.

Definition s_id := λ n, Var n.

Definition s_cons (t : expr) (σ : nat -> expr) :=
  λ n, match n with 0 => t | S n => σ n end.

Notation "t ⋅ s" := (s_cons t s) (at level 20, right associativity).

Fixpoint s_subst (σ : nat -> expr) (e : expr) :=
  match e with
  | Var n => σ n
  | App e1 e2 => App (s_subst σ e1) (s_subst σ e2)
  | Lam e => Lam (s_subst (Var 0 ⋅ σ) e)
  end.

Notation "[ s ] e" := (s_subst s e) (at level 11, right associativity).

Definition s_comp (σ : nat -> expr) (τ : nat -> expr) : (nat -> expr) :=
  λ n, s_subst σ (τ n).

Notation "s ∘ r" := (s_comp s r).

Definition s_up := λ n, Var (S n).

Notation "↑↑" := s_up.

Axiom s_funext : ∀ (σ τ : nat -> expr), (∀ n, σ n = τ n) -> σ = τ.

Lemma r1 σ a b :
  [σ] (App a b) = App ([σ] a) ([σ] b).
Proof. done. Qed.

Lemma r2 e σ :
  [σ] (Lam e) = Lam ([Var 0 ⋅ σ ∘ ↑↑] e).
Proof. Admitted.

Lemma r3 e σ :
  [e ⋅ σ] (Var 0) = e.
Proof. done. Qed.

Lemma r4 e σ :
  (e ⋅ σ) ∘ ↑↑ = σ.
Proof. done. Qed.

Lemma r5 e : [s_id] e = e.
Proof. Admitted.

Lemma r6 σ :
  ([σ] Var 0) ⋅ (σ ∘ ↑↑) = σ.
Proof. Admitted.

Lemma r7 σ :
  s_id ∘ σ = σ.
Proof. apply s_funext. intro. unfold s_comp. by rewrite r5. Qed.

Lemma r8 σ :
  σ ∘ s_id = σ.
Proof. by apply s_funext. Qed.

Lemma r9 σ τ θ :
  (σ ∘ τ) ∘ θ = σ ∘ (τ ∘ θ).
Proof. apply s_funext. intro. unfold s_comp.
  induction (θ n); simpl.
  - done.
  - by rewrite IHe1 IHe2.
  - f_equal. admit.
Admitted.

Lemma r10 e σ τ :
  (e ⋅ σ) ∘ τ = [τ] e ⋅ σ ∘ τ.
Proof. Admitted.

Lemma r11 e σ τ :
  [σ] [τ] e = [σ ∘ τ] e.
Proof. Admitted.

Lemma r12 :
  Var 0 ⋅ ↑↑ = s_id.
Proof. Admitted.