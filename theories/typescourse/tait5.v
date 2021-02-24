From iris.proofmode Require Import tactics.
Ltac inv H := inversion H; clear H; simplify_eq; simpl in *.

Inductive expr :=
  | YN : bool -> expr
  | Var : nat -> expr (* De Bruijn *)
  | App : expr -> expr -> expr
  | Lam : expr -> expr.

(* We use σ-calculus to handle substitution *)

Fixpoint incr k e :=
  match e with
  | YN b => YN b
  | Var n => Var (if decide (k ≤ n) then S n else n)
  | App e1 e2 => App (incr k e1) (incr k e2)
  | Lam e => Lam (incr (S k) e)
  end.

Definition inc := incr 0.

Definition shift e (γ : nat -> expr) n :=
  match n with
  | 0 => e
  | S n => γ n
  end.

Definition lift γ := shift (Var 0) (inc ∘ γ).

Fixpoint subst (γ : nat -> expr) (e : expr) : expr :=
  match e with
  | YN b => YN b
  | Var n => γ n
  | App e1 e2 => App (subst γ e1) (subst γ e2)
  | Lam e => Lam (subst (lift γ) e)
  end.

Definition comp (γ1 γ2 : nat -> expr) := subst γ1 ∘ γ2.

Definition up n := Var (S n).

Axiom funext : ∀ A B (f g : A -> B), (∀ a, f a = g a) -> f = g.

Lemma incr_subst k :
  incr k = subst (λ n, Var (if decide (k ≤ n) then S n else n)).
Proof.
  apply funext. intros e.
  revert k. induction e; intros k; simpl;
  rewrite /lift ?IHe1 ?IHe2 ?IHe //.
  do 2 f_equal. apply funext.
  intros []; rewrite // /inc /=.
  f_equal. repeat case_decide; lia.
Qed.

Lemma inc_subst :
  inc = subst up.
Proof. apply incr_subst. Qed.

Lemma shift_inc f :
  shift (f 0) (f ∘ S) = f.
Proof.
  apply funext. by intros [].
Qed.

Lemma subst_Var :
  subst Var = id.
Proof.
  apply funext. intros e. induction e;
  rewrite /= ?IHe1 ?IHe2 /lift ?shift_inc ?IHe //.
Qed.

Lemma comp_id_l γ :
  comp Var γ = γ.
Proof.
  rewrite /comp subst_Var //.
Qed.

Lemma comp_id_r γ :
  comp γ Var = γ.
Proof.
  done.
Qed.

Lemma comp_up_shift e γ :
  comp (shift e γ) up = γ.
Proof.
  done.
Qed.

Lemma comp_shift e γ1 γ2 :
  comp γ1 (shift e γ2) = shift (subst γ1 e) (comp γ1 γ2).
Proof.
  apply funext. by intros [].
Qed.

Definition shiftN n γ k :=
  if decide (k ≤ n) then Var k else γ (n+k-1).

Definition foo (n : nat) (γ : nat -> expr) :=
  shiftN n (incr n ∘ γ).
(*
(liftN (S n') (lift γ)) = (lift (liftN n' γ))
 *)
Lemma incr_foo n γ e :
  incr n (subst γ e) = subst (foo n γ) (incr n e).
Proof.
  revert n γ; induction e; intros; simpl.
Admitted.

Lemma foo_lift : foo 0 = lift.
Proof.
  rewrite /foo /lift. apply funext. intros.
  rewrite /shiftN. simpl. apply funext. intros.
  case_decide; destruct a0; try lia; try done.
  simpl. rewrite /inc. f_equal. f_equal. lia.
Qed.

Lemma lift_subst γ1 γ2 :
  lift (subst γ1 ∘ γ2) = subst (lift γ1) ∘ lift γ2.
Proof.
  apply funext. intros []; rewrite // /=. rewrite /inc.
  generalize (γ2 n). intros e. rewrite -foo_lift.
  apply incr_foo.
Qed.

Lemma comp_subst γ1 γ2 :
  subst (comp γ1 γ2) = subst γ1 ∘ subst γ2.
Proof.
  unfold comp.
  apply funext. intros e.
  revert γ1 γ2. induction e; intros γ1 γ2; simpl;
  rewrite ?IHe1 ?IHe2 // lift_subst IHe //.
Qed.

Lemma comp_assoc γ1 γ2 γ3 :
  comp (comp γ1 γ2) γ3 = comp γ1 (comp γ2 γ3).
Proof.
  unfold comp. rewrite comp_subst. done.
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

Lemma subst_subst e γ1 γ2 :
  subst γ1 (subst γ2 e) = subst (subst γ1 ∘ γ2) e.
Proof.
Admitted.

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