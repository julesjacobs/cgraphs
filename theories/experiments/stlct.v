From iris Require Import bi.

Inductive ty := Base | Fun (t1 t2 : ty).
Inductive tm := Var (n : nat) | App (e1 e2 : tm) | Lam (t : ty) (e : tm).

Lemma ty_dec (a b : ty) : {a = b} + {a ≠ b}.
Proof. decide equality. Qed.

Inductive typed : list ty -> tm -> ty -> Prop :=
  | Var_ty Γ n t :
      Γ !! n = Some t -> typed Γ (Var n) t
  | App_ty Γ e1 e2 t1 t2 :
      typed Γ e1 (Fun t1 t2) -> typed Γ e2 t1 -> typed Γ (App e1 e2) t2
  | Lam_ty Γ e t1 t2 :
      typed (t1::Γ) e t2 -> typed Γ (Lam t1 e) (Fun t1 t2).

Fixpoint check (Γ : list ty) (e : tm) : option ty :=
  match e with
  | Var n => Γ !! n
  | App e1 e2 =>
      match check Γ e1, check Γ e2 with
      | Some (Fun t1 t2), Some t1' =>
          match ty_dec t1 t1' with
          | left _ => Some t2
          | right _ => None
          end
      | _,_ => None
      end
  | Lam t1 e =>
      match check (t1::Γ) e with
      | Some t2 => Some (Fun t1 t2)
      | None => None
      end
  end.

Lemma typed_check Γ e t : typed Γ e t <-> check Γ e = Some t.
Proof.
  split.
  - induction 1; simpl; rewrite ?IHtyped1 ?IHtyped2 ?IHtyped; eauto.
    destruct (ty_dec t1 t1); simplify_eq. eauto.
  - revert Γ t; induction e; intros ??; simpl;
    repeat match goal with
    | |- context[match ?x with _ => _ end] => destruct x eqn:?
    end; intros; simplify_eq; eauto using typed.
Qed.