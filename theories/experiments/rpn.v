From iris Require Import bi.

Inductive exp :=
  | Var (n : nat) | Lit (n : nat)
  | Op (f : nat -> nat -> nat) (e1 e2 : exp).

Fixpoint eval v e :=
  match e with
  | Var n => v n | Lit n => n
  | Op f e1 e2 => f (eval v e1) (eval v e2)
  end.

Inductive op := VarR (n : nat) | LitR (n : nat) | OpR (f : nat -> nat -> nat).

Definition rpn_eval1 v (s : option (list nat)) (o : op) :=
  match o,s with
  | VarR n,Some s => Some (v n::s)
  | LitR n,Some s => Some (n::s)
  | OpR f, Some (n::m::s) => Some (f m n::s)
  | _,_ => None
  end.
Definition rpn_eval v s := foldl (rpn_eval1 v) (Some s).

Fixpoint to_rpn (e : exp) :=
  match e with
  | Var n => [VarR n] | Lit n => [LitR n]
  | Op f e1 e2 => to_rpn e1 ++ to_rpn e2 ++ [OpR f]
  end.

Lemma rpn_eval_to_rpn v s e ops :
  rpn_eval v s (to_rpn e ++ ops) = rpn_eval v (eval v e::s) ops.
Proof.
  revert s ops; induction e; intros; rewrite //= -!assoc IHe1 IHe2 //.
Qed.

Lemma rpn_eval_to_rpn' v e :
  rpn_eval v [] (to_rpn e) = Some [eval v e].
Proof.
  rewrite -(right_id_L _ app (to_rpn e)) rpn_eval_to_rpn //.
Qed.