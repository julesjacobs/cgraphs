From iris.proofmode Require Import tactics.
Ltac inv H := inversion H; clear H; simplify_eq; simpl in *.

Inductive expr :=
  | EUnit : expr
  | EVar : string -> expr
  | ELam : string -> expr -> expr
  | EApp : expr -> expr -> expr
  | EPi : expr -> expr -> expr.
