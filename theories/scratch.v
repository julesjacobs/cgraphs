From iris.proofmode Require Import tactics.


Inductive expr : Type := Zero | Var (x : string) | Succ (a : expr) | Add (a b : expr).

(* Fixpoint f (x : expr) : expr :=
    match x with
    | Add (Succ a) b => f (Succ (f (Add a b)))
    | y => y
    end. *)

Fixpoint f_Add a b :=
    match a with
    | Succ a => Succ (f_Add a b)
    | _ => Add a b
    end.

Fixpoint f (x : expr) : expr :=
    match x with
    | Add (Succ a) b => Succ (f_Add a b)
    | y => y
    end.