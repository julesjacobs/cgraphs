From cgraphs.locks Require Export langdef.

(* In this file we demonstrate how typed macros work. *)
(* We define a macro for let in terms of function application and lambda. *)

Definition Let x e1 e2 := App (Fun x e2) e1.

(* Check Let. *)
(* Check Fun. *)

(* We can now prove a typing rule for Let *)

Lemma Let_typed Γ Γ1 Γ1' Γ2 x e1 e2 t1 t2 :
  env_split Γ Γ1 Γ2 ->
  env_bind Γ1' x t1 Γ1 ->
  typed Γ1' e2 t2 ->
  typed Γ2  e1 t1 ->
  typed Γ (Let x e1 e2) t2.
Proof.
  intros Hs Hb H1 H2.
  unfold Let.
  eapply App_typed; eauto.
  eapply (Fun_typed _ _ _ _ _ _ Lin); eauto.
  intros [=].
Qed.

(* Check Let_typed. *)
(* Check Fun_typed. *)

(* We now have a lemma that lets us type check our Let construct using the
   usual typing rule for let. From the outside, this gives the same interface
   as if we had added Let as a primitive expression and added a typing rule
   to our language: *)

(*
Inductive typed : env -> expr -> type -> Prop :=
  | ...
  | Let_typed Γ Γ1 Γ1' Γ2 x e1 e2 t1 t2 :
    env_split Γ Γ1 Γ2 ->
    env_bind Γ1' x t1 Γ1 ->
    typed Γ1' e2 t2 ->
    typed Γ2  e1 t1 ->
    typed Γ (Let x e1 e2) t2
  | ...
*)