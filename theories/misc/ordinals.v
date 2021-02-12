

Inductive O : Set :=
    sup : forall t:Set, (t -> O) -> O.

Check O_ind.

Definition huh : O := sup O (fun x => x).

Definition zero := sup False (fun x => match x with end).
Definition succ o := sup True (fun x => o).

Inductive Pbool : Set := Ptrue | Pfalse.
Definition add o o' := sup Pbool (fun x => match x with Ptrue => o | Pfalse => o' end).

Inductive O_lt : O -> O -> Prop :=
    lt_sup : forall A B : Prop, forall f g,
       forall a:A, exists b:B, O_lt (f a) (g b) -> O_lt (sup A f) (sup B g).

       revert Gamma A.
       induction 1; simpl; rewrite ?...; trivial.

       induction e
       ; intros Gamma A0 H
       ; induction H
       ; simpl
       ; try rewrite IHtyped
       ; try rewrite IHtyped1
       ; try rewrite IHtyped2
       ; try rewrite IHtyped3
       ; try rewrite type_eq_refl
       ; trivial.