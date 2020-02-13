From iris.proofmode Require Import tactics.

Fixpoint evalp (x : Z) (p : list Z) : Z :=
  match p with
  | [] => 0
  | a :: p' => a * x ^ (length p') + evalp x p'
  end%Z.

Fixpoint zero (p : list Z) :=
  match p with
  | [] => True
  | a :: p' => a = 0 /\ zero p'
  end.


Lemma zero_if_ext_zero p :
  (forall n, evalp n p = 0) -> zero p.
Proof.
  induction p; first done. simpl.
  intros. assert (a=0); last (subst;auto). clear IHp.
  
Qed.

Lemma zero_if_ext_zero' (p : list nat) :
  (forall n, evalp n p = 0) -> (forall i a, p !! i = Some a -> a=0).
Proof.
  intros. specialize (H 1).
  induction p; first done.
  intros.
  intros. assert (a=0);[|subst;simpl;auto].
  specialize (H 1). simpl in H. rewrite Nat.pow_1_l in H. lia.
Qed.

Lemma foo (P : nat -> Prop) :
  (forall n, (forall m, m < n -> P m) -> P n) -> (forall n m, m < n -> P m).
Proof.
    intros H n. induction n.
    - lia.
    - intros. apply H. intros. apply IHn. lia.
Qed.

Lemma bar (P : nat -> Prop) :
  (forall n, (forall m, m < n -> P m) -> P n) -> (forall n, P n).
Proof.
  intros. apply H. induction n.
  - lia.
  - intros. apply H. intros. apply IHn. lia.
Qed.

Ltac doind :=
  match goal with
  | x : _ |- _ => induction x; simpl
  end.

Hint Extern 200 => doind : induction.

Lemma foo' (P : nat -> Prop) :
  (forall n, (forall m, m < n -> P m) -> P n) -> (forall n, P n).
Proof.
    eauto with induction lia.
Qed.

Ltac dorew :=
  match goal with
  | x : _ |- _ => rewrite x || rewrite<- x
  end.

Hint Extern 100 => dorew : rewrite.

Inductive N : Type := Z : N | S : N -> N.

Fixpoint plus a b :=
  match a with
  | Z => b
  | S a' => S (plus a' b)
  end.

Lemma plus_comm : forall a b, plus a b = plus b a.
Proof.
  eauto 7 with induction rewrite.
Qed.

Lemma plus_assoc : forall a b c, plus (plus a b) c = plus a (plus b c).
Proof.
  eauto with induction rewrite.
Qed.

Definition t_id := forall t:Type, t -> t.
Definition p1_id f := forall a, forall P : a -> Prop, forall x, P x -> P (f a x).

Lemma all_id (f : t_id) : p1_id f -> forall a x, f a x = x.
Proof.
  unfold p1_id. intros. apply H. auto.
Qed.

Definition cnat := forall t:Prop, t -> (t -> t) -> t.

Definition cZ : cnat := fun t z f => z.
Definition cS (n : cnat) : cnat := fun t z f => f (n t z f).

Definition p2_nat f g := 
  forall a b, forall R : a -> b -> Prop,
  forall x y s r, R x y -> (forall x' y', R x' y' -> R (s x') (r y')) -> R (f a x s) (g b y r).

Lemma cnat_repr : (forall n:cnat, n cnat cZ cS = n).

Lemma cnat_ind : (forall n:cnat, p2_nat n n) -> forall P : cnat -> Prop, P cZ -> (forall n, P n -> P (cS n)) -> forall n, P n.
Proof.
  unfold p2_nat.
  intros.


Inductive A := fooA : A.
Inductive B := fooB : B.
Inductive C := fooC : C.
Inductive D := fooD : D.

Class R (x : Type) (y : Type) : Type := { foo : nat }.

Check R.

Instance I4 {x y z : Type} (a1 : R x y) (a2 : R y z) : R x z := { foo := 4 }.
Instance I5 (a1 : R A A) : R A D := { foo := 5 }.

Instance I1 : R A B := { foo := 1 }.
Instance I2 : R A C := { foo := 2 }.
Instance I3 : R C D := { foo := 3 }.

Definition bar `{x : R A D} := 2.
Definition baz `{x : R A A} := 3.
Set Typeclasses Iterative Deepening.
Compute bar.

From diris.heap_lang Require Export proofmode notation.
Set Default Proof Using "Type".


Definition lock : val := λ: "x", WAS "x" #false #true.
Definition unlock : val := λ: "x", "x" <- #true.


Lemma lock_spec1 : {{{ True }}} lock  {{{ RET #(); True }}}.
Proof.
Qed.

Lemma lock_spec1 (x:loc) (a:val) : {{{ x ↦ a }}} lock #x {{{ RET #(); x ↦ #true }}}.
Proof.
Qed.