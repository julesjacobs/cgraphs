Require Import List Lia Arith Basics Nat.

Definition bnat := list bool.

Fixpoint add1 (x : bnat) : bnat :=
  match x with
  | nil => false::nil
  | false::x => true::x
  | true::x => false::add1 x
  end.

Definition from_nat n := iter n add1 nil.

Definition mb {A} (b : bool) (f : A -> A) x := if b then f x else x.

Fixpoint to_nat (x : bnat) : nat :=
  match x with
  | nil => 0
  | b::x => mb b S (to_nat x * 2 + 1)
  end.

Lemma to_nat_add1 x : to_nat (add1 x) = S (to_nat x).
Proof.
  induction x as [|[] xs IH]; simpl; eauto. lia.
Qed.

Lemma to_nat_from_nat n : to_nat (from_nat n) = n.
Proof.
  induction n; simpl; rewrite ?to_nat_add1; eauto.
Qed.

Lemma to_nat_inj x y : to_nat x = to_nat y -> x = y.
Proof.
  revert y; induction x; intros []; simpl; eauto; try destruct a;
  try destruct b; simpl; try lia; intros; f_equal; apply IHx; lia.
Qed.

Lemma from_nat_to_nat x : from_nat (to_nat x) = x.
Proof.
  apply to_nat_inj. rewrite to_nat_from_nat. eauto.
Qed.

Fixpoint add (x y : bnat) : bnat :=
  match x,y with
  | nil,a | a,nil => a
  | b::x,c::y => mb b add1 (mb c add1 (true :: add x y))
  end.

Lemma add_add1 x y : add (add1 x) y = add1 (add x y).
Proof.
  revert y. induction x; intros []; simpl; eauto; destruct a;
  simpl; eauto. rewrite IHx. destruct b; simpl; eauto.
Qed.

Lemma add_plus (n m : nat) :
  add (from_nat n) (from_nat m) = from_nat (n + m).
Proof.
  revert m. induction n; intros m; simpl; eauto. rewrite add_add1, IHn. eauto.
Qed.

Lemma plus_add (x y : bnat) :
  to_nat (add x y) = to_nat x + to_nat y.
Proof.
  rewrite <-(from_nat_to_nat x), <-(from_nat_to_nat y), add_plus, !to_nat_from_nat. eauto.
Qed.