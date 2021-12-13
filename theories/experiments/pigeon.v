Require Import List Lia Arith Basics.

Lemma length_filter_filter {A} (f g : A -> bool) (xs : list A) :
  length (filter f (filter g xs)) <= length (filter f xs).
Proof.
  induction xs; simpl; [lia|].
  destruct (g a); simpl; destruct (f a); simpl; lia.
Qed.

Lemma length_filter_negb {A} (f : A -> bool) (xs : list A) :
  length xs = length (filter f xs) + length (filter (fun x => negb (f x)) xs).
Proof.
  induction xs; simpl; eauto. destruct (f a); simpl; lia.
Qed.

Lemma Forall_filter {A} (P : A -> Prop) (f : A -> bool) (xs : list A) :
  Forall P xs -> Forall (fun x => f x = true /\ P x) (filter f xs).
Proof.
  induction xs; simpl; eauto using Forall_nil. destruct (f a) eqn:E;
  eauto 6 using Forall_cons, Forall_inv_tail, (Forall_inv (P := P)).
Qed.

Lemma pigeon (xs : list nat) (n : nat):
  Forall (fun x => x < n) xs -> n < length xs ->
  exists a, 2 <= length (filter (Nat.eqb a) xs).
Proof.
  revert xs. induction n; intros xs Hin Hlen; simpl.
  - destruct xs; simpl in *; [|apply Forall_inv in Hin]; lia.
  - destruct (le_lt_dec 2 (length (filter (Nat.eqb n) xs))); [eauto|].
    destruct (IHn (filter (fun x => negb (Nat.eqb n x)) xs)) as [a Ha].
    + eapply Forall_impl;[|eauto using Forall_filter]. simpl.
      intros a []. assert (n <> a); [|lia].
      intros ->. rewrite Nat.eqb_refl in H. discriminate.
    + pose proof (length_filter_negb (Nat.eqb n) xs). lia.
    + exists a. etransitivity; eauto using length_filter_filter.
Qed.