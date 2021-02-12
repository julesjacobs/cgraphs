From iris.proofmode Require Import base tactics classes.

Definition A := nat.
Definition graph := gset (A * A).

(* 
We represent a cycle p as a list of nodes. Conceptually, the sequence
of nodes repeats itself (p..,p..,p..), and represents an infinite
path in G.
If p = [x] it represents the cycle [x,x,x,...]. 
This can only occur if the node x has a self loop in G.
A cycle is never empty.
*)
Definition cycle (p : list A) (G : graph) :=
  p ≠ [] ∧
  ∀ i x y,
    p !! i = Some x ->
    p !! (S i `mod` length p) = Some y ->
    (x,y) ∈ G ∨ (y,x) ∈ G.

Lemma baz : cycle [3] (singleton (3,3)).
Proof.
  split.
  - admit.
  - intros i x y H1 H2.
    destruct i. simpl in *. simplify_eq.
    + admit.
    + simpl in *. admit.
Qed.

(*
A cycle has a U-turn if it visits [...,x,y,x,...], that is, 
it visits x, then y, then goes back to x.
*)
Definition has_uturn (p : list A) :=
  ∃ i x, p !! i = Some x ∧ p !! (i+2 `mod` length p) = Some x.

Definition no_self_loops (G : graph) :=
  ∀ i, (i,i) ∉ G.

(* Corner cases:
1. Self loops
2. Cycles of a single edge and back
*)

Lemma foo : has_uturn [3;4].
Proof.
  exists 0.
  exists 3.
  simpl. auto.
Qed.

Lemma bar : has_uturn [3].
Proof.
  exists 0.
  exists 3.
  simpl. auto.
Qed.

Definition tree (G : graph) :=
  no_self_loops G ∧ (∀ p, cycle p G -> has_uturn p).

Lemma empty_is_tree : tree ∅.
  split.
  { intro. apply not_elem_of_empty. } 
  intros p [Hne Hc].
  destruct p; simplify_eq.
  exfalso.
  destruct p; simplify_eq.
  - specialize (Hc 0 a a).
    destruct Hc; eauto.
    rewrite-> elem_of_empty in H. destruct H.
    rewrite-> elem_of_empty in H. destruct H.
  - specialize (Hc 0 a a0).
    destruct Hc; eauto. simpl.
    replace (S (length p) - length p) with 1 by lia; done.
    rewrite-> elem_of_empty in H. destruct H.
    rewrite-> elem_of_empty in H. destruct H.
Qed.

Definition lone (x : A) (G : graph) :=
  ∀ y, (x,y) ∉ G ∧ (y,x) ∉ G.

Lemma cycle_edge_unused G p x y :
  cycle p (G ∪ {[x, y]}) -> y ∉ p -> cycle p G.
Proof.
  intros [Hne Hc] Hnip.
  split; auto.
  intros i a b H1 H2.
  cut ((a, b) ∈ (G ∪ {[x, y]}) ∨ (b, a) ∈ (G ∪ {[x, y]})); last by eauto.
  assert (a ≠ y) as Ha.
  { intros H. subst. apply elem_of_list_lookup_2 in H1. done. }
  assert (b ≠ y) as Hb.
  { intros H. subst. apply elem_of_list_lookup_2 in H2. done. }
  rewrite-> !elem_of_union.
  intros [[]|[]]; auto; exfalso; 
  rewrite-> elem_of_singleton in H; simplify_eq.
Qed.

Lemma extend_tree (x y : A) (G : graph) :
  x ≠ y -> lone y G -> tree G -> tree (G ∪ {[x,y]}).
Proof.
  intros Hneq Hl Ht.
  split.
  { unfold tree,no_self_loops in *. set_solver. }
  intros p [Hne Hc].
  destruct Ht as [Hnocy Huturn].
  destruct (decide (y ∈ p)).
  - apply elem_of_list_lookup_1 in e as (i & Hi).
    exists ((i - 1) `mod` length p).
    exists x.
    split.
    {
      assert (∃ x0, p !! ((i - 1) `mod` length p) = Some x0).
      {

      }
      destruct H.
      specialize (Hc ((i-1) `mod` length p)).
      specialize (Hc x0 y).
      specialize (Hc H).
      replace ((i - 1) `mod` length p + 1 `mod` length p) with i in Hc by admit.
      specialize (Hc Hi).
      destruct (Hl x0) as [Hlx0 Hl0x].
      destruct Hc.
      {
        rewrite-> elem_of_union in H0.
        destruct H0.
        - exfalso. by apply Hl0x.
        - apply elem_of_singleton in H0. simplify_eq. done.
      }
      { 
        rewrite-> elem_of_union in H0.
        destruct H0.
        - exfalso. by apply Hlx0.
        - apply elem_of_singleton in H0. simplify_eq.
      }
    }
    replace ((i - 1) `mod` strings.length p + 2 `mod` strings.length p) 
      with ((i + 1) `mod` strings.length p) by admit.
    {

    }
  - apply Huturn. by eapply cycle_edge_unused.
Admitted.

Lemma modify_tree (x y z : A) (G : graph) :
  (x,y) ∈ G -> (y,z) ∉ G ->
  tree (G ∪ {[y,z]}) -> 
  tree (G ∪ {[x,z]}).
Proof.
Admitted.

Definition cardinality_at_most (n : nat) (G : graph) :=
  ∃ V : list A,
    length V = n ∧
    ∀ x y, (x,y) ∈ G -> x ∈ V ∧ y ∈ V.

Lemma long_paths_have_uturns (G : graph) (p : list A) (n : nat) :
  cardinality_at_most n G ->
  tree G -> path p G -> 
  length p > n -> has_uturn p.
Proof.
Admitted.