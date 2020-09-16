From stdpp Require Import gmap.
From stdpp Require Import base.

Definition graph A `{Countable A} := gset (A * A).

Section graph.
  Context `{Countable A}.
  Context `{Inhabited A}.

  Definition undirected (g : graph A) :=
    ∀ x y, (x,y) ∈ g → (y,x) ∈ g.
  Definition no_self_loops (g : graph A) :=
    ∀ x, (x,x) ∉ g.

  Definition lookup_edge (i : nat) (xs : list A) :=
    match xs !! i, xs !! (i+1) with
    | Some x, Some y => Some (x,y)
    | _,_ => None
    end.
  
  Definition path (g : graph A) (xs : list A) := 
    ∀ i e, lookup_edge i xs = Some e -> e ∈ g.

  Lemma lookup_rev {B} (i : nat) (xs : list B) :
    i < length xs -> rev xs !! i = xs !! (length xs - S i).
  Proof.
    revert i; induction xs; intros; simpl; eauto.
    assert (length (rev xs) = length xs) by eauto using rev_length.
    destruct (decide (i = length xs)).
    {
      rewrite lookup_app_r; try lia. simplify_eq. rewrite H2.
      replace (length xs - length xs) with 0 by lia.
      done.
    }
    rewrite lookup_app_l;[|simpl in *;rewrite H2;lia].
    replace (a :: xs) with ([a] ++ xs) by done.
    rewrite lookup_app_r; simpl; try lia.
    rewrite IHxs.
    f_equiv. lia. simpl in *. lia. simpl in *. lia.
  Qed.

  Definition swap {A} : A*A -> A*A := λ '(a,b), (b,a).
  
  Lemma lookup_edge_rev (i : nat) (xs : list A) (x y : A) :
    i < length xs ->
    lookup_edge (length xs - i) (rev xs) = swap <$> lookup_edge i xs.
  Proof.
    intros Hle.
    unfold lookup_edge in *.
    destruct (rev _ !! _) eqn:E.



  Lemma path_rev g xs :
    undirected g -> path g (rev xs) -> path g xs.
  Proof.
    intros Hundir Hpath i [a b] Hi.
    apply Hundir.