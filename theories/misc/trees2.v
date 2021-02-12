From stdpp Require Import gmap.
Definition graph A `{Countable A} := gset (A * A).
Section graph.
  Context `{Countable A}.
  Definition undirected (g : graph A) :=
    ∀ x y, (x,y) ∈ g → (y,x) ∈ g.
  Definition no_self_loops (g : graph A) :=
    ∀ x, (x,x) ∉ g.
  Definition path (g : graph A) (xs : list A) :=
    ∀ i x y, xs !! i = Some x → xs !! S i = Some y → (x,y) ∈ g.
  Record cycle (g : graph A) (xs : list A) : Prop := Cycle {
    cycle_length : 3 < length xs;
    cycle_NoDup : NoDup (tail xs);
    cycle_begin_end : xs !! 0 = xs !! pred (length xs);
    cycle_path : path g xs;
  }.
  Record tree (g : graph A) : Prop := Tree {
    tree_undirected : undirected g;
    tree_no_self_loops : no_self_loops g;
    tree_no_cycle xs : ¬cycle g xs;
  }.
  Lemma undirected_empty : undirected ∅.
  Proof. unfold undirected. set_solver. Qed.
  Lemma no_self_loops_empty : no_self_loops ∅.
  Proof. unfold no_self_loops. set_solver. Qed.
  Lemma no_cycle_empty xs : ¬cycle ∅ xs.
  Proof.
    destruct 1 as [Hlen _ _ Hcycle].
    destruct xs as [|x1 [|x2 xs]]; simplify_eq/=; [lia..|].
    specialize (Hcycle 0). set_solver.
  Qed.
  Lemma tree_empty : tree ∅.
  Proof.
    split; eauto using undirected_empty, no_self_loops_empty, no_cycle_empty.
  Qed.
  Definition lone (x : A) (g : graph A) :=
    ∀ y, (x,y) ∉ g.
  Definition graph_singleton (x y : A) : graph A := {[ (x,y); (y,x) ]}.
  Lemma graph_singleton_sym (x y : A) : 
    graph_singleton x y = graph_singleton y x.
  Proof. unfold graph_singleton. set_solver. Qed.
  Lemma graph_singleton_elem (x y z : A) :
    (x,z) ∈ graph_singleton x y → z = y.
  Proof. unfold graph_singleton. set_solver. Qed.
  Lemma graph_singleton_elem_2 (x y z : A) :
    (z,x) ∈ graph_singleton x y → z = y.
  Proof. unfold graph_singleton. set_solver. Qed.
  Lemma undirected_extend (x y : A) (g : graph A) :
    undirected g → undirected (g ∪ graph_singleton x y).
  Proof. unfold undirected, graph_singleton. set_solver. Qed.
  Lemma no_self_loops_extend (x y : A) (g : graph A) :
    x ≠ y →
    no_self_loops g → no_self_loops (g ∪ graph_singleton x y).
  Proof. unfold no_self_loops, graph_singleton. set_solver. Qed.
  Lemma cycle_extend (x y : A) (g : graph A) xs :
    undirected g →
    x ≠ y → lone y g →
    cycle (g ∪ graph_singleton x y) xs →
    cycle g xs.
  Proof.
    intros Hundir Hneq Hlone [Hlen Hnodup Hbe Hpath].
    assert (y ∉ xs). 
    {
      intro.
      apply elem_of_list_lookup_1 in H0 as [i Helem].
      destruct (decide (i = 0)).
      - subst.
        assert (xs !! (pred (length xs)) = Some y).
        { rewrite<- Helem. by symmetry. }
        assert (xs !! 1 = Some x).
        {
          destruct (xs !! 1) eqn:E.
          - specialize (Hpath 0 y a Helem E).
            apply elem_of_union in Hpath as [].
            * specialize (Hlone a). set_solver.
            * f_equiv. rewrite graph_singleton_sym in *. by eapply graph_singleton_elem.
          - apply lookup_ge_None in E. lia.
        }
        assert (xs !! (length xs - 2) = Some x).
        { 
          destruct (xs !! (length xs - 2)) eqn:E.
          - specialize (Hpath (length xs - 2) a y E).
            replace (S (length xs - 2)) with (pred (length xs)) in * by lia.
            specialize (Hpath H0).
            apply elem_of_union in Hpath as [].
            * specialize (Hlone a). apply Hundir in H2. set_solver.
            * f_equiv. rewrite graph_singleton_sym in *.
              by apply (graph_singleton_elem_2 y).
          - rewrite lookup_ge_None in E. lia.
        }
        assert (0 = length xs - 3); try lia.
        eapply NoDup_lookup; eauto; rewrite lookup_tail; eauto.
        replace (S (length xs - 3)) with (length xs - 2) by lia. done.
      - assert (is_Some (xs !! (i-1))) as [z Hz].
        { apply lookup_lt_is_Some. apply lookup_lt_Some in Helem. lia. }
        assert (z = x).
        {
          specialize (Hpath (i-1) z y Hz).
          replace (S (i-1)) with i in Hpath by lia.
          specialize (Hpath Helem).
          apply elem_of_union in Hpath.
          destruct Hpath.
          - exfalso. specialize (Hlone z). apply Hundir in H0. set_solver.
          - unfold graph_singleton in *. set_solver.
        }
        subst.
        destruct (decide (S i = length xs)).
        * assert (xs !! 0 = Some y).
          { 
            rewrite Hbe. rewrite<- e.
            by replace (pred (S i)) with i by lia.
          }
          assert (xs !! 1 = Some x).
          {
            destruct (xs !! 1) eqn:E.
            - specialize (Hpath 0 y a H0 E).
              apply elem_of_union in Hpath as [].
              * specialize (Hlone a). set_solver.
              * f_equiv. rewrite graph_singleton_sym in *. by eapply graph_singleton_elem.
            - apply lookup_ge_None in E. lia.
          }
          assert (0 = i - 2); try lia.
          eapply NoDup_lookup; eauto; rewrite lookup_tail; eauto.
          replace (S (i - 2)) with (i - 1) by lia. done.
        * assert (is_Some (xs !! (S i))) as [z Hz'].
          { apply lookup_lt_is_Some. apply lookup_lt_Some in Helem. lia. }
          assert (z = x).
          {
            specialize (Hpath i y z Helem Hz').
            apply elem_of_union in Hpath.
            destruct Hpath.
            - exfalso. specialize (Hlone z). set_solver.
            - unfold graph_singleton in *. set_solver.
          }
          subst.
          destruct (decide (i - 1 = 0)).
          + rewrite e in *.
            assert (xs !! (pred (length xs)) = Some x).
            { by rewrite<- Hbe. }
            assert (i = length xs - 2); try lia.
            eapply NoDup_lookup; eauto; rewrite lookup_tail; eauto.
            replace (S (length xs - 2)) with (pred (length xs)) by lia. done.
          + assert (i - 2 = i); try lia.
            Check NoDup_lookup.
            eapply NoDup_lookup; eauto; rewrite lookup_tail; eauto.
            replace (S (i - 2)) with (i - 1) by lia. done.
    }
    split; [by auto..|].
    intros i z1 z2 ??.
    specialize (Hpath i z1 z2).
    rewrite elem_of_union in Hpath.
    destruct Hpath; auto.
    exfalso.
    unfold graph_singleton in *.
    set_solver by eauto using elem_of_list_lookup_2.
  Qed.
  
  Lemma tree_extend (x y : A) (g : graph A) :
    x ≠ y → lone y g →
    tree g → tree (g ∪ graph_singleton x y).
  Proof.
    intros ?? [].
    split; eauto using undirected_extend, no_self_loops_extend.
    intros ??. specialize (tree_no_cycle0 xs). apply tree_no_cycle0.
    eapply cycle_extend; eauto.
  Qed.

  Lemma tree_modify (x y z : A) (g : graph A) :
    (x,y) ∈ g -> (y,z) ∉ g ->
    tree (g ∪ graph_singleton y z) -> 
    tree (g ∪ graph_singleton x z).
  Proof.

  Admitted.

  Definition cardinality_at_most (n : nat) (g : graph A) :=
    ∃ V : list A,
      length V = n ∧
      ∀ x y, (x,y) ∈ g -> x ∈ V ∧ y ∈ V.

  Definition no_u_turn (xs : list A) :=
    ∀ i x y, xs !! i = Some x -> xs !! (i+2) = Some y -> x ≠ y.

  Lemma no_u_turn_tree_paths_are_short (g : graph A) (xs : list A) (n : nat) :
    cardinality_at_most n g ->
    tree g -> path g xs -> no_u_turn xs ->
    length xs <= n.
  Proof.
  Admitted.