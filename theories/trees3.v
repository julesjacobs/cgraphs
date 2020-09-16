From stdpp Require Import gmap.
From stdpp Require Import base.

Definition lookup_mod `{Inhabited A} (i : Z) (xs : list A) : A :=
  xs !!! (Z.to_nat (i `mod` length xs)).

Lemma lookup_mod_mod `{Inhabited A} (xs : list A) (i : Z) :
  lookup_mod i xs = lookup_mod (i + length xs) xs.
Proof.
  intros.
  unfold lookup_mod.
  f_equiv. f_equiv.
  rewrite Zplus_mod, Z_mod_same_full, Z.add_0_r, Zmod_mod. done.
Qed.

Lemma lookup_mod_some {A} (xs : list A) (i : Z) :
  length xs ≠ 0 -> is_Some (xs !! Z.to_nat (i `mod` length xs)).
Proof.
  intro.
  apply lookup_lt_is_Some_2.
  pose proof (Z_mod_lt i (length xs)) as []. lia. lia.
Qed.

Lemma elem_of_list_lookup_mod `{Inhabited A} (xs : list A) (x : A) :
  x ∈ xs -> ∃ (i : Z), lookup_mod i xs = x.
Proof.
  intros Hin.
  apply elem_of_list_lookup_1 in Hin as [i Hi].
  exists i. unfold lookup_mod.
  apply list_lookup_total_correct.
  rewrite Zmod_small,Nat2Z.id; auto.
  split; [lia|].
  apply lookup_lt_Some in Hi. lia.
Qed.

Lemma elem_of_list_lookup_mod_r `{Inhabited A} (xs : list A) (x : A) (i : Z) :
  length xs ≠ 0 -> lookup_mod i xs = x -> x ∈ xs.
Proof.
  intros Hlen Hlookup.
  eapply elem_of_list_lookup_2.
  unfold lookup_mod in *.
  rewrite list_lookup_total_alt in Hlookup.
  pose proof (lookup_mod_some xs i Hlen) as [].
  rewrite H0 in Hlookup. simpl in *. simplify_eq. eauto.
Qed.

Lemma NoDup_lookup_mod `{Inhabited A} (xs : list A) (i j : Z) (x : A) :
  NoDup xs → lookup_mod i xs = lookup_mod j xs ->
  ((i - j) `mod` length xs = 0)%Z.
Proof.
  unfold lookup_mod.
  rewrite !list_lookup_total_alt.
  destruct (decide (length xs = 0)) as [Hzero|?].
  { rewrite Hzero. rewrite !Zmod_0_r. simpl. reflexivity. }
  destruct (lookup_mod_some xs i) as [y E]; [done|].
  destruct (lookup_mod_some xs j) as [z F]; [done|].
  rewrite E, F. simpl.
  intros Hnodup ->.
  pose proof (NoDup_lookup xs _ _ z Hnodup E F) as Heq.
  apply Z2Nat.inj in Heq; eauto using Z_mod_pos with lia.
  rewrite Zminus_mod, Heq, Z.sub_diag. reflexivity.
Qed.

Lemma uturn_has_dup `{Inhabited A} (xs : list A) (i : Z) :
  NoDup xs -> length xs >= 3 -> lookup_mod (i-1)%Z xs = lookup_mod (i+1)%Z xs -> False.
Proof.
  intros Hnodup Hlen Heq.
  symmetry in Heq.
  apply NoDup_lookup_mod in Heq; [|exact inhabitant|done].
  replace (i + 1 - (i - 1))%Z with 2%Z in Heq by lia.
  rewrite Zmod_small in Heq;[discriminate|lia].
Qed.

Definition graph A `{Countable A} := gset (A * A).

Section graph.
  Context `{Countable A}.
  Context `{Inhabited A}.
  Definition undirected (g : graph A) :=
    ∀ x y, (x,y) ∈ g → (y,x) ∈ g.
  Definition no_self_loops (g : graph A) :=
    ∀ x, (x,x) ∉ g.
  Definition lookup_edge (i : Z) (xs : list A) :=
    (lookup_mod i xs, lookup_mod (i+1) xs).
  Record cycle (g : graph A) (xs : list A) : Prop := Cycle {
    cycle_length : 3 <= length xs;
    cycle_NoDup : NoDup xs;
    cycle_cycle : ∀ i, lookup_edge i xs ∈ g;
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
    destruct 1 as [Hlen _ Hcycle].
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
  Lemma graph_singleton_elem (x y a b : A) :
    (a,b) ∈ graph_singleton x y <-> (a = x ∧ b = y) ∨ (a = y) ∧ (b = x).
  Proof. unfold graph_singleton. set_solver. Qed.
  Lemma graph_singleton_sym (x y : A) : 
    graph_singleton x y = graph_singleton y x.
  Proof. unfold graph_singleton. set_solver. Qed.
  Lemma graph_singleton_elem_1 (x y z : A) :
    (y,z) ∈ graph_singleton x y → z = x.
  Proof. unfold graph_singleton. set_solver. Qed.
  Lemma graph_singleton_elem_2 (x y z : A) :
    (z,y) ∈ graph_singleton x y → z = x.
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
    intros Hundir Hneq Hlone [Hlen Hnodup Hcycle].
    assert (y ∉ xs).
    {
      intro Hin.
      apply elem_of_list_lookup_mod in Hin as [i Helem].
      unfold lookup_edge in *.
      assert (lookup_mod (i+1) xs = x).
      {
        specialize (Hcycle i).
        apply elem_of_union in Hcycle as [].
        - specialize (Hlone (lookup_mod (i+1) xs)). set_solver.
        - rewrite-> Helem in *. eapply graph_singleton_elem_1; done.
      }
      assert (lookup_mod (i-1) xs = x).
      {
        specialize (Hcycle (i-1)%Z).
        replace (i - 1 + 1)%Z with i in * by lia.
        apply elem_of_union in Hcycle as [].
        - specialize (Hlone (lookup_mod (i-1) xs)).
          unfold undirected in *.  set_solver.
        - rewrite-> Helem in *. eapply graph_singleton_elem_2; done.
      }
      subst. eapply uturn_has_dup; (done || lia).
    }
    split; [by auto..|].
    intros i.
    specialize (Hcycle i).
    apply elem_of_union in Hcycle as []; auto.
    unfold graph_singleton in *.
    unfold lookup_edge in *.
    set_solver by eauto using elem_of_list_lookup_mod_r with lia.
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

  Lemma undirected_delete (x y : A) (g : graph A) :
    undirected g ->
    undirected (g ∖ graph_singleton x y).
  Proof.
    intros Hundir a b.
    rewrite !elem_of_difference.
    intros [].
    split.
    - by apply Hundir.
    - unfold graph_singleton in *. set_solver.
  Qed.

  Lemma no_self_loops_delete (x y : A) (g : graph A) :
    x ≠ y -> no_self_loops g ->
    no_self_loops (g ∖ graph_singleton x y).
  Proof.
    intros Hneq Hsl a [H1 ?]%elem_of_difference.
    apply Hsl in H1 as [].
  Qed.

  Lemma dec_exists_list {B} (xs : list B) (P : B → Prop) :
  (∀ x, P x → x ∈ xs) → (∀ x, x ∈ xs → Decision (P x)) → Decision (∃ x, P x).
  Proof.
    intros HPxs Hdec.
    induction xs as [|x xs IHxs]. { right. set_solver. }
    assert (Decision (P x)) as [] by (apply Hdec; set_solver).
    { left. naive_solver. }
    apply IHxs.
    - intros x' HPx'. specialize (HPxs x' HPx').
      assert (x' = x ∨ x' ∈ xs) as []; set_solver.
    - intros ??. apply Hdec. set_solver.
  Qed.

  Lemma exists_lookup_mod_dec (n : nat) (P : nat -> Prop) :
    (∀ i, Decision (P i)) ->
    Decision (∃ i, P i ∧ i < n).
  Proof.
    intros Hdec.
    eapply (dec_exists_list (seq 0 n)).
    - intros ? []. rewrite elem_of_list_In. apply in_seq. lia.
    - solve_decision.
  Qed.

  Lemma lookup_reverse {B} (i : nat) (xs : list B) :
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

  Lemma NoDup_rev {B} (xs : list B) :
    NoDup xs -> NoDup (rev xs).
  Proof.
    rewrite !NoDup_alt.
    intros.
    assert (i < length xs). { rewrite <-rev_length. by eapply lookup_lt_Some. }
    assert (j < length xs). { rewrite <-rev_length. by eapply lookup_lt_Some. }
    rewrite lookup_reverse in H2; eauto.
    rewrite lookup_reverse in H3; eauto.
    assert (length xs - S i = length xs - S j). eauto.
    lia.
  Qed.

  Lemma lookup_mod_rev (i : Z) (xs : list A) :
    lookup_mod i xs = lookup_mod (- i - 1) (rev xs).
  Proof.
    destruct (decide (length xs = 0)).
    {
      destruct xs; simpl in *; simplify_eq.
      unfold lookup_mod.
      rewrite !list_lookup_total_alt, !lookup_nil. done.
    }
    unfold lookup_mod.
    rewrite rev_length.
    rewrite !list_lookup_total_alt.
    rewrite lookup_reverse.
    {
      subst. rewrite<- !list_lookup_total_alt. f_equiv.
      revert n.
      generalize (length xs). intros.
      rewrite<- Z2Nat.inj_succ;[|apply Z_mod_pos; lia].
      replace n with (Z.to_nat (Z.of_nat n));[|lia].
      rewrite<- Z2Nat.inj_sub.
      2: {
        assert (0 <= (- i - 1) `mod` Z.to_nat n)%Z.
        apply Z_mod_pos. lia. lia.
      }
      f_equiv.
      assert (n = 37) by admit.
      assert (i = 163) by admit.
      subst. done.
    }
    destruct (Z.mod_pos_bound (- i - 1) (length xs)). lia. lia.
  Admitted.

  Lemma cycle_rev (g : graph A) (xs : list A) :
    undirected g ->
    cycle g xs -> cycle g (rev xs).
  Proof.
    intros Hundir [].
    constructor.
    - rewrite rev_length. lia.
    - apply NoDup_rev. done.
    - intros i.
      unfold lookup_edge in *.
(*       
      rewrite<- lookup_mod_rev.
      replace (- (i + 1) - 1)%Z with (- i - 2)%Z by lia.
      replace (-i - 1)%Z with ((-i - 2)+1)%Z by lia.
      apply Hundir.
      apply cycle_cycle0.
  Qed. *)

  Lemma cycle_mono (g h : graph A) (xs : list A) :
    cycle g xs -> cycle (g ∪ h) xs.
  Proof.
    intros []. constructor; eauto.
    intro. apply elem_of_union_l. done.
  Qed.

  Lemma cycle_mono' (g h : graph A) (xs : list A) :
    cycle (g ∖ h) xs -> cycle g xs.
  Proof.
    intros []. constructor; eauto.
    intro. eapply elem_of_difference. done.
  Qed.

  Lemma cycle_edge_unused (g : graph A) (x y : A) (xs : list A) :
    cycle (g ∪ graph_singleton x y) xs ->
    (∀ i, lookup_edge i xs = (x,y) ∨ lookup_edge i xs = (y,x) -> False) ->
    cycle g xs.
  Proof.
    intros [] Hi. constructor; eauto.
    intro. specialize (cycle_cycle0 i).
    rewrite elem_of_union in cycle_cycle0.
    destruct cycle_cycle0. done.
    exfalso. apply (Hi i).
    unfold lookup_edge in *.
    rewrite graph_singleton_elem in *.
    naive_solver.
  Qed.

  Definition delete_mod (i : Z) (xs : list A) : list A.
  Admitted.
  
  Definition insert_mod (i : Z) (x : A) (xs : list A) : list A.
  Admitted.

  Lemma insert_mod_length (i : Z) (x : A) (xs : list A) :
    length (insert_mod i x xs) = 1 + length xs.
  Proof. Admitted.

  Lemma delete_mod_length (i : Z) (xs : list A) :
    length (delete_mod i xs) = length xs - 1.
  Proof. Admitted.

  Lemma insert_mod_NoDup (i : Z) (x : A) (xs : list A) :
    x ∉ xs -> NoDup xs -> NoDup (insert_mod i x xs).
  Proof. Admitted.

  Lemma delete_mod_NoDup (i : Z) (xs : list A) :
    NoDup xs -> NoDup (delete_mod i xs).
  Proof. Admitted.

  Definition edges (xs : list A) : gset (A * A). Admitted.

  Lemma edges_delete (xs : list A) (a b c : A) (i : nat) :
    3 ≤ length xs ->
    lookup_mod i xs = a ->
    lookup_mod (i+1) xs = b ->
    lookup_mod (i+2) xs = c ->
    edges (delete_mod (i+1) xs) = edges xs ∖ {[a,b]} ∖ {[b,c]} ∪ {[a,c]}.
  Proof. Admitted.

  Lemma edges_insert (xs : list A) (a b c : A) (i : nat) :
    3 ≤ length xs ->
    lookup_mod i xs = a ->
    lookup_mod (i+1) xs = c ->
    edges (insert_mod (i+1) b xs) = edges xs ∖ {[a,c]} ∪ {[a,b]} ∪ {[b,c]}.
  Proof. Admitted.

  Lemma lookup_edge_mod (i : Z) (xs : list A) :
    length xs ≠ 0 ->
    lookup_edge (i `mod` length xs) xs = lookup_edge i xs.
  Proof.
    intro.
    unfold lookup_edge.
    unfold lookup_mod.
    rewrite Z.add_mod_idemp_l; [|lia].
    rewrite Zmod_mod. done.
  Qed.

  Lemma lookup_mod_rev_2 (i : Z) (xs : list A) :
    lookup_mod i (rev xs) = lookup_mod (- i - 1) xs.
  Proof.
    replace (lookup_mod (- i - 1) xs) with (lookup_mod (- i - 1) (rev (rev xs))).
    - rewrite lookup_mod_rev. done.
    - f_equiv. rewrite rev_involutive. done.
  Qed.

  Definition swap {A} (p : A * A) := 
      let (a,b) := p in (b,a).

  Lemma lookup_edge_reverse (i : Z) (xs : list A) :
    lookup_edge (- i - 2) (rev xs) = swap (lookup_edge i xs).
  Proof.
    unfold lookup_edge. unfold swap.
    rewrite !lookup_mod_rev_2. f_equiv.
    f_equiv. lia. f_equiv. lia.
  Qed.

  Lemma no_cycle_modify (x y z : A) (xs : list A) (g : graph A) :
    x ≠ z -> y ≠ z ->
    tree g -> (x,y) ∈ g -> (x,z) ∈ g ->
    ¬ cycle (g ∖ graph_singleton x z ∪ graph_singleton y z) xs.
  Proof.
    intros Hxneqz Hyneqz [] Hxyg Hxzg Hcycle.
    assert (Decision (∃ i, 
      lookup_edge i xs = (y,z) ∨ 
      lookup_edge i xs = (z,y))).
    {
      assert (Decision (∃ i,
        0 <= i ∧ i < length xs ∧ 
        (lookup_edge i xs = (y,z) ∨ 
        lookup_edge i xs = (z,y))))%Z.
      {
        apply (dec_exists_list (map Z.of_nat (seq 0 (length xs))))%Z.
        {
          intros. rewrite elem_of_list_In, in_map_iff.
          exists (Z.to_nat x0). split. lia.
          rewrite in_seq. lia.
        }
        solve_decision.
      }
      destruct H1.
      - left. destruct e. exists x0. naive_solver.
      - right. intro. destruct H1. apply n.
        exists (x0 `mod` (length xs))%Z.
        pose proof (Z.mod_pos_bound x0 (length xs)).
        destruct Hcycle.
        split. lia.
        split. lia.
        rewrite lookup_edge_mod;[|lia].
        done.
    }
    
    destruct H1 as [Hedge|Hnotedge].
    2: {
      apply (tree_no_cycle0 xs).
      eapply cycle_mono'.
      eapply cycle_edge_unused. done.
      naive_solver.
    }
    destruct Hedge as [i Hedge].
    revert i Hedge Hcycle Hxzg Hxyg tree_no_cycle0 tree_no_self_loops0
            tree_undirected0 Hxneqz Hyneqz.
    revert xs x y z.
    cut (∀ (xs : list A) (x y z : A) (i : Z),
      lookup_edge i xs = (z, y)
      → cycle (g ∖ graph_singleton x z ∪ graph_singleton y z) xs
        → (x, z) ∈ g
          → (x, y) ∈ g
            → (∀ xs0 : list A, ¬ cycle g xs0)
              → no_self_loops g → undirected g → x ≠ z → y ≠ z → False).
    {
      intros.
      destruct Hedge; eauto.
      specialize (H1 (rev xs)).
      specialize (H1 x y z).
      eapply H1; eauto. rewrite lookup_edge_reverse.
      simpl. unfold lookup_edge in H2. simplify_eq. done.
      apply cycle_rev; eauto.
      apply undirected_extend.
      apply undirected_delete. 
      done.
    }
    intros xs x y z.
    intros i Hedge Hcycle Hxzg Hxyg tree_no_cycle0 tree_no_self_loops0
            tree_undirected0 Hxneqz Hyneqz.
    destruct Hcycle.

    destruct (decide (lookup_mod (i+2) xs = x)) as [Hx|Hnx].
    - apply (tree_no_cycle0 (delete_mod (i+1) xs)).
      constructor.
      + (* prove that the length wasn't 3 *)
        destruct (decide (length xs = 3)); [|rewrite delete_mod_length;lia].
        exfalso.
        specialize (cycle_cycle0 (i+2)%Z).
        assert (lookup_edge (i+2)%Z xs = (x,z)).
        {
          unfold lookup_edge in *.
          replace (i + 2 + 1)%Z with (i + length xs)%Z by lia.
          rewrite<- lookup_mod_mod. simplify_eq. done.
        }
        rewrite H1 in cycle_cycle0.
        rewrite elem_of_union in cycle_cycle0.
        rewrite elem_of_difference in cycle_cycle0.
        destruct cycle_cycle0 as [[]|].
        * rewrite graph_singleton_elem in *. naive_solver.
        * rewrite graph_singleton_elem in *.
          assert (x = y). naive_solver.
          eapply tree_no_self_loops0. subst. eauto.
      + apply delete_mod_NoDup. done.
      + intros j.
        admit.
    - apply (tree_no_cycle0 (insert_mod (i+1) x xs)).
      constructor.
      + rewrite insert_mod_length. lia.
      + apply insert_mod_NoDup; [|done]. intro.
        (* if x is in xs, we can construct a smaller cycle *)
        
        admit.
      + intros j.
        (* prove that after inserting x, the cycle is in g *)
        admit.
  Admitted.

  Lemma tree_modify (x y z : A) (g : graph A) :
    x ≠ z -> y ≠ z ->
    tree g -> (x,y) ∈ g -> (x,z) ∈ g ->
    tree ((g ∖ graph_singleton x z) ∪ graph_singleton y z).
  Proof.
    intros ?? [] ??.
    constructor.
    - apply undirected_extend. apply undirected_delete. done.
    - apply no_self_loops_extend;[done|]. 
      apply no_self_loops_delete;done.
    - intros. eapply no_cycle_modify; done. 
  Qed.

  Lemma tree_delete (x y : A) (g : graph A) :
    tree g -> tree (g ∖ graph_singleton x y).
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
  
  (* set_wf *)