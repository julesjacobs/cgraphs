From stdpp Require Import gmap.

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

  Lemma mod_0_k (n i k : Z) :
    (n > 0)%Z ->
    ((i - k) `mod` n = 0 -> 0 ≤ k -> k < n -> i `mod` n = k)%Z.
  Proof.
    intros.
    erewrite <-Zmod_unique_full. done. unfold Remainder. lia.
    rewrite Zmod_eq in H2;[|done].
    assert (i = n * ((i - k) `div` n) + k)%Z. lia. done.
  Qed.

  Lemma mod_horrible (i n : Z) :
    (0 < n)%Z ->
    (i `mod` n = n - Z.succ ((- i - 1) `mod` n))%Z.
  Proof.
    intro.
    pose proof (Z.mod_pos_bound (- i - 1) n)%Z.
    eapply mod_0_k; try lia.
    assert (∀ x, Z.succ x = x + 1)%Z as Q by lia.
    rewrite Q.
    rewrite <- Zminus_mod_idemp_r.
    rewrite <- (Zminus_mod_idemp_r n).
    rewrite Zplus_mod_idemp_l.
    rewrite (Zminus_mod_idemp_r n).
    rewrite Zminus_mod_idemp_r.
    replace (i - (n - (- i - 1 + 1)))%Z with ((-1)*n)%Z by lia.
    rewrite Z.mod_mul; lia.
  Qed.

  Lemma lookup_mod_rev (i : Z) (xs : list A) :
    lookup_mod i xs = lookup_mod (- i - 1)%Z (rev xs).
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
      replace (length xs) with (Z.to_nat (Z.of_nat (length xs))) by lia.
      assert (Z.of_nat (length xs) > 0)%Z by lia.
      clear n. revert H1.
      generalize (Z.of_nat (length xs)). intros n Hn.
      rewrite Z2Nat.id;[|lia].
      pose proof (Z.mod_pos_bound (-i-1) n)%Z.
      assert (S (Z.to_nat ((- i - 1) `mod` n)) ≤ Z.to_nat n) by lia.
      rewrite <-Z2Nat.inj_succ by lia.
      rewrite <-Z2Nat.inj_sub by lia.
      f_equiv. apply mod_horrible. lia.
    }
    destruct (Z.mod_pos_bound (- i - 1) (length xs)). lia. lia.
  Qed.

  Lemma lookup_mod_rev' (i : Z) (xs : list A) :
    lookup_mod (- i - 1) xs = lookup_mod i (rev xs).
  Proof.
    replace i with (-(-i - 1) -1)%Z by lia.
    rewrite<- lookup_mod_rev. f_equiv. lia.
  Qed.

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
      rewrite<- !lookup_mod_rev'.
      replace (- (i + 1) - 1)%Z with (- i - 2)%Z by lia.
      replace (-i - 1)%Z with ((-i - 2)+1)%Z by lia.
      apply Hundir.
      apply cycle_cycle0.
  Qed.

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

  Fixpoint insert {T} (i : nat) (x : T) (xs : list T) : list T :=
      match i,xs with
      | 0,xs => x :: xs
      | S i',y :: xs => y :: insert i' x xs
      | S i',[] => []
      end.

  Lemma insert_length {T} (i : nat) (x : T) (xs : list T) :
    i ≤ length xs -> length (insert i x xs) = length xs + 1.
  Proof.
    revert i. induction xs; intros; destruct i; simpl in *; auto with lia.
  Qed.

  Lemma in_insert {T} (i : nat) (x a : T) (xs : list T) :
    i ≤ length xs -> (a ∈ insert i x xs <-> a = x ∨ a ∈ xs).
  Proof.
    revert i; induction xs; intros; destruct i; simpl in *; rewrite ?elem_of_cons, ?IHxs;
    rewrite ?elem_of_cons; naive_solver lia.
  Qed.

  Lemma insert_NoDup {T} (i : nat) (x : T) (xs : list T) :
    i ≤ length xs ->
      (x ∉ xs ∧ NoDup xs <-> NoDup (insert i x xs)).
  Proof.
    revert i; induction xs; destruct i; simpl; intros;
    rewrite ?list.NoDup_cons; eauto with lia.
    rewrite <-IHxs, in_insert, not_elem_of_cons; naive_solver lia.
  Qed.

  Lemma insert_out_of_bounds {T} (i : nat) (x : T) (xs : list T) :
    i > length xs -> insert i x xs = xs.
  Proof.
    revert i; induction xs; destruct i; simpl; intros; try f_equiv; eauto with lia.
  Qed.

  Lemma insert_NoDup_2 {T} (i : nat) (x : T) (xs : list T) :
    x ∉ xs -> NoDup xs -> NoDup (insert i x xs).
  Proof.
    destruct (decide (i ≤ length xs)).
    - rewrite <-insert_NoDup; eauto with lia.
    - rewrite insert_out_of_bounds; eauto with lia.
  Qed.

  Lemma insert_delete {T} (i : nat) (x : T) (xs : list T) :
    delete i (insert i x xs) = xs.
  Proof.
    revert i; induction xs; destruct i; simpl; try f_equiv; eauto.
  Qed.

  Lemma delete_insert {T} (i : nat) (x : T) (xs : list T) :
    xs !! i = Some x -> insert i x (delete i xs) = xs.
  Proof.
    revert i; induction xs; destruct i; simpl; intros; try f_equiv; naive_solver.
  Qed.

  Definition insert_mod (i : Z) (x : A) (xs : list A) :=
      insert (Z.to_nat (i `mod` length xs)) x xs.

  Definition delete_mod (i : Z) (xs : list A) :=
      delete (Z.to_nat (i `mod` length xs)) xs.

  Lemma delete_mod_length i xs :
    length (delete_mod i xs) = length xs - 1.
  Proof.
    destruct (decide (length xs = 0)).
    { by destruct xs; simplify_eq. }
    unfold delete_mod.
    rewrite length_delete. done.
    by apply lookup_mod_some.
  Qed.

  Lemma in_delete x i (xs : list A) :
    x ∈ delete i xs -> x ∈ xs.
  Proof.
    revert i; induction xs; intros; destruct i; simpl in *;
    eauto; rewrite elem_of_cons; eauto.
    rewrite elem_of_cons in H1.
    destruct H1; eauto.
  Qed.

  Lemma NoDup_delete i (xs : list A) :
    NoDup xs -> NoDup (delete i xs).
  Proof.
    intro. revert i; induction xs; intros; destruct i; simpl in *; eauto.
    - eapply NoDup_cons_12. done.
    - eapply NoDup_cons_2; eauto using NoDup_cons_12.
      rewrite list.NoDup_cons in H1. intro.
      apply in_delete in H2. naive_solver.
  Qed.

  Lemma NoDup_delete_mod i xs :
    NoDup xs -> NoDup (delete_mod i xs).
  Proof.
    intro. unfold delete_mod.
    apply NoDup_delete. done.
  Qed.

  Lemma insert_mod_length i x (xs : list A) :
    length xs > 0 -> length (insert_mod i x xs) = length xs + 1.
  Proof.
    unfold insert_mod. intro.
    rewrite insert_length. done.
    pose proof (Zmod_pos_bound i (length xs)).
    naive_solver lia.
  Qed.

  Lemma insert_mod_NoDup i x (xs : list A) :
    length xs > 0 -> x ∉ xs -> NoDup xs -> NoDup (insert_mod i x xs).
  Proof.
    intros. unfold insert_mod.
    apply insert_NoDup; eauto.
    pose proof (Zmod_pos_bound i (length xs)).
    naive_solver lia.
  Qed.

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

    cut (∀ (xs : list A) (x y z : A) (i : Z),
      x ∉ xs
      → lookup_edge i xs = (z, y)
      → cycle (g ∖ graph_singleton x z ∪ graph_singleton y z) xs
      → (x, z) ∈ g
      → (x, y) ∈ g
      → (∀ xs0 : list A, ¬ cycle g xs0)
      → no_self_loops g → undirected g → x ≠ z → y ≠ z → False).
    {
      intros.
      destruct (decide (x ∈ xs)) as [Hin|]; eauto.

      admit.
    }
    intros xs x y z i.
    intros Hxnotinxs Hedge Hcycle Hxzg Hxyg tree_no_cycle0 tree_no_self_loops0
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
      + apply NoDup_delete_mod. done.
      + intros j.
        admit.
    - apply (tree_no_cycle0 (insert_mod (i+1) x xs)).
      constructor.
      + rewrite insert_mod_length; lia.
      + apply insert_mod_NoDup; eauto with lia.
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
    intros []. constructor.
    - intros ???.
      rewrite elem_of_difference in *.
      split.
      + apply tree_undirected0. naive_solver.
      + unfold graph_singleton in *. set_solver.
    - intros ??.
      rewrite elem_of_difference in H1.
      eapply tree_no_self_loops0. naive_solver.
    - intros. intro. apply (tree_no_cycle0 xs).
      destruct H1.
      constructor; eauto with lia.
      intro. specialize (cycle_cycle0 i).
      rewrite elem_of_difference in cycle_cycle0.
      naive_solver.
  Qed.

  Definition vertices (g : graph A) : gset A :=
    set_map fst g ∪ set_map snd g.

  Definition cardinality (g : graph A) : nat := size (vertices g).

  Definition no_u_turns (f : A -> option A) : Prop :=
      ∀ a b c, f a = Some b -> f b = Some c -> a ≠ c.

  (* Inductive Vertex :=
    | Thread : nat -> Vertex
    | Channel : nat -> Vertex. *)

  Fixpoint search_iter
    (g : graph A) (f : A -> option A) (a : A) (n : nat) : A :=
    match n with
    | 0 => a
    | S n => match f a with
             | None => a
             | Some a' => search_iter g f a' n
             end
    end.

  Definition search (g : graph A) (x : A) (f : A -> option A) : A :=
    search_iter g f x (cardinality g).

  (*

                                      C5
                                      |
  T1 -- C1 -- T2 -- C2 -- T3 -- C3 -- T4

  B -- T1 -- C1 -- T2

  T1 -- C1L -- C1R -- T2

              C1
              |
  B1 -- T1 -- C2 -- T2

  f(Thread n) =
    if n can take a step
    then None
    else Some (Channel that n is blocked on)

  f(Channel k) =
    if the left endpoint of k is held by a thread and the thread is blocked on k
    then Some (the channel/thread holding the right endpoint)
    else Some (the channel/thread holding the left endpoint)

  f(Channel (k,b)) =
    if we are held by a thread and the thread is blocked on us
    then Some(Channel (k, negb b)))
    else Some(the channel/thread holding us)

  T1 = recv C1
  T2 = recv C2
  T3 = 1+3; ...

  C1 = ([],[])
  C2 = ([],[]) *)

  Definition path (g : graph A) (xs : list A) :=
      ∀ i a b, xs !! i = Some a -> xs !! (i+1) = Some b -> (a,b) ∈ g.

  Definition no_u_turn (xs : list A) :=
    ∀ i a b, xs !! i = Some a -> xs !! (i+2) = Some b -> a ≠ b.

  Lemma long_path_has_duplicate_vertex (s : gset A) (xs : list A) :
    (∀ i x, xs !! i = Some x -> x ∈ s) ->
    size s < length xs ->
    ∃ i j a, xs !! i = Some a ∧ xs !! j = Some a ∧ i ≠ j.
  Proof.
    revert s. induction xs as [|x xs IH]; simpl; [lia|].
    intros s Hxs Hsize.
    destruct (decide (Exists (x=.) xs)) as [(? & Hx & <-)%Exists_exists|H2].
    - apply elem_of_list_lookup in Hx as [j Hj].
      exists 0,(S j),x.
      eauto with lia.
    - apply not_Exists_Forall in H2; [|solve_decision].
      rewrite Forall_forall in H2. simpl in *.
      assert (x ∈ s).
      { specialize (Hxs 0). naive_solver. }
      assert (∀ i x, xs !! i = Some x -> x ∈ s).
      { intros i x' Hi. specialize (Hxs (S i)). naive_solver.  }
      destruct (IH (s ∖ {[x]})) as (i & j & a & ?).
      * intros i x' Hi.
        apply elem_of_difference. split;[naive_solver|].
        apply not_elem_of_singleton_2. apply not_symmetry.
        apply H2. eapply elem_of_list_lookup_2. done.
      * assert (size s = 1 + size (s ∖ {[x]})); try lia.
        replace 1 with (size ((singleton x) : gset A)); try apply size_singleton.
        replace (size s) with (size ({[x]} ∪ s)); try apply size_union_alt.
        f_equiv. apply subseteq_union_1_L.
        rewrite <-elem_of_subseteq_singleton. done.
      * exists (S i),(S j),a. naive_solver.
  Qed.

  Lemma no_u_turn_drop (xs : list A) (k : nat) :
    no_u_turn xs -> no_u_turn (drop k xs).
  Proof.
    intros Hnut i x y Hx Hy.
    rewrite lookup_drop in Hx.
    rewrite lookup_drop in Hy.
    eapply (Hnut (k + i)). done.
    replace (k + i + 2) with (k + (i + 2)) by lia. done.
  Qed.

  Lemma lookup_take_Some (xs : list A) (k i : nat) (x : A) :
    take k xs !! i = Some x -> xs !! i = Some x.
  Proof.
    revert k i. induction xs; destruct k, i; naive_solver.
  Qed.

  Lemma no_u_turn_take (xs : list A) (k : nat) :
    no_u_turn xs -> no_u_turn (take k xs).
  Proof.
    intros Hnut i x y Hx Hy.
    eapply (Hnut i); eauto using lookup_take_Some.
  Qed.

  Lemma no_uturn_path_to_cycle (g : graph A) (xs : list A) :
    (∃ i j a, xs !! i = Some a ∧ xs !! j = Some a ∧ i < j) ->
    no_u_turn xs -> path g xs ->
    ∃ xs' x, no_u_turn ([x] ++ xs' ++ [x]) ∧ path g ([x] ++ xs' ++ [x]).
  Proof.
    intros [i [j [a (Hi & Hj & Hij)]]] Hnut Hpath.
    exists (take (j - i) (drop (i + 1) xs)), a.
    split.
    - intros k x y Hx Hy. admit.
    - intros k x y Hx Hy. admit.
  Admitted.

  Lemma no_no_uturn_cycles (g : graph A) (xs : list A) (x : A) :
    tree g -> path g ([x] ++ xs ++ [x]) ->
    no_u_turn ([x] ++ xs ++ [x]) -> False.
  Proof.
  Admitted.

  Definition valid (g : graph A) (f : A -> option A) :=
    ∀ x y, x ∈ vertices g -> f x = Some y -> (x,y) ∈ g.

  Lemma search_lemma (g : graph A) (x : A) (f : A -> option A) :
    x ∈ vertices g -> tree g -> no_u_turns f -> valid g f ->
    f (search g x f) = None.
  Admitted.