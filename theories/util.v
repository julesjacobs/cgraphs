From stdpp Require Import gmap.
From iris.bi Require Import bi.

Lemma lookup_app_lr {A} (l1 l2 : list A) {i : nat} :
  (l1 ++ l2) !! i = if decide (i < length l1) then l1 !! i else l2 !! (i - length l1).
Proof.
  case_decide.
  - apply lookup_app_l. lia.
  - apply lookup_app_r. lia.
Qed.

Lemma lookup_app_plus {A} (l1 l2 : list A) (i : nat) :
  (l1 ++ l2) !! (length l1 + i) = l2 !! i.
Proof.
  by induction l1.
Qed.

Lemma pigeon `{Countable A} (s : gset A) (xs : list A) :
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
    rewrite-> Forall_forall in H2. simpl in *.
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

Lemma lookup_take_Some {A} (xs : list A) (k i : nat) (x : A) :
  take k xs !! i = Some x -> xs !! i = Some x.
Proof.
  revert k i. induction xs; destruct k, i; naive_solver.
Qed.

Lemma lookup_take_Some_iff {A} (xs : list A) (k i : nat) (x : A) :
  take k xs !! i = Some x <-> xs !! i = Some x ∧ i < k.
Proof.
  split.
  - intros. split.
    + apply lookup_take_Some in H. done.
    + apply lookup_lt_Some in H. rewrite take_length in H. lia.
  - intros [].
    rewrite lookup_take; done.
Qed.

Fixpoint insert {T} (i : nat) (x : T) (xs : list T) : list T :=
  match i,xs with
  | 0,xs => x :: xs
  | S i',y :: xs => y :: insert i' x xs
  | S i',[] => []
  end.

Lemma lookup_insert {A} i j (x : A) xs :
  i ≤ length xs ->
  insert i x xs !! j =
    if decide (j < i) then xs !! j
    else if decide (j = i) then Some x
    else xs !! (j - 1).
Proof.
  intros Hlen. revert xs j Hlen; induction i;
  intros xs j Hlen;
  destruct xs; simpl; destruct j; simpl in *; eauto with lia.
  - f_equiv. lia.
  - rewrite IHi; last lia. repeat case_decide; eauto with lia.
    destruct j; eauto with lia. simpl. f_equiv. lia.
Qed.

Lemma insert_length {T} (i : nat) (x : T) (xs : list T) :
  i ≤ length xs -> length (insert i x xs) = length xs + 1.
Proof.
  revert i. induction xs; intros; destruct i; simpl in *; auto with lia.
Qed.

Lemma in_insert {T} (i : nat) (x a : T) (xs : list T) :
  i ≤ length xs -> (a ∈ insert i x xs <-> a = x ∨ a ∈ xs).
Proof.
  revert i; induction xs; intros; destruct i; simpl in *; rewrite ->?elem_of_cons, ?IHxs;
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

Lemma in_delete {A} x i (xs : list A) :
  x ∈ delete i xs -> x ∈ xs.
Proof.
  revert i; induction xs; intros; destruct i; simpl in *;
  eauto; rewrite elem_of_cons; eauto.
  rewrite-> elem_of_cons in H.
  destruct H; eauto.
Qed.

Lemma NoDup_delete {A} i (xs : list A) :
  NoDup xs -> NoDup (delete i xs).
Proof.
  intro. revert i; induction xs; intros; destruct i; simpl in *; eauto.
  - eapply NoDup_cons_12. done.
  - eapply NoDup_cons_2; eauto using NoDup_cons_12.
    rewrite-> list.NoDup_cons in H. intro.
    apply in_delete in H0. naive_solver.
Qed.

Lemma take_nonempty {A} (xs : list A) (k : nat) :
  k ≠ 0 -> xs ≠ [] -> take k xs ≠ [].
Proof.
  destruct k, xs; simpl; naive_solver.
Qed.

Lemma drop_nonempty {A} (xs : list A) (i : nat) (a : A) :
  xs !! i = Some a -> drop i xs ≠ [].
Proof.
  revert xs; induction i; destruct xs; simpl; naive_solver.
Qed.

Lemma drop_take_app {A} (xs : list A) n :
  xs = take n xs ++ drop n xs.
Proof.
  revert n; induction xs; simpl; intros.
  - destruct n; simpl; done.
  - destruct n; simpl; try done.
    f_equiv. eauto.
Qed.

Lemma lookup_reverse {A} i (l : list A) :
  i < length l → reverse l !! i = l !! (length l - S i).
Proof.
  revert i. induction l as [|y l IH]; intros i ?; simplify_eq/=; [done|].
  rewrite reverse_cons. destruct (decide (i = length l)) as [->|].
  - by rewrite ->lookup_app_r, reverse_length, Nat.sub_diag
      by (by rewrite reverse_length).
  - rewrite ->lookup_app_l, IH by (rewrite ?reverse_length; lia).
    by replace (length l - i) with (S (length l - S i)) by lia.
Qed.

Lemma lookup_reverse_Some {A} i a (l : list A) :
  reverse l !! i = Some a -> l !! (length l - S i) = Some a.
Proof.
  destruct (decide (i < length l)).
  - rewrite lookup_reverse; done.
  - intro. apply lookup_lt_Some in H. rewrite reverse_length in H. lia.
Qed.

Lemma lookup_reverse_Some_iff {A} i a (l : list A) :
  reverse l !! i = Some a <-> l !! (length l - S i) = Some a ∧ i < length l.
Proof.
  destruct (decide (i < length l)).
  - rewrite lookup_reverse;[|done]. naive_solver.
  - split.
    + intro. apply lookup_lt_Some in H. rewrite reverse_length in H. lia.
    + naive_solver lia.
Qed.

Lemma lookup_singleton_Some {A} (a b : A) i :
  [a] !! i = Some b <-> i = 0 ∧ a = b.
Proof.
  destruct i; simpl. naive_solver.
  destruct i; simpl; naive_solver.
Qed.

Lemma lookup_delete_lr {A} (xs : list A) (i j : nat) :
  delete i xs !! j = if decide (j < i) then xs !! j else xs !! (S j).
Proof.
  case_decide.
  - rewrite lookup_delete_lt; done.
  - rewrite lookup_delete_ge. done. lia.
Qed.

Lemma split_first {A} (xs : list A) a :
  xs !! 0 = Some a -> xs = [a] ++ drop 1 xs.
Proof.
  intros. destruct xs; simpl in *; simplify_eq. rewrite drop_0. done.
Qed.

Lemma last_lookup {A} (xs : list A) :
  last xs = xs !! (length xs - 1).
Proof.
  induction xs; simpl. done.
  destruct xs; simpl in *. done.
  rewrite Nat.sub_0_r in IHxs. done.
Qed.

Lemma split_last {A} (xs : list A) a :
  last xs = Some a -> xs = take (length xs - 1) xs ++ [a].
Proof.
  rewrite last_lookup.
  intro.
  assert ([a] = drop (length xs - 1) xs).
  {
    induction xs; simpl. simplify_eq.
    rewrite Nat.sub_0_r.
    simpl in *. rewrite Nat.sub_0_r in H.
    destruct xs; simpl in *. simplify_eq. done.
    rewrite Nat.sub_0_r in IHxs.
    eauto.
  }
  rewrite H0.
  rewrite take_drop. done.
Qed.

Lemma last_take {A} i (xs : list A) :
  i < length xs -> last (take (S i) xs) = xs !! i.
Proof.
  intro.
  rewrite last_lookup.
  rewrite lookup_take; rewrite take_length.
  { f_equiv. lia. } lia.
Qed.

Lemma last_take_Some {A} i (xs : list A) a :
  xs !! i = Some a -> last (take (S i) xs) = Some a.
Proof.
  intro.
  rewrite last_take; first done.
  apply lookup_lt_Some in H. done.
Qed.

Lemma last_drop {A} (xs : list A) i :
  i < length xs -> last (drop i xs) = last xs.
Proof.
  intros Hlt.
  rewrite !last_lookup.
  rewrite lookup_drop.
  f_equiv. rewrite drop_length. lia.
Qed.

Lemma lookup_update {A} i j (xs : list A) x :
  (<[ i := x ]> xs) !! j = if decide (i = j ∧ j < length xs) then Some x else xs !! j.
Proof.
  revert i j; induction xs; intros i j; destruct i,j; simpl; eauto.
  - case_decide. lia. done.
  - rewrite IHxs. clear IHxs. repeat case_decide; eauto with lia.
Qed.

Section disjoint.
  Context `{Countable K}.
  Context {V : Type}.

  Definition disjoint (xs : list (gmap K V)) :=
    forall i j h1 h2,
        xs !! i = Some h1 -> xs !! j = Some h2 -> i ≠ j -> h1 ##ₘ h2.

  Lemma disjoint_nil : disjoint [].
  Proof.
    intros j1 j2 h1 h2 Hs1 Hs2 Hneq; simplify_eq.
  Qed.

  Lemma disjoint_singleton g : disjoint [g].
  Proof.
    intros [] [] h1 h2 Hs1 Hs2 Hneq; simplify_eq.
  Qed.

  Lemma disjoint_two g1 g2 : g1 ##ₘ g2 -> disjoint [g1; g2].
  Proof.
    intros Hdisj j1 j2 h1 h2 Hs1 Hs2 Hneq.
    destruct j1; destruct j2; try destruct j1; try destruct j2; try lia; simpl in *;
    simplify_eq; eauto.
  Qed.

  Lemma disjoint_cons g gs :
    (∀ g', g' ∈ gs -> g ##ₘ g') -> disjoint gs -> disjoint (g::gs).
  Proof.
    intros Hdisj1 Hdisj2.
    intros j1 j2 h1 h2 Hs1 Hs2 Hneq.
    destruct j1; destruct j2; try lia; simpl in *; simplify_eq.
    - eauto using elem_of_list_lookup_2.
    - symmetry. eauto using elem_of_list_lookup_2.
    - unfold disjoint in *. eauto.
  Qed.

  Lemma disjoint_delete gs i:
    disjoint gs -> disjoint (delete i gs).
  Proof.
    intros Hdisj j1 j2 h1 h2 Hs1 Hs2 Hneq.
    rewrite lookup_delete_lr in Hs1.
    rewrite lookup_delete_lr in Hs2.
    repeat case_decide; simpl in *; unfold disjoint in *; eauto with lia.
  Qed.

  Lemma disjoint_insert gs g i :
    (∀ g', g' ∈ gs -> g ##ₘ g') -> disjoint gs -> disjoint (insert i g gs).
  Proof.
    destruct (decide (length gs < i)).
    { rewrite insert_out_of_bounds; eauto with lia. }
    intros HH Hdisj j1 j2 h1 h2 Hs1 Hs2 Hneq.
    rewrite lookup_insert in Hs1; last lia.
    rewrite lookup_insert in Hs2; last lia.
    repeat case_decide; simpl in *; simplify_eq;
    unfold disjoint in *;
    eauto using elem_of_list_lookup_2 with lia; symmetry;
    eauto using elem_of_list_lookup_2 with lia.
  Qed.

  Lemma disjoint_update gs g i :
    (∀ g', g' ∈ gs -> g ##ₘ g') -> disjoint gs -> disjoint (<[ i := g ]> gs).
  Proof.
    destruct (decide (length gs <= i)).
    { rewrite list_insert_ge; eauto with lia. }
    intros HH Hdisj j1 j2 h1 h2 Hs1 Hs2 Hneq.
    rewrite lookup_update in Hs1.
    rewrite lookup_update in Hs2.
    repeat case_decide; simpl in *; simplify_eq;
    unfold disjoint in *;
    eauto using elem_of_list_lookup_2 with lia; symmetry;
    eauto using elem_of_list_lookup_2 with lia.
  Qed.

  Lemma disjoint_app_singleton gs g :
    (∀ g', g' ∈ gs -> g ##ₘ g') -> disjoint gs -> disjoint (gs ++ [g]).
  Proof.
    intros HH Hdisj j1 j2 h1 h2 Hs1 Hs2 Hneq.
    rewrite lookup_app_lr in Hs1.
    rewrite lookup_app_lr in Hs2.
    unfold disjoint in *.
    case_decide; case_decide;
      try apply lookup_singleton_Some in Hs1 as [];
      try apply lookup_singleton_Some in Hs2 as []; subst;
      eauto using elem_of_list_lookup_2 with lia; symmetry;
      eauto using elem_of_list_lookup_2 with lia.
  Qed.
End disjoint.
