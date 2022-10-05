From stdpp Require Import gmap.
From stdpp Require Export finite.
From cgraphs.cgraphs Require Export multiset.

Lemma list_lookup_insert_spec {V} (xs : list V) i j v :
  (<[ i := v ]> xs) !! j = if (decide (i = j ∧ i < length xs)) then Some v else (xs !! j).
Proof.
  case_decide.
  - destruct H. subst. apply list_lookup_insert; done.
  - destruct (decide (i < length xs)).
    + assert (i ≠ j) by naive_solver. apply list_lookup_insert_ne. done.
    + rewrite list_insert_ge; [done|lia].
Qed.

From iris.bi Require Import bi.

Lemma insert_subseteq_None `{Countable K} {V} (m m' : gmap K V) i v :
  m !! i = None ->
  <[ i := v ]> m ⊆ m' ->
  m ⊆ m' ∧ m' !! i = Some v.
Proof.
  rewrite !map_subseteq_spec.
  intros H1 H2.
  split.
  - intros. apply H2.
    destruct (decide (i = i0)); simplify_eq.
    rewrite lookup_insert_ne //.
  - apply H2. rewrite lookup_insert //.
Qed.

Lemma fmap_map_disjoint `{Countable K} {V1 V2} (f : V1 -> V2) (m1 m2 : gmap K V1) :
  m1 ##ₘ m2 -> f <$> m1 ##ₘ f <$> m2.
Proof.
  intros HH.
  intros x. rewrite !lookup_fmap.
  specialize (HH x).
  destruct (m1 !! x); destruct (m2 !! x); try done.
Qed.

Lemma fmap_singleton_inv `{Countable K} {V1 V2} (f : V1 -> V2) (x : gmap K V1) (k : K) (v : V2) :
  f <$> x = {[ k := v ]} -> ∃ v' : V1, x = {[ k := v' ]}.
Proof.
  intros HH.
  rewrite ->map_eq_iff in HH.
  pose proof (HH k) as H'.
  rewrite lookup_fmap in H'.
  rewrite lookup_singleton in H'.
  destruct (x !! k) eqn:E; simpl in *; simplify_eq.
  exists v0.
  rewrite map_eq_iff.
  intros. specialize (HH i).
  rewrite lookup_fmap in HH.
  destruct (decide (i = k)).
  - subst. rewrite lookup_singleton in HH. rewrite lookup_singleton.
    destruct (x !! k); simplify_eq. done.
  - rewrite lookup_singleton_ne in HH; eauto.
    rewrite lookup_singleton_ne; eauto.
    destruct (x !! i); simplify_eq. done.
Qed.

Lemma singleton_eq_iff `{Countable K} {V} (k1 k2 : K) (v1 v2 : V) :
  ({[ k1 := v1 ]} : gmap K V) = {[ k2 := v2 ]} <-> k1 = k2 ∧ v1 = v2.
Proof.
  split; last naive_solver.
  intros HH.
  rewrite ->map_eq_iff in HH.
  specialize (HH k1).
  rewrite lookup_singleton in HH.
  destruct (decide (k1 = k2)); subst.
  - rewrite lookup_singleton in HH. simplify_eq; done.
  - rewrite lookup_singleton_ne in HH. simplify_eq. done.
Qed.

Lemma dec_exists_list {A} (P : A → Prop) (xs : list A) :
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

Lemma dec_forall_list {A} (P : A → Prop) (xs : list A) :
  (∀ x, P x ∨ x ∈ xs) → (∀ x, x ∈ xs → Decision (P x)) → Decision (∀ x, P x).
  intros HPxs Hdec.
  Proof.
  induction xs as [|x xs IHxs]. { left. set_solver. }
  assert (Decision (P x)) as [] by (apply Hdec; set_solver);
    [|right;naive_solver].
  apply IHxs.
  - intros x'. destruct (HPxs x').
    + set_solver.
    + assert (x' = x ∨ x' ∈ xs) as []; set_solver.
  - intros ??. apply Hdec. set_solver.
Qed.

Lemma lookup_app_lr {A} (l1 l2 : list A) {i : nat} :
  (l1 ++ l2) !! i = if decide (i < length l1) then l1 !! i else l2 !! (i - length l1).
Proof.
  case_decide.
  - apply lookup_app_l. lia.
  - apply lookup_app_r. lia.
Qed.

Lemma list_lookup_singleton_spec {A} (a : A) {i : nat} :
  [a] !! i = if decide (i = 0) then Some a else None.
Proof.
  destruct i; simpl; eauto.
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
    { intros. apply elem_of_difference.
      split;[naive_solver|].
      apply not_elem_of_singleton_2. apply not_symmetry.
      apply H2. eapply elem_of_list_lookup_2. done. }
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


Fixpoint insert2 {T} (i : nat) (x : T) (xs : list T) : list T :=
  match i,xs with
  | 0,xs => x :: xs
  | S i',y :: xs => y :: insert2 i' x xs
  | S i',[] => [x]
  end.

Lemma lookup_insert2' {A} i j (x : A) xs :
  i ≤ length xs ->
  insert2 i x xs !! j =
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

Lemma insert2_length {T} (i : nat) (x : T) (xs : list T) :
  length (insert2 i x xs) = length xs + 1.
Proof.
  revert i. induction xs; intros; destruct i; simpl in *; auto with lia.
Qed.

Lemma in_insert2 {T} (i : nat) (x a : T) (xs : list T) :
  a ∈ insert2 i x xs <-> a = x ∨ a ∈ xs.
Proof.
  revert i; induction xs; intros; destruct i; simpl in *; rewrite ->?elem_of_cons, ?IHxs;
  rewrite ?elem_of_cons; naive_solver lia.
Qed.

Lemma insert2_NoDup {T} (i : nat) (x : T) (xs : list T) :
  x ∉ xs ∧ NoDup xs <-> NoDup (insert2 i x xs).
Proof.
  revert i; induction xs; destruct i; simpl; intros;
  rewrite ?list.NoDup_cons; eauto with lia.
  rewrite <-IHxs, in_insert2, not_elem_of_cons; naive_solver lia.
Qed.

Lemma insert2_out_of_bounds {T} (i : nat) (x : T) (xs : list T) :
  i > length xs -> insert2 i x xs = xs ++ [x].
Proof.
  revert i; induction xs; destruct i; simpl; intros; try f_equiv; eauto with lia.
Qed.

Lemma insert2_NoDup_2 {T} (i : nat) (x : T) (xs : list T) :
  x ∉ xs -> NoDup xs -> NoDup (insert2 i x xs).
Proof.
  rewrite <-insert2_NoDup. eauto.
Qed.

Lemma insert2_delete {T} (i : nat) (x : T) (xs : list T) :
  i ≤ length xs -> delete i (insert2 i x xs) = xs.
Proof.
  revert i; induction xs; destruct i; simpl; try f_equiv; eauto with lia.
  intro. f_equiv. rewrite IHxs; eauto with lia.
Qed.

Lemma delete_insert2' {T} (i : nat) (x : T) (xs : list T) :
  xs !! i = Some x -> insert2 i x (delete i xs) = xs.
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
  - eapply NoDup_cons_1_2. done.
  - eapply NoDup_cons_2; eauto using NoDup_cons_1_2.
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

Lemma lookup_union_Some' `{Countable K} {V} (A B : gmap K V) x v :
  A ##ₘ B ->
  (A ∪ B) !! x = Some v ->
  (A !! x = Some v ∧ B !! x = None) ∨ (B !! x = Some v ∧ A !! x = None).
Proof.
  intros Hdisj Hl.
  apply lookup_union_Some in Hl as []; eauto; [left | right]; split; eauto;
  rewrite ->map_disjoint_alt in Hdisj; specialize (Hdisj x);
  destruct (A !! x); naive_solver.
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

  Lemma disjoint_cons_weaken g gs :
    disjoint (g::gs) -> disjoint gs.
  Proof.
    intros Hdisj.
    intros j1 j2 h1 h2 Hs1 Hs2 Hneq.
    eapply (Hdisj (S j1) (S j2)); eauto with lia.
  Qed.

  Lemma disjoint_cons_alt g gs :
    disjoint (g::gs) <-> Forall (λ g', g ##ₘ g') gs ∧ disjoint gs.
  Proof.
    split.
    - intros Hdisj. split; last by eapply disjoint_cons_weaken.
      rewrite Forall_forall.
      intros h Hin.
      eapply elem_of_list_lookup in Hin as [? ?].
      eapply (Hdisj 0 (S x)); eauto with lia.
    - intros [Hfa Hdisj].
      rewrite ->Forall_forall in Hfa.
      eapply disjoint_cons; eauto.
  Qed.

  Lemma disjoint_delete gs i:
    disjoint gs -> disjoint (delete i gs).
  Proof.
    intros Hdisj j1 j2 h1 h2 Hs1 Hs2 Hneq.
    rewrite lookup_delete_lr in Hs1.
    rewrite lookup_delete_lr in Hs2.
    repeat case_decide; simpl in *; unfold disjoint in *; eauto with lia.
  Qed.

  Lemma disjoint_update gs g i :
    (∀ j g', gs !! j = Some g' -> i ≠ j -> g ##ₘ g') ->
    disjoint gs -> disjoint (<[ i := g ]> gs).
  Proof.
    destruct (decide (length gs <= i)).
    { rewrite list_insert_ge; eauto with lia. }
    intros HH Hdisj j1 j2 h1 h2 Hs1 Hs2 Hneq.
    rewrite lookup_update in Hs1.
    rewrite lookup_update in Hs2.
    repeat case_decide.
    - destruct H0,H1. simplify_eq.
    - destruct H0. simplify_eq. symmetry. eauto.
    - destruct H1. simplify_eq. eauto.
    - eauto.
  Qed.

  Lemma disjoint_weaken gs gs' :
    gs' ⊆* gs -> disjoint gs -> disjoint gs'.
  Proof.
    intros Hsub Hdisj.
    intros j1 j2 h1 h2 Hs1 Hs2 Hneq.
    eapply Forall2_lookup_l in Hs1; last done.
    eapply Forall2_lookup_l in Hs2; last done.
    destruct Hs1 as (h1' & Hs1 & Hsub1).
    destruct Hs2 as (h2' & Hs2 & Hsub2).
    eapply map_disjoint_weaken.
    - eapply Hdisj; last done; eauto.
    - done.
    - done.
  Qed.

  Lemma sublist_elem_of {A} (x : A) (xs ys : list A) :
    sublist xs ys -> x ∈ xs -> x ∈ ys.
  Proof.
    induction 1; rewrite ?elem_of_cons; naive_solver.
  Qed.

  Lemma sublist_Forall {A} P (xs ys : list A) :
    sublist xs ys -> Forall P ys -> Forall P xs.
  Proof.
    rewrite !Forall_forall. eauto using sublist_elem_of.
  Qed.

  Lemma disjoint_sublist gs gs' :
    sublist gs' gs -> disjoint gs -> disjoint gs'.
  Proof.
    intros Hsub Hdisj.
    induction Hsub.
    - apply disjoint_nil.
    - apply disjoint_cons_alt in Hdisj as [].
      rewrite ->disjoint_cons_alt. split; eauto.
      eapply sublist_Forall; eauto.
    - apply IHHsub. eapply disjoint_cons_weaken; eauto.
  Qed.

  Lemma disjoint_update_sub gs g g' i :
    gs !! i = Some g -> g' ⊆ g -> disjoint gs -> disjoint (<[i := g']> gs).
  Proof.
    intros Hsome Hsub Hdisj.
    eapply disjoint_update; last done.
    intros j h Hin Hneq.
    eapply map_disjoint_weaken_l; last done.
    eapply Hdisj; eauto.
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

  Lemma disjoint_insert gs g i :
    (∀ g', g' ∈ gs -> g ##ₘ g') -> disjoint gs -> disjoint (insert2 i g gs).
  Proof.
    destruct (decide (length gs < i)).
    { rewrite insert2_out_of_bounds; eauto with lia.
      intros. apply disjoint_app_singleton; eauto. }
    intros HH Hdisj j1 j2 h1 h2 Hs1 Hs2 Hneq.
    rewrite lookup_insert2' in Hs1; last lia.
    rewrite lookup_insert2' in Hs2; last lia.
    repeat case_decide; simpl in *; simplify_eq;
    unfold disjoint in *;
    eauto using elem_of_list_lookup_2 with lia; symmetry;
    eauto using elem_of_list_lookup_2 with lia.
  Qed.
End disjoint.

Lemma map_disjoint_self_empty `{Countable K} {V} (m : gmap K V) :
  m ##ₘ m -> m = ∅.
Proof.
  intros HH.
  apply map_empty. intro.
  specialize (HH i).
  destruct (m !! i); eauto; done.
Qed.

Definition fin_list {A} n (f : fin n -> A) : list A := vec_to_list (fun_to_vec f).

Lemma fin_list_lookup {A} n (f : fin n -> A) (i : fin n) :
  fin_list n f !! fin_to_nat i = Some (f i).
Proof.
  unfold fin_list.
  rewrite -vlookup_lookup lookup_fun_to_vec //.
Qed.

Lemma fin_list_length {A} n (f : fin n -> A) :
  length (fin_list n f) = n.
Proof.
  unfold fin_list.
  rewrite vec_to_list_length //.
Qed.

Lemma fin_list_lookup_ne {A} n (f : fin n -> A) (i : nat) :
  i >= n -> fin_list n f !! i = None.
Proof.
  intros. destruct (fin_list n f !! i) eqn:E; eauto.
  exfalso. eapply lookup_lt_Some in E. rewrite fin_list_length in E. lia.
Qed.


Definition fin_gset `{Countable A} n (f : fin n -> A) : gset A
  := list_to_set (fin_list n f).

Lemma elem_of_fin_gset `{Countable A} n (f : fin n -> A) (x : A) :
  x ∈ fin_gset n f <-> ∃ i, f i = x.
Proof.
  unfold fin_gset.
  rewrite elem_of_list_to_set elem_of_list_lookup.
  split.
  - intros [i Hi].
    assert (i < n) as Q.
    { eapply lookup_lt_Some in Hi. rewrite fin_list_length in Hi. done. }
    replace i with (fin_to_nat (nat_to_fin Q)) in Hi
      by rewrite fin_to_nat_to_fin //.
    rewrite fin_list_lookup in Hi. naive_solver.
  - intros [i Hi]. exists (fin_to_nat i).
    rewrite fin_list_lookup. by f_equal.
Qed.

Definition all_fin n := fin_gset n id.

Lemma all_fin_all n : ∀ i, i ∈ all_fin n.
Proof.
  intro. apply elem_of_fin_gset. eauto.
Qed.

Definition big_union `{Countable A} : gset (gset A) -> gset A := set_fold (∪) ∅.

Lemma elem_of_big_union `{Countable A} (s : gset (gset A)) (x : A) :
  x ∈ big_union s <-> ∃ a, a ∈ s ∧ x ∈ a.
Proof.
  eapply (set_fold_ind_L (λ y s, x ∈ y ↔ (∃ a, a ∈ s ∧ x ∈ a))); first set_solver.
  intros. rewrite elem_of_union H1. set_solver.
Qed.

Definition fin_union `{Countable A} n (f : fin n -> gset A) : gset A :=
  big_union (fin_gset n f).

Lemma elem_of_fin_union `{Countable A} n (f : fin n -> gset A) (x : A) :
  x ∈ fin_union n f <-> ∃ i, x ∈ f i.
Proof.
  unfold fin_union.
  rewrite elem_of_big_union.
  setoid_rewrite elem_of_fin_gset.
  naive_solver.
Qed.

Fixpoint list_to_mapi' {A} (xs : list A) (n : nat) : gmap nat A :=
  match xs with
  | [] => ∅
  | x::r => <[ n := x ]> (list_to_mapi' r (S n))
  end.

Definition list_to_mapi {A} (xs : list A) := list_to_mapi' xs 0.

Lemma list_to_mapi'_lookup {A} (xs : list A) (i n : nat) :
  i >= n -> list_to_mapi' xs n !! i = xs !! (i - n).
Proof.
  revert i n. induction xs; simpl; intros.
  - rewrite !lookup_empty. by destruct (i - n).
  - rewrite lookup_insert_spec lookup_cons.
    case_decide; subst.
    + replace (i - i) with 0 by lia. done.
    + destruct (i - n) eqn:E; try lia.
      erewrite IHxs; last lia.
      f_equal. lia.
Qed.

Lemma list_to_mapi_lookup {A} (xs : list A) (i : nat) :
  list_to_mapi xs !! i = xs !! i.
Proof.
  unfold list_to_mapi. rewrite list_to_mapi'_lookup; f_equal; lia.
Qed.

Definition fin_gmap {T} n : (fin n -> T) -> gmap nat T := list_to_mapi ∘ fin_list n.

Lemma fin_gmap_lookup {T} n (f : fin n -> T) (i : fin n) :
  fin_gmap n f !! (fin_to_nat i) = Some (f i).
Proof.
  unfold fin_gmap. simpl.
  rewrite list_to_mapi_lookup fin_list_lookup //.
Qed.

Lemma fin_gmap_lookup_ne {T} n (f : fin n -> T) (k : nat) :
  k >= n -> fin_gmap n f !! k = None.
Proof.
  unfold fin_gmap. simpl. intros.
  rewrite list_to_mapi_lookup fin_list_lookup_ne //.
Qed.

Lemma lookup_alter_spec `{Countable K} {V} (f : V -> V) (m : gmap K V) i j :
  alter f i m !! j = if decide (i = j) then f <$> m !! i else m !! j.
Proof.
  case_decide; subst.
  - rewrite lookup_alter //.
  - rewrite lookup_alter_ne //.
Qed.

Definition gmap_slice `{Countable K1, Countable K2} {A} (m : gmap (K1 * K2) A) (x : K1) : gmap K2 A :=
  default ∅ (gmap_curry m !! x).

Lemma gmap_slice_lookup `{Countable K1, Countable K2} {A}
(m : gmap (K1*K2) A) x y :
  gmap_slice m x !! y = m !! (x,y).
Proof.
  unfold gmap_slice.
  destruct (gmap_curry m !! x) eqn:E; simpl.
  - rewrite -lookup_gmap_curry E //.
  - rewrite ->lookup_gmap_curry_None in E.
    rewrite E lookup_empty //.
Qed.

Lemma gmap_slice_alter `{Countable K1, Countable K2} {A} (f : A -> A)
  (m : gmap (K1*K2) A) x y x' :
  gmap_slice (alter f (x,y) m) x' =
    if decide (x = x')
    then alter f y (gmap_slice m x')
    else gmap_slice m x'.
Proof.
  eapply map_eq. intros.
  case_decide; subst;
  rewrite !gmap_slice_lookup ?lookup_alter_spec; repeat case_decide;
  simplify_eq; eauto; rewrite gmap_slice_lookup //.
Qed.

Lemma gmap_slice_insert `{Countable K1, Countable K2} {A}
  (m : gmap (K1*K2) A) x y x' v :
  gmap_slice (<[ (x,y) := v ]> m) x' =
    if decide (x = x')
    then <[ y := v ]> (gmap_slice m x')
    else gmap_slice m x'.
Proof.
  eapply map_eq. intros.
  case_decide; subst; rewrite !gmap_slice_lookup ?lookup_insert_spec;
  repeat case_decide; simplify_eq; rewrite // gmap_slice_lookup //.
Qed.

Lemma gmap_slice_delete `{Countable K1, Countable K2} {A}
  (m : gmap (K1*K2) A) x y x' :
  gmap_slice (delete (x,y) m) x' =
    if decide (x = x')
    then delete y (gmap_slice m x')
    else gmap_slice m x'.
Proof.
  eapply map_eq. intros.
  case_decide; subst; rewrite !gmap_slice_lookup ?lookup_delete_spec;
  repeat case_decide; simplify_eq; rewrite // gmap_slice_lookup //.
Qed.

Lemma gmap_slice_empty `{Countable K1, Countable K2} {A} (x : K1) :
  gmap_slice (∅ : gmap (K1*K2) A) x = ∅.
Proof.
  eapply map_eq. intros.
  rewrite gmap_slice_lookup !lookup_empty //.
Qed.

Lemma gmap_slice_union `{Countable K1, Countable K2} {A} (m1 m2 : gmap (K1*K2) A) (x : K1) :
  gmap_slice (m1 ∪ m2) x = gmap_slice m1 x ∪ gmap_slice m2 x.
Proof.
  eapply map_eq. intros.
  rewrite lookup_union !gmap_slice_lookup lookup_union //.
Qed.

Definition gmap_unslice `{Countable K1, Countable K2} {A} (m : gmap K2 A) (x : K1) : gmap (K1 * K2) A :=
  map_kmap (λ y, (x,y)) m.

Lemma gmap_slice_unslice `{Countable K1, Countable K2} {A} (m : gmap K2 A) (x y : K1) :
  gmap_slice (gmap_unslice m x) y = if decide (x = y) then m else ∅.
Proof.
  eapply map_eq. intros i.
  rewrite gmap_slice_lookup.
  unfold gmap_unslice.
  case_decide.
  - subst. rewrite lookup_map_kmap //.
  - rewrite lookup_empty lookup_map_kmap_None.
    intros; simplify_eq.
Qed.

Lemma imap_fin_list {A B} n (g : nat -> A -> B) (f : fin n -> A) :
  imap g (fin_list n f) = fin_list n (λ i, g (fin_to_nat i) (f i)).
Proof.
  eapply list_eq. intros.
  rewrite list_lookup_imap.
  destruct (decide (i < n)) as [H|H].
  - rewrite -(fin_to_nat_to_fin _ _ H).
    rewrite !fin_list_lookup //.
  - rewrite !fin_list_lookup_ne //; lia.
Qed.

Lemma list_to_mapi_imap {A} (xs : list A) :
  list_to_mapi xs = list_to_map (imap (λ i a, (i,a)) xs).
Proof.
  apply map_eq. intros.
  rewrite list_to_mapi_lookup.
  destruct (list_to_map (imap (λ (i0 : nat) (a : A), (i0, a)) xs) !! i) eqn:E.
  - eapply elem_of_list_to_map_2 in E.
    eapply elem_of_lookup_imap_1 in E as (j & y & H1 & H2).
    by simplify_eq.
  - eapply not_elem_of_list_to_map_2 in E.
    rewrite fmap_imap in E.
    rewrite ->elem_of_lookup_imap in E.
    destruct (xs !! i) eqn:F; eauto.
    exfalso. apply E. eauto.
Qed.

Definition fin_multiset {A} n (f : fin n -> A) : multiset A :=
  list_to_multiset (fin_list n f).

Lemma fin_multiset_gmap {A:ofe} n (f : fin n -> A) :
  fin_multiset n (λ m, (fin_to_nat m, f m)) ≡ map_to_multiset (fin_gmap n f).
Proof.
  unfold fin_multiset, fin_gmap, map_to_multiset. simpl.
  rewrite list_to_mapi_imap map_to_list_to_map.
  - rewrite imap_fin_list //.
  - rewrite fmap_imap NoDup_alt. intros ???.
    rewrite !list_lookup_imap.
    destruct (fin_list n f !! i) eqn:E; last naive_solver.
    destruct (fin_list n f !! j) eqn:F; naive_solver.
Qed.

Lemma fin_list_0 {A} (f : fin 0 -> A) : fin_list 0 f = [].
Proof. done. Qed.

Lemma fin_gset_0 `{Countable A} (f : fin 0 -> A) : fin_gset 0 f = ∅.
Proof. done. Qed.

Lemma fin_gmap_0 {A} (f : fin 0 -> A) : fin_gmap 0 f = ∅.
Proof. done. Qed.

Lemma fin_multiset_0 {A : ofe} (f : fin 0 -> A) : fin_multiset 0 f = ε.
Proof. done. Qed.

Lemma fin_union_0 `{Countable A} (f : fin 0 -> gset A) : fin_union 0 f = ∅.
Proof. done. Qed.


Lemma fin_list_S {A} n (f : fin (S n) -> A) :
  fin_list (S n) f = f 0%fin :: fin_list n (λ i, f (FS i)).
Proof. done. Qed.

Lemma fin_gset_S `{Countable A} n (f : fin (S n) -> A) :
  fin_gset (S n) f = {[ f 0%fin ]} ∪ fin_gset n (λ i, f (FS i)).
Proof. done. Qed.

Lemma fin_gmap_dom {A} n (f : fin n -> A) (k : nat) :
  k ∈ dom (fin_gmap n f) <-> k < n.
Proof.
  rewrite elem_of_dom.
  destruct (decide (k < n)) as [H|H].
  - rewrite -(fin_to_nat_to_fin _ _ H).
    rewrite fin_gmap_lookup.
    erewrite !fin_to_nat_to_fin. naive_solver.
  - rewrite fin_gmap_lookup_ne; last lia.
    split; intros; try lia.
    destruct H0. discriminate.
Qed.

Lemma fin_multiset_S {A : ofe} n (f : fin (S n) -> A) :
  fin_multiset (S n) f = {[ f 0%fin ]} ⋅ fin_multiset n (λ i, f (FS i)).
Proof. done. Qed.

Lemma big_union_empty `{Countable A} :
  big_union (∅ : gset (gset A)) = ∅.
Proof. done. Qed.

Lemma big_union_singleton `{Countable A} (a : gset A) :
  big_union {[ a ]} = a.
Proof.
  unfold big_union.
  rewrite set_fold_singleton right_id_L //.
Qed.

Lemma big_union_singleton_union `{Countable A} (a : gset A) (b : gset (gset A)) :
  big_union ({[ a ]} ∪ b) = a ∪ big_union b.
Proof.
  destruct (decide (a ∈ b)) as [Q|Q].
  - rewrite subseteq_union_1_L; last rewrite singleton_subseteq_l //.
    eapply set_eq. intros.
    rewrite elem_of_union.
    rewrite !elem_of_big_union.
    set_solver.
  - unfold big_union.
    assert (a ∪ set_fold union ∅ b =
        set_fold union (set_fold union ∅ b) ({[ a ]} : gset (gset A))) as ->.
    { rewrite set_fold_singleton //. }
    rewrite -set_fold_disj_union; last set_solver.
    rewrite comm_L //.
Qed.

Lemma big_union_union `{Countable A} (a b : gset (gset A)) :
  big_union (a ∪ b) = big_union a ∪ big_union b.
Proof.
  revert b. induction a using set_ind_L; intros.
  - rewrite big_union_empty !left_id_L //.
  - rewrite -assoc_L !big_union_singleton_union IHa assoc_L //.
Qed.

Lemma fin_union_S `{Countable A} n (f : fin (S n) -> gset A) :
  fin_union (S n) f = (f 0%fin) ∪ fin_union n (λ i, f (FS i)).
Proof.
  unfold fin_union.
  rewrite fin_gset_S big_union_union big_union_singleton //.
Qed.
