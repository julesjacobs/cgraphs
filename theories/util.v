From stdpp Require Import gmap.

Definition map_kmap `{∀ A, Insert K2 A (M2 A), ∀ A, Empty (M2 A),
    ∀ A, FinMapToList K1 A (M1 A)} {A} (f : K1 → K2) (m : M1 A) : M2 A :=
  list_to_map (fmap (prod_map f id) (map_to_list m)).

Section map_kmap.
  Context `{FinMap K1 M1} `{FinMap K2 M2}.
  Context (f : K1 → K2) `{!Inj (=) (=) f}.
  Local Notation map_kmap := (map_kmap (M1:=M1) (M2:=M2)).

  Lemma lookup_map_kmap_Some {A} (m : M1 A) (j : K2) x :
    map_kmap f m !! j = Some x ↔ ∃ i, j = f i ∧ m !! i = Some x.
  Proof.
    assert (∀ x',
      (j, x) ∈ prod_map f id <$> map_to_list m →
      (j, x') ∈ prod_map f id <$> map_to_list m → x = x').
    { intros x'. rewrite !elem_of_list_fmap.
      intros [[? y1] [??]] [[? y2] [??]]; simplify_eq/=.
      by apply (map_to_list_unique m k). }
    unfold map_kmap. rewrite <-elem_of_list_to_map', elem_of_list_fmap by done.
    setoid_rewrite elem_of_map_to_list'. split.
    - intros [[??] [??]]; naive_solver.
    - intros [? [??]]. eexists (_, _); naive_solver.
  Qed.
  Lemma lookup_map_kmap_is_Some {A} (m : M1 A) (j : K2) :
    is_Some (map_kmap f m !! j) ↔ ∃ i, j = f i ∧ is_Some (m !! i).
  Proof. unfold is_Some. setoid_rewrite lookup_map_kmap_Some. naive_solver. Qed.
  Lemma lookup_map_kmap_None {A} (m : M1 A) (j : K2) :
    map_kmap f m !! j = None ↔ ∀ i, j = f i → m !! i = None.
  Proof.
    setoid_rewrite eq_None_not_Some.
    rewrite lookup_map_kmap_is_Some. naive_solver.
  Qed.
  Lemma lookup_map_kmap {A} (m : M1 A) (i : K1) :
    map_kmap f m !! f i = m !! i.
  Proof. apply option_eq. setoid_rewrite lookup_map_kmap_Some. naive_solver. Qed.
  Lemma lookup_total_map_kmap `{Inhabited A} (m : M1 A) (i : K1) :
    map_kmap f m !!! f i = m !!! i.
  Proof. by rewrite !lookup_total_alt, lookup_map_kmap. Qed.

  Lemma map_kmap_empty {A} : map_kmap f ∅ =@{M2 A} ∅.
  Proof. unfold map_kmap. by rewrite map_to_list_empty. Qed.
  Lemma map_kmap_singleton {A} i (x : A) : map_kmap f {[ i := x ]} = {[ f i := x ]}.
  Proof. unfold map_kmap. by rewrite map_to_list_singleton. Qed.

  Lemma map_kmap_partial_alter {A} (g : option A → option A) (m : M1 A) i :
    map_kmap f (partial_alter g i m) = partial_alter g (f i) (map_kmap f m).
  Proof.
    apply map_eq; intros j. apply option_eq; intros y.
    destruct (decide (j = f i)) as [->|?].
    { by rewrite lookup_partial_alter, !lookup_map_kmap, lookup_partial_alter. }
    rewrite lookup_partial_alter_ne, !lookup_map_kmap_Some by done. split.
    - intros [i' [? Hm]]; simplify_eq/=.
      rewrite lookup_partial_alter_ne in Hm by naive_solver. naive_solver.
    - intros [i' [? Hm]]; simplify_eq/=. exists i'.
      rewrite lookup_partial_alter_ne by naive_solver. naive_solver.
  Qed.
  Lemma map_kmap_insert {A} (m : M1 A) i x :
    map_kmap f (<[i:=x]> m) = <[f i:=x]> (map_kmap f m).
  Proof. apply map_kmap_partial_alter. Qed.
  Lemma map_kmap_delete {A} (m : M1 A) i :
    map_kmap f (delete i m) = delete (f i) (map_kmap f m).
  Proof. apply map_kmap_partial_alter. Qed.
  Lemma map_kmap_alter {A} (g : A → A) (m : M1 A) i :
    map_kmap f (alter g i m) = alter g (f i) (map_kmap f m).
  Proof. apply map_kmap_partial_alter. Qed.

  Lemma map_kmap_imap {A B} (g : K2 → A → option B) (m : M1 A) :
    map_kmap f (map_imap (g ∘ f) m) = map_imap g (map_kmap f m).
  Proof.
    apply map_eq; intros j. apply option_eq; intros y.
    rewrite map_lookup_imap, bind_Some. setoid_rewrite lookup_map_kmap_Some.
    setoid_rewrite map_lookup_imap. setoid_rewrite bind_Some. naive_solver.
  Qed.
  Lemma map_kmap_omap {A B} (g : A → option B) (m : M1 A) :
    map_kmap f (omap g m) = omap g (map_kmap f m).
  Proof.
    apply map_eq; intros j. apply option_eq; intros y.
    rewrite lookup_omap, bind_Some. setoid_rewrite lookup_map_kmap_Some.
    setoid_rewrite lookup_omap. setoid_rewrite bind_Some. naive_solver.
  Qed.
  Lemma map_kmap_fmap {A B} (g : A → B) (m : M1 A) :
    map_kmap f (g <$> m) = g <$> (map_kmap f m).
  Proof. by rewrite !map_fmap_alt, map_kmap_omap. Qed.
End map_kmap.

Lemma lookup_insert_spec `{Countable K} {V} (A : gmap K V) i j v :
  (<[ i := v]> A) !! j = if (decide (i = j)) then Some v else (A !! j).
Proof.
  case_decide.
  - subst. apply lookup_insert.
  - by apply lookup_insert_ne.
Qed.

Lemma list_lookup_insert_spec {V} (xs : list V) i j v :
  (<[ i := v]> xs) !! j = if (decide (i = j ∧ i < length xs)) then Some v else (xs !! j).
Proof.
  case_decide.
  - destruct H. subst. apply list_lookup_insert; done.
  - destruct (decide (i < length xs)).
    + assert (i ≠ j) by naive_solver. apply list_lookup_insert_ne. done.
    + rewrite list_insert_ge; [done|lia].
Qed.

Lemma lookup_delete_spec `{Countable K} {V} (A : gmap K V) i j :
  (delete i A) !! j = if (decide (i = j)) then None else A !! j.
Proof.
  case_decide.
  - apply lookup_delete_None; eauto.
  - rewrite lookup_delete_ne; eauto.
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

Lemma lookup_app_plus {A} (l1 l2 : list A) (i : nat) :
  (l1 ++ l2) !! (length l1 + i) = l2 !! i.
  by induction l1.
  Proof.
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

Lemma lookup_insert' {A} i j (x : A) xs :
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

Lemma delete_insert' {T} (i : nat) (x : T) (xs : list T) :
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

  Lemma disjoint_insert gs g i :
    (∀ g', g' ∈ gs -> g ##ₘ g') -> disjoint gs -> disjoint (insert i g gs).
  Proof.
    destruct (decide (length gs < i)).
    { rewrite insert_out_of_bounds; eauto with lia. }
    intros HH Hdisj j1 j2 h1 h2 Hs1 Hs2 Hneq.
    rewrite lookup_insert' in Hs1; last lia.
    rewrite lookup_insert' in Hs2; last lia.
    repeat case_decide; simpl in *; simplify_eq;
    unfold disjoint in *;
    eauto using elem_of_list_lookup_2 with lia; symmetry;
    eauto using elem_of_list_lookup_2 with lia.
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

  (* Lemma disjoint_submseteq gs gs' :
    submseteq gs' gs -> disjoint gs -> disjoint gs'.
  Proof.
  Admitted. *)

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
End disjoint.
