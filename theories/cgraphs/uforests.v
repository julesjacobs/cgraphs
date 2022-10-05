From stdpp Require Import gmap.
From iris.bi Require Import bi.
From cgraphs Require Import util.

Ltac qed := done || eauto || naive_solver lia || set_solver.
Definition uforest A `{Countable A} := gset (A * A).

Section uforest.
  Context `{Countable A}.
  Context `{Inhabited A}.
  Notation G := (uforest A).
  Notation P := (list A).

  Definition path (g : G) (xs : P) :=
    ∀ i a b, xs !! i = Some a -> xs !! (i+1) = Some b -> (a,b) ∈ g.

  Definition undirected (g : G) :=
    ∀ x y, (x,y) ∈ g → (y,x) ∈ g.

  Definition no_self_loops (g : G) :=
    ∀ x, (x,x) ∉ g.

  Definition has_u_turn (xs : P) :=
    ∃ i x, xs !! i = Some x ∧ xs !! (i+2) = Some x.

  Record is_uforest (g : G) : Prop := {
    forest_undirected : undirected g;
    forest_u_turns : ∀ x xs, path g ([x] ++ xs ++ [x]) -> has_u_turn ([x] ++ xs ++ [x])
  }.

  Lemma forest_no_self_loops (g : G) :
    is_uforest g -> no_self_loops g.
  Proof.
    intros Hforest x Hx.
    destruct (forest_u_turns g Hforest x []) as (i & a & H1 & H2).
    - simpl. intros i a b.
      destruct i; simpl.
      + qed.
      + destruct i; qed.
    - simpl in *.
      destruct i; simpl in *; simplify_eq.
      destruct i; simpl in *; simplify_eq.
  Qed.

  Lemma has_u_turn_reverse (xs : P) :
    has_u_turn (reverse xs) -> has_u_turn xs.
  Proof.
    intros (i & x & Hx1 & Hx2).
    assert (i+2 < length xs).
    {
      apply lookup_lt_Some in Hx2. rewrite reverse_length in Hx2. done.
    }
    apply lookup_reverse_Some in Hx1.
    apply lookup_reverse_Some in Hx2.
    exists (length xs - S (i + 2)), x.
    split. done.
    rewrite <- Hx1. f_equiv. lia.
  Qed.

  Lemma has_u_turn_reverse' (xs : P) :
    has_u_turn xs -> has_u_turn (reverse xs).
  Proof.
    intros HH. rewrite <-(reverse_involutive xs) in HH.
    by apply has_u_turn_reverse.
  Qed.

  (* NB. connected g a a <-> False *)
  Definition connected (g : G) (a b : A) := ∃ xs, path g ([a] ++ xs ++ [b]).

  Lemma path_reverse (g : G) (xs : P) :
    undirected g -> path g xs -> path g (reverse xs).
  Proof.
    unfold path. intros Hundir Hpath i a b H1 H2.
    apply lookup_reverse_Some_iff in H1 as [].
    apply lookup_reverse_Some_iff in H2 as [].
    apply Hundir.
    eapply Hpath. done.
    rewrite <- H1. f_equiv. lia.
  Qed.

  Lemma connected_sym (g : G) (a b : A) :
    undirected g -> connected g a b -> connected g b a.
  Proof.
    unfold connected.
    intros Hundir (xs & Hxs).
    exists (reverse xs).
    simpl. rewrite <-reverse_cons, <-reverse_snoc.
    apply path_reverse; done.
  Qed.

  Lemma path_app (g : G) (a : A) (xs ys : P) :
    path g (xs ++ [a]) -> path g ([a] ++ ys) -> path g (xs ++ [a] ++ ys).
  Proof.
    intros H1 H2 i x y Hx Hy.
    rewrite !lookup_app_lr in Hx.
    rewrite !lookup_app_lr in Hy.
    simpl in *.
    repeat (case_decide; try lia); unfold path in *.
    - eapply H1; rewrite lookup_app_lr; case_decide; (done || lia).
    - eapply H1; rewrite lookup_app_lr; case_decide; (done || lia).
    - replace (i + 1 - length xs - 1) with (i - length xs) in * by lia.
      eapply (H2 0).
      + simpl. rewrite-> lookup_singleton_Some in Hx. qed.
      + simpl. apply lookup_singleton_Some in Hx as []. rewrite H7 in Hy. done.
    - replace (i + 1 - length xs - 1) with ((i - length xs - 1) + 1) in * by lia.
      eapply (H2 (S (i - length xs - 1))); done.
  Qed.

  Lemma path_edge (g : G) (a b : A) :
    (a,b) ∈ g -> path g [a;b].
  Proof.
    intros Hedge i x y Hx Hy.
    destruct i; simpl in *; simplify_eq. done.
    destruct i; simpl in *; simplify_eq.
  Qed.

  Lemma connected_trans (g : G) (a b c : A) :
    connected g a b -> connected g b c -> connected g a c.
  Proof.
    intros (xs & Hxs) (ys & Hys).
    exists (xs ++ [b] ++ ys).
    replace ([a] ++ (xs ++ [b] ++ ys) ++ [c]) with (([a] ++ xs) ++ [b] ++ (ys ++ [c])).
    - apply path_app; rewrite <-?app_assoc; done.
    - rewrite !app_assoc. done.
  Qed.

  Definition uedge (x y : A) : uforest A := {[ (x,y); (y,x) ]}.

  Lemma edge_sym x y : uedge x y = uedge y x.
  Proof. unfold uedge. set_solver. Qed.

  Lemma path_delete (g : G) (a b : A) (xs : P) :
    path (g ∖ uedge a b) xs -> path g xs.
  Proof.
    intros Hpath i x y Hx Hy.
    unfold path in *.
    specialize (Hpath i x y Hx Hy).
    rewrite-> elem_of_difference in Hpath.
    destruct Hpath. done.
  Qed.

  Lemma has_u_turn_dec (xs : P) :
    Decision (has_u_turn xs).
  Proof.
    induction xs.
    - right. intros (i & xs & H1 & H2). destruct i; simpl in *; simplify_eq.
    - destruct IHxs.
      + left. destruct h as (i & x & H1 & H2).
        exists (i+1),x.
        replace (i+1) with (S i) by lia. simpl. split;done.
      + destruct xs.
        { right. intros (i & x & H1 & H2). destruct i; simpl in *; simplify_eq. }
        destruct xs.
        { right. intros (i & x & H1 & H2). do 2 try destruct i; simpl in *; simplify_eq. }
        destruct (decide (a = a1)).
        * left. exists 0,a; simpl. subst. split;done.
        * right. intros (i & x & H1 & H2).
          destruct i; simpl in *; simplify_eq.
          apply n. exists i,x. split;done.
  Qed.

  Theorem list_length_ind {T} (P : list T -> Prop): (∀ xs, (∀ l, length l < length xs -> P l) -> P xs) -> ∀ xs, P xs.
  Proof.
    intros H'.
    assert (∀ xs l : list T, length l <= length xs -> P l) as Hind.
    { induction xs; intros l Hlen; apply H'; intros l0 H0'.
      - inversion Hlen. lia.
      - apply IHxs. simpl in Hlen. lia.
    }
    intros xs.
    eapply (Hind xs). lia.
  Qed.

  Lemma path_sub_r (g : G) (xs ys : P) :
    path g (xs ++ ys) -> path g ys.
  Proof.
    intros Hpath i x y Hx Hy.
    apply (Hpath (i + length xs)); rewrite lookup_app_r; try lia.
    - replace (i + length xs - length xs) with i by lia. done.
    - replace (i + length xs + 1 - length xs) with (i + 1) by lia. done.
  Qed.

  Lemma edge_undirected a b : undirected (uedge a b).
  Proof.
    intros x y HH.
    unfold uedge in *. set_solver.
  Qed.

  Lemma path_cons (g : G) (a b : A) (xs : P) :
    (a,b) ∈ g -> path g (b :: xs) -> path g (a :: b :: xs).
  Proof.
    intros Hedge Hpath i x y Hx Hy.
    destruct i; simpl in *; simplify_eq. done.
    eapply Hpath; done.
  Qed.

  Lemma path_remove_mid (g : G) (x : A) (i j : nat) (xs : P) :
    i <= j -> xs !! i = Some x -> xs !! j = Some x ->
    path g xs -> path g (take i xs ++ drop j xs).
  Proof.
    intros Hle Hi Hj Hpath.
    intros k a b Ha Hb.
    unfold path in *.
    rewrite lookup_app_lr in Ha.
    rewrite lookup_app_lr in Hb.
    repeat case_decide; try lia.
    - apply lookup_take_Some in Ha.
      apply lookup_take_Some in Hb.
      eauto.
    - assert (k+1 = length (take i xs)) by lia.
      clear H1 H2.
      replace (k + 1 - length (take i xs)) with 0 in Hb by lia.
      rewrite ->take_length_le in H3 by (apply lookup_lt_Some in Hi; lia).
      apply lookup_take_Some in Ha. subst.
      rewrite lookup_drop in Hb.
      replace (j + 0) with j in Hb by lia.
      assert (x = b) as -> by qed.
      eapply Hpath; eauto.
    - rewrite lookup_drop in Ha.
      rewrite lookup_drop in Hb.
      replace (j + (k + 1 - length (take i xs))) with
              (j + (k - length (take i xs)) + 1) in Hb by lia.
      eapply Hpath; eauto.
  Qed.

  Lemma connected_no_u_turn (g : G) (a b : A) (xs : P) :
    a≠b -> path g ([a] ++ xs ++ [b]) -> ∃ xs', path g ([a] ++ xs' ++ [b]) ∧ ¬ has_u_turn ([a] ++ xs' ++ [b]).
  Proof.
    intros Hneq.
    induction xs using list_length_ind.
    intros Hpath.
    destruct (has_u_turn_dec ([a] ++ xs ++ [b])); eauto.
    destruct h as (i & x & Hs1 & Hs2).
    destruct i.
    - simpl in *. simplify_eq. destruct xs. simpl in *; simplify_eq.
      simpl in *. destruct xs; simpl in *; simplify_eq.
      eapply (H1 xs). lia.
      replace (x :: a :: x :: xs ++ [b]) with ([x;a] ++ x :: xs ++ [b]) in Hpath by set_solver.
      eapply path_sub_r. done.
    - simpl in *.
      rewrite lookup_app_l in Hs1.
      2: { apply lookup_lt_Some in Hs2. rewrite app_length in Hs2. simpl in *. lia. }
      eapply (H1 (take i xs ++ drop (i+2) xs)).
      {
        rewrite app_length.
        rewrite drop_length.
        rewrite take_length_le.
        { apply lookup_lt_Some in Hs2. rewrite app_length in Hs2. simpl in *. lia. }
        apply lookup_lt_Some in Hs1. lia.
      }
      rewrite !app_comm_cons.
      rewrite <-firstn_cons.
      rewrite <-app_assoc.
      rewrite <-drop_app_le.
      2: { apply lookup_lt_Some in Hs2; rewrite app_length in Hs2; simpl in *; lia. }
      replace (take (S i) (a :: xs)) with ((take (S i) (a :: xs ++ [b]))).
      2: { rewrite-> app_comm_cons, take_app_le. done. simpl. apply lookup_lt_Some in Hs1. lia. }
      replace (drop (i + 2) (xs ++ [b])) with (drop (i + 3) (a :: xs ++ [b])).
      2: { replace (i+3) with (S (i+2)) by lia. simpl. done. }
      eapply path_remove_mid; try done; try lia.
      + simpl. rewrite lookup_app_l. done. apply lookup_lt_Some in Hs1. lia.
      + replace (i+3) with (S (i+2)) by lia. simpl. done.
  Qed.

  Lemma find_first_edge (xs : P) (a b : A) :
    (∃ i, xs !! i = Some a ∧ xs !! S i = Some b ∧
      ∀ j, j < i -> ¬ (xs !! j = Some a ∧ xs !! S j = Some b)) ∨
    (∀ i, ¬ (xs !! i = Some a ∧ xs !! S i = Some b)).
  Proof.
    induction xs.
    { right. intros i []. destruct i; simplify_eq. }
    destruct xs; simpl in *.
    { right. intros i []. destruct i; simplify_eq.  }
    destruct (decide (a0 = a ∧ a1 = b)).
    { left. exists 0. qed. }
    destruct IHxs.
    - left. destruct H1 as (i & Ha & Hb & Hlow).
      exists (S i). simpl. split. done. split. done.
      intros j Hj.
      intros []. apply n.
      destruct j; simpl in *. qed.
      specialize (Hlow j).
      assert (j < i) as Q by lia.
      specialize (Hlow Q).
      exfalso.
      apply Hlow. done.
    - right. intros i [].
      destruct i; simpl in *. qed.
      specialize (H1 i). apply H1.
      done.
  Qed.

  Definition has_edge (xs : P) a b i :=
    (xs !! i = Some a ∧ xs !! (i + 1) = Some b) ∨
    (xs !! i = Some b ∧ xs !! (i + 1) = Some a).

  Lemma has_edge_dec xs a b i : Decision (has_edge xs a b i).
  Proof. solve_decision. Qed.

  Lemma has_edge_sym xs a b i :
    has_edge xs a b i <-> has_edge xs b a i.
  Proof.
    unfold has_edge. qed.
  Qed.

  Lemma find_first_has_edge (xs : P) (a b : A) :
    (∃ i, has_edge xs a b i ∧ ∀ j, j < i -> ¬ has_edge xs a b j)
    ∨ (∀ i, ¬ has_edge xs a b i).
  Proof.
    induction xs; simpl.
    { right. intros i HH. unfold has_edge in *. destruct i; simpl in *; qed. }
    destruct xs.
    { right. intro. unfold has_edge. replace (i + 1) with (S i) by lia; simpl. destruct i; simpl; qed. }
    destruct (decide ((a0 = a ∧ a1 = b) ∨ (a0 = b ∧ a1 = a))).
    {
      left. exists 0. split; intros; try lia.
      unfold has_edge. simpl. qed.
    }
    destruct IHxs.
    {
      left. destruct H1 as (i & Hi1 & Hi2). exists (S i).
      split.
      - unfold has_edge. simpl. unfold has_edge in Hi1. qed.
      - intros. destruct j.
        + unfold has_edge. simpl. qed.
        + unfold has_edge in *. simpl.
          assert (j < i) as QQ by lia.
          specialize (Hi2 _ QQ).
          qed.
    }
    right. intro. intro. unfold has_edge in *.
    destruct i; simpl in *; qed.
  Qed.

  Lemma has_edge_reverse xs a b i :
    has_edge (reverse xs) a b i -> has_edge xs a b (length xs - (i + 2)).
  Proof.
    unfold has_edge. intros [[]|[]];
    assert (i+1 < length xs) by (apply lookup_lt_Some in H2; rewrite reverse_length in H2; lia);
    apply lookup_reverse_Some in H1;
    apply lookup_reverse_Some in H2;
    rewrite <- H1; rewrite <- H2; [right | left]; split; f_equiv; lia.
  Qed.

  Lemma path_has_edge g a b xs :
    path (g ∪ uedge a b) xs -> (∀ i, ¬ has_edge xs a b i) ->
    path g xs.
  Proof.
    intros Hpath Hne i x y Hx Hy.
    specialize (Hpath i x y Hx Hy).
    apply elem_of_union in Hpath as []; first done.
    specialize (Hne i). contradict Hne.
    unfold has_edge. unfold uedge in H1.
    set_solver.
  Qed.

  Lemma path_take g i xs :
    path g xs -> path g (take i xs).
  Proof.
    intros Hpath j a b Ha Hb.
    apply lookup_take_Some in Ha.
    apply lookup_take_Some in Hb.
    eapply Hpath; done.
  Qed.

  Lemma path_drop g i xs :
    path g xs -> path g (drop i xs).
  Proof.
    intros Hpath j a b Ha Hb.
    rewrite lookup_drop in Ha.
    rewrite lookup_drop in Hb.
    rewrite Nat.add_assoc in Hb.
    eapply Hpath; done.
  Qed.

  Lemma has_edge_take a b j i xs :
    has_edge xs a b i ∧ i+1 < j <-> has_edge (take j xs) a b i.
  Proof.
    split.
    - intros [].
      destruct H1 as [[]|[]]; [left | right]; split;
      rewrite lookup_take; (done || lia).
    - intros [[]|[]];
      apply lookup_take_Some_iff in H1;
      apply lookup_take_Some_iff in H2; split; try lia; [left | right]; qed.
  Qed.

  Lemma has_edge_drop a b j i xs :
    has_edge xs a b i ∧ i >= j -> has_edge (drop j xs) a b (i - j).
  Proof.
    intros [].
    destruct H1 as [[]|[]]; [left | right]; split;
    rewrite lookup_drop; rewrite <-?H1, <-?H3; f_equiv; lia.
  Qed.

  Lemma connected_alt g a b :
    a≠b ->
      connected g a b <->
      ∃ xs, path g xs ∧ xs !! 0 = Some a ∧ last xs = Some b.
  Proof.
    intros Hneq.
    split.
    + intros [xs Hxs]. exists ([a] ++ xs ++ [b]).
      split; first done.
      split; first done.
      rewrite app_assoc.
      by rewrite last_snoc.
    + intros (xs & Hpath & Hxs1 & Hxs2).
      assert (length xs > 1).
      { destruct xs; simplify_eq. destruct xs; simpl in *; simplify_eq. lia.  }
      apply split_last in Hxs2.
      rewrite Hxs2 in Hxs1.
      apply split_first in Hxs1.
      rewrite drop_app_le in Hxs1.
      exists (drop 1 (take (length xs - 1) xs)).
      by rewrite <-Hxs1, <-Hxs2.
      destruct xs; simpl in *. simplify_eq.
      destruct xs; simpl in *; try lia.
  Qed.

  (* Hiding this in a definition is necessary because otherwise the wlog tactic
     will generalize over the Lookup instance.
     This way the wlog tactic can not peek inside the proposition and won't find any
     Lookup instance as a subterm. *)
  Definition bar (xs : P) x i1 a b :=
    ([x] ++ xs ++ [x]) !! i1 = Some a ∧ ([x] ++ xs ++ [x]) !! (i1 + 1) = Some b.

  Definition connected0 g a b := (a = b) ∨ connected g a b.

  Lemma path_singleton g b : path g [b].
  Proof.
    intros i x y Hx Hy. destruct i; simplify_eq.
  Qed.

  Lemma connected0_alt g a b :
    connected0 g a b <->
    ∃ xs, path g xs ∧ xs !! 0 = Some a ∧ last xs = Some b.
  Proof.
    destruct (decide (a = b)).
    - unfold connected0. split; eauto. intros _. subst.
      exists [b]. eauto using path_singleton.
    - unfold connected0. rewrite connected_alt; qed.
  Qed.

  Lemma last_cons {T} (x : T) xs z :
    last xs = Some z ->
    last (x :: xs) = Some z.
  Proof.
    induction xs; simpl; intros; simplify_eq. done.
  Qed.

  Lemma connected0_sym g a b :
    undirected g -> connected0 g a b -> connected0 g b a.
  Proof.
    unfold connected0.
    intros Hundir []; eauto. right.
    apply connected_sym; eauto.
  Qed.

  Lemma connected0_trans g a b c :
    connected0 g a b -> connected0 g b c -> connected0 g a c.
  Proof.
    intros []; subst; first done.
    intros []; subst.
    { unfold connected0. eauto. }
    right. eapply connected_trans; done.
  Qed.

  Lemma split_both (xs : P) a :
    length xs > 1 -> xs !! 0 = Some a -> last xs = Some a ->
    xs = [a] ++ drop 1 (take (length xs - 1) xs) ++ [a].
  Proof.
    intros Hlen H1 H2.
    apply split_last in H2.
    rewrite H2 in H1.
    apply split_first in H1.
    rewrite drop_app_le in H1; first by rewrite <-H1.
    rewrite take_length. lia.
  Qed.

  Lemma has_u_turn_alt (g : G) xs x :
    is_uforest g -> path g xs -> length xs > 1 ->
    xs !! 0 = Some x -> last xs = Some x ->
    has_u_turn xs.
  Proof.
    intros Hforest Hpath Hlen H1 H2.
    pose proof (split_both xs x Hlen H1 H2).
    rewrite H3. rewrite H3 in Hpath.
    destruct Hforest; eauto.
  Qed.

  Lemma has_u_turn_drop xs i :
    has_u_turn (drop i xs) -> has_u_turn xs.
  Proof.
    intros [j [x HH]].
    rewrite !lookup_drop in HH.
    rewrite Nat.add_assoc in HH.
    unfold has_u_turn. eauto.
  Qed.

  Lemma has_u_turn_take xs i :
    has_u_turn (take i xs) -> has_u_turn xs.
  Proof.
    intros [j [x []]].
    apply lookup_take_Some in H1.
    apply lookup_take_Some in H2.
    unfold has_u_turn; eauto.
  Qed.

  Lemma has_u_turn_mid (g : G) xs i1 i2 x :
    is_uforest g -> path g (drop i1 (take (S i2) xs)) -> i1 < i2 ->
    xs !! i1 = Some x -> xs !! i2 = Some x ->
    has_u_turn xs.
  Proof.
    intros Hforest Hpath Hneq H1 H2.
    eapply has_u_turn_take.
    eapply has_u_turn_drop.
    eapply (has_u_turn_alt g (drop i1 (take (S i2) xs))); eauto.
    - rewrite drop_length. rewrite take_length. apply lookup_lt_Some in H2. apply lookup_lt_Some in H1. lia.
    - rewrite lookup_drop. apply lookup_take_Some_iff. split; last lia.
      rewrite<-H1. f_equiv. lia.
    - rewrite<-H2. rewrite last_drop. eapply last_take.
      + by apply lookup_lt_Some in H2.
      + rewrite take_length. apply lookup_lt_Some in H2. apply lookup_lt_Some in H1. lia.
  Qed.

  Lemma forest_connect (g : G) (a b : A) :
    is_uforest g -> ¬ connected0 g a b -> is_uforest (g ∪ uedge a b).
  Proof.
    intros [] Hnconn.
    constructor.
    { intros x y HH.
      apply elem_of_union.
      apply elem_of_union in HH as [].
      + left. apply forest_undirected0. done.
      + right. apply edge_undirected. done. }
    intros x xs Hpath.
    destruct (find_first_has_edge ([x] ++ xs ++ [x]) a b) as [(i1 & Hi1v & Hi1r)|H1].
    {
      (* Use wlog (a,b) here *)
      unfold has_edge in Hi1v.
      wlog: a b Hpath Hi1v Hi1r Hnconn / bar xs x i1 a b; unfold bar.
      {
        intros Hwlog.
        destruct Hi1v.
        { apply (Hwlog a b); eauto. }
        apply (Hwlog b a); eauto.
        - rewrite edge_sym. done.
        - intro. rewrite has_edge_sym. eauto.
        - contradict Hnconn. apply connected0_sym; eauto.
      }
      clear Hi1v. intros [Hi1vA Hi1vB].
      (* Now we are in the situation x .. a b ... x *)
      assert (path g (take (i1+1) ([x] ++ xs ++ [x]))) as Hpath1.
      {
        apply (path_has_edge g a b).
        - apply path_take. done.
        - intros j He.
          apply has_edge_take in He as [He Hle].
          assert (j < i1) by lia.
          eapply Hi1r; done.
      }
      destruct (find_first_has_edge (drop (i1 + 1) ([x] ++ xs ++ [x])) a b).
      {
        (* Now we are in the situation x ... a b ... (ab|ba) ... x *)
        destruct H1 as (i2 & He & Hne).
        assert (path g (take (i2+1) $ drop (i1+1) ([x] ++ xs ++ [x]))) as Hpath2.
        {
          apply (path_has_edge g a b).
          - apply path_take. apply path_drop. done.
          - intros j He'.
            rewrite <-has_edge_take in He'.
            destruct He' as [He' Hne'].
            assert (j < i2) by lia.
            eapply Hne; done.
        }
        assert (take (i2 + 1) (drop (i1 + 1) ([x] ++ xs ++ [x])) !! 0 = Some b) as Hsb.
        {
          rewrite lookup_take; last lia. rewrite lookup_drop.
          rewrite Nat.add_0_r. done.
        }
        destruct He as [He|He].
        {
          (* Now we are in the situation x ... a b ... a b ... x *)
          exfalso. apply Hnconn. apply connected0_sym; first done.
          apply connected0_alt.
          eexists.
          split; first done. split; first done.
          replace (i2+1) with (S i2) by lia.
          apply last_take_Some. destruct He. done.
        }
        {
          (* Now we are in the situation x ... a b ... b a ... x *)
          assert (last (take (i2 + 1) (drop (i1 + 1) ([x] ++ xs ++ [x]))) = Some b) as Hsb'.
          {
            replace (i2 + 1) with (S i2) by lia.
            destruct He.
            rewrite last_take; first done.
            apply lookup_lt_Some in H1. done.
          }
          destruct He.
          destruct (decide (i2 = 0)).
          {
            subst. simpl in *.
            rewrite lookup_drop in H1.
            apply lookup_take_Some in Hsb. rewrite lookup_drop in Hsb.
            rewrite lookup_drop in H2.
            exists i1, a.
            split; eauto.
            rewrite<-H2. f_equiv. lia.
          }
          rewrite take_drop_commute in Hpath2.
          replace (i1 + 1 + (i2 + 1)) with (S (i1 + (i2 + 1))) in Hpath2 by lia.
          eapply has_u_turn_mid.
          + constructor; eauto.
          + exact Hpath2.
          + lia.
          + apply lookup_take_Some in Hsb. rewrite lookup_drop in Hsb. replace (i1 + 1 + 0) with (i1 + 1) in Hsb by lia.
            done.
          + rewrite lookup_drop in H1. rewrite <- H1. f_equiv. lia.
        }
      }
      {
        (* Now we are in the situation x ... a b ... x *)
        assert (path g (drop (i1+1) ([x] ++ xs ++ [x]))) as Hpath2.
        {
          apply (path_has_edge g a b).
          - apply path_drop. done.
          - intros j He'. eapply H1. done.
        }
        contradict Hnconn.
        apply connected0_sym; first done.
        apply (connected0_trans g b x a).
        - apply connected0_alt. eexists.
          split; first exact Hpath2.
          split.
          + rewrite lookup_drop. rewrite <- Hi1vB. f_equiv. lia.
          + rewrite last_drop.
            * rewrite app_assoc. rewrite last_snoc. done.
            * apply lookup_lt_Some in Hi1vB. done.
        - apply connected0_alt. eexists.
          split; first exact Hpath1; replace (i1 + 1) with (S i1) by lia.
          split; first done.
          rewrite last_take; first done.
          apply lookup_lt_Some in Hi1vA. done.
      }
    }
    (* No (a,b)|(b,a) *)
    apply forest_u_turns0. revert H1 Hpath.
    generalize ([x] ++ xs ++ [x]). intros.
    intros i q r Hq Hr.
    specialize (Hpath i q r).
    rewrite-> elem_of_union in Hpath.
    destruct Hpath; eauto.
    specialize (H1 i). exfalso. apply H1.
    unfold has_edge.
    assert ((q = a ∧ r = b) ∨ (q = b ∧ r = a)) as [[]|[]] by (unfold uedge in *; set_solver);
    subst; eauto.
  Qed.

  Lemma forest_disconnect (g : G) (a b : A) :
    is_uforest g -> (a,b) ∈ g -> ¬ connected0 (g ∖ uedge a b) a b.
  Proof.
    intros [] Hedge [|Hconn].
    { subst. eapply forest_no_self_loops; try constructor; eauto. }
    destruct Hconn as (xs & Hpath).
    apply connected_no_u_turn in Hpath.
    - destruct Hpath as (xs' & Hpath' & Hnut).
      pose proof (forest_u_turns0 b ([a] ++ xs')).
      destruct H1.
      {
        simpl. apply path_cons. apply forest_undirected; done. eapply path_delete. done.
      }
      destruct H1. destruct H1.
      destruct x; simpl in *.
      assert (x0 = b) as -> by qed. simplify_eq.
      + destruct xs'; simpl in *; simplify_eq.
        * specialize (Hpath' 0 a b); simpl in *. unfold uedge in *. set_solver.
        * specialize (Hpath' 0 a b); simpl in *. unfold uedge in *. set_solver.
      + apply Hnut. exists x,x0. split; eauto.
    - intro. subst. pose proof (forest_no_self_loops g).
      cut ((b,b) ∉ g). { intro Q. apply Q. done. }
      apply H1. constructor; done.
  Qed.

  Lemma forest_delete (g : G) (a b : A) :
    is_uforest g -> is_uforest (g ∖ uedge a b).
  Proof.
    intros [].
    constructor.
    - intros x y Hxy.
      rewrite-> elem_of_difference in *.
      destruct Hxy.
      apply forest_undirected0 in H1.
      split; [done|].
      unfold uedge in *. set_solver.
    - intros x xs Hpath.
      eauto using path_delete.
  Qed.

  Lemma forest_empty : is_uforest ∅.
  Proof.
    constructor.
    - intros ???.
      eauto using not_elem_of_empty.
    - intros x xs Hpath.
      exfalso.
      specialize (Hpath 0 x).
      destruct xs.
      + simpl in *.
        specialize (Hpath x).
        apply not_elem_of_empty in Hpath; done.
      + simpl in *.
        specialize (Hpath a).
        apply not_elem_of_empty in Hpath; done.
  Qed.

  Definition lone (x : A) (g : uforest A) :=
    ∀ y, (x,y) ∉ g.

  Lemma forest_extend (x y : A) (g : uforest A) :
    x ≠ y → lone y g →
    is_uforest g → is_uforest (g ∪ uedge x y).
  Proof.
    intros Hneq Hlone [].
    apply forest_connect; [done..|].
    intros [->|[]]; eauto.
    unfold path in *. unfold lone in *.
    destruct (([x] ++ x0 ++ [y]) !! length x0) eqn:E.
    2: {
      apply lookup_ge_None_1 in E. simpl in *.
      rewrite app_length in E. lia.
    }
    eapply Hlone.
    apply forest_undirected0.
    eapply (H1 (length x0)); [done|].
    replace (length x0 + 1) with (length ([x] ++ x0) + 0); simpl; [|lia].
    rewrite lookup_app_plus. done.
  Qed.

  Lemma connected_edge (g : G) (x y : A) :
    (x,y) ∈ g -> connected0 g x y.
  Proof.
    intros Hxy. right.
    exists []. simpl.
    intros i a b Ha Hb.
    destruct i; simpl in *. simplify_eq. done.
    destruct i; simpl in *. simplify_eq.
    rewrite lookup_nil in Ha. simplify_eq.
  Qed.

  Lemma forest_modify (x y z : A) (g : uforest A) :
    x ≠ z -> y ≠ z ->
    is_uforest g -> (x,y) ∈ g -> (x,z) ∈ g ->
    is_uforest ((g ∖ uedge x z) ∪ uedge y z).
  Proof.
    intros Hxnz Hynz Hforest Hxy Hxz.
    apply forest_connect; try done.
    - by apply forest_delete.
    - pose proof (forest_disconnect g x z Hforest Hxz) as Hconn.
      intro Hconn'.
      eapply connected0_trans in Hconn'.
      apply Hconn. exact Hconn'.
      apply connected_edge.
      unfold uedge. set_solver.
  Qed.

  Definition uvertices (g : G) : gset A :=
    set_map fst g ∪ set_map snd g.

  Definition no_u_turns (f : A -> option A) : Prop :=
      ∀ a b c, f a = Some b -> f b = Some c -> a ≠ c.

  Fixpoint search_iter
    (g : uforest A) (f : A -> option A) (a : A) (n : nat) : A :=
    match n with
    | 0 => a
    | S n => match f a with
             | None => a
             | Some a' => search_iter g f a' n
             end
    end.

  Definition search (g : uforest A) (x : A) (f : A -> option A) : A :=
    search_iter g f x (size (uvertices g)).

  Fixpoint search_iter_list
    (g : uforest A) (f : A -> option A) (a : A) (n : nat) : list A :=
    match n with
    | 0 => []
    | S n => match f a with
             | None => []
             | Some a' => a' :: search_iter_list g f a' n
             end
    end.

  Definition valid (g : uforest A) (f : A -> option A) :=
    ∀ x y, x ∈ uvertices g -> f x = Some y -> (x,y) ∈ g.

  Definition fpath (g : G) (f : A -> option A) (xs : P) :=
    ∀ i a b, xs !! i = Some a -> xs !! (i+1) = Some b -> f a = Some b.

  Lemma fpath_sub (g : G) (f : A -> option A) (xs ys : P) :
    fpath g f (xs ++ ys) -> fpath g f xs.
  Proof.
    intros Hpath i a b Ha Hb.
    eapply Hpath.
    - rewrite lookup_app_l. done.
      eapply lookup_lt_Some; done.
    - rewrite lookup_app_l. done.
      eapply lookup_lt_Some; done.
  Qed.

  Lemma edge_in_uvertices (g : G) (x y : A) :
    (x,y) ∈ g -> y ∈ uvertices g.
  Proof.
    intro. unfold uvertices.
    apply elem_of_union_r.
    apply elem_of_map.
    exists (x,y). simpl. eauto.
  Qed.

  Lemma fpath_uvertices (g : G) (f : A -> option A) (x : A) (xs : P) :
    valid g f -> x ∈ uvertices g -> fpath g f (x::xs) -> ∀ a, a ∈ (x::xs) -> a ∈ uvertices g.
  Proof.
    rewrite <- (reverse_involutive xs).
    generalize (reverse xs). clear xs.
    intros xs Hvalid Hvert Hfpath.
    induction xs as [|y xs IHxs]; simpl; intros a Hin.
    { apply elem_of_cons in Hin as []; qed. }
    rewrite reverse_cons in Hin.
    rewrite reverse_cons in Hfpath.
    rewrite-> app_comm_cons in *.
    apply elem_of_app in Hin as [].
    - apply IHxs; eauto.
      eapply fpath_sub; done.
    - assert (a = y) as <- by set_solver. clear H1.
      unfold valid in *.
      destruct xs; simpl in *.
      + eapply edge_in_uvertices. eapply Hvalid.
        done.
        eapply (Hfpath 0). done. done.
      + eapply edge_in_uvertices. eapply Hvalid.
        eapply IHxs.
        * eapply fpath_sub. done.
        * rewrite reverse_cons. rewrite app_comm_cons.
          apply elem_of_app. right. assert (∀ (x:A), x ∈ [x]) by set_solver.
          apply H1.
        * eapply (Hfpath (length (x :: reverse xs))).
          -- rewrite reverse_cons. rewrite app_comm_cons.
             rewrite lookup_app_l. rewrite app_comm_cons.
             replace (length (x :: reverse xs)) with (length (x :: reverse xs) + 0) by lia.
             rewrite lookup_app_plus. done.
             rewrite app_comm_cons.
             rewrite app_length. simpl. lia.
          -- rewrite app_comm_cons.
             rewrite lookup_app_r.
             simpl.
             rewrite reverse_cons. rewrite app_length. simpl.
             replace (length (reverse xs) + 1 - (length (reverse xs) + 1)) with 0 by lia. done.
             rewrite reverse_cons. rewrite app_comm_cons. rewrite app_length. simpl.
             lia.
  Qed.

  Lemma fpath_path (g : G) (f : A -> option A) (x : A) (xs : P) :
    x ∈ uvertices g -> valid g f -> fpath g f (x::xs) -> path g (x::xs).
  Proof.
    intros Hvert Hvalid Hfpath i a b Ha Hb.
    apply Hvalid.
    - eapply fpath_uvertices; try done. eapply elem_of_list_lookup_2;done.
    - unfold fpath in *. eapply Hfpath; done.
  Qed.

  Lemma fpath_drop (g : G) (f : A -> option A) (xs : P) (k : nat) :
    fpath g f xs -> fpath g f (drop k xs).
  Proof.
    intros Hfpath i a b Ha Hb.
    rewrite-> (lookup_drop xs) in Ha.
    rewrite-> (lookup_drop xs) in Hb.
    eapply Hfpath.
    exact Ha.
    rewrite <-Nat.add_assoc. done.
  Qed.

  Lemma fpath_take (g : G) (f : A -> option A) (xs : P) (k : nat) :
    fpath g f xs -> fpath g f (take k xs).
  Proof.
    intros Hfpath i a b Ha Hb.
    apply lookup_take_Some in Ha.
    apply lookup_take_Some in Hb.
    eapply Hfpath; eauto.
  Qed.

  Lemma fpaths_no_u_turns f g xs :
    no_u_turns f -> fpath g f xs -> ¬ has_u_turn xs.
  Proof.
    intros Hnut Hpath Hut.
    destruct Hut as (i & x & H1 & H2).
    unfold fpath in *.
    destruct (xs !! (i+1)) eqn:E.
    - pose proof (Hpath _ _ _ H1 E).
      replace (i+2) with (i+1+1) in H2.
      pose proof (Hpath _ _ _ E H2).
      eapply Hnut; eauto. lia.
    - apply lookup_ge_None_1 in E.
      apply lookup_lt_Some in H2. lia.
  Qed.

  Lemma forest_no_floops (g : G) (f : A -> option A) (x y : A) (xs : P) i j :
    valid g f -> no_u_turns f -> is_uforest g -> x ∈ uvertices g ->
    xs !! 0 = Some x -> i < j -> xs !! i = Some y -> xs !! j = Some y ->
    fpath g f xs -> False.
  Proof.
    intros Hvalid Hnut Hforest Hvert Hstart Hle H1 H2 Hfpath.
    assert (path g xs).
    { destruct xs; simpl in *; simplify_eq. apply fpath_path in Hfpath; try done. }
    assert (has_u_turn xs).
    {
      eapply has_u_turn_mid; eauto. apply path_drop. apply path_take. done.
    }
    eapply fpaths_no_u_turns; eauto.
  Qed.

  Lemma forest_no_floops' (g : G) (f : A -> option A) (x : A) (xs : P) :
    valid g f -> no_u_turns f -> is_uforest g -> x ∈ uvertices g -> fpath g f ([x] ++ xs ++ [x]) -> False.
  Proof.
    intros Hvalid Hnut [] Hvert Hfpath.
    apply fpath_path in Hfpath as Hpath; try done.
    edestruct forest_u_turns0. exact Hpath.
    destruct H1 as (y & Hy1 & Hy2).
    unfold fpath in Hfpath.
    destruct (([x] ++ xs ++ [x]) !! (x0 + 1)) eqn:Hymid.
    2: {
      apply lookup_ge_None_1 in Hymid.
      apply lookup_lt_Some in Hy2.
      lia.
    }
    specialize (Hfpath x0 y a Hy1 Hymid) as Q1.
    specialize (Hfpath (x0 + 1) a y Hymid) as Q2. replace (x0 + 1 + 1)  with (x0 + 2)  in Q2 by lia.
    specialize (Q2 Hy2).
    unfold no_u_turns in *.
    eapply Hnut; eauto.
  Qed.

  Lemma search_lemma (g : uforest A) (x : A) (f : A -> option A) :
    is_uforest g -> no_u_turns f -> valid g f ->
    x ∈ uvertices g -> f (search g x f) = None.
  Proof.
    intros Hforest Huturn Hvalid Hx.
    (* Suppose f (search g x f) = Some y *)
    destruct (f (search g x f)) eqn:Hss;[|done].
    exfalso.
    (* Have a long f-path in g *)
    assert (∃ xs, fpath g f (x::xs) ∧ size (uvertices g) < length (x::xs)).
    {
      unfold search in Hss.
      exists (search_iter_list g f x (size (uvertices g))).
      revert x Hss Hx.
      induction (size (uvertices g)); simpl in *; intros.
      - split;last lia. unfold fpath. intros. destruct i; simpl in *; simplify_eq.
      - destruct (f x) eqn:E; simpl in *; simplify_eq.
        specialize (IHn _ Hss). destruct IHn. unfold valid in *.
        eapply edge_in_uvertices. eapply Hvalid; eauto.
        split; last lia.
        unfold fpath in *.
        intros. destruct i; simpl in *; simplify_eq; eauto.
    }
    destruct H1 as (xs & Hpath & Hsize).
    (* Since the path is longer than the number of uvertices, there must be a duplicate vertex in the path *)
    edestruct (pigeon (uvertices g) (x::xs)) as (i & j & y & Hi & Hj & Hneq); eauto.
    {
      intros. apply elem_of_list_lookup_2 in H1. eapply fpath_uvertices; eauto.
    }
    wlog: i j Hi Hj Hneq / i < j.
    {
      intros. destruct (decide (i < j)); eauto.
      assert (j < i) by lia.
      eauto.
    }
    intros Hlt. clear Hneq.
    (* Duplicate vertex gives a u-turn -> contradiction *)
    eapply forest_no_floops; eauto; done.
  Qed.

  Lemma search_in_uvertices (g : uforest A) (x : A) (f: A -> option A) :
    is_uforest g -> valid g f -> x ∈ uvertices g -> search g x f ∈ uvertices g.
  Proof.
    unfold search.
    revert x.
    induction (size _); simpl; eauto. intros.
    destruct (f x) eqn:E; eauto. apply IHn; eauto.
    unfold valid in *.
    eapply edge_in_uvertices; eauto.
  Qed.

  Lemma search_exists (g : uforest A) (x : A) (f : A -> option A) :
    is_uforest g -> no_u_turns f -> valid g f ->
    x ∈ uvertices g -> ∃ y, f y = None ∧ y ∈ uvertices g.
  Proof.
    intros. exists (search g x f).
    split.
    + apply search_lemma; eauto.
    + apply search_in_uvertices; eauto.
  Qed.

  Lemma path_uvertices g xs :
    is_uforest g -> 2 ≤ length xs -> path g xs -> ∀ x, x ∈ xs -> x ∈ uvertices g.
  Proof.
    intros Hforest. intros.
    unfold path in *.
    apply elem_of_list_lookup in H3 as (? & ?).
    destruct x0.
    - destruct (xs !! 1) eqn:E.
      + specialize (H2 _ _ _ H3 E).
        eapply edge_in_uvertices.
        eapply forest_undirected; eauto.
      + eapply lookup_ge_None in E. lia.
    - destruct (xs !! x0) eqn:E.
      + eapply edge_in_uvertices. eapply H2; eauto. rewrite <- H3.
        f_equiv. lia.
      + eapply lookup_lt_Some in H3.
        eapply lookup_ge_None in E.
        lia.
  Qed.

  Lemma lookup_take_spec (xs : list A) k n :
    take n xs !! k = if decide (k < n) then xs !! k else None.
  Proof.
    case_decide.
    - rewrite lookup_take; eauto.
    - rewrite lookup_take_ge; eauto. lia.
  Qed.

  Lemma lookup_length_unfold (xs : list A) k :
    xs !! k = if decide (k < length xs) then xs !! k else None.
  Proof.
    case_decide; eauto.
    eapply lookup_ge_None_2. lia.
  Qed.

  Lemma lookup_list_singleton_spec k (x : A) :
    [x] !! k = if decide (k = 0) then Some x else None.
  Proof.
    case_decide; subst; eauto. destruct k; simpl; eauto. lia.
  Qed.

  Lemma long_paths_have_u_turns g xs :
    is_uforest g -> size (uvertices g)+10 < length xs -> path g xs -> has_u_turn xs.
  Proof.
    intros Hforest Hsize Hpath.
    edestruct (pigeon (uvertices g) xs) as (i & j & y & Hi & Hj & Hneq); eauto.
    { intros. eapply path_uvertices; eauto using elem_of_list_lookup_2. lia. }
    { lia. }
    wlog: i j Hi Hj Hneq / i < j.
    {
      intros. destruct (decide (i < j)); eauto.
      assert (j < i) by lia.
      eauto.
    }
    intros Hlt.
    assert (path g (drop i (take (S j) xs))) as Hsubpath
      by eauto using path_take, path_drop.
    eapply has_u_turn_mid; eauto.
  Qed.

  Definition asym (R : A -> A -> Prop) :=
    ∀ x y, R x y -> R y x -> x = y.
  Definition Rpath (R : A -> A -> Prop) (xs : list A) : Prop :=
    ∀ i x y, xs !! i = Some x -> xs !! (i + 1) = Some y -> R y x.
  Definition Rvalid (R : A -> A -> Prop) (g : uforest A) : Prop :=
    ∀ x y, R x y -> (y,x) ∈ g.

  Lemma Rpath_path g (R : A -> A -> Prop) (xs : list A) :
    Rpath R xs -> Rvalid R g -> path g xs.
  Proof.
    intros H1 H2 i a b Ha Hb.
    eapply H2.
    eapply H1; eauto.
  Qed.

  Lemma Rpath_no_u_turns R xs g :
    is_uforest g -> Rvalid R g -> Rpath R xs -> asym R -> ¬ has_u_turn xs.
  Proof.
    intros Hforest Hvalid H1 H2 (i & x & Q1 & Q2).
    destruct (xs !! (i + 1)) eqn:E; last first.
    { eapply lookup_ge_None in E.
      eapply lookup_lt_Some in Q2. lia. }
    assert (x = a).
    {
      eapply H2.
      - eapply H1. exact E.
        replace (i + 1 + 1) with (i + 2) by lia. done.
      - eapply H1; last done. done.
    }
    subst.
    eapply forest_no_self_loops; first done.
    eapply Hvalid.
    eapply H1. exact Q1. done.
  Qed.

  Lemma lookup_length_app (xs : list A) (ys : list A) n :
    (xs ++ ys) !! (length xs + n) = ys !! n.
  Proof.
    rewrite lookup_app.
    destruct (xs !! (length xs + n)) eqn:E.
    apply lookup_lt_Some in E; first lia.
    f_equiv. lia.
  Qed.

  Lemma Rpath_snoc xs x y R :
    Rpath R (xs ++ [x]) -> R y x -> Rpath R ((xs ++ [x]) ++ [y]).
  Proof.
    intros.
    unfold Rpath in *.
    intros.
    destruct (decide (i + 1 < length (xs ++ [x]))).
    - eapply (H1 i).
      + rewrite lookup_app in H3.
        rewrite <-H3.
        destruct ((xs ++ [x]) !! i) eqn:E; eauto.
        destruct (i - length (xs ++ [x])) eqn:F; simpl in *; simplify_eq.
        eapply lookup_ge_None in E.
        assert (length (xs ++ [x]) = i) by lia.
        subst.
        rewrite lookup_length_app in H4. simpl in *. simplify_eq.
      + rewrite lookup_app in H4.
        rewrite <-H4.
        destruct ((xs ++ [x]) !! (i + 1)) eqn:E; eauto.
        destruct (i + 1 - length (xs ++ [x])) eqn:F; simpl in *; simplify_eq.
        eapply lookup_ge_None in E. lia.
    - assert (i + 1 = length (xs ++ [x])).
      { eapply lookup_lt_Some in H4. rewrite app_length in H4. simpl in *. lia. }
      rewrite H5 in H4.
      replace (length (xs ++ [x])) with (length (xs ++ [x]) + 0) in H4 by lia.
      rewrite lookup_length_app in H4. simpl in H4. simplify_eq.
      rewrite lookup_app in H3.
      rewrite lookup_app in H3.
      destruct (xs !! i) eqn:E.
      { eapply lookup_lt_Some in E.
        rewrite app_length in H5. simpl in *. lia. }
      destruct (i - length xs) eqn:F.
      + simpl in *. simplify_eq. done.
      + simpl in *. destruct ((i - length (xs ++ [x]))) eqn:G;
        simpl in *; simplify_eq.
        rewrite app_length in G. simpl in *.
        rewrite app_length in n.
        rewrite app_length in H5.
        simpl in *. lia.
  Qed.

  Definition ureachable (R : A -> A -> Prop) g n x :=
    ∃ xs, Rpath R (xs ++ [x]) ∧
      length (xs ++ [x]) + n > size (uvertices g) + 10.

  Lemma rel_wf_helper (R : A -> A -> Prop) (g : uforest A) n :
    is_uforest g -> asym R -> Rvalid R g ->
    ∀ x, ureachable R g n x -> Acc R x.
  Proof.
    intros Hforest Hasym Hvalid.
    induction n.
    - intros x (xs & HRpath & Hlen).
      exfalso. eapply Rpath_no_u_turns; eauto.
      eapply long_paths_have_u_turns; eauto. lia.
      eapply Rpath_path; eauto.
    - intros x (xs & HRpath & Hlen).
      constructor. intros. eapply IHn.
      exists (xs ++ [x]). split.
      + eapply Rpath_snoc; eauto.
      + simpl. rewrite app_length; simpl. lia.
  Qed.

  Lemma ureachable_0 R g a :
    ureachable R g (size (uvertices g) + 10) a.
  Proof.
    unfold ureachable.
    exists [].
    split.
    - unfold Rpath. intros. simpl in *.
      destruct i; simpl in *; simplify_eq.
    - simpl in *. lia.
  Qed.

  Lemma rel_wf (R : A -> A -> Prop) (g : uforest A) :
    asym R ->
    Rvalid R g ->
    is_uforest g -> wf R.
  Proof.
    intros. unfold wf. intro.
    eapply rel_wf_helper; eauto using ureachable_0.
  Qed.

  Lemma uforest_ind (R : A -> A -> Prop) (g : uforest A) (P : A -> Prop) :
    is_uforest g ->
    asym R ->
    (∀ x, (∀ y, R x y -> (x,y) ∈ g -> P y) -> P x) -> (∀ x, P x).
  Proof.
    intros Hforest Hasym Hind.
    set T := λ x y, R y x ∧ (y,x) ∈ g.
    assert (asym T).
    { intros x y [] []. eapply Hasym; eauto. }
    assert (Rvalid T g).
    { intros x y []. done. }
    pose proof (rel_wf T g H1 H2 Hforest).
    intros x. specialize (H3 x).
    induction H3. eapply Hind.
    intros. eapply H4. split; eauto.
  Qed.

End uforest.

Lemma rtc_list {T} (R : T -> T -> Prop) a b :
  rtc R a b <-> ∃ xs, xs !! 0 = Some a ∧ last xs = Some b ∧
                  ∀ i x y, xs !! i = Some x -> xs !! (i+1) = Some y -> R x y.
Proof.
  split.
  - induction 1.
    + exists [x]; simpl.
      split_and!; eauto.
      intros. destruct i; simpl in *; simplify_eq.
    + destruct IHrtc as (xs & Hxs & Qf & Ql).
      exists (x :: xs).
      split_and!; eauto.
      * destruct xs; eauto using path_singleton.
        simpl in *. simplify_eq.
      * intros. destruct i; simpl in *; simplify_eq; eauto.
  - intros (xs & Qf & Ql & Qxs).
    destruct xs; simpl in *; simplify_eq. revert a Qxs Ql.
    induction xs; intros; simplify_eq/=; try reflexivity.
    eapply rtc_transitive.
    + eapply rtc_once. eapply (Qxs 0); simpl; eauto.
    + eapply IHxs; eauto.
      intros. eapply (Qxs (S i)); simpl; eauto.
Qed.

Lemma connected0_elem_of `{Countable A} (f : uforest A) v1 v2 :
  is_uforest f ->
  connected0 f v1 v2 <-> rtsc (λ x y, (x,y) ∈ f) v1 v2.
Proof.
  intros.
  rewrite connected0_alt.
  split.
  - unfold rtsc. rewrite rtc_list. intros (xs & Hpath & Qf & Ql).
    exists xs. split_and!; eauto.
    intros. left. eapply Hpath; eauto.
  - unfold rtsc. rewrite rtc_list.
    intros (xs & Qf & Ql & Hpath).
    exists xs. split_and!; eauto.
    intros ?????.
    edestruct Hpath; first exact H1; eauto.
    eapply forest_undirected; eauto.
Qed.