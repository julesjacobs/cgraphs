From iris.proofmode Require Import tactics.

Lemma lookup_insert_spec `{Countable K} {V} (A : gmap K V) i j v :
  (<[ i := v]> A) !! j = if (decide (i = j)) then Some v else (A !! j).
Proof.
  case_decide.
  - subst. apply lookup_insert.
  - by apply lookup_insert_ne.
Qed.

Lemma lookup_delete_spec `{Countable K} {V} (A : gmap K V) i j :
  (delete i A) !! j = if (decide (i = j)) then None else A !! j.
Proof.
  case_decide.
  - apply lookup_delete_None; eauto.
  - rewrite lookup_delete_ne; eauto.
Qed.

Definition difference_opt {T} (o1 o2 : option T) :=
  match o1,o2 with
  | Some v1, None => Some v1
  | _, _ => None
  end.

Lemma lookup_difference_spec `{Countable K} {V} (A B : gmap K V) i :
  (A ∖ B) !! i = difference_opt (A !! i) (B !! i).
Proof.
  destruct (A !! i) eqn:E.
  - destruct (B !! i) eqn:F; simpl.
    + apply lookup_difference_None. rewrite F. eauto.
    + apply lookup_difference_Some. done.
  - apply lookup_difference_None. eauto.
Qed.

Definition intersection_opt {T} (o1 o2 : option T) :=
  match o1,o2 with
  | Some v1, Some v2 => Some v1
  | _,_ => None
  end.

Lemma lookup_intersection_spec `{Countable K} {V} (A B : gmap K V) i :
  (A ∩ B) !! i = intersection_opt (A !! i) (B !! i).
Proof.
  destruct (A !! i) eqn:E.
  - destruct (B !! i) eqn:F; simpl.
    + apply lookup_intersection_Some. eauto.
    + apply lookup_intersection_None. eauto.
  - apply lookup_intersection_None. eauto.
Qed.

Ltac prep :=
  rewrite ?map_eq_iff ?map_subseteq_spec; intros;
  repeat rewrite ?lookup_insert_spec
                 ?lookup_difference_spec
                 ?lookup_delete_spec
                 ?lookup_union
                 ?lookup_intersection_spec.

Ltac prep_hyp i H :=
  specialize (H i);
  repeat rewrite ?lookup_insert_spec
                 ?lookup_difference_spec
                 ?lookup_delete_spec
                 ?lookup_intersection_spec
                 ?lookup_union in H.

Ltac fin := repeat case_decide; simpl in *; simplify_eq; done.

Lemma foo1 `{Countable K} {V} (A B : gmap K V) :
  A ∪ B = A ∪ B ∪ A.
Proof.
  prep.
  destruct (A !! i) eqn:?;
  destruct (B !! i) eqn:?;
  fin.
Qed.

Lemma foo2 `{Countable K} {V} (A B : gmap K V) :
  B ∪ A = A -> B ⊆ A.
Proof.
  prep.
  prep_hyp i H0.
  destruct (A !! i) eqn:?;
  destruct (B !! i) eqn:?;
  fin.
Qed.

Lemma foo3 `{Countable K} {V} (A B : gmap K V) i v :
  B !! i = None -> <[ i := v ]> (A ∖ B) = (<[ i := v ]> A) ∖ B.
Proof.
  prep.
  destruct (A !! i0) eqn:?;
  destruct (B !! i0) eqn:?;
  fin.
Qed.

Lemma foo4 `{Countable K} {V} (A B : gmap K V) i v :
  <[i:=v]> (A ∪ B) = <[i:=v]> A ∪ delete i B.
Proof.
  prep.
  destruct (A !! i0) eqn:?;
  destruct (B !! i0) eqn:?;
  fin.
Qed.

Lemma foo5 `{Countable K} {V} (A B : gmap K V) i :
  (A ∖ delete i B) !! i = A !! i.
Proof.
  prep.
  destruct (A !! i) eqn:?;
  destruct (B !! i) eqn:?;
  fin.
Qed.

Lemma foo6 `{Countable K} {V} (A B : gmap K V) i v :
  delete i (A ∖ delete i B) = A ∖ <[ i := v ]> B.
Proof.
  prep.
  destruct (A !! i0) eqn:?;
  destruct (B !! i0) eqn:?;
  fin.
Qed.

Lemma foo7 `{Countable K} {V} (A B : gmap K V) i v :
  <[ i := v ]> (A ∪ B) = (<[ i := v ]> A) ∪ B.
Proof.
  prep.
  destruct (A !! i0) eqn:?;
  destruct (B !! i0) eqn:?;
  fin.
Qed.

Lemma foo8 `{Countable K} {V} (A B : gmap K V) i v w :
  <[ i := v ]> (A ∪ B) = (<[ i := v ]> A) ∪ (<[ i := w ]> B).
Proof.
  prep.
  destruct (A !! i0) eqn:?;
  destruct (B !! i0) eqn:?;
  fin.
Qed.

Lemma foo9 `{Countable K} {V} (A B : gmap K V) :
  A ∪ B = A ∪ (B ∖ A).
Proof.
  prep.
  destruct (A !! i) eqn:?;
  destruct (B !! i) eqn:?;
  fin.
Qed.

Lemma foo10 `{Countable K} {V} (A B : gmap K V) i v :
  (<[ i := v]> A) ∪ (delete i B) = (delete i A) ∪ (<[ i := v]> B).
Proof.
  prep.
  destruct (A !! i0) eqn:?;
  destruct (B !! i0) eqn:?;
  fin.
Qed.

Lemma foo11 `{Countable K} {V} (A B : gmap K V) :
  (A ∖ B) ∪ (B ∖ A) = (A ∪ B) ∖ (A ∩ B).
Proof.
  prep.
  destruct (A !! i) eqn:?;
  destruct (B !! i) eqn:?;
  fin.
Qed.

Lemma foo12 `{Countable K} {V} (A B C : gmap K V) :
  A ∖ (B ∪ C) = A ∖ (C ∪ B).
Proof.
  prep.
  destruct (A !! i) eqn:?;
  destruct (B !! i) eqn:?;
  destruct (C !! i) eqn:?;
  fin.
Qed.

Lemma foo13 `{Countable K} {V} (A B C : gmap K V) :
  A ∖ (B ∩ C) = A ∖ (C ∩ B).
Proof.
  prep.
  destruct (A !! i) eqn:?;
  destruct (B !! i) eqn:?;
  destruct (C !! i) eqn:?;
  fin.
Qed.

Lemma foo14 `{Countable K} {V} (A B C : gmap K V) :
  A ∪ B = B ∪ A -> A ∩ B = B ∩ A.
Proof.
  prep.
  prep_hyp i H0.
  destruct (A !! i) eqn:?;
  destruct (B !! i) eqn:?;
  fin.
Qed.

Lemma foo15 `{Countable K} {V} (A B C : gmap K V) :
  A ∪ B = B ∩ A -> A = B.
Proof.
  prep.
  prep_hyp i H0.
  destruct (A !! i) eqn:?;
  destruct (B !! i) eqn:?;
  fin.
Qed.

Lemma foo16 `{Countable K} {V} (A B C : gmap K V) :
  A ∪ B = B ∪ A -> A ∩ B = B ∩ A.
Proof.
  prep.
  prep_hyp i H0.
  destruct (A !! i) eqn:?;
  destruct (B !! i) eqn:?;
  fin.
Qed.