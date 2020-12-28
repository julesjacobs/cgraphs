(* Import all convenient notations and tactics from Iris... *)
From iris.bi Require Import bi.

(* Requires -impredicative-set *)
Definition N : Set := ∀ (t : Set), t -> (t -> t) -> t.

Definition Z : N := λ t z f, z.
Definition S (n : N) : N := λ t z f, f (n t z f).

Definition induction_N :=
  ∀ (P : N -> Prop), P Z -> (∀ (n : N), P n -> P (S n)) -> ∀ (n : N), P n.

Definition unary_parametricity_N :=
  ∀ (t : Set) (P : t -> Prop) (z : t) (f : t -> t),
    P z ->
    (∀ (x:t), P x -> P (f x)) ->
    ∀ n:N, P (n t z f).

Definition binary_parametricity_N :=
  ∀ (t1 t2 : Set) (P : t1 -> t2 -> Prop) (z1 : t1) (z2 : t2) (f1 : t1 -> t1) (f2 : t2 -> t2),
    P z1 z2 ->
    (∀ (x1 : t1) (x2 : t2), P x1 x2 -> P (f1 x1) (f2 x2)) ->
    ∀ n:N, P (n t1 z1 f1) (n t2 z2 f2).

Definition induction_N' :=
  ∀ (P : N -> Prop), P Z -> (∀ (n : N), P n -> P (S n)) -> ∀ (n : N), P (n N Z S).

Lemma binary_parametricity_implies_unary_parametricity :
  binary_parametricity_N -> unary_parametricity_N.
Proof.
  intros Hb t P. specialize (Hb t t (λ x y, P x)). eauto.
Qed.

Lemma unary_parametricity_implies_induction_N' :
  unary_parametricity_N -> induction_N'.
Proof.
  intros Hu ????. eapply Hu; eauto.
Qed.

Lemma binary_parametricity_implies_obs :
  binary_parametricity_N -> ∀ (n:N) (t:Set) z f, n t z f = n N Z S t z f.
Proof.
  intros Hb n t z f.
  unfold binary_parametricity_N in Hb.
  specialize (Hb t N (λ x y, x = y t z f)).
  simpl in *.
  apply Hb.
  - unfold Z. reflexivity.
  - intros x1 x2 H. unfold S. f_equiv. eauto.
Qed.

(* Leibniz equality *)

Definition eq {t : Set} (x y : t) :=
  ∀ P : t -> Prop, P x -> P y.

Lemma eq_trans (t : Set) (x y z : t) :
  eq x y -> eq y z -> eq x z.
Proof.
  intros Hxy Hyz ??. apply Hyz. apply Hxy. eauto.
Qed.

Lemma eq_refl (t : Set) (x : t) :
  eq x x.
Proof.
  intro. eauto.
Qed.

Lemma eq_sym (t : Set) (x y : t) :
  eq x y -> eq y x.
Proof.
  intros H P. specialize (H (λ z, P z -> P x)). eauto.
Qed.

Lemma eq_equals (t : Set) (x y : t) :
  eq x y <-> x = y.
Proof.
  split.
  - intros H. specialize (H (λ z, x = z)). eauto.
  - intros ->. apply eq_refl.
Qed.

Definition bp (n1 n2 : N) :=
  ∀ (t1 t2 : Set) (P : t1 -> t2 -> Prop) (z1 : t1) (z2 : t2) (f1 : t1 -> t1) (f2 : t2 -> t2),
    P z1 z2 ->
    (∀ (x1 : t1) (x2 : t2), P x1 x2 -> P (f1 x1) (f2 x2)) ->
    P (n1 t1 z1 f1) (n2 t2 z2 f2).

(* bp_refl : (∀ n:N, bp n n) is binary parametricity for N, so we can't prove it *)

Lemma bp_sym (n m : N) :
  bp n m -> bp m n.
Proof.
  intros H. unfold bp. intros.
  specialize (H t2 t1 (λ x y, P y x)). eauto.
Qed.

Lemma bp_equals (n m : N) (t : Set) (z : t) (f : t -> t) :
  bp n m -> n t z f = m t z f.
Proof.
  intros H.
  unfold bp in H.
  specialize (H t t (λ x y, x = y)).
  simpl in *.
  apply H.
  - eauto.
  - intros ?? ->. eauto.
Qed.