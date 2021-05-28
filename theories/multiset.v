From Coq Require Import SetoidPermutation.
From iris.algebra Require Export cmra.

Lemma PermutationA_mono {A} (R1 R2 : relation A) xs1 xs2 :
  (∀ x1 x2, R1 x1 x2 → R2 x1 x2) →
  PermutationA R1 xs1 xs2 → PermutationA R2 xs1 xs2.
Proof. induction 2; econstructor; by eauto. Qed.

Record multiset A := MultiSet { multiset_car : list A }.
Arguments MultiSet {_} _.
Arguments multiset_car {_} _.

Section multiset.
  Context {A : ofe}.
  Implicit Types x y : A.
  Implicit Types X Y : multiset A.

  Local Instance multiset_equiv_instance : Equiv (multiset A) := λ X1 X2,
    ∀ n, PermutationA (≡{n}≡) (multiset_car X1) (multiset_car X2).
  Local Instance multiset_dist_instance : Dist (multiset A) := λ n X1 X2,
    PermutationA (≡{n}≡) (multiset_car X1) (multiset_car X2).
  Local Instance multiset_valid_instance : Valid (multiset A) := λ _, True.
  Local Instance multiset_validN_instance : ValidN (multiset A) := λ _ _, True.
  Local Instance multiset_unit_instance : Unit (multiset A) := MultiSet [].
  Local Instance multiset_op_instance : Op (multiset A) := λ X1 X2,
    MultiSet (multiset_car X1 ++ multiset_car X2).
  Local Instance multiset_pcore_instance : PCore (multiset A) := λ X, Some ε.

  Global Instance multiset_singleton : Singleton A (multiset A) := λ x,
    MultiSet [x].

  Lemma multiset_ofe_mixin : OfeMixin (multiset A).
  Proof.
    split; rewrite /equiv /dist /multiset_equiv_instance /multiset_dist_instance /=.
    - done.
    - intros n. split.
      + by intros X.
      + intros X1 X2 ?. done.
      + intros X1 X2 X3 ??. by etrans.
    - intros n X1 X2. apply PermutationA_mono, dist_S.
  Qed.
  Canonical Structure multisetO := Ofe (multiset A) multiset_ofe_mixin.

  Global Instance multiset_ofe_discrete : OfeDiscrete A → OfeDiscrete multisetO.
  Proof.
    intros HA [xs1] [xs2] Hxs n. revert Hxs. apply PermutationA_mono.
    by intros x1 x2 ->%(discrete _).
  Qed.

  Lemma multiset_cmra_mixin : CmraMixin (multiset A).
  Proof.
    apply cmra_total_mixin; try by eauto.
    - intros X n Y1 Y2 HY. by apply (PermutationA_app _).
    - by intros n X1 X2.
    - intros X1 X2 X3. admit.
    - intros X1 X2 n. apply (PermutationA_app_comm _).
    - by intros X n.
    - intros X1 X2 _. exists ε. by intros n.
    - intros n [xs] [ys1] [ys2] _. rewrite /equiv /dist /op
        /multiset_equiv_instance /multiset_dist_instance /multiset_op_instance /=.
      induction ys1 as [|y1 ys1 IH]; intros Hxs; simpl in *.
      { by exists (MultiSet []), (MultiSet xs). }
      admit.
  Admitted.
  Canonical Structure multisetR := Cmra (multiset A) multiset_cmra_mixin.

  Lemma multiset_ucmra_mixin : UcmraMixin (multiset A).
  Proof. split; [done | | done]. by intros X n. Qed.
  Canonical Structure multisetUR := Ucmra (multiset A) multiset_ucmra_mixin.

  Global Instance multiset_cancelable X : Cancelable X.
  Proof. Admitted.

  Global Instance multiset_singleton_ne : NonExpansive (singleton (B:=multiset A)).
  Proof. intros n x1 x2. by repeat constructor. Qed.
  Global Instance multiset_singleton_proper :
    Proper ((≡) ==> (≡)) (singleton (B:=multiset A)).
  Proof. apply (ne_proper _). Qed.
  Global Instance multiset_singleton_dist_inj n :
    Inj (dist n) (dist n) (singleton (B:=multiset A)).
  Proof. intros x1 x2. Admitted.
  Global Instance multiset_singleton_inj :
    Inj (≡) (≡) (singleton (B:=multiset A)).
  Proof.
    intros x1 x2 Hx. apply equiv_dist=> n. apply (inj singleton). by rewrite Hx.
  Qed.
End multiset.

Global Arguments multisetO : clear implicits.
Global Arguments multisetR : clear implicits.
Global Arguments multisetUR : clear implicits.