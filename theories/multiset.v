From Coq Require Import SetoidPermutation.
From iris.algebra Require Export cmra.
From stdpp Require Export gmap.

Lemma PermutationA_mono {A} (R1 R2 : relation A) xs1 xs2 :
  (∀ x1 x2, R1 x1 x2 → R2 x1 x2) →
  PermutationA R1 xs1 xs2 → PermutationA R2 xs1 xs2.
Proof. induction 2; econstructor; by eauto. Qed.

Section PermutationA.
  Context {A} (R : relation A) `{!Equivalence R}.

  Global Instance PermutationA_app_assoc : Assoc (PermutationA R) (++).
  Proof.
    intros ???. by rewrite assoc.
  Qed.
  Global Instance PermutationA_app_comm : Comm (PermutationA R) (++).
  Proof. intros xs1 xs2. by apply PermutationA_app_comm. Qed.

  Lemma PermutationA_length xs1 xs2 :
    PermutationA R xs1 xs2 → length xs1 = length xs2.
  Proof. induction 1; simpl; auto with lia. Qed.

  Lemma PermutationA_nil xs : PermutationA R xs [] ↔ xs = [].
  Proof.
    split; [|intros ->; constructor].
    by intros ?%PermutationA_length%length_zero_iff_nil.
  Qed.

  Lemma Permutation_inv_l x xs1 xs2 ys :
    PermutationA R (xs1 ++ x :: xs2) ys →
    ∃ ys1 y ys2,
      ys = ys1 ++ y :: ys2 ∧ R x y ∧ PermutationA R (xs1 ++ xs2) (ys1 ++ ys2).
  Proof.
    intros Hperm. remember (xs1 ++ x :: xs2) as xs eqn:Hxs.
    revert x xs1 xs2 Hxs.
    induction Hperm as [|z1 z2 zs1 zs2 ?? IH|z1 z2 zs|zs1 zs2 zs3 ? IH1 ? IH2];
      intros x xs1 xs2 ?; simplify_eq/=.
    - by destruct xs1.
    - destruct xs1 as [|x1 xs1]; simplify_eq/=.
      { by eexists [], _, _. }
      destruct (IH _ _ _ eq_refl) as (ys1&y&ys2&->&?&?).
      eexists (_ :: _), _, _. by repeat constructor.
    - destruct xs1 as [|x1 [|x2 xs1]]; simplify_eq/=.
      + by eexists [_], _, _.
      + by eexists [], _, _.
      + eexists (_ :: _ :: _), _, _; by repeat constructor.
    - destruct (IH1 _ _ _ eq_refl) as (ys1&y&ys2&->&?&?).
      destruct (IH2 _ _ _ eq_refl) as (ys1'&y'&ys2'&->&?&?).
      eexists _, _, _; split_and!; [done|by etrans..].
  Qed.

  Global Instance PermutationA_cons_inj_l x :
    Inj (PermutationA R) (PermutationA R) (x ::.).
  Proof.
    intros xs ys ([|y1 ys1]&y2&ys2&?&Hy&Hxs)%(Permutation_inv_l _ []);
      simplify_eq/=; [done|].
    by rewrite Hxs Hy PermutationA_middle.
  Qed.
  Global Instance PermutationA_app_inj_l xs :
    Inj (PermutationA R) (PermutationA R) (xs ++.).
  Proof.
    intros ys1 ys2 H. induction xs as [|x xs IH]; simpl in *; [done|].
    by apply IH, (inj (x ::.)).
  Qed.
  Lemma PermutationA_singleton_inv_l x1 xs :
    PermutationA R [x1] xs → ∃ x2, xs = [x2] ∧ R x1 x2.
  Proof.
    intros (ys1&y&ys2&->&?&Hnil)%(Permutation_inv_l _ []).
    symmetry in Hnil. apply PermutationA_nil in Hnil as [-> ->]%app_eq_nil.
    eauto.
  Qed.
End PermutationA.

Record multiset A := MultiSet { multiset_car : list A }.
Arguments MultiSet {_} _.
Arguments multiset_car {_} _.

Section multiset.
  Context {A : ofe}.
  Implicit Types x y : A.
  Implicit Types X Y : multiset A.

  Local Instance multiset_equiv_instance : Equiv (multiset A) := λ X1 X2,
    PermutationA (≡) (multiset_car X1) (multiset_car X2).
  Local Instance multiset_valid_instance : Valid (multiset A) := λ _, True.
  Local Instance multiset_validN_instance : ValidN (multiset A) := λ _ _, True.
  Local Instance multiset_unit_instance : Unit (multiset A) := MultiSet [].
  Local Instance multiset_op_instance : Op (multiset A) := λ X1 X2,
    MultiSet (multiset_car X1 ++ multiset_car X2).
  Local Instance multiset_pcore_instance : PCore (multiset A) := λ X, Some ε.

  Global Instance multiset_singleton : Singleton A (multiset A) := λ x,
    MultiSet [x].

  Local Instance multiset_equivalence : Equivalence multiset_equiv_instance.
  Proof.
    split; rewrite /multiset_equiv_instance.
    - by intros X.
    - intros X1 X2 ?. done.
    - intros X1 X2 X3 ??. by etrans.
  Qed.
  Canonical Structure multisetO := discreteO (multiset A).

  Global Instance multiset_ofe_discrete : OfeDiscrete multisetO.
  Proof. by intros X1 X2. Qed.

  Lemma multiset_ra_mixin : RAMixin (multiset A).
  Proof.
    apply ra_total_mixin;
      rewrite /equiv /multiset_equiv_instance /=; try by eauto.
    - intros X Y1 Y2 HY. by apply (PermutationA_app _).
    - by intros X1 X2.
    - intros X1 X2 X3. apply (assoc (++)).
    - intros X1 X2. apply (comm (++)).
    - intros X1 X2 _. by exists ε.
  Qed.
  Canonical Structure multisetR := discreteR (multiset A) multiset_ra_mixin.

  Global Instance multiset_cmra_discrete : CmraDiscrete multisetR.
  Proof. apply discrete_cmra_discrete. Qed.

  Lemma multiset_ucmra_mixin : UcmraMixin (multiset A).
  Proof.
    split; [done | | done].
    rewrite /equiv /multiset_equiv_instance. by intros X.
  Qed.
  Canonical Structure multisetUR := Ucmra (multiset A) multiset_ucmra_mixin.

  Global Instance multiset_cancelable X : Cancelable X.
  Proof.
    apply (discrete_cancelable _). intros Y1 Y2 _.
    apply (PermutationA_app_inj_l _).
  Qed.

  Global Instance multiset_singleton_proper :
    Proper ((≡) ==> (≡)) (singleton (B:=multiset A)).
  Proof. intros x1 x2. by repeat constructor. Qed.
  Global Instance multiset_singleton_inj :
    Inj (≡) (≡) (singleton (B:=multiset A)).
  Proof. by intros x1 x2 (?&[= ->]&?)%(PermutationA_singleton_inv_l _). Qed.
End multiset.

Global Arguments multisetO : clear implicits.
Global Arguments multisetR : clear implicits.
Global Arguments multisetUR : clear implicits.

Lemma multiset_empty_mult {A : ofe} (x y : multiset A) :
  x ⋅ y ≡ ε -> x = ε ∧ y = ε.
Proof.
Admitted.

Lemma multiset_empty_neq_singleton {A : ofe} {a : A} :
  {[ a ]} ≠@{multiset A} ε.
Proof.
Admitted.

Lemma mset_xsplit {A : ofe} (e1 e2 e1' e2' : multiset A) :
  e1 ⋅ e2 ≡ e1' ⋅ e2' ->
  ∃ e11 e12 e21 e22,
    e1 ≡ e11 ⋅ e12 ∧
    e2 ≡ e21 ⋅ e22 ∧
    e1' ≡ e11 ⋅ e21 ∧
    e2' ≡ e12 ⋅ e22.
Proof.
Admitted.

Lemma multiset_singleton_mult {A:ofe} (a : A) (x y : multiset A) :
  {[ a ]} ≡ x ⋅ y ->
  (x ≡ ε ∧ y ≡ {[ a ]}) ∨ (x ≡ {[ a ]} ∧ y ≡ ε).
Proof.
Admitted.

Lemma multiset_empty_equiv {A:ofe} (x:multiset A) :
  x ≡ ε -> x = ε.
Proof.
Admitted.

Lemma multiset_singleton_inv {A:ofe} (a b : A) :
  {[ a ]} ≡ ({[ b ]} : multiset A) -> a ≡ b.
Proof.
Admitted.

Lemma multiset_mult_singleton_inv {A:ofe} (a : A) (x x' : multiset A) :
  {[ a ]} ⋅ x ≡ {[ a ]} ⋅ x' -> x ≡ x'.
Proof.
Admitted.