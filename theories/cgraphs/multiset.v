From iris.algebra Require Export cmra.

Record multiset A := MultiSet { multiset_car : list A }.
Arguments MultiSet {_} _.
Arguments multiset_car {_} _.

Section multiset.
  Context {A : ofe}.
  Implicit Types x y : A.
  Implicit Types X Y : multiset A.

  Local Instance multiset_equiv_instance : Equiv (multiset A) := λ X1 X2,
    ∃ xs, multiset_car X1 ≡ₚ xs ∧ xs ≡ multiset_car X2.
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
    - intros X. by exists (multiset_car X).
    - intros X1 X2 (xs&?&?). by eapply equiv_Permutation.
    - intros X1 X2 X3 (xs1&?&?) (xs2&?&?).
      destruct (equiv_Permutation xs1 (multiset_car X2) xs2) as (xs&?&?); [done..|].
      exists xs; split; by etrans.
  Qed.
  Canonical Structure multisetO := discreteO (multiset A).

  Global Instance multiset_ofe_discrete : OfeDiscrete multisetO.
  Proof. by intros X1 X2. Qed.

  Lemma multiset_ra_mixin : RAMixin (multiset A).
  Proof.
    apply ra_total_mixin;
      rewrite /equiv /multiset_equiv_instance /=; try by eauto.
    - intros X Y1 Y2 (xs&?&?); simpl.
      exists (multiset_car X ++ xs); split; by f_equiv.
    - intros X1 X2 (xs&?&?). by exists [].
    - intros X1 X2 X3. exists (multiset_car (X1 ⋅ (X2 ⋅ X3))).
      by rewrite /= (assoc (++)).
    - intros X1 X2. exists (multiset_car (X2 ⋅ X1)).
      split; [|done]. by rewrite /= (comm (++)).
    - intros X1 X2 _. by exists ε.
  Qed.
  Canonical Structure multisetR := discreteR (multiset A) multiset_ra_mixin.

  Global Instance multiset_cmra_discrete : CmraDiscrete multisetR.
  Proof. apply discrete_cmra_discrete. Qed.

  Lemma multiset_ucmra_mixin : UcmraMixin (multiset A).
  Proof.
    split; [done | | done].
    intros X. by exists (multiset_car X).
  Qed.
  Canonical Structure multisetUR := Ucmra (multiset A) multiset_ucmra_mixin.

  Global Instance multiset_op_inj X : Inj (≡) (≡) (op X).
  Proof.
    destruct X as [xs]. intros [ys1] [ys2] (ys&Hperm&Hequiv); hnf; simpl in *.
    revert ys Hperm Hequiv.
    induction xs as [|x xs IH]; intros ys Hperm Hequiv; simpl in *.
    { by exists ys. }
    apply Permutation_cons_inv_l in Hperm as ([|y ys1']&ys2'&->&?);
      inversion_clear Hequiv; simplify_eq/=; [by eauto|].
    apply (IH (ys1' ++ y :: ys2')).
    - by rewrite -Permutation_middle.
    - by setoid_subst.
  Qed.

  Global Instance multiset_cancelable X : Cancelable X.
  Proof. apply (discrete_cancelable _). by intros Y1 Y2 _ ?%(inj _). Qed.

  Global Instance multiset_singleton_proper :
    Proper ((≡) ==> (≡)) (singleton (B:=multiset A)).
  Proof. intros x1 x2 ?. exists [x1]; by repeat constructor. Qed.
  Global Instance multiset_singleton_inj :
    Inj (≡) (≡) (singleton (B:=multiset A)).
  Proof.
    by intros x1 x2 (xs&<-%Permutation_singleton_l&
      (?&[= <-]&?)%list_singleton_equiv_eq).
  Qed.

  Lemma multiset_unit_equiv_eq X : X ≡ ε ↔ X = ε.
  Proof.
    split; [|by intros ->].
    intros (xs&Hperm&->%nil_equiv_eq). apply Permutation_nil_r in Hperm.
    destruct X; naive_solver.
  Qed.

  Lemma multiset_cross_split (Xa Xb Xc Xd : multiset A) :
    Xa ⋅ Xb ≡ Xc ⋅ Xd →
    ∃ Xac Xad Xbc Xbd,
      Xac ⋅ Xad ≡ Xa ∧ Xbc ⋅ Xbd ≡ Xb ∧ Xac ⋅ Xbc ≡ Xc ∧ Xad ⋅ Xbd ≡ Xd.
  Proof.
    intros (xs&Hperm&(xsc&xsd&->&?&?)%app_equiv_eq).
    apply Permutation_cross_split in Hperm as (xsac&xsad&xsbc&xsbd&?&?&?&?).
    exists (MultiSet xsac), (MultiSet xsad), (MultiSet xsbc), (MultiSet xsbd).
    split_and!; by eexists.
  Qed.

  Lemma multiset_singleton_not_unit x : {[ x ]} ≢@{multiset A} ε.
  Proof.
    intros (xs&Hperm&->%nil_equiv_eq). by apply Permutation_nil_r in Hperm.
  Qed.

  Lemma multiset_op_unit X1 X2 : X1 ⋅ X2 ≡ ε → X1 ≡ ε ∧ X2 ≡ ε.
  Proof.
    destruct X1 as [xs1], X2 as [xs2]. intros (xs&Hperm&->%nil_equiv_eq).
    apply Permutation_nil_r in Hperm as [??]%app_eq_nil; by simplify_eq/=.
  Qed.

  Lemma multiset_op_singleton X1 X2 x :
    X1 ⋅ X2 ≡ {[ x ]} → (X1 ≡ ε ∧ X2 ≡ {[ x ]}) ∨ (X1 ≡ {[ x ]} ∧ X2 ≡ ε).
  Proof.
    destruct X1 as [xs1], X2 as [xs2].
    intros (xs&Hperm&(x'&->&?)%list_singleton_equiv_eq).
    apply Permutation_singleton_r in Hperm as [[??]|[??]]%app_eq_unit;
      simplify_eq/=; [left|right]; by repeat econstructor.
  Qed.

  Lemma multiset_equiv_alt X1 X2 : X1 ≡ X2 ↔ X1 ≼ X2 ∧ X2 ≼ X1.
  Proof.
    split; [by intros ->|].
    intros [[Y1 HX1] [Y2 HX2]].
    assert (X1 ⋅ (Y1 ⋅ Y2) ≡ X1 ⋅ ε) as [HY1 HY2]%(inj _)%multiset_op_unit.
    { by rewrite assoc -HX1 -HX2 right_id. }
    by rewrite HX2 HY2 right_id.
  Qed.
  Global Instance multiset_subseteq_anti_symm : AntiSymm (≡@{multiset A}) (≼).
  Proof. intros X1 X2 ??. by apply multiset_equiv_alt. Qed.
  Global Instance multiset_op_subseteq_inj X : Inj (≼) (≼) (op X).
  Proof. intros X1 X2 [Y ?]. exists Y. apply (inj (op X)). by rewrite assoc. Qed.

  Lemma multiset_subseteq_unit X : X ≼ ε ↔ X ≡ ε.
  Proof. split; [|by intros ->]. by intros [Y [??]%symmetry%multiset_op_unit]. Qed.
  Lemma multiset_included_singleton (x1 x2 : A) : ({[ x1 ]} : multiset A) ≼ {[ x2 ]} ↔ x1 ≡ x2.
  Proof.
    split; [|by intros ->].
    intros [K [[[]%multiset_singleton_not_unit ?]|[??]]%symmetry%multiset_op_singleton].
    by apply (inj singleton).
  Qed.
  Lemma multiset_singleton_included x X1 X2 :
    {[ x ]} ≼ X1 ⋅ X2 ↔ {[ x ]} ≼ X1 ∨ {[ x ]} ≼ X2.
  Proof.
    split.
    - intros [Y (Xac&Xad&Xbc&Xbd&?&?&
        [[??]|[??]]%multiset_op_singleton&?)%multiset_cross_split]; setoid_subst.
      + right. by exists Xbd.
      + left. by exists Xad.
    - intros [[Y HX]|[Y HX]].
      + exists (Y ⋅ X2). by rewrite assoc -HX.
      + exists (Y ⋅ X1). by rewrite assoc -HX comm.
  Qed.

  Global Instance multiset_elem_of_instance : ElemOf A (multiset A) := λ x X,
    {[ x ]} ≼ X.
  Global Instance multiset_elem_of_proper :
    Proper ((≡) ==> (≡@{multiset A}) ==> iff) (∈).
  Proof. unfold elem_of. solve_proper. Qed.
  Lemma multiset_elem_of x X : x ∈ X ↔ {[ x ]} ≼ X.
  Proof. done. Qed.

  Lemma multiset_elem_of_unit x : x ∉@{multiset A} ε.
  Proof.
    rewrite multiset_elem_of multiset_subseteq_unit.
    apply multiset_singleton_not_unit.
  Qed.
  Lemma multiset_elem_of_singleton x y : x ∈@{multiset A} {[ y ]} ↔ x ≡ y.
  Proof. by rewrite !multiset_elem_of multiset_included_singleton. Qed.
  Lemma multiset_elem_of_op x X1 X2 : x ∈ X1 ⋅ X2 ↔ x ∈ X1 ∨ x ∈ X2.
  Proof. by rewrite !multiset_elem_of multiset_singleton_included. Qed.
End multiset.

Global Arguments multisetO : clear implicits.
Global Arguments multisetR : clear implicits.
Global Arguments multisetUR : clear implicits.


Lemma multiset_empty_mult {A : ofe} (x y : multiset A) :
  x ⋅ y ≡ ε -> x = ε ∧ y = ε.
Proof.
  intros. apply multiset_op_unit in H as [].
  rewrite -!multiset_unit_equiv_eq. done.
Qed.

Lemma multiset_empty_neq_singleton {A : ofe} {a : A} :
  {[ a ]} ≠@{multiset A} ε.
Proof.
  intro.
  eapply multiset_singleton_not_unit.
  apply multiset_unit_equiv_eq. done.
  Unshelve. done. done.
Qed.

Lemma mset_xsplit {A : ofe} (e1 e2 e1' e2' : multiset A) :
  e1 ⋅ e2 ≡ e1' ⋅ e2' ->
  ∃ e11 e12 e21 e22,
    e1 ≡ e11 ⋅ e12 ∧
    e2 ≡ e21 ⋅ e22 ∧
    e1' ≡ e11 ⋅ e21 ∧
    e2' ≡ e12 ⋅ e22.
Proof.
  intros.
  apply multiset_cross_split in H as (?&?&?&?&?&?&?&?).
  symmetry in H.
  symmetry in H0.
  symmetry in H1.
  symmetry in H2.
  eauto 10.
Qed.

Lemma multiset_singleton_mult {A:ofe} (a : A) (x y : multiset A) :
  {[ a ]} ≡ x ⋅ y ->
  (x ≡ ε ∧ y ≡ {[ a ]}) ∨ (x ≡ {[ a ]} ∧ y ≡ ε).
Proof.
  intros H.
  symmetry in H.
  apply multiset_op_singleton in H. eauto.
Qed.

