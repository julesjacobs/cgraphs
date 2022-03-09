From iris.algebra Require Export cmra.
From stdpp Require Import gmap.

Record multiset A := MultiSet { multiset_car : list A }.
Arguments MultiSet {_} _.
Arguments multiset_car {_} _.

Section multiset.
  Context {A : ofe}.
  Implicit Types x y : A.
  Implicit Types X Y : multiset A.

  Global Instance multiset_equiv_instance : Equiv (multiset A) := λ X1 X2,
    ∃ xs, multiset_car X1 ≡ₚ xs ∧ xs ≡ multiset_car X2.
    Global Instance multiset_valid_instance : Valid (multiset A) := λ _, True.
  Global Instance multiset_validN_instance : ValidN (multiset A) := λ _ _, True.
  Global Instance multiset_unit_instance : Unit (multiset A) := MultiSet [].
  Global Instance multiset_op_instance : Op (multiset A) := λ X1 X2,
    MultiSet (multiset_car X1 ++ multiset_car X2).
  Global Instance multiset_pcore_instance : PCore (multiset A) := λ X, Some ε.

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

Lemma multiset_singleton_mult' {A : ofe} a1 a2 (x : multiset A) :
  {[ a1 ]} ⋅ x ≡ {[ a2 ]} ->
  a1 ≡ a2 ∧ x = ε.
Proof.
  intros H.
  apply multiset_op_singleton in H as [[]|[]].
  - eapply multiset_singleton_not_unit in H as [].
  - apply (inj _) in H. apply multiset_unit_equiv_eq in H0. done.
Qed.

Lemma multiset_xsplit_singleton {A : ofe} a1 a2 a3 (x : multiset A) :
  {[ a1 ]} ⋅ x ≡ {[ a2 ]} ⋅ {[ a3 ]} ->
  a1 ≡ a2 ∧ x ≡ {[ a3 ]} ∨ a1 ≡ a3 ∧ x ≡ {[ a2 ]}.
Proof.
  intros H.
  eapply mset_xsplit in H as (?&?&?&?&?&?&?&?).
  eapply multiset_singleton_mult in H as [[]|[]].
  - setoid_subst. rewrite left_id in H1. setoid_subst.
    symmetry in H2. eapply multiset_singleton_mult' in H2 as [].
    subst. setoid_subst. eauto.
  - setoid_subst. symmetry in H1.
    eapply multiset_singleton_mult' in H1 as [].
    rewrite left_id in H2. setoid_subst. eauto.
Qed.


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
  Proof. by rewrite !lookup_total_alt lookup_map_kmap. Qed.

  Lemma map_kmap_empty {A} : map_kmap f ∅ =@{M2 A} ∅.
  Proof. unfold map_kmap. by rewrite map_to_list_empty. Qed.
  Lemma map_kmap_singleton {A} i (x : A) : map_kmap f {[ i := x ]} = {[ f i := x ]}.
  Proof. unfold map_kmap. by rewrite map_to_list_singleton. Qed.

  Lemma map_kmap_partial_alter {A} (g : option A → option A) (m : M1 A) i :
    map_kmap f (partial_alter g i m) = partial_alter g (f i) (map_kmap f m).
  Proof.
    apply map_eq; intros j. apply option_eq; intros y.
    destruct (decide (j = f i)) as [->|?].
    { by rewrite lookup_partial_alter !lookup_map_kmap lookup_partial_alter. }
    rewrite lookup_partial_alter_ne ?lookup_map_kmap_Some //. split.
    - intros [i' [? Hm]]; simplify_eq/=.
      rewrite lookup_partial_alter_ne in Hm; naive_solver.
    - intros [i' [? Hm]]; simplify_eq/=. exists i'.
      rewrite lookup_partial_alter_ne; naive_solver.
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
    rewrite map_lookup_imap bind_Some. setoid_rewrite lookup_map_kmap_Some.
    setoid_rewrite map_lookup_imap. setoid_rewrite bind_Some. naive_solver.
  Qed.
  Lemma map_kmap_omap {A B} (g : A → option B) (m : M1 A) :
    map_kmap f (omap g m) = omap g (map_kmap f m).
  Proof.
    apply map_eq; intros j. apply option_eq; intros y.
    rewrite lookup_omap bind_Some. setoid_rewrite lookup_map_kmap_Some.
    setoid_rewrite lookup_omap. setoid_rewrite bind_Some. naive_solver.
  Qed.
  Lemma map_kmap_fmap {A B} (g : A → B) (m : M1 A) :
    map_kmap f (g <$> m) = g <$> (map_kmap f m).
  Proof. by rewrite !map_fmap_alt map_kmap_omap. Qed.
End map_kmap.

Definition list_to_multiset {A} (l : list A) := MultiSet l.

Lemma list_to_multiset_cons {A:ofe} (l : list A) (x : A) :
  list_to_multiset (x :: l) ≡ {[ x ]} ⋅ list_to_multiset l.
Proof. done. Qed.

Global Instance list_to_multiset_proper {A:ofe} : Proper ((≡ₚ) ==> (≡)) (list_to_multiset (A:=A)).
Proof.
  intros ???.
  induction H; eauto.
  - rewrite !list_to_multiset_cons IHPermutation //.
  - rewrite !list_to_multiset_cons !assoc (comm (⋅) {[y]}) //.
  - by rewrite IHPermutation1.
Qed.

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


Section map_to_multiset.
  Context {K : ofe}.
  Context `{HC : Countable K}.
  Context {HL : LeibnizEquiv K}.
  Context {A:ofe}.
  Implicit Type m : gmap K A.
  Implicit Type x : multiset (K*A).
  Implicit Type i : K.
  Implicit Type v : A.

  Definition map_to_multiset m :=
    list_to_multiset (map_to_list m).

  Lemma map_to_multiset_empty :
    map_to_multiset ∅ = ε.
  Proof.
    unfold map_to_multiset.
    rewrite map_to_list_empty //.
  Qed.

  Lemma map_to_multiset_empty' m :
    (∀ i, m !! i = None) ->
    map_to_multiset m = ε.
  Proof.
    intros HH.
    assert (m = ∅) as -> by by apply map_empty.
    apply map_to_multiset_empty.
  Qed.

  Lemma map_to_multiset_insert m i v :
    m !! i = None ->
    map_to_multiset (<[i:=v]> m) ≡ {[ (i, v) ]} ⋅ map_to_multiset m.
  Proof.
    intros Hi.
    unfold map_to_multiset.
    rewrite map_to_list_insert //.
  Qed.

  Lemma map_to_multiset_lookup m i v x :
    {[ (i, v) ]} ⋅ x ≡ map_to_multiset m ->
    m !! i ≡ Some v.
  Proof.
    revert x. induction m using map_ind; intros x'.
    - rewrite map_to_multiset_empty.
      intros HH. eapply multiset_empty_mult in HH as [].
      exfalso.
      eapply multiset_empty_neq_singleton; done.
    - rewrite map_to_multiset_insert //.
      intros HH.
      eapply mset_xsplit in HH as (e11 & e12 & e21 & e22 & Q1 & Q2 & Q3 & Q4).
      eapply multiset_singleton_mult in Q1.
      eapply multiset_singleton_mult in Q3.
      destruct Q1 as [[H11 H12]|[H11 H12]].
      + rewrite ->H12 in Q4.
        symmetry in Q4.
        pose proof (IHm _ Q4) as H6.
        rewrite lookup_insert_spec.
        case_decide; subst; eauto.
        rewrite H in H6. inversion H6.
      + rewrite ->H12 in Q4.
        revert Q4. rewrite left_id. intros Q4.
        destruct Q3 as [[H31 H32]|[H31 H32]].
        * rewrite ->H11 in H31.
          exfalso. eapply multiset_empty_neq_singleton, multiset_unit_equiv_eq.
          exact H31.
        * rewrite ->H11 in H31.
          eapply inj in H31; last apply _.
          inversion H31; simpl in *.
          rewrite H1.
          assert (i = i0).
          { apply leibniz_equiv. done. } subst.
          rewrite lookup_insert //.
  Qed.

  Lemma map_to_multiset_delete m i v x :
    {[ (i, v) ]} ⋅ x ≡ map_to_multiset m ->
    x ≡ map_to_multiset (delete i m).
  Proof.
    intros HH.
    pose proof (map_to_multiset_lookup _ _ _ _ HH) as Hi.
    inversion Hi; subst.
    replace m with (<[ i := x0 ]> (delete i m)) in HH; last first.
    { apply map_eq. intros j.
      rewrite lookup_insert_spec lookup_delete_spec.
      case_decide; subst; eauto. }
    rewrite ->map_to_multiset_insert in HH; last apply lookup_delete.
    rewrite ->H1 in HH.
    by apply multiset_op_inj in HH.
  Qed.

  Lemma map_to_multiset_update m x i v v' :
    {[ (i, v) ]} ⋅ x ≡ map_to_multiset m ->
    {[ (i, v') ]} ⋅ x ≡ map_to_multiset (<[i:=v']> m).
  Proof.
    rewrite <-fin_maps.insert_delete_insert.
    rewrite map_to_multiset_insert; last apply lookup_delete.
    intros H.
    rewrite <-map_to_multiset_delete; done.
  Qed.

  Lemma map_to_multiset_Some m i v :
    m !! i = Some v ->
    map_to_multiset m ≡ {[ (i,v) ]} ⋅ map_to_multiset (delete i m).
  Proof.
    intros H.
    replace m with (<[ i := v ]> (delete i m)); last first.
    { apply map_eq. intros j.
      rewrite lookup_insert_spec lookup_delete_spec.
      case_decide; naive_solver. }
    rewrite delete_insert; last apply lookup_delete.
    rewrite map_to_multiset_insert //. apply lookup_delete.
  Qed.
End map_to_multiset.

Global Instance multiset_fmap : FMap multiset :=
  λ A B f m, list_to_multiset (f <$> multiset_car m).