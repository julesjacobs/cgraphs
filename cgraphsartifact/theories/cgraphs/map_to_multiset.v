From diris Require Export multiset.
From diris Require Export rtypesystem.

Definition list_to_multiset {A} (l : list A) := MultiSet l.

Lemma list_to_multiset_cons {A:ofe} (l : list A) (x : A) :
  list_to_multiset (x :: l) ≡ {[ x ]} ⋅ list_to_multiset l.
Proof. done. Qed.

Instance list_to_multiset_proper {A:ofe} : Proper ((≡ₚ) ==> (≡)) (list_to_multiset (A:=A)).
Proof.
  intros ???.
  induction H; eauto.
  - rewrite !list_to_multiset_cons IHPermutation //.
  - rewrite !list_to_multiset_cons !assoc (comm (⋅) {[y]}) //.
  - by rewrite IHPermutation1.
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
