From diris Require Export multiset.
From diris Require Export rtypesystem.

Definition list_to_multiset {A} (l : list A) := MultiSet l.

Instance list_to_multiset_proper {A:ofe} : Proper ((≡ₚ) ==> (≡)) (list_to_multiset (A:=A)).
Proof.
Admitted.

Section map_to_multiset.
  Implicit Type m : gmap bool chan_type.
  Implicit Type x : multiset clabel.
  Implicit Type i : bool.
  Implicit Type v : chan_type.

  Definition map_to_multiset m : multiset clabel :=
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
    intros H.
    assert (m = ∅) as -> by by apply map_empty.
    apply map_to_multiset_empty.
  Qed.

  Lemma map_to_multiset_lookup m i v x :
    {[ (i, v) ]} ⋅ x ≡ map_to_multiset m ->
    m !! i = Some v.
  Proof.
    intros H.
    unfold map_to_multiset in H.
    symmetry in H.
    (* apply map_to_list_insert_inv in H. *)
  Admitted.

  Lemma map_to_multiset_insert m i v :
    m !! i = None ->
    map_to_multiset (<[i:=v]> m) ≡ {[ (i, v) ]} ⋅ map_to_multiset m.
  Proof.
    intros Hi.
    unfold map_to_multiset.
    rewrite map_to_list_insert //.
  Qed.

  Lemma map_to_multiset_delete m i v x :
    {[ (i, v) ]} ⋅ x ≡ map_to_multiset m ->
    x ≡ map_to_multiset (delete i m).
  Proof.
    intros H.
    pose proof (map_to_multiset_lookup _ _ _ _ H) as Hi.
    replace m with (<[ i := v ]> (delete i m)) in H; last first.
    { apply map_eq. intros j.
      rewrite lookup_insert_spec lookup_delete_spec.
      case_decide; naive_solver. }
    rewrite ->map_to_multiset_insert in H; last apply lookup_delete.
    by apply multiset_mult_singleton_inv in H.
  Qed.

  Lemma map_to_multiset_update m x i v v' :
    {[ (i, v) ]} ⋅ x ≡ map_to_multiset m ->
    {[ (i, v') ]} ⋅ x ≡ map_to_multiset (<[i:=v']> m).
  Proof.
    rewrite <-fin_maps.insert_delete.
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
