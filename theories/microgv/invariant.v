From diris.microgv Require Export rtypesystem.

Definition linv (ρ : cfg) (v : vertex) (in_l : multiset label) : rProp :=
  match v with
  | VThread k =>
    ⌜⌜ in_l ≡ ε ⌝⌝ ∗
    match ρ !! k with
    | Some (Thread e) => rtyped0 e UnitT
    | _ => emp
    end
  | VBarrier k =>
    ⌜⌜ match ρ !! k with
      | Some Barrier => ∃ t1 t2, in_l ≡ {[ (t1,t2)]} ⋅ {[ (t2,t1) ]}
      | _ => in_l ≡ ε
      end ⌝⌝
  end%I.

Instance lin_Proper ρ v : Proper ((≡) ==> (≡)) (linv ρ v).
Proof. solve_proper. Qed.

Definition ginv ρ := inv (linv ρ).

Lemma lookup_union_spec `{Countable K} {V} (m1 m2 : gmap K V) (x : K) :
  (m1 ∪ m2) !! x = from_option Some (m2 !! x) (m1 !! x).
Proof.
  rewrite lookup_union.
  destruct (m1 !! x),(m2 !! x); simpl; eauto.
Qed.

Ltac sdec := repeat (progress simp || case_decide || done || eauto).
Ltac smap := repeat (
  rewrite lookup_union_spec ||
  rewrite lookup_alter_spec ||
  rewrite lookup_insert_spec ||
  rewrite lookup_delete_spec ||
  rewrite lookup_empty || sdec).

Lemma preservation i ρ ρ' :
  step i ρ ρ' -> ginv ρ -> ginv ρ'.
Proof.
  intros H Hinv.
  destruct H as [ρ ρ' ρf D1 D2 i H].
  destruct H.
  - eapply inv_impl; last done.
    iIntros ([n|n] x) "H"; smap.
    iDestruct "H" as "[? H]". iFrame.
    iDestruct (replacement with "H") as (t) "[H Q]"; first done.
    iApply "Q". iApply pure_preservation; done.
  - eapply inv_impl; last done.
    iIntros ([n|n] x) "H"; smap; iDestr "H";
    assert (ρf !! n = None) as -> by solve_map_disjoint; eauto.
    destruct v; simpl; iDestr "H"; simp. done.
  - eapply (inv_alloc_lr (VThread i0) (VBarrier n) (VThread j));
    last done; first apply _; first apply _.
    + naive_solver.
    + iIntros (? ? ?) "H". simp.
      destruct v0; simpl; smap;
      assert (ρf !! n0 = None) as -> by solve_map_disjoint; eauto.
    + iIntros (?) "H". simpl. smap.
      assert (ρf !! n = None) as -> by solve_map_disjoint; eauto.
    + iIntros (?) "H". simpl. smap. iDestr "H".
      assert (ρf !! j = None) as -> by solve_map_disjoint; eauto.
    + iIntros (?) "H". simpl.
      iDestr "H". rewrite lookup_union_spec lookup_singleton. simpl.
      iDestruct (replacement with "H") as (t) "[H Q]"; first done. simpl.
      iDestr "H". simp.
      iExists (t1,t2), (t2,t1).
      iSplitL "Q".
      * smap. iIntros "H". iSplit; first done.
        iApply "Q". simpl. eauto.
      * smap. iSplit; eauto.
        iIntros "Q". iSplit; eauto 10 with iFrame.
  - admit.
Admitted.