From diris.microgv Require Export rtypesystem.

(* Can we just do vertex = nat here? *)
Definition linv (ρ : cfg) (v : nat) (in_l : multiset labelO) : rProp :=
  match ρ !! v with
  | Some (Thread e) => ⌜⌜ in_l ≡ ε ⌝⌝ ∗ rtyped0 e UnitT
  | Some Barrier => ⌜⌜ ∃ t1 t2, in_l ≡ {[ (false,(t1,t2)) ]} ⋅ {[ (false,(t2,t1)) ]} ⌝⌝
  | None => ⌜⌜ in_l ≡ ε ⌝⌝
  end.

Global Instance lin_Proper ρ v : Proper ((≡) ==> (≡)) (linv ρ v).
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

Lemma multiset_singleton_mult' {A : ofe} a1 a2 (x : multiset A) :
  {[ a1 ]} ⋅ x ≡ {[ a2 ]} ->
  a1 = a2 ∧ x = ε.
Proof.
Admitted.

Lemma multiset_xsplit_singleton {A : ofe} a1 a2 a3 (x : multiset A) :
  {[ a1 ]} ⋅ x ≡ {[ a2 ]} ⋅ {[ a3 ]} ->
  a1 = a2 ∧ x = {[ a3 ]} ∨ a1 = a3 ∧ x = {[ a2 ]}.
Proof.
  intros H.
  eapply mset_xsplit in H as (?&?&?&?&?&?&?&?).
  eapply multiset_singleton_mult in H as [[]|[]].
Admitted.

Lemma preservation i ρ ρ' :
  step i ρ ρ' -> ginv ρ -> ginv ρ'.
Proof.
  intros H Hinv.
  destruct H as [ρ ρ' ρf D1 D2 i H].
  destruct H.
  - eapply inv_impl; last done.
    iIntros (n x) "H". unfold linv. smap.
    iDestruct "H" as "[? H]". iFrame.
    iDestruct (replacement with "H") as (t) "[H Q]"; first done.
    iApply "Q". iApply pure_preservation; done.
  - eapply inv_impl; last done.
    iIntros (n x) "H". unfold linv. smap; iDestr "H";
    assert (ρf !! n = None) as -> by solve_map_disjoint; eauto.
    destruct v; simpl; iDestr "H"; simp. done.
  - eapply (inv_alloc_lr i0 n j);
    last done; first apply _; first apply _.
    + naive_solver.
    + iIntros (? ? ?) "H". unfold linv. smap.
    + iIntros (?) "H". unfold linv. smap.
      assert (ρf !! n = None) as -> by solve_map_disjoint; eauto.
    + iIntros (?) "H". unfold linv. smap.
      assert (ρf !! j = None) as -> by solve_map_disjoint; eauto.
    + iIntros (?) "H". unfold linv. smap. iDestr "H".
      iDestruct (replacement with "H") as (t) "[H Q]"; first done. simpl.
      iDestr "H". simp.
      iExists (false,(t1,t2)), (false,(t2,t1)).
      iSplitL "Q".
      * iIntros "H". iSplit; first done.
        iApply "Q". simpl. eauto.
      * iSplit; eauto.
        iIntros "Q". iSplit; eauto 10 with iFrame.
  - assert (inv (λ k x,
      if decide (k = i0) then
        ⌜⌜ x ≡ ε ⌝⌝ ∗ ∃ t1 t2, own_out n (true,(t1,t2)) ∗ ∀ e' : expr, rtyped0 e' t2 -∗ rtyped0 (k1 e') UnitT
      else if decide (k = n) then
        ∃ t1 t2, ⌜⌜ x ≡ {[ (true,(t1,t2)) ]} ⋅ {[ (false,(t2,t1)) ]} ⌝⌝ ∗
        vtyped v1 t1
      else if decide (k = j) then
        ⌜⌜ x ≡ ε ⌝⌝ ∗ rtyped0 (k2 (App (Val (BarrierV n)) (Val v2))) UnitT
      else linv ρf k x
        )%I) as Hinv'.
    {
      eapply (inv_exchange i0 n); last done; [solve_proper|solve_proper|..].
      - simp. smap; unfold linv; smap.
      - simp. smap. unfold linv. smap.
        iIntros "[% H]".
        rewrite replacement; last done.
        iDestruct "H" as (t1) "[H1 H2]". simpl.
        iDestruct "H1" as (t2 l) "[H1 H3]".
        iDestruct "H1" as (t1' t2' ?) "H1". simplify_eq.
        iExists _. iFrame. iIntros (x [t1 [t2 ?]]) "".
        eapply multiset_xsplit_singleton in H8 as [[]|[]]; simplify_eq.
        + iExists _. iSplitL "H2".
          * iIntros "H". iSplit; eauto. iExists _,_. iFrame.
          * iExists _,_. iFrame. eauto.
        + iExists _. iSplitL "H2".
          * iIntros "H". iSplit; eauto. iExists _,_. iFrame.
          * iExists _,_. iFrame. eauto.
    } clear Hinv.

    assert (inv (λ k x,
      if decide (k = i0) then
        ⌜⌜ x ≡ ε ⌝⌝ ∗ ∃ t1 t2, own_out n (true,(t1,t2)) ∗ ∀ e' : expr, rtyped0 e' t2 -∗ rtyped0 (k1 e') UnitT
      else if decide (k = n) then
        ∃ t1 t2, ⌜⌜ x ≡ {[ (true,(t1,t2)) ]} ⌝⌝ ∗
        vtyped v2 t2
      else if decide (k = j) then
        ⌜⌜ x ≡ ε ⌝⌝ ∗ rtyped0 (k2 (Val v1)) UnitT
      else linv ρf k x
        )%I) as Hinv''.
    {
      eapply (inv_dealloc j n); last done; [solve_proper|solve_proper|..].
      - simp. smap.
      - simp. smap.
        iIntros "[% H]".
        rewrite replacement; last done.
        iDestruct "H" as (t1) "[H1 H2]". simpl.
        iDestruct "H1" as (t2 l) "[H3 H4]".
        iDestruct "H3" as (t1' t2' ?) "H". simplify_eq.
        iExists _. iFrame. iIntros (?) "H".
        iDestruct "H" as (t1 t2 ?) "H".
        eapply multiset_xsplit_singleton in H8 as [[]|[]]; simplify_eq.
        iSplitL "H H2".
        + iSplit; eauto. iApply "H2". done.
        + iExists _,_. iFrame. eauto.
    } clear Hinv'.

    eapply (inv_dealloc i0 n); last done; [solve_proper|solve_proper|..].
    + simp. smap; unfold linv; smap.
    + simp. smap.
      iIntros "[% H]".
      iDestruct "H" as (t1 t2) "[H1 H2]".
      iExists _. iFrame. iIntros (?) "H".
      iDestruct "H" as (t1' t2' ?) "H".
      eapply multiset_singleton_mult' in H6 as []. simplify_eq.
      unfold linv. smap.
      assert (ρf !! n = None) as -> by solve_map_disjoint.
      iSplit; eauto. iSplit; eauto.
      iApply "H2". simpl. done.
Qed.

Lemma fresh2 (s : gset nat) :
  ∃ x y, x ∉ s ∧ y ∉ s ∧ x ≠ y.
Proof.
  exists (fresh s), (fresh (s ∪ {[ fresh s ]})).
  split; first apply is_fresh.
  pose proof (is_fresh (s ∪ {[ fresh s ]})).
  set_solver.
Qed.

Lemma cfg_fresh2 (ρ : cfg) :
  ∃ j1 j2, ρ !! j1 = None ∧ ρ !! j2 = None ∧ j1 ≠ j2.
Proof.
  destruct (fresh2 (dom (gset nat) ρ)) as (j1 & j2 & H1 & H2 & H3).
  exists j1,j2. split_and!; last done;
  apply not_elem_of_dom; done.
Qed.

Lemma linv_out_Some i j Σ l ρ x :
  holds (linv ρ j x) Σ ->
  Σ !! i ≡ Some l ->
  ∃ e, ρ !! j = Some (Thread e).
Proof.
  unfold linv.
  destruct (ρ !! j) as [[]|]; eauto.
  - rewrite affinely_pure_holds.
    intros [H ?] Q.
    specialize (H i). rewrite H lookup_empty in Q. simplify_eq.
  - rewrite affinely_pure_holds.
    intros [H ?] Q.
    specialize (H i). rewrite H lookup_empty in Q. simplify_eq.
Qed.

Definition own_dom A : rProp := ∃ Σ, ⌜⌜ A = dom (gset vertex) Σ ⌝⌝ ∗ own Σ.

Lemma own_dom_empty : own_dom ∅ ⊣⊢ emp.
Proof.
  iSplit; unfold own_dom; iIntros "H".
  - iDestruct "H" as (? H) "H".
    symmetry in H. apply dom_empty_iff_L in H as ->.
    by iApply own_empty.
  - iExists ∅. rewrite own_empty dom_empty_L //.
Qed.

Lemma own_dom_singleton k v : own {[ k := v ]} ⊢ own_dom {[ k ]}.
Proof.
  iIntros "H". iExists {[ k := v ]}.
  rewrite dom_singleton_L. iFrame. done.
Qed.

Lemma own_dom_union A B : own_dom A ∗ own_dom B ⊢ own_dom (A ∪ B).
Proof.
  iIntros "[H1 H2]".
  iDestruct "H1" as (Σ1 H1) "H1".
  iDestruct "H2" as (Σ2 H2) "H2". subst.
  iExists (Σ1 ∪ Σ2). rewrite dom_union_L. iSplit; eauto.
  iApply own_union. iFrame.
Qed.

Lemma own_dom_fin_gset `{Countable A} n (g : fin n -> A) (f : A -> gset vertex) :
  ([∗ set] p ∈ fin_gset n g, own_dom (f p)) -∗ own_dom (big_union (fin_gset n (f ∘ g))).
Proof.
  induction n.
  - rewrite !fin_gset_0 big_union_empty big_sepS_empty own_dom_empty //.
  - rewrite !fin_gset_S big_union_singleton_union.
    destruct (decide (g 0%fin ∈ fin_gset n (λ i : fin n, g (FS i)))).
    + rewrite subseteq_union_1_L; last rewrite singleton_subseteq_l //.
      rewrite subseteq_union_1_L; first apply IHn.
      eapply elem_of_fin_gset in e.
      intros ??.
      eapply elem_of_big_union.
      destruct e. simpl in *.
      rewrite -H1 in H0.
      eexists. split; last done.
      eapply elem_of_fin_gset. eauto.
    + rewrite big_sepS_insert //.
      iIntros "[H1 H2]".
      iDestruct (IHn with "H2") as "H2".
      iApply own_dom_union. iFrame.
Qed.

Lemma own_dom_fin_union n f :
  ([∗ set] p ∈ all_fin n, own_dom (f p)) ⊢ own_dom (fin_union n f).
Proof.
  iApply own_dom_fin_gset.
Qed.

Lemma own_dom_all {A} (f : A -> gset vertex) :
  (∀ i, own_dom (f i)) ⊢ ⌜ ∀ i j, f i = f j ⌝.
Proof.
  apply entails_holds.
  intros Σ H.
  rewrite pure_holds. intros.
  rewrite ->forall_holds in H.
  assert (∀ i, f i = dom (gset _) Σ).
  { intros k. specialize (H k).
    eapply exists_holds in H as [].
    eapply pure_sep_holds in H as [].
    eapply own_holds in H0.
    rewrite -H0 H //. }
  rewrite !H0 //.
Qed.

Lemma own_dom_and A B :
  own_dom A ∧ own_dom B ⊢ ⌜ A = B ⌝.
Proof.
  iIntros "H".
  iAssert (∀ c:bool, own_dom (if c then A else B))%I with "[H]" as "H".
  { iIntros ([]).
    - by iDestruct "H" as "[H _]".
    - by iDestruct "H" as "[_ H]". }
  iDestruct (own_dom_all with "H") as %Q.
  specialize (Q true false). simpl in *. eauto.
Qed.

Lemma fin_union_same `{Countable A} n (s : gset A) :
  fin_union (S n) (λ i, s) = s.
Proof.
  induction n.
  - rewrite fin_union_S fin_union_0 right_id_L //.
  - rewrite fin_union_S IHn union_idemp_L //.
Qed.

Lemma rtyped_refs Γ e t :
  rtyped Γ e t ⊢ own_dom (expr_refs e)
with val_typed_refs v t :
  vtyped v t ⊢ own_dom (val_refs v).
Proof.
  - iIntros "H". destruct e; simpl; repeat (iDestruct "H" as (?) "H"); try destruct l;
    rewrite ?val_typed_refs ?rtyped_refs ?own_dom_empty ?own_dom_union; eauto.
    iDestruct "H" as "[H1 H]". iApply own_dom_union; iFrame.
    case_decide; subst. { rewrite fin_union_0 own_dom_empty //. }
    setoid_rewrite rtyped_refs.
    iDestruct (own_dom_all with "H") as %Q.
    destruct n; simplify_eq.
    assert (expr_refs ∘ e0 = λ i, expr_refs (e0 0%fin)) as ->.
    { apply functional_extensionality. intros. eapply Q. }
    rewrite fin_union_same. iApply "H".
  - iIntros "H". destruct v; simpl; rewrite ?own_dom_empty; eauto;
    repeat (iDestruct "H" as (?) "H"); try destruct l;
    rewrite ?val_typed_refs ?rtyped_refs ?own_dom_union; eauto.
    by iApply own_dom_singleton.
Qed.

Lemma expr_refs_linv ρ j e x Σ :
  ρ !! j = Some (Thread e) ->
  holds (linv ρ j x) Σ ->
  expr_refs e = dom (gset vertex) Σ.
Proof.
  intros H1 H2.
  unfold linv in *.
  rewrite H1 in H2.
  eapply pure_sep_holds in H2 as [_ H2].
  rewrite -rtyped_rtyped0 in H2.
  eapply holds_entails in H2; last eapply rtyped_refs.
  unfold own_dom in *.
  eapply exists_holds in H2 as [Σ' H2].
  eapply pure_sep_holds in H2 as [-> H2].
  eapply own_holds in H2. rewrite H2 //.
Qed.

Lemma full_reachability ρ :
  ginv ρ -> fully_reachable ρ.
Proof.
  unfold fully_reachable.
  intros Hinv.
  destruct Hinv as [g [Hwf Hinv]].
  eapply (cgraph_ind' (λ a b l, waiting ρ a b)); eauto; first solve_proper.
  intros i IH1 IH2.
  classical_right.
  rewrite /inactive in H.
  pose proof (Hinv i) as Q.
  unfold linv in Q.
  destruct (ρ !! i) eqn:E; simplify_eq. clear H.
  destruct o.
  - apply pure_sep_holds in Q as [Q1 Q2]. assert (Q2' := Q2).
    eapply holds_entails in Q2; last apply pure_progress.
    assert (ρ = {[ i := Thread e ]} ∪ delete i ρ) as HH.
    { apply map_eq. intro. smap. } rewrite HH.
    apply pure_holds in Q2 as [[v ->]|Q].
    + constructor. exists (∅ ∪ delete i ρ).
      econstructor; last constructor; last solve_map_disjoint.
      intro x. smap. destruct (_!!x); done.
    + destruct Q as (k & e0 & [Hk ->] & [[e0' Q] | [[v ->] | [v [j ->]]]]).
      * constructor. eexists ({[ i := Thread (k e0') ]} ∪ delete i ρ).
        constructor; [intro j; smap; by destruct (_!!j)..|].
        constructor; eauto.
      * constructor.
        destruct (cfg_fresh2 ρ) as (j & n & Hj & Hn & Hjn).
        exists ({[ i := Thread (k $ Val $ BarrierV n);
                   j := Thread (App (Val v) (Val $ BarrierV n));
                   n := Barrier ]} ∪ delete i ρ).
        constructor; [intro x; smap; by destruct (_!!x)..|].
        constructor; eauto; intros ->; simplify_eq.
      * (* Thread is now trying to sync with a barrier *)
        (* It is therefore waiting and reachable *)
        rewrite -HH.
        assert (∃ l, out_edges g i !! j ≡ Some l) as [l Hl].
        {
          (* rewrite replacement in Q2'; last done. *)
          (* simpl in Q2'. *)
          assert (holds ((∃ l, own_out j l) ∗ True) (out_edges g i)) as QQ.
          {
            eapply holds_entails; first exact Q2'.
            iIntros "H".
            rewrite replacement; last done.
            iDestruct "H" as (t) "[H1 H2]".
            simpl.
            iDestruct "H1" as (t2 l) "[H11 H12]".
            iDestruct "H11" as (t1 t0 ?) "H11". simplify_eq.
            iSplitL "H11"; eauto.
          }
          eapply sep_holds in QQ as (Σ1 & Σ2 & H12 & Hdisj & Hout & HP).
          eapply exists_holds in Hout as [l Hout].
          unfold own_out in Hout.
          eapply own_holds in Hout.
          exists l. rewrite H12.
          rewrite -Hout.
          smap.
        }
        assert (ρ !! j = Some Barrier) as F.
        {
          eapply out_edges_in_labels in Hl as [x Hx].
          specialize (Hinv j).
          rewrite Hx in Hinv.
          eapply pure_holds.
          eapply holds_entails; first exact Hinv.
          iIntros "H".
          unfold linv.
          destruct (ρ !! j) as [[]|]; eauto.
          - iDestruct "H" as (?) "H".
            exfalso. eapply multiset_empty_neq_singleton.
            eapply multiset_empty_mult in H as []; eauto.
          - iDestruct "H" as "%".
            exfalso. eapply multiset_empty_neq_singleton.
            eapply multiset_empty_mult in H as []; eauto.
        }
        assert (waiting ρ i j). {
          unfold waiting. rewrite E F.
          unfold expr_waiting; eauto.
        }
        assert (reachable ρ j). {
          edestruct (IH1 j); eauto.
          unfold inactive in *. simplify_eq.
        }
        eauto using reachable.
  - eapply affinely_pure_holds in Q as [Q1 [t1 [t2 Q2]]].
    (* Need to check whether both threads are trying to sync. *)
    (* If so, then can_step *)
    (* Otherwise, use IH *)
    apply in_labels_out_edges2 in Q2 as (j1 & j2 & Hj12 & Hj1 & Hj2).

    edestruct (linv_out_Some i j1) as [e1 He1]; eauto.
    edestruct (linv_out_Some i j2) as [e2 He2]; eauto.

    destruct (classic (waiting ρ j1 i)) as [W1|W1]; last first.
    {
      edestruct IH2; [|done|..]; eauto.
      - unfold inactive in H. simplify_eq.
      - assert (waiting ρ i j1); eauto using reachable.
        unfold waiting in *.
        rewrite He1 E in W1.
        rewrite E He1. split; eauto.
        erewrite expr_refs_linv; eauto.
        apply elem_of_dom. rewrite Hj1. done.
    }
    destruct (classic (waiting ρ j2 i)) as [W2|W2]; last first.
    {
      edestruct IH2; [|done|..]; eauto.
      - unfold inactive in H. simplify_eq.
      - assert (waiting ρ i j2); eauto using reachable.
        unfold waiting in *.
        rewrite He2 E in W2.
        rewrite E He2. split; eauto.
        erewrite expr_refs_linv; eauto.
        apply elem_of_dom. rewrite Hj2. done.
    }
    constructor.
    unfold waiting in W1,W2.
    rewrite He1 E in W1.
    rewrite He2 E in W2.
    assert (ρ = {[ j1 := Thread e1; j2 := Thread e2; i := Barrier ]} ∪ (delete j2 $ delete j1 $ delete i ρ)) as HH.
    { apply map_eq. intro. smap. }
    destruct W2 as (k2 & v2 & Hk2 & ->).
    destruct W1 as (k1 & v1 & Hk1 & ->).
    unfold can_step.
    exists ({[ j1 := Thread (k1 $ Val v2); j2 := Thread (k2 $ Val v1) ]} ∪ (delete j2 $ delete j1 $ delete i ρ)).
    rewrite {1}HH.
    constructor.
    { intro x. smap. destruct (_!!x); done. }
    { intro x. smap. destruct (_!!x); done. }
    constructor; eauto; intros ->; simplify_eq.
Qed.
