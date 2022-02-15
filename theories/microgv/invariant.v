From diris.microgv Require Export rtypesystem.

(* Can we just do vertex = nat here? *)
Definition linv (ρ : cfg) (v : nat) (in_l : multiset labelO) : rProp :=
  match ρ !! v with
  | Some (Thread e) => ⌜⌜ in_l ≡ ε ⌝⌝ ∗ rtyped0 e UnitT
  | Some Barrier => ⌜⌜ ∃ t1 t2, in_l ≡ {[ (t1,t2) ]} ⋅ {[ (t2,t1) ]} ⌝⌝
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
      iExists (t1,t2), (t2,t1).
      iSplitL "Q".
      * iIntros "H". iSplit; first done.
        iApply "Q". simpl. eauto.
      * iSplit; eauto.
        iIntros "Q". iSplit; eauto 10 with iFrame.
  - admit.
Admitted.

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
Admitted.

Lemma expr_refs_linv ρ j e x Σ :
  ρ !! j = Some (Thread e) ->
  holds (linv ρ j x) Σ ->
  expr_refs e = dom (gset vertex) Σ.
Proof.
Admitted.

Ltac model := (setoid_rewrite pure_sep_holds || setoid_rewrite exists_holds
  || setoid_rewrite own_holds
  || setoid_rewrite sep_holds).

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
