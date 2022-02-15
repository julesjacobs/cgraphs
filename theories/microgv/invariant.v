From diris.microgv Require Export rtypesystem.

(* Can we just do vertex = nat here? *)
Definition linv (ρ : cfg) (v : nat) (in_l : multiset label) : rProp :=
  match ρ !! v with
  | Some (Thread e) => ⌜⌜ in_l ≡ ε ⌝⌝ ∗ rtyped0 e UnitT
  | Some Barrier => ⌜⌜ ∃ t1 t2, in_l ≡ {[ (t1,t2) ]} ⋅ {[ (t2,t1) ]} ⌝⌝
  | None => ⌜⌜ in_l ≡ ε ⌝⌝
  end.

(* Definition linv (ρ : cfg) (v : vertex) (in_l : multiset label) : rProp :=
  match v with
  | VThread k =>
    ⌜⌜ in_l ≡ ε ⌝⌝ ∗
    match ρ !! k with
    | Some (Thread e) => rtyped0 e UnitT
    | _ => emp
    end
  | VBarrier k =>
    ⌜⌜ match ρ !! k with
      | Some Barrier => ∃ t1 t2, in_l ≡ {[ (t1,t2) ]} ⋅ {[ (t2,t1) ]}
      | _ => in_l ≡ ε
      end ⌝⌝
  end%I. *)

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

Lemma full_reachability ρ :
  ginv ρ -> fully_reachable ρ.
Proof.
  unfold fully_reachable.
  intros Hinv.
  destruct Hinv as [g [Hwf Hinv]].
  eapply (cgraph_ind' (λ a b l, waiting ρ a b)); [solve_proper|eauto|].
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
      * eapply (Waiting_reachable _ _ j).
        -- unfold waiting. smap.
          ++ admit.
          ++ destruct (ρ !! j) as [[]|] eqn:F; rewrite ?F.
            ** admit.
            ** unfold expr_waiting. eauto.
            ** admit.
        -- assert (∃ l, out_edges g i !! j = Some l) as [l Hl].
           { admit. }
           destruct (IH1 j l).
           ++ rewrite Hl //.
           ++ unfold waiting. rewrite E.
              admit.
           ++ unfold inactive in H. admit.
           ++ rewrite -HH //.
  - eapply affinely_pure_holds in Q as [Q1 [t1 [t2 Q2]]].
Admitted.
