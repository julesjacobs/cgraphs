From iris.proofmode Require Import tactics.
Require Export diris.uforests.
From diris Require Export util.
From stdpp Require Export gmap.
Require Export diris.multiset.
From stdpp Require Import fin_maps.

Ltac sdec := repeat case_decide; simplify_eq.

(* Definition uforest V := gset (V * V). *)
Notation cgraph V L := (gmap V (gmap V L)).

Section cgraph.
  Context {V : Type}.
  Context `{Countable V}.
  Context {L : ofe}.

  Definition out_edges (g : cgraph V L) (v : V) : gmap V L :=
    match g !! v with
    | Some e => e
    | None => ∅
    end.

  Definition ms_insert (v v' : V) (ev' : gmap V L) (ins : multiset L) : multiset L :=
    from_option singleton ε (ev' !! v) ⋅ ins.

  Definition in_labels (g : cgraph V L) (v : V) : multiset L :=
    map_fold (ms_insert v) ε g.

  Definition edge (g : cgraph V L) (v1 v2 : V) := is_Some (out_edges g v1 !! v2).

  Definition cgraph_wf (g : cgraph V L) : Prop. Admitted. (* no_short_loops g ∧ acyclic g. *)

  Definition uconn (g : cgraph V L) := rtsc (edge g).


  (* Definition swap {A B} : (A*B -> B*A) := λ '(x,y), (y,x).
  Definition make_undirected (g : gset (V*V)) : gset (V*V) :=
    g ∪ (set_map swap g).
  Definition dedges (g : cgraph V L) : gset (V*V) :=
    dom (gset _) (gmap_curry g).
  Definition to_uforest (g : cgraph V L) : uforest V :=
    make_undirected $ dedges g.
  Definition acyclic (g : cgraph V L) := is_uforest (to_uforest g).


  Definition no_short_loops (g : cgraph V L) :=
    ∀ v1 v2, ¬ (edge g v1 v2 ∧ edge g v2 v1). *)

  Section general.


    Lemma in_labels_insert g i x v :
      g !! i = None ->
      in_labels (<[i:=x]> g) v ≡ from_option singleton ε (x !! v) ⋅ in_labels g v.
    Proof.
      intros Hi.
      unfold in_labels at 1.
      erewrite map_fold_insert with (R := (≡));
      eauto; first apply _; first solve_proper.
      intros. unfold ms_insert.
      destruct (z1 !! v) eqn:E;
      destruct (z2 !! v) eqn:F; simpl; eauto.
      rewrite assoc.
      rewrite (comm (⋅) {[ o ]}).
      rewrite assoc. done.
    Qed.

    Lemma in_labels_delete g i v y :
      g !! i = Some y ->
      from_option singleton ε (y !! v) ⋅ in_labels (delete i g) v ≡ in_labels g v.
    Proof.
      intro.
      pose proof (in_labels_insert (delete i g) i y v) as HH.
      rewrite insert_delete in HH.
      rewrite insert_id in HH; eauto.
      rewrite HH; last by apply lookup_delete.
      done.
    Qed.

    Lemma in_labels_update g i x y v :
      g !! i = Some y ->
      from_option singleton ε (y !! v) ⋅ in_labels (<[i:=x]> g) v ≡
      from_option singleton ε (x !! v) ⋅ in_labels g v.
    Proof.
      intro.
      assert (<[i:=x]> g = <[i:=x]> $ delete i g) as -> by by rewrite insert_delete.
      rewrite in_labels_insert; last by apply lookup_delete.
      rewrite comm. rewrite -assoc.
      rewrite (comm (⋅) (in_labels _ _)).
      rewrite in_labels_delete; eauto.
    Qed.

    (* Lemma in_labels_dependence g g' v2 :
      (∀ v1, out_edges g v1 !! v2 = out_edges g' v1 !! v2) ->
      in_labels g v2 = in_labels g' v2.
    Proof.
    Admitted. *)

    Lemma out_edges_in_labels g v1 v2 l :
      out_edges g v1 !! v2 = Some l ->
      ∃ x, in_labels g v2 ≡ {[ l ]} ⋅ x.
    Proof.
      revert v1 v2 l.
      induction g using map_ind; intros.
      - rewrite lookup_empty in H0. simplify_eq.
      - unfold out_edges in H1. rewrite lookup_insert_spec in H1.
        case_decide; simplify_eq.
        + exists (in_labels m v2).
          rewrite in_labels_insert; eauto.
          rewrite H1. done.
        + destruct (m !! v1) eqn:E; simplify_eq.
          destruct (IHg v1 v2 l).
          { unfold out_edges. rewrite E. done. }
          setoid_rewrite in_labels_insert; eauto.
          setoid_rewrite H3.
          exists (from_option singleton ε (x !! v2) ⋅ x0).
          rewrite !assoc.
          rewrite (comm (⋅) _ {[ l ]}).
          done.
    Qed.

    Lemma multiset_empty_mult {A : ofe} (x y : multiset A) :
      x ⋅ y ≡ ε -> x = ε ∧ y = ε.
    Proof.
    Admitted.

    Lemma multiset_empty_neq_singleton {A : ofe} {a : A} :
      {[ a ]} ≠ ε.
    Proof.
    Admitted.

    Lemma no_in_labels_no_out_edge g v1 v2 :
      in_labels g v2 ≡ ε ->
      out_edges g v1 !! v2 = None.
    Proof.
      destruct (out_edges g v1 !! v2) eqn:E; eauto.
      eapply out_edges_in_labels in E as []. rewrite H0. intros HH.
      eapply multiset_empty_mult in HH.
      destruct HH as [H1%multiset_empty_neq_singleton H2]. done.
    Qed.

    Lemma not_rtsc `{R : A -> A -> Prop} x :
      (∀ y, ¬ R x y ∧ ¬ R y x) ->
      (∀ y, rtsc R x y -> x = y).
    Proof.
      intros Hy y Hr.
      induction Hr; eauto. destruct H0; naive_solver.
    Qed.

    Lemma no_edges_no_uconn g v v' :
      out_edges g v = ∅ ->
      in_labels g v ≡ ε ->
      uconn g v' v -> v = v'.
    Proof.
      intros Hout Hin Hconn.
      eapply not_rtsc; last done.
      intros y. unfold edge. split; intros [].
      - rewrite Hout in H0. rewrite lookup_empty in H0. simplify_eq.
      - eapply no_in_labels_no_out_edge in Hin. erewrite H0 in Hin. simplify_eq.
    Qed.

    Lemma some_edge (g : cgraph V L) (v1 v2 : V) (l : L) :
      out_edges g v1 !! v2 = Some l -> edge g v1 v2.
    Proof.
      unfold edge. intros ->. eauto.
    Qed.



    Lemma not_uconn_out_disjoint g v1 v2 :
      ¬ uconn g v1 v2 -> out_edges g v1 ##ₘ out_edges g v2.
    Proof.
      intros HH v.
      destruct (out_edges g v1 !! v) eqn:E;
      destruct (out_edges g v2 !! v) eqn:F; simpl; eauto.
      assert (edge g v1 v); eauto using some_edge.
      assert (edge g v2 v); eauto using some_edge.
      apply HH.
      eapply rtc_transitive; eapply rtc_once; [left|right]; eauto.
    Qed.
  End general.

  Section empty_cgraph.
    Lemma out_edges_empty v :
      out_edges ∅ v = ∅.
    Proof.
      unfold out_edges. rewrite lookup_empty //.
    Qed.

    Lemma in_labels_empty v :
      in_labels ∅ v ≡ ε.
    Proof.
      unfold in_labels. rewrite map_fold_empty. done.
    Qed.

    Lemma empty_wf :
      cgraph_wf ∅.
    Proof.
    Admitted.
  End empty_cgraph.

  Section insert_edge.
    (* This function is only supposed to be called if there is not already an edge
       between v1 and v2. In fact, it's only supposed to be called if v1 and v2
       are complete disconnected. *)
    Definition insert_edge (g : cgraph V L) (v1 v2 : V) (l : L) :=
      <[ v1 := <[ v2 := l ]> $ out_edges g v1 ]> g.

    Lemma out_edges_insert (g : cgraph V L) (v1 v2 : V) e :
      out_edges (<[ v1 := e ]> g) v2 =
        if decide (v1 = v2) then e
        else out_edges g v2.
    Proof.
      rewrite /out_edges. rewrite lookup_insert_spec.
      repeat case_decide; simplify_eq; done.
    Qed.

    Lemma out_edges_insert_edge (g : cgraph V L) (v1 v2 v3 : V) (l : L) :
      out_edges (insert_edge g v1 v2 l) v3 =
        if decide (v1 = v3) then <[ v2 := l ]> $ out_edges g v3
        else out_edges g v3.
    Proof.
      unfold insert_edge. rewrite out_edges_insert.
      repeat case_decide; simplify_eq; done.
    Qed.

    Lemma in_labels_insert_edge (g : cgraph V L) (v1 v2 v3 : V) (l : L) :
      ¬ edge g v1 v2 ->
      in_labels (insert_edge g v1 v2 l) v3 ≡
        if decide (v2 = v3) then {[ l ]} ⋅ in_labels g v3
        else in_labels g v3.
    Proof.
      intros Hnotedge.
      unfold insert_edge.
      destruct (g !! v1) eqn:E.
      - assert (g !! v1 = Some g0) as HH; eauto.
        pose proof (in_labels_update g v1 (<[v2:=l]> (out_edges g v1)) g0 v3 HH) as H0.
        rewrite lookup_insert_spec in H0.
        destruct (g0 !! v3) eqn:F; simpl in *.
        + case_decide; simplify_eq; simpl in *.
          * exfalso. apply Hnotedge.
            unfold edge. unfold out_edges.
            rewrite E. rewrite F. eauto.
          * unfold out_edges in H0 at 2.
            rewrite E in H0.
            rewrite F in H0. simpl in *.
            apply cancelable in H0; eauto; first apply _; done.
        + rewrite ->left_id in H0. 2: { intro. simpl. rewrite left_id. done. }
          rewrite H0. case_decide; simpl; eauto. unfold out_edges.
          rewrite HH. rewrite F. simpl. rewrite left_id. done.
      - rewrite in_labels_insert; eauto.
        rewrite lookup_insert_spec.
        case_decide; simplify_eq; try done.
        unfold out_edges.
        rewrite E. rewrite lookup_empty.
        simpl. rewrite left_id. done.
    Qed.

    Lemma insert_edge_wf g v1 v2 l :
      ¬ uconn g v1 v2 ->
      cgraph_wf g ->
      cgraph_wf (insert_edge g v1 v2 l).
    Proof.
    Admitted.
  End insert_edge.


  Section delete_edge.
    Definition delete_edge (g : cgraph V L) (v1 v2 : V) :=
      <[ v1 := delete v2 (out_edges g v1) ]> g.

    Lemma out_edges_delete_edge (g : cgraph V L) (v1 v2 v3 : V) :
      out_edges (delete_edge g v1 v2) v3 =
        if decide (v1 = v3) then delete v2 (out_edges g v3)
        else out_edges g v3.
    Proof.
      unfold delete_edge. rewrite out_edges_insert.
      repeat case_decide; simplify_eq; done.
    Qed.

    Lemma in_labels_delete_edge_eq (g : cgraph V L) (v1 v2 : V) (l : L) (x : multiset L) :
      out_edges g v1 !! v2 = Some l ->
      in_labels g v2 ≡ {[ l ]} ⋅ x ->
      in_labels (delete_edge g v1 v2) v2 ≡ x.
    Proof.
      intros H1 H2.
      unfold delete_edge.
      destruct (g !! v1) eqn:E; last first.
      { unfold out_edges in H1. rewrite E lookup_empty in H1. simplify_eq. }
      pose proof (in_labels_update g v1 (delete v2 (out_edges g v1)) g0 v2 E) as H0.
      destruct (g0 !! v2) eqn:F; simpl in *.
      - rewrite lookup_delete in H0.
        simpl in *.
        rewrite ->H2 in H0.
        unfold out_edges in H1.
        rewrite E in H1. rewrite F in H1. simplify_eq.
        revert H0. rewrite left_id. intros H0.
        apply cancelable in H0; eauto; first apply _; done.
      - unfold out_edges in H1. rewrite E F in H1. simplify_eq.
    Qed.

    Lemma in_labels_delete_edge_neq (g : cgraph V L) (v1 v2 v3 : V) :
      v2 ≠ v3 ->
      in_labels (delete_edge g v1 v2) v3 ≡ in_labels g v3.
    Proof.
      intros Hneq.
      unfold delete_edge.
      destruct (g !! v1) eqn:E.
      - pose proof (in_labels_update g v1 (delete v2 (out_edges g v1)) g0 v3 E) as H0.
        destruct (g0 !! v3) eqn:F.
        + simpl in *.
          rewrite lookup_delete_spec in H0.
          unfold out_edges in H0 at 2.
          rewrite E in H0.
          rewrite F in H0.
          case_decide; simplify_eq.
          simpl in *. apply cancelable in H0; eauto; first apply _; done.
        + simpl in *. rewrite ->left_id in H0.
          2: { intro. simpl. rewrite left_id. done. }
          rewrite H0.
          rewrite lookup_delete_spec.
          unfold out_edges. rewrite E.
          rewrite F. case_decide; simplify_eq; simpl.
          rewrite left_id. done.
      - rewrite in_labels_insert; eauto.
        rewrite lookup_delete_spec.
        unfold out_edges.
        rewrite E. rewrite lookup_empty.
        case_decide; simpl; rewrite left_id //.
    Qed.

    Lemma delete_edge_wf g v1 v2 :
      cgraph_wf g ->
      cgraph_wf (delete_edge g v1 v2).
    Proof.
    Admitted.

    Lemma delete_edge_uconn g v1 v2 :
      cgraph_wf g ->
      edge g v1 v2 ->
      ¬ uconn (delete_edge g v1 v2) v1 v2.
    Proof.
    Admitted.

    Lemma edge_delete_edge g v1 v2 w1 w2 :
      v1 ≠ w1 ∨ v2 ≠ w2 ->
      edge g w1 w2 ->
      edge (delete_edge g v1 v2) w1 w2.
    Proof.
      intros.
      unfold edge.
      rewrite out_edges_delete_edge.
      case_decide; simplify_eq; eauto.
      rewrite lookup_delete_spec.
      case_decide; simplify_eq; eauto.
      naive_solver.
    Qed.

    Lemma edge_delete_edge' g v1 v2 w1 w2 :
      edge g w1 w2 ->
      edge (delete_edge g v1 v2) w1 w2 ∨ (v1 = w1 ∧ v2 = w2).
    Proof.
      intros.
      pose proof (edge_delete_edge g v1 v2 w1 w2).
      destruct (decide (v1 = w1));
      destruct (decide (v2 = w2));
      naive_solver.
    Qed.

    Lemma no_self_edge g v1 v2 :
      cgraph_wf g ->
      edge g v1 v2 -> v1 ≠ v2.
    Proof.
      intros H1 H2 ->.
      eapply delete_edge_uconn; eauto. reflexivity.
    Qed.

    Lemma no_self_edge' g v1 v2 :
      cgraph_wf g ->
      sc (edge g) v1 v2 -> v1 ≠ v2.
    Proof.
      intros H1 [] ->; eapply no_self_edge; eauto.
    Qed.

    Lemma no_self_edge'' g v :
      cgraph_wf g ->
      out_edges g v !! v = None.
    Proof.
      intros.
      destruct (_!!_) eqn:E; eauto.
      exfalso.
      eapply no_self_edge; eauto using some_edge.
    Qed.

    Lemma no_triangle g v1 v2 v3 :
      cgraph_wf g ->
      sc (edge g) v1 v2 ->
      sc (edge g) v2 v3 ->
      sc (edge g) v3 v1 ->
      False.
    Proof.
      intros Hwf H1 H2 H3.
      assert (v1 ≠ v2); eauto using no_self_edge'.
      assert (v2 ≠ v3); eauto using no_self_edge'.
      assert (v3 ≠ v1); eauto using no_self_edge'.
      destruct H1,H2,H3; eapply delete_edge_uconn; eauto;
      eapply rtc_transitive; eapply rtc_once;
      try (solve [left; eapply edge_delete_edge; eauto] ||
           solve [right; eapply edge_delete_edge; eauto]).
      - left. eapply edge_delete_edge; eauto.
      - left. eapply edge_delete_edge.
        + right. intro. eapply H4. symmetry. done.
        + eauto.
      - right. eapply edge_delete_edge; eauto.
    Qed.

    Lemma edge_out_disjoint g v1 v2 :
      cgraph_wf g -> edge g v1 v2 -> out_edges g v1 ##ₘ out_edges g v2.
    Proof.
      intros Hwf Hv12 v.
      destruct (out_edges g v1 !! v) eqn:E;
      destruct (out_edges g v2 !! v) eqn:F; simpl; eauto.
      eapply no_triangle; eauto.
      - left. eauto.
      - left. unfold edge. erewrite F. eauto.
      - right. unfold edge. rewrite E. eauto.
    Qed.
  End delete_edge.


  Section update_edge.
    Definition update_edge g v1 v2 l' :=
      insert_edge (delete_edge g v1 v2) v1 v2 l'.

    Lemma update_edge_out_edges g v1 v2 l' v :
      out_edges (update_edge g v1 v2 l') v =
        if decide (v = v1) then <[ v2 := l' ]> (out_edges g v)
        else out_edges g v.
    Proof.
      unfold update_edge.
      rewrite out_edges_insert_edge.
      rewrite out_edges_delete_edge.
      repeat case_decide; simplify_eq; eauto.
      apply map_eq. intros v.
      rewrite insert_delete //.
    Qed.

    Lemma update_in_labels_eq g v1 v2 l l' x :
      out_edges g v1 !! v2 = Some l ->
      in_labels g v2 ≡ {[ l ]} ⋅ x ->
      in_labels (update_edge g v1 v2 l') v2 ≡ {[ l' ]} ⋅ x.
    Proof.
      intros H1 H2.
      rewrite /update_edge in_labels_insert_edge.
      - case_decide; simplify_eq.
        rewrite in_labels_delete_edge_eq;eauto.
      - unfold edge. rewrite out_edges_delete_edge.
        case_decide; simplify_eq. rewrite lookup_delete. done.
    Qed.

    Lemma update_in_labels_neq g v v1 v2 l' :
      v ≠ v2 ->
      in_labels (update_edge g v1 v2 l') v ≡ in_labels g v.
    Proof.
      intros H1.
      rewrite /update_edge in_labels_insert_edge.
      - case_decide; simplify_eq. rewrite in_labels_delete_edge_neq; eauto.
      - unfold edge. rewrite out_edges_delete_edge.
        case_decide; simplify_eq. rewrite lookup_delete. done.
    Qed.

    Lemma update_edge_wf g v1 v2 l' :
      cgraph_wf g ->
      edge g v1 v2 ->
      cgraph_wf (update_edge g v1 v2 l').
    Proof.
      intros H1 H2.
      unfold update_edge.
      apply insert_edge_wf.
      - apply delete_edge_uconn; eauto.
      - eapply delete_edge_wf; eauto.
    Qed.
  End update_edge.

  Section move_edge.
    (* Move an edge v1 --[l]--> v3 to be v2 --[l]--> v *)
    (* This is only allowed if there is also an edge between v1 and v2. *)
    Definition move_edge g v1 v2 v3 :=
      match out_edges g v1 !! v3 with
      | Some l => insert_edge (delete_edge g v1 v3) v2 v3 l
      | None => g
      end.

    Lemma move_edge_out_edges g v1 v2 v3 v l :
      out_edges g v1 !! v3 = Some l ->
      out_edges (move_edge g v1 v2 v3) v =
        if decide (v = v2) then <[ v3 := l ]> $ out_edges g v
        else if decide (v = v1) then delete v3 $ out_edges g v
        else out_edges g v.
    Proof.
      intros H1.
      unfold move_edge. rewrite H1.
      rewrite out_edges_insert_edge.
      rewrite out_edges_delete_edge.
      repeat case_decide; simplify_eq; eauto; apply map_eq; intro;
      rewrite ?lookup_union ?lookup_insert_spec ?lookup_delete_spec ?lookup_empty;
      repeat case_decide; simplify_eq; eauto.
    Qed.

    Lemma move_edge_in_labels g v1 v2 v3 v :
      cgraph_wf g ->
      sc (edge g) v1 v2 ->
      in_labels (move_edge g v1 v2 v3) v ≡ in_labels g v.
    Proof.
      intros Hwf Hv12.
      unfold move_edge.
      destruct (_!!_) eqn:E; eauto.
      rewrite in_labels_insert_edge.
      - case_decide; simplify_eq.
        + destruct (out_edges_in_labels _ _ _ _ E).
          rewrite in_labels_delete_edge_eq; eauto.
          by symmetry.
        + rewrite in_labels_delete_edge_neq; eauto.
      - unfold edge.
        assert (v1 ≠ v2); eauto using no_self_edge'.
        rewrite out_edges_delete_edge.
        case_decide; simplify_eq.
        intro HH.
        eapply no_triangle; eauto.
        + left; eauto.
        + right. unfold edge. erewrite E. eauto.
    Qed.

    Lemma move_edge_in_labels' g v1 v2 v3 v :
      cgraph_wf g ->
      ¬ uconn g v1 v2 ->
      in_labels (move_edge g v1 v2 v3) v ≡ in_labels g v.
    Proof.
      intros Hwf Hv12.
      unfold move_edge.
      destruct (_!!_) eqn:E; eauto.
      rewrite in_labels_insert_edge.
      - case_decide; simplify_eq.
        + destruct (out_edges_in_labels _ _ _ _ E).
          rewrite in_labels_delete_edge_eq; eauto.
          by symmetry.
        + rewrite in_labels_delete_edge_neq; eauto.
      - unfold edge.
        assert (v1 ≠ v2). { intros ->. apply Hv12. reflexivity. }
        rewrite out_edges_delete_edge.
        case_decide; simplify_eq.
        intros [].
        assert (edge g v1 v3); eauto using some_edge.
        assert (edge g v2 v3); eauto using some_edge.
        apply Hv12.
        eapply rtc_transitive; eapply rtc_once;[left|right]; eauto.
    Qed.

    Lemma move_edge_wf g v1 v2 v3 :
      v2 ≠ v3 ->
      cgraph_wf g ->
      sc (edge g) v1 v2 ->
      cgraph_wf (move_edge g v1 v2 v3).
    Proof.
      intros Hneq Hwf Hv12.
      unfold move_edge.
      destruct (_!!_) eqn:E; eauto.
      apply insert_edge_wf; eauto using delete_edge_wf.
      intro Hconn.
      eapply (delete_edge_uconn g v1 v3); eauto.
      - unfold edge. rewrite E. eauto.
      - unfold uconn in *.
        assert (sc (edge (delete_edge g v1 v3)) v1 v2). {
          destruct Hv12.
          - left. unfold edge. rewrite out_edges_delete_edge.
            case_decide; simplify_eq.
            rewrite lookup_delete_ne; eauto.
          - right. unfold edge. rewrite out_edges_delete_edge.
            case_decide; simplify_eq; eauto.
            exfalso. eapply no_self_edge; eauto.
        }
        eapply transitivity; last done.
        econstructor; first done.
        econstructor.
    Qed.

    Lemma edge_delete_edge'' g v1 v2 w1 w2 :
      edge (delete_edge g w1 w2) v1 v2 -> edge g v1 v2.
    Proof.
      rewrite /delete_edge /edge /out_edges.
      destruct (g !! w1) eqn:F; simpl; rewrite lookup_insert_spec; repeat case_decide;
      rewrite ?lookup_delete_spec; repeat case_decide; simplify_eq;
      try destruct (g !! v1) eqn:E; simpl; rewrite ?lookup_empty; eauto; try intros [];
      simplify_eq. rewrite H0. eauto.
    Qed.

    Lemma delete_edge_preserves_not_uconn g v1 v2 w1 w2 :
      uconn (delete_edge g w1 w2) v1 v2 -> uconn g v1 v2.
    Proof.
      intros HH. induction HH; try reflexivity.
      eapply rtc_transitive; eauto. eapply rtc_once.
      destruct H0; [left|right]; eauto using edge_delete_edge''.
    Qed.

    Lemma move_edge_wf' g v1 v2 v3 :
      v2 ≠ v3 ->
      cgraph_wf g ->
      ¬ uconn g v1 v2 ->
      cgraph_wf (move_edge g v1 v2 v3).
    Proof.
      intros Hneq Hwf Hv12.
      unfold move_edge.
      destruct (_!!_) eqn:E; eauto.
      apply insert_edge_wf; eauto using delete_edge_wf.
      assert (¬ uconn g v3 v2).
      { intro. apply Hv12.
        eapply rtc_transitive; eauto.
        eapply rtc_once. left. eauto using some_edge. }
      intro. apply delete_edge_preserves_not_uconn in H1.
      apply H0. symmetry. done.
    Qed.

    Definition cgraph_equiv g1 g2 :=
      ∀ v, out_edges g1 v = out_edges g2 v.

    Lemma cgraph_equiv_edge g1 g2 v1 v2 :
      cgraph_equiv g1 g2 ->
      edge g1 v1 v2 ->
      edge g2 v1 v2.
    Proof.
      unfold edge. intros ->. done.
    Qed.

    Lemma uconn_equiv g1 g2 v1 v2 :
      cgraph_equiv g1 g2 ->
      uconn g1 v1 v2 -> uconn g2 v1 v2.
    Proof.
      intros He Hc.
      induction Hc; try reflexivity.
      eapply rtc_transitive; eauto.
      eapply rtc_once.
      destruct H0;[left|right]; eauto using cgraph_equiv_edge.
    Qed.

    Lemma move_edge_uconn g v1 v2 v3 :
      cgraph_wf g ->
      ¬ uconn g v1 v2 ->
      ¬ uconn (move_edge g v1 v2 v3) v1 v2.
    Proof.
      intros Hwf H1.
      destruct (out_edges g v1 !! v3) eqn:E; last first.
      { unfold move_edge. rewrite E. done. }
      assert (¬ uconn (delete_edge (move_edge (insert_edge g v1 v2 o) v1 v2 v3) v1 v2) v1 v2).
      {
        eapply delete_edge_uconn.
        - eapply move_edge_wf.
          + intros ->. eapply H1. eapply rtc_once. left. eauto using some_edge.
          + eapply insert_edge_wf; eauto.
          + left. unfold edge.
            rewrite out_edges_insert_edge.
            case_decide; simplify_eq. rewrite lookup_insert. eauto.
        - unfold edge.
          erewrite move_edge_out_edges; last first.
          + rewrite out_edges_insert_edge.
            case_decide; simplify_eq.
            rewrite lookup_insert_spec.
            case_decide; simplify_eq; eauto.
          + rewrite !out_edges_insert_edge.
            repeat case_decide; simplify_eq.
            * rewrite !lookup_insert_spec.
              case_decide; simplify_eq. eauto.
            * rewrite lookup_delete_spec lookup_insert_spec.
              case_decide; simplify_eq.
              -- exfalso. apply H1.
                 eapply rtc_once. left. eauto using some_edge.
              -- case_decide; simplify_eq. eauto.
      }
      intro. apply H0.
      eapply uconn_equiv; eauto.
      intro.
      rewrite out_edges_delete_edge.
      erewrite move_edge_out_edges; last done.
      erewrite move_edge_out_edges; last first.
      { rewrite out_edges_insert_edge. case_decide; eauto.
        rewrite lookup_insert_spec. case_decide; simplify_eq; eauto. }
      rewrite !out_edges_insert_edge.
      repeat case_decide; simplify_eq; eauto.
      - assert (v2 ≠ v3). { intros ->. eapply no_self_edge; eauto using some_edge. }
        rewrite delete_insert_ne; eauto.
        rewrite delete_insert; eauto.
        destruct (out_edges g v2 !! v2) eqn:F; eauto.
        exfalso. eapply no_self_edge; eauto using some_edge.
      - rewrite delete_commute.
        rewrite delete_insert; eauto.
        destruct (out_edges g v !! v2) eqn:F; eauto.
        exfalso. apply H1. apply rtc_once.
        left. eapply some_edge; eauto.
    Qed.
  End move_edge.

  Section move_edges.
    Lemma move_edges g v1 v2 e1 e2 :
      cgraph_wf g ->
      ¬ uconn g v1 v2 ->
      e1 ##ₘ e2 ->
      out_edges g v1 = e1 ∪ e2 ->
      ∃ g', cgraph_wf g' ∧
        ¬ uconn g' v1 v2 ∧
        (∀ v, out_edges g' v =
          if decide (v = v1) then e1
          else if decide (v = v2) then out_edges g v ∪ e2
          else out_edges g v) ∧
        (∀ v, in_labels g' v ≡ in_labels g v).
    Proof.
      revert g e1.
      induction e2 using map_ind; intros g e1;
      intros Hwf Hnuconn Hdisj Hout.
      - exists g. rewrite right_id_L in Hout.
        split_and!; eauto. intro.
        repeat case_decide; simplify_eq; eauto.
        rewrite right_id_L //.
      - specialize (IHe2 (move_edge g v1 v2 i) e1).
        destruct IHe2.
        + apply move_edge_wf'; eauto. intros ->. apply Hnuconn.
          apply rtc_once.
          left.
          unfold edge.
          rewrite Hout.
          rewrite lookup_union lookup_insert.
          destruct (e1 !! i); eauto.
        + apply move_edge_uconn; eauto.
        + solve_map_disjoint.
        + destruct (out_edges g v1 !! i) eqn:E.
          2: { rewrite Hout in E. rewrite lookup_union lookup_insert in E.
            destruct (e1 !! i); simpl in *; simplify_eq.  }
          erewrite move_edge_out_edges; eauto.
          repeat case_decide; simplify_eq.
          -- exfalso. apply Hnuconn. reflexivity.
          -- rewrite Hout. rewrite delete_union.
             rewrite delete_insert; eauto.
             rewrite delete_notin; eauto.
             solve_map_disjoint.
        + destruct H1 as (H1 & H2 & H3 & H4).
          exists x0. split_and!; eauto.
          -- intros v. rewrite H3.
             assert (out_edges g v1 !! i = Some x).
             { rewrite Hout. rewrite lookup_union lookup_insert.
                destruct (e1 !! i) eqn:E; simpl; eauto.
                specialize (Hdisj i). rewrite E in Hdisj. rewrite lookup_insert in Hdisj.
                simpl in *. done. }
             repeat case_decide; simplify_eq; eauto.
             ++ erewrite move_edge_out_edges; eauto.
                case_decide; simplify_eq.
                apply map_eq; intro.
                rewrite !lookup_union !lookup_insert_spec;
                repeat case_decide; simplify_eq; eauto.
                rewrite H0. simpl.
                destruct (out_edges g v2 !! i0) eqn:E; eauto; simpl.
                exfalso.
                apply Hnuconn.
                eapply rtc_transitive; eapply rtc_once; [left|right];
                eauto using some_edge.
             ++ erewrite move_edge_out_edges; eauto.
                repeat case_decide; simplify_eq. done.
          -- intros v. rewrite H4. rewrite move_edge_in_labels'; eauto.
    Qed.

    Lemma move_edges' g v1 v2 e1 e2 :
      cgraph_wf g ->
      ¬ uconn g v1 v2 ->
      e1 ##ₘ e2 ->
      out_edges g v1 = e1 ∪ e2 ->
      ∃ g', cgraph_wf g' ∧
        ¬ uconn g' v1 v2 ∧
        out_edges g' v1 = e1 ∧
        out_edges g' v2 = out_edges g v2 ∪ e2 ∧
        (∀ v, v ≠ v1 -> v ≠ v2 -> out_edges g' v = out_edges g v) ∧
        (∀ v, in_labels g' v ≡ in_labels g v).
    Proof.
      intros.
      edestruct move_edges as (?&?&?&?&?); eauto.
      eexists. split_and!; eauto.
      - specialize (H6 v1). case_decide; simplify_eq; done.
      - specialize (H6 v2). repeat case_decide; simplify_eq; done.
      - intros. specialize (H6 v); repeat case_decide; simplify_eq; eauto.
    Qed.
  End move_edges.


  Lemma gmap_xsplit (e1 e2 e1' e2' : gmap V L) :
    e1 ##ₘ e2 ->
    e1' ##ₘ e2' ->
    e1 ∪ e2 = e1' ∪ e2' ->
    ∃ e11 e12 e21 e22,
      e11 ##ₘ e12 ∧ e21 ##ₘ e22 ∧
      e11 ##ₘ e21 ∧ e12 ##ₘ e22 ∧
      e1 = e11 ∪ e12 ∧ e2 = e21 ∪ e22 ∧
      e1' = e11 ∪ e21 ∧ e2' = e12 ∪ e22.
  Proof. Admitted.
    

  Section exchange.
    Lemma exchange g v1 v2 e1 e2 :
      cgraph_wf g ->
      ¬ uconn g v1 v2 ->
      e1 ##ₘ e2 ->
      out_edges g v1 ∪ out_edges g v2 = e1 ∪ e2 ->
      ∃ g', cgraph_wf g' ∧
        ¬ uconn g' v1 v2 ∧
        out_edges g' v1 = e1 ∧
        out_edges g' v2 = e2 ∧
        (∀ v, v ≠ v1 -> v ≠ v2 -> out_edges g' v = out_edges g v) ∧
        (∀ v, in_labels g' v ≡ in_labels g v).
    Proof.
      intros Hwf Hnuconn Hdisj Hsplit.
      assert (out_edges g v1 ##ₘ out_edges g v2) as Hdisj'.
      { apply not_uconn_out_disjoint. done. }
      destruct (gmap_xsplit _ _ _ _ Hdisj' Hdisj Hsplit)
        as (e11 & e12 & e21 & e22 & Hdisj1 & Hdisj2 & Hdisj3 & Hdisj4 &
            ? & ? & HH1 & HH2); subst.

      destruct (move_edges' g v1 v2 e11 e12)
        as (g' & Hwf' & Hnuconn' & Hv1 & Hv2 & Hv & Hin); eauto.
      rewrite H1 in Hv2.
      rewrite <-assoc in Hv2; last apply _.
      rewrite map_union_comm in Hv2; last solve_map_disjoint.

      destruct (move_edges' g' v2 v1 (e22 ∪ e12) e21)
        as (g'' & Hwf'' & Hnuconn'' & Hv1' & Hv2' & Hv' & Hin'); eauto.
      { intro. apply Hnuconn'. symmetry. done. }
      { solve_map_disjoint. }

      eexists. split_and!; eauto.
      - intro. symmetry in H2. eauto.
      - rewrite Hv2' Hv1 //.
      - rewrite Hv1'. rewrite map_union_comm; eauto.
      - intros. rewrite Hv'; eauto.
      - intros. rewrite Hin'. eauto.
    Qed.
  End exchange.

  Section exchange_alloc.
    Lemma exchange_alloc g v1 v2 e1 e2 l :
      cgraph_wf g ->
      ¬ uconn g v1 v2 ->
      e1 ##ₘ e2 ->
      out_edges g v1 ∪ out_edges g v2 = e1 ∪ e2 ->
      ∃ g', cgraph_wf g' ∧
        out_edges g' v1 = <[v2:=l]> e1 ∧
        out_edges g' v2 = e2 ∧
        (∀ v, v ≠ v1 -> v ≠ v2 -> out_edges g' v = out_edges g v) ∧
        in_labels g' v2 ≡ {[ l ]} ⋅ in_labels g v2 ∧
        (∀ v, v ≠ v2 -> in_labels g' v ≡ in_labels g v).
    Proof.
      intros Hwf Hnuconn Hdisj Hsplit.
      destruct (exchange g v1 v2 e1 e2)
        as (g' & Hwf' & Hnuconn' & Hout1 & Hout2 & Hrest & Hin); eauto.
      exists (insert_edge g' v1 v2 l).
      split_and!.
      - eapply insert_edge_wf; eauto.
      - rewrite out_edges_insert_edge. sdec; done.
      - rewrite out_edges_insert_edge. sdec; eauto.
        exfalso. apply Hnuconn'. reflexivity.
      - intros. rewrite out_edges_insert_edge. sdec. eauto.
      - rewrite in_labels_insert_edge.
        + sdec. rewrite Hin. done.
        + intro. eapply Hnuconn'. eapply rtc_once. left. done.
      - intros. rewrite in_labels_insert_edge.
        + sdec. rewrite Hin. done.
        + intro. eapply Hnuconn'. eapply rtc_once. left. done.
    Qed.
  End exchange_alloc.


  Section exchange_dealloc.
    Lemma exchange_dealloc g v1 v2 e1 e2 l :
      cgraph_wf g ->
      out_edges g v1 !! v2 = Some l ->
      e1 ##ₘ e2 ->
      delete v2 (out_edges g v1) ∪ out_edges g v2 = e1 ∪ e2 ->
      ∃ g', cgraph_wf g' ∧
        ¬ uconn g' v1 v2 ∧
        out_edges g' v1 = e1 ∧
        out_edges g' v2 = e2 ∧
        (∀ v, v ≠ v1 -> v ≠ v2 -> out_edges g' v = out_edges g v) ∧
        (∀ x, in_labels g v2 ≡ {[ l ]} ⋅ x -> in_labels g' v2 ≡ x) ∧
        (∀ v, v ≠ v2 -> in_labels g' v ≡ in_labels g v).
    Proof.
      intros Hwf H1 Hdisj Hsplit.
      destruct (exchange (delete_edge g v1 v2) v1 v2 e1 e2)
        as (g' & Hwf' & Hnuconn' & Hout1 & Hout2 & Hrest & Hin).
      - eapply delete_edge_wf; eauto.
      - eapply delete_edge_uconn; eauto using some_edge.
      - eauto.
      - rewrite !out_edges_delete_edge. sdec; eauto.
        exfalso. eapply no_self_edge; eauto using some_edge.
      - exists g'. split_and!; eauto.
        + intros. rewrite Hrest; eauto.
          rewrite out_edges_delete_edge. sdec. done.
        + intros. rewrite Hin. rewrite in_labels_delete_edge_eq; last done; eauto.
        + intros. rewrite Hin.
          rewrite in_labels_delete_edge_neq; eauto.
    Qed.
  End exchange_dealloc.

  Section exchange_relabel.
    Lemma exchange_relabel g v1 v2 e1 e2 l l' :
      cgraph_wf g ->
      out_edges g v1 !! v2 = Some l ->
      e1 ##ₘ e2 ->
      delete v2 (out_edges g v1) ∪ out_edges g v2 = e1 ∪ e2 ->
      ∃ g', cgraph_wf g' ∧
        out_edges g' v1 = <[v2:=l']> e1 ∧
        out_edges g' v2 = e2 ∧
        (∀ v, v ≠ v1 -> v ≠ v2 -> out_edges g' v = out_edges g v) ∧
        (∀ x, in_labels g v2 ≡ {[ l ]} ⋅ x -> in_labels g' v2 ≡ {[ l' ]} ⋅ x) ∧
        (∀ v, v ≠ v2 -> in_labels g' v ≡ in_labels g v).
    Proof.
      intros Hwf H1 Hdisj Hsplit.
      destruct (exchange_dealloc g v1 v2 e1 e2 l)
        as (g' & Hwf' & Hnuconn' & Hout1 & Hout2 & Hrest & Hin2 & Hin); eauto.
      exists (insert_edge g' v1 v2 l').
      split_and!; eauto.
      - eapply insert_edge_wf; eauto.
      - rewrite out_edges_insert_edge. sdec; done.
      - rewrite out_edges_insert_edge. sdec; eauto.
        exfalso. apply Hnuconn'. reflexivity.
      - intros. rewrite out_edges_insert_edge. sdec.
        rewrite Hrest; eauto.
      - intros. rewrite in_labels_insert_edge.
        + sdec. rewrite Hin2; done.
        + intro. eapply Hnuconn'. eapply rtc_once. left. done.
      - intros. rewrite in_labels_insert_edge.
        + sdec. rewrite Hin; done.
        + intro. eapply Hnuconn'. eapply rtc_once. left. done.
    Qed.
  End exchange_relabel.

End cgraph.