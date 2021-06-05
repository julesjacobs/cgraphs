From iris.proofmode Require Import tactics.
Require Export diris.uforests.
From diris Require Export util.
From stdpp Require Export gmap.
Require Export diris.multiset.
From stdpp Require Import fin_maps.

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
    match ev' !! v with | Some l => {[ l ]} ⋅ ins | None => ins end.

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
    Lemma no_self_out_edge g v :
      cgraph_wf g ->
      out_edges g v !! v = None.
    Proof.
      intros Hwf.
    Admitted.

    Lemma no_self_edge g v1 v2 :
      cgraph_wf g ->
      edge g v1 v2 -> v1 ≠ v2.
    Proof.
      intros H1 [] ->.
      assert (out_edges g v2 !! v2 = None); eauto using no_self_out_edge.
      rewrite H0 in H2. simplify_eq.
    Qed.
  End general.

  Section insert_edge.
    Definition insert_edge (g : cgraph V L) (v1 v2 : V) (l : L) :=
      <[ v1 := out_edges g v1 ∪ {[ v2 := l ]} ]> g.

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
        if decide (v1 = v3) then out_edges g v3 ∪ {[ v2 := l ]}
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
      unfold insert_edge, in_labels.
      rewrite map_fold_insert_L.
      Search map_fold insert.
    Admitted.

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
    Admitted.

    Lemma in_labels_delete_edge_neq (g : cgraph V L) (v1 v2 v3 : V) :
      v2 ≠ v3 ->
      in_labels (delete_edge g v1 v2) v3 ≡ in_labels g v3.
    Proof.
    Admitted.

    Lemma delete_edge_wf g v1 v2 :
      cgraph_wf g ->
      cgraph_wf (delete_edge g v1 v2).
    Proof.
    Admitted.

    Lemma delete_edge_uconn g v1 v2 :
      cgraph_wf g ->
      v1 ≠ v2 ->
      ¬ uconn (delete_edge g v1 v2) v1 v2.
    Proof.
    Admitted.
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
      rewrite lookup_insert_spec.
      rewrite lookup_union.
      rewrite lookup_delete_spec.
      repeat case_decide; simplify_eq.
      + rewrite lookup_singleton. simpl. done.
      + rewrite lookup_singleton_ne; eauto.
        destruct (_ !! _); done.
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
        eapply no_self_edge; eauto.
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

    Lemma move_edge_out_edges g v1 v2 v3 v :
      out_edges (move_edge g v1 v2 v3) v = ∅.
    Proof.
    Admitted.

    
  End move_edge.








  Lemma cgraph_wellfounded (R : V -> V -> Prop) g :
  (* Problem: self loops *)
    cgraph_wf g ->
    antisymmetric V R ->
    (∀ x y, R x y -> sc (edge g) x y) ->
    wf R.
  Proof.
  Admitted.

  Lemma not_rtsc `{R : A -> A -> Prop} x :
    (∀ y, ¬ R x y ∧ ¬ R y x) ->
    (∀ y, rtsc R x y -> x = y).
  Proof.
    Search rtsc.
  Admitted.

  Lemma multiset_empty_mult {A : ofe} (x y : multiset A) :
    x ⋅ y ≡ ε -> x = ε ∧ y = ε.
  Proof.
  Admitted.

  Lemma multiset_empty_neq_singleton {A : ofe} {a : A} :
    {[ a ]} ≠ ε.
  Proof.
  Admitted.

  Lemma out_edges_in_labels g v1 v2 l :
    out_edges g v1 !! v2 = Some l ->
    ∃ x, in_labels g v2 ≡ {[ l ]} ⋅ x.
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

  Lemma edge_out_disjoint g v1 v2 :
    cgraph_wf g -> edge g v1 v2 -> out_edges g v1 ##ₘ out_edges g v2.
  Proof.
  Admitted.

  Lemma no_self_out_edge g v :
    cgraph_wf g ->
    out_edges g v !! v = None.
  Proof.
    intros Hwf.
    pose proof (cgraph_wellfounded (λ x y, x = v ∧ y = v) g Hwf).
  Admitted.

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
    split.
    - intros ??[[] []].
      rewrite out_edges_empty in H0.
      rewrite lookup_empty in H0.
      simplify_eq.
    - admit.
  Admitted.




  Lemma delete_edge_uconn g v1 v2 :
    edge g v1 v2 ->
    cgraph_wf g ->
    ¬ uconn (delete_edge g v1 v2) v1 v2.
  Proof.
  Admitted.

  Definition exchange (g : cgraph V L) v1 v2 l' e1 e2 :=
    <[ v1 := e1 ∪ {[ v2 := l' ]} ]> $ <[ v2 := e2 ]> g.

  Definition exchange_valid g v1 v2 e1 e2 :=
    edge g v1 v2 ∧ e1 ##ₘ e2 ∧ e1 ∪ e2 = (delete v2 $ out_edges g v1) ∪ out_edges g v2.

  Lemma exchange_wf g v1 v2 l' e1 e2 :
    exchange_valid g v1 v2 e1 e2 ->
    cgraph_wf g ->
    cgraph_wf (exchange g v1 v2 l' e1 e2).
  Proof.
  Admitted.

  Lemma exchange_in_labels g v1 v2 v3 l l' e1 e2 x :
    exchange_valid g v1 v2 e1 e2 ->
    in_labels g v2 ≡ {[ l ]} ⋅ x ->
    cgraph_wf g ->
    in_labels (exchange g v1 v2 l' e1 e2) v3 =
      if decide (v3 = v2) then {[ l' ]} ⋅ x
      else in_labels g v3.
  Proof.
  Admitted.

  Lemma exchange_out_edges g v1 v2 v3 l' e1 e2 :
    out_edges (exchange g v1 v2 l' e1 e2) v3 =
      if decide (v3 = v1) then e1 ∪ {[ v2 := l' ]}
      else if decide (v3 = v2) then e2
      else out_edges g v3.
  Proof.
    unfold exchange.
    unfold out_edges.
    rewrite !lookup_insert_spec.
    repeat case_decide; simplify_eq; eauto.
  Qed.

  Definition dealloc (g : cgraph V L) v1 v2 e1 e2 :=
    <[ v1 := e1 ]> $ <[ v2 := e2 ]> g.

  Definition dealloc_valid g v1 v2 e1 e2 :=
    edge g v1 v2 ∧ e1 ##ₘ e2 ∧ e1 ∪ e2 = (delete v2 $ out_edges g v1) ∪ out_edges g v2.


  Lemma dealloc_wf g v1 v2 e1 e2 :
    dealloc_valid g v1 v2 e1 e2 ->
    cgraph_wf g ->
    cgraph_wf (dealloc g v1 v2 e1 e2).
  Proof.
  Admitted.

  Lemma dealloc_in_labels g v1 v2 v3 l e1 e2 x :
    dealloc_valid g v1 v2 e1 e2 ->
    in_labels g v2 ≡ {[ l ]} ⋅ x ->
    cgraph_wf g ->
    in_labels (dealloc g v1 v2 e1 e2) v3 =
      if decide (v3 = v2) then x
      else in_labels g v3.
  Proof.
  Admitted.

  Lemma dealloc_out_edges g v1 v2 v3 e1 e2 :
    out_edges (dealloc g v1 v2 e1 e2) v3 =
      if decide (v3 = v1) then e1
      else if decide (v3 = v2) then e2
      else out_edges g v3.
  Proof.
    unfold dealloc.
    unfold out_edges.
    rewrite !lookup_insert_spec.
    repeat case_decide; simplify_eq; eauto.
  Qed.

  Definition alloc (g : cgraph V L) v1 v2 l' e1 e2 :=
    <[ v1 := e1 ∪ {[ v2 := l' ]} ]> $ <[ v2 := e2 ]> g.

  Definition alloc_valid g v1 v2 e1 e2 :=
    ¬ (uconn g v1 v2) ∧ e1 ##ₘ e2 ∧ e1 ∪ e2 = out_edges g v1 ∪ out_edges g v2.

  Lemma alloc_wf g v1 v2 l' e1 e2 :
    alloc_valid g v1 v2 e1 e2 ->
    cgraph_wf g ->
    cgraph_wf (alloc g v1 v2 l' e1 e2).
  Proof.
  Admitted.

  Lemma alloc_in_labels g v1 v2 v3 l' e1 e2 :
    alloc_valid g v1 v2 e1 e2 ->
    cgraph_wf g ->
    in_labels (alloc g v1 v2 l' e1 e2) v3 =
      if decide (v3 = v2) then {[ l' ]} ⋅ in_labels g v2
      else in_labels g v3.
  Proof.
  Admitted.

  Lemma alloc_out_edges g v1 v2 v3 l' e1 e2 :
    out_edges (alloc g v1 v2 l' e1 e2) v3 =
      if decide (v3 = v1) then e1 ∪ {[ v2 := l' ]}
      else if decide (v3 = v2) then e2
      else out_edges g v3.
  Proof.
    unfold alloc.
    unfold out_edges.
    rewrite !lookup_insert_spec.
    repeat case_decide; simplify_eq; eauto.
  Qed.


End cgraph.