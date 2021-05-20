From iris.proofmode Require Export tactics.
Require Export diris.uforests.
From diris Require Export util.
From stdpp Require Export gmap.

Section cgraph.
  Context {V : Type}.
  Context `{Countable V}.
  Context {L : Type}.

  Definition cgraph := gmap V (gmap V L).

  Definition c_vertices (g : cgraph) : gset V := dom (gset V) g.

  Definition c_out (g : cgraph) (v : V) : gmap V L :=
    match g !! v with
    | Some e => e
    | None => ∅
    end.

  Definition c_in (g : cgraph) (v : V) : gmap V L :=
    map_fold (λ v' ev' (ins : gmap V L),
      match ev' !! v with
      | Some l => <[ v' := l ]> ins
      | None => ins
      end) ∅ g.

  Definition c_insertV (g : cgraph) (v : V) := <[ v := ∅ ]> g.
  Definition c_deleteV (g : cgraph) (v : V) := delete v g.

  Definition c_insertE (g : cgraph) (v1 v2 : V) (l : L) :=
    alter (λ e, <[ v2 := l ]> e) v1 g.
  Definition c_deleteE (g : cgraph) (v1 v2 : V) :=
    alter (λ e, delete v2 e) v1 g.

  Definition swap {A B} : (A*B -> B*A) := λ '(x,y), (y,x).
  Definition make_undirected (g : gset (V*V)) : gset (V*V) :=
    g ∪ (set_map swap g).
  Definition c_dedges (g : cgraph) : gset (V*V) :=
    dom (gset _) (gmap_curry g).
  Definition c_to_uforest (g : cgraph) : uforest V :=
    make_undirected $ c_dedges g.
  Definition c_acyclic (g : cgraph) := is_uforest (c_to_uforest g).

  Definition c_dom_valid (g : cgraph) :=
    ∀ (v : V) e, g !! v = Some e -> dom (gset V) e ⊆ c_vertices g.

  Definition cgraph_wf (g : cgraph) := c_dom_valid g ∧ c_acyclic g.

  Definition c_edge (g : cgraph) (v1 v2 : V) := is_Some (c_out g v1 !! v2).

  Definition c_uconn (g : cgraph) := rtsc (c_edge g).


  (* Mutate/reader lemmas *)

  Lemma c_vertices_insertV g v :
    c_vertices (c_insertV g v) = {[ v ]} ∪ c_vertices g.
  Proof.
    apply dom_insert_L.
  Qed.

  Lemma c_vertices_deleteV g v :
    c_vertices (c_deleteV g v) = c_vertices g ∖ {[ v ]}.
  Proof.
    apply dom_delete_L.
  Qed.

  Lemma c_insertE_out g v1 v1' v2 l :
    v1 ∈ c_vertices g -> c_out (c_insertE g v1 v2 l) v1' = if decide (v1 = v1') then <[ v2 := l ]> (c_out g v1') else c_out g v1'.
  Proof.
    intros Hin.
    rewrite /c_out /c_insertE.
    case_decide.
    + subst. rewrite lookup_alter. destruct (g !! v1') eqn:E.
      - rewrite E //.
      - exfalso. rewrite /c_vertices in Hin. apply elem_of_dom in Hin.
        rewrite E in Hin. destruct Hin. simplify_eq.
    + rewrite lookup_alter_ne //.
  Qed.

  Lemma c_insertE_in g v1 v2 v2' l :
    c_in (c_insertE g v1 v2 l) v2' = if decide (v2 = v2') then <[ v1 := l ]> (c_in g v2') else c_in g v2'.
  Proof.
  Admitted.

  Lemma c_deleteE_out g v1 v1' v2 :
    c_out (c_deleteE g v1 v2) v1' = if decide (v1 = v1') then delete v2 (c_out g v1') else c_out g v1'.
  Proof.
    rewrite /c_out /c_deleteE.
    case_decide.
    + subst. rewrite lookup_alter. destruct (g !! v1') eqn:E.
      - rewrite E //.
      - rewrite E /= delete_empty //.
    + rewrite lookup_alter_ne //.
  Qed.

  Lemma c_deleteE_in g v1 v2 v2' :
    c_in (c_deleteE g v1 v2) v2' = if decide (v2 = v2') then delete v1 (c_in g v2') else c_in g v2'.
  Proof.
    rewrite /c_in /c_deleteE.
    case_decide.
    - subst. Search map_fold alter. admit.
  Admitted.

  (* Mutate/wf lemmas *)

  Lemma gmap_curry_empty `{Countable A} {B} : gmap_curry (∅ : gmap A (gmap A B)) = ∅.
  Proof.
    rewrite /gmap_curry map_fold_empty //.
  Qed.

  Lemma make_undirected_empty : make_undirected ∅ = ∅.
  Proof.
    unfold make_undirected. rewrite left_id_L. rewrite set_map_empty. done.
  Qed.

  Lemma c_to_uforest_empty : c_to_uforest ∅ = ∅.
  Proof.
    unfold c_to_uforest, c_dedges.
    Search gmap_curry. rewrite gmap_curry_empty.
    rewrite dom_empty_L. rewrite make_undirected_empty. done.
  Qed.

  Lemma c_empty_wf :
    cgraph_wf ∅.
  Proof.
    split.
    - unfold c_dom_valid. intros. rewrite lookup_empty in H0. simplify_eq.
    - unfold c_acyclic. rewrite c_to_uforest_empty. apply forest_empty.
  Qed.

  Lemma gmap_curry_insert_empty `{Countable A} {B} (g : gmap A (gmap A B)) v :
    gmap_curry (<[v:=∅]> g) = gmap_curry g.
  Proof.
  Admitted.


  Lemma c_to_uforest_insert_empty g v : c_to_uforest (<[v:=∅]> g) = c_to_uforest g.
  Proof.
    unfold c_to_uforest. unfold c_dedges. rewrite gmap_curry_insert_empty //.
  Qed.

  Lemma c_insertV_wf g v :
    cgraph_wf g -> cgraph_wf (c_insertV g v).
  Proof.
    intros [].
    split.
    - unfold c_dom_valid. intros.
      destruct (decide (v = v0)).
      + subst. unfold c_insertV in *. rewrite lookup_insert in H2. simplify_eq.
        rewrite dom_empty. set_solver.
      + unfold c_insertV in *. rewrite lookup_insert_ne in H2; try done.
        specialize (H0 _ _ H2). set_solver.
    - unfold c_acyclic. unfold c_insertV. rewrite c_to_uforest_insert_empty. apply H1.
  Qed.

  Lemma c_in_empty g v :
    c_in g v = ∅ -> ∀ v' e, g !! v' = Some e -> e !! v = None.
  Proof.
  Admitted.

  Lemma is_uforest_mono `{Countable A} (g1 g2 : uforest A) :
    g1 ⊆ g2 -> is_uforest g2 -> undirected g1 -> is_uforest g1.
  Proof.
  Admitted.

  Lemma make_undirected_undirected g :
    undirected (make_undirected g).
  Proof.
    unfold undirected. intros.
    unfold make_undirected in *.
    rewrite elem_of_union.
    apply elem_of_union in H0 as [].
    - right. replace (y,x) with (swap (x,y)) by done. apply elem_of_map_2. done.
    - left. apply elem_of_map_1 in H0 as (?&?&?). destruct x0. simpl in *.
      simplify_eq. done.
  Qed.

  Lemma make_undirected_mono (g1 g2 : gset (V*V)) :
    g1 ⊆ g2 -> make_undirected g1 ⊆ make_undirected g2.
  Proof.
    intros HH.
    unfold make_undirected.
    apply union_mono; eauto.
    apply set_map_mono; eauto. done.
  Qed.

  Lemma gmap_curry_mono `{Countable A} {B} (g1 g2 : gmap A (gmap A B)) :
    g1 ⊆ g2 -> gmap_curry g1 ⊆ gmap_curry g2.
  Proof.
  Admitted.

  Lemma c_to_uforest_mono (g1 g2 : cgraph) :
    g1 ⊆ g2 -> c_to_uforest g1 ⊆ c_to_uforest g2.
  Proof.
    intros HH.
    unfold c_to_uforest. apply make_undirected_mono.
    unfold c_dedges. apply subseteq_dom.
    apply gmap_curry_mono. done.
  Qed.

  Lemma c_deleteV_wf g v :
    c_in g v = ∅ -> cgraph_wf g -> cgraph_wf (c_deleteV g v).
  Proof.
    intros Hin [].
    split.
    - intros ???. unfold c_vertices, c_deleteV in *.
      unfold c_dom_valid in H0.
      destruct (decide (v = v0)).
      + subst. rewrite lookup_delete in H2. simplify_eq.
      + rewrite lookup_delete_ne in H2; try done.
        specialize (H0 _ _ H2). rewrite dom_delete_L.
        unfold c_vertices in *.
        assert (v ∉ dom (gset V) e); last set_solver.
        rewrite not_elem_of_dom. eapply c_in_empty; eauto.
    - eapply is_uforest_mono. 2: eauto. 2: apply make_undirected_undirected.
      apply c_to_uforest_mono. unfold c_deleteV.
      apply delete_subseteq.
  Qed.

  Lemma c_insertE_wf g v1 v2 l :
    ¬ c_uconn g v1 v2 -> v2 ∈ c_vertices g ->
    cgraph_wf g -> cgraph_wf (c_insertE g v1 v2 l).
  Proof.
    intros Hcon Hv2 [].
    split.
    - intros ???.
      unfold c_insertE, c_vertices in *.
      rewrite dom_alter.
      destruct (decide (v1 = v)).
      + subst. rewrite lookup_alter in H2.
        destruct (g !! v) eqn:E; rewrite E in H2; simpl in *; simplify_eq.
        specialize (H0 _ _ E). rewrite dom_insert_L. set_solver.
      + rewrite lookup_alter_ne in H2; eauto.
    - admit.
  Admitted.

  Lemma c_deleteE_wf g v1 v2 :
    cgraph_wf g -> cgraph_wf (c_deleteE g v1 v2).
  Proof.
    intros []. split.
    - intros ???. unfold c_deleteE in *.
      destruct (decide (v1 = v)).
      + subst. rewrite lookup_alter in H2.
        destruct (g !! v) eqn:E; rewrite E in H2; simpl in *; simplify_eq.
        specialize (H0 _ _ E). unfold c_vertices in *. rewrite dom_alter.
        rewrite dom_delete_L. set_solver.
      + rewrite lookup_alter_ne in H2; eauto.
        unfold c_vertices. rewrite dom_alter.
        specialize (H0 _ _ H2). done.
    - unfold c_deleteE. unfold c_acyclic.
      unfold c_to_uforest.
      unfold c_dedges. admit.
  Admitted.

  Lemma c_deleteE_conn g v1 v2 :
    c_edge g v1 v2 -> cgraph_wf g -> ¬ c_uconn (c_deleteE g v1 v2) v1 v2.
  Proof.
  Admitted.

  (* Todo: adequacy for acyclicity lemma *)
End cgraph.