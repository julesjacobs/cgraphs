From iris.proofmode Require Export tactics.
Require Export diris.uforests.
From diris Require Export util.
From stdpp Require Export gmap.

Section cgraph.
  Context `{Countable V}.
  Context (L : Type).

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

  Definition make_undirected (g : gset (V*V)) : gset (V*V) :=
    g ∪ (set_map (λ '(x,y), (y,x)) g).
  Definition c_to_uforest (g : cgraph) : uforest V :=
    make_undirected $ dom (gset _) (gmap_curry g).
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
    - admit.
  Admitted.

  Lemma c_deleteV_wf g v :
    c_in g v = ∅ -> c_out g v = ∅ -> cgraph_wf g -> cgraph_wf (c_deleteV g v).
  Proof.
  Admitted.

  Lemma c_insertE_wf g v1 v2 l :
    ¬ c_uconn g v1 v2 -> v1 ∈ c_vertices g -> v2 ∈ c_vertices g ->
    cgraph_wf g -> cgraph_wf (c_insertE g v1 v2 l).
  Proof.
  Admitted.

  Lemma c_deleteE_wf g v1 v2 :
    cgraph_wf g -> cgraph_wf (c_deleteE g v1 v2).
  Proof.
  Admitted.

  Lemma c_deleteE_conn g v1 v2 :
    c_edge g v1 v2 -> cgraph_wf g -> ¬ c_uconn (c_deleteE g v1 v2) v1 v2.
  Proof.
  Admitted.

  (* Todo: adequacy for acyclicity lemma *)
End cgraph.