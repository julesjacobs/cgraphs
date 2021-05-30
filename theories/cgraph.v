From iris.proofmode Require Import tactics.
Require Export diris.uforests.
From diris Require Export util.
From stdpp Require Export gmap.
Require Export diris.multiset.

Definition map_fold `{FinMapToList K A M} {B}
  (f : K → A → B → B) (b : B) : M → B := foldr (curry f) b ∘ map_to_list.

Notation cgraph V L := (gmap V (gmap V L)).
(* Definition uforest V := gset (V * V). *)

Section cgraph.
  Context {V : Type}.
  Context `{Countable V}.
  Context {L : ofe}.

  Definition vertices (g : cgraph V L) : gset V := dom (gset V) g.

  Definition out_edges (g : cgraph V L) (v : V) : gmap V L :=
    match g !! v with
    | Some e => e
    | None => ∅
    end.

  (* Definition mb_insert (v v' : V) (ev' ins : gmap V L) :=
    match ev' !! v with | Some l => <[v':=l]> ins | None => ins end.

  Definition in_edges (g : cgraph V L) (v : V) : gmap V L :=
    map_fold (mb_insert v) ∅ g. *)

  Definition ms_insert (v v' : V) (ev' : gmap V L) (ins : list L) : list L :=
    match ev' !! v with | Some l => l :: ins | None => ins end.

  Definition in_labels (g : cgraph V L) (v : V) : multiset L. Admitted.
    (* ev' ← map_to_list g ; option_list (ev'.2 !! v). *)

    (* map_fold (ms_insert v) [] g. *)

  Definition insert_edge (g : cgraph V L) (v1 v2 : V) (l : L) :=
    <[ v1 := out_edges g v1 ∪ {[ v2 := l ]} ]> g.

  Definition delete_edge (g : cgraph V L) (v1 v2 : V) :=
    <[ v1 := delete v2 (out_edges g v1) ]> g.

  Definition swap {A B} : (A*B -> B*A) := λ '(x,y), (y,x).
  Definition make_undirected (g : gset (V*V)) : gset (V*V) :=
    g ∪ (set_map swap g).
  Definition dedges (g : cgraph V L) : gset (V*V) :=
    dom (gset _) (gmap_curry g).
  Definition to_uforest (g : cgraph V L) : uforest V :=
    make_undirected $ dedges g.
  Definition acyclic (g : cgraph V L) := is_uforest (to_uforest g).

  (* Definition dom_valid (g : cgraph V L) :=
    ∀ (v : V) e, g !! v = Some e -> dom (gset V) e ⊆ vertices g. *)

  Definition edge (g : cgraph V L) (v1 v2 : V) := is_Some (out_edges g v1 !! v2).

  Definition no_short_loops (g : cgraph V L) :=
    ∀ v1 v2, ¬ (edge g v1 v2 ∧ edge g v2 v1).

  Definition cgraph_wf (g : cgraph V L) := no_short_loops g ∧ acyclic g.

  Definition uconn (g : cgraph V L) := rtsc (edge g).


  Lemma out_edges_empty v :
    out_edges ∅ v = ∅.
  Proof.
    unfold out_edges. rewrite lookup_empty //.
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

  Lemma in_labels_empty v :
    in_labels ∅ v = ε.
  Proof.
  Admitted.

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

  Lemma out_edges_delete_edge (g : cgraph V L) (v1 v2 v3 : V) :
    out_edges (delete_edge g v1 v2) v3 =
      if decide (v1 = v3) then delete v2 (out_edges g v3)
      else out_edges g v3.
  Proof.
    unfold delete_edge. rewrite out_edges_insert.
    repeat case_decide; simplify_eq; done.
  Qed.

  Lemma in_labels_insert_edge (g : cgraph V L) (v1 v2 v3 : V) (l : L) :
    in_labels (insert_edge g v1 v2 l) v3 =
      if decide (v2 = v3) then in_labels g v3 ⋅ {[ l ]}
      else in_labels g v3.
  Proof.
  Admitted.

  Lemma in_labels_delete_edge (g : cgraph V L) (v1 v2 v3 : V) (l : L) (x : multiset L) :
    out_edges g v1 !! v2 = Some l ->
    in_labels g v3 = x ⋅ {[ l ]} ->
    in_labels (delete_edge g v1 v2) v3 =
      if decide (v2 = v3) then x
      else in_labels g v3.
  Proof.
  Admitted.

  Lemma insert_edge_wf g v1 v2 l :
    ¬ uconn g v1 v2 ->
    cgraph_wf g ->
    cgraph_wf (insert_edge g v1 v2 l).
  Proof.
  Admitted.

  Lemma delete_edge_wf g v1 v2 :
    cgraph_wf g ->
    cgraph_wf (delete_edge g v1 v2).
  Proof.
  Admitted.

  Lemma delete_edge_uconn g v1 v2 :
    edge g v1 v2 ->
    cgraph_wf g ->
    ¬ uconn (delete_edge g v1 v2) v1 v2.
  Proof.
  Admitted.

  Definition exchange_valid g v1 v2 e1 e2 :=
    edge g v1 v2 ∧ e1 ##ₘ e2 ∧ e1 ∪ e2 = (delete v2 $ out_edges g v1) ∪ out_edges g v2.

  Definition exchange (g : cgraph V L) v1 v2 l' e1 e2 :=
    <[ v1 := e1 ∪ {[ v2 := l' ]} ]> $ <[ v2 := e2 ]> g.

  Lemma exchange_wf g v1 v2 l' e1 e2 :
    exchange_valid g v1 v2 e1 e2 ->
    cgraph_wf g ->
    cgraph_wf (exchange g v1 v2 l' e1 e2).
  Proof.
  Admitted.

  Lemma exchange_in_labels g v1 v2 v3 l l' e1 e2 x :
    exchange_valid g v1 v2 e1 e2 ->
    in_labels g v2 = x ⋅ {[ l ]} ->
    cgraph_wf g ->
    in_labels (exchange g v1 v2 l' e1 e2) v3 =
      if decide (v3 = v2) then x ⋅ {[ l' ]}
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

  Lemma cgraph_wellfounded g (R : V -> V -> Prop) :
    antisymmetric V R ->
    (∀ x y, R x y -> sc (edge g) x y) ->
    cgraph_wf g ->
    wf R.
  Proof.
  Admitted.

(*
  Lemma vertices_insert_vertex g v :
    vertices (insert_vertex g v) = {[ v ]} ∪ vertices g.
  Proof.
    rewrite /insert_vertex /vertices dom_insert_L //.
  Qed.

  Lemma vertices_delete_vertex g v :
    vertices (delete_vertex g v) = vertices g ∖ {[ v ]}.
  Proof.
    rewrite /delete_vertex /vertices dom_delete_L //.
  Qed.

  Lemma insert_edge_out g v1 v1' v2 l :
    v1 ∈ vertices g -> out_edges (insert_edge g v1 v2 l) v1' = if decide (v1 = v1') then <[ v2 := l ]> (out_edges g v1') else out_edges g v1'.
  Proof.
    intros Hin.
    rewrite /out_edges /insert_edge.
    case_decide.
    + subst. rewrite lookup_alter. destruct (g !! v1') eqn:E.
      - done.
      - exfalso. rewrite /vertices in Hin. apply elem_of_dom in Hin.
        rewrite E in Hin. destruct Hin. simplify_eq.
    + rewrite lookup_alter_ne //.
  Qed.

  (* Lemma insert_edge_in g v1 v2 v2' l :
    in_edges (insert_edge g v1 v2 l) v2' = if decide (v2 = v2') then <[ v1 := l ]> (in_edges g v2') else in_edges g v2'.
  Proof.
  Admitted. *)

  Lemma delete_edge_out g v1 v1' v2 :
    out_edges (delete_edge g v1 v2) v1' = if decide (v1 = v1') then delete v2 (out_edges g v1') else out_edges g v1'.
  Proof.
    rewrite /out_edges /delete_edge.
    case_decide.
    + subst. rewrite lookup_alter. destruct (g !! v1') eqn:E.
      - done.
      - rewrite /= delete_empty //.
    + rewrite lookup_alter_ne //.
  Qed.

  (* Lemma delete_edge_in g v1 v2 v2' :
    in_edges (delete_edge g v1 v2) v2' = if decide (v2 = v2') then delete v1 (in_edges g v2') else in_edges g v2'.
  Proof.
    rewrite /in_edges /delete_edge.
    case_decide.
    - subst. Search map_fold alter. admit.
  Admitted. *)

  (* Mutate/wf lemmas *)

  Lemma gmap_curry_empty `{Countable A} {B} : gmap_curry (∅ : gmap A (gmap A B)) = ∅.
  Proof.
    rewrite /gmap_curry map_fold_empty //.
  Qed.

  Lemma make_undirected_empty : make_undirected ∅ = ∅.
  Proof.
    unfold make_undirected. rewrite left_id_L. rewrite set_map_empty. done.
  Qed.

  Lemma to_uforest_empty : to_uforest ∅ = ∅.
  Proof.
    unfold to_uforest, dedges.
    Search gmap_curry. rewrite gmap_curry_empty.
    rewrite dom_empty_L. rewrite make_undirected_empty. done.
  Qed.

  Lemma empty_wf :
    cgraph_wf ∅.
  Proof.
    split.
    - unfold dom_valid. intros. rewrite lookup_empty in H0. simplify_eq.
    - unfold acyclic. rewrite to_uforest_empty. apply forest_empty.
  Qed.

  Lemma gmap_curry_insert_empty `{Countable A} {B} (g : gmap A (gmap A B)) v :
    g !! v = None -> gmap_curry (<[v:=∅]> g) = gmap_curry g.
  Proof.
    intros. apply map_eq. intros [k1 k2].
    rewrite !lookup_gmap_curry.
    destruct (decide (k1=v)); by simplify_map_eq.
  Qed.


  Lemma to_uforest_insert_empty g v : g !! v = None -> to_uforest (<[v:=∅]> g) = to_uforest g.
  Proof.
    unfold to_uforest. unfold dedges. intro. rewrite gmap_curry_insert_empty //.
  Qed.

  Lemma insert_vertex_wf g v :
    v ∉ vertices g -> cgraph_wf g -> cgraph_wf (insert_vertex g v).
  Proof.
    intros Hin.
    intros [].
    split.
    - unfold dom_valid. intros.
      destruct (decide (v = v0)).
      + subst. unfold insert_vertex in *. rewrite lookup_insert in H2. simplify_eq.
        rewrite dom_empty. set_solver.
      + unfold insert_vertex in *. rewrite lookup_insert_ne in H2; try done.
        specialize (H0 _ _ H2). unfold vertices in *. set_solver.
    - unfold acyclic. unfold insert_vertex. rewrite to_uforest_insert_empty. apply H1.
  Admitted.


  (* Lemma mb_insert_fold g v v' e :
    g !! v' = Some e -> in_edges g v = mb_insert v v' e (in_edges (delete v' g) v).
  Proof.
    intros Hv'. unfold in_edges.
    assert (g = <[ v' := e ]> $ delete v' g) as Heq.
    {
      rewrite insert_delete.
      rewrite insert_id; done.
    }
    rewrite {1}Heq.
    rewrite map_fold_insert_L; first done.
    {
      intros. unfold mb_insert.
      destruct (z1 !! v) eqn:E; destruct (z2 !! v) eqn:F; eauto.
      apply insert_commute; done.
    }
    apply lookup_delete.
  Qed. *)



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

  Lemma to_uforest_mono (g1 g2 : cgraph V L) :
    g1 ⊆ g2 -> to_uforest g1 ⊆ to_uforest g2.
  Proof.
    intros HH.
    unfold to_uforest. apply make_undirected_mono.
    unfold dedges. apply subseteq_dom.
    apply gmap_curry_mono. done.
  Qed.

  (* Lemma in_labels_empty g v :
    in_labels g v ≡ ε -> ∀ v' e, g !! v' = Some e -> e !! v = None.
  Proof.
    intros H1 v' e Hv'.
  Admitted. *)
    (* erewrite mb_insert_fold in H1; try done.
    unfold mb_insert in *.
    destruct (e !! v); try done.
    by apply insert_non_empty in H1.
  Qed. *)

  (* Lemma delete_vertex_wf g v :
    in_labels g v = [] -> cgraph_wf g -> cgraph_wf (delete_vertex g v).
  Proof.
    intros Hin [].
    split.
    - intros ???. unfold vertices, delete_vertex in *.
      unfold dom_valid in H0.
      destruct (decide (v = v0)).
      + subst. rewrite lookup_delete in H2. simplify_eq.
      + rewrite lookup_delete_ne in H2; try done.
        specialize (H0 _ _ H2). rewrite dom_delete_L.
        unfold vertices in *.
        assert (v ∉ dom (gset V) e); last set_solver.
        rewrite not_elem_of_dom. eapply in_labels_empty; eauto.
    - eapply is_uforest_mono. 2: eauto. 2: apply make_undirected_undirected.
      apply to_uforest_mono. unfold delete_vertex.
      apply delete_subseteq.
  Qed. *)

  Lemma insert_edge_wf g v1 v2 l :
    ¬ uconn g v1 v2 -> v2 ∈ vertices g ->
    cgraph_wf g -> cgraph_wf (insert_edge g v1 v2 l).
  Proof.
    intros Hcon Hv2 [].
    split.
    - intros ???.
      unfold insert_edge, vertices in *.
      rewrite dom_alter.
      destruct (decide (v1 = v)).
      + subst. rewrite lookup_alter in H2.
        destruct (g !! v) eqn:E; simpl in *; simplify_eq.
        specialize (H0 _ _ E). rewrite dom_insert_L. set_solver.
      + rewrite lookup_alter_ne in H2; eauto.
    - admit.
  Admitted.

  Lemma delete_edge_wf g v1 v2 :
    cgraph_wf g -> cgraph_wf (delete_edge g v1 v2).
  Proof.
    intros []. split.
    - intros ???. unfold delete_edge in *.
      destruct (decide (v1 = v)).
      + subst. rewrite lookup_alter in H2.
        destruct (g !! v) eqn:E; simpl in *; simplify_eq.
        specialize (H0 _ _ E). unfold vertices in *. rewrite dom_alter.
        rewrite dom_delete_L. set_solver.
      + rewrite lookup_alter_ne in H2; eauto.
        unfold vertices. rewrite dom_alter.
        specialize (H0 _ _ H2). done.
    - unfold delete_edge. unfold acyclic.
      unfold to_uforest.
      unfold dedges. admit.
  Admitted.

  Lemma delete_edge_conn g v1 v2 :
    edge g v1 v2 -> cgraph_wf g -> ¬ uconn (delete_edge g v1 v2) v1 v2.
  Proof.
  Admitted. *)

  (* Todo: adequacy for acyclicity lemma *)
End cgraph.