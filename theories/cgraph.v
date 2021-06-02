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

  Lemma some_edge (g : cgraph V L) (v1 v2 : V) (l : L) :
    out_edges g v1 !! v2 = Some l -> edge g v1 v2.
  Proof.
    unfold edge. intros ->. eauto.
  Qed.

  Lemma edge_out_disjoint g v1 v2 :
    cgraph_wf g -> edge g v1 v2 -> out_edges g v1 ##ₘ out_edges g v2.
  Proof.
  Admitted.

  Lemma out_edges_in_labels g v1 v2 l :
    out_edges g v1 !! v2 = Some l ->
    ∃ x, in_labels g v2 ≡ {[ l ]} ⋅ x.
  Proof.
  Admitted.

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
    in_labels ∅ v ≡ ε.
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
    in_labels (insert_edge g v1 v2 l) v3 ≡
      if decide (v2 = v3) then in_labels g v3 ⋅ {[ l ]}
      else in_labels g v3.
  Proof.
  Admitted.

  Lemma in_labels_delete_edge (g : cgraph V L) (v1 v2 v3 : V) (l : L) (x : multiset L) :
    out_edges g v1 !! v2 = Some l ->
    in_labels g v3 ≡ x ⋅ {[ l ]} ->
    in_labels (delete_edge g v1 v2) v3 ≡
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

  Lemma cgraph_wellfounded g (R : V -> V -> Prop) :
    antisymmetric V R ->
    (∀ x y, R x y -> sc (edge g) x y) ->
    cgraph_wf g ->
    wf R.
  Proof.
  Admitted.
End cgraph.