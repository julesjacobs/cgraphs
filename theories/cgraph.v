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
    match g !! v with
    | Some e => e
    | None => ∅
    end.

  Definition c_insertV (g : cgraph) (v : V) := <[ v := ∅ ]> g.
  Definition c_deleteV (g : cgraph) (v : V) := delete v g.

  Definition c_insertE (g : cgraph) (v1 v2 : V) (l : L) :=
    alter (λ e, <[ v2 := l ]> e) v1 g.
  Definition c_deleteE (g : cgraph) (v1 v2 : V) :=
    alter (λ e, delete v2 e) v1 g.

  Definition c_to_uforest (g : cgraph) : uforest V. Admitted.
  Definition c_acyclic (g : cgraph) : Prop := forest (c_to_uforest g).

  Definition c_dom_valid (g : cgraph) : Prop :=
    ∀ (v : V) e, g !! v = Some e -> dom (gset V) e ⊆ c_vertices g.

  Definition cgraph_wf (g : cgraph) : Prop := c_dom_valid g ∧ c_acyclic g.

  Definition c_conn (g : cgraph) (v1 v2 : V) := True.


  (* Mutate/reader lemmas *)

  Lemma c_vertices_insertV g v :
    c_vertices (c_insertV g v) = c_vertices g ∪ {[ v ]}.
  Proof. Admitted.

  Lemma c_vertices_deleteV g v :
    c_vertices (c_deleteV g v) = c_vertices g ∖ {[ v ]}.
  Proof. Admitted.

  Lemma c_insertE_out g v1 v1' v2 l :
    c_out (c_insertE g v1 v2 l) v1' = if decide (v1 = v1') then <[ v2 := l ]> (c_out g v1') else c_out g v1'.
  Proof.
  Admitted.

  Lemma c_insertE_in g v1 v2 v2' l :
    c_in (c_insertE g v1 v2 l) v2' = if decide (v2 = v2') then <[ v1 := l ]> (c_in g v2') else c_in g v2'.
  Proof.
  Admitted.

  Lemma c_deleteE_out g v1 v1' v2 :
    c_out (c_deleteE g v1 v2) v1' = if decide (v1 = v1') then delete v2 (c_out g v1') else c_out g v1'.
  Proof.
  Admitted.

  Lemma c_deleteE_in g v1 v2 v2' :
    c_in (c_deleteE g v1 v2) v2' = if decide (v2 = v2') then delete v1 (c_in g v2') else c_in g v2'.
  Proof.
  Admitted.

  (* Mutate/wf lemmas *)

  Lemma c_insertV_wf g v :
    cgraph_wf g -> cgraph_wf (c_insertV g v).
  Proof.
  Admitted.

  Lemma c_deleteV_wf g v :
    cgraph_wf g -> cgraph_wf (c_deleteV g v).
  Proof.
  Admitted.

  Lemma c_insertE_wf g v1 v2 l :
    cgraph_wf g -> cgraph_wf (c_insertE g v1 v2 l).
  Proof.
  Admitted.

  Lemma c_deleteE_wf g v1 v2 :
    cgraph_wf g -> cgraph_wf (c_deleteE g v1 v2).
  Proof.
  Admitted.

  Lemma c_deleteE_conn g v1 v2 :
    cgraph_wf g -> ¬ c_conn (c_deleteE g v1 v2) v1 v2.
  Proof.
  Admitted.

  (* Todo: adequacy for acyclicity lemma *)
End cgraph.