From diris.microgv Require Export invariant.

Definition vertex_waiting (ρ : cfg) (x y : vertex) (l : label) :=
  match x,y with
  | VThread n, VBarrier k => True
  | _,_ => False
  end.

Definition vertex_reachable ρ (v : vertex) :=
  match v with
  | VThread n => reachable ρ n
  | VBarrier n => reachable ρ n
  end.

Lemma full_reachability ρ :
  ginv ρ -> fully_reachable ρ.
Proof.
  unfold fully_reachable.
  intros Hinv i.
  classical_right.
  destruct Hinv as [g [Hwf Hinv]].
  cut (∀ v, vertex_reachable ρ v). admit.
  intros v.
  eapply (cgraph_ind' (vertex_waiting ρ) g (vertex_reachable ρ)); eauto; first admit.
  intros.
    [solve_proper|eauto|].
Admitted.