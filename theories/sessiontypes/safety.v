From diris Require Import invariant progress.

Theorem safety (e : expr) (es : list expr) (h : heap) :
  typed ∅ e UnitT ->
  steps [e] ∅ es h ->
    (h = ∅ ∧ ∀ e, e ∈ es -> e = Val UnitV) ∨
    (∃ es' h', step es h es' h').
Proof.
  intros Htyped Hsteps.
  by eapply global_progress, invariant_holds.
Qed.