From cgraphs.sessiontypes Require Import invariant progress.

Theorem safety (e : expr) (es : list expr) (h : heap) :
  typed ∅ e UnitT ->
  steps [e] ∅ es h ->
    (h = ∅ ∧ ∀ e, e ∈ es -> e = Val UnitV) ∨
    (∃ es' h', step es h es' h').
Proof.
  intros Htyped Hsteps.
  by eapply global_progress, invariant_holds.
Qed.


(*
  The following command can be used to verify that everything has been formally
  proved. It should print "classic : ∀ P : Prop, P ∨ ¬ P" as the only axiom.
  This indicates that our proof relies on classical logic.
  (we use classical logic for convenience.)
*)
(* Print Assumptions safety. *)