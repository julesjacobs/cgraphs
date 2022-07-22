From cgraphs.multiparty Require Import invariant langdef progress.
Require Import Coq.Logic.Classical.

(* This file contains the main theorems about MPGV. *)
(* This is the theorems part of section 5 in the paper. *)

(* The definitions used in this file can be found in definitions.v *)
(* The language definition can be found in langdef.v *)

(* Theorem 5.1 *)
Theorem global_progress e es h :
  typed ∅ e UnitT -> steps [e] ∅ es h ->
  (∃ es' h', step es h es' h') ∨ (h = ∅ ∧ ∀ e, e ∈ es -> e = Val UnitV).
Proof.
  intros. edestruct inv_global_progress; eauto using invariant_holds.
Qed.

(* Theorem 5.2 *)
Theorem reachability_deadlock_freedom es h :
  deadlock_free es h <-> fully_reachable es h.
Proof.
  unfold deadlock_free, fully_reachable.
  split.
  - intros. destruct (classic (reachable es h x)); eauto.
    assert (∃ s : gset object, ∀ x, x ∈ s <-> active es h x ∧ ¬ reachable es h x) as [s Hs].
    { edestruct activeset_exists. eapply subset_exists. naive_solver. }
    exfalso. eapply (H s).
    split; eauto.
    + set_solver.
    + naive_solver.
    + intros ???. assert (¬ reachable es h (Thread i)) by naive_solver.
      eauto using reachable.
    + intros ????.
      destruct (classic (Chan c ∈ s)); eauto. exfalso.
      eapply Hs in H2 as [].
      destruct (classic (reachable es h (Chan c))); eauto using reachable.
      assert (active es h (Chan c)).
      { destruct H3 as (?&?&?&?&?&?&?&?). eexists. eauto. }
      naive_solver.
    + intros. apply Hs in H2 as [].
      rewrite Hs.
      split. { by eapply obj_refs_active. }
      intro. eapply H4.
      eauto using reachable.
  - intros. intros [].
    eapply set_choose_L in dl_nonempty as [x Hx].
    assert (reachable es h x) as Q by eauto.
    induction Q; naive_solver.
Qed.

(* Theorem 5.3 *)
Theorem deadlock_freedom_and_full_reachability e es h :
  typed ∅ e UnitT -> steps [e] ∅ es h ->
  deadlock_free es h ∧ fully_reachable es h.
Proof.
  intros Htyped Hinv%invariant_holds; last done.
  split; [eapply reachability_deadlock_freedom|];
  unfold fully_reachable; eauto using strong_progress.
Qed.