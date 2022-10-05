From cgraphs.locks.lambdalock Require Import invariant.


Lemma fully_reachable_iff_deadlock_free ρ :
  fully_reachable ρ <-> deadlock_free ρ.
Proof.
  split.
  - intros Hfr s [] i si.
    destruct (Hfr i); eauto.
    exfalso. induction H; naive_solver.
  - intros Hdf i. classical_left.
    eapply (Hdf (λ i, ¬ reachable ρ i));
    first constructor; eauto using reachable.
Qed.

Lemma fully_reachable_type_safety ρ :
  fully_reachable ρ -> type_safety ρ.
Proof.
  intros Hfr i. destruct (Hfr i) as [|[]]; eauto.
Qed.

Lemma fully_reachable_global_progress ρ :
  fully_reachable ρ -> global_progress ρ.
Proof.
  intros Hfr.
  destruct (classic (∃ i, ¬ inactive ρ i)).
  - destruct H as [i Hi]. destruct (Hfr i); first naive_solver.
    clear Hi. right. induction H; eauto.
  - left. intros i. apply NNPP. eauto.
Qed.

Lemma typed_full_reachability e ρ :
  typed ∅ e UnitT -> steps {[ 0 := Thread e ]} ρ -> fully_reachable ρ.
Proof.
  intros Ht Hsteps.
  assert (ginv {[ 0 := Thread e ]}) as Hinv.
  { eapply initialization. done. }
  induction Hsteps.
  - eapply full_reachability. done.
  - eapply IHHsteps. destruct H. eapply preservation; eauto.
Qed.

Lemma typed_global_progress e ρ :
  typed ∅ e UnitT -> steps {[ 0 := Thread e ]} ρ -> global_progress ρ.
Proof.
  intros. eapply fully_reachable_global_progress, typed_full_reachability; done.
Qed.
