From stdpp Require Import gmap.
From iris.bi Require Import interface.
From iris.proofmode Require Import tactics.
Require Import diris.langdef.
Require Import diris.hprop.
Require Import diris.util.
Require Import diris.htypesystem.

Fixpoint buf_typed (buf : list val) (ct : chan_type) (rest : chan_type) : hProp :=
  match buf, ct with
  | v::buf', RecvT t ct' => val_typed v t ∗ buf_typed buf' ct' rest
  | [], ct => ⌜⌜ rest = ct ⌝⌝
  | _,_ => False
  end%I.

Definition bufs_typed (bufs : list val * list val) (ct1 ct2 : chan_type) : hProp :=
  (∃ rest:chan_type,
     buf_typed (fst bufs) ct1 rest ∗
     buf_typed (snd bufs) ct2 (dual rest))%I.

Definition invariantΣ (Σ : gmap endpoint chan_type)
      (threads : list expr) (chans : heap) : hProp :=
  (
    ([∗ list] e∈threads, ptyped ∅ e UnitT) ∗
    ([∗ list] i↦bufs∈chans,
    bufs_typed bufs (default EndT (Σ !! (i,true))) (default EndT (Σ !! (i,false))))
  )%I.

Definition invariant (threads : list expr) (chans : heap) : Prop :=
  ∃ Σ, own Σ ⊢ invariantΣ Σ threads chans.

(* Which lemma's do we need for own? *)
(*
  We need to instantiate the existential, then we have:
  own Σ -∗ invariant Σ es h
  -------------------------
  own Σ' -∗ invariant Σ' es' h'

  We want to transform this so that we have the same own Σ'' in top and bottom,
  so that we can get a goal of the worm invariant (?) (?) -∗ invariant (?') (?').
*)

Lemma preservation (threads threads' : list expr) (chans chans' : heap) :
  invariant threads chans ->
  step threads chans threads' chans' ->
  invariant threads' chans'.
Proof.
  intros Hinv Hstep. unfold invariant in *.
  destruct Hinv as [Σ Hinv].
  destruct Hstep.
  destruct H.
  destruct H1.
  (* TODO: Need to extract type info here *)
  - exists Σ. iIntros "HΣ".
    iDestruct (Hinv with "HΣ") as "Hinv".
    unfold invariantΣ.
    rewrite right_id.
    iDestruct "Hinv" as "[Htyped Hbufs]". iFrame.
    admit.
  - admit.
  - admit.
  - exists (delete c Σ).
    admit.
  - admit.
Admitted.





  (*
  invariant : list expr -> heap -> Prop
  invariant' : list expr -> heap -> hProp
  invariant es h := ∃ Σ, invariant' es h Σ

  init : typed ∅ e UnitT -> invariant [e] []
  preservation : step es1 h1 es2 h2 -> invariant es1 h1 -> invariant es2 h2
  progress : invariant es1 h1 -> (final es1 h1) ∨ ∃ es2 h2, step es1 h1 es2 h2
  final es h := (∀ e, e∈es -> is_value e) ∧ ∀ b, b∈h -> b = []

  GOAL:
  type_safety :
    typed ∅ e UnitT ->
    steps [e] [] es h ->
    (final es h) ∨ ∃ es2 h2, step es h es2 h2

  1. Deadlock freedom for session types
  2. Deadlock freedom for locks + session types
  3. Program logic for deadlock freedom
     a) 1&2 als logical relation
     b) put forests in the hProp

  Conferences: LICS, ICFP, POPL
  *)