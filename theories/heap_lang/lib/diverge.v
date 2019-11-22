From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export lang.
From iris.heap_lang Require Import proofmode notation.
Set Default Proof Using "Type".

(** This library provides a [diverge] function that goes into an infinite loop
when provided with an (arbitrary) argument value. This function can be used to
let the program diverge in corner cases that one wants to omit in proofs. This
mechanism should be used with care and communicated clearly, obviously.

Note that this mechanism only works when establishing partial correctness with
the ordinary version of weakest preconditions, and not when establishing total
correctness using the total version of weakest preconditions.

A typical application for [diverge] is insertion functions for data structures
having a fixed capacity. In such cases, we can choose divergence instead of an
explicit error handling when the full capacity has already been reached. *)

Definition diverge : val :=
  rec: "diverge" "v" := "diverge" "v".

Lemma wp_diverge `{!heapG Σ} s E (Φ : val → iProp Σ) (v : val) :
  WP diverge v @ s;E {{ Φ }}%I.
Proof.
  iLöb as "IH". wp_lam. iApply "IH".
Qed.
