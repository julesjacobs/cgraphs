From diris.heap_lang Require Export notation.
From iris.proofmode Require Export tactics.
From iris.heap_lang Require Import proofmode.


Set Default Proof Using "Type".

Definition new_lock : val := λ: <>, ref #false.
Definition lock : val := λ: "x", WAS "x" #false #true.
Definition unlock : val := λ: "x", "x" <- #true.

Lemma lock_spec1 x a : {{{ x ↦ a }}} lock x {{{ RET #(); x ↦ #true }}}.
Proof.
Qed.