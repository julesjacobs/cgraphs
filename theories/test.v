From diris.heap_lang Require Export notation.
Set Default Proof Using "Type".
Definition new_lock1 : val := λ: <>, ref #false.
Definition new_lock6 : val := λ: <>, ref #false.
Definition new_lock7 : val := λ: <>, ref #false.
Definition new_lock3 : val := λ: <>, ref #false.

Definition lock : val := λ: "x", WAS "x" #false #true.
Definition unlock : val := λ: "x", "x" <- #true.

Lemma lock_spec1 x a : {{{ x ↦ a }}} lock x {{{ RET #(); x ↦ #true }}}.
Proof.
Qed.