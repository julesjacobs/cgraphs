From diris.heap_lang Require Export proofmode notation.
Set Default Proof Using "Type".


Definition lock : val := λ: "x", WAS "x" #false #true.
Definition unlock : val := λ: "x", "x" <- #true.


Lemma lock_spec1 : {{{ True }}} lock  {{{ RET #(); True }}}.
Proof.
Qed.

Lemma lock_spec1 (x:loc) (a:val) : {{{ x ↦ a }}} lock #x {{{ RET #(); x ↦ #true }}}.
Proof.
Qed.