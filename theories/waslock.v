From diris.heap_lang Require Export proofmode notation.
Set Default Proof Using "Type".

Definition newlock : val := λ: <>, ref #false.
Definition lock : val := λ: "x", WAS "x" #false #true.
Definition unlock : val := λ: "x", "x" <- #true.

Section proof.
  Context `{!heapG Σ}.

  Lemma foo x a : vals_compare_safe a #false → {{{ x ↦ a }}} lock #x {{{ RET #(); x ↦ #true }}}.
  Proof.
    intros Hvcs.
    iIntros (Φ) "Hx Post".
    wp_lam.
    Check wp_was.
    wp_apply (wp_was with "Hx").
    - done.
    - iIntros "H". iApply "Post". iDestruct "H" as "[H1 H2]". iFrame.
  Qed.
End proof.
