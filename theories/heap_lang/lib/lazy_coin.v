From iris.base_logic Require Export invariants.
From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export lang proofmode notation.
From iris.heap_lang.lib Require Export nondet_bool.

Definition new_coin: val := λ: <>, (ref NONE, NewProph).

Definition read_coin : val :=
  λ: "cp",
  let: "c" := Fst "cp" in
  let: "p" := Snd "cp" in
  match: !"c" with
    NONE => let: "r" := nondet_bool #() in
           "c" <- SOME "r";; resolve_proph: "p" to: "r";; "r"
  | SOME "b" => "b"
  end.

Section proof.
  Context `{!heapG Σ}.

  Definition val_to_bool (v : val) : bool := bool_decide (v = #true).

  Definition prophecy_to_bool (vs : list (val * val)) : bool :=
    default false (val_to_bool ∘ snd <$> head vs).

  Lemma prophecy_to_bool_of_bool (b : bool) v vs :
    prophecy_to_bool ((v, #b) :: vs) = b.
  Proof. by destruct b. Qed.

  Definition coin (cp : val) (b : bool) : iProp Σ :=
    (∃ (c : loc) (p : proph_id) (vs : list (val * val)),
        ⌜cp = (#c, #p)%V⌝ ∗ proph p vs ∗
        (c ↦ SOMEV #b ∨ (c ↦ NONEV ∗ ⌜b = prophecy_to_bool vs⌝)))%I.

  Lemma new_coin_spec : {{{ True }}} new_coin #() {{{ c b, RET c; coin c b }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    wp_lam.
    wp_apply wp_new_proph; first done.
    iIntros (vs p) "Hp".
    wp_alloc c as "Hc".
    wp_pair.
    iApply ("HΦ" $! (#c, #p)%V ).
    rewrite /coin; eauto 10 with iFrame.
  Qed.

  Lemma read_coin_spec cp b :
    {{{ coin cp b }}} read_coin cp {{{ RET #b; coin cp b }}}.
  Proof.
    iIntros (Φ) "Hc HΦ".
    iDestruct "Hc" as (c p vs ->) "[Hp [Hc | [Hc ->]]]".
    - wp_lam. wp_load. wp_match.
      iApply "HΦ".
      rewrite /coin; eauto 10 with iFrame.
    - wp_lam. wp_load. wp_match.
      wp_apply nondet_bool_spec; first done.
      iIntros (r) "_".
      wp_let.
      wp_store.
      wp_apply (wp_resolve_proph with "[Hp]"); first done.
      iIntros (ws) "[-> Hws]".
      rewrite !prophecy_to_bool_of_bool.
      wp_seq.
      iApply "HΦ".
      rewrite /coin; eauto with iFrame.
  Qed.

End proof.
