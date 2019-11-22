From iris.base_logic Require Export invariants.
From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export lang proofmode notation.
From iris.heap_lang.lib Require Export nondet_bool.

(** The clairvoyant coin predicts all the values that it will
*non-deterministically* choose throughout the execution of the
program. This can be seen in the spec. The predicate [coin c bs]
expresses that [bs] is the list of all the values of the coin in the
future. The [read_coin] operation always returns the head of [bs] and the
[toss_coin] operation takes the [tail] of [bs]. *)

Definition new_coin: val :=
  λ: <>, (ref (nondet_bool #()), NewProph).

Definition read_coin : val := λ: "cp", !(Fst "cp").

Definition toss_coin : val :=
  λ: "cp",
  let: "c" := Fst "cp" in
  let: "p" := Snd "cp" in
  let: "r" := nondet_bool #() in
  "c" <- "r";; resolve_proph: "p" to: "r";; #().

Section proof.
  Context `{!heapG Σ}.

  Definition prophecy_to_list_bool (vs : list (val * val)) : list bool :=
    (λ v, bool_decide (v = #true)) ∘ snd <$> vs.

  Definition coin (cp : val) (bs : list bool) : iProp Σ :=
    (∃ (c : loc) (p : proph_id) (vs : list (val * val)),
        ⌜cp = (#c, #p)%V⌝ ∗
        ⌜bs ≠ []⌝ ∗ ⌜tail bs = prophecy_to_list_bool vs⌝ ∗
        proph p vs ∗
        from_option (λ b : bool, c ↦ #b) (∃ b : bool, c ↦ #b) (head bs))%I.

  Lemma new_coin_spec : {{{ True }}} new_coin #() {{{ c bs, RET c; coin c bs }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    wp_lam.
    wp_apply wp_new_proph; first done.
    iIntros (vs p) "Hp".
    wp_apply nondet_bool_spec; first done.
    iIntros (b) "_".
    wp_alloc c as "Hc".
    wp_pair.
    iApply ("HΦ" $! (#c, #p)%V (b :: prophecy_to_list_bool vs)).
    rewrite /coin; eauto with iFrame.
  Qed.

  Lemma read_coin_spec cp bs :
    {{{ coin cp bs }}}
      read_coin cp
    {{{b bs', RET #b; ⌜bs = b :: bs'⌝ ∗ coin cp bs }}}.
  Proof.
    iIntros (Φ) "Hc HΦ".
    iDestruct "Hc" as (c p vs -> ? ?) "[Hp Hb]".
    destruct bs as [|b bs]; simplify_eq/=.
    wp_lam. wp_load.
    iApply "HΦ"; iSplit; first done.
    rewrite /coin; eauto 10 with iFrame.
  Qed.

  Lemma toss_coin_spec cp bs :
    {{{ coin cp bs }}}
      toss_coin cp
    {{{b bs', RET #(); ⌜bs = b :: bs'⌝ ∗ coin cp bs' }}}.
  Proof.
    iIntros (Φ) "Hc HΦ".
    iDestruct "Hc" as (c p vs -> ? ?) "[Hp Hb]".
    destruct bs as [|b bs]; simplify_eq/=.
    wp_lam. do 2 (wp_proj; wp_let).
    wp_apply nondet_bool_spec; first done.
    iIntros (r) "_".
    wp_store.
    wp_apply (wp_resolve_proph with "[Hp]"); first done.
    iIntros (ws) "[-> Hp]".
    wp_seq.
    iApply "HΦ"; iSplit; first done.
    destruct r; rewrite /coin; eauto 10 with iFrame.
  Qed.

End proof.
