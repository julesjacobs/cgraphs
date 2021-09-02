From iris.proofmode Require Export tactics.
Require Export diris.sessiontypes.langdef.
Require Export diris.sessiontypes.rtypesystem.

Lemma subst_rtyped0 (x : string) (v : val) (vT : type) (e : expr) (eT : type) :
  val_typed v vT -∗
  rtyped {[ x := vT ]} e eT -∗
  rtyped0 (subst x v e) eT.
Proof.
  iIntros "Hv Hr".
  rewrite -rtyped_rtyped0_iff.
  replace (∅ : envT) with (delete x {[ x := vT]} : envT) by (apply delete_singleton).
  iApply (subst_rtyped with "Hv Hr"). rewrite lookup_singleton //.
Qed.

Lemma pure_step_rtyped0 e e' t :
  pure_step e e' -> rtyped0 e t -∗ rtyped0 e' t.
Proof.
  intros Hps.
  iIntros "Ht".
  iInduction Hps as [] "IH"; simpl;
  repeat (iDestruct "Ht" as "[Ht Ht2]" || iDestruct "Ht" as (?) "Ht"); eauto; try destruct b; simplify_eq;
  try iApply (subst_rtyped0 with "Ht2 Ht");
  try solve [try iDestruct "Ht2" as "[_ Ht2]"; eauto; try iApply (subst_rtyped0 with "Ht Ht2")];
  try solve [try iDestruct "Ht2" as "[Ht2 _]"; eauto; try iApply (subst_rtyped0 with "Ht Ht2")].
  iDestruct "Ht" as "%".
  iDestruct "Ht2" as "[Ht2 HH]".
  iDestruct "Ht2" as (t0 t3 HH) "[Hv1 Hv2]".
  rewrite -rtyped_rtyped0_iff.
  replace (∅ : envT) with (delete x1 $ delete x2 $ (({[x1 := t1]} ∪ {[x2 := t2]})) : envT); last first.
  { rewrite delete_union delete_singleton right_id delete_singleton_ne // delete_singleton //. }
  iApply (subst_rtyped with "Hv1 [HH Hv2]"); simplify_eq.
  + rewrite delete_union delete_singleton right_id delete_singleton_ne // lookup_singleton //.
  + iApply (subst_rtyped with "Hv2 HH"). rewrite lookup_union lookup_singleton lookup_singleton_ne //.
Qed.