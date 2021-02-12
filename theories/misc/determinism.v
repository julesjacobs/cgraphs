
Ltac cnv := match goal with
| [C : ctx ?k, H : ?k _ = Val _ |- _] => apply ctx_not_val in H as (-> & ->); eauto
| [C : ctx ?k, H : Val _ = ?k _ |- _] => symmetry in H; apply ctx_not_val in H as (-> & ->); eauto
end; match goal with
[H : head_step (Val _) _ _ _ |- _] => inversion H
end.


Lemma head_step_deterministic e s e1 e2 s1 s2 :
    head_step e s e1 s1 -> head_step e s e2 s2 -> e1 = e2 ∧ s1 = s2.
Proof.
    intros H1 H2.
    induction H1; inversion H2; simplify_eq; eauto.
Qed.

Lemma ctx_headstep_deterministic k1 e1 k2 e2 s : ctx k1 -> ctx k2 ->
  k1 e1 = k2 e2 -> (∃ e1' s', head_step e1 s e1' s') -> (∃ e2' s', head_step e2 s e2' s') ->
  k1 = k2 ∧ e1 = e2.
Proof.
  intros C1.
  revert k2.
  induction C1 as [|C1' k1']; intros k2 C2 Heq.
  - induction C2; eauto.
    intros (e1' & s1 & Hs1) (e2' & s2 & Hs2).
    inversion H; simplify_eq; simpl in *; inversion Hs1; simplify_eq; cnv.
  - induction C2.
    + intros (e1' & s1 & Hs1) (e2' & s2 & Hs2).
      inversion H; simplify_eq; simpl in *; inversion Hs2; simplify_eq; cnv.
    + inversion H; inversion H0; simplify_eq;
      try (intros; assert (k1' = k2 ∧ e1 = e2) as (-> & ->); eauto);
      destruct H1 as (e1' & s1' & Hs1); destruct H2 as (e2' & s2' & Hs2); try cnv.
Qed.

Inductive ctx_step : expr -> heap -> expr -> heap -> Prop :=
    | Ctx_step : ∀ k e1 e2 s1 s2,
        ctx k -> head_step e1 s1 e2 s2 -> ctx_step (k e1) s1 (k e2) s2.

Lemma ctx_step_deterministic e s e1 e2 s1 s2 :
    ctx_step e s e1 s1 -> ctx_step e s e2 s2 -> e1 = e2 ∧ s1 = s2.
Proof.
    intros H1 H2. inversion H1. inversion H2. simplify_eq.
    assert (k = k0 ∧ e0 = e4) as (-> & ->) by (eapply ctx_headstep_deterministic; eauto).
    assert (e3 = e5 ∧ s1 = s2) as (-> & ->) by (eapply head_step_deterministic; eauto); eauto.
Qed.
