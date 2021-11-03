From diris.multiparty Require Import langdef.

Definition SendB e1 i e2 := Send 1 e1 i e2.
Definition RecvB e := Recv 1 e.
Definition ForkB e := Relabel (const 1) (Spawn 1 (const e)).
Definition CloseB e := Close e.

CoInductive session_typeB :=
  | SendTB n : (fin n -> type) -> (fin n -> session_typeB) -> session_typeB
  | RecvTB n : (fin n -> type) -> (fin n -> session_typeB) -> session_typeB
  | EndTB : session_typeB.

CoFixpoint dual (σ : session_typeB) : session_typeB :=
  match σ with
  | SendTB n ts σs => RecvTB n ts (dual ∘ σs)
  | RecvTB n ts σs => SendTB n ts (dual ∘ σs)
  | EndBT => EndTB
  end.

CoFixpoint toM (σ : session_typeB) : session_type :=
  match σ with
  | SendTB n ts σs => SendT n 1 ts (toM ∘ σs)
  | RecvTB n ts σs => RecvT n 1 ts (toM ∘ σs)
  | EndBT => EndT
  end.

Definition ChanTB σ := ChanT (toM σ).

Lemma SendB_typed Γ1 Γ2 e1 e2 n ts σs i :
  disj Γ1 Γ2 ->
  typed Γ1 e1 (ChanTB (SendTB n ts σs)) ->
  typed Γ2 e2 (ts i) ->
  typed (Γ1 ∪ Γ2) (SendB e1 i e2) (ChanTB (σs i)).
Proof.
  unfold ChanTB. intros.
  eapply (Send_typed _ _ _ _ _ _ (toM ∘ σs)); eauto.
  econstructor; last done.
  constructor. apply session_type_equiv_alt. simpl. done.
Qed.

Lemma RecvB_typed Γ e n ts σs :
  typed Γ e (ChanTB (RecvTB n ts σs)) ->
  typed Γ (RecvB e) (SumNT n (λ i, PairT (ChanTB (σs i)) (ts i))).
Proof.
  unfold ChanTB. intros.
  eapply (Recv_typed _ _ _ _ (toM ∘ σs)); eauto.
  econstructor; last done.
  constructor. apply session_type_equiv_alt. simpl. done.
Qed.

Lemma CloseB_typed Γ e :
  typed Γ e (ChanTB EndTB) ->
  typed Γ (CloseB e) UnitT.
Proof.
  unfold ChanTB. intros.
  constructor. econstructor; last done.
  constructor. apply session_type_equiv_alt. simpl. done.
Qed.

Definition σsB σ := λ i : fin 2, match i with 0%fin => toM σ | _ => toM (dual σ) end.

Print global_type.

CoFixpoint toG σ :=
  match σ with
  | SendTB n ts σs => Message n 0 1 ts (toG ∘ σs)
  | EndBT => EndG
  end.

Lemma projGM_0 σ : proj 0 (toG σ) (toM σ).
Proof.
Admitted.

Lemma projGM_1 σ : proj 1 (toG σ) (toM (dual σ)).
Proof.
Admitted.

Lemma projGM_other σ p : p >= 2 -> proj p (toG σ) EndT.
Proof.
Admitted.


Lemma σsB_consistent σ : consistent 2 (σsB σ).
Proof.
  exists (toG σ). split.
  - intros. unfold σsB. dependent inversion i; simpl.
    + subst. apply projGM_0.
    + subst. inv_fin t; last (intros j; inversion j). apply projGM_1.
  - intros i Hi. apply projGM_other. done.
Qed.

Lemma disj_union_1 Γ : disj_union 1 Γ (const Γ).
Proof.
  constructor; eauto.
  intros p q Hpq. exfalso. apply Hpq.
  clear Hpq. inv_fin p.
  - inv_fin q; eauto. intros i. inv_fin i.
  - intros i. inv_fin i.
  Unshelve. exact 0%fin.
Qed.

Lemma toM_relabel_1 σ : toM σ ≡ relabelT (const 1) (toM σ).
Proof.
  revert σ. cofix IH. intros [];
  apply session_type_equiv_alt; simpl; constructor; try done; intro; apply IH.
Qe.

Lemma ForkB_typed Γ σ e :
  typed Γ e (FunT (ChanTB (dual σ)) UnitT) ->
  typed Γ (ForkB e) (ChanTB σ).
Proof.
  unfold ChanTB, ForkB. intros.
  do 2 econstructor; last first.
  { eapply (Spawn_typed _ _ (const Γ) _ (σsB σ)); eauto using disj_union_1, σsB_consistent. }
  constructor. apply toM_relabel_1.
Qed.