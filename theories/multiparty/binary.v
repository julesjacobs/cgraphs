From diris.multiparty Require Import langdef.

Definition SendB e1 i e2 := Send 1 e1 i e2.
Definition RecvB e := Recv 1 e.
Definition ForkB e := Relabel (const 0) (Spawn 1 (const e)).
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

Section helpers.
  (* Helper definitions and proofs for the binary typing rules. *)
  Definition session_typeB_id (σ : session_typeB) : session_typeB :=
    match σ with
    | SendTB n ts σs => SendTB n ts σs
    | RecvTB n ts σs => RecvTB n ts σs
    | EndTB => EndTB
    end.

  Lemma session_typeB_id_id (σ : session_typeB) :
    session_typeB_id σ = σ.
  Proof.
    by destruct σ.
  Qed.

End helpers.

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

Lemma ForkB_typed Γ ct e :
  typed Γ e (FunT (ChanTB (dual ct)) UnitT) ->
  typed Γ (ForkB e) (ChanTB ct).
Proof.
  unfold ChanTB, ForkB. intros.
  econstructor.

Admitted.