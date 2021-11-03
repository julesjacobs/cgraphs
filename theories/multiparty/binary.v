From diris.multiparty Require Import langdef.

Definition SendB e1 i e2 := Send 0 e1 i e2.
Definition RecvB e1 := Recv 0 e1.
Definition ForkB e1 := Spawn 1 (λ _, e1).
Definition CloseB e1 := Close e1.

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
  | SendTB n ts σs => SendT n 0 ts (toM ∘ σs)
  | RecvTB n ts σs => RecvT n 0 ts (toM ∘ σs)
  | EndBT => EndT
  end.

Definition ChanTB σ := ChanT (toM σ).

Lemma SendB_typed Γ1 Γ2 e1 e2 n t r i :
  disj Γ1 Γ2 ->
  typed Γ1 e1 (ChanTB (SendTB n t r)) ->
  typed Γ2 e2 (t i) ->
  typed (Γ1 ∪ Γ2) (SendB e1 (fin_to_nat i) e2) (ChanTB (r i)).
Proof.
Admitted.

Lemma RecvB_typed Γ e n t r :
  typed Γ e (ChanTB (RecvTB n t r)) ->
  typed Γ (RecvB e) (SumNT n (λ i, PairT (ChanTB (r i)) (t i))).
Proof.
Admitted.

Lemma CloseB_typed Γ e :
  typed Γ e (ChanTB EndTB) ->
  typed Γ (CloseB e) UnitT.
Proof.
Admitted.

Lemma ForkB_typed Γ ct e :
  typed Γ e (FunT (ChanTB (dual ct)) UnitT) ->
  typed Γ (ForkB e) (ChanTB ct).
Proof.
Admitted.