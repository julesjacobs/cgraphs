From diris.multiparty Require Import langdef.
From diris.multiparty Require Import ycombinator.

Definition SendB e1 i e2 := Send 0 e1 i e2.
Definition RecvB e := Recv 0 e.
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

CoFixpoint toM (p : participant) (σ : session_typeB) : session_type :=
  match σ with
  | SendTB n ts σs => SendT n p ts (toM p ∘ σs)
  | RecvTB n ts σs => RecvT n p ts (toM p ∘ σs)
  | EndBT => EndT
  end.

Definition ChanTB σ := ChanT (toM 0 σ).

Lemma SendB_typed Γ1 Γ2 e1 e2 n ts σs i :
  disj Γ1 Γ2 ->
  typed Γ1 e1 (ChanTB (SendTB n ts σs)) ->
  typed Γ2 e2 (ts i) ->
  typed (Γ1 ∪ Γ2) (SendB e1 i e2) (ChanTB (σs i)).
Proof.
  unfold ChanTB. intros.
  eapply (Send_typed _ _ _ _ _ _ (toM 0 ∘ σs)); eauto.
  econstructor; last done.
  constructor. apply session_type_equiv_alt. simpl. done.
Qed.

Lemma RecvB_typed Γ e n ts σs :
  typed Γ e (ChanTB (RecvTB n ts σs)) ->
  typed Γ (RecvB e) (SumNT n (λ i, PairT (ChanTB (σs i)) (ts i))).
Proof.
  unfold ChanTB. intros.
  eapply (Recv_typed _ _ _ _ (toM 0 ∘ σs)); eauto.
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

Definition σsB σ := λ i : fin 2,
  match i with
  | 0%fin => toM 1 σ
  | _ => toM 0 (dual σ)
  end.

CoFixpoint toG σ :=
  match σ with
  | SendTB n ts σs => Message n 0 1 ts (toG ∘ σs)
  | RecvTB n ts σs => Message n 1 0 ts (toG ∘ σs)
  | EndTB => EndG
  end.

CoInductive global_type_equiv : Equiv global_type :=
  | gte_Message n p q ts1 ts2 Gs1 Gs2 :
    ts1 ≡ ts2 -> Gs1 ≡ Gs2 ->
    Message n p q ts1 Gs1 ≡ Message n p q ts2 Gs2
  | gte_EndG : EndG ≡ EndG.
Existing Instance global_type_equiv.

Axiom global_type_extensionality : ∀ G1 G2 : global_type, G1 ≡ G2 -> G1 = G2.

Definition global_type_id (G : global_type) : global_type :=
  match G with
  | Message n p q ts Gs => Message n p q ts Gs
  | EndG => EndG
  end.

Lemma global_type_id_id (G : global_type) :
  global_type_id G = G.
Proof.
  by destruct G.
Qed.

Lemma global_type_equiv_alt (G1 G2 : global_type) :
  global_type_id G1 ≡ global_type_id G2 -> G1 ≡ G2.
Proof.
  intros.
  rewrite -(global_type_id_id G1).
  rewrite -(global_type_id_id G2).
  done.
Defined.

Lemma global_type_reflexive : Reflexive (≡@{global_type}).
Proof.
  cofix IH. intros []; constructor; done.
Defined.

Lemma global_type_symmetric : Symmetric (≡@{global_type}).
Proof.
  cofix IH. intros [] []; intros; try solve [constructor || inversion H].
  inversion H; simplify_eq. constructor; eauto.
Defined.

Lemma global_type_transitive : Transitive (≡@{global_type}).
Proof.
  cofix IH. intros ???[].
  - remember (Message n p q ts2 Gs2).
    inversion 1; simplify_eq.
    constructor; etrans; eauto.
  - inversion 1. constructor.
Defined.

Global Instance global_type_equivalence : Equivalence (≡@{global_type}).
Proof.
  split.
  - apply global_type_reflexive.
  - apply global_type_symmetric.
  - apply global_type_transitive.
Qed.

Lemma projGM_0 σ : proj 0 (toG σ) (toM 1 σ).
Proof.
  revert σ. cofix IH; intros [].
  - assert (toM 1 (SendTB n t s) = SendT n 1 t (toM 1 ∘ s)) as ->.
    { apply session_type_extensionality. apply session_type_equiv_alt; simpl. done. }
    assert (toG (SendTB n t s) = Message n 0 1 t (toG ∘ s)) as ->.
    { apply global_type_extensionality. apply global_type_equiv_alt; simpl. done. }
    econstructor; first lia. simpl.
    intro. apply IH.
  - assert (toM 1 (RecvTB n t s) = RecvT n 1 t (toM 1 ∘ s)) as ->.
    { apply session_type_extensionality. apply session_type_equiv_alt; simpl. done. }
    assert (toG (RecvTB n t s) = Message n 1 0 t (toG ∘ s)) as ->.
    { apply global_type_extensionality. apply global_type_equiv_alt; simpl. done. }
    econstructor; first lia. simpl.
    intro. apply IH.
  - assert (toM 1 EndTB = EndT) as ->.
    { apply session_type_extensionality. apply session_type_equiv_alt; simpl. done. }
    assert (toG EndTB = EndG) as ->.
    { apply global_type_extensionality. apply global_type_equiv_alt; simpl. done. }
    econstructor. inversion 1.
Qed.

Lemma projGM_1 σ : proj 1 (toG σ) (toM 0 (dual σ)).
Proof.
  revert σ. cofix IH; intros [].
  - assert (toM 0 (dual (SendTB n t s)) = RecvT n 0 t (toM 0 ∘ dual ∘ s)) as ->.
    { apply session_type_extensionality. apply session_type_equiv_alt; simpl. done. }
    assert (toG (SendTB n t s) = Message n 0 1 t (toG ∘ s)) as ->.
    { apply global_type_extensionality. apply global_type_equiv_alt; simpl. done. }
    econstructor; first lia. simpl.
    intro. apply IH.
  - assert (toM 0 (dual (RecvTB n t s)) = SendT n 0 t (toM 0 ∘ dual ∘ s)) as ->.
    { apply session_type_extensionality. apply session_type_equiv_alt; simpl. done. }
    assert (toG (RecvTB n t s) = Message n 1 0 t (toG ∘ s)) as ->.
    { apply global_type_extensionality. apply global_type_equiv_alt; simpl. done. }
    econstructor; first lia. simpl.
    intro. apply IH.
  - assert (toM 0 (dual EndTB) = EndT) as ->.
    { apply session_type_extensionality. apply session_type_equiv_alt; simpl. done. }
    assert (toG EndTB = EndG) as ->.
    { apply global_type_extensionality. apply global_type_equiv_alt; simpl. done. }
    econstructor. inversion 1.
Qed.

Lemma not_occurs_in_toG p σ : p >= 2 -> ¬ occurs_in p (toG σ).
Proof.
  intros Hp Hoc. remember (toG σ).
  revert σ Heqg. induction Hoc; intros [];
  rewrite <-(global_type_id_id (toG _)); simpl; intros; simplify_eq; try lia; eauto.
Qed.

Lemma projGM_other σ p : p >= 2 -> proj p (toG σ) EndT.
Proof.
  intros Hp. constructor. by apply not_occurs_in_toG.
Qed.

Lemma σsB_consistent σ : consistent 2 (σsB σ).
Proof.
  exists (toG σ). split.
  - intros. unfold σsB. dependent inversion i; simpl.
    + subst. apply projGM_0.
    + subst. inv_fin t; last (intros j; inversion j). simpl. apply projGM_1.
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

Lemma toM_relabel p q σ : toM p σ ≡ relabelT (const p) (toM q σ).
Proof.
  revert σ. cofix IH. intros [];
  apply session_type_equiv_alt; simpl; constructor; try done; intro; apply IH.
Qed.

Lemma ForkB_typed Γ σ e :
  typed Γ e (FunT (ChanTB (dual σ)) UnitT) ->
  typed Γ (ForkB e) (ChanTB σ).
Proof.
  unfold ChanTB, ForkB. intros.
  do 2 econstructor; last first.
  { eapply (Spawn_typed _ _ (const Γ) _ (σsB σ));
    eauto using disj_union_1, σsB_consistent. }
  constructor.
  apply toM_relabel.
Qed.


Require Import String.
Open Scope string_scope.


Lemma Var_typed' x t :
  typed {[ x := t ]} (Var x) t.
Proof.
  replace ({[ x := t ]}) with ((∅ : envT) ∪ {[ x := t ]}).
  - eapply Var_typed; admit.
  - admit.
Admitted.

(* Define pi-calculus style send+let *)
Definition sendC x msg cont :=
  Let x (SendB (Var x) 0 msg) cont.

(* Define a send type with only 1 choice branch *)
Definition SendTB' t r := SendTB 1 (fun _ => t) (fun _ => r).

(*
Γ1 ⊢ msg : t           Γ2, x : r ⊢ cont : t'
--------------------------------------------
  Γ1, Γ2, x : !t.r ⊢ sendC x msg cont : t'
*)
Lemma sendC_typed Γ1 Γ2 x msg cont t t' r :
  disj Γ1 Γ2 ->
  Γ1 !! x = None ->
  Γ2 !! x = None ->
  typed Γ1 msg t ->
  typed (Γ2 ∪ {[ x := ChanTB r ]}) cont t' ->
  typed (({[ x := ChanTB (SendTB' t r) ]} ∪ Γ1) ∪ Γ2)
        (sendC x msg cont) t'.
Proof.
  intros Hdisj H1 H2 Ht1 Ht2.
  unfold sendC.
  eapply (Let_typed _ _ _ _ (ChanTB r) t').
  - admit.
  - done.
  - eapply (SendB_typed _ _ _ _ 1 (fun _ => t) (fun _ => r) 0%fin).
    + admit.
    + eapply Var_typed'.
    + done.
  - done.
Admitted.


Definition recvC x msgVar cont :=
  MatchSumN 1 (RecvB (Var x))
    (λ i, (Lam "X"
      (LetProd x msgVar (Var "X") cont))).

Definition RecvTB' t r := RecvTB 1 (fun _ => t) (fun _ => r).

Lemma recvC_typed Γ x msgVar cont t t' r :
  x ≠ msgVar ∧ x ≠ "X" ->
  Γ !! "X" = None -> (* Macros don't work well in linear setting because we forbit shadowing *)
  Γ !! x = None ->
  Γ !! msgVar = None ->
  typed (Γ ∪ {[ x := ChanTB r ]} ∪ {[ msgVar := t ]}) cont t' ->
  typed ({[ x := ChanTB (RecvTB' t r) ]} ∪ Γ)
    (recvC x msgVar cont) t'.
Proof.
  intros Hd H0 H1 H2 Ht.
  unfold recvC.
  eapply MatchSumN_typed.
  - admit.
  - lia.
  - eapply RecvB_typed.
    eapply Var_typed'.
  - intro.
    eapply Lam_typed.
    + done.
    + replace (Γ ∪ {["X" := PairT (ChanTB r) t]}) with
              ({["X" := PairT (ChanTB r) t]} ∪ Γ) by admit.
      eapply LetProd_typed.
      * admit.
      * admit.
      * admit.
      * admit.
      * eapply Var_typed'.
      * done.
Admitted.


Definition msg := Val (NatV 0).

Definition example1 : expr :=
  Let "c" (ForkB (Lam "c'"
      (sendC "c'" msg ((CloseB (Var "c'"))))))
    (recvC "c" "m" (CloseB (Var "c"))).

Lemma example_typed :
  typed (∅ ∪ ∅) example1 UnitT.
Proof.
  unfold example1.
  eapply (Let_typed _ _ _ _ (ChanTB (RecvTB' NatT EndTB))).
  - admit.
  - admit.
  - eapply ForkB_typed.
    eapply Lam_typed. admit.
    replace (((∅ : envT) ∪ {["c'" := ChanTB (dual (RecvTB' NatT EndTB))]})) with
      (({["c'" := ChanTB (SendTB' NatT EndTB)]} ∪ ∅ : envT) ∪ ∅) by admit.
    eapply sendC_typed.
    admit. admit. admit. admit. admit.
  - admit.
Admitted.


(*
y : ((t1 -> t2) -> (t1 -> t2)) -> (t1 -> t2)

Below:

y : ((t -> unit) -> (t -> unit)) -> (t -> unit)
*)


(*

loop : (t -> t) -> (t -> unit)

loop f x =
  let x' = f x in
  loop f x'

loop f = Y (λ rec, λ x,
            let x' = f x in
            rec x')

*)

Definition loop e :=
  UApp y (ULam "rec" (ULam "x" (UApp (Var "rec") (UApp e (Var "x"))))).


Definition example2 : expr :=
  Let "c" (ForkB (loop (ULam "c'" (SendB (Var "c'") 0 msg))))
    (Var "c").