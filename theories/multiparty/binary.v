From cgraphs.multiparty Require Import langdef.
From cgraphs.multiparty Require Import ycombinator.
From cgraphs.multiparty Require Import globaltypes.

(* Encoding binary session types in MPGV *)
(* ===================================== *)
(* This is section 4 in the paper.  *)


(* Definition of the binary session operations in terms of MPGV's multiparty operations. *)
Definition SendB e1 i e2 := Send 0 e1 i e2.
Definition RecvB e := Recv 0 e.
Definition ForkB e := Relabel (const 1) (Spawn 1 (const e)).
Definition CloseB e := Close e.

(* Definition of binary session types. *)
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

(* Converting a binary session type to multiparty sesion type. *)
CoFixpoint toM (p : participant) (σ : session_typeB) : session_type :=
  match σ with
  | SendTB n ts σs => SendT n p ts (toM p ∘ σs)
  | RecvTB n ts σs => RecvT n p ts (toM p ∘ σs)
  | EndBT => EndT
  end.

Definition ChanTB σ := ChanT (toM 0 σ).


(* We prove that the typing rules for binary session types are admissible. *)
(* These proofs for Send, Recv, and Close are relatively easy. *)
(* The main difficulty is proving the rule for Fork (see below). *)

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

(* Proof of the rule for Fork *)
(* ========================== *)

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
Global Existing Instance global_type_equiv.

(*
  Coq's default notion of equality is not good enough for coinductive types:
   the default equality is syntactic equality and not extensional equality.
   We add an axiom to make equality extensional.
   See https://coq.inria.fr/refman/language/core/coinductive.html:
   "More generally, as in the case of positive coinductive types,
   it is consistent to further identify extensional equality of coinductive
   types with propositional equality"
   Such an axiom is similar to functional extensionality, but for coinductive types.
*)
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
  apply consistent_gt_consistent.
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

(* The Fork rule for binary session types is admissible in MPGV. *)
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