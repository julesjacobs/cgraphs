From cgraphs.lambdabar Require Export langdef.
From cgraphs.lambdabar Require Export rtypesystem.


(* Session types *)

CoInductive session_type :=
  | SendTB n : (fin n -> type) -> (fin n -> session_type) -> session_type
  | RecvTB n : (fin n -> type) -> (fin n -> session_type) -> session_type
  | EndTB : session_type.


Global Instance finvec_equiv `{Equiv T} n : Equiv (fin n -> T) := λ f g, ∀ i, f i ≡ g i.

CoInductive session_type_equiv : Equiv session_type :=
  | cteq_EndT : EndTB ≡ EndTB
  | cteq_SendT n t1 t2 f1 f2 : t1 ≡ t2 -> f1 ≡ f2 -> SendTB n t1 f1 ≡ SendTB n t2 f2
  | cteq_RecvT n t1 t2 f1 f2 : t1 ≡ t2 -> f1 ≡ f2 -> RecvTB n t1 f1 ≡ RecvTB n t2 f2.
Global Existing Instance session_type_equiv.

Axiom session_type_extensionality : ∀ σ1 σ2 : session_type, σ1 ≡ σ2 -> σ1 = σ2.

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

CoFixpoint dual (σ : session_type) : session_type :=
  match σ with
  | SendTB n ts σs => RecvTB n ts (dual ∘ σs)
  | RecvTB n ts σs => SendTB n ts (dual ∘ σs)
  | EndBT => EndTB
  end.

(* Interpretation of session types into linear lambda calculus types *)

CoFixpoint toL (σ : session_type) : type :=
  match σ with
  | SendTB n ts σs => FunT Lin (SumT n (λ i, PairT (toL (dual $ σs i)) (ts i))) UnitT
  | RecvTB n ts σs => FunT Lin UnitT (SumT n (λ i, PairT (toL (σs i)) (ts i)))
  | EndBT => FunT Lin UnitT UnitT
  end.

(* Session type operations in terms of binary barriers *)

Definition SendB e1 i e2 :=
    LetPair (Pair e1 e2) (Fun "x" (Fun "y"
      (Fork (Fun "z" (App (Var "x") (Sum i (Pair (Var "z") (Var "y")))))))).
Definition RecvB e := App e Unit.
Definition ForkB e := Fork e.
Definition CloseB (e : expr) := App e Unit.


(* Helper definitions and lemmas *)

Definition session_type_id (σ : session_type) : session_type :=
  match σ with
  | SendTB n ts σs => SendTB n ts σs
  | RecvTB n ts σs => RecvTB n ts σs
  | EndBT => EndTB
  end.

Lemma session_type_id_id (σ : session_type) :
  session_type_id σ = σ.
Proof.
  by destruct σ.
Qed.

Lemma global_type_eq_alt (σ1 σ2 : session_type) :
  session_type_id σ1 = session_type_id σ2 -> σ1 = σ2.
Proof.
  rewrite !session_type_id_id //.
Defined.

Definition type_id (t : type) :=
  match t with
  | FunT l t1 t2 => FunT l t1 t2
  | UnitT => UnitT
  | PairT t1 t2 => PairT t1 t2
  | SumT n ts => SumT n ts
  end.

Lemma type_id_id (t : type) :
  type_id t = t.
Proof.
  by destruct t.
Qed.

Lemma env_split_left Γ :
  env_split Γ Γ ∅.
Proof.
  unfold env_split. rewrite right_id. split; eauto.
  unfold disj. intros ???. smap.
Qed.

Definition toL1 (σ : session_type) : type :=
  match σ with
  | SendTB n ts σs => SumT n (λ i, PairT (toL (dual $ σs i)) (ts i))
  | RecvTB n ts σs => UnitT
  | EndBT => UnitT
  end.

Lemma session_type_equiv_alt (σ1 σ2 : session_type) :
  session_type_id σ1 ≡ session_type_id σ2 -> σ1 ≡ σ2.
Proof.
  intros.
  rewrite -(session_type_id_id σ1).
  rewrite -(session_type_id_id σ2).
  done.
Defined.

Lemma dual_dual σ : dual (dual σ) = σ.
Proof.
  apply session_type_extensionality.
  apply session_type_equiv_alt.
  revert σ. cofix IH. intros []; simpl; constructor; try done; intros i;
  apply session_type_equiv_alt; apply IH.
Qed.

Lemma toL_toL1 σ :
  toL σ = FunT Lin (toL1 σ) (toL1 (dual σ)).
Proof.
  rewrite -{1}(type_id_id (toL _)).
  destruct σ; simpl; eauto; simplify_eq.
  f_equal. f_equal. apply functional_extensionality.
  intros x. f_equal. rewrite dual_dual. done.
Qed.

Lemma toL_toL_dual_split σ :
  ∃ t1 t2, toL σ = FunT Lin t1 t2 ∧ toL (dual σ) = FunT Lin t2 t1.
Proof.
  exists (toL1 σ), (toL1 (dual σ)).
  rewrite toL_toL1 //. split; eauto.
  rewrite toL_toL1 dual_dual //.
Qed.



Lemma env_bind_notin x Γ t :
  Γ !! x = None ->
  env_bind (<[ x := t ]> Γ) x t Γ.
Proof.
  intros H.
  rewrite /env_bind H; split; simp.
Qed.

Lemma env_split_disjoint Γ Γ1 Γ2 :
  Γ = Γ1 ∪ Γ2 -> Γ1 ##ₘ Γ2 -> env_split Γ Γ1 Γ2.
Proof.
  intros -> H.
  rewrite /env_split. split; eauto.
  rewrite /disj.  intros i ??.
  specialize (H i).
  destruct (Γ1 !! i) eqn:E, (Γ2 !! i) eqn:F; rewrite ?E ?F; simp.
Qed.

Lemma env_var_singleton x t :
  env_var {[ x := t ]} x t.
Proof.
  rewrite /env_var. exists ∅.
  split; eauto using env_unr_empty.
Qed.

Lemma env_var_singleton_eq x t1 t2 :
  t1 = t2 -> env_var {[ x := t1 ]} x t2.
Proof.
  intros ->. apply env_var_singleton.
Qed.

(* Admissibility of typing rules *)

(* Prove typing rule for ForkB admissible *)

Lemma ForkB_typed Γ σ e :
  typed Γ e (FunT Lin (toL (dual σ)) UnitT) ->
  typed Γ (ForkB e) (toL σ).
Proof.
  intros H. rewrite /ForkB.
  destruct (toL_toL_dual_split σ) as [t1 [t2 [H1 H2]]].
  rewrite H1.
  eapply Fork_typed.
  rewrite -H2.
  exact H.
Qed.

(* Prove typing rule for SendB admissible *)

Lemma SendB_typed Γ Γ1 Γ2 e1 e2 n ts σs i :
  env_split Γ Γ1 Γ2 ->
  typed Γ1 e1 (toL (SendTB n ts σs)) ->
  typed Γ2 e2 (ts i) ->
  typed Γ (SendB e1 i e2) (toL (σs i)).
Proof.
  intros Hsplit H1 H2.
  rewrite /SendB.
  eapply LetPair_typed.
  { eapply env_split_left. } { eauto using typed. }
  eapply Fun_typed.
  { eapply env_bind_notin. smap. } { simp. }
  eapply Fun_typed.
  { eapply env_bind_notin. smap. } { simp. }
  eapply ForkB_typed.
  eapply Fun_typed.
  { eapply env_bind_notin. smap. } { simp. }
  eapply (App_typed _ {[ "x" := _ ]} {[ "y" := _; "z" := _ ]}).
  1: {
    eapply env_split_disjoint; last solve_map_disjoint.
    apply map_eq. intros x. smap. }
  2: {
    eapply (Sum_typed _ _ (λ i, PairT (toL (dual (σs i))) (ts i))).
    eapply (Pair_typed _ {[ "z" := _ ]} {[ "y" := _ ]}).
    + eapply env_split_disjoint; last solve_map_disjoint.
      apply map_eq. intros x. smap.
    + eapply Var_typed. eapply env_var_singleton.
    + eapply Var_typed. eapply env_var_singleton.
  }
  eapply Var_typed.
  eapply env_var_singleton_eq.
  rewrite -(type_id_id (toL _)). simpl.
  done.
Qed.

(* Prove typing rule for RecvB admissible *)

Lemma RecvB_typed Γ e n ts σs :
  typed Γ e (toL (RecvTB n ts σs)) ->
  typed Γ (RecvB e) (SumT n (λ i, PairT (toL (σs i)) (ts i))).
Proof.
  intros H.
  rewrite /RecvB.
  rewrite -(type_id_id (toL _)) /= in H.
  eapply App_typed; eauto using typed, env_unr_empty, env_split_left.
Qed.

(* Prove typing rule for CloseB admissible *)

Lemma CloseB_typed Γ e :
  typed Γ e (toL EndTB) ->
  typed Γ (CloseB e) UnitT.
Proof.
  intros H. rewrite /CloseB.
  rewrite -(type_id_id (toL _)) // in H. simpl in *.
  eapply App_typed; eauto using env_split_left, typed, env_unr_empty.
Qed.