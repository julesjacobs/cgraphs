From iris.proofmode Require Import tactics.
Ltac inv H := inversion H; clear H; simplify_eq; simpl in *.

Inductive ty :=
  | T2 : ty
  | TVar : nat -> ty (* De Bruijn so that we don't need to deal with α-equivalence *)
  | TFun : ty -> ty -> ty
  | TForall : ty -> ty.

Inductive expr :=
  | E2 : bool -> expr
  | EVar : string -> expr
  | ELam : string -> ty -> expr -> expr
  | EApp : expr -> expr -> expr
  | ETLam : expr -> expr
  | ETApp : expr -> ty -> expr.

Notation envT := (gmap string ty).
Notation env := (gmap string expr).

Inductive is_type : nat -> ty -> Prop :=
  | T2_is_type n : is_type n T2
  | Var_is_type n k : k < n -> is_type n (TVar k)
  | Fun_is_type n a b : is_type n a -> is_type n b -> is_type n (TFun a b)
  | Forall_is_type n a : is_type (n+1) a -> is_type n (TForall a).

Lemma is_type_mono n k t :
  is_type n t -> n ≤ k -> is_type k t.
Proof.
  intros H. revert k.
  induction H; intros;
  constructor; eauto with lia.
Qed.





(* Can only substitute closed types *)
Fixpoint ty_subst (s : nat -> ty) t :=
  match t with
  | T2 => T2
  | TVar n' => if decide (n' = n) then x
               else TVar (if decide (n' < n) then n' else n' - 1)
  | TFun t1 t2 => TFun (ty_subst t1 n x) (ty_subst t2 n x)
  | TForall t => TForall (ty_subst t (n + 1) x)
  end.

(* Instead of substituting n first and then k,
   we wan to substitute k first and then n.
   This function returns the new indices n',k' that we then
   have to substitute at. *)
Definition comm_debruijn n k :=
  if decide (n = k) then (n,k+1)
  else if decide (n < k) then (n,k+1)
  else (n-1,k).

Lemma ty_subst_closed a b n k :
  is_type n b -> n ≤ k -> ty_subst b k a = b.
Proof.
  intros H. revert k. induction H; intros; simpl;
  rewrite ?IHis_type ?IHis_type1 ?IHis_type2;
  try repeat case_decide; (done || lia).
Qed.

Lemma ty_subst_commute a b x k n :
  is_type 0 a -> is_type 0 b ->
  ty_subst (ty_subst x n b) k a =
  ty_subst (ty_subst x (comm_debruijn n k).2 a) (comm_debruijn n k).1 b.
Proof.
  intros Ha Hb. revert n k. induction x; intros; simpl.
  - done.
  - unfold comm_debruijn.
    repeat (case_decide; subst; simpl in *; try (done||lia));
    erewrite ty_subst_closed; eauto; lia.
  - erewrite IHx1; eauto.
    erewrite IHx2; eauto.
  - erewrite IHx. unfold comm_debruijn.
    repeat case_decide; simpl; repeat (done || lia || f_equal).
Qed.

Lemma ty_subst_is_type n k t x :
  k < n -> is_type 0 x -> is_type n t ->
  is_type (n-1) (ty_subst t k x).
Proof.
  intros Hk Hx Ht. revert k Hk.
  induction Ht; simpl; intros; subst.
  - constructor.
  - repeat case_decide; subst; try (constructor;lia).
    eauto using is_type_mono with lia.
  - constructor; eauto.
  - constructor.
    assert (n - 1 + 1 = n + 1 - 1) as -> by lia.
    eapply IHHt. lia.
Qed.

Fixpoint weaken (t : ty) n :=
  match t with
  | T2 => T2
  | TVar k => TVar (if decide (n ≤ k) then k+1 else k)
  | TFun t1 t2 => TFun (weaken t1 n) (weaken t2 n)
  | TForall t => TForall (weaken t (n+1))
  end.

Lemma is_type_weaken t n k :
  is_type n t -> is_type (n+1) (weaken t k).
Proof.
  intros H. revert k. induction H; intros;
  simpl; constructor; eauto.
  case_decide; lia.
Qed.

Lemma subst_weaken t v k :
  ty_subst (weaken t k) k v = t.
Proof.
  revert k; induction t; intros; simpl;
  rewrite ?IHt ?IHt1 ?IHt2; try done.
  repeat case_decide; eauto; try lia.
  f_equal; lia.
Qed.

Lemma weaken_subst t k v n :
  weaken (ty_subst t k v) n = ty_subst (weaken t _) _ v

Definition weaken_Γ (Γ : envT) n := (λ t, weaken t n) <$> Γ.

Inductive typed : nat -> envT -> expr -> ty -> Prop :=
  | E2_typed n Γ b :
      typed n Γ (E2 b) T2
  | EVar_typed n Γ x t :
      Γ !! x = Some t -> typed n Γ (EVar x) t
  | ELam_typed n Γ x e a b :
      typed n (<[ x := a ]> Γ) e b ->
      typed n Γ (ELam x a e) (TFun a b)
  | EApp_typed n Γ e1 e2 a b :
      typed n Γ e1 (TFun a b) ->
      typed n Γ e2 a ->
      typed n Γ (EApp e1 e2) b
  | ETLam_typed n Γ e t :
      typed (n+1) (weaken_Γ Γ 0) e t ->
      typed n Γ (ETLam e) (TForall t)
  | ETApp_typed n Γ e a b :
      is_type n a ->
      typed n Γ e (TForall b) ->
      typed n Γ (ETApp e a) (ty_subst b 0 a).

Lemma typed_mono_n n k Γ e t :
  typed n Γ e t -> n ≤ k -> typed k Γ e t.
Proof.
  intros H. revert k. induction H; intros;
  econstructor; eauto using is_type_mono with lia.
Qed.

Lemma typed_mono_Γ n Γ Γ' e t :
  typed n Γ e t -> Γ ⊆ Γ' -> typed n Γ' e t.
Proof.
  intros H. revert Γ'. induction H; intros;
  econstructor; eauto using lookup_weaken.
  apply IHtyped. apply insert_mono. done.
  apply IHtyped. unfold weaken_Γ.
  apply map_fmap_mono. done.
Qed.

Fixpoint ty_subst_expr e n x :=
  match e with
  | E2 b => E2 b
  | EVar x => EVar x
  | ELam x' t e => ELam x' (ty_subst t n x) (ty_subst_expr e n x)
  | EApp e1 e2 => EApp (ty_subst_expr e1 n x) (ty_subst_expr e2 n x)
  | ETLam e => ETLam (ty_subst_expr e (n+1) x)
  | ETApp e1 t => ETApp (ty_subst_expr e1 n x) (ty_subst t n x)
  end.

Definition ty_subst_Γ (Γ : envT) n x := (λ t, ty_subst t n x) <$> Γ.

Lemma ty_subst_typed n a Γ e t k :
  k < n -> is_type 0 a -> typed n Γ e t ->
  typed (n-1) (ty_subst_Γ Γ k a) (ty_subst_expr e k a) (ty_subst t k a).
Proof.
  intros Hk Hta Htyped. revert k Hk.
  induction Htyped; intros.
  - constructor.
  - constructor. unfold ty_subst_Γ.
    rewrite lookup_fmap. simpl. rewrite H. done.
  - simpl. econstructor.
    assert (<[x:=ty_subst a0 k a]> (ty_subst_Γ Γ k a) =
            ty_subst_Γ (<[x:=a0]> Γ) k a) as ->; eauto.
    { unfold ty_subst_Γ. rewrite fmap_insert. done. }
  - econstructor; eauto.
  - simpl. econstructor. admit.
  - simpl. rewrite ty_subst_commute; [|admit..].
    unfold comm_debruijn; repeat case_decide; try lia; subst; simpl.
    constructor.
Admitted.

Fixpoint expr_subst e x v :=
  match e with
  | E2 b => E2 b
  | EVar x' => if decide (x = x') then v else EVar x'
  | ELam x' t e =>
      if decide (x = x') then ELam x' t e
      else ELam x' t (expr_subst e x v)
  | EApp e1 e2 => EApp (expr_subst e1 x v) (expr_subst e2 x v)
  | ETLam e => ETLam (expr_subst e x v)
  | ETApp e t => ETApp (expr_subst e x v) t
  end.

Inductive val : expr -> Prop :=
  | E2_val b : val (E2 b)
  | ELam_val x t e : val (ELam x t e).

Lemma empty_subseteq' (Γ : envT) : ∅ ⊆ Γ.
Proof.
  intro. rewrite lookup_empty. destruct (Γ !! i); done.
Qed.

Lemma expr_subst_typed Γ x tv e t v n :
  Γ !! x = Some tv -> val v -> typed 0 ∅ v tv ->
  typed n Γ e t -> typed n (delete x Γ) (expr_subst e x v) t.
Proof.
  intros HΓ Hv Htv Ht.
  induction Ht; simpl; try solve [econstructor; eauto].
  - case_decide.
    + subst. rewrite HΓ in H. simplify_eq.
      eapply (typed_mono_n 0); last lia.
      eapply typed_mono_Γ; first done.
      apply empty_subseteq'.
    + constructor. rewrite lookup_delete_ne; done.
  - case_decide.
    + subst. econstructor. rewrite insert_delete. done.
    + econstructor. rewrite <-delete_insert_ne; last done.
      apply IHHt; try done. rewrite lookup_insert_ne; done.
Qed.