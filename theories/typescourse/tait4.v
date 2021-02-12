From iris.proofmode Require Import tactics.
Ltac inv H := inversion H; clear H; simplify_eq; simpl in *.

Inductive expr :=
  | EUnit : expr
  | EVar : string -> expr
  | ELam : string -> expr -> expr
  | EApp : expr -> expr -> expr
  | EPair : expr -> expr -> expr
  | EProj : bool -> expr -> expr
  | EInj : bool -> expr -> expr
  | EMatch : expr -> expr -> expr -> expr
  | EMatch0 : expr -> expr
  | EZero : expr
  | ESucc : expr -> expr
  | ERec : expr -> expr -> expr -> expr.

Fixpoint subst e x v :=
  match e with
  | EUnit => EUnit
  | EVar x' => if decide (x = x') then v else EVar x'
  | ELam x' e' =>  (* only works for when v is a value *)
      if decide (x = x') then ELam x' e' else ELam x' (subst e' x v)
  | EApp e1 e2 => EApp (subst e1 x v) (subst e2 x v)
  | EPair e1 e2 => EPair (subst e1 x v) (subst e2 x v)
  | EProj b e' => EProj b (subst e' x v)
  | EInj b e' => EInj b (subst e' x v)
  | EMatch e1 e2 e3 => EMatch (subst e1 x v) (subst e2 x v) (subst e3 x v)
  | EMatch0 e' => EMatch0 (subst e' x v)
  | EZero => EZero
  | ESucc e => ESucc (subst e x v)
  | ERec e1 e2 e3 => ERec (subst e1 x v) (subst e2 x v) (subst e3 x v)
  end.

Inductive val : expr -> Prop :=
  | VUnit : val EUnit
  | VPair e1 e2 : val e1 -> val e2 -> val (EPair e1 e2)
  | VLam x e : val (ELam x e)
  | VInj e b : val e -> val (EInj b e)
  | VZero : val EZero
  | VSucc e : val e -> val (ESucc e).

Inductive head_step : expr -> expr -> Prop :=
  | head_step_app x e v :
      val v ->
      head_step (EApp (ELam x e) v) (subst e x v)
  | head_step_proj b v1 v2 :
      val v1 -> val v2 ->
      head_step (EProj b (EPair v1 v2)) (if b then v1 else v2)
  | head_step_match b v e1 e2 :
      val v ->
      head_step (EMatch (EInj b v) e1 e2) (EApp (if b then e1 else e2) v)
  | head_step_rec_1 z f :
      val z -> val f -> head_step (ERec EZero z f) z
  | head_step_rec_2 z f n :
      val n -> val z -> val f -> head_step (ERec (ESucc n) z f) (EApp f (ERec n z f)).


Inductive ctx1 : (expr -> expr) -> Prop :=
  | ctx1_app_l e : ctx1 (λ x, EApp x e)
  | ctx1_app_r v : val v -> ctx1 (λ x, EApp v x)
  | ctx1_pair_l e : ctx1 (λ x, EPair x e)
  | ctx1_pair_r v : val v -> ctx1 (λ x, EPair v x)
  | ctx1_proj b : ctx1 (λ x, EProj b x)
  | ctx1_inj b : ctx1 (λ x, EInj b x)
  | ctx1_match e1 e2 : ctx1 (λ x, EMatch x e1 e2)
  | ctx1_match0 : ctx1 (λ x, EMatch0 x)
  | ctx1_rec_1 e2 e3 : ctx1 (λ x, ERec x e2 e3)
  | ctx1_rec_2 v1 e3 : val v1 -> ctx1 (λ x, ERec v1 x e3)
  | ctx1_rec_3 v1 v2 : val v1 -> val v2 -> ctx1 (λ x, ERec v1 v2 x)
  | ctx1_succ : ctx1 (λ x, ESucc x).

Inductive ctx : (expr -> expr) -> Prop :=
  | ctx_nil : ctx (λ x, x)
  | ctx_cons k1 k2 : ctx1 k1 -> ctx k2 -> ctx (k1 ∘ k2).

Inductive step : expr -> expr -> Prop :=
  | step_head_step k e e' :
      ctx k -> head_step e e' -> step (k e) (k e').

Inductive ty :=
  | TZero : ty
  | TUnit : ty
  | TFun : ty -> ty -> ty
  | TPair : ty -> ty -> ty
  | TSum : ty -> ty -> ty
  | TNat : ty.

Notation env := (gmap string expr).
Notation envT := (gmap string ty).

Inductive typed : envT -> expr -> ty -> Prop :=
  | typed_unit Γ :
      typed Γ EUnit TUnit
  | typed_var Γ x t :
      Γ !! x = Some t -> typed Γ (EVar x) t
  | typed_lam Γ x t1 t2 e :
      typed (<[ x := t1 ]> Γ) e t2 ->
      typed Γ (ELam x e) (TFun t1 t2)
  | typed_app Γ e1 e2 t1 t2 :
      typed Γ e1 (TFun t1 t2) ->
      typed Γ e2 t1 ->
      typed Γ (EApp e1 e2) t2
  | typed_pair Γ t1 t2 e1 e2 :
      typed Γ e1 t1 ->
      typed Γ e2 t2 ->
      typed Γ (EPair e1 e2) (TPair t1 t2)
  | typed_proj Γ t1 t2 e b :
      typed Γ e (TPair t1 t2) ->
      typed Γ (EProj b e) (if b then t1 else t2)
  | typed_inj Γ t1 t2 e (b : bool) :
      typed Γ e (if b then t1 else t2) ->
      typed Γ (EInj b e) (TSum t1 t2)
  | typed_match Γ e1 e2 e3 t1 t2 t :
      typed Γ e1 (TSum t1 t2) ->
      typed Γ e2 (TFun t1 t) ->
      typed Γ e3 (TFun t2 t) ->
      typed Γ (EMatch e1 e2 e3) t
  | typed_match0 Γ e t :
      typed Γ e TZero ->
      typed Γ (EMatch0 e) t
  | typed_zero Γ :
      typed Γ EZero TNat
  | typed_succ Γ e :
      typed Γ e TNat ->
      typed Γ (ESucc e) TNat
  | typed_rec Γ t n z f :
      typed Γ n TNat ->
      typed Γ z t ->
      typed Γ f (TFun t t) ->
      typed Γ (ERec n z f) t.

Definition steps := rtc step.

Lemma ctx1_ctx k :
  ctx1 k -> ctx k.
Proof.
  intros Hk. apply ctx_cons; first done. constructor.
Qed.

Lemma ctx_comp k1 k2 :
  ctx k1 -> ctx k2 -> ctx (k1 ∘ k2).
Proof.
  induction 1; first done.
  intro. apply (ctx_cons k1); auto.
Qed.

Lemma step_ctx k e e' :
  ctx k -> step e e' -> step (k e) (k e').
Proof.
  intros Hk Hs.
  destruct Hs.
  apply (step_head_step (k ∘ k0));
  first apply ctx_comp; done.
Qed.

Lemma steps_ctx k e e' :
  ctx k -> steps e e' -> steps (k e) (k e').
Proof.
  intros Hk Hs.
  induction Hs; first done.
  eapply rtc_transitive; last done.
  apply rtc_once. apply step_ctx; done.
Qed.

Definition ctx_typed k t1 t2 :=
    ∀ e, typed ∅ e t1 -> typed ∅ (k e) t2.

Lemma ctx_typed_typed k t1 t2 e :
  ctx_typed k t1 t2 -> typed ∅ e t1 -> typed ∅ (k e) t2.
Proof.
  intros Hc Ht. apply Hc. done.
Qed.

Lemma typed_ctx1_typed k e t2 :
  ctx1 k -> typed ∅ (k e) t2 -> ∃ t1, typed ∅ e t1 ∧ ctx_typed k t1 t2.
Proof.
  intros Hc Ht.
  destruct Hc; inv Ht; eexists; split;
  try done; intros ??; econstructor; done.
Qed.

Lemma ctx_typed_comp k k' t1 t2 t3 :
  ctx_typed k t1 t2 -> ctx_typed k' t2 t3 -> ctx_typed (k' ∘ k) t1 t3.
Proof.
  intros Hc Hc' ??. apply Hc'. apply Hc. done.
Qed.

Lemma typed_ctx_typed k e t2 :
  ctx k -> typed ∅ (k e) t2 -> ∃ t1, typed ∅ e t1 ∧ ctx_typed k t1 t2.
Proof.
  intros Hk. revert t2.
  induction Hk; intros t2 Ht.
  - eexists. split; first done. intros ??; done.
  - apply (typed_ctx1_typed k1) in Ht; last done.
    destruct Ht as (t1 & Ht' & Hct').
    edestruct IHHk as (t' & H1 & H2); first done.
    eexists. split; first done.
    eapply ctx_typed_comp; done.
Qed.

Lemma typed_mono Γ e t :
  typed Γ e t -> ∀ Γ', Γ ⊆ Γ' -> typed Γ' e t.
Proof.
  induction 1; intros Γ' Hs; try econstructor;
  eauto using lookup_weaken.
  apply IHtyped. apply insert_mono. done.
Qed.

Lemma empty_subseteq' (Γ : envT) : ∅ ⊆ Γ.
Proof.
  intro. rewrite lookup_empty. destruct (Γ !! i); done.
Qed.

Lemma subst_typed Γ x tv e t v :
  Γ !! x = Some tv -> val v -> typed ∅ v tv ->
  typed Γ e t -> typed (delete x Γ) (subst e x v) t.
Proof.
  intros HΓ Hv Htv Ht.
  induction Ht; simpl; try solve [econstructor; eauto].
  - case_decide.
    + subst. rewrite HΓ in H. simplify_eq.
      eapply typed_mono; first done.
      apply empty_subseteq'.
    + constructor. rewrite lookup_delete_ne; done.
  - case_decide.
    + subst. econstructor. rewrite insert_delete. done.
    + econstructor. rewrite <-delete_insert_ne; last done.
      apply IHHt. rewrite lookup_insert_ne; done.
Qed.

Lemma head_step_typed e e' t :
  typed ∅ e t -> head_step e e' -> typed ∅ e' t.
Proof.
  intros Ht Hs.
  destruct Hs; try solve [inv Ht; done].
  - inv Ht. inv H3.
    replace (∅ : envT) with (delete x (<[x:=t1]> ∅) : envT).
    + eapply subst_typed; try done.
      rewrite lookup_insert. done.
    + rewrite delete_insert; first done.
      apply lookup_empty.
  - inv Ht. inv H5.
    destruct b; done.
  - inv Ht. inv H4. destruct b; econstructor; eauto.
  - inv Ht. inv H6. econstructor; eauto. constructor; eauto.
Qed.

Lemma step_typed e e' t :
  typed ∅ e t -> step e e' -> typed ∅ e' t.
Proof.
  intros Ht Hs.
  destruct Hs.
  apply typed_ctx_typed in Ht as (t1 & H1 & H2); last done.
  apply H2. eapply head_step_typed; done.
Qed.

Lemma steps_typed e e' t :
  typed ∅ e t -> steps e e' -> typed ∅ e' t.
Proof.
  intros Ht Hs.
  induction Hs; first done.
  apply IHHs. eapply step_typed; done.
Qed.

Lemma head_step_step e e' :
  head_step e e' -> step e e'.
Proof.
  intros Hs. apply (step_head_step id); last done. constructor.
Qed.

Inductive HT_nat : expr -> Prop :=
  | HT_nat_zero : HT_nat EZero
  | HT_nat_succ v : HT_nat v -> HT_nat (ESucc v).

Inductive HT_lazy_nat : expr -> Prop :=
  | HT_lnat_zero : HT_lazy_nat EZero
  | NT_lnat_succ e v : steps e v -> HT_lazy_nat v -> HT_lazy_nat (ESucc e).

Fixpoint HTv (e : expr) (t : ty) : Prop :=
  match t with
  | TUnit => (e = EUnit)
  | TFun t1 t2 =>
      ∃ x e', (e = ELam x e') ∧
              ∀ v, typed ∅ v t1 -> HTv v t1 ->  (* we want to say HTe (subst e' x v) t2 *)
              ∃ w, steps (subst e' x v) w ∧ HTv w t2 (* but Coq's termination checker is too weak *)
  | TPair t1 t2 =>
      ∃ e1 e2, e = EPair e1 e2 ∧ HTv e1 t1 ∧ HTv e2 t2
  | TSum t1 t2 =>
      ∃ b e',  e = EInj b e' ∧ HTv e' (if b then t1 else t2)
  | TZero => False
  | TNat => HT_nat e
  end.

Definition HTe (e : expr) (t : ty) : Prop := ∃ v, steps e v ∧ HTv v t.

Definition env_HT (γ : env) (Γ : envT) :=
  ∀ x, match  (Γ !! x),(γ !! x) with
       | Some t, Some v => HTv v t ∧ typed ∅ v t
       | None, None => True
       | _, _ => False
       end.

Fixpoint env_subst (γ : env) (e : expr) :=
  match e with
  | EUnit => EUnit
  | EVar x' =>
    match γ !! x' with
    | Some v => v
    | None => EVar x'
    end
  | ELam x' e' => ELam x' (env_subst (delete x' γ) e')
  | EApp e1 e2 => EApp (env_subst γ e1) (env_subst γ e2)
  | EPair e1 e2 => EPair (env_subst γ e1) (env_subst γ e2)
  | EProj b e' => EProj b (env_subst γ e')
  | EInj b e' => EInj b (env_subst γ e')
  | EMatch e1 e2 e3 => EMatch (env_subst γ e1) (env_subst γ e2) (env_subst γ e3)
  | EMatch0 e' => EMatch0 (env_subst γ e')
  | EZero => EZero
  | ESucc e => ESucc (env_subst γ e)
  | ERec e1 e2 e3 => ERec (env_subst γ e1) (env_subst γ e2) (env_subst γ e3)
  end.

Lemma typed_subst_id e t x v Γ :
  Γ !! x = None -> typed Γ e t -> subst e x v = e.
Proof.
  intros Hx Ht.
  induction Ht; intros; simpl; try done; try case_decide;
  simplify_eq; try done;
  rewrite ?IHHt ?IHHt1 ?IHHt2 ?IHHt3; try done.
  rewrite lookup_insert_ne; done.
Qed.

Lemma typed_emp_subst_id x e v t :
  typed ∅ e t -> subst e x v = e.
Proof.
  eapply typed_subst_id. apply lookup_empty.
Qed.

Lemma env_HT_insert x v t1 γ Γ :
  typed ∅ v t1 -> HTv v t1 -> env_HT γ Γ -> env_HT (<[x:=v]> γ) (<[x:=t1]> Γ).
Proof.
  intros Ht Hv He y.
  destruct (decide (x = y)).
  - subst. rewrite !lookup_insert; eauto.
  - specialize (He y). rewrite !lookup_insert_ne; done.
Qed.

Lemma env_HT_delete γ Γ x :
  env_HT γ Γ -> env_HT (delete x γ) (delete x Γ).
Proof.
  intros He y.
  destruct (decide (x = y)).
  - subst. rewrite !lookup_delete. done.
  - specialize (He y). rewrite !lookup_delete_ne; done.
Qed.

Lemma subst_env_subst x γ v e Γ :
  γ !! x = None ->
  env_HT γ Γ ->
  subst (env_subst γ e) x v = env_subst (<[ x := v ]> γ) e.
Proof.
  revert γ Γ.
  induction e; intros γ Γ Hx Hvals; simpl in *; eauto;
  try solve [ try erewrite IHe; try erewrite IHe1;
              try erewrite IHe2; try erewrite IHe3; done].
  - destruct (decide (x = s)).
    + subst. rewrite lookup_insert Hx. simpl.
      case_decide; try done.
    + rewrite lookup_insert_ne; last done.
      pose proof (Hvals s).
      destruct (γ !! s) eqn:E; simpl;
      try case_decide; try done.
      destruct (Γ !! s) eqn:F; try done.
      destruct H.
      eapply typed_emp_subst_id; try done.
  - case_decide; subst; f_equal.
    + rewrite delete_insert_delete. done.
    + erewrite IHe.
      * rewrite delete_insert_ne; done.
      * rewrite lookup_delete_ne; eauto.
      * eapply env_HT_delete. done.
Qed.

(* Γ !! x = Some tv -> val v -> typed ∅ v tv ->
typed Γ e t -> typed (delete x Γ) (subst e x v) t. *)

Lemma map_union_delete (A B : envT) x :
  is_Some (A !! x) -> A ∪ B = A ∪ (delete x B).
Proof.
  intros Hs.
  apply map_eq. intros i.
  rewrite !lookup_union.
  destruct (decide (i = x)).
  - subst. destruct Hs. rewrite H. simpl. rewrite lookup_delete. simpl.
    destruct (B !! x); simpl; done.
  - rewrite lookup_delete_ne; eauto.
Qed.

Lemma map_union_insert' (A B : envT) x v :
  <[x:=v]> (A ∪ B) = <[x:=v]> A ∪ delete x B.
Proof.
  rewrite insert_union_l.
  rewrite <- map_union_delete; first done.
  rewrite lookup_insert. eauto.
Qed.

Lemma disjoint_move (A B : envT) x v :
  A ##ₘ B -> delete x A ##ₘ <[x:=v]> B.
Proof.
  intros H y.
  destruct (decide (x = y)).
  - subst. rewrite lookup_delete. simpl. rewrite lookup_insert. done.
  - rewrite lookup_delete_ne; last done.
    rewrite lookup_insert_ne; last done. done.
Qed.

Lemma env_subst_typed Γ Γ' γ e t :
  Γ' ##ₘ Γ -> typed (Γ ∪ Γ') e t -> env_HT γ Γ' -> typed Γ (env_subst γ e) t.
Proof.
  remember (Γ ∪ Γ') as g.
  intros Hdisj Ht. revert γ Γ' Γ Hdisj Heqg.
  induction Ht; intros; simpl in *; try solve [econstructor;eauto]; simplify_eq.
  - specialize (H0 x).
    destruct (Γ' !! x) eqn:E; destruct (γ !! x) eqn:F; simplify_eq; try done.
    + simplify_map_eq. destruct H0.
      eapply typed_mono; first done.
      apply empty_subseteq'.
    + constructor. apply lookup_union_Some in H; naive_solver.
  - constructor. eapply IHHt; eauto using env_HT_delete.
    + apply disjoint_move. done.
    + apply map_union_insert'.
Qed.

Lemma HT_steps_rev e' e t :
  steps e e' -> HTe e' t -> HTe e t.
Proof.
  intros Hs Ht.
  destruct Ht as (e'' & Hs' & H).
  eexists. split; last done.
  eapply rtc_transitive; eauto.
Qed.

Lemma HT_val e t :
  HTv e t -> val e.
Proof.
  revert e. induction t; intros e; simpl; try done.
  - intros ->. constructor.
  - intros (? & ? & -> & H). constructor.
  - intros (? & ? & -> & []). constructor; eauto.
  - intros (? & ? & -> & H). constructor. destruct x; eauto.
  - induction 1; constructor; done.
Qed.

Lemma HT_app e1 e2 t1 t2 :
  typed ∅ e2 t1 ->
  HTv e1 (TFun t1 t2) ->
  HTv e2 t1 ->
  HTe (EApp e1 e2) t2.
Proof.
  intros Htyped IHtyped1 IHtyped2.
  simpl in *.
  destruct IHtyped1 as (x & e' & -> & H).
  apply (HT_steps_rev (subst e' x e2)).
  { apply rtc_once. eapply (step_head_step id); first by constructor.
    fold subst. constructor. by eapply HT_val. }
  unfold HTe. eauto.
Qed.

Lemma HT_ctx1 k e v t :
  ctx1 k ->
  steps e v ->
  HTe (k v) t ->
  HTe (k e) t.
Proof.
  intros Hk H1 H2.
  eapply HT_steps_rev; eauto.
  eapply steps_ctx; eauto.
  eapply ctx1_ctx; eauto.
Qed.

Lemma HTv_HTe e t : HTv e t -> HTe e t.
Proof. intros. eexists. split; done. Qed.

Ltac lemmas := eauto using HT_val, HTv_HTe.
Ltac fin := done || (constructor; lemmas; done) || lemmas.

Lemma HT_app_e e1 e2 t1 t2 :
  typed ∅ e2 t1 ->
  HTe e1 (TFun t1 t2) ->
  HTe e2 t1 ->
  HTe (EApp e1 e2) t2.
Proof.
  intros Htyped IHtyped1 IHtyped2.
  destruct IHtyped1 as (v1 & Hs1 & Hv1).
  destruct IHtyped2 as (v2 & Hs2 & Hv2).
  eapply (HT_ctx1 (λ x, EApp x _)); fin.
  eapply HT_ctx1; fin.
  eapply HT_app; eauto.
  eapply steps_typed; eauto.
Qed.

Lemma HT_step v e t :
  HTe v t ->
  head_step e v ->
  HTe e t.
Proof.
  intros ??.
  destruct H as (? & ? & ?).
  repeat eexists; last done.
  eapply rtc_transitive.
  eapply rtc_once. eapply (step_head_step id); fin. done.
Qed.

Ltac destrHT H := edestruct H as (? & ? & ?); fin.

Lemma main Γ e t : typed Γ e t -> ∀ γ, env_HT γ Γ -> HTe (env_subst γ e) t.
Proof.
  induction 1; intros γ Hγ; simpl in *.
  - by apply HTv_HTe.
  - apply HTv_HTe. specialize (Hγ x). rewrite H in Hγ.
    destruct (γ !! x) eqn:E; naive_solver.
  - apply HTv_HTe. simpl. do 2 eexists. split; first done.
    intros v Hvt Hv.
    destrHT IHtyped.
    { apply env_HT_insert; try done. }
    eexists. split; last done.
    erewrite subst_env_subst; eauto using env_HT_delete.
    + rewrite insert_delete. done.
    + rewrite lookup_delete. done.
  - eapply HT_app_e; eauto. eapply env_subst_typed; eauto.
    solve_map_disjoint. rewrite left_id. done.
  - destrHT IHtyped1.
    destrHT IHtyped2.
    eapply (HT_ctx1 (λ x, EPair x _)); fin.
    eapply HT_ctx1; fin.
    eapply HTv_HTe. simpl.
    repeat eexists; done.
  - destrHT IHtyped.
    eapply HT_ctx1; fin.
    destruct H1 as (? & ? & -> & ? & ?).
    eapply (HT_step (if b then x0 else x1)); fin.
    destruct b; fin.
  - destrHT IHtyped.
    eapply HT_ctx1; fin.
    eapply HTv_HTe. simpl.
    repeat eexists; done.
  - destrHT IHtyped1.
    eapply (HT_ctx1 (λ x, EMatch x _ _)); fin.
    simpl in *. destruct H3 as (? & ? & -> & ?).
    assert (typed ∅ (EInj x0 x1) (TSum t1 t2)).
    { eapply steps_typed; eauto. eapply env_subst_typed; eauto.
      solve_map_disjoint. rewrite left_id. done. }
    inv H4.
    eapply HT_steps_rev.
    + eapply rtc_once. eapply (step_head_step id); fin.
    + eapply HT_app_e; eauto using HTv_HTe; last (destruct x0; eauto).
  - specialize (IHtyped γ Hγ). unfold HTe in *. simpl in *. naive_solver.
  - apply HTv_HTe. simpl. constructor.
  - destrHT IHtyped.
    eapply HT_ctx1; fin. apply HTv_HTe. simpl in *. constructor. done.
  - destrHT IHtyped1.
    destrHT IHtyped2.
    destrHT IHtyped3.
    eapply (HT_ctx1 (λ x, ERec x _ _)); fin.
    eapply (HT_ctx1 (λ x, ERec _ x _)); fin.
    eapply (HT_ctx1 (λ x, ERec _ _ x)); fin.
    simpl in *. destruct H7 as (? & ? & -> & ?).
    clear H2.
    assert (typed ∅ x TNat).
    { induction H3; fin. }
    assert (typed ∅ x0 t).
    { eapply steps_typed; last done. eapply env_subst_typed; eauto.
      solve_map_disjoint. rewrite left_id. done. }
    assert (typed ∅ (ELam x2 x3) (TFun t t)).
    { eapply steps_typed; last done. eapply env_subst_typed; eauto.
      solve_map_disjoint. rewrite left_id. done. }
    induction H3.
    + eapply HT_step; fin. constructor; fin.
    + eapply HT_step; last constructor; fin.
      eapply HT_app_e; fin.
      * inv H2. constructor; eauto.
      * apply HTv_HTe. simpl. do 2 eexists. split; first done. done.
      * inv H2; fin.
      * eapply (HT_val _ TNat). done.
Qed.

Lemma env_HT_empty : env_HT ∅ ∅.
Proof.
  intro. rewrite !lookup_empty. done.
Qed.

Lemma env_subst_empty e :
  env_subst ∅ e = e.
Proof.
  induction e; simpl; rewrite ?delete_empty ?IHe ?IHe1 ?IHe2 ?IHe3; try done.
Qed.

Theorem termination e t : typed ∅ e t -> ∃ e', steps e e' ∧ val e'.
Proof.
  intros Ht.
  eapply (main ∅ e t) in Ht; eauto using env_HT_empty.
  erewrite env_subst_empty in Ht.
  destruct Ht as (? & ? & ?).
  eauto using HT_val.
Qed.