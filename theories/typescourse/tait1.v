From iris.proofmode Require Import tactics.
Ltac inv H := inversion H; clear H; simplify_eq; simpl in *.

Inductive expr :=
  | EUnit : expr
  | EVar : string -> expr
  | ELam : string -> expr -> expr
  | EApp : expr -> expr -> expr
  | EPair : expr -> expr -> expr
  | EProj : bool -> expr -> expr.

Fixpoint subst e x v :=
  match e with
  | EUnit => EUnit
  | EVar x' => if decide (x = x') then v else EVar x'
  | ELam x' e' =>  (* only works for when v is a value *)
      if decide (x = x') then ELam x' e' else ELam x' (subst e' x v)
  | EApp e1 e2 => EApp (subst e1 x v) (subst e2 x v)
  | EPair e1 e2 => EPair (subst e1 x v) (subst e2 x v)
  | EProj b e' => EProj b (subst e' x v)
  end.

Inductive val : expr -> Prop :=
  | VNat : val EUnit
  | VPair e1 e2 : val e1 -> val e2 -> val (EPair e1 e2)
  | VLam x e : val (ELam x e).

Inductive head_step : expr -> expr -> Prop :=
  | head_step_app x e v :
      val v ->
      head_step (EApp (ELam x e) v) (subst e x v)
  | head_step_proj b v1 v2 :
      val v1 -> val v2 ->
      head_step (EProj b (EPair v1 v2)) (if b then v1 else v2).

Inductive ctx1 : (expr -> expr) -> Prop :=
  | ctx1_app_l e : ctx1 (λ x, EApp x e)
  | ctx1_app_r v : val v -> ctx1 (λ x, EApp v x)
  | ctx1_pair_l e : ctx1 (λ x, EPair x e)
  | ctx1_pair_r v : val v -> ctx1 (λ x, EPair v x)
  | ctx1_proj b : ctx1 (λ x, EProj b x).

Inductive ctx : (expr -> expr) -> Prop :=
  | ctx_nil : ctx (λ x, x)
  | ctx_cons k1 k2 : ctx1 k1 -> ctx k2 -> ctx (k1 ∘ k2).

Inductive step : expr -> expr -> Prop :=
  | step_head_step k e e' :
      ctx k -> head_step e e' -> step (k e) (k e').

Inductive ty :=
  | TUnit : ty
  | TFun : ty -> ty -> ty
  | TPair : ty -> ty -> ty.

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
      typed Γ (EProj b e) (if b then t1 else t2).

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
  induction Ht; simpl.
  - constructor.
  - case_decide.
    + subst. rewrite HΓ in H. simplify_eq.
      eapply typed_mono; first done.
      apply empty_subseteq'.
    + constructor. rewrite lookup_delete_ne; done.
  - case_decide.
    + subst. econstructor. rewrite insert_delete. done.
    + econstructor. rewrite <-delete_insert_ne; last done.
      apply IHHt. rewrite lookup_insert_ne; done.
  - econstructor; eauto.
  - econstructor; eauto.
  - econstructor; eauto.
Qed.

Lemma head_step_typed e e' t :
  typed ∅ e t -> head_step e e' -> typed ∅ e' t.
Proof.
  intros Ht Hs.
  destruct Hs.
  - inv Ht. inv H3.
    replace (∅ : envT) with (delete x (<[x:=t1]> ∅) : envT).
    + eapply subst_typed; try done.
      rewrite lookup_insert. done.
    + rewrite delete_insert; first done.
      apply lookup_empty.
  - inv Ht. inv H5.
    destruct b; done.
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

Lemma termination_failed_attempt e t Γ :
  Γ = ∅ -> typed Γ e t -> ∃ e', steps e e' ∧ val e'.
Proof.
  intros HΓ H.
  induction H.
  - eexists. split; first done. constructor.
  - subst. rewrite lookup_empty in H. simplify_eq.
  - eexists. split; first done. constructor.
  - admit. (* impossible with this IH *)
  - destruct IHtyped1 as (v1 & H11 & H12); first done.
    destruct IHtyped2 as (v2 & H21 & H22); first done.
    exists (EPair v1 v2). split.
    + eapply rtc_transitive.
      * apply (steps_ctx (λ x, EPair x e2)); last done.
        apply ctx1_ctx. constructor.
      * apply (steps_ctx (λ x, EPair v1 x)); last done.
        apply ctx1_ctx. constructor. done.
    + constructor; done.
  - destruct IHtyped as (v & H1 & H2); first done. subst.
    eapply steps_typed in H; last done.
    inv H; inv H2. (* canonical forms lemma = inversion on typed and val *)
    exists (if b then e1 else e2).
    split.
    + eapply rtc_transitive.
      * apply (steps_ctx (λ x, EProj b x)); last done.
        apply ctx1_ctx. constructor.
      * apply rtc_once.
        apply head_step_step. constructor; done.
    + destruct b; done.
Admitted. (* Failed attempt *)

Fixpoint HT (e : expr) (t : ty) :=
  match t with
  | TUnit =>
      steps e EUnit
  | TFun t1 t2 =>
      ∃ x e', steps e (ELam x e') ∧
              ∀ v, typed ∅ v t1 -> HT v t1 -> HT (subst e' x v) t2
  | TPair t1 t2 =>
      ∃ e1 e2, steps e (EPair e1 e2) ∧ HT e1 t1 ∧ HT e2 t2
  end.

Definition env_HT (γ : env) (Γ : envT) :=
  ∀ x, match  (Γ !! x),(γ !! x) with
       | Some t, Some v => HT v t ∧ typed ∅ v t
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
  end.

Lemma typed_subst_id e t x v Γ :
  Γ !! x = None -> typed Γ e t -> subst e x v = e.
Proof.
  intros Hx Ht.
  induction Ht; intros; simpl; try done; try case_decide;
  simplify_eq; try done;
  rewrite ?IHHt ?IHHt1 ?IHHt2; try done.
  rewrite lookup_insert_ne; done.
Qed.

Lemma typed_emp_subst_id x e v t :
  typed ∅ e t -> subst e x v = e.
Proof.
  eapply typed_subst_id. apply lookup_empty.
Qed.

Lemma env_HT_insert x v t1 γ Γ :
  typed ∅ v t1 -> HT v t1 -> env_HT γ Γ -> env_HT (<[x:=v]> γ) (<[x:=t1]> Γ).
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
  try solve [ try erewrite IHe; try erewrite IHe1; try erewrite IHe2; done].
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
  steps e e' -> HT e' t -> HT e t.
Proof.
  intros Hs Ht.
  induction t; simpl in *.
  - eapply rtc_transitive; done.
  - destruct Ht as (x & e1 & ? & ?).
    repeat eexists.
    + eapply rtc_transitive; done.
    + eauto.
  - destruct Ht as (e1 & e2 & ? & ? & ?).
    repeat eexists.
    + eapply rtc_transitive; done.
    + eauto.
    + eauto.
Qed.

Lemma HT_val e t :
  HT e t -> ∃ v, steps e v ∧ val v ∧ HT v t.
Proof.
  revert e. induction t; intros e; simpl.
  - intros ?. repeat eexists; first done.
    constructor. reflexivity.
  - intros (? & ? & ? & ?).
    repeat eexists; try done.
    constructor.
  - intros (? & ? & ? & ? & ?).
    edestruct IHt1 as (v1 & ? & ? & ?); try done.
    edestruct IHt2 as (v2 & ? & ? & ?); try done.
    exists (EPair v1 v2).
    repeat eexists; try done.
    + eapply rtc_transitive; first done.
      eapply (rtc_transitive _ (EPair v1 x0)).
      { apply (steps_ctx (λ x, EPair x _)); last done.
        apply ctx1_ctx. constructor. }
      apply (steps_ctx (λ x, EPair _ x)); last done.
      apply ctx1_ctx. constructor. done.
    + constructor; done.
Qed.

(*
  For env_HT γ Γ we need to have:
  - if Γ !! x = Some t then γ !! x = Some v and HT v t
  - subst (env_subst (delete x γ) e) x v
               =
      env_subst (<[x:=v]> γ) e
  - we need to be able to insert into γ
*)

Definition judg_HT Γ e t :=
  ∀ γ, env_HT γ Γ -> HT (env_subst γ e) t.

Lemma main Γ e t : typed Γ e t -> judg_HT Γ e t.
Proof.
  induction 1; intros γ Hγ; simpl in *.
  - reflexivity.
  - specialize (Hγ x). rewrite H in Hγ.
    destruct (γ !! x) eqn:E; naive_solver.
  - do 2 eexists. split; first done.
    intros v Hvt Hv.
    assert (HT (env_subst (<[x:=v]> γ) e) t2).
    { apply IHtyped. apply env_HT_insert; try done. }
    assert ((subst (env_subst (delete x γ) e) x v) =
            (env_subst (<[x:=v]> γ) e)).
    { erewrite subst_env_subst; eauto using env_HT_delete.
      - rewrite insert_delete. done.
      - rewrite lookup_delete. done. }
    rewrite H1. done.
  - specialize (IHtyped1 γ Hγ).
    specialize (IHtyped2 γ Hγ).
    simpl in *.
    destruct IHtyped1 as (x & e' & Hsteps & HH).
    eapply HT_steps_rev.
    { apply (steps_ctx (λ x, EApp x _)); last done.
      apply ctx1_ctx. constructor. }
    apply HT_val in IHtyped2.
    destruct IHtyped2 as (v & Hst & Hv & Hv').
    eapply HT_steps_rev.
    { apply (steps_ctx (λ x, EApp _ x)); last done.
      apply ctx1_ctx. constructor. constructor. }
    apply (HT_steps_rev (subst e' x v)).
    { apply rtc_once. eapply (step_head_step id); first by constructor.
      fold subst. constructor. done. }
    eapply HH; eauto.
    eapply steps_typed; last done.
    eapply env_subst_typed; eauto.
    + solve_map_disjoint.
    + rewrite left_id. done.
  - specialize (IHtyped1 γ Hγ).
    specialize (IHtyped2 γ Hγ).
    do 2 eexists.
    split; first by reflexivity.
    split; done.
  - specialize (IHtyped γ Hγ).
    simpl in *.
    destruct IHtyped as (e1 & e2 & Hs & Ht1 & Ht2).
    eapply HT_steps_rev.
    { apply (steps_ctx (λ x, EProj b x)); last done.
      apply ctx1_ctx. constructor. }
    apply HT_val in Ht1 as (v & Hs1 & Hv1 & Ht1).
    apply HT_val in Ht2 as (v' & Hs1' & Hv1' & Ht1').
    eapply HT_steps_rev.
    { apply (steps_ctx (λ x, EProj b (EPair x _))); last done.
      apply ctx_cons. constructor. apply ctx1_ctx. constructor. }
    eapply HT_steps_rev.
    { apply (steps_ctx (λ x, EProj b (EPair _ x))); last done.
      apply ctx_cons. constructor. apply ctx1_ctx. constructor. done. }
    apply (HT_steps_rev (if b then v else v')).
    { apply rtc_once. eapply (step_head_step id); first by constructor.
      constructor; done. }
    destruct b; done.
Qed.

Lemma env_HT_empty : env_HT ∅ ∅.
Proof.
  intro. rewrite !lookup_empty. done.
Qed.

Lemma env_subst_empty e :
  env_subst ∅ e = e.
Proof.
  induction e; simpl; rewrite ?delete_empty ?IHe ?IHe1 ?IHe2; done.
Qed.

Theorem termination e t : typed ∅ e t -> ∃ e', steps e e' ∧ val e'.
Proof.
  intros Ht.
  apply main in Ht.
  specialize (Ht ∅ env_HT_empty).
  apply HT_val in Ht as (? & ? & ? & ?).
  rewrite env_subst_empty in H.
  eauto.
Qed.