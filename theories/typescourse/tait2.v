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

Fixpoint freevars e : gset string :=
  match e with
  | EUnit => ∅
  | EVar x => {[ x ]}
  | ELam x e => freevars e ∖ {[ x ]}
  | EApp e1 e2 => freevars e1 ∪ freevars e2
  | EPair e1 e2 => freevars e1 ∪ freevars e2
  | EProj b e => freevars e
  end.

Lemma freevars_notin_subst_id x e v :
  x ∉ freevars e -> subst e x v = e.
Proof.
  intro. induction e; simpl in *; try case_decide;
  rewrite ?IHe ?IHe1 ?IHe2; set_solver.
Qed.

Lemma freevars_subst x e v :
  freevars v = ∅ -> freevars (subst e x v) = freevars e ∖ {[ x ]}.
Proof.
  intro. induction e; simpl; try case_decide; rewrite ?IHe ?IHe1 ?IHe2; set_solver.
Qed.

Lemma head_step_freevars e e' :
  freevars e = ∅ -> head_step e e' -> freevars e' = ∅.
Proof.
  intros H Hs. destruct Hs; simpl in *.
  - rewrite freevars_subst; set_solver.
  - destruct b; set_solver.
Qed.

Lemma freevars_ctx1 k e :
  ctx1 k -> freevars (k e) = freevars e ∪ freevars (k EUnit).
Proof.
  destruct 1; simpl; set_solver.
Qed.

Lemma freevars_ctx k e :
  ctx k -> freevars (k e) = freevars e ∪ freevars (k EUnit).
Proof.
  induction 1. set_solver. simpl.
  rewrite freevars_ctx1; last done.
  rewrite (freevars_ctx1 k1 (k2 EUnit)); last done;
  rewrite IHctx. set_solver.
Qed.

Lemma step_freevars e e' :
  freevars e = ∅ -> step e e' -> freevars e' = ∅.
Proof.
  intros H Hs. destruct Hs.
  rewrite freevars_ctx; last done.
  rewrite freevars_ctx in H; last done.
  apply head_step_freevars in H1; last set_solver.
  rewrite H1. set_solver.
Qed.

Lemma steps_freevars e e' :
  freevars e = ∅ -> steps e e' -> freevars e' = ∅.
Proof.
  intros H. induction 1; eauto using step_freevars.
Qed.

Lemma typed_freevars Γ e t :
  typed Γ e t -> freevars e ⊆ dom (gset string) Γ.
Proof.
  induction 1; simpl; try set_solver.
  assert (x ∈ dom (gset string) Γ); last set_solver.
  eapply elem_of_dom_2; done.
Qed.

Fixpoint HT (e : expr) (t : ty) :=
  match t with
  | TUnit =>
      steps e EUnit
  | TFun t1 t2 =>
      ∃ x e', steps e (ELam x e') ∧
              ∀ v, freevars v = ∅ -> HT v t1 -> HT (subst e' x v) t2
  | TPair t1 t2 =>
      ∃ e1 e2, steps e (EPair e1 e2) ∧ HT e1 t1 ∧ HT e2 t2
  end.

Definition env_HT (γ : env) (Γ : envT) :=
  ∀ x, match  (Γ !! x),(γ !! x) with
       | Some t, Some v => HT v t ∧ freevars v = ∅
       | None, None => True
       | _, _ => False
       end.

Lemma env_HT_dom γ Γ :
  env_HT γ Γ -> dom (gset string) γ = dom (gset string) Γ.
Proof.
  intros H. apply elem_of_equiv_L.
  intros x. specialize (H x).
  destruct (Γ !! x) eqn:E; destruct (γ !! x) eqn:F; try done.
  apply elem_of_dom_2 in E,F. done.
  apply not_elem_of_dom in E,F. done.
Qed.

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

Lemma env_HT_insert x v t1 γ Γ :
  freevars v = ∅ -> HT v t1 -> env_HT γ Γ -> env_HT (<[x:=v]> γ) (<[x:=t1]> Γ).
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
      apply freevars_notin_subst_id. set_solver.
  - case_decide; subst; f_equal.
    + rewrite delete_insert_delete. done.
    + erewrite IHe.
      * rewrite delete_insert_ne; done.
      * rewrite lookup_delete_ne; eauto.
      * eapply env_HT_delete. done.
Qed.

Lemma env_subst_freevars Γ γ e :
  env_HT γ Γ -> freevars (env_subst γ e) = freevars e ∖ dom (gset string) γ.
Proof.
  revert γ Γ.
  induction e; intros γ Γ He; simpl.
  - set_solver.
  - specialize (He s).
    destruct (γ !! s) eqn:E; simpl;
    destruct (Γ !! s) eqn:F; simpl; try done.
    + destruct He. rewrite H0.
      assert (s ∈ dom (gset string) γ); last set_solver.
      eapply elem_of_dom_2; done.
    + assert (s ∉ dom (gset string) γ); last set_solver.
      rewrite elem_of_dom. rewrite E. done.
  - erewrite IHe. set_solver.
    apply env_HT_delete; done.
  - erewrite IHe1; last done.
    erewrite IHe2; last done.
    set_solver.
  - erewrite IHe1; last done. set_solver.
  - erewrite IHe; set_solver.
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
    repeat eexists; eauto.
    eapply rtc_transitive; done.
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
    eapply steps_freevars; eauto.
    erewrite env_subst_freevars; last done.
    apply typed_freevars in H0.
    erewrite env_HT_dom; last done.
    set_solver.
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