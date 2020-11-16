From iris.proofmode Require Import base tactics classes.
From diris Require Import util.
Ltac inv a := inversion a; simplify_eq.
Ltac invc a := inv a; clear a.

Definition chan := nat.

(*
We have a heap of channel buffers indexed by chan's (e.g. natural numbers).
We represent a channel as a natural number and a boolean for the polarity of the endpoint
Each party will put its messages in one buffer and read from the other
*)
Definition endpoint := (chan * bool)%type.

(*
We have a lambda calculus-based language with natural numbers, closures, and unit.
In addition we have channel values.
*)
Inductive val :=
    | Unit : val
    | Nat : nat -> val
    | Pair : val -> val -> val
    | Fun : string -> expr -> val
    | Chan : endpoint -> val

with expr :=
    | Val : val -> expr
    | Var : string -> expr
    | App : expr -> expr -> expr
    | Lam : string -> expr -> expr
    | Send : expr -> expr -> expr
    | Recv : expr -> expr
    | Let : string -> expr -> expr -> expr
    | LetUnit : expr -> expr -> expr
    | LetProd : string -> string -> expr -> expr -> expr
    | If : expr -> expr -> expr -> expr
    | Fork : expr -> expr
    | Close : expr -> expr.

Definition heap := list (list val * list val).

Inductive type :=
    | UnitT : type
    | NatT : type
    | PairT : type -> type -> type
    | FunT : type -> type -> type
    | ChanT : chan_type -> type

with chan_type :=
    | SendT : type -> chan_type -> chan_type
    | RecvT : type -> chan_type -> chan_type
    | EndT : chan_type.

Notation envT := (gmap string type).

Fixpoint dual ct :=
    match ct with
    | EndT => EndT
    | SendT c ct => RecvT c (dual ct)
    | RecvT c ct => SendT c (dual ct)
    end.

Definition heapT := gmap endpoint chan_type.

(* Definition jProp := heapT -> Prop.

Definition jWand (p q : jProp) : jProp :=
    λ Σ, ∀ Σ', Σ ##ₘ Σ' -> p Σ' -> q (Σ ∪ Σ').

Definition jEntails (p q : jProp) : Prop :=
  ∀ Σ', p Σ' -> q Σ'.

Inductive val_typed : val -> type -> jProp :=
    | Unit_typed :
        val_typed Unit UnitT ∅
    | Pair_typed : ∀ a b aT bT,
        jEntails (val_typed a aT) $
        jWand (val_typed b bT) $
              (val_typed (Pair a b) (PairT aT bT)). *)

Inductive val_typed : heapT -> val -> type -> Prop :=
    | Unit_typed :
        val_typed ∅ Unit UnitT
    | Nat_typed : ∀ n,
        val_typed ∅ (Nat n) NatT
    | Pair_typed : ∀ a b aT bT Σ1 Σ2,
        Σ1 ##ₘ Σ2 ->
        val_typed Σ1 a aT ->
        val_typed Σ2 b bT ->
        val_typed (Σ1 ∪ Σ2) (Pair a b) (PairT aT bT)
    | Fun_typed : ∀ Σ x e a b,
        typed Σ {[ x := a ]} e b ->
        val_typed Σ (Fun x e) (FunT a b)
    | Chan_typed : ∀ c ct,
        val_typed {[ c := ct ]} (Chan c) (ChanT ct)

with typed : heapT -> envT -> expr -> type -> Prop :=
    | Val_typed : ∀ Σ v t,
        val_typed Σ v t ->
        typed Σ ∅ (Val v) t
    | Var_typed : ∀ x t,
        typed ∅ {[ x := t ]} (Var x) t
    | App_typed : ∀ Σ1 Σ2 Γ1 Γ2 e1 e2 t1 t2,
        Σ1 ##ₘ Σ2 ->
        Γ1 ##ₘ Γ2 ->
        typed Σ1 Γ1 e1 (FunT t1 t2) ->
        typed Σ2 Γ2 e2 t1 ->
        typed (Σ1 ∪ Σ2) (Γ1 ∪ Γ2) (App e1 e2) t2
    | Lam_typed : ∀ Σ Γ x e t1 t2,
        Γ !! x = None ->
        typed Σ (Γ ∪ {[ x := t1 ]}) e t2 ->
        typed Σ Γ (Lam x e) (FunT t1 t2)
    | Send_typed : ∀ Σ1 Σ2 Γ1 Γ2 e1 e2 t r,
        Σ1 ##ₘ Σ2 ->
        Γ1 ##ₘ Γ2 ->
        typed Σ1 Γ1 e1 (ChanT (SendT t r)) ->
        typed Σ2 Γ2 e2 t ->
        typed (Σ1 ∪ Σ2) (Γ1 ∪ Γ2) (Send e1 e2) (ChanT r)
    | Recv_typed : ∀ Σ Γ e t r,
        typed Σ Γ e (ChanT (RecvT t r)) ->
        typed Σ Γ (Recv e) (PairT t (ChanT r))
    | Let_typed : ∀ Σ1 Σ2 Γ1 Γ2 e1 e2 t1 t2 x,
        Σ1 ##ₘ Σ2 ->
        Γ1 ##ₘ Γ2 ->
        Γ2 !! x = None ->
        typed Σ1 Γ1 e1 t1 ->
        typed Σ2 (Γ2 ∪ {[ x := t1 ]}) e2 t2 ->
        typed (Σ1 ∪ Σ2) (Γ1 ∪ Γ2) (Let x e1 e2) t2
    | LetUnit_typed : ∀ Σ1 Σ2 Γ1 Γ2 e1 e2 t,
        Σ1 ##ₘ Σ2 ->
        Γ1 ##ₘ Γ2 ->
        typed Σ1 Γ1 e1 UnitT ->
        typed Σ2 Γ2 e2 t ->
        typed (Σ1 ∪ Σ2) (Γ1 ∪ Γ2) (LetUnit e1 e2) t
    | LetProd_typed : ∀ Σ1 Σ2 Γ1 Γ2 e1 e2 t11 t12 t2 x1 x2,
        Σ1 ##ₘ Σ2 ->
        Γ1 ##ₘ Γ2 ->
        x1 ≠ x2 ->
        Γ2 !! x1 = None ->
        Γ2 !! x2 = None ->
        typed Σ1 Γ1 e1 (PairT t11 t12) ->
        typed Σ2 (Γ2 ∪ {[ x1 := t11 ]} ∪ {[ x2 := t12 ]}) e2 t2 ->
        typed (Σ1 ∪ Σ2) (Γ1 ∪ Γ2) (LetProd x1 x2 e1 e2) t2
    | If_typed : ∀ Σ1 Σ2 Γ1 Γ2 e1 e2 e3 t,
        Σ1 ##ₘ Σ2 ->
        Γ1 ##ₘ Γ2 ->
        typed Σ1 Γ1 e1 NatT ->
        typed Σ2 Γ2 e2 t ->
        typed Σ2 Γ2 e3 t ->
        typed (Σ1 ∪ Σ2) (Γ1 ∪ Γ2) (If e1 e2 e3) t
    | Fork_typed : ∀ Σ Γ e ct,
        typed Σ Γ e (FunT (ChanT (dual ct)) UnitT) ->
        typed Σ Γ (Fork e) (ChanT ct)
    | Close_typed : ∀ Σ Γ e,
        typed Σ Γ e (ChanT EndT) ->
        typed Σ Γ (Close e) UnitT.

Fixpoint subst (x:string) (a:val) (e:expr) : expr :=
  match e with
  | Val _ => e
  | Var x' => if decide (x = x') then Val a else e
  | App e1 e2 => App (subst x a e1) (subst x a e2)
  | Lam x' e1 => if decide (x = x') then e else Lam x' (subst x a e1)
  | Send e1 e2 => Send (subst x a e1) (subst x a e2)
  | Recv e1 => Recv (subst x a e1)
  | Let x' e1 e2 => Let x' (subst x a e1) (if decide (x = x') then e2 else subst x a e2)
  | LetUnit e1 e2 => LetUnit (subst x a e1) (subst x a e2)
  | LetProd x' y' e1 e2 =>
      LetProd x' y' (subst x a e1) (if decide (x = x' ∨ x = y') then e2 else subst x a e2)
  | If e1 e2 e3 => If (subst x a e1) (subst x a e2) (subst x a e3)
  | Fork e1 => Fork (subst x a e1)
  | Close e1 => Close (subst x a e1)
  end.

Lemma typed_no_var_subst e Γ Σ t x v :
  Γ !! x = None ->
  typed Σ Γ e t ->
  subst x v e = e.
Proof.
  intros Heq Ht.
  induction Ht; simpl; try case_decide; simplify_eq;
  eauto; first simplify_map_eq; f_equal/=;
  try (apply lookup_union_None in Heq as []; eauto);
  try eapply IHHt2; try eapply IHHt; eauto;
  rewrite !lookup_union !lookup_singleton_ne; eauto;
  rewrite ?Heq ?H4 ?H6; eauto.
Qed.

Lemma lookup_union_Some' `{Countable K} {V} (A B : gmap K V) x v :
  A ##ₘ B ->
  (A ∪ B) !! x = Some v ->
  (A !! x = Some v ∧ B !! x = None) ∨ (B !! x = Some v ∧ A !! x = None).
Proof.
  intros Hdisj Hl.
  apply lookup_union_Some in Hl as []; eauto; [left | right]; split; eauto;
  rewrite ->map_disjoint_alt in Hdisj; specialize (Hdisj x);
  destruct (A !! x); naive_solver.
Qed.

Lemma send_to_l `{Countable K} {V} (A X Y : gmap K V) :
  A ##ₘ X ->
  A ∪ (X ∪ Y) = (A ∪ X) ∪ Y.
Proof.
  intros Hdisj.
  by rewrite !assoc.
Qed.

Lemma send_to_r `{Countable K} {V} (A X Y : gmap K V) :
  A ##ₘ X ->
  A ∪ (X ∪ Y) = X ∪ (A ∪ Y).
Proof.
  intros Hdisj.
  rewrite !assoc.
  rewrite (map_union_comm A); solve_map_disjoint.
Qed.

Lemma subst_typed Σv Σe Γ e eT v vT x :
  Σv ##ₘ Σe ->
  Γ !! x = Some vT ->
  val_typed Σv v vT ->
  typed Σe Γ e eT ->
  typed (Σv ∪ Σe) (delete x Γ) (subst x v e) eT.
Proof.
  intros DΣ DΓ Hv Ht. induction Ht; simpl.
  - simplify_map_eq.
  - simplify_map_eq.
    rewrite delete_singleton.
    rewrite right_id. by constructor.
  - apply lookup_union_Some' in DΓ as [[]|[]]; last done.
    + erewrite (typed_no_var_subst e2); eauto.
      rewrite delete_union (delete_notin Γ2); eauto.
      rewrite send_to_l; last solve_map_disjoint.
      econstructor; eauto; solve_map_disjoint.
    + erewrite (typed_no_var_subst e1); eauto.
      rewrite delete_union (delete_notin Γ1); eauto.
      rewrite send_to_r; last solve_map_disjoint.
      econstructor; eauto; solve_map_disjoint.
  - assert (x ≠ x0) by naive_solver.
    rewrite decide_False; last done.
    rewrite delete_union in IHHt.
    rewrite delete_singleton_ne in IHHt; last done.
    econstructor.
    + rewrite lookup_delete_ne; done.
    + eapply IHHt; first solve_map_disjoint.
      by apply lookup_union_Some_l.
  - apply lookup_union_Some' in DΓ as [[]|[]]; last done.
    + erewrite (typed_no_var_subst e2); eauto.
      rewrite delete_union (delete_notin Γ2); eauto.
      rewrite send_to_l; last solve_map_disjoint.
      econstructor; eauto; solve_map_disjoint.
    + erewrite (typed_no_var_subst e1); eauto.
      rewrite delete_union (delete_notin Γ1); eauto.
      rewrite send_to_r; last solve_map_disjoint.
      econstructor; eauto; solve_map_disjoint.
  - econstructor; eauto.
  - apply lookup_union_Some' in DΓ as [[]|[]]; last done.
    + (* Goes to e1 *)
      case_decide.
      * (* Shadowing: var that is being substituted is
           the same as the var in the let *)
        symmetry in H4. subst.
        rewrite delete_union (delete_notin Γ2); eauto.
        rewrite send_to_l; last solve_map_disjoint.
      econstructor; eauto; solve_map_disjoint.
      * erewrite (typed_no_var_subst e2); last eauto.
        2: { apply lookup_union_None; eauto.
          split; eauto.
          apply lookup_singleton_ne; done. }
      rewrite delete_union (delete_notin Γ2); eauto.
      rewrite send_to_l; last solve_map_disjoint.
      econstructor; eauto; solve_map_disjoint.
    + (* Goes to e2 *)
      erewrite (typed_no_var_subst e1); eauto.
      assert (x ≠ x0) by naive_solver.
      rewrite decide_False; eauto.
      rewrite delete_union (delete_notin Γ1); eauto.
      rewrite send_to_r; last solve_map_disjoint.
      econstructor; eauto; try solve_map_disjoint.
      * rewrite lookup_delete_ne; eauto.
      * rewrite delete_union in IHHt2. rewrite delete_singleton_ne in IHHt2; eauto.
        eapply IHHt2; try solve_map_disjoint.
        by apply lookup_union_Some_l.
  - apply lookup_union_Some' in DΓ as [[]|[]]; last done.
    + erewrite (typed_no_var_subst e2); eauto.
      rewrite delete_union (delete_notin Γ2); eauto.
      rewrite send_to_l; last solve_map_disjoint.
      econstructor; eauto; solve_map_disjoint.
    + erewrite (typed_no_var_subst e1); eauto.
      rewrite delete_union (delete_notin Γ1); eauto.
      rewrite send_to_r; last solve_map_disjoint.
      econstructor; eauto; solve_map_disjoint.
  - apply lookup_union_Some' in DΓ as [[]|[]]; last done.
    + (* Goes to e1 *)
      case_decide.
      * (* Shadowing: var that is being substituted is
          the same as the var in the let *)
        symmetry in H4. subst.
        rewrite delete_union (delete_notin Γ2); eauto.
        rewrite send_to_l; last solve_map_disjoint.
        econstructor; eauto; solve_map_disjoint.
      * erewrite (typed_no_var_subst e2); last eauto.
        2: {
          apply lookup_union_None. split.
          - apply lookup_union_None. split; eauto.
            apply lookup_singleton_ne; eauto.
          - apply lookup_singleton_ne; eauto.
        }
        rewrite delete_union (delete_notin Γ2); eauto.
        rewrite send_to_l; last solve_map_disjoint.
        econstructor; eauto; solve_map_disjoint.
    + (* Goes to e2 *)
      erewrite (typed_no_var_subst e1); eauto.
      assert (x ≠ x1) by naive_solver.
      assert (x ≠ x2) by naive_solver.
      rewrite decide_False; last naive_solver.
      rewrite delete_union (delete_notin Γ1); eauto.
      rewrite send_to_r; last solve_map_disjoint.
      econstructor; eauto; try solve_map_disjoint.
      * rewrite lookup_delete_ne; eauto.
      * rewrite lookup_delete_ne; eauto.
      * rewrite !delete_union in IHHt2. rewrite !delete_singleton_ne in IHHt2; eauto.
        eapply IHHt2; try solve_map_disjoint.
        apply lookup_union_Some_l.
        apply lookup_union_Some_l. done.
  - apply lookup_union_Some' in DΓ as [[]|[]]; last done.
    + erewrite (typed_no_var_subst e2); eauto.
      erewrite (typed_no_var_subst e3); eauto.
      rewrite delete_union (delete_notin Γ2); eauto.
      rewrite send_to_l; last solve_map_disjoint.
      econstructor; eauto; try solve_map_disjoint.
    + erewrite (typed_no_var_subst e1); eauto.
      rewrite delete_union (delete_notin Γ1); eauto.
      rewrite send_to_r; last solve_map_disjoint.
      econstructor; eauto; solve_map_disjoint.
  - econstructor; eauto.
  - econstructor; eauto.
Qed.

Definition lookup_recv (h : heap) (c : endpoint) : option (list val) :=
  h !! c.1 ≫= λ '(x,y), Some (if c.2 then x else y).

Definition lookup_send (h : heap) (c : endpoint) : option (list val) :=
  h !! c.1 ≫= λ '(x,y), Some (if c.2 then y else x).

Definition set_recv (h : heap) (c : endpoint) (buf : list val) : heap :=
  let (l,b) := c in
  match h !! l with
  | Some (x,y) => <[ l := if b then (buf,y) else (x,buf) ]> h
  | None => h
  end.
Definition set_send (h : heap) (c : endpoint) (buf : list val) : heap :=
  let (l,b) := c in
  match h !! l with
  | Some (x,y) => <[ l := if b then (x,buf) else (buf,y) ]> h
  | None => h
  end.

Inductive pure_step : expr -> expr -> Prop :=
    | App_step : ∀ x e a,
        pure_step (App (Val (Fun x e)) (Val a)) (subst x a e)
    | Lam_step : ∀ x e,
        pure_step (Lam x e) (Val (Fun x e))
    | If_step1 : ∀ n e1 e2,
        n ≠ 0 ->
        pure_step (If (Val (Nat n)) e1 e2) e1
    | If_step2 : ∀ e1 e2,
        pure_step (If (Val (Nat 0)) e1 e2) e2
    | Let_step : ∀ x v e,
        pure_step (Let x (Val v) e) (subst x v e)
    | LetUnit_step : ∀ e,
        pure_step (LetUnit (Val Unit) e) e
    | LetProd_step : ∀ x1 x2 v1 v2 e,
        pure_step (LetProd x1 x2 (Val (Pair v1 v2)) e) (subst x1 v1 $ subst x2 v2 e).

Inductive head_step : expr -> heap -> expr -> heap -> list expr -> Prop :=
    | Pure_step : ∀ e e' h,
        pure_step e e' -> head_step e h e' h []
    | Send_step : ∀ h c y buf,
        lookup_send h c = Some buf ->
        head_step (Send (Val (Chan c)) (Val y)) h (Val (Chan c)) (set_recv h c (buf ++ [y])) []
    | Recv_step : ∀ h c y buf,
        lookup_recv h c = Some (y::buf) ->
        head_step (Recv (Val (Chan c))) h (Val (Pair (Chan c) y)) (set_send h c buf) []
    | Close_step : ∀ c h,
        lookup_recv h c = Some [] ->
        head_step (Close (Val (Chan c))) h (Val Unit) h []
    | Fork_step : ∀ v (h : heap),
        head_step
          (Fork (Val v)) h
          (Val $ Chan (length h, true)) (h++[([],[])])
          [App (Val v) (Val (Chan (length h, false)))].

Inductive ctx1 : (expr -> expr) -> Prop :=
    | Ctx_App_l : ∀ e, ctx1 (λ x, App x e)
    | Ctx_App_r : ∀ v, ctx1 (λ x, App (Val v) x)
    | Ctx_Send_l : ∀ e, ctx1 (λ x, Send x e)
    | Ctx_Send_r : ∀ v, ctx1 (λ x, Send (Val v) x)
    | Ctx_Recv : ctx1 (λ x, Recv x)
    | Ctx_Let : ∀ s e, ctx1 (λ x, Let s x e)
    | Ctx_LetUnit : ∀ e, ctx1 (λ x, LetUnit x e)
    | Ctx_LetProd : ∀ s1 s2 e, ctx1 (λ x, LetProd s1 s2 x e)
    | Ctx_If : ∀ e1 e2, ctx1 (λ x, If x e1 e2)
    | Ctx_Fork : ctx1 (λ x, Fork x)
    | Ctx_Close : ctx1 (λ x, Close x).

Inductive ctx : (expr -> expr) -> Prop :=
    | Ctx_nil : ctx (λ x, x)
    | Ctx_cons : ∀ k1 k2, ctx1 k1 -> ctx k2 -> ctx (λ x, (k1 (k2 x))).

Inductive ctx_step : expr -> heap -> expr -> heap -> list expr -> Prop :=
  | Ctx_step : ∀ k e h e' h' ts,
      ctx k -> head_step e h e' h' ts -> ctx_step (k e) h (k e') h' ts.

Inductive step : list expr -> heap -> list expr -> heap -> Prop :=
  | Head_step : ∀ e e' h h' i ts es,
      ctx_step e h e' h' ts ->
      es !! i = Some e ->
      step es h (<[i := e']> es ++ ts) h'.

(* Closure of the step relation; this is used in the theorem statement. *)
Inductive steps : list expr -> heap -> list expr -> heap -> Prop :=
  | Trans_step : ∀ e1 e2 e3 s1 s2 s3,
      step e1 s1 e2 s2 ->
      steps e2 s2 e3 s3 ->
      steps e1 s1 e3 s3
  | Empty_step : ∀ e1 s1,
      steps e1 s1 e1 s1.

(* Lemma foo :
  ctx k ->
  typed (Σk ∪ Σ1) (k e1) A ->
  typed Σ1 e1 B ->
  typed Σ2 e2 B ->
  typed (Σk ∪ Σ2) (k e2) A. *)

Lemma ctx_app k1 k2 : ctx k1 -> ctx k2 -> ctx (k1 ∘ k2).
Proof.
  intros H. revert k2. induction H; simpl; auto; intros.
  apply (Ctx_cons k1); eauto.
Qed.

Lemma ctx1_headstep_val k e s e' s' : ctx1 k -> head_step (k e) s e' s' [] -> ∃ v, e = Val v.
Proof.
    intros H. inversion H; intro; inversion H1; inv H2; eauto.
Qed.

Lemma ctx_not_val k e v : ctx k -> k e = Val v -> k = (λ x, x) ∧ e = Val v.
Proof.
  induction 1; eauto; simpl. intro.
  inv H.
Qed.

Lemma pure_step_typed e e' Σ A :
  pure_step e e' ->
  typed Σ ∅ e A ->
  typed Σ ∅ e' A.
Proof.
  intros Hps Hty.
  destruct Hps.
  + invc Hty. rewrite H.
    invc H7.
    invc H5.
    invc H7.
    replace (∅ : envT) with (delete x {[x := t1]} : envT) by
      (by rewrite delete_singleton).
    rewrite map_union_comm; eauto.
    eapply subst_typed; eauto.
    eapply lookup_singleton.
  + invc Hty.
    econstructor. econstructor. rewrite left_id in H5. done.
  + inv Hty. rewrite H0.
    inv H7.
    inv H5. rewrite left_id.
    rewrite left_id in H0. rewrite H0 in H9. done.
  + inv Hty. rewrite H.
    inv H6.
    inv H4. rewrite left_id.
    rewrite left_id in H. rewrite H in H9. done.
  + inv Hty. rewrite H.
    inv H8. rewrite left_id in H. simplify_eq.
    rewrite left_id in H9.
    replace (∅ : envT) with (delete x {[x := t1]} : envT) by
      (by rewrite delete_singleton).
    eapply subst_typed; eauto.
    eapply lookup_singleton.
  + inv Hty. inv H5.
    rewrite left_id in H. simplify_eq. rewrite left_id.
    inv H6. rewrite left_id. done.
  + inv Hty. rewrite H.
    inv H11.
    inv H3.
    rewrite left_id in H. simplify_eq.
    rewrite left_id in H12.
    replace (∅) with (delete x1 (delete x2 ({[x1 := t11]} ∪ {[x2 := t12]})) : envT).
    2: { rewrite delete_union delete_singleton right_id delete_singleton_ne; eauto.
          rewrite delete_singleton. done. }
    rewrite <-(assoc union).
    eapply subst_typed; eauto.
    * solve_map_disjoint.
    * rewrite delete_union delete_singleton right_id delete_singleton_ne; eauto.
      apply lookup_singleton.
    * eapply subst_typed; eauto. solve_map_disjoint.
      apply lookup_union_Some_r.
      {
        rewrite map_disjoint_alt. intro.
        destruct (decide (i = x1)) as [->|?].
        - right. apply lookup_singleton_ne; eauto.
        - left. apply lookup_singleton_ne; eauto.
      }
      apply lookup_singleton.
Qed.

Definition ctx_typed (Σ : heapT) (Γ : envT) (k : expr -> expr) (A : type) (B : type) :=
    ∀ e Σ' Γ', Σ ##ₘ Σ' -> Γ ##ₘ Γ' -> typed Σ' Γ' e A -> typed (Σ ∪ Σ') (Γ ∪ Γ') (k e) B.

Lemma ctx_typed_typed Σ Σ' k A B Γ Γ' e :
  Σ ##ₘ Σ' -> Γ ##ₘ Γ' -> ctx_typed Σ Γ k A B -> typed Σ' Γ' e A -> typed (Σ ∪ Σ') (Γ ∪ Γ') (k e) B.
Proof.
  unfold ctx_typed; eauto.
Qed.

Lemma ctx_typed_compose Σ Σ' Γ Γ' k k' A B C :
  Σ' ##ₘ Σ -> Γ' ##ₘ Γ -> ctx_typed Σ Γ k A B -> ctx_typed Σ' Γ' k' B C -> ctx_typed (Σ' ∪ Σ) (Γ' ∪ Γ) (k' ∘ k) A C.
Proof.
  intros Hdisj Hdisj' Hct1 Hct2.
  unfold ctx_typed in *.
  intros e Σ1 Γ1 Hdisj1 Hdisj1' Htyped1. simpl.
  rewrite <-!(assoc union).
  solve_map_disjoint.
Qed.

Lemma typed_ctx1_typed Σ Γ B k e :
  ctx1 k -> typed Σ Γ (k e) B ->
  ∃ Σ1 Σ2 Γ1 Γ2 A,
    Σ = Σ1 ∪ Σ2 ∧ Σ1 ##ₘ Σ2 ∧
    Γ = Γ1 ∪ Γ2 ∧ Γ1 ##ₘ Γ2 ∧
    ctx_typed Σ2 Γ2 k A B ∧ typed Σ1 Γ1 e A.
Proof.
  intros Hctx1 Htyped.
  destruct Hctx1; invc Htyped;
  try solve [
    do 5 eexists;
    split; last split; last split; last split; last split; eauto;
    intros e' Σ' Γ' Hdisj1 Hdisj2 Htyped';
    rewrite (map_union_comm Σ2); eauto;
    rewrite (map_union_comm Γ2); eauto;
    econstructor; try solve_map_disjoint; eauto
  ]; try solve [
    do 5 eexists;
    split; last split; last split; last split; last split; last eauto; eauto using map_union_comm;
    [by apply map_union_comm|by apply map_union_comm|];
    intros e' Σ' Γ' Hdisj1 Hdisj2 Htyped';
    econstructor; try solve_map_disjoint; eauto
  ]; solve [
    exists Σ; exists ∅; exists Γ; exists ∅; eexists;
    split; last split; last split; last split; last split; last eauto; try rewrite right_id; eauto;
    try apply map_disjoint_empty_r;
    intros e' Σ' Γ' Hdisj1 Hdisj2 Htyped';
    rewrite !left_id;
    econstructor; try solve_map_disjoint; eauto
  ].
Qed.

Lemma typed_ctx_typed Σ Γ B k e :
  ctx k -> typed Σ Γ (k e) B ->
  ∃ Σ1 Σ2 Γ1 Γ2 A,
    Σ = Σ1 ∪ Σ2 ∧ Σ1 ##ₘ Σ2 ∧
    Γ = Γ1 ∪ Γ2 ∧ Γ1 ##ₘ Γ2 ∧
    ctx_typed Σ1 Γ1 k A B ∧ typed Σ2 Γ2 e A.
Proof.
  intros Hctx. revert Σ Γ B. induction Hctx; intros Σ Γ B Htyped.
  - exists ∅, Σ.
    exists ∅, Γ, B.
    rewrite !left_id. repeat split; try apply map_disjoint_empty_l; eauto.
    unfold ctx_typed. intros e' Σ' Γ' _ _. rewrite !left_id. eauto.
  - simpl in *.
    eapply typed_ctx1_typed in Htyped; eauto.
    destruct Htyped as (Σ1 & Σ2 & Γ1 & Γ2 & A & Heq1 & Hdisj1 &
      Heq2 & Hdisj2 & Hctx_typed & Htyped). subst.
    eapply IHHctx in Htyped.
    destruct Htyped as (Σ11 & Σ12 & Γ11 & Γ12 & A' & Heq1' & Hdisj1' &
      Heq2' & Hdisj2' & Hctx_typed' & Htyped). subst.
    exists (Σ2 ∪ Σ11),Σ12.
    exists (Γ2 ∪ Γ11),Γ12.
    eexists.
    repeat split; try solve_map_disjoint; eauto.
    + rewrite map_union_comm; eauto. by rewrite assoc.
    + rewrite map_union_comm; eauto. by rewrite assoc.
    + eapply ctx_typed_compose; eauto; solve_map_disjoint.
Qed.

Lemma map_positive {V} `{Countable K} (A B : gmap K V) :
  A ∪ B = ∅ -> A = ∅ ∧ B = ∅.
Proof.
  intros. apply map_positive_l in H0 as H0'. subst. rewrite left_id in H0. done.
Qed.


Inductive bufs_typed : heapT -> list val * chan_type -> list val * chan_type -> Prop :=
  | BT_emp : ∀ ct, bufs_typed ∅ ([], ct) ([], dual ct)
  | BT_consL : ∀ Σ1 Σ2 v vT vs ct c,
    Σ1 ##ₘ Σ2 ->
    val_typed Σ1 v vT ->
    bufs_typed Σ2 (vs, ct) ([], c) ->
    bufs_typed (Σ1 ∪ Σ2) (v::vs, ct) ([], RecvT vT c)
  | BT_consR : ∀ Σ1 Σ2 v vT vs ct c,
    Σ1 ##ₘ Σ2 ->
    val_typed Σ1 v vT ->
    bufs_typed Σ2 ([], c) (vs, ct) ->
    bufs_typed (Σ1 ∪ Σ2) ([], RecvT vT c) (v::vs, ct).

Definition none_to_end (ct' : option chan_type) : chan_type :=
  match ct' with
  | None => EndT
  | Some ct => ct
  end.

Definition invariant (threads : list expr) (chans : heap) : Prop :=
  ∃ (threadΣs : list heapT) (chanΣs : list heapT),
    disjoint (threadΣs ++ chanΣs) ∧
    Forall2 (λ Σt t, typed Σt ∅ t UnitT) threadΣs threads ∧
    let Σ := ⋃ (threadΣs ++ chanΣs) in
    Forall3 (λ (Σbuf : heapT) '(buf1,buf2) (i : nat),
        bufs_typed Σbuf
            (buf1, none_to_end (Σ !! (i,true)))
            (buf2, none_to_end (Σ !! (i,false)))
      ) chanΣs chans (seq 0 (length chans)).

Lemma preservation es h es' h' :
  invariant es h -> step es h es' h' -> invariant es' h'.
Proof.
  intros Hinv Hstep.
  destruct Hstep.
  destruct H.
  unfold invariant in *.
  destruct Hinv as (threadΣs & chanΣs & Hdisj & Hthreads & Hheap).
  destruct (Forall2_lookup_r _ _ _ _ _ Hthreads H0) as (Σ' & Hsome & Htyped).
  eapply typed_ctx_typed in Htyped; eauto.
  destruct Htyped as (Σ1 & Σ2 & Γ1 & Γ2 & A & Heq1 & Hdisj1 & Heq2 & Hdisj2 & Hctx_typed & Htyped).
  symmetry in Heq2. apply map_positive in Heq2 as [-> ->]. clear Hdisj2. subst.

  destruct H1; try rewrite right_id.
  - eapply pure_step_typed in H1; eauto.
    eapply ctx_typed_typed in H1; eauto; last solve_map_disjoint.
    rewrite left_id in H1.
    exists threadΣs, chanΣs.
    split; first done. split; last done.
    replace threadΣs with (<[ i := (Σ1 ∪ Σ2) ]> threadΣs : list heapT) by
      (by eapply list_insert_id in Hsome).
    apply Forall2_insert; done.
  - invc Htyped.
    apply map_positive in H2 as [-> ->]. clear H7.
    invc H10.
    invc H8.
    invc H6.
    (* Need to get our hands on the bufs typed here *)
    (* Need to get the exists right here, then the rest should be easier *)
    admit.
  - invc Htyped.
    invc H5.
    invc H4.
    admit.
  - invc Htyped.
    invc H5.
    invc H4.
    exists (<[ i := Σ1 ]> threadΣs), chanΣs.
    split.
    {
      rewrite <-insert_app_l by (apply lookup_lt_Some in Hsome; done).
      eapply disjoint_update_sub; last done.
      - eapply lookup_app_l_Some; eauto.
      - apply map_union_subseteq_l.
    }
    split.
    {
      apply Forall2_insert; first done.
      assert (typed ∅ ∅ (Val Unit) UnitT) by (econstructor; econstructor).
      eapply ctx_typed_typed in H2; last done; rewrite ?right_id in H2; solve_map_disjoint.
    }
    {
      eapply Forall3_impl; first done.
      intros Σh [buf1 buf2] j Hbt.
      (* Need lemma about lookup in foldr union *)
      admit.
    }
  - invc Htyped.
    set c := length h.
    exists (<[ i := Σ1 ∪ {[ (c,true) := ct ]} ]> threadΣs ++ [Σ2 ∪ {[ (c,false) := dual ct ]}]).
    exists (chanΣs ++ [∅]).
    split.
    {
      admit.
    }
    split.
    {
      admit.
    }
    {
      admit.
    }
Admitted.

Inductive final : expr -> Prop :=
  | final_val : ∀ v, final (Val v)
  | final_recv : ∀ c k, ctx k -> final (k $ Recv $ Val $ Chan c).

Lemma ctx_step_cons k e h e' h' ts :
  ctx1 k -> ctx_step e h e' h' ts -> ctx_step (k e) h (k e') h' ts.
Proof.
  intros Hctx1 Hcs.
  destruct Hcs.
  eapply (Ctx_step (λ x, k (k0 x))).
  - constructor; done.
  - done.
Qed.

Lemma progress1 Σ e h A :
  typed Σ ∅ e A -> final e ∨ ∃ e' h' ts, ctx_step e h e' h' ts.
Proof.
  intros Htyped.
  revert A Σ Htyped; induction e; intros A Σ Htyped.
  - left. constructor.
  - exfalso. admit.
  - invc Htyped.
    apply map_positive in H as [-> ->]. clear H4.
    edestruct IHe1; first done.
    + invc H;[|invc H5].
      invc H5.
      edestruct IHe2; first done.
      * invc H.
        {
          invc H7.
          invc H1.
          right.
          do 3 eexists.
          eapply (Ctx_step id). constructor.
          constructor. constructor.
        }
        {
          invc H7.
          admit.
        }
      * destruct H as (e'' & h'' & ts & Hcs).
        invc Hcs. do 3 eexists.
        eapply (ctx_step_cons (λ x, App (Val v) x)). constructor.
        constructor. done.
        done.
    + destruct H as (e' & h' & ts & Hcs).
      right. do 3 eexists.
      eapply (ctx_step_cons (λ x, App x e2)); [constructor|done].
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
Admitted.

Lemma progress es h :
  invariant es h -> Forall final es ∨ ∃ es' h', step es h es' h'.
Proof.
Admitted.

Lemma lookup_one_Some {A} (x : A) i v :
  [x] !! i = Some v -> x = v ∧ i = 0.
Proof.
  destruct i; simpl in *.
  - intro. simplify_eq. done.
  - destruct i; simpl; intro; simplify_eq.
Qed.

Lemma disjoint_singleton (x : heapT) :
  disjoint [x].
Proof.
  unfold disjoint. intros.
  apply lookup_one_Some in H0 as [_ ->].
  apply lookup_one_Some in H1 as [_ ->].
  done.
Qed.

Theorem invariant_init e : typed ∅ ∅ e UnitT -> invariant [e] [].
Proof.
  intros Htyped.
  unfold invariant.
  exists [∅], []. simpl.
  split; first by apply disjoint_singleton.
  split; eauto. constructor.
Qed.

Lemma dual_dual c : dual (dual c) = c.
Proof.
  induction c; simpl; auto; rewrite IHc; auto.
Qed.

Lemma bufs_typed_sym Σ Σ' vs vs' r r' :
  bufs_typed (Σ,vs,r) (Σ',vs',r') ->
  bufs_typed (Σ',vs',r') (Σ,vs,r).
Proof.
  induction 1.
  - rewrite<- (dual_dual ct) at 2. constructor.
  - econstructor; eauto.
  - econstructor; eauto.
Qed.

Lemma bufs_typed_sym_iff Σ Σ' vs vs' r r' :
  bufs_typed (Σ,vs,r) (Σ',vs',r') <->
  bufs_typed (Σ',vs',r') (Σ,vs,r).
Proof.
  split; intros; apply bufs_typed_sym; done.
Qed.

Lemma unsimpl_dual_recv aT r : RecvT aT (dual r) = dual (SendT aT r).
Proof. done. Qed.

(*
Does not hold:

Lemma bufs_typed_recv_l Σ Σ' aT vs r vs' r' :
  bufs_typed (Σ,vs,RecvT aT r) (Σ',vs',r') ->
    ∃ Σ1 Σ2 a vs'',
      vs' = a::vs'' ∧
      disj_union Σ' Σ1 Σ2 ∧
      val_typed Σ1 a aT ∧
      bufs_typed (Σ,vs,r) (Σ2,vs',r').
Proof.
  intros H. inv H. eauto.
Qed.
*)

Lemma bufs_typed_recv_l Σ Σ' a aT vs r vs' r' :
  bufs_typed (Σ,vs,RecvT aT r) (Σ',a::vs',r') ->
    ∃ Σ1 Σ2,
      disj_union Σ' Σ1 Σ2 ∧
      val_typed Σ1 a aT ∧
      bufs_typed (Σ,vs,r) (Σ2,vs',r').
Proof.
  intros H. inv H. eauto.
Qed.

Lemma bufs_typed_recv_r Σ Σ' a aT vs r vs' r' :
  bufs_typed (Σ',a::vs',r') (Σ,vs,RecvT aT r) ->
    ∃ Σ1 Σ2,
      disj_union Σ' Σ1 Σ2 ∧
      val_typed Σ1 a aT ∧
      bufs_typed (Σ2,vs',r') (Σ,vs,r) .
Proof.
  intros H. inv H. eauto.
Qed.

Lemma bufs_typed_send_l Σ Σ' Σ1 Σp a aT vs r vs' r' :
  val_typed Σ1 a aT ->
  disj_union Σp Σ Σ1 ->
  bufs_typed (Σ,vs,SendT aT r) (Σ',vs',r') ->
  bufs_typed (Σp,vs++[a],r) (Σ',vs',r').
Proof.
  revert Σ Σ' Σ1 Σp a aT r vs' r'.
  induction vs as [|v1 vr]; intros Σ Σ' Σ1 Σp a aT r vs' r' Hv Hd Hbt; simpl.
  - inv Hbt.
    econstructor. 3: econstructor.
    + apply disj_union_empty_r. apply disj_union_sym in Hd.
      apply disj_union_empty_r in Hd. eauto.
    + eauto.
  - inv Hbt.
    econstructor; last first. 2: done.
    + eapply IHvr; last done; first done.
      unfold disj_union in *. split; last done.
      destruct Hd. destruct H2. simplify_eq.
      rewrite-> map_disjoint_union_l in H. by destruct H.
    + unfold disj_union in *.
      destruct Hd. destruct H2. simplify_eq.
      split.
      * rewrite-> map_disjoint_union_l in H. destruct H.
        symmetry.
        rewrite map_disjoint_union_l. split; auto.
      * by rewrite assoc.
Qed.

Lemma bufs_typed_send_r Σ Σ' Σ1 Σp a aT vs r vs' r' :
  val_typed Σ1 a aT ->
  disj_union Σp Σ Σ1 ->
  bufs_typed (Σ',vs',r') (Σ,vs,SendT aT r) ->
  bufs_typed (Σ',vs',r') (Σp,vs++[a],r).
Proof.
  intros. rewrite-> bufs_typed_sym_iff in H1. rewrite bufs_typed_sym_iff.
  eapply bufs_typed_send_l; try done.
Qed.

(*
Deadlock invariant:
0. Define the type of abstract states

The abstract state is a graph with threads and channels as vertices.
We call this graph the connectivity graph.

1. Compute the abstract state for the simple case where all channel endpoints are inside thread exprs

In this case we have an edge from a thread to a channel if the thread has a channel endpoint for that channel.

2. State the invariant that holds for this abstract state.

The (undirected) connectivity graph is acyclic.

3. Generalize to the case where channel endpoints can also appear in the heap

In this case we also have edges between channels and other channels. If we have an endpoint for channel A in a buffer for channel B, then we have an edge from A to B.

4. State the invariant that holds for this abstract state.

Still the same: the (undirected) connectivity graph is acyclic.
*)

Record connectivity_graph := {
  thread_outgoing_edges : list (gset chan);
  channel_outgoing_edges : list (gset chan)
}.

Fixpoint val_abstract_state (v : val) : gset chan :=
  match v with
  | Unit | Nat _ => ∅
  | Fun _ e => expr_abstract_state e
  | Pair a b => val_abstract_state a ∪ val_abstract_state b
  | Chan (l,_) => {[ l ]}
  end
with expr_abstract_state (e : expr) : gset chan :=
  match e with
  | Val v => val_abstract_state v
  | Var _ => ∅
  | Lam _ a | Recv a | Fork a | Close a => expr_abstract_state a
  | App a b | Send a b | Let _ a b | LetUnit a b | LetProd _ _ a b =>
    expr_abstract_state a ∪ expr_abstract_state b
  | If a b c => expr_abstract_state a ∪ expr_abstract_state b ∪ expr_abstract_state c
  end.

Definition chan_abstract_state (bufs : list val * list val) : gset chan :=
  let (buf1,buf2) := bufs in
  union_list ((val_abstract_state <$> buf1) ++ (val_abstract_state <$> buf2)).

Definition compute_abstract_state (es : list expr) (h : heap) : abstract_state :=
  (expr_abstract_state <$> es, chan_abstract_state <$> h).


Definition node := (nat + chan)%type.
Inductive graph (s : abstract_state) : node -> node -> Prop :=
  | expr_edge : forall E C i o out,
    s = (E,C) -> E !! i = Some out -> o ∈ out -> graph s (inl i) (inr o)
  | chan_edge : forall E C i o out,
    s = (E,C) -> C !! i = Some out -> o ∈ out -> graph s (inr i) (inr o).

(* Current idea:
- A simple path is a path without duplicate nodes
- A tree is a graph where there is a unique simple path between each pair of nodes
- Can do inductive reasoning because there is a maximum length to simple paths in a finite graph
*)

(*
Prior work for deadlocks: type system, language, what kind of proof, how detailed.
- Honda session types (pi calculus) vs intuitionistic vs classical (vs lambda calculus + channels)
- Formal vs informal
- Synchronous vs asynchronous
- Logic based proof (cut elimination) vs buffer based

Potential publication without separation logic.

Wadler is the most related previous work: he has a linear lambda calculus,
and "proves" deadlock freedom by translation to pi calculus.
*)

Theorem invariant_preserved es es' h h' :
  invariant es h -> step es h es' h' -> invariant es' h'.
Proof.
  intros Hinv Hstep.
  inv Hstep.
  - admit.
    (* TODO: think about the right induction hypothesis here, for the induction over the context *)
  - unfold invariant.
    (* TODO: get the type out of the invariant, then construct the right Σ, and prove the new invariant *)
    admit.
Admitted.

Theorem invariant_progress : True.
Proof.
Admitted.