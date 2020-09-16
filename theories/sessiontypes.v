(* tid := nat
obj : Type
obj := loc * loc

blocked : tid → option obj
safe : obj → option tid

(∃ t, blocked t = Some w) → is_Some (safe w)
safe w = Some t → blocked t ≠ Some w
blocked t = None → reducible (es !! i) *)

From iris.proofmode Require Import base tactics classes.

Definition loc := nat.

(*
We have a heap of channel buffers indexed by loc's (e.g. natural numbers).
We represent a channel as a natural number and a boolean for the polarity of the endpoint
Each party will put its messages in one buffer and read from the other
*)
Definition chan := (loc * bool)%type.

(*
We have a lambda calculus-based language with natural numbers, closures, and unit.
In addition we have channel values.
*)
Inductive val :=
    | Unit : val
    | Nat : nat -> val
    | Pair : val -> val -> val
    | Fun : string -> expr -> val
    | Chan : chan -> val

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

Definition heapT := gmap chan chan_type.

Definition disj_union {A B : Type} `{EqDecision A, Countable A}
  (a b c : gmap A B) := b ##ₘ c ∧ a = b ∪ c.

Inductive val_typed : heapT -> val -> type -> Prop :=
    | Unit_typed :
        val_typed ∅ Unit UnitT
    | Nat_typed : ∀ n,
        val_typed ∅ (Nat n) NatT
    | Pair_typed : ∀ a b aT bT Σ Σ1 Σ2,
        disj_union Σ Σ1 Σ2 ->
        val_typed Σ1 a aT ->
        val_typed Σ2 b bT ->
        val_typed Σ (Pair a b) (PairT aT bT)
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
    | App_typed : ∀ Σ Σ1 Σ2 Γ Γ1 Γ2 e1 e2 t1 t2,
        disj_union Σ Σ1 Σ2 ->
        disj_union Γ Γ1 Γ2 ->
        typed Σ1 Γ1 e1 (FunT t1 t2) ->
        typed Σ2 Γ2 e2 t1 ->
        typed Σ Γ (App e1 e2) t2
    | Lam_typed : ∀ Σ Γ Γ' x e t1 t2,
        disj_union Γ' Γ {[ x := t1 ]} ->
        typed Σ Γ' e t2 ->
        typed Σ Γ (Lam x e) (FunT t1 t2)
    | Send_typed : ∀ Σ Σ1 Σ2 Γ Γ1 Γ2 e1 e2 t r,
        disj_union Σ Σ1 Σ2 ->
        disj_union Γ Γ1 Γ2 ->
        typed Σ1 Γ1 e1 (ChanT (SendT t r)) ->
        typed Σ2 Γ2 e2 t ->
        typed Σ Γ (Send e1 e2) (ChanT r)
    | Recv_typed : ∀ Σ Γ e t r,
        typed Σ Γ e (ChanT (RecvT t r)) ->
        typed Σ Γ (Recv e) (PairT t (ChanT r))
    | Let_typed : ∀ Σ Σ1 Σ2 Γ Γ1 Γ2 Γ2' e1 e2 t1 t2 x,
        disj_union Σ Σ1 Σ2 ->
        disj_union Γ Γ1 Γ2 ->
        disj_union Γ2' Γ2 {[ x := t1 ]} ->
        typed Σ1 Γ1 e1 t1 ->
        typed Σ2 Γ2' e2 t2 ->
        typed Σ Γ (Let x e1 e2) t2
    | LetUnit_typed : ∀ Σ Σ1 Σ2 Γ Γ1 Γ2 e1 e2 t,
        disj_union Σ Σ1 Σ2 ->
        disj_union Γ Γ1 Γ2 ->
        typed Σ1 Γ1 e1 UnitT ->
        typed Σ2 Γ2 e2 t ->
        typed Σ Γ (LetUnit e1 e2) t
    | LetProd_typed : ∀ Σ Σ1 Σ2 Γ Γ1 Γ2 Γ2' e1 e2 t11 t12 t2 x1 x2,
        disj_union Σ Σ1 Σ2 ->
        disj_union Γ Γ1 Γ2 ->
        x1 ≠ x2 ->
        disj_union Γ2' Γ2 (<[ x1 := t11 ]> {[ x2 := t12 ]}) ->
        typed Σ1 Γ1 e1 (PairT t11 t12) ->
        typed Σ2 Γ2' e2 t2 ->
        typed Σ Γ (LetProd x1 x2 e1 e2) t2
    | If_typed : ∀ Σ Σ1 Σ2 Γ Γ1 Γ2 e1 e2 e3 t,
        disj_union Σ Σ1 Σ2 ->
        disj_union Γ Γ1 Γ2 ->
        typed Σ1 Γ1 e1 NatT ->
        typed Σ2 Γ2 e2 t ->
        typed Σ2 Γ2 e3 t ->
        typed Σ Γ (If e1 e2 e3) t
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
  | LetUnit x' e1 => LetUnit x' (subst x a e1)
  | LetProd x' y' e1 e2 =>
      LetProd x' y' (subst x a e1) (if decide (x = x' ∨ x = y') then e2 else subst x a e2)
  | If e1 e2 e3 => If (subst x a e1) (subst x a e2) (subst x a e3)
  | Fork e1 => Fork (subst x a e1)
  | Close e1 => Close (subst x a e1)
  end.

Definition lookup_recv (h : heap) (c : chan) : option (list val) :=
  h !! c.1 ≫= λ '(x,y), Some (if c.2 then x else y).

Definition lookup_send (h : heap) (c : chan) : option (list val) :=
  h !! c.1 ≫= λ '(x,y), Some (if c.2 then y else x).

Definition set_recv (h : heap) (c : chan) (buf : list val) : heap :=
  let (l,b) := c in
  match h !! l with
  | Some (x,y) => <[ l := if b then (buf,y) else (x,buf) ]> h
  | None => h
  end.
Definition set_send (h : heap) (c : chan) (buf : list val) : heap :=
  let (l,b) := c in
  match h !! l with
  | Some (x,y) => <[ l := if b then (x,buf) else (buf,y) ]> h
  | None => h
  end.

Inductive head_step : expr -> heap -> expr -> heap -> Prop :=
    | App_head_step : ∀ x e h a,
        head_step (App (Val (Fun x e)) (Val a)) h (subst x a e) h
    | Lam_head_step : ∀ x e h,
        head_step (Lam x e) h (Val (Fun x e)) h
    | Send_head_step : ∀ h c y buf,
        lookup_send h c = Some buf ->
        head_step (Send (Val (Chan c)) (Val y)) h (Val (Chan c)) (set_recv h c (buf ++ [y]))
    | Recv_head_step : ∀ h c y buf,
        lookup_recv h c = Some (y::buf) ->
        head_step (Recv (Val (Chan c))) h (Val (Pair (Chan c) y)) (set_send h c buf)
    | If_head_step1 : ∀ n h e1 e2,
        n ≠ 0 ->
        head_step (If (Val (Nat n)) e1 e2) h e1 h
    | If_head_step2 : ∀ h e1 e2,
        head_step (If (Val (Nat 0)) e1 e2) h e2 h
    | Let_head_step : ∀ x v e h,
        head_step (Let x (Val v) e) h (subst x v e) h
    | LetUnit_head_step : ∀ e h,
        head_step (LetUnit (Val Unit) e) h e h
    | LetProd_head_step : ∀ x1 x2 v1 v2 e h,
        head_step (LetProd x1 x2 (Val (Pair v1 v2)) e) h (subst x1 v1 $ subst x2 v2 e) h
    | Close_step : ∀ c h,
        lookup_recv h c = Some [] ->
        head_step (Close (Val (Chan c))) h (Val Unit) h.

Lemma head_step_deterministic e s e1 e2 s1 s2 :
    head_step e s e1 s1 -> head_step e s e2 s2 -> e1 = e2 ∧ s1 = s2.
Proof.
    intros H1 H2.
    induction H1; inversion H2; auto.
Admitted.
    (* - rewrite H in H7. simplify_eq. auto.
    - rewrite H in H6. simplify_eq. auto.
    - simplify_eq.
    - simplify_eq.
Qed. *)

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
    | Ctx_cons : ∀ k1 k2, ctx1 k1 -> ctx k2 -> ctx (k1 ∘ k2).

Lemma ctx_app k1 k2 : ctx k1 -> ctx k2 -> ctx (k1 ∘ k2).
Proof.
  intros H. revert k2. induction H; simpl; auto; intros.
  apply (Ctx_cons k1); eauto.
Qed.

Lemma ctx1_headstep_val k e s e' s' : ctx1 k -> head_step (k e) s e' s' -> ∃ v, e = Val v.
Proof.
    intros H. inversion H; intro; inversion H1; simplify_eq; eauto.
Qed.

Lemma ctx_not_val k e v : ctx k -> k e = Val v -> k = (λ x, x) ∧ e = Val v.
Proof.
  induction 1; eauto; simpl. intro.
  inversion H; simplify_eq.
Qed.

Ltac cnv := match goal with
  | [C : ctx ?k, H : ?k _ = Val _ |- _] => apply ctx_not_val in H as (-> & ->); eauto
  | [C : ctx ?k, H : Val _ = ?k _ |- _] => symmetry in H; apply ctx_not_val in H as (-> & ->); eauto
  end; match goal with
  [H : head_step (Val _) _ _ _ |- _] => inversion H
  end.

Lemma ctx_headstep k1 e1 k2 e2 s : ctx k1 -> ctx k2 ->
  k1 e1 = k2 e2 -> (∃ e1' s', head_step e1 s e1' s') -> (∃ e2' s', head_step e2 s e2' s') ->
  k1 = k2 ∧ e1 = e2.
Proof.
  intros C1.
  revert k2.
  induction C1 as [|C1' k1']; intros k2 C2 Heq.
  - induction C2; eauto.
    intros (e1' & s1 & Hs1) (e2' & s2 & Hs2).
    inversion H; simplify_eq; simpl in *; inversion Hs1; simplify_eq; cnv.
  - induction C2.
    + intros (e1' & s1 & Hs1) (e2' & s2 & Hs2).
      inversion H; simplify_eq; simpl in *; inversion Hs2; simplify_eq; cnv.
    + inversion H; inversion H0; simplify_eq;
      try (intros; assert (k1' = k2 ∧ e1 = e2) as (-> & ->); eauto);
      destruct H1 as (e1' & s1' & Hs1); destruct H2 as (e2' & s2' & Hs2); try cnv.
Qed.

Inductive ctx_step : expr -> heap -> expr -> heap -> Prop :=
    | Ctx_step : ∀ k e1 e2 s1 s2,
        ctx k -> head_step e1 s1 e2 s2 -> ctx_step (k e1) s1 (k e2) s2.

Lemma ctx_step_deterministic e s e1 e2 s1 s2 :
    ctx_step e s e1 s1 -> ctx_step e s e2 s2 -> e1 = e2 ∧ s1 = s2.
Proof.
    intros H1 H2. inversion H1. inversion H2. simplify_eq.
    assert (k = k0 ∧ e0 = e4) as (-> & ->) by (eapply ctx_headstep; eauto).
    assert (e3 = e5 ∧ s1 = s2) as (-> & ->) by (eapply head_step_deterministic; eauto); eauto.
Qed.

(* TODO: make this a relation on pairs, then steps = rtc step *)
(* We put the fork step here because it needs to spawn a new thread. *)
Inductive step : list expr -> heap -> list expr -> heap -> Prop :=
    | Head_step : ∀ e1 e2 s1 s2 es i k,
        ctx k ->
        head_step e1 s1 e2 s2 ->
        es !! i = Some (k e1) ->
        step es s1 (<[i := (k e2)]> es) s2
    | Fork_step : ∀ (es : list expr) i v (h : heap) k,
        let l := length h in
        ctx k ->
        es !! i = Some (k $ Fork (Val v)) ->
        step es h
            (<[i := k $ Val (Chan (l,true))]> es ++ [App (Val v) (Val (Chan (l,false)))])
            (h++[([],[])]).

(* Closure of the step relation; this is used in the theorem statement. *)
Inductive steps : list expr -> heap -> list expr -> heap -> Prop :=
    | Trans_step : ∀ e1 e2 e3 s1 s2 s3,
        step e1 s1 e2 s2 ->
        steps e2 s2 e3 s3 ->
        steps e1 s1 e3 s3
    | Empty_step : ∀ e1 s1,
        steps e1 s1 e1 s1.

Inductive all_values : list expr -> Prop :=
    | AV_nil : all_values []
    | AV_cons : ∀ es v, all_values es -> all_values (Val v :: es).
    (* TODO: add case for waiting on Recv on an empty buffer for now *)

Definition disjoint (xs : list heapT) :=
    forall i j h1 h2, i ≠ j ->
        xs !! i = Some h1 -> xs !! j = Some h2 -> h1 ##ₘ h2.

Fixpoint disjoint_union {A B : Type} `{Countable A}
                        (x : gmap A B) (ys : list (gmap A B)) :=
    match ys with
    | [] => x = ∅
    | y::ys' => ∃ x', disj_union x x' y ∧ disjoint_union x' ys'
    end.

(* Definition connected (hs : list heapT) (i j : nat) :=
    ∃ h1 h2 (l1 l2 : loc) (t : chan_type),
        hs !! i = Some h1 ∧ hs !! j = Some h2 ∧
        h1 !! (l1,l2) = Some t ∧ h2 !! (l2,l1) = Some (dual t).
        (* TODO: how to handle the things in the buffers?? *)

Definition unidirect (T : nat -> nat -> Prop) i j := i < j ∧ T i j.

Definition is_undirected_tree (T : nat -> nat -> Prop) : Prop :=
  Symmetric T ∧ Irreflexive (tc (unidirect T)). *)


Inductive bufs_typed : heapT * list val * chan_type -> heapT * list val * chan_type -> Prop :=
  | BT_emp : ∀ ct, bufs_typed (∅, [], ct) (∅, [], dual ct)
  | BT_consL : ∀ Σ Σ1 Σ2 v vT vs ct c,
    disj_union Σ Σ1 Σ2 ->
    val_typed Σ1 v vT ->
    bufs_typed (Σ2, vs, ct) (∅, [], c) ->
    bufs_typed (Σ, v::vs, ct) (∅, [], RecvT vT c)
  | BT_consR : ∀ Σ Σ1 Σ2 v vT vs ct c,
    disj_union Σ Σ1 Σ2 ->
    val_typed Σ1 v vT ->
    bufs_typed (∅, [], c) (Σ2, vs, ct) ->
    bufs_typed (∅, [], RecvT vT c) (Σ, v::vs, ct).

Definition invariant (es : list expr) (h : heap) : Prop :=
  ∃ (Σ : heapT) (Σs : list heapT) (Σh1 Σh2 : list heapT),
    disjoint_union Σ (Σh1 ++ Σh2 ++ Σs) ∧
    Forall2 (λ Σ e, typed Σ ∅ e UnitT) Σs es ∧
    length Σh1 = length h ∧
    length Σh2 = length h ∧
    ∀ l b ct, Σ !! (l,b) = Some ct ->
      ∃ b1 b2 ct' Σ1 Σ2,
        Σ !! (l,negb b) = Some ct' ∧
        lookup_recv h (l,b) = Some b1 ∧
        lookup_recv h (l,negb b) = Some b2 ∧
        Σh1 !! l = Some Σ1 ∧
        Σh2 !! l = Some Σ2 ∧
        bufs_typed (Σ1, b1, ct) (Σ2, b2, ct').

Theorem invariant_init e : typed ∅ ∅ e UnitT -> invariant [e] [].
Proof.
  intros Ht.
  unfold invariant.
  exists ∅, [∅ : heapT], [], []. simpl. split.
  - exists ∅. unfold disj_union. split; eauto. split.
    + apply map_disjoint_empty_l.
    + by rewrite left_id_L.
  - repeat (split;eauto). intros.
    by apply lookup_empty_Some in H.
Qed.

Lemma disj_union_positive {A B : Type} `{Countable A} (x y : gmap A B) : disj_union ∅ x y -> x = ∅ ∧ y = ∅.
Proof.
  unfold disj_union.
  intros [Hd Hu]. symmetry in Hu. split.
  - by apply map_positive_l in Hu.
  - by rewrite map_union_comm in Hu; first apply map_positive_l in Hu.
Qed.

Lemma disj_union_empty_r {A B : Type} `{Countable A} (x y : gmap A B) : disj_union x y ∅ <-> x = y.
Proof.
  unfold disj_union.
  rewrite right_id; split.
  - naive_solver.
  - intros H'. split; auto. apply map_disjoint_empty_r.
Qed.

Lemma disj_union_sym {A B : Type} `{Countable A} (x y z : gmap A B) : disj_union x y z <-> disj_union x z y.
Proof.
  unfold disj_union. split; intros []; split; try (symmetry; done); subst; rewrite map_union_comm; eauto.
Qed.

Lemma disj_union_singleton_r {A B : Type} `{Countable A} (x : gmap A B) k v k' v' :
  disj_union {[k := v]} x {[k' := v']} -> x = ∅ ∧ k = k' ∧ v = v'.
Proof.
  intros [Hd Hx]. pose proof (f_equal (.!! k') Hx); simplify_map_eq.
  split; [|done]. apply map_empty; intros k''. apply eq_None_not_Some; intros [y ?].
  apply (f_equal (.!! k'')) in Hx; simplify_map_eq.
Qed.

(* Lemma disj_union_singleton_case {A B : Type} `{Countable A} {Γ' Γ Γ1 Γ2 : gmap A B} {x vT} :
  disj_union Γ' Γ {[x := vT]} ->
  disj_union Γ' Γ1 Γ2 ->
  (∃ Γ1', disj_union Γ1 Γ1' {[ x := vT ]}) ∨ (∃ Γ2', disj_union Γ2 Γ2' {[ x:= vT ]}).
Proof.
Admitted.
*)

Lemma disj_union_assoc_l {A B : Type} `{Countable A} {Σ123 Σ23 Σ1 Σ2 Σ3 : gmap A B} :
  disj_union Σ123 Σ1 Σ23 ->
  disj_union Σ23 Σ2 Σ3 ->
  disj_union Σ123 (Σ1 ∪ Σ2) Σ3.
Proof.
Admitted.

Lemma disj_union_assoc_r {A B : Type} `{Countable A} {Σ123 Σ23 Σ1 Σ2 Σ3 : gmap A B} :
  disj_union Σ123 Σ1 Σ23 ->
  disj_union Σ23 Σ2 Σ3 ->
  disj_union (Σ1 ∪ Σ2) Σ1 Σ2.
Proof.
Admitted.


Lemma disj_union_lookup_None_l {A B : Type} `{Countable A} {Γ Γ1 Γ2 : gmap A B} x :
  disj_union Γ Γ1 Γ2 ->
  Γ !! x = None ->
  Γ1 !! x = None.
Proof.
  unfold disj_union; intros [? ->] ?. apply lookup_union_None in H1. by destruct H1.
Qed.

Lemma disj_union_lookup_None_r {A B : Type} `{Countable A} {Γ Γ1 Γ2 : gmap A B} x :
  disj_union Γ Γ1 Γ2 ->
  Γ !! x = None ->
  Γ2 !! x = None.
Proof.
  rewrite disj_union_sym. apply disj_union_lookup_None_l.
Qed.

Lemma typed_no_var_subst Γ Σ e t x v :
  Γ !! x = None ->
  typed Σ Γ e t ->
  subst x v e = e.
Proof.
  intros Heq Ht. induction Ht; f_equal/=;
  eauto using disj_union_lookup_None_l, disj_union_lookup_None_r; case_decide; simplify_map_eq; auto.
  - f_equal. apply IHHt. destruct H. simplify_map_eq. rewrite lookup_union Heq lookup_singleton_ne; auto.
  - apply IHHt2. destruct H1. destruct H0. simplify_map_eq. rewrite lookup_union.
    apply lookup_union_None in Heq. destruct Heq as (_ & ->).
    rewrite lookup_singleton_ne; auto.
  - apply IHHt2. destruct H0. destruct H2. simplify_map_eq.
    rewrite lookup_union. apply lookup_union_None in Heq. destruct Heq as (_ & ->).
    rewrite lookup_insert_ne; auto. rewrite lookup_singleton_ne; auto.
Qed.

Lemma disj_union_case {A B : Type} `{Countable A} {Γ Γ0 Γ1 Γ2 : gmap A B} {x v} :
  disj_union Γ Γ1 Γ2 ->
  disj_union Γ Γ0 {[x := v]} ->
  (disj_union Γ1 (delete x Γ1) {[x := v]} ∧ Γ2 !! x = None) ∨
  (disj_union Γ2 (delete x Γ2) {[x := v]} ∧ Γ1 !! x = None).
Proof.
  intros [] []. simplify_map_eq.
  destruct (Γ1 !! x) eqn:E.
  - left. split; last eauto using map_disjoint_Some_r.
    pose proof (f_equal (.!! x) H3). simplify_map_eq. unfold disj_union.
    rewrite -insert_union_singleton_r; last apply lookup_delete.
    rewrite insert_delete.
    rewrite insert_id; auto. split; auto.
    apply map_disjoint_singleton_r_2.
    by rewrite lookup_delete.
  - right. split; auto.
    pose proof (f_equal (.!! x) H3). simplify_map_eq. unfold disj_union.
    rewrite -insert_union_singleton_r; last apply lookup_delete.
    rewrite insert_delete.
    rewrite insert_id; auto. split; auto.
    apply map_disjoint_singleton_r_2.
    by rewrite lookup_delete. apply lookup_union_Some in H1; auto.
    destruct H1; simplify_eq. auto.
Qed.

Lemma disj_union_neq {A B : Type} `{Countable A} {Γ Γ' Γ'' : gmap A B} {x1 x2 v1 v2} :
  disj_union Γ' Γ {[x1 := v1]} ->
  disj_union Γ'' Γ' {[x2 := v2]} ->
  x1 ≠ x2 ∧ ∃ Γ2', disj_union Γ2' Γ {[x2 := v2]}.
Proof.
  intros [] []. subst. split; first by simplify_map_eq.
  exists (<[x2 := v2]> Γ).
  split. solve_map_disjoint. simplify_map_eq. rewrite insert_union_singleton_r; auto.
Qed.

Lemma subst_typed Σ Σ1 Σ2 Γ Γ1 e eT v vT x :
  disj_union Σ Σ1 Σ2 ->
  disj_union Γ Γ1 {[ x := vT ]} ->
  val_typed Σ1 v vT ->
  typed Σ2 Γ e eT ->
  typed Σ Γ1 (subst x v e) eT.
Proof.
  intros Ds Dg Hv Ht. revert Ds Dg Hv. revert Γ1 Σ Σ1 x v vT.
  induction Ht; simpl; intros.
  - apply disj_union_positive in Dg as [_ Dg]. apply singleton_non_empty in Dg. by exfalso.
  - apply disj_union_empty_r in Ds. apply disj_union_singleton_r in Dg as (A & B & C). subst.
    case_decide; first by constructor. by contradict H.
  - destruct (disj_union_case H0 Dg) as [[]|[]].
    + erewrite-> (typed_no_var_subst _ _ e2) by done.
      econstructor; last done.
      * eapply disj_union_assoc_l; eauto.
      * admit.
      * eapply IHHt1.
       admit. (* map reasoning *)
    + admit. (* symmetric case *)
  - destruct (disj_union_neq Dg H) as (Heq & Γ1' & Hdisj). rewrite decide_False; last done.
    econstructor; eauto. eapply IHHt; eauto.
    destruct H. destruct Dg. destruct Hdisj. subst.
    split. solve_map_disjoint. rewrite -assoc_L. rewrite (map_union_comm {[x0 := vT]}). rewrite assoc_L. done. solve_map_disjoint.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - constructor. eauto.
  - constructor. eauto.
Admitted.

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
  intros H. inversion H; simplify_eq. eauto.
Qed.
*)

Lemma bufs_typed_recv_l Σ Σ' a aT vs r vs' r' :
  bufs_typed (Σ,vs,RecvT aT r) (Σ',a::vs',r') ->
    ∃ Σ1 Σ2,
      disj_union Σ' Σ1 Σ2 ∧
      val_typed Σ1 a aT ∧
      bufs_typed (Σ,vs,r) (Σ2,vs',r').
Proof.
  intros H. inversion H. simplify_eq. eauto.
Qed.

Lemma bufs_typed_recv_r Σ Σ' a aT vs r vs' r' :
  bufs_typed (Σ',a::vs',r') (Σ,vs,RecvT aT r) ->
    ∃ Σ1 Σ2,
      disj_union Σ' Σ1 Σ2 ∧
      val_typed Σ1 a aT ∧
      bufs_typed (Σ2,vs',r') (Σ,vs,r) .
Proof.
  intros H. inversion H. simplify_eq. eauto.
Qed.

Lemma bufs_typed_send_l Σ Σ' Σ1 Σp a aT vs r vs' r' :
  val_typed Σ1 a aT ->
  disj_union Σp Σ Σ1 ->
  bufs_typed (Σ,vs,SendT aT r) (Σ',vs',r') ->
  bufs_typed (Σp,vs++[a],r) (Σ',vs',r').
Proof.
  revert Σ Σ' Σ1 Σp a aT r vs' r'.
  induction vs as [|v1 vr]; intros Σ Σ' Σ1 Σp a aT r vs' r' Hv Hd Hbt; simpl.
  - inversion Hbt. simplify_eq.
    econstructor. 3: econstructor.
    + apply disj_union_empty_r. apply disj_union_sym in Hd.
      apply disj_union_empty_r in Hd. eauto.
    + eauto.
  - inversion Hbt. simplify_eq.
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
  thread_outgoing_edges : list (gset loc);
  channel_outgoing_edges : list (gset loc)
}.

Fixpoint val_abstract_state (v : val) : gset loc :=
  match v with
  | Unit | Nat _ => ∅
  | Fun _ e => expr_abstract_state e
  | Pair a b => val_abstract_state a ∪ val_abstract_state b
  | Chan (l,_) => {[ l ]}
  end
with expr_abstract_state (e : expr) : gset loc :=
  match e with
  | Val v => val_abstract_state v
  | Var _ => ∅
  | Lam _ a | Recv a | Fork a | Close a => expr_abstract_state a
  | App a b | Send a b | Let _ a b | LetUnit a b | LetProd _ _ a b =>
    expr_abstract_state a ∪ expr_abstract_state b
  | If a b c => expr_abstract_state a ∪ expr_abstract_state b ∪ expr_abstract_state c
  end.

Definition chan_abstract_state (bufs : list val * list val) : gset loc :=
  let (buf1,buf2) := bufs in
  union_list ((val_abstract_state <$> buf1) ++ (val_abstract_state <$> buf2)).

Definition compute_abstract_state (es : list expr) (h : heap) : abstract_state :=
  (expr_abstract_state <$> es, chan_abstract_state <$> h).


Definition node := (nat + loc)%type.
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
  inversion Hstep; simplify_eq.
  - admit.
    (* TODO: think about the right induction hypothesis here, for the induction over the context *)
  - unfold invariant.
    (* TODO: get the type out of the invariant, then construct the right Σ, and prove the new invariant *)
    admit.
Admitted.

Theorem invariant_progress : True.
Proof.
Admitted.