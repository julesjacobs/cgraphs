(* tid := nat
obj : Type
obj := loc * loc

blocked : tid → option obj
safe : obj → option tid

(∃ t, blocked t = Some w) → is_Some (safe w)
safe w = Some t → blocked t ≠ Some w
blocked t = None → reducible (es !! i) *)

From iris.proofmode Require Import tactics.

Definition loc := nat.

(*
We have a heap of channel buffers indexed by loc's (e.g. natural numbers).
We represent a channel as a pair of buffers.
Each party will put its messages in one buffer and read from the other
*)
Definition chan := (loc * loc)%type.

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

Definition heap := gmap loc (list val).

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

Definition envT := list (string * type).

Fixpoint dual ct :=
    match ct with
    | EndT => EndT
    | SendT c ct => RecvT c (dual ct)
    | RecvT c ct => SendT c (dual ct)
    end.

Definition heapT := gmap chan chan_type.

Definition disj_union (a b c : heapT) := a ##ₘ b ∧ c = a ∪ b.

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
        typed Σ [(x,a)] e b ->
        val_typed Σ (Fun x e) (FunT a b)
    | Chan_typed : ∀ c ct,
        val_typed {[ c := ct ]} (Chan c) (ChanT ct)

with typed : heapT -> envT -> expr -> type -> Prop :=
    | Val_typed : ∀ Σ v t,
        val_typed Σ v t ->
        typed Σ [] (Val v) t
    | Var_typed : ∀ x t,
        typed ∅ [(x,t)] (Var x) t
    | App_typed : ∀ Σ Σ1 Σ2 Γ Γ1 Γ2 e1 e2 t1 t2,
        disj_union Σ Σ1 Σ2 ->
        Γ ≡ₚ Γ1 ++ Γ2 ->
        typed Σ1 Γ1 e1 (FunT t1 t2) ->
        typed Σ2 Γ2 e2 t1 ->
        typed Σ Γ (App e1 e2) t2
    | Lam_typed : ∀ Σ Γ x e t1 t2,
        (* TODO: freshness condition: x not in Γ depending on whether Γ_x is Drop
            Same condition in Let -> factor freshness predicate is_fresh Γ x
            x not in Γ : is_fresh Γ x
            Γ_x is Drop : is_fresh Γ x
            is_fresh Γ x := match Γ !! x with Some t => is_drop t | None => True end.
            is_fresh Γ x := from_option is_drop True (Γ !! x)
            Change envT to be a map.
        *)
        typed Σ ((x,t1)::Γ) e t2 ->
        typed Σ Γ (Lam x e) (FunT t1 t2)
    | Send_typed : ∀ Σ Σ1 Σ2 Γ Γ1 Γ2 e1 e2 t r,
        disj_union Σ Σ1 Σ2 ->
        Γ ≡ₚ Γ1 ++ Γ2 ->
        typed Σ1 Γ e1 (ChanT (SendT t r)) ->
        typed Σ2 Γ e2 t ->
        typed Σ Γ (Send e1 e2) (ChanT r)
    | Recv_typed : ∀ Σ Γ e t r,
        typed Σ Γ e (ChanT (RecvT t r)) ->
        typed Σ Γ (Recv e) (PairT t (ChanT r))
    | Let_typed : ∀ Σ Σ1 Σ2 Γ Γ1 Γ2 e1 e2 t1 t2 x,
        disj_union Σ Σ1 Σ2 ->
        Γ ≡ₚ Γ1 ++ Γ2 ->
        typed Σ1 Γ1 e1 t1 ->
        typed Σ2 ((x,t1)::Γ2) e2 t2 ->
        typed Σ Γ (Let x e1 e2) t2
    | LetUnit_typed : ∀ Σ Σ1 Σ2 Γ Γ1 Γ2 e1 e2 t,
        disj_union Σ Σ1 Σ2 ->
        Γ ≡ₚ Γ1 ++ Γ2 ->
        typed Σ1 Γ1 e1 UnitT ->
        typed Σ2 Γ2 e2 t ->
        typed Σ Γ (LetUnit e1 e2) t
    | LetProd_typed : ∀ Σ Σ1 Σ2 Γ Γ1 Γ2 e1 e2 t11 t12 t2 x1 x2,
        disj_union Σ Σ1 Σ2 ->
        Γ ≡ₚ Γ1 ++ Γ2 ->
        typed Σ1 Γ1 e1 (PairT t11 t12) ->
        typed Σ2 ((x1,t11)::(x2,t12)::Γ2) e2 t2 ->
        typed Σ Γ (LetProd x1 x2 e1 e2) t2
    (* TODO: LetProd & LetUnit *)
    (* TODO: Shadowing
    0. Freshness condition depending on whether the type is Drop
    1. Barendreght convention, subst renames
    2. De Bruijn -> no shadowing, but environments more complicated (with options, or maps)
    3. Explicit environments in op sem -> Hoare logic mismatch
    4. Subst as a constructor of expr
    *)
    | If_typed : ∀ Σ Σ1 Σ2 Γ Γ1 Γ2 e1 e2 e3 t,
        Γ ≡ₚ Γ1 ++ Γ2 ->
        disj_union Σ Σ1 Σ2 ->
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

(* FIXME: implement substitution *)
Definition subst (x:string) (a:val) (e:expr) : expr := Val Unit.

Inductive head_step : expr -> heap -> expr -> heap -> Prop :=
    | App_head_step : ∀ x e s a,
        head_step (App (Val (Fun x e)) (Val a)) s (subst x a e) s
    | Lam_head_step : ∀ x e s,
        head_step (Lam x e) s (Val (Fun x e)) s
    | Send_head_step : ∀ s l1 l2 y buf,
        s !! l1 = Some buf ->
        head_step (Send (Val (Chan (l1,l2))) (Val y)) s (Val (Chan (l1,l2))) (<[l1 := y::buf]> s)
    | Recv_head_step : ∀ s l1 l2 y buf,
        s !! l2 = Some (y :: buf) ->
        head_step (Recv (Val (Chan (l1,l2)))) s (Val (Pair (Chan (l1,l2)) y)) (<[l2 := buf]> s)
    | If_head_step1 : ∀ n s e1 e2,
        n ≠ 0 ->
        head_step (If (Val (Nat n)) e1 e2) s e1 s
    | If_head_step2 : ∀ s e1 e2,
        head_step (If (Val (Nat 0)) e1 e2) s e2 s
    | Let_head_step : ∀ x v e s,
        head_step (Let x (Val v) e) s (subst x v e) s
    | LetUnit_head_step : ∀ e s,
        head_step (LetUnit (Val Unit) e) s e s
    | LetProd_head_step : ∀ x1 x2 v1 v2 e s,
        head_step (LetProd x1 x2 (Val (Pair v1 v2)) e) s (subst x1 v1 $ subst x2 v2 e) s
    | Close_step : ∀ l1 l2 s,
        head_step (Close (Val (Chan (l1,l2)))) s (Val Unit) (delete l2 s).

Lemma head_step_deterministic e s e1 e2 s1 s2 :
    head_step e s e1 s1 -> head_step e s e2 s2 -> e1 = e2 ∧ s1 = s2.
Proof.
    intros H1 H2.
    induction H1; inversion H2; auto.
    - rewrite H in H7. simplify_eq. auto.
    - rewrite H in H6. simplify_eq. auto.
    - simplify_eq.
    - simplify_eq.
Qed.

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

(* We put the fork step here because it needs to spawn a new thread. *)
Inductive step : list expr -> heap -> list expr -> heap -> Prop :=
    | Head_step : ∀ e1 e2 s1 s2 es i k,
        ctx k ->
        head_step e1 s1 e2 s2 ->
        es !! i = Some (k e1) ->
        step es s1 (<[i := (k e2)]> es) s2
    | Fork_step : ∀ (es : list expr) i v (s : heap) (l1 l2 : loc) k,
        ctx k ->
        es !! i = Some (k $ Fork (Val v)) ->
        s !! l1 = None ->
        s !! l2 = None ->
        l1 ≠ l2 ->
        step es s
            (<[i := k $ Val (Chan (l2,l1))]> es ++ [App (Val v) (Val (Chan (l1,l2)))])
            (<[l1 := []]> $ <[l2 := []]> s).

(* Closure of the step relation; this is used in the theorem heapment. *)
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

(* TODO: make into big disjoint union predicate *)
Definition disjoint (xs : list heapT) :=
    forall i j h1 h2, i ≠ j ->
        xs !! i = Some h1 -> xs !! j = Some h2 -> h1 ##ₘ h2.

Definition connected (hs : list heapT) (i j : nat) :=
    ∃ h1 h2 (l1 l2 : loc) (t : chan_type),
        hs !! i = Some h1 ∧ hs !! j = Some h2 ∧
        h1 !! (l1,l2) = Some t ∧ h2 !! (l2,l1) = Some (dual t).
        (* TODO: the things in the buffers *)

Inductive is_undirected_tree (T : nat -> nat -> Prop) : Prop := .

Definition invariant (es : list expr) (s : heap) : Prop :=
(*
    This invariant should make sure that either all es are values or some e in es can take a step.
    We need to ensure that the expr and heap are well typed.
    And we need to ensure that we have an acyclic connectivity graph.
    Picture the current heap as a graph with threads as vertices.
    The vertices are connected by channels, so each edge stores a channel.
    A channel consists of a pair of buffers and a channel type for each endpoint.
    The channel types are dual up to what is already stored in the buffer.
    The connectivity graph must be acyclic.
*)
    ∃ Σs, Forall2 (λ Σ e, typed Σ [] e UnitT) Σs es ∧
        disjoint Σs ∧ is_undirected_tree (connected Σs).
    (* disjoint_union Σs Σ ∧ heap_typed Σ s *)
(*
PLAN:
1. naming/shadowing
2. safety, invariant
    ask Stephanie: TAPL for session types?
3. deadlocks
*)
    (*
    Q: What about the elements already in the buffer?
       This can mean that one session type is ahead of the other.
    Q: What about channels that sit in a buffer?
    *)
    (* TODO: figure out invariant
        * Maintain graph + acyclicity predicate
        * Or maintain Coq tree with tree rotations/surgery
     *)

Theorem invariant_init e : invariant [e] ∅.
Admitted.

Theorem invariant_step e1 s1 e2 s2 :
    invariant e1 s1 ->
    step e1 s1 e2 s2 ->
    invariant e2 s2.
Admitted.
(*
    For steps not involving channels, we need to ensure that they preserve types.
    The interesting steps are fork, send, recv.

    Fork creates a new thread in the connectivity graph. The parent thread gives some of its linear resources to
    the forked thread. Finally, we insert an edge between the forked thread and the parent thread, which has a
    channel with dual session types and empty buffers. So this preserves the invariant.

    Send takes a linear resource from a thread and puts it in one of the buffers of a channel endpoint that
    the thread owns. This simultaneously steps the session protocol and puts something in the buffer. So this
    preserves the invariant.

    Receive takes an element out of one of the channel endpoints that the thread owns. This simultaneously steps
    the session protocol and takes something out of the buffer. So this preserves the invariant.
*)

Theorem deadlock_freedom e e1 s1 :
    steps [e] ∅ e1 s1 ->
    all_values e1 ∨ ∃ e2 s2, step e1 s1 e2 s2.
Proof.
    intros. induction H.
    - admit.
    -
Qed.
(*
    We first check if all threads are values. If so, we return the first disjunct.
    If there is a thread that's not a value, we will start an iterative process.
    If the thread is not blocked on receive, we are done, because then the thread can take a step.
    If it is blocked on receive, we look at which channel it is blocked on, and to which thread
    the other endpoint is connected to. We continue the iterative process at that thread.
    Because the connectivity graph is a tree, this process will not go in a cycle, so it eventually
    terminates at a thread that can take a step.

    The crucial point is that it is never the case that two threads connected to a channel c are
    both blocked on c. Therefore this iterative process never goes back to where it came from.
    Instead it follows some path in an acyclic graph, and since the graph is finite this will terminate.
*)