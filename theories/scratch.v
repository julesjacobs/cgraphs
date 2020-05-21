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

Definition state := gmap loc (list val).

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

Definition env := list (string * type).

Fixpoint dual ct :=
    match ct with
    | EndT => EndT
    | SendT c ct => RecvT c (dual ct)
    | RecvT c ct => SendT c (dual ct)
    end.

Definition heapT := gmap chan chan_type.

(* TODO: Add subscripts to vs code latex thing *)
Definition disj_union (a b c : heapT) := a ##ₘ b ∧ c = a ∪ b.

Inductive val_typed : heapT -> val -> type -> Prop :=
    | Unit_typed :
        val_typed ∅ Unit UnitT
    | Nat_typed : forall n,
        val_typed ∅ (Nat n) NatT
    | Pair_typed : forall a b aT bT Σ Σ1 Σ2,
        disj_union Σ Σ1 Σ2 ->
        val_typed Σ1 a aT ->
        val_typed Σ2 b bT ->
        val_typed Σ (Pair a b) (PairT aT bT)
    | Fun_typed : forall Σ x e a b,
        typed Σ [(x,a)] e b ->
        val_typed Σ (Fun x e) (FunT a b)
    | Chan_typed : forall c ct,
        val_typed {[ c := ct ]} (Chan c) (ChanT ct)

with typed : heapT -> env -> expr -> type -> Prop :=
    | Val_typed : forall Σ v t,
        val_typed Σ v t ->
        typed Σ [] (Val v) t
    | Var_typed : forall x t,
        typed ∅ [(x,t)] (Var x) t
    | App_typed : forall Σ Σ1 Σ2 Γ Γ1 Γ2 e1 e2 t1 t2,
        disj_union Σ Σ1 Σ2 ->
        Γ ≡ₚ Γ1 ++ Γ2 ->
        typed Σ1 Γ1 e1 (FunT t1 t2) ->
        typed Σ2 Γ2 e2 t1 ->
        typed Σ Γ (App e1 e2) t2
    | Lam_typed : forall Σ Γ x e t1 t2,
        typed Σ ((x,t1)::Γ) e t2 ->
        typed Σ Γ (Lam x e) (FunT t1 t2)
    | Send_typed : forall Σ Σ1 Σ2 Γ Γ1 Γ2 e1 e2 t r,
        disj_union Σ Σ1 Σ2 ->
        Γ ≡ₚ Γ1 ++ Γ2 ->
        typed Σ1 Γ e1 (ChanT (SendT t r)) ->
        typed Σ2 Γ e2 t ->
        typed Σ Γ (Send e1 e2) (ChanT r)
    | Recv_typed : forall Σ Γ e t r,
        typed Σ Γ e (ChanT (RecvT t r)) ->
        typed Σ Γ (Recv e) (PairT t (ChanT r))
    | Let_typed : forall Σ Σ1 Σ2 Γ Γ1 Γ2 e1 e2 t1 t2 x,
        disj_union Σ Σ1 Σ2 ->
        Γ ≡ₚ Γ1 ++ Γ2 ->
        typed Σ1 Γ1 e1 t1 ->
        typed Σ2 ((x,t1)::Γ2) e2 t2 ->
        typed Σ Γ (Let x e1 e2) t2
    | If_typed : forall Σ Σ1 Σ2 Γ Γ1 Γ2 e1 e2 e3 t,
        Γ ≡ₚ Γ1 ++ Γ2 ->
        disj_union Σ Σ1 Σ2 ->
        typed Σ1 Γ1 e1 NatT ->
        typed Σ2 Γ2 e2 t ->
        typed Σ2 Γ2 e3 t ->
        typed Σ Γ (If e1 e2 e3) t
    | Fork_typed : forall Σ Γ e ct,
        typed Σ Γ e (FunT (ChanT (dual ct)) UnitT) ->
        typed Σ Γ (Fork e) (ChanT ct)
    | Close_typed : forall Σ Γ e,
        typed Σ Γ e (ChanT EndT) ->
        typed Σ Γ (Close e) UnitT.

(* FIXME: implement substitution *)
Definition subst (x:string) (a:val) (e:expr) : expr := Val Unit.

Inductive head_step : expr -> state -> expr -> state -> Prop :=
    | App_head_step : forall x e s a,
        head_step (App (Val (Fun x e)) (Val a)) s (subst x a e) s
    | Lam_head_step : forall x e s,
        head_step (Lam x e) s (Val (Fun x e)) s
    | Let_head_step : forall x v e2 s,
        head_step (Let x (Val v) e2) s (subst x v e2) s

    (* Not clear how to do this... *)
    | Send_head_step : forall s l1 l2 y buf,
        s !! l1 = Some buf ->
        head_step (Send (Val (Chan (l1,l2))) (Val y)) s (Val (Chan (l1,l2))) (<[l1 := y::buf]> s)
    | Recv_head_step : forall s l1 l2 y buf,
        s !! l2 = Some (y :: buf) ->
        head_step (Recv (Val (Chan (l1,l2)))) s (Val (Pair (Chan (l1,l2)) y)) (<[l2 := buf]> s)

    | If_head_step1 : forall n s e1 e2,
        n ≠ 0 ->
        head_step (If (Val (Nat n)) e1 e2) s e1 s
    | If_head_step2 : forall s e1 e2,
        head_step (If (Val (Nat 0)) e1 e2) s e1 s

    (* TODO: implement these steps *)
    | LetUnit_head_step : forall e s, head_step e s e s
    | LetProd_head_step : forall e s, head_step e s e s
    | Close_step : forall l1 l2 s,
        head_step (Close (Val (Chan (l1,l2)))) s (Val Unit) (delete l1 s).
        (* TODO: check whether it matters that we delete l1 s here *)

(* We put the fork step here because it needs to spawn a new thread. *)
(* FIXME step under contexts
    Build contexts into these rules *)
Inductive step : list expr -> state -> list expr -> state -> Prop :=
    | Head_step : forall e1 e2 s1 s2 es i,
        head_step e1 s1 e2 s2 ->
        es !! i = Some e1 ->
        step es s1 (<[i := e2]> es) s2
    | Fork_step : forall (es : list expr) i e (s : state) e1 (l1 l2 : loc),
        es !! i = Some (Fork e) ->
        s !! l1 = None ->
        s !! l2 = None ->
        l1 ≠ l2 ->
        step e1 s
            (<[i := Val Unit]> e1 ++ [App e (Val (Chan (l1,l2)))])
            (<[l1 := []]> $ <[l2 := []]> s).

(* Closure of the step relation; this is used in the theorem statement. *)
Inductive steps : list expr -> state -> list expr -> state -> Prop :=
    | Trans_step : forall e1 e2 e3 s1 s2 s3,
        step e1 s1 e2 s2 ->
        steps e2 s2 e3 s3 ->
        steps e1 s1 e3 s3
    | Empty_step : forall e1 s1,
        steps e1 s1 e1 s1.

Inductive all_values : list expr -> Prop :=
    | AV_nil : all_values []
    | AV_cons : forall es v, all_values es -> all_values (Val v :: es).

Definition disjoint (xs : list heapT) := True.

Definition invariant (es : list expr) (s : state) : Prop :=
(*
    This invariant should make sure that either all es are values or some e in es can take a step.
    We need to ensure that the expr and state are well typed.
    And we need to ensure that we have an acyclic connectivity graph.
    Picture the current state as a graph with threads as vertices.
    The vertices are connected by channels, so each edge stores a channel.
    A channel consists of a pair of buffers and a channel type for each endpoint.
    The channel types are dual up to what is already stored in the buffer.
    The connectivity graph must be acyclic.
*)
    Forall2 (λ Σ e, typed Σ ∅ e UnitT) Σs es ∧ disjoint Σs.
    (* TODO: figure out invariant
        * Maintain graph + acyclicity predicate
        * Or maintain Coq tree with tree rotations/surgery
     *)

Theorem invariant_init e : invariant [e] [].

Theorem invariant_step e1 s1 e2 s2 :
    invariant e1 s1 ->
    step e1 s1 e2 s2 ->
    invariant e2 s2.
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
    steps [e] [] e1 s1 ->
    all_values e1 ∨ exists e2 s2, step e1 s1 e2 s2.
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