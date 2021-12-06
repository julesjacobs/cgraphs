From diris.microgv Require Export langtools.

(* Expressions and values *)
(* ---------------------- *)

Inductive expr :=
  | Val : val -> expr
  | Var : string -> expr
  | Fun : string -> expr -> expr
  | App : expr -> expr -> expr
  | Unit : expr
  | Pair : expr -> expr -> expr
  | LetPair : expr -> expr -> expr
  | Sum : nat -> expr -> expr
  | MatchSum n : expr -> (fin n -> expr) -> expr
  | Fork : expr -> expr
with val :=
  | FunV : string -> expr -> val
  | UnitV : val
  | PairV : val -> val -> val
  | SumV : nat -> val -> val
  | BarrierV : nat -> val.


(* Type system *)
(* ----------- *)

Inductive linearity := Lin | Unr.

CoInductive type :=
  | FunT : linearity -> type -> type -> type
  | UnitT : type
  | PairT : type -> type -> type
  | SumT n : (fin n -> type) -> type.

CoInductive unr : type -> Prop :=
  | Fun_unr t1 t2 : unr (FunT Unr t1 t2)
  | Unit_unr : unr UnitT
  | Pair_unr t1 t2 : unr t1 -> unr t2 -> unr (PairT t1 t2)
  | Sum_unr n ts : (∀ i, unr (ts i)) -> unr (SumT n ts).

(* We want to use generic tools here.
   Input: predicate that describes copyable and droppable types.
          (we use unr for both)
   Output: the predicates below.
   In general, we may want to allow more interesting splitting within types.
   Then we can lift such a separation algebra to contexts.
   Can we incorporate subtyping too? *)
Definition env := gmap string type.

Definition env_unr (Γ : env) : Prop. Admitted.
(* Γ = Γ1 ∪ Γ2 *)
Definition env_split (Γ : env) (Γ1 : env) (Γ2 : env) : Prop. Admitted.
(* Γ = {[ x := t ]} ∪ Γ' *)
Definition env_insert (Γ : env) (x : string) (t : type) (Γ' : env) : Prop. Admitted.

Inductive typed : env -> expr -> type -> Prop :=
  | Var_typed Γ Γ' x t :
    env_insert Γ x t Γ' ->
    env_unr Γ' ->
    typed Γ (Var x) t
  | Fun_typed Γ Γ' x e t1 t2 l :
    env_insert Γ' x t1 Γ ->
    (l = Unr -> env_unr Γ) ->
    typed Γ' e t2 ->
    typed Γ (Fun x e) (FunT l t1 t2)
  | App_typed Γ Γ1 Γ2 e1 e2 t1 t2 l :
    env_split Γ Γ1 Γ2 ->
    typed Γ1 e1 (FunT l t1 t2) ->
    typed Γ2 e2 t1 ->
    typed Γ (App e1 e2) t2
  | Unit_typed Γ :
    env_unr Γ ->
    typed Γ Unit UnitT
  | Pair_typed Γ Γ1 Γ2 e1 e2 t1 t2 :
    env_split Γ Γ1 Γ2 ->
    typed Γ1 e1 t1 ->
    typed Γ2 e2 t2 ->
    typed Γ (Pair e1 e2) (PairT t1 t2)
  | LetPair_typed Γ Γ1 Γ2 e1 e2 t1 t2 t :
    env_split Γ Γ1 Γ2 ->
    typed Γ1 e1 (PairT t1 t2) ->
    typed Γ2 e2 (FunT Lin t1 (FunT Lin t2 t)) ->
    typed Γ (LetPair e1 e2) t
  | Sum_typed Γ n (ts : fin n -> type) i e :
    typed Γ e (ts i) ->
    typed Γ (Sum i e) (SumT n ts)
  | MatchSumN_typed n Γ Γ1 Γ2 t (ts : fin n -> type) es e :
    env_split Γ Γ1 Γ2 ->
    (n = 0 -> env_unr Γ2) ->
    typed Γ1 e (SumT n ts) ->
    (∀ i, typed Γ2 (es i) (FunT Lin (ts i) t)) ->
    typed Γ (MatchSum n e es) t
  | Fork_typed Γ e t1 t2 :
    typed Γ e (FunT Lin (FunT Lin t2 t1) UnitT) ->
    typed Γ (Fork e) (FunT Lin t1 t2).
  (* fork(e) : ((τ₁ -> τ₂) -> 1) -> (τ₂ -> τ₁) *)
  (* fork(e) : K[τ₁ -> τ₂] -> (τ₂ -> τ₁)

       Γ,x:τ₁->τ₂ ⊢ e:1
    ------------------------
     Γ ⊢ fork(λx.e):τ₂->τ₁
  *)


(* Operational semantics *)
(* --------------------- *)

Definition subst (x:string) (a:val) := fix rec e :=
  match e with
  | Val _ => e
  | Var x' => if decide (x = x') then Val a else e
  | Fun x' e => Fun x' (if decide (x = x') then e else rec e)
  | App e1 e2 => App (rec e1) (rec e2)
  | Unit => Unit
  | Pair e1 e2 => Pair (rec e1) (rec e2)
  | LetPair e1 e2 => LetPair (rec e1) (rec e2)
  | Sum n e => Sum n (rec e)
  | MatchSum n e1 e2 => MatchSum n (rec e1) (rec ∘ e2)
  | Fork e => Fork (rec e)
  end.

Inductive pure_step : expr -> expr -> Prop :=
  | Fun_step x e :
    pure_step (Fun x e) (Val $ FunV x e)
  | App_step x e a :
    pure_step (App (Val $ FunV x e) (Val a)) (subst x a e)
  | Unit_step :
    pure_step Unit (Val $ UnitV)
  | Pair_step v1 v2 :
    pure_step (Pair (Val v1) (Val v2)) (Val $ PairV v1 v2)
  | LetPair_step v1 v2 e:
    pure_step (LetPair (Val $ PairV v1 v2) e) (App (App e (Val v1)) (Val v2))
  | Sum_step n v :
    pure_step (Sum n (Val v)) (Val $ SumV n v)
  | MatchSum_step n (i : fin n) v es :
    pure_step (MatchSum n (Val $ SumV i v) es) (App (es i) (Val v)).

Inductive ctx1 : (expr -> expr) -> Prop :=
  | Ctx_App_l e : ctx1 (λ x, App x e)
  | Ctx_App_r e : ctx1 (λ x, App e x)
  | Ctx_Pair_l e : ctx1 (λ x, Pair x e)
  | Ctx_Pair_r e : ctx1 (λ x, Pair e x)
  | Ctx_LetPair e : ctx1 (λ x, LetPair x e)
  | Ctx_Sum i : ctx1 (λ x, Sum i x)
  | Ctx_MatchSum n es : ctx1 (λ x, MatchSum n x es)
  | Ctx_Fork : ctx1 (λ x, Fork x).

Inductive ctx : (expr -> expr) -> Prop :=
  | Ctx_id : ctx id
  | Ctx_comp k1 k2 : ctx1 k1 -> ctx k2 -> ctx (k1 ∘ k2).

Inductive obj := Thread (e : expr) | Barrier.
Definition cfg := gmap nat obj.

Inductive local_step : nat -> cfg -> cfg -> Prop :=
  | Pure_step i k e e' :
    ctx k -> pure_step e e' ->
    local_step i {[ i := Thread (k e) ]} {[ i := Thread (k e') ]}
  | Exit_step i v :
    local_step i {[ i := Thread (Val v) ]} ∅
  | Fork_step i j n k v : i ≠ j -> i ≠ n -> j ≠ n -> ctx k ->
    local_step i {[ i := Thread (k (Fork (Val v))) ]}
                 {[ i := Thread (k (Val $ BarrierV n));
                    j := Thread (App (Val v) (Val $ BarrierV n));
                    n := Barrier ]}
  | Sync_step i j n k1 k2 v1 v2 : i ≠ j -> i ≠ n -> j ≠ n -> ctx k1 -> ctx k2 ->
    local_step n {[ i := Thread (k1 (App (Val $ BarrierV n) (Val v1)));
                    j := Thread (k2 (App (Val $ BarrierV n) (Val v2)));
                    n := Barrier ]}
                 {[ i := Thread (k1 $ Val v2);
                    j := Thread (k2 $ Val v1)]}.

Inductive step : nat -> cfg -> cfg -> Prop :=
  | Frame_step ρ ρ' ρf i :
    ρ ##ₘ ρf -> ρ' ##ₘ ρf ->
    local_step i ρ ρ' -> step i (ρ ∪ ρf) (ρ' ∪ ρf).

(* Theorem statements *)
(* ------------------ *)

(*
  We have freedom in defining the waiting and can_step predicates.
  One option:
    Thread is waiting for barrier if it's K[App (BarrierV n) v].
    Barrier is waiting for thread if thread holds its endpoint but is not that.
    Thread can step if it can do a pure step.
    Barrier can step if it can do a sync step.
*)

Fixpoint expr_refs e :=
  match e with
  | Val v => val_refs v
  | Var x => ∅
  | Fun x e => expr_refs e
  | App e1 e2 => expr_refs e1 ∪ expr_refs e2
  | Unit => ∅
  | Pair e1 e2 => expr_refs e1 ∪ expr_refs e2
  | LetPair e1 e2 => expr_refs e1 ∪ expr_refs e2
  | Sum i e => expr_refs e
  | MatchSum n e es => expr_refs e ∪ fin_union n (expr_refs ∘ es)
  | Fork e => expr_refs e
  end
with val_refs v :=
  match v with
  | FunV x e => expr_refs e
  | UnitV => ∅
  | PairV v1 v2 => val_refs v1 ∪ val_refs v2
  | SumV i v => val_refs v
  | BarrierV i => {[ i ]}
  end.

Definition expr_waiting e j := ∃ k v, ctx k ∧ e = k (App (Val $ BarrierV j) (Val v)).

Definition waiting (ρ : cfg) (i j : nat) :=
  match ρ !! i, ρ !! j with
  | Some (Thread e), Some Barrier => expr_waiting e j
  | Some Barrier, Some (Thread e) => i ∈ expr_refs e ∧ ¬ expr_waiting e i
  | _,_ => False
  end.

Definition can_step (ρ : cfg) (i : nat) := ∃ ρ', step i ρ ρ'.

Definition inactive (ρ : cfg) (i : nat) := ρ !! i = None.

Inductive reachable (ρ : cfg) : nat -> Prop :=
  | Can_step_reachable i :
      can_step ρ i -> reachable ρ i
  | Waiting_reachable i j:
      waiting ρ i j -> reachable ρ j -> reachable ρ i.

(* Inductive strongly_reachable (ρ : cfg) : nat -> Prop :=
  | Strongly_reachable i :
      (can_step ρ i ∨ ∃ j, waiting ρ i j) ->
      (∀ j, waiting ρ i j -> strongly_reachable ρ j) ->
      strongly_reachable ρ i. *)

(* wf (waiting ρ) ∧ type_safety ρ *)
(* Barrier can wait for two objects at the same time.
   Thread can also do that, but it means something different.
   For a barrier, it means that its needs both to do something in order to step.
   For a thread, it means that it needs any one of those in order to step.
   (Or maybe a thread can even step when it is still waiting!)
   For a thread, should we say for all contexts?
   Or say minimum?
   What about reachability? Even for a thread, we can still say that everything
   it's waiting for is already reachable, right?
   So maybe it does not matter? *)

(* Give coinductive characterization of not reachable:
   Not reachable if can't step, and all the things it's waiting for are not reachable either. *)
(* Give set characterization of reachable? *)

Record deadlock (ρ : cfg) (s : nat -> Prop) := {
  dl_nostep i : s i -> ¬ can_step ρ i;
  dl_waiting i j : waiting ρ i j -> s i -> s j;
}.

Definition type_safety (ρ : cfg) :=
  ∀ i, inactive ρ i ∨ can_step ρ i ∨ ∃ j, waiting ρ i j.
Definition global_progress (ρ : cfg) :=
  (∀ i, inactive ρ i) ∨ (∃ i, can_step ρ i).
Definition fully_reachable (ρ : cfg) :=
  ∀ i, inactive ρ i ∨ reachable ρ i.
Definition deadlock_free (ρ : cfg) :=
  ∀ s, deadlock ρ s -> ∀ i, s i -> inactive ρ i.

Lemma fully_reachable_type_safety ρ :
  fully_reachable ρ -> type_safety ρ.
Proof.
  intros Hfr i. destruct (Hfr i) as [|[]]; eauto.
Qed.

Lemma fully_reachable_global_progress ρ :
  fully_reachable ρ -> global_progress ρ.
Proof.
  intros Hfr.
  destruct (classic (∃ i, ¬ inactive ρ i)).
  - destruct H as [i Hi]. destruct (Hfr i); first naive_solver.
    clear Hi. right. induction H; eauto.
  - left. intros i. apply NNPP. eauto.
Qed.

Lemma fully_reachable_iff_deadlock_free ρ :
  fully_reachable ρ <-> deadlock_free ρ.
Proof.
  split.
  - intros Hfr s [] i si.
    destruct (Hfr i); eauto.
    exfalso. induction H; naive_solver.
  - intros Hdf i. classical_left.
    eapply (Hdf (λ i, ¬ reachable ρ i));
    first constructor; eauto using reachable.
Qed.