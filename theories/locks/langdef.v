From diris.locks Require Export langtools.

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
  (* Barriers *)
  | ForkBarrier : expr -> expr
  (* Locks *)
  | NewLock : expr -> expr
  | ForkLock : expr -> expr -> expr
  | Acquire : expr -> expr
  | Release : expr -> expr -> expr
  | Wait : expr -> expr
  | Drop : expr -> expr
with val :=
  | FunV : string -> expr -> val
  | UnitV : val
  | PairV : val -> val -> val
  | SumV : nat -> val -> val
  | BarrierV : nat -> val
  | LockV : nat -> val.


(* Type system *)
(* ----------- *)

Inductive linearity := Lin | Unr.

Inductive lockstate := Opened | Closed.
Inductive lockownership := Owner | Client.
Definition lockcap : Type := lockownership * lockstate.
Inductive lockownership_split : lockownership -> lockownership -> lockownership -> Prop :=
  | lo_split_1 : lockownership_split Owner Client Owner
  | lo_split_2 : lockownership_split Owner Owner Client
  | lo_split_3 : lockownership_split Client Client Client.
Inductive lockstate_split : lockstate -> lockstate -> lockstate -> Prop :=
  | ls_split_1 : lockstate_split Opened Closed Opened
  | ls_split_2 : lockstate_split Opened Opened Closed
  | ls_split_3 : lockstate_split Closed Closed Closed.
Definition lockcap_split l1 l2 l3 :=
  lockownership_split l1.1 l2.1 l3.1 ∧ lockstate_split l1.2 l2.2 l3.2.

CoInductive type :=
  | FunT : linearity -> type -> type -> type
  | UnitT : type
  | PairT : type -> type -> type
  | SumT n : (fin n -> type) -> type
  | LockT : lockcap -> type -> type.

CoInductive unr : type -> Prop :=
  | Fun_unr t1 t2 : unr (FunT Unr t1 t2)
  | Unit_unr : unr UnitT
  | Pair_unr t1 t2 : unr t1 -> unr t2 -> unr (PairT t1 t2)
  | Sum_unr n ts : (∀ i, unr (ts i)) -> unr (SumT n ts).

(* We define linear environment splitting here.
   On paper this is implicit in Γ1,Γ2 ⊢ e : A.
   In Coq we have to explicitly say env_split Γ Γ1 Γ2, and typed Γ e A. *)
Definition env := gmap string type.

Definition env_unr (Γ : env) :=
  ∀ x t, Γ !! x = Some t -> unr t.

Definition disj (Γ1 Γ2 : env) :=
  ∀ i t1 t2, Γ1 !! i = Some t1 -> Γ2 !! i = Some t2 -> t1 = t2 ∧ unr t1.

Definition env_split (Γ : env) (Γ1 : env) (Γ2 : env) :=
  Γ = Γ1 ∪ Γ2 ∧ disj Γ1 Γ2.

Definition env_bind (Γ' : env) (x : string) (t : type) (Γ : env) :=
  Γ' = <[ x := t ]> Γ ∧ ∀ t', Γ !! x = Some t' -> unr t'.

Definition env_var (Γ : env) (x : string) (t : type) :=
  ∃ Γ', Γ = <[ x := t ]> Γ' ∧ env_unr Γ'.


Inductive typed : env -> expr -> type -> Prop :=
  (* Base language *)
  | Var_typed Γ x t :
    env_var Γ x t ->
    typed Γ (Var x) t
  | Fun_typed Γ Γ' x e t1 t2 l :
    env_bind Γ' x t1 Γ ->
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
  (* Barriers *)
  | Fork_typed Γ e t1 t2 :
    typed Γ e (FunT Lin (FunT Lin t2 t1) UnitT) ->
    typed Γ (ForkBarrier e) (FunT Lin t1 t2)
  (* Locks *)
  | NewLock_typed Γ e t:
    typed Γ e t ->
    typed Γ (NewLock e) (LockT (Owner,Closed) t)
  | ForkLock_typed Γ Γ1 Γ2 e1 e2 t l1 l2 l3 :
    env_split Γ Γ1 Γ2 ->
    lockcap_split l1 l2 l3 ->
    typed Γ1 e1 (LockT l1 t) ->
    typed Γ2 e2 (FunT Lin (LockT l2 t) UnitT) ->
    typed Γ (ForkLock e1 e2) (LockT l3 t)
  | Acquire_typed Γ e t lo :
    typed Γ e (LockT (lo,Closed) t) ->
    typed Γ (Acquire e) (PairT (LockT (lo,Opened) t) t)
  | Release_typed Γ Γ1 Γ2 e1 e2 t lo :
    env_split Γ Γ1 Γ2 ->
    typed Γ1 e1 (LockT (lo,Opened) t) ->
    typed Γ2 e2 t ->
    typed Γ (Release e1 e2) (LockT (lo,Closed) t)
  | Wait_typed Γ e t :
    typed Γ e (LockT (Owner,Closed) t) ->
    typed Γ (Wait e) t
  | Drop_typed Γ e t :
    typed Γ e (LockT (Client,Closed) t) ->
    typed Γ (Drop e) UnitT.


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
  | ForkBarrier e => ForkBarrier (rec e)
  | NewLock e => NewLock (rec e)
  | ForkLock e1 e2 => ForkLock (rec e1) (rec e2)
  | Acquire e => Acquire (rec e)
  | Release e1 e2 => Release (rec e1) (rec e2)
  | Wait e => Wait (rec e)
  | Drop e => Drop (rec e)
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
  | Ctx_ForkBarrier : ctx1 (λ x, ForkBarrier x)
  | Ctx_NewLock : ctx1 (λ x, NewLock x)
  | Ctx_ForkLock_l e : ctx1 (λ x, ForkLock x e)
  | Ctx_ForkLock_r e : ctx1 (λ x, ForkLock e x)
  | Ctx_Acquire : ctx1 (λ x, Acquire x)
  | Ctx_Release_l e : ctx1 (λ x, Release x e)
  | Ctx_Release_r e : ctx1 (λ x, Release e x)
  | Ctx_Wait : ctx1 (λ x, Wait x)
  | Ctx_Drop : ctx1 (λ x, Drop x).

Inductive ctx : (expr -> expr) -> Prop :=
  | Ctx_id : ctx id
  | Ctx_comp k1 k2 : ctx1 k1 -> ctx k2 -> ctx (k1 ∘ k2).

Inductive obj := Thread (e : expr) | Barrier | Lock (refcnt : nat) (o : option val).
Definition cfg := gmap nat obj.

Inductive local_step : nat -> cfg -> cfg -> Prop :=
  (* Base language *)
  | Pure_step i k e e' :
    ctx k -> pure_step e e' ->
    local_step i {[ i := Thread (k e) ]} {[ i := Thread (k e') ]}
  | Exit_step i :
    local_step i {[ i := Thread (Val UnitV) ]} ∅
  (* Barriers *)
  | Fork_step i j n k v :
    i ≠ j -> i ≠ n -> j ≠ n -> ctx k ->
    local_step i {[ i := Thread (k (ForkBarrier (Val v))) ]}
                 {[ i := Thread (k (Val $ BarrierV n));
                    j := Thread (App (Val v) (Val $ BarrierV n));
                    n := Barrier ]}
  | Sync_step i j n k1 k2 v1 v2 :
    i ≠ j -> i ≠ n -> j ≠ n -> ctx k1 -> ctx k2 ->
    local_step n {[ i := Thread (k1 (App (Val $ BarrierV n) (Val v1)));
                    j := Thread (k2 (App (Val $ BarrierV n) (Val v2)));
                    n := Barrier ]}
                 {[ i := Thread (k1 $ Val v2);
                    j := Thread (k2 $ Val v1) ]}
  (* Locks *)
  | NewLock_step v k n i:
    i ≠ n -> ctx k ->
    local_step i {[ i := Thread (k (NewLock (Val v))) ]}
                 {[ i := Thread (k (Val $ LockV n));
                    n := Lock 0 (Some v) ]}
  | ForkLock_step v o k i j n refcnt :
    i ≠ j -> i ≠ n -> j ≠ n -> ctx k ->
    local_step n {[ i := Thread (k (ForkLock (Val $ LockV n) (Val v)));
                    n := Lock refcnt o ]}
                 {[ i := Thread (k (Val $ LockV n));
                    j := Thread (App (Val v) (Val $ LockV n));
                    n := Lock (S refcnt) o ]}
  | Acquire_step v k i n refcnt :
    i ≠ n -> ctx k ->
    local_step n {[ i := Thread (k (Acquire (Val $ LockV n)));
                    n := Lock refcnt (Some v) ]}
                 {[ i := Thread (k (Val $ PairV (LockV n) v));
                    n := Lock refcnt None ]}
  | Release_step v k i n refcnt :
    i ≠ n -> ctx k ->
    local_step n {[ i := Thread (k (Release (Val $ LockV n) (Val v)));
                    n := Lock refcnt None ]}
                 {[ i := Thread (k (Val $ LockV n));
                    n := Lock refcnt (Some v) ]}
  | Wait_step v k i n :
    i ≠ n -> ctx k ->
    local_step n {[ i := Thread (k (Wait (Val $ LockV n)));
                    n := Lock 0 (Some v) ]}
                 {[ i := Thread (k (Val v)) ]}
  | Drop_step o k i n refcnt :
    i ≠ n -> ctx k ->
    local_step n {[ i := Thread (k (Drop (Val $ LockV n)));
                    n := Lock (S refcnt) o ]}
                 {[ i := Thread (k (Val $ UnitV));
                    n := Lock refcnt o ]}.

Inductive step : nat -> cfg -> cfg -> Prop :=
  | Frame_step ρ ρ' ρf i :
    ρ ##ₘ ρf -> ρ' ##ₘ ρf ->
    local_step i ρ ρ' -> step i (ρ ∪ ρf) (ρ' ∪ ρf).

Definition step' ρ ρ' := ∃ i, step i ρ ρ'.
Definition steps := rtc step'.

